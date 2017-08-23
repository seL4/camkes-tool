/*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 */

#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>
#include <string.h>
#include <camkes/gdb/serial.h>
#include <camkes/gdb/gdb.h>
#include <sel4/sel4.h>
#include <utils/util.h>


#define BAUD_RATE 115200
#define MAX_PRINTF_LENGTH 256
// Register layout. Done by offset from base port
#define THR_ADDR (0)
#define RBR_ADDR (0)
#define LATCH_LOW_ADDR (0)
#define LATCH_HIGH_ADDR (1)
#define IER_ADDR (1)
#define FCR_ADDR (2)
#define IIR_ADDR (2)
#define LCR_ADDR (3)
#define MCR_ADDR (4)
#define LSR_ADDR (5)
#define MSR_ADDR (6)

#define IER_RESERVED_MASK (BIT(6) | BIT(7))

#define FCR_ENABLE BIT(0)
#define FCR_CLEAR_RECEIVE BIT(1)
#define FCR_CLEAR_TRANSMIT BIT(2)
#define FCR_TRIGGER_16_1 (0)

#define LCR_DLAB BIT(7)

#define MCR_DTR BIT(0)
#define MCR_RTS BIT(1)
#define MCR_AO1 BIT(2)
#define MCR_AO2 BIT(3)

#define LSR_EMPTY_DHR BIT(6)
#define LSR_EMPTY_THR BIT(5)
#define LSR_DATA_READY BIT(0)

#define IIR_FIFO_ENABLED (BIT(6) | BIT(7))
#define IIR_REASON (BIT(1) | BIT(2) | BIT(3))
#define IIR_MSR (0)
#define IIR_THR BIT(1)
#define IIR_RDA BIT(2)
#define IIR_TIME (BIT(3) | BIT(2))
#define IIR_LSR (BIT(2) | BIT(1))
#define IIR_PENDING BIT(0)



static void serial_putchar(int c);

// Serial buffer manipulation
static void initialise_buffer(void);
static int push_buffer(int c);
static void clear_buffer(void);

// Register manipulation functions
static void write_latch(uint16_t val);
static void write_latch_high(uint8_t val);
static void write_latch_low(uint8_t val);
static void write_ier(uint8_t val);
static uint8_t read_ier(void);
static void write_lcr(uint8_t val);
static uint8_t read_lcr(void);
static void write_fcr(uint8_t val);
static void write_mcr(uint8_t val);
static uint8_t read_lsr(void);
static uint8_t read_rbr(void);
static void write_thr(uint8_t val);
static uint8_t read_iir(void);
static uint8_t read_msr(void);

// Serial config
static void set_dlab(int v);
static void disable_interrupt(void);
static void disable_fifo(void);
static void set_baud_rate(uint32_t baud);
static void reset_state(void);
static void enable_fifo(void);
static void enable_interrupt(void);
static void reset_lcr(void);
static void reset_mcr(void);
static void wait_for_fifo(void);
static bool clear_iir(void);

void serial_port_out8_offset(uint16_t offset, uint8_t value);
uint8_t serial_port_in8_offset(uint16_t offset);


int command_wait = false;
int fifo_depth = 1;
int fifo_used = 0;
static gdb_state_t *gdb_state;
// Serial buffer manipulation
static void initialise_buffer(void) {
    buf.length = 0;
    buf.checksum_count = 0;
    buf.checksum_index = 0;
}

static int push_buffer(int c) {
    if (buf.length == GETCHAR_BUFSIZ) {
        return -1;
    } else {
        buf.data[buf.length] = c;
        buf.length++;
        return 0;
    }
}

static void clear_buffer(void) {
    int i;
    for (i = 0; i < buf.length; i++) {
        buf.data[i] = 0;
    }
    initialise_buffer();
}

// Register manipulation functions
static inline void write_latch(uint16_t val) {
    set_dlab(1);
    write_latch_high(val >> 8);
    write_latch_low(val & 0xff);
    set_dlab(0);
}

static inline void write_latch_high(uint8_t val) {
    serial_port_out8_offset(LATCH_HIGH_ADDR, val);
}

static inline void write_latch_low(uint8_t val) {
    serial_port_out8_offset(LATCH_LOW_ADDR, val);
}

static inline void write_ier(uint8_t val) {
    serial_port_out8_offset(IER_ADDR, val);
}
static inline uint8_t read_ier() {
    return serial_port_in8_offset(IER_ADDR);
}

static inline void write_lcr(uint8_t val) {
    serial_port_out8_offset(LCR_ADDR, val);
}
static inline uint8_t read_lcr() {
    return serial_port_in8_offset(LCR_ADDR);
}

static inline void write_fcr(uint8_t val) {
    serial_port_out8_offset(FCR_ADDR, val);
}
// you cannot read the fcr

static inline void write_mcr(uint8_t val) {
    serial_port_out8_offset(MCR_ADDR, val);
}

static inline uint8_t read_lsr() {
    return serial_port_in8_offset(LSR_ADDR);
}

static inline uint8_t read_rbr() {
    return serial_port_in8_offset(RBR_ADDR);
}

static inline void write_thr(uint8_t val) {
    serial_port_out8_offset(THR_ADDR, val);
}

static inline uint8_t read_iir() {
    return serial_port_in8_offset(IIR_ADDR);
}

static inline uint8_t read_msr() {
    return serial_port_in8_offset(MSR_ADDR);
}

// Serial config

void serial_init(gdb_state_t *gdb) {
    // Initialize the serial port
    int UNUSED error;
    error = serial_lock();
    gdb_state = gdb;
    set_dlab(0); // we always assume the dlab is 0 unless we explicitly change it
    disable_interrupt();
    disable_fifo();
    reset_lcr();
    reset_mcr();
    clear_iir();
    set_baud_rate(BAUD_RATE);
    reset_state();
    enable_fifo();
    enable_interrupt();
    clear_iir();
    initialise_buffer();
    error = serial_unlock();

}

static void set_dlab(int v) {
    if (v) {
        write_lcr(read_lcr() | LCR_DLAB);
    } else {
        write_lcr(read_lcr() & ~LCR_DLAB);
    }
}

static void disable_interrupt() {
    write_ier(0);
}

static void disable_fifo() {
    // first attempt to use the clear fifo commands
    write_fcr(FCR_CLEAR_TRANSMIT | FCR_CLEAR_RECEIVE);
    // now disable with a 0
    write_fcr(0);
}

static void set_baud_rate(uint32_t baud) {
    assert(baud != 0);
    assert(115200 % baud == 0);
    uint16_t divisor = 115200 / baud;
    write_latch(divisor);
}

static void reset_state(void) {
    // clear internal global state here
    fifo_used = 0;
}

static void enable_fifo(void) {
    // check if there is a fifo and how deep it is
    uint8_t info = read_iir();
    if ((info & IIR_FIFO_ENABLED) == IIR_FIFO_ENABLED) {
        fifo_depth = 16;
        write_fcr(FCR_TRIGGER_16_1 | FCR_ENABLE);
    } else {
        fifo_depth = 1;
    }
}

static void enable_interrupt(void) {
    write_ier(1);
}

static void reset_lcr(void) {
    // set 8-n-1
    write_lcr(3);
}

static void reset_mcr(void) {
    write_mcr(MCR_DTR | MCR_RTS | MCR_AO1 | MCR_AO2);
}

static void wait_for_fifo() {
    while(! (read_lsr() & (LSR_EMPTY_DHR | LSR_EMPTY_THR)));
    fifo_used = 0;
}

static bool handle_char(void) {
    char c = read_rbr();
    if (c == '$') {
        command_wait = true;
        clear_buffer();

    } else if (buf.checksum_index) {
        buf.checksum_count++;
    } else if (c == '#') {
        buf.checksum_index = buf.length;
    }
    push_buffer(c);
    if (buf.checksum_count == 2 && command_wait) {
        /* Got a command */
        return true;
    }
    return false;
}

static bool clear_iir(void) {
    uint8_t iir;
    while (! ((iir = read_iir()) & IIR_PENDING)) {
        switch(iir & IIR_REASON) {
        case IIR_RDA:
        case IIR_TIME:
            while (read_lsr() & LSR_DATA_READY) {
                bool result = handle_char();
                if (result) {
                    return result;
                }
            }
        default:
            break;
        }
    }
    return false;
}

// Serial usage
static void serial_putchar(int c) {
    // check how much fifo we've used and if we need to drain it
    if (fifo_used == fifo_depth) {
        wait_for_fifo();
    }
    write_thr((uint8_t)c);
    if (c == '\n') {
        wait_for_fifo();
        write_thr('\r');
    }
    fifo_used++;
}


void serial_irq_handle(void) {
    int UNUSED error;
    error = serial_lock();
    bool got_command = clear_iir();
    error = serial_irq_acknowledge();
    error = serial_unlock();
    if (got_command) {
        handle_gdb(gdb_state);
        error = serial_lock();
        clear_buffer();
        command_wait = false;
        error = serial_unlock();
    }
}

void gdb_printf(const char *format, ...) {
    va_list arg;
    char text_buf[MAX_PRINTF_LENGTH];
    va_start(arg, format);
    vsnprintf(text_buf, MAX_PRINTF_LENGTH, format, arg);
    va_end(arg);
    int UNUSED error;
    error = serial_lock();
    for (int i = 0; i < strlen(text_buf); i++) {
        serial_putchar(text_buf[i]);
    }
    error = serial_unlock();
}
