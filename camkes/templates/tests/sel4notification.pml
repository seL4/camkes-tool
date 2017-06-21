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

/* The following SPIN model attempts to represent the semantics of the
 * seL4Notification connector code and its relevant correctness properties. It is not
 * intended to be exhaustive, but is intended to give some confidence of the
 * concurrency correctness of the connector's glue code. To execute:
 *
 *     # Verify safety
 *     spin -a sel4notification.pml
 *     gcc -o pan-safety -O3 -DREACH -DSAFETY pan.c
 *     ./pan-safety | tee /dev/stderr | grep -q 'errors: 0'
 *
 *     # Verify liveness
 *     spin -a sel4notification.pml
 *     gcc -o pan-liveness -O3 -DNP -DNOREDUCE pan.c
 *     ./pan-liveness -l -m100000 | tee /dev/stderr | grep -q 'errors: 0'
 */

#define NULL 0

/* The NOTIFICATION underlying the connection itself (`notification` in the template). */
chan connection = [1] of {bool};

/* Models of seL4 NOTIFICATION functions. */
inline NOTIFICATION_WAIT(notification) {
    notification ? 1;
}
inline NOTIFICATION_NOTIFY(notification) {
    atomic {
        if
            :: notification ? [1] -> skip;
            :: !(notification ? [1]) -> notification ! 1;
        fi;
    }
}

/* Models of sync_sem_bare_*. We don't attempt to model the internals of the
 * semaphore with any accuracy, and just assume we have some external evidence
 * of the correctness of the libsel4sync-provided implementation.
 */
byte handoff = 0;
inline SEM_WAIT(result, sem) {
    atomic {
        if
            :: sem > 0 ->
                sem--;
                result = 0;
            /* We over approximate `wait` and assume it can fail at any time
             * for no reason.
             */
            :: result = 1;
        fi;
    }
}
inline SEM_TRYWAIT(result, sem) {
    atomic {
        if
            :: sem > 0 ->
                sem--;
                result = 1;
            :: else ->
                result = 0;
        fi;
    }
}
inline SEM_POST(sem) {
    sem++;
}

/* Model of a binary semaphore. Similarly, we don't attempt to accurately model
 * its internals.
 */
int lock_count = 1;
inline lock() {
    atomic {
        lock_count == 1 ->
            lock_count--;
    }
}
inline unlock() {
    assert(lock_count == 0);
    lock_count++;
}

/* The slot for registered callbacks. */
bool callback = NULL;

/* A process representing the glue code thread. This code is intended to model
 * the glue code execution as closely as possible.
 */
active [1] proctype inf_run() {
    do
        ::
            NOTIFICATION_WAIT(connection);
            lock();
            bool cb = callback;
            callback = NULL;
            if
                :: cb == NULL ->
                    if
                        /* We cap the semaphore at 10, though the
                         * implementation caps it at `INT_MAX`. It is unlikely
                         * we mask any bugs with this under approximation, but
                         * we could increase this value to reduce the risk in
                         * future.
                         */
                        :: handoff < 10 ->
                            SEM_POST(handoff);
                        :: else ->
                            skip;
                    fi;
                :: else ->
                    skip;
            fi;
            /* A claim of the correctness of the connector code is that, at
             * this point, no one else can be concurrently modifying the
             * callback slot, so we ought to know it is empty.
             */
            assert(callback == NULL);
            unlock();
            if
                :: cb != NULL ->
                    /* Here is where we invoke the callback function. We don't
                     * model execution of the callback function.
                     */
                    skip;
                :: else ->
                    skip;
            fi;
progress:
    od;
}

/* The various API functions from the 'to' side of the connector follow. */

inline inf_poll() {
    /* For the purposes of this model, we don't care whether the polled
     * endpoint contained a message or not.
     */
    bool ignored;
    SEM_TRYWAIT(ignored, handoff);
}

inline inf_wait() {
    /* Similarly, we don't care whether a `wait` failed or not. */
    bool ignored;
    SEM_WAIT(ignored, handoff);
}

inline inf_reg_callback() {
    bool result;
    SEM_TRYWAIT(result, handoff);
    if
        :: result -> goto done;
        :: else -> skip;
    fi;
    lock();
    SEM_TRYWAIT(result, handoff);
    if
        :: result ->
            unlock();
            /* At this point in the implementation, we invoke the callback
             * function. We don't model the actual execution of the callback
             * function here.
             */
        :: !result && callback ->
            unlock();
        :: else ->
            /* The following captures a desired correctness property of the
             * connector code. Namely, that we are not overwriting an existing
             * registered callback and there is no pending message.
             */
            assert(callback == NULL && handoff == 0);
            /* The value of the callback pointer itself is irrelevant, so we
             * just use 1 to indicate that the slot is occupied.
             */
            callback = 1;
            unlock();
    fi;
done:;
}

/* A process to represent the user making calls into glue code on the 'to'
 * side. The model is processed in a reasonable time with 4 processes, but we
 * may wish to increase this limit to be more thorough in future.
 */
active [4] proctype user() {
    if
        :: inf_poll();
        :: inf_wait();
        :: inf_reg_callback();
    fi;
progress:
}

/* A process to represent the user making calls into glue code on the 'from'
 * side. Note that we only ever need 1 process for this to capture all possible
 * interleavings.
 */
active [1] proctype inf_emit() {
    do
        ::
            NOTIFICATION_NOTIFY(connection);
progress:
    od;
}
