/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */
/*
 * A default crt0 for ARM. It does the bare minimum required to get into
 * main() with a sensible C environment.
 *
 * This file will only be linked in if:
 *   - no other file already provides a _start symbol, and
 *   - _start is an undefined external symbol (force this by passing
 *     "-u _start" to ld).
 */

.text

/*
 * Image Entry point.
 */
.global _start
_start:
    /* Call main. */
    bl      main

    /* Call _Exit() to suspend ourselves, as opposed to exit() that assumes we
     * are exiting the process and does some undesirable things like closing
     * stdout.
     */
    bl      _Exit

    /* We do not expect to return from _Exit. */
1:  b 1b

/* .text Literal Pool */
.pool
