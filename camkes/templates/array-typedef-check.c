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

/*# For RPC interfaces, the user can eschew the built-in CAmkES types and
 *# provide their own C typedef for a parameter. Unfortunately when you typedef
 *# an array it has different behaviour to a typedef-ed scalar type, and some
 *# of these differences interfere with the functionality of glue code. CAmkES
 *# cannot easily introspect the user's C code, so the following code
 *# implements a best effort attempt to trigger a compile-time warning if the
 *# user has used a typedef-ed array. See also JIRA CAMKES-306.
 #*/

/*- macro array_typedef_check(interface, method, parameter, type) -*/
  /*# This convoluted no-op triggers a warning if 'type' is an array. #*/
  /*- set tmp = c_symbol() -*/
  static void /*? tmp ?*/(void) NO_INLINE UNUSED
    WARNING("typedef /*? type ?*/ looks like an array (unsupported) and should be wrapped in a struct");
  static void /*? tmp ?*/(void) {
    /* We need something opaque here to prevent the compiler from optimising
     * away an invocation of (and hence the warning attached to) this function.
     * This is also why this function is marked noinline.
     */
    asm volatile ("");
  }
  static void /*? interface ?*/_/*? method ?*/_/*? parameter ?*/_array_typedef_check(/*? type ?*/ x UNUSED)
    UNUSED;
  static void /*? interface ?*/_/*? method ?*/_/*? parameter ?*/_array_typedef_check(/*? type ?*/ x UNUSED) {
    __builtin_choose_expr(

      /*# Arrays decay to pointers across function calls so the size of the
       *# parameter will not match its type if we have a non-word-sized array.
       #*/
      sizeof(x) != sizeof(/*? type ?*/) ||

      /*# The type may be a word-sized array. Check it against all the
       *# underlying types it could map to. Note that we check against some
       *# things that may not be word-sized, but it doesn't hurt to be overly
       *# broad here for a bit of portability. We do not warn on word-sized
       *# struct arrays because they are an unlikely use case, but this check
       *# could be extended in future to cope with these as well.
       #*/
      (sizeof(/*? type ?*/) == sizeof(void*) &&
        (__builtin_types_compatible_p(char[sizeof(void*)], /*? type ?*/) ||
         __builtin_types_compatible_p(signed char[sizeof(void*)], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned char[sizeof(void*)], /*? type ?*/) ||
         __builtin_types_compatible_p(short[sizeof(void*) / sizeof(short)], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned short[sizeof(void*) / sizeof(unsigned short)], /*? type ?*/) ||
         __builtin_types_compatible_p(int[sizeof(void*) / sizeof(int)], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned[sizeof(void*) / sizeof(unsigned)], /*? type ?*/) ||
         __builtin_types_compatible_p(long[sizeof(void*) / sizeof(long)], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned long[sizeof(void*) / sizeof(unsigned long)], /*? type ?*/) ||
         (sizeof(void*) / sizeof(long long) > 0 &&
           __builtin_types_compatible_p(long long[sizeof(void*) / sizeof(long long)], /*? type ?*/)) ||
         (sizeof(void*) / sizeof(unsigned long long) > 0 &&
           __builtin_types_compatible_p(unsigned long long[sizeof(void*) / sizeof(unsigned long long)], /*? type ?*/)) ||
         (sizeof(void*) / sizeof(double) > 0 &&
           __builtin_types_compatible_p(double[sizeof(void*) / sizeof(double)], /*? type ?*/)) ||
         (sizeof(void*) / sizeof(long double) > 0 &&
           __builtin_types_compatible_p(long double[sizeof(void*) / sizeof(long double)], /*? type ?*/)) ||
         (sizeof(void*) / sizeof(float) > 0 &&
           __builtin_types_compatible_p(float[sizeof(void*) / sizeof(float)], /*? type ?*/)))),

      /* trigger a compile-time warning: */ /*? tmp ?*/(),
      /* do nothing: */ (void)0);
  }
/*- endmacro -*/

/*- set checked_types = set() -*/
/*- for m in me.interface.type.methods -*/
  /*- if m.return_type is not none and m.return_type not in checked_types -*/
    /*? array_typedef_check(me.interface.type.name, m.name, 'return', macros.show_type(m.return_type)) ?*/
    /*- do checked_types.add(m.return_type) -*/
  /*- endif -*/
  /*- for p in m.parameters -*/
    /*- if p.type not in checked_types -*/
      /*? array_typedef_check(me.interface.type.name, m.name, p.name, macros.show_type(p.type)) ?*/
      /*- do checked_types.add(p.type) -*/
    /*- endif -*/
  /*- endfor -*/
/*- endfor -*/
