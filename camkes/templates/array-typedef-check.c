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
        (__builtin_types_compatible_p(char[4], /*? type ?*/) ||
         __builtin_types_compatible_p(signed char[4], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned char[4], /*? type ?*/) ||
         __builtin_types_compatible_p(short[2], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned short[2], /*? type ?*/) ||
         __builtin_types_compatible_p(int[1], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned int[1], /*? type ?*/) ||
         __builtin_types_compatible_p(long[1], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned long[1], /*? type ?*/) ||
         __builtin_types_compatible_p(long long[1], /*? type ?*/) ||
         __builtin_types_compatible_p(unsigned long long[1], /*? type ?*/) ||
         __builtin_types_compatible_p(double[1], /*? type ?*/) ||
         __builtin_types_compatible_p(long double[1], /*? type ?*/) ||
         __builtin_types_compatible_p(float[1], /*? type ?*/))),

      /* trigger a compile-time warning: */ /*? tmp ?*/(),
      /* do nothing: */ (void)0);
  }
/*- endmacro -*/

/*- set checked_types = set() -*/
/*- for m in me.from_interface.type.methods -*/
  /*- if m.return_type is not none and isinstance(m.return_type, camkes.ast.Reference) and m.return_type._symbol not in checked_types -*/
    /*? array_typedef_check(me.from_interface.type.name, m.name, 'return', m.return_type._symbol) ?*/
    /*- do checked_types.add(m.return_type._symbol) -*/
  /*- endif -*/
  /*- for p in m.parameters -*/
    /*- if isinstance(p.type, camkes.ast.Reference) and p.type._symbol not in checked_types -*/
      /*? array_typedef_check(me.from_interface.type.name, m.name, p.name, p.type._symbol) ?*/
      /*- do checked_types.add(p.type._symbol) -*/
    /*- endif -*/
  /*- endfor -*/
/*- endfor -*/
