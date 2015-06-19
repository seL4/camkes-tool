/*- macro call_array_typedef_check(interface, method, parameter, type) -*/
  /*- set tmp = c_symbol() -*/
  static /*? type ?*/ /*? tmp ?*/;
  /*? interface ?*/_/*? method ?*/_/*? parameter ?*/_array_typedef_check(/*? tmp ?*/);
/*- endmacro -*/

/*- set checked_types = set() -*/
/*- for m in me.from_interface.type.methods -*/
  /*- if m.return_type is not none and isinstance(m.return_type, camkes.ast.Reference) and m.return_type._symbol not in checked_types -*/
    /*? call_array_typedef_check(me.from_interface.type.name, m.name, 'return', m.return_type._symbol) ?*/
    /*- do checked_types.add(m.return_type._symbol) -*/
  /*- endif -*/
  /*- for p in m.parameters -*/
    /*- if isinstance(p.type, camkes.ast.Reference) and p.type._symbol not in checked_types -*/
      /*? call_array_typedef_check(me.from_interface.type.name, m.name, p.name, p.type._symbol) ?*/
      /*- do checked_types.add(p.type._symbol) -*/
    /*- endif -*/
  /*- endfor -*/
/*- endfor -*/
