/*# Setup #*/
/*- set thy = splitext(os.path.basename(options.outfile.name))[0] -*/
/*- set interface = me.from_interface.type -*/
/*- set have_heap = {8: False, 16: False, 32: False, 64: False} -*/
/*- set used_types = set() -*/
/*- include 'autocorres/have_heap.thy' -*/

theory /*? thy ?*/ imports 
  "../../../tools/autocorres/AutoCorres"
  "../../../lib/LemmaBucket"
  "../../../lib/WordBitwiseSigned"
begin

/*# install_code.thy expects the thy variable to have a specific relationship
 *# to the underlying C file we want to install.
 #*/
/*- set thy = re.sub('(.*)_base', '\\1', thy) -*/
/*- include 'autocorres/install_code.thy' -*/

end
