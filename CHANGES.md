Revision history for CAmkES

For more information see the release notes at https://docs.sel4.systems/camkes_release/

This file should be word wrapped to 120 characters

---
Upcoming release

## Changes

* Added RISC-V in `is_64_bit_arch()`
* Added helpers `is_arch_arm()` and `is_arch_riscv()`
* Added an additional parameter with the current architectures for the macros
  `parse_dtb_node_interrupts()` and `global_endpoint_badges()`.
* Extended DTB interrupt property parsing to support either one value or three
  values per interrupt. For three values, ignore the first value on RISC-V.

## Upgrade Notes
---
camkes-3.10.0 2021-06-10
Using seL4 version 12.1.0

## Changes

* Fixed new line generation in `show_attribute_value`.
* Added const expression attributes to help convert CAmkES attributes to literals.
* Fixed broken Python nosetests that weren't updated when moving to Python3 from Python2.
* Added caching when querying DMA frame physical addresses to avoid unnecessary kernel context switch overheads.
* Changed templates and libraries to be DMA cache-aware and to not ignore requests for cache-able memory
  allocations.
* Added a macro function for every dataport to query its size.
* Changed DMA bookkeeping to keep track of pools of frames and not individual frames.
* Added code to sanitize the names of nested components for the naming of a components' DMA pool.
* Converted the repository to use SPDX license tags.
* Fixed the passing of LD flags to the linker from CAmkES generation tools.
* Added the failing C pre-processor command to an exception in the CAmkES parser tools for easier diagnosis.
* Moved the CAmkES component interface header contents away from `camkes.h` and into separate header files that is
  included by `camkes.h`.
* Simplified the `sys_uname` library function.
* Fix handling of array parameters for the CAmkES templates.
* Sped up proofs for cdl-refine.
* Fixed a CMake argument marshalling bug in the `execute_process_with_stale_check` function.

### Upgrade Notes

* DMA pools now require an option to be set explicitly to be made to be cache-able. In a `.camkes` CAmkES assembly
  file, add the following `<component name>.dma_pool_cached = True;` in the 'configuration' block to make a component's
  DMA pool to be cached. Additionally, use `camkes_dma_alloc` in libsel4camkes with the correct arguments to allocate
  cached DMA memory from that pool.

---
camkes-3.9.0 2020-10-27
Using seL4 version 12.0.0

## Changes

* Enforce system-V stack ordering for libc.
    - This allows `musllibc` to initialise and infer the location of `auxv` from `envp` consistently.
* Add `uint64_t` and `int64_t` types to language.
    - This introduced two new data types into the CAmkES language to support larger types.
* Remove `elf.h`, now defined in sel4runtime.
* Camkes,rumprun: fix tls management implementation:
    - `.tdata*` and `.tbss*` linker symbol declarations are suppressed until the final link step.
* Fix `generate_seL4_SignalRecv` in `Context.py` and update `rpc-connector.c` template accordingly.
    - `seL4SignalRecv` only exists on MCS, split the two calls for compatibility.
* Save preprocessed camkes files to allow for easier debugging.
* CMake: Skip fetching gpio list for pc99 platforms.
    - Most PC99 platforms do not have GPIO pins.
* Support for running odroidc2 in camkes-arm-vm. Get the IRQ trigger type through the interrupt node in the dts.
* Add gpio query engine.
    - The engine takes in a YAML file containing a list of GPIO pins and sorts out the 'gpio' queries so that the connector templates for the `seL4GPIOServer` can generate the appropriate structures and functions.
* Add option `CAmkESNoFPUByDefault`.
    - By enabling CAmkESNoFPUByDefault camkes will compile all user-level libraries (except musllibc) with compilation flags to not use the FPU. A component that wishes to use the FPU must override the flags itself.
* Update `seL4InitHardware` template for api change.
    - The configuration name for the list of devices to bind is now a component attribute instead of an interface attribute.
* `libsel4camkes` Support registering DMA memory that is both cached and uncached.
* Add sel4bench dependency into `camkes/templates` to allow for cycle counting.
* `component.common.c`: use correct label for dma pool.
    - When calling `register_shared_variable` from a component context the label needs to be provided.
* Add `seL4DTBHW` connector. This connector variant is similar to `seL4DTBHardware`, but takes a hardware component on the from end.
* `seL4DTBHardware` bug fix, use global interface name. This prevents the allocator from throwing an error when the same interface name is used in a different component.
* Camkes connector extensions + DMA improvements:
    - libsel4camkes: Implement DMA cache for Arm
    - component.common.c: Support additional DMA setting. Allow setting the cache and base paddr value of the DMA pool.
    - Add single_threaded attribute which when set adds the `seL4SingleThreadedComponent` templates.
    - Allow connectors to declare CMake libraries for each end of the connection. This allows a connector to have most of its implementation in a library and only use the template for initialisation and configuration.
    - camkes-gen.cmake: Create component target stub. This is equivalent to creating a Component with no customization but would still contain things based on its Camkes definition, such as connector artifacts.
* Component.common.c: Move init() to C constructor
    - Connectors that don't use threads use runtime constructors for their initialisation.
* Libsel4camkes: camkes_call_hardware_init_modules
Provide this public function for starting hardware modules that have been registered.
* Add `global_rpc_endpoint_badges` macro.
    - This macro assigns badges for different connectors that share the global-rpc-endpoint object for a component instance.
* Libsel4camkes: irq backend for global-connectors. This adds a way for calling registered IRQ notification handlers for connectors that don't have their own threads.
* Add seL4DMASharedData connector and add appropriate library functionality in `libsel4camkes`.
    - This connector sets up a dataport connector that is added to the DMA pool that the camkes runtime tracks for each component.
* Add support for connector header files and component header templates.
    - A connector can now define template header files that will be included by `camkes.h`. Similarly, component header templates will be instantiated and then automatically included by `camkes.h`.
* Support creating TCB pools and assigning domains to them in camkes templates.
    - Assign domain IDs for TCBs in the thread pool based on values provided by the config option array values.
* Generalise jinja linter to support non-camkes use cases. The Jinja linter can now be used on any arbitrary Jinja template.
* Add support in `libsel4camkes` for matching interrupts even if they are defined
with different base types.
* Add interface registration to `libsel4camkes` via `interface_registration.h` as part of the driver framework.
* Revive graph.dot output file for each asssembly. This can be loaded with a
program like `xdot` to view a diagram of the camkes system.
* Virtqueues:
    - Add virtqueue recieve.
    - Set virtqueue size on creation to the number of rings and descriptor tables have.
    - Add `virtqueue_get_client_id` macro for automatically assigning client IDs to distinguish different virtqueue channels within a single component instance.
    - Link channel ID to name, this allows components to bind to channels via naming them rather than knowing their IDs.
* Add Arm irq type support to `seL4HardwareInterrupt` template. This allows IRQs on Arm to have the trigger mode and target core configured.
* Allow `size` to be number as well as a string in `marshal.c` template.
* Add `global_endpoint_badges` macro used by the global-endpoints mechanism to assign badge
values based on a full system composition.
* Make `public allocate_badges` method which is used to standardize badge allocation across many connectors.
* Add support for a component definition to specify a template C source file. This file will be passed through the template tool before passed to the C compiler.
    - This is how components can allocate objects required from a loader without having to define special connector types.
* Add `msgqueue` mechanism which allows componets to sent messages. This is essentially another layer ontop of the virtqueue functionality.
* Accept Red Hat ARM cross-compilers in `check_deps.py`.
* Simplify the logic for combining the connections in the stage9 parser. This improves processing times.
* Camkes-tool:
    - Add priority to muslc so that its initialsation comes after camkes. This relates to recent changes in sel4runtime.
    - Add an interface `dataport_caps` for accessing dataport caps that is used by the seL4SharedDataWithCaps template.
* Tools: define `camkes_tool_processing` when running the C preprocessor.
* Remove `template` keyword from camkes language.
    - This is driven by wanting to make it easier to extend camkes generation build rules with more inputs than a single template file and make it possible better manage non-template code that needs to run when generating templates.

---
camkes-3.8.0 2019-11-19
Using seL4 version 11.0.0

## Changes

* Support for the new seL4 Endpoint GrantReply access right for CAmkES connector types.
  - This allows multi-sender/single-receiver connectors such as `seL4RPCCall` that don't also provide the ability for
    arbitrary capability transfer from sender to receiver. Previously the `seL4RPC` connector was used instead of
    `seL4RPCCall` to create an Endpoint without a Grant right. This used a combination of `seL4_Send` and `seL4_Wait`
    to communicate without the ability for capability transfer, however this only supports a single sender and single
    receiver.
* Better support for configuring components with a provided devicetree.
  - This support includes adding a seL4DTBHardware connector that can be used instead of seL4HardwareMMIO and
  seL4HardwareInterrupt and can be used to extract IRQs and MMIO register information out of the devicetree node rather
  than specifying the info directly. This connector can also be used to access a devicetree within a component for
  querying further device information. There is also a connector seL4VMDTBPassthrough that can be used for specifying
  devices to pass through to a `camkes-arm-vm` VM component.
* CapDL Refinement framework (cdl-refine).
  These are generated Isabelle proof scripts to prove that the generated capDL respects the isolation properties
  expected from its CAmkES system specification. Only the AARCH32 platform is supported. The generated capDL is a
  specification of seL4 objects and capabilities that will implement the CAmkES system specification. This
  specification is then given to a system initialiser to create the objects and capabilities and load the system.
* Support for RISC-V systems.
* Port libsel4camkes environments to the sel4runtime
* CAmkES can be used on any seL4 platform that uses a camkes supported seL4 architecture (x86, Arm, RISC-V)
* By default the C preprocessor will be run over CAmkES ADL files
  - The Camkes syntax excludes lines starting with `#` due to the integration of CPP. This can sometimes cause
    confusion where #ifdef is used but the CPP isn't configured to run. Projects are still able to disable the CPP.
* capDL Static initialisation
  - Using the capDL support for static allocation of objects from an Untyped list, Camkes supports generating specs
    with all objects preallocated. This can then be loaded by a static loader.
  - This is only supported on Arm by setting CAmkESCapDLStaticAlloc=ON.
* Use large pages for dataports if able
  - Instead of rounding the dataports to 4K pages all the time, try to use multiples of larger frames to back the
    dataports if the size of the dataports are a multiple of the larger frames.
* Fix cache flush for seL4HardwareMMIO connectors
  - This was a feature that was available in 2.x.x but removed in 3.0.0.

---
camkes-3.7.0 2018-11-12
Using seL4 version 10.1.1

## Changes


## Upgrade Notes
---
camkes-3.6.0 2018-11-07
Using seL4 version 10.1.0

## Changes

* AARCH64 is now supported.
* CakeML components are now supported.
* Added `query` type to Camkes ADL to allow for querying plugins for component configuration values.
* Components can now make dtb queries to parse device information from dts files.
* Component definitions for serial and timer added on exynos5422, exynos5410, pc99.
* Preliminary support for Isabelle verification of generated capDL.
    - See cdl-refine-tests/README for more information
* Simplify and refactor the alignment and section linking policy for generated Camkes binaries.
* Dataports are now required to declare their size in the ADL.
* Templates now use seL4_IRQHandler instead of seL4_IRQControl, which is consistent with the seL4 API.
    - This change is BREAKING.
* Remove Kbuild based build system.
* Remove caches that optimised the Kbuild build system, which are not required with the new Cmake build system.
* Added virtqueue infrastructure to libsel4camkes, which allows virtio style queues between components.


## Upgrade Notes

* Any dataport definitions that did not specify a size must be updated to use a size.
* Any template that used seL4_IRQControl must be updated to use seL4_IRQHandler.
* Projects must now use the new Cmake based build system.

---
camkes-3.5.0 2018-05-28
Using seL4 version 10.0.0

This release is the last release with official support for Kbuild based projects.
This release and future releases use CMake as the build system for building applications.

## Changes
* Remove `crit` and `max_crit` fields from TCB CapDL Object
  These fields were previously added to support an earlier version of seL4-mcs that gave threads criticality fields.
  This feature was removed from seL4-mcs. This also means that the arguments to camkes-tool, `--default-criticality`
  and `--default-max-criticality`, have also been removed.

## Upgrade Notes
* Calls to `camkes.sh` that used the above arugments will need to be updated.

---
camkes-3.4.0 2018-04-18
Using seL4 version 9.0.1

## Changes


## Upgrade Notes
---
camkes-3.3.0 2018-04-11
Using seL4 version 9.0.0

## Changes
* Hardware dataport with large frame sizes issue has been fixed
* Bug fix: Enumerating connections for hierarchical components with custom connection types is now done correctly
* Bug fix: Data structure caching is now correctly invalidated between builds
* Initial CMake implementation for CAmkES.  See the CAmkES test apps for examples.

## Upgrade notes
* No special upgrade requirements.

## Known issues
* Hierarchical components that export dataport connectors create compilation errors as the templates cannot accurately
  tell that the connector of the parent component is exported from the child and no code should be generated.  A
  temporary workaround involves making the dataport connection explicitly available to the parent component.

---
camkes-3.2.0 2018-01-17
Using seL4 version 8.0.0

= Changes =
 * New ADL Syntax: Allow struct elements to have defaults.
    See the following ADL files for examples of Struct and Attribute behavior.
    https://github.com/SEL4PROJ/rumprun/blob/master/platform/sel4/camkes/rumprun.camkes
    https://github.com/seL4/camkes/tree/master/apps/structs
    https://github.com/seL4/camkes/tree/master/apps/attributes
 * Added experimental Rumprun support:
    This functionality is experimental and may not work as expected.  See the following examples:
    https://github.com/seL4/camkes/tree/master/apps/rumprun_ethernet
    https://github.com/seL4/camkes/tree/master/apps/rumprun_hello
    https://github.com/seL4/camkes/tree/master/apps/rumprun_pthreads
    https://github.com/seL4/camkes/tree/master/apps/rumprun_rust
    More information about the Rumprun unikernel on seL4 can be found here:
       https://research.csiro.au/tsblog/using-rump-kernels-to-run-unmodified-netbsd-drivers-on-sel4/
 * New Templates: Remote GDB debugging support
    On ia32 platforms a GDB server can be used to debug a component using the GDB server remote serial protocol.
    documentation: https://github.com/seL4/camkes-tool/blob/master/docs/DEBUG.md
 * Added "hardware_cached" attribute to hardware dataports
    This feature had been added to camkes-2.x.x but hadn't been forward ported to camkes-3.x.x.
    documentation: https://github.com/seL4/camkes-tool/blob/master/docs/index.md#cached-hardware-dataports

= Known issues =
 * Hardware dataports that are large enough to use larger frame sizes are currently broken.  There is an issue with
large frame promotion and hardware dataports where the capDL loader is unable to map the promoted memory. This can be
demonstrated by running the testhwdataportlrgpages app on either arm_testhwdataportlrgpages_defconfig or
x86_testhwdataportlrgpages_defconfig configurations. If this functionality is required, hold off upgrading until this
issue is fixed.

= Upgrade notes =
 * ADL files: ADL syntax changes in this release should not break any existing ADL files.
 * Templates:
    - seL4HardwareMMIO template now has an option to map hardware memory as cached. The default setting is uncached
      which is the same as the old behaviour.

---
For previous releases see https://docs.sel4.systems/camkes_release/
