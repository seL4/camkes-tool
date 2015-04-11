% CAmkES Manual

<!--
     Copyright 2014, NICTA

     This software may be distributed and modified according to the terms of
     the BSD 2-Clause license. Note that NO WARRANTY is provided.
     See "LICENSE_BSD2.txt" for details.

     @TAG(NICTA_BSD)
  -->

This document describes the structure and functionality of CAmkES, a platform
for building componentised systems for embedded platforms. The documentation is
broken into sections for users, template authors and developers. The
[Usage](#usage) section is for people wanting to develop systems
using CAmkES as a platform. The [Templating](#templating) section is
for people wanting to write their own CAmkES templates and use more complex
functionality. Finally the [Developers](#developers) section is for
people wanting to modify the internals of CAmkES itself. Regardless of which
section is most relevant for you, you should at least familiarise yourself with
the [Terminology](#terminology) section.

If you are familiar with CAmkES concepts and just need to forward port
something from the older CAmkES implementation, jump to the
[Legacy Implementation](#legacy-implementation) section.


## Terminology

Throughout this document some domain specific terminology is used that may have
connotations outside CAmkES/component systems. To avoid confusion the meanings
of these terms are made explicit below.

**Abstract Syntax Tree (AST)**

> An internal representation of the results of parsing a generalised grammar.
  More thorough definitions of ASTs are provided
  [elsewhere](https://en.wikipedia.org/wiki/Abstract_syntax_tree), but this is
  noted here because the abbreviation 'AST' is used heavily in this
  documentation.

**Architecture Description Language (ADL)**

> The CAmkES syntax for describing a component system. Most component platforms
  have their own architecture description language for describing a set of
  components and how they are wired together, but the term 'ADL' will be used
  in this documentation to exclusively refer to the CAmkES input specification
  language.

**Assembly**

> A top-level element that encapsulates a component system description. An
  assembly can be thought of as a complete description of a full system. 
  A system must contain at least one assembly. A system with more than one
  assembly is equivalent to a system with one assembly whose composition
  and configuration sections are the concatenation of the composition and
  configuration sections of each assembly.

**Attribute**

> Components and connectors can have extra data of an arbitrary type associated
  with them. These are referred to as attributes. The description of a
  component/connector must describe the name of the attribute and its type. The
  value of the attribute itself is unspecified. It is assigned when the entity
  is instantiated, and this assignment is referred to as a _setting_. Attributes
  are generally used to specialise or differentiate a component at runtime.

**Component**

> A _type_ of functional entity. It is important to stress this distinction.
  'Component' is used colloquially to refer to both types and instances, but in
  a formal sense 'component' refers only to the type. To make this more
  concrete, the statement `component foo f` describes a component _instance_ f,
  whose _type_ is foo.

**Composition**

> A container for the component and connector instantiations that form a system.
  This is essentially a syntactic element for delimiting sections in a
  specification. It is contained by an assembly block, along with an optional
  configuration.

**Compound Component**

> A component with a composition section, and optionally a configuration section.

**Configuration**

> A container for describing settings. This is a syntactic element to hold the
  assignment of attributes for a given system. It is expressed inside an
  assembly block.

**Connection**

> An instantiation of a connector. Connections connect two _instances_. Because
  the instantiation of a connector does not really specialise the connector in
  any particular way, it is easy to conflate the two. However, the sources make
  important distinctions between connectors and connections.

**Connector**

> A _type_ of link between instances. The distinction between 'connector' and
  'connection' is the same as that between 'component' and 'instance,' i.e. a
  connection is an instantiation of a particular connector.

**Consumes**

> Event interfaces that are accepted by a component. If a component consumes a
  particular event it means that it is expecting to receive and handle that
  event.

**Dataport**

> Port interfaces that are used by a component. A component's dataports
  are expected to be available to it at runtime as shared memory regions.

**Direction**

> The flow of a parameter of a procedure method. The only possible directions
  are 'in' (caller to callee), 'out' (callee to caller), 'inout'
  (bidirectional) and 'refin' (identical to 'in' except for the C backend where
  this is optimised to pass-by-reference).

**Emits**

> Event interfaces that are expressed by a component. If a component emits a
  given event it means that it produces events of this type.

**Event**

> An asynchronous signal interface of a component. Events are defined completely
  by their identifier, a numerical value. It may be helpful to think of this
  value as mapping to something like an interrupt number or a signal type,
  although they do not necessarily represent hardware messages.

**Export Connector**

> A special type of connector which can only appear inside a compound component's
  composition section. It can be used to connect one of the compound component's
  interfaces to an interface of an internal instance declared in the compound component's
  composition section. Interfaces of compound components connected with an export
  connector are considered "Virtual Interfaces". Interfaces of internal instances
  connected to virtual interfaces are known as "Exported Interfaces".

**Exported Interface**

> An interface of an internal instance connected to a virtual interface with an export connector.

**Instance**

> An instantiation of a component type. Of course 'instance' can be used to
  refer to an instantiation of any type, but when you see the term 'instance' in
  the sources it is generally referring to the instantiation of a component. To
  give a concrete example, in the statement `component foo f` f is an instance.

**Interface**

> An abstract exposed interaction point of a component. There could be a
  distinction made here between type and instance of one of these interaction
  points, but in practice this is not necessary and ambiguity rarely arises. The
  subcategories of interface are _procedure_, _event_ and _port_.

**Interface Definition Language (IDL)**

> A subset of CAmkES ADL for describing interfaces of components. Previously
  this was considered distinct from ADL, but now the term 'ADL' is intended to
  encompass both syntaxes. The CAmkES IDL subset is heavily inspired by
  [OMG IDL](http://www.omg.org/gettingstarted/omg_idl.htm).

**Internal Instance**

> A component instance declared inside a compound component's composition section.

**Internal Connection**

> A connection declared inside a compound component which connects two internal
  instance interfaces. That is, any connection declared inside a compound component
  which does not use an export connector.

**Method**

> An item of a procedure. When targeting a conventional programming language,
  methods usually map directly to generated functions.

**Parameter**

> A piece of data referenced by a procedure method. This can be thought of as an
  argument to a function.

**Port**

> The interface type that represents shared memory semantics. This was
  previously referred to as 'dataport', but an attempt has been made to use that
  term only for the dependency of a component on a port in the sources. Some
  other documentation may still use 'dataport' to refer to one of these
  interfaces.

**Procedure**

> An interface with function call semantics. This was previously referred to as
  just 'interface.' This older terminology is
  deprecated. Procedures consist of a series of methods that can be invoked
  independently.

**Provides**

> Procedure interfaces implemented by a component. When targeting a conventional
  programming language this typically means that the component contains
  functions that are implementations of each method in the procedures provided.

**Setting**

> An assignment of an attribute to a specific value. A setting does not specify
  the type of the attribute, because this has already been described by the
  attribute as specified in the component/connector description.

**Type**

> A procedure method's return type or parameter type. This information does not
  include the direction of a parameter. An example type is something like
  'string.'

**Uses**

> Procedure interfaces that are invoked by a component. When targeting a
  conventional programming language this typically means that the component
  contains calls to functions that are expected to implement each method in the
  procedures used.

**Virtual Interface**

> An interface of a compound component connected to an internal instance's interface
  using an export connector.

A concrete example:

    procedure thing {
      int func(in int x);
    }

    event sig = 42;

    dataport Buf buffer;

    component foo {
      control;
      uses thing t1;
      emits sig s1;
      dataport buffer b1;
    }

    component bar {
      provides thing t2;
      consumes sig s2;
      dataport buffer b2;
    }

    assembly {
      composition {
        component foo f;
        component bar b;

        connection RPC c1(from f.t1, to b.t2);
        connection Asynch c2(from f.s1, to b.s2);
        connection SharedData c3(from f.b1, to b.b2);
      }
    }

* `thing` is a **procedure**
* `int` is a **type**
* `func` is a **method**
* `in` is a **direction**
* `x` is a **parameter**
* `sig` is an **event**
* `buffer` is a **port**
* `foo` and `bar` are **component**s
* `t1` is a **uses**
* `s1` is a **emits**
* `b1` and `b2` are **dataport**s
* `t2` is a **provides**
* `s2` is a **consumes**
* `assembly { ... }` is an **assembly**
* `composition { ... }` is a **composition**
* `f` and `b` are **instance**s
* `RPC`, `Asynch` and `SharedData` are **connector**s
* `c1`, `c2` and `c3` are **connection**s

## Usage

This section is targeted at people building systems on top of the CAmkES
platform. It assumes a basic knowledge of C programming.

### Dependencies

To work with any of the CAmkES tools you will need some extra software
installed. It is assumed you are operating on a Linux host. Although an attempt
has been made to implement functionality in an OS-independent way you may find
extra dependencies or undocumented portability issues if you are running
another OS.

**Python**

> Python should come pre-installed in most Linux distributions, but if not you
  will need to install it. The tools have been tested with versions 2.6 and
  2.7, but not version 3.

**[PLY](http://www.dabeaz.com/ply/)**

> PLY is an implementation of [Lex](http://dinosaur.compilertools.net/#lex)
  and [Yacc](http://dinosaur.compilertools.net/#yacc) in Python. It is used in
  the parser and should be available from most Linux distributions' default
  repositories as python-ply.

**[PyElftools](https://github.com/eliben/pyelftools)**

> PyElftools contains Python disassembly functionality for ELF files. The
  [runner](#runner) uses this to derive virtual address information for CapDL
  specifications. You will need a fairly up to date version that supports ARM
  files, so you may need to build and install this from source.

**[CapDL Python module](https://github.com/seL4/python-capdl-tool)**

> This module contains functionality for managing and generating CapDL
  specifications in Python. If you are working in the larger CAmkES project
  repository, this is already available as a subrepository.

**[Expect](http://expect.sourceforge.net/)**

> Expect is a tool for automating interaction with a command line application.
  This is only required for running the test suite.

**[Jinja2](http://jinja.pocoo.org/docs/)**

> Jinja2 is a templating system primarily used for HTML targets. The CAmkES
  templates use Jinja2 for their functionality. This should be available in the
  default repositories of most Linux distributions and any recent version
  should be fine.

Some additional tools used by CAmkES in a seL4 build have their own
dependencies. These are:

**data-ordlist**

> This is a Haskell package for dealing with list structures. This is a
  dependency of the CapDL translator. It is installable from
  [cabal](http://www.haskell.org/cabal/).

**GCC**

> A C compiler is necessary for building any C-based CAmkES application.
  Obviously if building for a different target than your host machine you will
  need to a cross compiler.

**MissingH**

> A Haskell package providing extra standard library functionality. This is a
  dependency of the CapDL translator. It is installable from cabal.

**split**

> A Haskell package providing some extra functionality for splitting
  operations. Again, this is a dependency of the CapDL translator that is
  installable from cabal.

### Tutorial

This section is aimed at getting you up and running with CAmkES applications
and increase your familiarity with the CAmkES environment. We assume you are
working in the CAmkES project repository for this.

#### Running a Simple Example

There's an example application under apps/simple that involves two components,
echo and client, communicating over a single interface.

![Simple system](imgs/echo.png)

To build this example, from the top-level directory run:

```bash
make arm_simple_defconfig
make silentoldconfig
make
```

This produces an image images/simple-image-arm-imx31. To run this image in
qemu:

```bash
qemu-system-arm -M kzm -nographic -kernel \
  images/capdl-loader-experimental-image-arm-imx31
```

You should see debugging output from the system initialisation, followed by:

    echo_int: 42 -> 42
    echo_float: 273421.437500 -> 273421.437500
    echo_double: 273421.427400 -> 273421.427400
    echo_mix: 273421.427400 -> 273421
    echo_string: "hello world" -> "hello world"
    echo_parameter: 123 -> 123 (returned = 123)
    increment_parameter: 100 -> 101
    After the client

To understand what this example is doing, open the files
apps/simple/components/Echo/src/echo.c and
apps/simple/components/Client/src/client.c. The implementations of the echo
functions are in echo.c and they are called from client.c. The function call
itself happens over a seL4 endpoint. The connection between the two components
is described in apps/simple/simple.camkes, and the functional interface that
echo is providing is described in apps/simple/interfaces/Simple.idl4.

If you want to run this example on IA32, the commands are similar:

```bash
make x86_simple_defconfig
make silentoldconfig
make clean
make
qemu-system-i386 -nographic -m 512 \
  -kernel images/kernel-ia32-pc99 \
  -initrd images/capdl-loader-experimental-image-ia32-pc99
```

#### Creating An Application

Let's create some simple hello world applications using the different interface
types available in CAmkES. Create a new application directory with two component
types:

```bash
mkdir -p apps/helloworld/components/Hello
mkdir -p apps/helloworld/components/Client
```

Functional interfaces, referred to as procedures, are made up of a set of
methods. Define an interface that the components will communicate over and save
this under apps/helloworld/interfaces/MyInterface.idl4:

    /* apps/helloworld/interfaces/MyInterface.idl4 */
     
    procedure MyInterface {
      void print(in string message);
    };

This interface consists of a single method, print that takes an input parameter
of type string. Note that, although we are planning to implement this component
in C, interfaces are defined with abstract types that have equivalents in all
target languages. In the case of C, string maps to `char*`. Each component
needs a description of the interfaces it exposes or needs in so-called
Architecture Description Language. Create these in
apps/helloworld/components/Hello/Hello.camkes and
apps/helloworld/components/Client/Client.camkes.

    /* apps/helloworld/components/Hello/Hello.camkes */
     
    import "../../interfaces/MyInterface.idl4";

    component Hello {
      provides MyInterface inf;
    }

    /* apps/helloworld/components/Client/Client.camkes */
        
    import "../../interfaces/MyInterface.idl4";
         
    component Client {
      control;
      uses MyInterface iface;
    }

Note that each component description needs to import the interface file we
created above from apps/helloworld/interfaces. Import statements function
similar to C's `#include`, in that they can be enclosed in double quotes and
relative to the source file, or enclosed in angle brackets and refer to a
built-in file. The Hello component is to contain an implementation of
MyInterface and the Client component will expect to be provided with an
implementation of MyInterface. The control keyword indicates that Client is what
is called an active component. This means it will contain a main function
(prototyped as run) and have an active thread of control.

Create a file to describe the instantiation and structure of the system at
apps/helloworld/helloworld.camkes.

    /* apps/helloworld/helloworld.camkes */

    import <std_connector.camkes>;
    import "components/Hello/Hello.camkes";
    import "components/Client/Client.camkes";

    assembly {
      composition {
        component Hello h;
        component Client c;
        connection seL4RPC conn(from c.iface, to h.inf);
      }
    }

This file begins with several import statements that reference other files.
Hello.camkes and Client.camkes are the files we created above, while
std_connector.camkes is a built-in file that defines the standard CAmkES
connector types. The body of the system description instantiates each component
once, `h` of type `Hello` and `c` of type `Client`. The components' interfaces
are connected via a connection, `conn`, of type `seL4RPC`.

Now for the implementation of the components. Create a single source file for
Hello as apps/helloworld/components/Hello/src/hello.c:

```c
/* apps/helloworld/components/Hello/src/hello.c */

#include <Hello.h>
#include <stdio.h>
 
void inf__init(void) {
}
  
void inf_print(const char *message) {
  printf("Client says: %s\n", message);
}
```

The header Hello.h is generated by the CAmkES build system and contains
prototypes for functions related to MyInterface that this component needs to
implement. Note that the actual implementations of interface functions are
prefixed with the component-local name of the interface (inf from Hello.camkes
above) and an underscore. The function `inf__init` is for this component to do
any required initialisation. In the case of this example we have no
initialisation to perform.

Create a source file for Client as
apps/helloworld/components/Client/src/client.c that calls these functions as if
they are directly available to it:

```c
/* apps/helloworld/components/Client/src/client.c */

#include <Client.h>

int run(void) {
  const char *s = "hello world";
  iface_print(s);
  return 0;
}
```

The entry point of a CAmkES component is run.

The final thing is to add some build system boiler plate to be able to build
the system. Create apps/helloworld/Kconfig for the build system menu:

    config APP_HELLOWORLD
    bool "Hello world CAmkES application"
    default n
        help
            Hello world tutorial exercise.

Add a source line to the top-level Kconfig under the applications menu that
references this file:

    source "apps/helloworld/Kconfig"

You can now run `make menuconfig` from the top-level directory and select your
application from the Applications menu. Make sure you deselect the simple
application while you're here.

Copy one of the Makefiles from another application or create
apps/helloworld/Makefile from scratch:

```Makefile
# apps/helloworld/Makefile

TARGETS := helloworld.cdl
ADL := helloworld.camkes

Client_CFILES = components/Client/src/client.c
Hello_CFILES = components/Hello/src/hello.c
 
include ${SOURCE_DIR}/../../tools/camkes/camkes.mk
```

Create a dependency entry in apps/helloworld/Kbuild for your application:

```Makefile
apps-$(CONFIG_APP_HELLOWORLD) += helloworld
helloworld: libsel4 libmuslc libsel4platsupport \
  libsel4muslccamkes libsel4sync libsel4debug libsel4bench
```

You're now ready to compile and run this application:

```bash
make clean
make
qemu-system-arm -M kzm -nographic -kernel \
  images/capdl-loader-experimental-image-arm-imx31
```

If all goes well you should see:

    Client says: hello world

Congratulations, you've just made your first CAmkES application.

#### Under the Hood

We basically just wrote a verbose and roundabout Hello World example, so what
benefit is CAmkES providing here? Note how the function call between the two
components looks just like a normal function invocation in C, even though the
two components are actually in different address spaces. During compilation
so-called glue code is generated to connect the two components via a seL4
endpoint and transparently pass the function invocation and return over this
channel. The communication itself is abstracted in the ADL description in
apps/helloworld/helloworld.camkes. The connection type we used was seL4RPC, but
it is possible to use another connection type here without modifying the code of
the components themselves.

CAmkES provides some interface types for other modes of interaction than
function calls. Events can be used for asynchronous communication and data ports
for shared memory.

#### An Example of Events

Events are the CAmkES interface type for modelling asynchronous communication
between components. Like procedures, events connect a single component to
another single component, but the receiver of an event (called consumer in
CAmkES parlance) has several ways of receiving the event. The following walks
through an example demonstrating these.

Create a new application directory with two components:

```bash
mkdir -p apps/helloevent/components/Emitter
mkdir -p apps/helloevent/components/Consumer
```

Events, unlike procedures, do not need to be defined in a separate IDL file. You
can simply refer to the event type in your component ADL files and CAmkES will
infer an event type. Create the following description for Emitter:

    /* apps/helloevent/components/Emitter/Emitter.camkes */

    component Emitter {
      control;
      emits MyEvent e;
    }

This description says Emitter is an active component (the control keyword) and
it emits a single event called e of type MyEvent. Create some basic source code
for the component that does nothing except emit the event itself:

```c
/* apps/helloevent/components/Emitter/src/main.c */

#include <Emitter.h>
  
int run(void) {
  while (1) {
    e_emit();
  }
  return 0;
}
```

CAmkES provides an emit function to send the event.

Now let's create a description of the Consumer that will handle this event:

    /* apps/helloevent/components/Consumer/Consumer.camkes */

    component Consumer {
      control;
      consumes MyEvent s;
    }

Note that this component consumes (handles) an event of the same type. Let's
instantiate and connect these components together using another ADL file:

    /* apps/helloevent/helloevent.camkes */
        
    import <std_connector.camkes>;
    import "components/Emitter/Emitter.camkes";
    import "components/Consumer/Consumer.camkes";

    assembly {
      composition {
        component Emitter source;
        component Consumer sink;
        connection seL4Asynch channel(from source.e, to sink.s);
      }
    }

In this file, seL4Asynch is a seL4 specific connector for transmitting
asynchronous signals. The two instantiated components, source and sink are
connected over the connection channel.

As mentioned above, there are several ways for a component to receive an event.
The consumer can register a callback function to be invoked when the event is
received, they can call a blocking function that will return when the event is
received or they can call a polling function that returns whether an event has
arrived or not. Let's add some source code that uses all three:

```c
#include <stdio.h>
#include <Consumer.h>

static void handler(void) {
  static int fired = 0;
  printf("Callback fired!\n");
  if (!fired) {
    fired = 1;
    s_reg_callback(&handler);
  }
}

int run(void) {
  printf("Registering callback...\n");
  s_reg_callback(&handler);

  printf("Polling...\n");
  if (s_poll()) {
    printf("We found an event!\n");
  } else {
    printf("We didn't find an event\n");
  }

  printf("Waiting...\n");
  s_wait();
  printf("Unblocked by an event!\n");

  return 0;
}
```

Note that we re-register the callback during the first execution of the handler.
Callbacks are deregistered when invoked, so if you want the callback to fire
again when another event arrives you need to explicitly re-register it.

We now have everything we need to run this system. Add the appropriate
information to Kconfig, apps/helloevent/Kbuild, apps/helloevent/Kconfig and
apps/helloevent/Makefile as for the previous example. Compile the system and
run it with similar qemu commands to the previous example. If all goes well you
should see something like the following:

    Registering callback...
    Callback fired!
    Polling...
    We didn't find an event
    Waiting...
    Unblocked by an event!
    Callback fired!

Whether you find an event during polling will be a matter of the schedule that
seL4 uses to run the components. This covers all the functionality available
when using events. One final point that may not be obvious from the example is
that callbacks will always be fired in preference to polling/waiting. That is,
if a component registers a callback and then waits on an event to arrive, the
callback will be fired when the first instance of the event arrives and the wait
will return when/if the second instance of the event arrives.

#### An Example of Dataports

Dataports are CAmkES' abstraction of shared memory. Dataports, like other
interfaces, connect a single component to a single other component. Both
components get read/write access to the dataport. The default dataport type is
`Buf`, which is implemented as a byte array in C of size `PAGE_SIZE`.
Alternatively you can specify a user-defined type for the shared memory region.
This example will demonstrate both.

Create two components that will use a pair of dataports for communication:

```bash
mkdir -p apps/hellodataport/components/Ping
mkdir -p apps/hellodataport/components/Pong
```

Let's define a struct that will be used as one of the dataports:

```c
/* apps/hellodataport/include/porttype.h */
 
#ifndef _PORTTYPE_H_
#define _PORTTYPE_H_
  
typedef struct MyData {
  char data[10];
} MyData_t;
   
#endif
```

The build system puts some constraints on where included headers can reside so
we need to symlink this header into the place the build system will be
expecting it:

```bash
mkdir -p apps/hellodataport/components/Ping/include
ln -s ../../../include/porttype.h \
  apps/hellodataport/components/Ping/include/porttype.h
mkdir -p apps/hellodataport/components/Pong/include
ln -s ../../../include/porttype.h \
  apps/hellodataport/components/Pong/include/porttype.h
```

Now let's create an ADL description of the Ping component:

    /* apps/hellodataport/components/Ping/Ping.camkes */
        
    import "Porttype.idl4";

    component Ping {
      include "porttype.h";
      control;
      dataport Buf d1;
      dataport MyData_t d2;
    }

Note that we need to include the C header in the ADL. CAmkES does not actually
parse this header, but it needs to know to `#include` it whenever it references
the `MyData_t` type. Add a similar description for Pong:

    /* apps/hellodataport/components/Pong/Pong.camkes */

    import "Porttype.idl4";

    component Pong {
      include "porttype.h";
      control;
      dataport Buf s1;
      dataport MyData_t s2;
    }

Now we'll create some basic code for each component to use the dataports:

```c
/* apps/components/Ping/src/main.c */

#include <stdio.h>
#include <string.h>

#include <Ping.h>

#include <porttype.h>

int run(void) {
  char *hello = "hello";

  printf("Ping: sending %s...\n", hello);
  strcpy((void*)d1_data, hello);

  /* Wait for Pong to reply. We can assume d2_data is
   * zeroed on startup by seL4.
   */
  while (!d2_data->data[0]);
  printf("Ping: received %s.\n", d2_data->data);

  return 0;
}
```

```c
/* apps/components/Pong/src/main.c */

#include <stdio.h>
#include <string.h>

#include <Pong.h>

#include <porttype.h>

int run(void) {
  char *world = "world";

  /* Wait for Ping to message us. We can assume s1_data is
   * zeroed on startup by seL4.
   */
  while (!*(volatile char*)s1_data);
  printf("Pong: received %s\n", (volatile char*)s1_data);

  printf("Pong: sending %s...\n", world);
  strcpy((void*)s2_data->data, world);

  return 0;
}
```

Note that components generally need to use volatile variables when referring to
shared memory to prevent the compiler eliminating repeated reads and writes. A
real system would have a more complete communication protocol between the two
components, but for the purposes of this example spinning until a byte changes
is good enough. We're ready to connect all these sources together with a
top-level ADL file:

    /* apps/hellodataport/hellodataport.camkes */

    import <std_connector.camkes>;
    import "components/Ping/Ping.camkes";
    import "components/Pong/Pong.camkes";

    assembly {
      composition {
        component Ping ping;
        component Pong pong;

        connection seL4SharedData channel1(from ping.d1, to pong.s1);
        connection seL4SharedData channel2(from ping.d2, to pong.s2);
      }
    }

Add the now familiar apps/hellodataport/Kconfig, apps/hellodataport/Makefile,
Kconfig and apps/hellodataport/Kbuild. If you now compile and run the resulting
image you should see some output like the following:

    Ping: sending hello...
    Pong: received hello
    Pong: sending world...
    Ping: received world.

#### Tutorial Summary

You should now have a reasonably comprehensive understanding of the basic
connector functionality available in CAmkES. The other apps in the CAmkES
project repository provide some more diverse system examples.

### Overview

The various parts that comprise CAmkES can be used in several ways, including
executing a standalone tool as an end user or importing a Python module to
perform programmatic operations. These two uses are broken up into the sections
below. [Tools](#tools) describes how to invoke standalone CAmkES functionality
from the command line, and [Modules](#modules) describes how to import
and use the various functional units. Importing CAmkES functionality as a module
is strictly more powerful than running any of the command line tools, but usage
is more complicated. Note that these sections only describe external
interaction with these artefacts. If you are interested in the internals of
these you will need to refer to the [Developers](#developers) section.

### Tools

This section discusses the standalone tools that are part of the CAmkES
ecosystem. Each of these can be run from the command line with a shell script
wrapper that checks their dependencies:

```bash
camkes.sh toolname args...
```

The tools each take a subset of a common set of command line arguments. These
are described below. When an argument is only accepted by some of the tools,
this is noted. If no limitation is mentioned then the argument is accepted by
all tools.

**--allow-forward-references**  
**--disallow-forward-references**

> Some tokens in a CAmkES specification can represent references to an entity
  defined elsewhere. For example, in `connection Foo foo(from a.b, to c.d);` the
  token `Foo` refers to a connector that is defined elsewhere in the spec. The
  default behaviour is to only accept references to entities that have been
  _previously_ defined. These options allow more permisive references to entities
  defined anywhere or restore the default behaviour, respectively.

**--cache**, **-c**  
**--cache-dir**

> In a complicated system, the compilation itself can be quite time intensive.
  CAmkES implements a template cache that reduces recompilation time within and
  across builds. The --cache option has several different settings:

  * "off" (default) - do not use the cache at all
  * "on" (read/write) - fully enable cache functionality
  * "readonly" - retrieve previous work done from the cache, but do not save
    any new work
  * "writeonly" - save any new work done during this execution, but do not
    retrieve any previously completed work

> The last two settings are essentially only useful for debugging. The
  --cache-dir option allows you to specify a directory root for the cache if
  you don't want to use the default. These options are only available for the
  runner. For details on how the cache works internally, refer to the
  [Template Cache](#template-cache) section.

**--cpp**  
**--nocpp**

> Whether or not to run the C pre-processor over the ADL input specification
  before processing it. The ADL input specification, strictly, is not C source
  code, but sometimes it can be useful to have the ability to pre-process it as
  if it was. The CAmkES ADL grammar is sufficiently similar to C that you are
  unlikely to run into any problems in this respect. This option is only
  available for the runner.

**-D**, **--debug**  
**-q**, **--quiet**  
**-v**, **--verbose**

> Set the level of information and error reporting emitted. The last one of
  these options encountered on the command line takes precedence. Note that
  there is no option to set the default verbosity (which is more than --quiet,
  but less than --verbose). The verbosity setting is applied globally during
  the execution of a tool. For example, applying --debug to inspect a parsing
  problem in the runner will also generate debugging output from the lexing
  phase.

**--default-priority**

> Threads in a seL4 system are all configured with an initial priority. This
  can be tuned via attributes, but otherwise threads inherit a global default.
  This parameter allows you to set the global default. This option is only
  available for the runner.

**--elf**, **-E**

> Pass an ELF file that is to contribute to the final CapDL specification of a
  system. This parameter, that is only relevant for the runner, allows you to
  pass in the compiled ELF binary of one of your component instances. The
  CAmkES build system should take care of passing this option.

**-f FILE**, **--file FILE**

> Each tool accepts a list of input specifications. This argument adds FILE to
  the list of input files to parse. If you use this argument multiple times the
  order in which the input files are encountered on the command line will
  determine the order in which they are parsed. This argument is optional for
  some tools, which read from standard input if it is not given.

**-h**, **--help**

> Shows usage information and then exits.

**-I PATH**, **--import-path**

> CAmkES specifications can contain `import` statements that are either
  relative or builtin. Analogously to C pre-processor `#include` directives,
  builtin `import` statements use angle brackets, `import &lt;foo.camkes&gt;`.
  This option is similar to the C compiler flag, -I, and adds a directory to be
  searched for these builtin files. When resolving imports, directories will be
  searched in the order in which they are specified on the command line with
  the first match taking preference. Note, _unlike_ the C pre-processor this
  option _only_ affects searches for builtin imports. Relative imports are
  _always_ relative to the location they are included from.

**--item**, **-T**

> Specify the output you wish the runner to generate. The available options
  here are dependent on your input specification and it is best to look at
  examples to see what is expected following this option.

**--platform**, **-p**

> The target output platform. This determines some aspects of the environment
  that the template being rendered is expected to function in. This option is
  only relevant to the runner. Valid platforms are "seL4", "Linux" and "CIMP",
  the last being a verification framework.

**--post-render-edit**

> This option is only relevant to the runner and is used for debugging. When
  enabled, it drops you into an editor following the rendering of each
  template. The purpose of this is to allow you to manually tweak the output
  of a template on the fly during compilation.

**--profiler**  
**--profiler-log**

> This option enables profiling of the runner's execution for the purpose of
  debugging compilation performance. The default is for no profiling. Valid
  profilers are "internal", "native" and "aggregate". These are respectively,
  basic profiling timing, fine-grained cProfile data and aggregate cProfile
  data. If you are experienced with profiling Python code, you will find
  "native" the most comfortable. Otherwise "internal" is probably more
  intuitive. The --profiler-log option can be used to redirect the profiling
  data to somewhere other than stdout.

**-r**, **--resolve-imports**  
**-d**, **--dont-resolve-imports**

> CAmkES specifications can contain `import` statements that are directives to
  include another file at that point. The default behaviour when parsing one of
  these statements is to recurse into parsing the contents of that file. These
  two options re-enable the default and disable this behaviour, respectively.
  With import resolution disabled the imported files will not be opened and the
  resulting AST will still contain the original `import` statements.

**-R**, **--resolve-references**  
**--dont-resolve-references**

> After parsing the input specification(s) the tools will attempt to resolve
  references to the underlying entity they name. For example, in the statement
  `connection Foo foo(from a.b, to c.d);` the reference `Foo` will be resolved
  to the connector it references if possible. These options re-enable this
  default behaviour and inhibit reference resolution, respectively. Obviously
  with reference resolution disabled you may end up with references in the
  resulting AST.

**--templates**, **-t**

> You can use this option to add an extra directory to search for templates
  before the built-in location. This can allow you to extend the available
  templates or even override the built-in templates.

**--version**

> Print basic version information and then exit.

The following options are all related to runtime optimisations within the
templates. They are only relevant to the runner. Note that most of these are
highly seL4 specific and would make no sense in the context of another
platform.

**--frpc-lock-elision**  
**--fno-rpc-lock-elision**

> Locks are used within the seL4RPC connector templates to prevent threads
  interfering with each other's execution. When this option is enabled, CAmkES
  will determine when this lock is not required and remove it at compile-time.

**--fcall-leave-reply-cap**  
**--fno-call-leave-reply-cap**

> The seL4RPCCall connector needs to save a so-called reply cap on the
  receiver's side to prevent accidental deletion in the presence of
  interference from other interfaces. In certain circumstances there is
  actually no risk of the reply cap being deleted. With this option enabled,
  CAmkES will detect these scenarios and operate on the reply cap in place to
  avoid extra syscalls.

**--fspecialise-syscall-stubs**  
**--fno-specialise-syscall-stubs**

> In a system involving many small procedural interfaces which are individually
  providing so-called microservices, the overhead of seL4's syscall entry stubs
  becomes perceptible. In pathological cases they can even become a performance
  bottleneck. With this option enabled, CAmkES detects these small interfaces
  and emits a custom assembly syscall entry stub. Due to the extra knowledge of
  the execution environment that CAmkES has, these stubs can actually induce
  even lower overhead than optimal generalised stubs.

The following options are all related to verification of templates outputs and
are only relevant to the runner.

**--fprovide-tcb-caps**  
**--fno-provide-tcb-caps**

> By default each thread gets a cap to its own TCB. The only purpose of this is
  to allow it to suspend itself when it exits. These TCBs can complicate
  reasoning about a generated CapDL specification. This option elides these TCB
  caps at the cost of threads messily VM faulting when they exit.

**--fsupport-init**  
**--fno-support-init**

> By default, CAmkES provides a fairly rich initialisation environment. This
  includes features like automatic calls to `pre_init`. All this infrastructure
  can be disabled at an obvious loss of functionality, but with a less
  complicated resulting capability distribution and control flow.

#### Lint

CAmkES provides a lint tool, similar to [pylint](http://www.pylint.org/) or
[xmllint](http://xmlsoft.org/xmllint.html) that checks a CAmkES description for
syntax errors and inconsistencies. It is intended to be run as an interactive
sanity check over your specification and may generate both false positives and
false negatives. To run the tool, execute:

```bash
camkes.sh lint args...
```

A list of valid arguments is given in the [Tools](#tools) section above. When
reviewing a list of warnings or errors emitted the filename and line number may
be slightly off. This information comes from the lexer and the inaccuracy seems
to be unavoidable as it does not provide exact line numbers that correspond to
token locations.

The lint tool is designed to be easily extensible by adding extra checks. You
can see the existing checks in camkes/lint/checks.py. To implement a new check
add a function to this file that accepts a list of `ASTObject`s and yields
instances of the class `Problem`. The checks that are executed are determined
by the `CHECKS` list in this file, so remember to add your function to this list
to enable it.

Note that the current checks are very limited as this tool has not seen much
use.

#### Parser

The standalone parser can be used for normalising specifications. To run it:

```bash
camkes.sh parser args...
```

Some examples:

```bash
camkes.sh parser --input=camkes --output=camkes
```

### Modules

Each subset of CAmkES functionality is encapsulate in a Python module that
defines exactly what functions and variables are exported. The APIs of these
are described below and usage should be reasonably straightforward. To import
any of these modules the top-level directory of this distribution should be in
your `PYTHONPATH` environment variable. The available modules are:

**[camkes.ast](#camkes.ast)**

> Definitions of objects that can appear in the result of parsing a CAmkES
  specification. If you want to reference the types of objects in a resulting
  AST you will need to import this.

**camkes.internal**

> Functionality used by other CAmkES modules. You should not import this
  module.

**[camkes.lint](#camkes.lint)**

> It is unlikely you would want to import the functionality of the
  [lint](#lint) tool to use programmatically as it is primarily an end user
  debugging aid. However, if you do so want to it is available.

**[camkes.parser](#camkes.parser)**

> To parse an input specification in memory or to do post-processing
  manipulations on a specification-derived AST you will need to import this
  module. The [runner](#runner) imports this module to perform its job.

**camkes.runner**

> This module is available, but does not export any symbols. You should never
  need to import it.

**[camkes.templates](#camkes.templates)**

> If you need to lookup builtin templates you will need to import this module.
  Note that this module does not contain any template _instantiation_ logic.

#### camkes.ast

There is no active functionality in this module, and thus no real API as such.
It simply defines a set of types to be used in an AST derived from parsed
input.

One of the AST objects is a class, `Reference`, which is inherited by a couple
of other classes. Objects of these classes are used in the AST to represent
symbols that refer to entities that are defined elsewhere. References can be
either resolved or unresolved, meaning they can point at an entity whose
definition has been located or they can point at an as-yet undiscovered entity.
When you encounter a reference you can test whether it is resolved or not based
on its `_referent` member. Resolved references will have their `_referent` set
to the entity they reference, which unresolved references will have their
`_referent` set to `None`.

In the code and in this document there is some discussion of 'collapsing' AST
references. This is meant to refer to replacing the `Reference` object in the
AST by the entity to which it refers. Note that this needs to be done by
reference so that you still only end up with a single copy of the entity, but
multiple pointers to it.

#### camkes.parser

If you need to manipulate the AST, rather than just simply printing it
out, you will want to import the parser as a module into your own code. After
importing this module, you can interact with the parser through the following
API.

<!-- TODO: This section probably needs an update -->

**`dedupe(ast)`**

> Remove duplicate entries from the AST list and return the deduped list. This
  is useful for removing entries that are duplicate in the AST because they are
  seen more than once during parsing (e.g. because one of the input files is
  imported in more than one place). Note that you should run this *before*
  resolving references or you may end up removing AST entries that are
  referenced by other entries.

**`parse_to_ast(s)`**

> Parse the input string `s` and return the
  resulting derived list of AST objects.

**`pretty(s)`**

> Return a nicely formatted string representation of the string `s`.

**`resolve_imports(ast, curdir, includepath=None)`**

> This function attempts to resolve imports
  to existing files and parse these files.
  `ast` is a list of AST objects to resolve. Import statements can be either relative
  (using "" as delimiters) or builtin (using <> as delimiters), similar to
  C-style #includes. Relative imports are resolved in relation to `curdir` and
  builtin imports are resolved in relation to `includepath`, taking the first
  match in the case of multiple matching files.

> The function returns a pair, containing the AST as the first member and a
  list of files that were read during the resolution as the second member.

**`resolve_references(ast, allow_forward)`**

> Some input grammars, like "camkes" support referring to grammar entities by
  reference. E.g. a statement like `component foo bar;` instantiates a
  component `bar` of type `foo`. Here, `foo` is a reference to a previously
  defined component type. References like this will appear in the initial AST
  as objects of type `Reference`.

> This function attempts to resolve these to objects defined elsewhere in the
  AST. `allow_forward` indicates whether objects after the current point should
  be considered when resolving symbols. Note that references can still exist in
  the returned AST if they could not be resolved to any existing object.

**`show(o)`**

> Returns a string representing the AST object (or list of objects) `o`.

#### camkes.templates

This module contains functionality for looking up builtin templates. The
templates themselves are actually stored in this directory (camkes/templates)
as well to reduce confusion. As a brief disclaimer, despite containing the
least code of any of the CAmkES modules, camkes.templates is by far the most
dense and complicated part of the CAmkES ecosystem. This is not intended to put
you off using or modifying this module, but is just a word of caution. The
description below only describes the externally facing behaviour of this
module. If you need to understand how template lookups actually work you will
need to read the source code and comments.

The API only contains a single class through which all access is intended to
flow.

`Templates.`**`__init__(self, platform, **kwargs)`**

> Create a new template store in which templates can later be looked up. The
  category of templates that are available from this store is specialised via
  **`platform`**. At time of writing the valid values of **`platform`** are
  'seL4', 'CIMP' and 'GraphViz'. When templates are looked up the lookup itself
  is narrowed by the extra parameters passed in **`kwargs`**. It may be
  difficult to follow the effects of this, so if in doubt refer to the usage in
  `camkes/runner/__main__.py`.

`Templates.`**`add_root(self, root)`**

> Add a directory to be searched for templates when performing lookups. This
  directory is added _before_ existing directories, which allows you to
  overwrite builtin templates if you wish.

`Templates.`**`get_roots(self)`**

> Return the list of directories that are searched for templates. Note that if
  you are the only client operating on this `Templates` object you will know
  the contents of this list anyway, but this function is provided for
  convenience.

`Templates.`**`add(self, connector_name, path, template)`**

> Add a template to the lookup dictionary, such that it can later be returned
  in a template lookup. Only connector templates can be added currently (i.e.
  component templates and top-level templates cannot be added). The caller
  provides the **`connector_name`** this template applies to (e.g.
  'seL4MyConnector'), a partial lookup **`path`** to the template (e.g.
  'from.source') and a roots-relative path to the **`template`** itself. Again,
  this function is sufficiently complicated that it may be easier to comprehend
  its usage from reading `camkes/runner/__main__.py`.

`Templates.`**`lookup(self, path, entity=None)`**

> Locate and return a template. The **`path`** provided should be a full lookup
  path from the second-level of the lookup dictionary (i.e. not including the
  platform prefix). For example, a valid **`path`** might be
  'seL4RPC.from.source'. If you provide an **`entity`** this is used as a guard
  on the lookup. The guards come into play when looking up connector templates.
  In this situation the connector type of the connection you pass in as
  **`entity`** will be used to determine if a given template matches your
  lookup. This function returns `None` if a matching template can't be found.

### Runtime API

This section describes the environment in which you, as a user, will find
yourself writing code. Standard C library functionality is available, but as a
CAmkES application, there is also extra functionality provided by generated
code and supporting libraries. This extra functionality is what is documented
in this section.

Parts of the functionality discussed below are provided by the library,
libsel4camkes. In a typical seL4 project the user would need to specify that
they want to link against this library. This is not required in CAmkES as it is
assumed you always want to link against this library. For more information from
a CAmkES developer's point of view, see [Core Libraries](#core-libraries). The
API is bidirectional in a sense, in that some of the functions below are called
by CAmkES code and expected to be provided by the user. This is noted in their
descriptions.

The following types are available at runtime from the C context of a component:

**`Buf`** (`#include <camkes/dataport.h>`)

> The underlying type of a dataport. A user is never expected to instantiate
  one of these manually, but they are free to do so if they wish.

**`camkes_error_handler_t`** (`#include <camkes/error.h>`)
> The type of an error handler for dealing with errors originating in glue
  code. For more information about this see
  [Error Handling](#error-handling).

**`camkes_tls_t`** (`#include <camkes/tls.h>`)

> Thread-local storage metadata. This captures some necessary information for
  constructing a thread context inside templates. A user is never expected to
  instantiate or deal with one of these, but they are free to do so if they
  wish.

**`dataport_ptr_t`** (`#include <camkes/dataport.h>`)

> A component-independent representation of a pointer into a dataport. This is
  intended to be an opaque type to the user that is only ever used via the
  `dataport_wrap_ptr` and `dataport_unwrap_ptr` functions.

The following variables are available:

**_`dataport`_** (`#include "`_`component`_`"`)

> If a component has a dataport they will be provided with a symbol of the
  dataport's name that is a pointer of the type they specified in their CAmkES
  specification. As mentioned previously, the default type is `Buf`.

The following functions are available at runtime:

**`camkes_error_handler_t camkes_register_error_handler(camkes_error_handler_t handler)`** (`#include <camkes/error.h>`)  
**`camkes_error_handler_t `&nbsp;_`interface`_`_register_error_handler(camkes_error_handler_t handler)`** (`#include <camkes/error.h>`)

> Register a component-wide or interface-specific error handler, respectively.
  These functions return the previous error handler or `NULL` if there was no
  previously installed error handler. For more information see
  [Error Handling](#error-handling).

**`dataport_ptr_t dataport_wrap_ptr(void *ptr)`** (`#include <camkes/dataport.h>`)  
**`void *dataport_unwrap_ptr(dataport_ptr_t ptr)`** (`#include <camkes/dataport.h>`)

> Utility functions for creating and destroying a component-independent
  representation of a pointer into a dataport. This `dataport_ptr_t` can be
  passed over a procedure interface to be unwrapped by the receiving component.
  Unwrapping will fail if the underlying pointer is not into a dataport that is
  shared with the receiver. `dataport_unwrap_ptr` returns `NULL` on failure.

**`void *camkes_dma_alloc(size_t size, int align)`** (`#include <camkes/dma.h>`)  
**`void camkes_dma_free(void *ptr, size_t size)`** (`#include <camkes/dma.h>`)

> Allocator for DMA device operations. These are closely linked with the DMA
  pool functionality, as the allocation is backed by this pool.

**`uintptr_t camkes_dma_get_paddr(void *ptr)`** (`#include <camkes/dma.h>`)

> Translate a pointer into a DMA region into a physical address. This function
  assumes that the pointer you are passing in is to a byte within a region
  allocated to you by `camkes_dma_alloc_page`. The reason for needing to obtain
  the physical address of a pointer is typically to pass to a device that is
  going to access this region outside of the scope of the MMU. For more
  information, see the [DMA](#direct-memory-access) section below.

**`void *camkes_io_map(void *cookie, uintptr_t paddr, size_t size, int cached, ps_mem_flags_t flags)`** (`#include <camkes/io.h>`)
> Lookup the translation to virtual address from the physical address of a
  memory-mapped IO device. This function is primarily to ease interaction with
  libplatsupport infrastructure, so refer to its documentation where
  appropriate.

**`int camkes_io_mapper(ps_io_mapper_t *mapper)`** (`#include <camkes/io.h>`)
> Construct an IO mapping structure to pass to libplatsupport. See source
  comments for more information about how to use this.

**`int camkes_io_ops(ps_io_ops_t *ops)`** (`#include <camkes/io.h>`)
> Construct an IO operations structure to pass to libplatsupport. See source
  comments for more information about how to use this.

**`int camkes_io_port_in(void *cookie, uint32_t port, int io_size, uint32_t *result)`** (`#include <camkes/io.h>`)
**`int camkes_io_port_out(void *cookie, uint32_t port, int io_size, uint32_t val)`** (`#include <camkes/io.h>`)
> Read from or write to a hardware IO port. This function is primarily to ease
  interaction with libplatsupport infrastructure, so refer to its documentation
  where appropriate.

**`int camkes_io_port_ops(ps_io_port_ops_t *ops)`** (`#include <camkes/io.h>`)
> Construct an IO port access structure to pass to libplatsupport. See source
  comments for more information about how to use this.

**`const char *get_instance_name(void)`** (`#include "`_`component`_`"`)

> Returns the name of this component instance. This can be helpful if you want
  to write component functionality that has different behaviour depending on
  which instance it is.

**`int`&nbsp;_`instance`_`_main(int thread_id)`**

> A component instance's entry point. This is generated by the platform and
  invokes the user's `run` function when complete.

**`int main(int thread_id)`** (in libsel4camkes.a)

> This function &mdash; the C entry point to a component &mdash; is provided by
  the platform. Components should not provide their own `main`. This function
  invokes _`instance`_`_main` when it has completed initialisation. The reason
  for these chained entry points is to support single address space components,
  in which all threads enter via `main` and then branch to their respective
  instance entry points, _`instance`_`_main`.

**`int run(void)`**

> This function is expected to be provided by the user in a control component.
  It is invoked by `main` after component initialisation is complete.

**`NORETURN _start(int thread_id)`** (in libsel4camkes.a)

> This function provides the assembly entry point of a component and consists
  of a brief trampoline to `main`. The user can override this if they wish, but
  it is unwise to do this unless you have a deep understanding of the runtime
  environment.

**`void pre_init(void)`**

> This function can be optionally provided by the user. If it is present, it
  will be invoked _before_ the component's interfaces' init functions have
  executed. Be aware that you will not have full runtime support in this
  function. For example, interfaces cannot be expected to be accessible.

**`void`&nbsp;_`interface`_`__init(void)`**

> For each incoming or outgoing interface a user can optionally provide this
  function. If it is present it will be invoked _after_ the component's
  pre-init function, but _before_ its post-init function. The same caveats about
  the runtime environment from above are applicable here.

**`void post_init(void)`**

> This function can be optionally provided by the user. If it is present, it
  will be invoked _after_ the component's pre-init function and after all
  interfaces' init functions, but _before_ any interface enters its run
  function.

**`int`&nbsp;_`interface`_`__run(void)`**

> This function can be provided for any incoming or outgoing interface. If it
  is present, it will be invoked after all pre- and post-init functions have
  run.

**_`return`_&nbsp;_`procedure`_`_`_`method`_`(`_`args...`_`)`** (`#include "`_`component`_`"`)

> In a component that provides a procedure interface, things are somewhat
  reversed and the implementation calls functions that you are expected to
  provide. For each method in the procedure you are expected to provide a
  matching implementation. In a component that uses a procedure interface,
  functions of this form are available for you to call.
  will expect.

**`void`&nbsp;_`event`_`_emit(void)`** (`#include "`_`component`_`"`)

> In a component that emits an event a function prefixed with the event's name
  is available that causes the event to be sent.

**`void`&nbsp;_`event`_`_poll(void)`** (`#include "`_`component`_`"`)

> In a component that consumes an event a function prefixed with the event's
  name is available that returns whether there is a pending event. Note, this
  function never blocks.

**`int`&nbsp;_`event`_`_reg_callback(void (*callback)(void*), void *arg)`** (`#include "`_`component`_`"`)

> In a component that consumes an event a function prefixed with the event's
  name is available for registering a callback for this event. When the event
  is received, the provided function will be invoked with the argument provided
  when registering the callback. Note that registered
  callbacks take precedence over threads blocked on calls to _`event`_`_wait`.
  _`event`_`_reg_callback` returns 0 on success and non-zero if the callback
  could not be registered.

**`void`&nbsp;_`event`_`_wait(void)`** (`#include "`_`component`_`"`)

> In a component that consumes an event a function prefixed with the event's
  name is available that blocks until the event is received.

### Mutexes and Semaphores

CAmkES provides two primitives for intra-component mutual exclusion. Mutexes
and semaphores are declared similarly as properties of a component definition:

    component Foo {
      has mutex m;
      has semaphore s;
    }

By default semaphores have a count (initial value) of 1, but this can be
adjusted using an attribute:

    assembly {
      composition {
        component Foo f;
        ...
      }
      configuration {
        f.s_value = 4;
        ...
      }
    }

An application can lock or unlock a declared mutex and call post or wait on a
declared semaphore. For example, for the above declarations, the following
functions are available at runtime:

```c
/* Lock mutex m */
int m_lock(void);

/* Unlock mutex m */
int m_unlock(void);

/* Wait on semaphore s */
int s_wait(void);

/* Try to wait on semaphore s */
int s_trywait(void);

/* Post to semaphore s */
int s_post(void);
```

The CAmkES mutexes and semaphores have the behaviour you would expect from an
seL4 or pthreads implementation.

There is no native support for inter-component locks. However, it is possible
to construct these on top of the CAmkES platform. An example of how you would
do this is shown in the lockserver example application in the CAmkES project
repository.

### Direct Memory Access

Direct Memory Access (DMA) is a hardware feature that allows devices to read
and write memory without going via the CPU. It is intended to give a fast I/O
path to devices, for which memory access is usually the bottleneck.

This only has specific relevance in the context of CAmkES because on platforms
without an [IOMMU](https://en.wikipedia.org/wiki/IOMMU) devices perform DMA
accesses on physical memory, rather than virtual memory. The implications of
this are that, when a device is being directed to perform I/O by a driver, it
needs to know the physical address(es) of the memory it is about to access. On
seL4 reversing a virtual memory mapping requires specific capability operations
and thus CAmkES needs to be aware of any memory region which you intend to use
for DMA transfers.

To allocate some memory for DMA within a specific component instance you
describe a DMA pool with a size in bytes. For example,

    assembly {
      composition {
        component Foo f;
        ...
      }
      configuration {
        f.dma_pool = 8192;
      }
    }

This declares an 8KB pool of memory that is available for DMA operations.
Within the component you must allocate and release pointers into this region
with the `camkes_dma_alloc` and `camkes_dma_free` functions described above.
The allocation function accepts a size and alignment constraint, but be aware
that allocation may not be efficient or guaranteed when requesting more than
4Kb. Note that if you declare a DMA pool that is not page-aligned (4K on the
platforms we support) it will automatically be rounded up.

### Error Handling

Some runtime conditions can lead to an error in the glue code. For example, if
an interface accepts a string parameter and the caller passes a string that is
too large to fit in the IPC buffer. Errors can also arise in glue code if your
user code is not well-behaved and attempts to operate directly on capabilities.
The glue code attempts to handle all errors occurring from user mistakes and
malicious user code, to the best of its abilities. It also attempts to handle
errors that occur as a result of unexpected runtime conditions. For example,
accesses to a device that unexpectedly is not found at runtime.

The mode of error handling can be configured at compile-time, but the default
mode is generally the only relevant one you will need. It allows for runtime
handling of errors. By default, all errors cause a diagnostic message and a
system halt on a debug kernel. To alter this behaviour, user code can call the
function `camkes_register_error_handler` (described in
[Runtime API](#runtime-api)) and provide their own error handling function.
The user's error handling will thenceforth be invoked by glue code whenever an
error is detected. The error handling function should return one of the
following values, documented further in `camkes/error.h`, that indicate to the
glue code how it should proceed:

* `CEA_DISCARD` — Ignore whatever message or request was currently being
  handled and return to the original calling function of the user or an event
  loop as appropriate. This is typically the failure mode you want for servers
  that are intended to be robust against denial-of-service attacks from
  malicious clients.

* `CEA_IGNORE` — Pretend the error was not detected and continue executing.
  This is almost never the response you want to take, but it can be useful for
  debugging or masking spurious errors.

* `CEA_ABORT` — Terminate the current thread with failure status. This is a
  fail-stop response, though note it will not halt the rest of the system. If
  the glue code is currently handling a request on behalf of a client, the
  client will likely end up stuck blocked waiting for a response.

* `CEA_HALT` — Halt the entire system. This is only possible on a debug
  kernel. On a release kernel it will act identically to `CEA_ABORT`.

To conditionally determine which response to return, the error handler is
passed a structure that describes the error that was detected. For details on
this structure, refer to `camkes/error.h`.

The mechanism just described allows for handling errors at a component-wide
level. In a more complicated component, there are often notional subsystems
that want to be able to handle their own errors independently. For this there
are interface-specific error handlers. Each interface has its own error handler
registration function as _`interface`_`_register_error_handler`. Any interface that
does not have a registered interface-specific error handler will default to the
component-wide error handler.

### Custom Attributes

CAmkES allows the programmer to define arbitrary attributes of components.

    component Foo {
      attribute string a;
      attribute int b;
    }

These attributes are set in the configuration section of the assembly:

    assembly {
      composition {
        component Foo f;
        ...
      }
      configuration {
        f.a = "Hello, World!";
        f.b = 42;
        ...
      }
    }

This results in the specified values being available as global variables
in the glue code with the same name as the attribute.

```c
const char * a = "Hello, World!";
const int b = 42;
```

### Hardware Components

A hardware component represents an interface to hardware in the form of a component.
Declaring a component with the `hardware` keyword creates a hardware component.

    component Device {
      hardware;

      provides IOPort io_port;
      emits Interrupt irq;
      dataport Buf mem;
    }

When an interface of a device component instance is connected to a regular
component, that component gets access to that device via some 
hardware interface (interface here refers to a means of interacting with
hardware - not a CAmkES interface).
The type of hardware interface depends on the type of CAmkES interface,
and the connector used. Available connectors for hardware, and their
corresponding hardware interfaces are listed below.

**Interface:** procedure            \
**Keyword:** `provides`               \
**Connector:** `seL4HardwareIOPort`   \
**Description:**
When using `IOPort` as the interface type, this provides access to IO ports. The connected 
component gets access to the methods in the `IOPort` interface, which allow sending and receiving 
data over IO ports. This is specific to the IA32 architecture.

**Interface:** event                    \
**Keyword:** `emits`                      \
**Connector:** `seL4HardwareInterrupt`    \
**Description:**
An event is emitted when an interrupt occurs.

**Interface:** port                 \
**Keyword:** `dataport`              \
**Connector:** `seL4HardwareMMIO`     \
**Description:**
Memory mapped registers can be accessed via the shared memory.

The following shows an example of connecting a hardware component to a driver
component. Note the order of arguments to the connection. `seL4HardwareInterrupt` requires
the hardware interface on the `from` side of the connection, whereas the other connectors
require the hardware interface on the `to` side.

    component Driver {
      uses IOPort io_port;
      consumes Interrupt irq;
      dataport Buf mem;
    }

    assembly {
      composition {
        component Device dev;
        component Driver drv;
        ...
        connection seL4HardwareIOPort ioport_c(from drv.io_port, to dev.io_port);
        connection seL4HardwareInterrupt irq_c(from dev.irq, to drv.irq);
        connection seL4HardwareMMIO mmio_c(from drv.mem, to dev.mem);
      }
    }

#### Configuration

Each type of hardware component interface has some configuration required for it
to work. This is done by setting attributes of instances of device components.

##### MMIO
The physical address of the memory, and size (in bytes) to make available
to a connected component must be specified. The example below specifies that
the port named `mem` of the component instance `d` is a 0x1000 byte region
starting at physical address 0xE0000000.

    component Device {
      hardware;

      dataport Buf mem;
      ...
    }

    assembly {
      composition {
        component Device d;
        ...
      }
      configuration {
        d.mem_attributes = "0xE0000000:0x1000";
        ...
      }
    }

##### Interrupts
The interrupt number must be specified. The example below specifies that
the event will be emitted when interrupt number 2 is received.

    component Device {
      hardware;

      emits Interrupt irq;
      ...
    }

    assembly {
      composition {
        component Device d;
        ...
      }
      configuration {
        d.irq_attributes = 2;
        ...
      }
    }

##### IO Ports
The allowable range of IO Ports must be specified.
The example below specifies that the hardware component instance
`d` may access IO ports greater than or equal to 0x60, and less 
than 0x64.

    component Device {
      hardware;
        
      provides IOPort io_port;
      ...
    }

    assembly {
      composition {
        component Device d;
        ...
      }
      configuration {
        d.io_port_attributes = "0x60:0x64";
        ...
      }
    }

### Port Privileges

CAmkES allows the programmer to specify access rights that instances have over the ports
connecting them to other instances. This is done by setting the `from_access` and `to_access`
attributes of the port connection. The value of the attribute must be a string containing
the letters "R", "W" and "X" (or "G"), giving the instance on specified side of the connection
read, write and execute privileges over the shared region of memory. If left unspecified,
read/write access will be given.

In the example below, instance `f` has read-only access to `port_a`, and instance `b` has
read/write access to `port_a`. Instance `b` has read-only access to `port_b`. Instance `a`
has read/write access to `port_b` even though it's not explicitly stated, as this is the
default.

    component Foo {
      dataport Buf data_a;
      dataport Buf data_b;
    }

    component Bar {
      dataport Buf data_a;
      dataport Buf data_b;
    }

    assembly {
      composition {
        component Foo f;
        component Bar b;
        ...
        connection seL4SharedMemory port_a(from f.data_a, to b.data_a);
        connection seL4SharedMemory port_b(from f.data_b, to b.data_b);
        ...
      }
      configuration {
        port_a.from_access = "R";
        port_a.to_access = "RW;
        port_b.to_access = "R";
        ...
      }
    }

### Thread Priorities

Each thread in a CAmkES system has a priority that determines how it is
scheduled by seL4. These priorities default to a value given by the
`--default-priority` command-line argument to the runner. In a given system, it
it possible to adjust the priority of a specific thread with an attribute that
has specific semantics. To adjust the priority of the control thread (the
thread that calls `run`), use the `_control_priority` attribute:

    assembly {
      composition {
        component Foo f;
        ...
      }
      configuration {
        f._control_priority = 100;
      }
    }

To adjust the priority of an interface thread, use an attribute named with the
name of the interface and the suffix ``_priority'':

    component Foo {
      uses MyInterface i;
    }

    assembly {
      composition {
        component Foo f;
        ...
      }
      configuration {
        f.i_priority = 100;
      }
    }

For more information about the specifics of the seL4 scheduler, please refer to
the seL4 documentation.

### Scheduling Domains

In CAmkES, it is possible to specify the domain each thread belongs to, by setting attributes.
Each interface of each component instance will have an associated thread. Additionally, components
with a thread of control (indicated by the `control` keyword in their component definition) will
have an additional thread. For interface threads, their domain can be specified by setting the
attribute `<interface>_domain` of the instance. For control threads, the attribute `_control_domain`
of the instance can be set.

    component Foo {
      control;
      uses iface i;
    }

    component Bar {
      provides iface o;
    }

    assembly {
      composition {
        component Foo f;
        component Bar b;
        connection seL4RPC c(from f.i, to b.o);
        ...
      }
      configuration {
        f._control_domain = 0;  // domain of control thread of f
        b.o_domain = 1;         // domain of o interface of b
        ...
      }
    }

### Multi-Assembly Applications

CAmkES allows programmers to define an arbitrary number of assemblies for their application.
Different assemblies may appear in different files, provided that they are appropriately
included in the main ast file. At compile time, the bodies of each
assembly are merged together, with all declared names remaining the same.
Thus, naming conflicts can occur on items declared in different assemblies.

    assembly {
      composition {
        component Foo f;
      }
    }

    assembly {
      composition {
        component Bar b;
        connection seL4RPC c(from f.a, to b.a);
      }
      configuration {
        f.some_attribute = 0;
      }
    }

The example above is equivalent to:
    
    assembly {
      composition {
        component Foo f;
        component Bar b;
        connection seL4RPC c(from f.a, to b.a);
      }
      configuration {
        f.some_attribute = 0;
      }
    }

### Hierarchical Components

#### Syntax

A component definition may include a composition and configuration section.
The composition and configuration sections must be the last items in the component definition.
The composition and configuration sections may appear in any order. A composition section
can be included without a configuration, however a configuration section is only allowed
if there is a composition.

    component Foo_Impl {
      provides iface_a a_impl;
      attribute string str;
    }

    component Foo {
      provides iface_a a;

      composition {
        component Foo_Impl fi;
        connection ExportRPC exp(from a, to fi.a_impl);
      } 
      configuration {
        fi.str = "Hello, World!";
      }
    }

    component Bar {
      control;
      uses iface_a a;
    }

    assembly {
      composition {
        component Foo f;
        component Bar b;
        connection seL4RPC c(from b.a, to f.a);
      }
    }

In the example above, the component `Foo` exposes a virtual interface `a`,
which is exported from the interface `a_impl` of the component instance `fi` of type `Foo_Impl`.

#### Hierarchy Resolution

Prior to compilation, the AST representing the system is transformed to remove all
hierarchical components. For each instance of a compound component, any internal instances 
and internal connections declared
inside the component are copied into the top-level assembly with the compound component instance's
name prepended to their own. 
Each appearance of a virtual interface of some compound component instance 
in a connection in the top-level assembly, is replaced
with the exported interface of the internal instance copied into the top-level assembly
while resolving that compound component instance.
Then, for each compound component, all virtual interfaces are removed.
If this results in any components with no interfaces, these components, and all instances
of such components, are removed from the specification.

The example above would be converted into the following:
     
    component Foo_Impl {
      provides iface_a a_impl;
      attribute string str;
    }
    
    component Bar {
      control;
      uses iface_a a;
    }
    assembly {
      composition {
        component Bar b;
        component Foo_Impl f_fi;
        connection seL4RPC c(from b.a, to f_fi.a_impl);
      }
      configuration {
        f_fi.str = "Hello, World!";
      }
    }

#### Export Connectors

The `ExportRPC` connector in the example above is an Export Connector.
Recall from the [Terminology](#terminology) section, that an export connector associates 
a virtual interface of a compound component
with an interface of an internal instance declared in the composition section
of that component. `ExportRPC` can be used to export procedural interfaces.
There is a similar export connector available for each type of interface:

- _ExportRPC_ exports a procedural interface
- _ExportAsync_ exports an event interface
- _ExportData_ exports a port interface

When a virtual interface of a compound component instance appears in a connection
in the top-level assembly, the side of the connection with the virtual interface
in this connection must be the same as the side of the exported interface
in the export connection in the compound component. That is, they must both
appear on the `to` side, or the `from` side of their respective connections.

    component Foo {
      provides iface_a a;

      composition {
        component Foo_Impl fi;
        
        // fi.a_impl is the exported interface, and appears on the 'to' side
        connection ExportRPC exp(from a, to fi.a_impl); 
      } 
    }

    component Bar {
      control;
      uses iface_a a;
    }

    assembly {
      composition {
        component Foo f;
        component Bar b;
        
        // f.a is the virtual interface, and appears on the 'to' side
        connection seL4RPC c(from b.a, to f.a);
      }
    }

The example above is correct, as the exported interface `fi.a_impl` in the compound component
definition, and the virtual interface `f.a` in the top-level assembly, both appear on the
`to` side of their connections.

#### Examples

##### Connecting multiple compound components
It's possible for both sides of a connection to be virtual interfaces:
    
    component Foo_Impl {
      provides iface_a a_impl;
    }

    component Bar_Impl {
      uses iface_a a_usage; 
    }

    component Foo {
      provides iface_a a;

      composition {
        component Foo_Impl fi;
        connection ExportRPC exp(from a, to fi.a_impl);
      } 
    }

    component Bar {
      uses iface_a a;

      composition {
        component Bar_Impl bi;
        connection ExportRPC exp(from bi.a_usage, to a);
      }
    }

    assembly {
      composition {
        component Foo f;
        component Bar b;
        connection seL4RPC c(from b.a, to f.a);
      }
    }

This example compiles to:

    component Foo_Impl {
      provides iface_a a_impl;
    }

    component Bar_Impl {
      uses iface_a a_usage; 
    }

    assembly {
      composition {
        component Foo_Impl f_fi;
        component Bar_Impl b_bi;
        connection seL4RPC c(from b_bi.a_usage, to f_fi.a_impl);
      }
    }

##### Compound component with non-virtual interfaces

A component can have both virtual and implemented interfaces:

    component Foo_Impl {
      provides iface_a a_impl;
    }

    component Foo {
      provides iface_a a;
      provides iface_b b;

      composition {
        component Foo_Impl fi;
        connection ExportRPC exp(from a, to fi.a_impl);
      }
    }

    component Bar {
      uses iface_a a;
      uses iface_b b;
    }
    
    assembly {
      composition {
        component Foo f;
        component Bar b;
        connection seL4RPC c(from b.a, to f.a);
        connection seL4RPC c(from b.b, to f.b);
      }
    }

This example compiles to:
    
    component Foo_Impl {
      provides iface_a a_impl;
    }

    component Foo {
      provides iface_b b;
    }

    component Bar {
      uses iface_a a;
      uses iface_b b;
    }
    
    assembly {
      composition {
        component Foo f;
        component Bar b;
        component Foo_Impl f_fi;
        connection seL4RPC c(from b.a, to f_fi.a_impl);
        connection seL4RPC c(from b.b, to f.b);
      }
    }

##### Deeper Hierarchy

So far, each example has had a compound component containing only non-compound component instances.
It's possible to have a hierarchy of components of an arbitrary depth.

    component A_Piece1 {
      provides a_piece ap;
    }

    component A_Piece2 {
      uses a_piece ap;
      provides iface_a a_impl;
    }

    component Foo_Impl {
      provides iface_a a_impl;

      composition {
        component A_Piece1 a1;
        component A_Piece2 a2;
        connection seL4RPC c(from a1.ap, to a2.ap);
        connection ExportRPC exp(from a_impl, to a2.a_impl);
      }
    }

    component Foo {
      provides iface_a a;

      composition {
        component Foo_Impl fi;
        connection ExportRPC exp(from a, to fi.a_impl);
      }
    }

    component Bar {
      uses iface_a a;
    }

    assembly {
      composition {
        component Foo f;
        component Bar b;
        connection seL4RPC c(from b.a, to f.a);
      }
    }

This example compiles to:

    component A_Piece1 {
      provides a_piece ap;
    }

    component A_Piece2 {
      uses a_piece ap;
      provides iface_a a_impl;
    }

    component Bar {
      uses iface_a a;
    }

    assembly {
      composition {
        component Bar b;
            
        component A_Piece1 f_fi_a1;
        component A_Piece2 f_fi_a2;

        connection seL4RPC f_fi_c(from f_fi_a1.ap, to f_fi_a2.ap);
        connection seL4RPC c(from b.a, to f_fi_a2.a_impl);
      }
    }

### Custom Data Types

CAmkES allows the definition of custom data types for procedure method arguments and ports.
Data types can be defined in C header files by typedefing a struct, enum or built-in type.
Sections of the application that refer to custom types must include the header file.

#### Procedures

Assume a data type `Vector` is defined in the file vector.h in the top level include directory of the application:

```c
#ifndef _VECTOR_H_
#define _VECTOR_H_

typedef struct {
  double x;
  double y;
} Vector;

#endif
```

A procedural interface could then be defined to use the type:
    
    procedure algebra_iface {
      include <vector.h>;
      Vector add(Vector a, Vector b);
    }

C source files that need access to this data type can include the file with:
```c
#include <vector.h>
```

To make the build system aware of the header file, for each component that uses it, the following must be added
to the application's Makefile (replacing the name `Component` with the name of the component):

```Makefile
Component_HFILES := \
  $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/include/*.h))
```

The header file can be placed anywhere in the application's directory structure, provided the path
in the Makefile is appropriately specified, though by convention, header files defining data types
should be placed in the top level include directory of the application.

#### Ports

Assume a data type `IntArray` is defined in int_array.h in the top level include directory of the application:

```c
#ifndef _INT_ARRAY_H_
#define _INT_ARRAY_H_

typedef struct {
  int data[1024];
} IntArray;

#endif
```

A component could declare a port of this type:

    component A {
      control;

      include "int_array.h";
      dataport IntArray int_arr;
    }

This would give the implementation access to a global pointer, which points to
an appropriately large region of memory for the data type:
```c
extern volatile IntArray * int_arr;
```

### Global Include Directories

CAmkES allows users to define a list of directories that will be searched
when resolving imports of .camkes files (components and interfaces) and
all files included in Makefiles.
This allows one to place common components and interfaces in a central location
rather than duplicating them inside the application directory of each
application that uses them. Components and interfaces defined in global include
directories are known as **Global Components** and **Global Interfaces**.
When the distinction is necessary, non-global components and interfaces are
known as **Local Components** and **Local Interfaces**.

#### Recommended Practices

Generally, a component should be created as a global component unless there's
some good reason not to. Applications should consist of a (usually) small number
of control components, and possibly some application specific utility components.
When possible, utility components should be generalised and placed in a global
component repository.

All procedural interfaces used or provided by global components should be
global interfaces. Applications containing multiple local components which
communicate over procedural interfaces should define these interfaces locally,
unless it would make sense for these interfaces to generalise to other components
in the future, in which case they should be global interfaces.

Regarding header files defining custom data types, if the data type is specific to
a particular component or procedural interface, the header file should be placed
in the directory of that component or interface. Otherwise, header files should
be placed in a well known top-level subdirectory of the component repository so
they may be reused between components and interfaces.

It is possible that between global components, there is some shared functionality
such as commonly used algorithms and data structures. Rather than duplicating this
code across multiple global components, it should be placed in source/header files
in a well known top-level subdirectory of the component repository.

The following examples will demonstrate some conventions for defining and using
global components and interfaces.

#### Simple Example

This example will demonstrate an application called pythagoras that computes
the length of the hypotenuse of a right-angle triangle using the Pythagorean 
theorem. All paths in this example are relative to the project root.

Two additional directories are created in the project root directory:

- components
- interfaces

They are made known to the build system by setting the
"Search path for components and interfaces" in the "CAmkES Options" section
when running `make menuconfig`, to: `${PWD}/components ${PWD}/interfaces`.
This value holds a space separated list of directories to search when
resolving imports. `${PWD}` is resolved to the project root directory.

The pythagoras application is located in apps/pythagoras. It has a client component
which computes the length of the hypotenuse of a right-angle triangle.
It makes calls into a math library component which is defined in a global
include directory outside of this application.

The math library component is defined in a directory components/Math.
The procedure interface it provides is named `MathIface` and is located
in a directory interfaces/MathIface.

In the top-level .camkes file shown below, note the angle brackets around Math/Math.camkes.
This denotes that the file is not located in the application's directory, but in
some global include directory (in this case, the components directory).

    /* apps/pythagoras/pythagoras.camkes */

    import <std_connector.camkes>;

    import <Math/Math.camkes>;

    import "components/Client/Client.camkes";

    assembly {
      composition {
        component Client client;
        component Math math;

        connection seL4RPC c(from client.math, to math.m);
      }
    }

The client's component definition (.camkes) is located inside the application 
directory. Note again the angle brackets around MathIface/MathIface.camkes.
This file contains the interface provided by the Math component, and is
located in a global include directory (the interfaces directory).

    /* apps/pythagoras/components/Client/Client.camkes */

    import <MathIface/MathIface.camkes>;

    component Client {
      control;

      uses MathIface math;
    }

The client's component implementation (.c) is also located inside the application.

```c
/* apps/pythagoras/components/Client/src/main.c */

#include <Client.h>
#include <stdio.h>

double pythag(double a, double b) {
  return math_sqrt(math_add(math_square(a), math_square(b)));
}

int run(void) {
  double a = 3;
  double b = 4;
  double c = pythag(a, b);
  
  printf("pythag(%2f, %2f) == %2f\n", a, b, c);

  return 0;
}
```

The .c file implementing the externally-defined Math component must be known
to the build system so it can be compiled. This is achieved by including
a component Makefile (Math.mk) in the application's Makefile. 
A component Makefile lists the .c and .h files required by a global component,
in the same way as the application Makefile below lists the .c and .h
files required by the local component `Client`.

Note that the path given
to include is relative to one of the global import directories (in this case, components).

```Makefile
# apps/pythagoras/Makefile

include Math/Math.mk

TARGETS := pythagoras.cdl
ADL := pythagoras.camkes

Client_CFILES := components/Client/src/*.c

include ${PWD}/tools/camkes/camkes.mk
```

The interface `MathIface` is defined as normal:
    
    /* interfaces/MathIface/MathIface.camkes */

    procedure MathIface {
      double square(in double a);
      double sqrt(in double a);
      double add(in double a, in double b);
      double divide(in double a, in double b);
    };

The component `Math` imports the `MathIface` component using angle brackets.
Even though `Math` is defined in a global include directory, it can still
import files from different global include directories.

    /* components/Math/Math.camkes */

    import <MathIface/MathIface.camkes>;

    component Math {
      provides MathIface m;
    }

The `Math` component is implemented inside the Math component directory.

```c
/* components/Math/src/main.c */

#include <Math.h>

#include <math.h>

double m_square(double a) {
  return a * a;
}

double m_sqrt(double a) {
  return sqrt(a);
}

double m_add(double a, double b) {
  return a + b;
}

double m_divide(double a, double b) {
  return a / b;
}
```

The build system must know the location of the component's source file(s), so
a Makefile specifying this information
is packaged with each global component. Recall that
this file was included by the application's Makefile.

```Makefile
# components/Math/Math.mk

BASE_DIR := $(dir $(abspath $(lastword ${MAKEFILE_LIST})))

Math_CFILES := $(wildcard ${BASE_DIR}/src/*.c)
Math_HFILES := $(wildcard ${BASE_DIR}/include/*.h)
```

#### Example involving Custom Procedure Type

The example above will be extended to include some basic vector arithmetic
operations. This will require the definition of a vector data type. 
The vector type is defined with the `MathIface` interface:

```c
/* interfaces/MathIface/include/vec.h */

#ifndef _VEC_H_
#define _VEC_H_

typedef struct {
  double x;
  double y;
} vec_t;

#endif
```

The client source will be modified to include an implementation
of vector projection composed from simpler vector operations, which will
be implemented in the `Math` global component. 

```c
/* apps/pythagoras/components/Client/src/main.c */

#include <Client.h>
#include <stdio.h>

#include <vec.h>

double pythag(double a, double b) {
  return math_sqrt(math_add(math_square(a), math_square(b)));
}

vec_t vec_project(vec_t a, vec_t b) {
  double scalar = math_divide(math_dot(a, b), math_square(math_length(a)));
  return math_scalar_mult(a, scalar);
}

int run(void) {
  double a = 3;
  double b = 4;
  double c = pythag(a, b);
  
  printf("pythag(%2f, %2f) == %2f\n", a, b, c);

  vec_t x_axis = (vec_t) {.x = 1, .y = 0};
  vec_t v = (vec_t) {.x = 3, .y = 4};
  vec_t proj = vec_project(x_axis, v);

  printf("x component of (%2f, %2f) is (%2f, %2f)\n",
      v.x, v.y, proj.x, proj.y);

  return 0;
}
```

Note that vec.h is included in the above code listing. 
The process by which vec.h is added to the include path for this
project is as follows.

A file MathIface.mk is added to the MathIface directory inside the
interfaces global include directory. This file serves to expose to the
rest of the project, a list of header files containing type definitions
for any types used for arguments or return values of methods that make
up the interface `MathIface`.

```Makefile
# interfaces/MathIface/MathIface.mk

BASE_DIR := $(dir $(abspath $(lastword ${MAKEFILE_LIST})))
MathIface_EXPORT_HFILES := $(wildcard ${BASE_DIR}/include/vec.h)
```

The variable `MathIface_EXPORT_HFILES` should contain a list of paths to
header files containing any types referenced in the `MathIface` interface.
This convention should be followed for any interfaces using custom types
defined in header files.

The `MathImpl` procedure definition was modified to include some new methods:

    procedure MathIface {
      include <vec.h>;

      ...

      double dot(in vec_t a, in vec_t b);
      vec_t scalar_mult(in vec_t v, in double s);
      double length(in vec_t a);
    };

The `Math` component implementation contains the implementation of these new methods:

```c
/* components/Math/src/main.c */

#include <Math.h>

#include <vec.h>

...

double m_dot(vec_t a, vec_t b) {
  return a.x*b.x + a.y*b.y;
}

vec_t m_scalar_mult(vec_t v, double s) {
  return (vec_t) {.x = v.x*s, .y = v.y*s};
}

double m_length(vec_t a) {
  return sqrt(a.x*a.x+a.y*a.y);
}
```

Since this file includes vec.h, it must be added to the header files for
this component in the component Makefile as follows:

```Makefile
# components/Math/Math.mk

BASE_DIR := $(dir $(abspath $(lastword ${MAKEFILE_LIST})))

Math_CFILES := $(wildcard ${BASE_DIR}/src/*.c)
Math_HFILES := $(wildcard ${BASE_DIR}/include/*.h)
include MathIface/MathIface.mk
Math_HFILES += ${MathIface_EXPORT_HFILES}
```

Finally, vec.h is also included in the local component `Client`. The path
to vec.h is added to the list of headers for `Client` in the application
Makefile in the same way:

```Makefile
# apps/pythagoras/Makefile

include Math/Math.mk
include MathIface/MathIface.mk

TARGETS := pythagoras.cdl
ADL := pythagoras.camkes

Client_CFILES := components/Client/src/*.c
Client_HFILES := ${MathIface_EXPORT_HFILES}

include ${PWD}/tools/camkes/camkes.mk
```

#### Example involving Custom Port Type

The example in this section will demonstrate defining a custom type
for a port in a global component. The previous
example will be extended to include a method which computes the nth 
complex roots of unity for an argument `n` - an operation which results 
in `n` values. For each positive integer `n`, the nth roots of unity are the
`n` complex numbers which, when raised to the power of `n`, result in a value of 1. 
A port will be used to pass the results of this operation from the `Math`
global component to the `Client` component.

A header file defining complex numbers, and a struct containing an array of
complex numbers, will be added to the Math component. Note that unlike in the
procedure in the previous example, ports do not have a corresponding .camkes file. Thus,
header files defining port types are placed in component directories instead of
interface directories.

```c
/* components/Math/include/vec.h */

#ifndef _VEC_ARR_H_
#define _VEC_ARR_H_

typedef struct {
  double real;
  double imaginary;
} complex_t;

typedef struct {
  complex_t data[4096];
} complex_arr_t;

#endif
```

A new port interface must be added to the `Math` and `Client` components:

    /* components/Math/Math.camkes */

    import <MathIface/MathIface.camkes>;

    component Math {
      provides MathIface m;
      
      include <complex_arr.h>;
      dataport complex_arr_t complex_data;
    }


    /* apps/pythagoras/components/Client/Client.camkes */

    import <MathIface/MathIface.camkes>;

    component Client {
      control;

      uses MathIface math;
      
      include <complex_arr.h>;
      dataport complex_arr_t complex_data;
    }

A new connection is added to the top level .camkes file:

    /* apps/pythagoras/pythagoras.camkes */

    ...
    assembly {
      composition {
        ...
        connection seL4SharedData d(from client.complex_data, 
                                    to math.complex_data);
      }
    }

A new method is added to the `MathIface` interface. Note that since
this method doesn't actually return the complex roots of unity (but
rather writes them into an area of shared memory) there is no reason
for this to include the header file defining complex numbers.

    /* interfaces/MathIface/MathIface.camkes */

    procedure MathIface {
      
      ...

      int compute_roots_of_unity(in int n);
    };

The implementation of this method is added to the `Math` component implementation:
```c
/* components/Math/src/main.c */

#include <Math.h>

#include <math.h>

#include <complex_arr.h>

...

int m_compute_roots_of_unity(int n) {
  if (n >= 4096) {
    return -1;
  }
  for (int i=0;i<n;i++) {
    complex_data->data[i] = (complex_t) {
      .real = cos((i*2*M_PI)/n),
      .imaginary = sin((i*2*M_PI)/n)
    };
  }
  return 0;
}
```

The method is called from the `Client` component implementation:
```c
/* apps/pythagoras/components/Client/src/main.c */

...

#include <complex_arr.h>

...

int run(void) {
  ...
  const int n = 4;
  if (math_compute_roots_of_unity(4) == 0) {
    printf("%dth roots of unity:\n", n);
    for (int i=0;i<4;i++) {
      printf("%2f + %2fi\n", complex_data->data[i].real, 
                             complex_data->data[i].imaginary);
    }
  }

  return 0;
}
```

To make the build system aware of the new header file (complex_arr.h), it must be exported
by the `Math` component Makefile much in the same way as vec.h was exported in the previous
example. It sets the `Math_EXPORT_HFILES` variable which becomes accessible to all dependent
Makefiles.

```Makefile
# components/Math/Math.mk

BASE_DIR := $(dir $(abspath $(lastword ${MAKEFILE_LIST})))

Math_CFILES := $(wildcard ${BASE_DIR}/src/*.c)
Math_HFILES := $(wildcard ${BASE_DIR}/include/*.h)

Math_EXPORT_HFILES := \
    $(wildcard ${BASE_DIR}/include/complex_arr.h)

include MathIface/MathIface.mk
Math_HFILES += ${MathIface_EXPORT_HFILES}
```

The application Makefile must be adjusted to add this dependency:

```Makefile
# apps/pythagoras/Makefile

include Math/Math.mk
include MathIface/MathIface.mk

TARGETS := pythagoras.cdl
ADL := pythagoras.camkes

Client_CFILES := components/Client/src/*.c
Client_HFILES := ${MathIface_EXPORT_HFILES} \
                 ${Math_EXPORT_HFILES}

include ${PWD}/tools/camkes/camkes.mk
```


## Templating

CAmkES glue code, code automatically introduced into your component system at
compile time, is driven by a set of templates. These templates are instantiated
with values determined from your input ADL specification. CAmkES templates are
written as C code with Python snippets embedded in comments. This is all driven
by the [Jinja2](http://jinja.pocoo.org/docs/) templating engine. You can see
examples of existing templates in camkes/templates/.

The remainder of this section gives advice for people intending to implement
their own templates or modify existing templates. If you are attempting to
modify the template environment itself, you should instead refer to the
[Template Environment](#template-environment) section.

### Template Writing

Inside a template you write C code as you would normally, but use the following
special comments to run Python code:

* `/*- execute code -*/` (equivalent of Python's `exec`)
* `/*? execute code and replace with result -*/` (equivalent of Python's `eval`)
* `/*# a comment to be removed at instantiation #*/`

In general, when writing code in a template, refer to the Jinja documentation
syntax and functionality. Note that the default Jinja delimiters are `{%` and
`%}` which have been modified to `/*` and `*/` to let syntax highlighting in C
work more naturally.

Within a given template you have a variable `me` that functions like native
Python's `self`. It refers to the object of relevance to the current template.
So, for example, during instantiation of the component source file, it refers
to the component instance being instantiated. In certain general "top-level"
templates, there is no particular "subject." In these templates, for example
the Makefile, `me` will be `None`.

The template environment is a limited subset of Python. It is relatively easy
to extend, and if you intend to do this you can see how in the
[Template Environment](#template-environment) section. Some statements in
Python could not be cleanly exposed and so have instead become functions. In
particular, be aware of quirks in assertions, lambdas and exceptions. `assert`
is available as a function. So instead of writing `assert foo == 1` you would
write `assert(foo == 1)`.

Lambdas are perhaps more confusing. Instead of writing
`lambda x: x.startswith('hello')` you would write
`lambda('x: x.startswith(\'hello\')'`. Note that you lose some type safety and
expressivity here, but there did not seem to be a nicer way to expose this.
Exceptions are now also raised by function. So instead of writing
`raise Exception('foo')` you would write `raise(Exception('foo'))`.

For the specific functionality available in the template context, it may be
helpful to refer to the file camkes/runner/Context.py. Note that in the
template context you also have access to the command line options via `options`
as well.

### Idioms

There are certain common operations you may wish to perform inside a template
context, for which idioms have developed. This section documents some of these
snippets of code that may look unusual when you first encounter them.

#### Passing Information Between Templates

You often wish to do this with two related templates. For example, in the
templates that form each side of a connection you often wish to talk about the
same object on both sides. None of the templates currently call the low-level
helper functions that enable this directly, but if you do want to invoke them,
they are `stash` and `pop`. `stash` lets you save a Python object under a given
key name and `pop` retrieves a previously saved Python object by key. Note that
these are only usable for passing objects between templates that share the same
`me` reference.

#### Generating Symbol Names

Within a C template you sometimes need a temporary variable in a context in
which user-provided variables may be in scope. That is, you need a named symbol
but you need to ensure it doesn't collide with any existing user symbols. To do
this you can call the function `c_symbol`. This generates a pseudo-unique name
that you can use from then on. For example,

```c
/*- set my_var = c_symbol() -*/
int /*? my_var ?*/ = 42;
...
```

`c_symbol` takes an optional string argument that will make that string part of
the resulting symbol name. This is helpful for debugging purposes if you want
to give someone looking at the instantiated template a visual clue as to the
purpose of a temporary variable.

#### Subverting Scoping

Jinja has some unusual and often counter-intuitive variable scoping rules.
Occasionally templates wish to conditionally assign to a variable within the
context of a loop or other Jinja block. In these circumstances it can be tricky
to get the write to propagate outside the loop. You may see a temporary array
and a `do` construct used in these situations:

```c
/*- set temp = [None] -*/
/*- for .... -*/
  ...
  /*- if ... -*/
    /*- do temp.__setitem__(0, True) -*/
  /*- else -*/
    /*- do temp.__setitem__(0, False) -*/
  /*- endif -*/
  ...
/*- endfor -*/
/*- set variable_we_want_to_set = temp[0] -*/
```

### Template Debugging

If you are writing complicated template logic and need to debug during
instantiation, you can insert breakpoints into your template. These can be
inserted as either `/*- breakpoint() -*/` or `/*? breakpoint() ?*/`. When
encountered during instantiation they will drop you into the Python
interpreter, from where you can explore `me` and other local variables.

When prototyping or debugging more complicated problems it can be helpful to
have the ability to run arbitrary Python in the template context. There is some
limited support for this, with the functions `exec` and `eval`. These operate
like the native Python `exec` and `eval`, but may be a little more fragile.
Note that `exec` is a function in this context, not a statement. So where you
would normally write `exec 'print \'hello\''` you would write
`exec('print \'hello\'')`.

Although never advisable in a proper implementation, it is possible to pass
arbitrary information between unrelated templates. Similar to the `stash` and
`pop` functions described above, there are lower level versions, `_stash` and
`_pop` that let you write to and read from a context that propagates across all
templates. Note that you can only use this to pass information "forwards" to
templates that are instantiated after the one you are calling `_stash` from.

## Developers

This section is targeted at those intending to modify the CAmkES implementation
itself. The information below assumes you are familiar with the features and
functionality of CAmkES.

If you are modifying the actual sources of any of the CAmkES modules I've
attempted
to leave helpful comments. I've occassionally used tags in the comments that
may help you when grepping and whatnot. They mean:

**FIXME**

> This is a stop gap piece of functionality that should be replaced
  with something more feature complete when time permits. This could also refer
  to an existing bug that cannot currently be easily remedied.

**HACK**

> This code is a bit dubious, but is intentionally written this way to
  work around limitations in some other tool outside our control.

**MOVE**

> This is the wrong place for this piece of functionality. It should
  be refactored somewhere else.

**PERF**

> This code is structured in a counter-intuitive or non-obvious way for
  performance reasons. Refactor if you wish, but be aware it may have a
  significant impact on runtime.

**SLOW**

> This code is known to be inefficient, but was deliberately written
  this way for simplicity. If you are hitting performance problems and looking
  for optimisation opportunities try grepping for this.

**TODO**

> Some part of the functionality in this section has not yet been
  implemented or the code could be improved in some way.

**XXX**

> There is something out of the ordinary about this piece of code that
  should probably be fixed. This is often in cases where I didn't have time to
  write a proper **FIXME** or **TODO** comment.

### Input Translation

The translation of a CAmkES specification into an Abstract
Syntax Tree is performed in two phases: lexing the input into a stream of valid
tokens and then parsing the tokens into a list of AST objects. Lexing and
parsing are performed using [PLY](http://www.dabeaz.com/ply/), an implementation
of Lex and YACC in Python. The sections below discuss the inner workings of
this process that happens during execution of the runner.

#### Lexing

Lexing via `lex.lex()` relies on a set of tokens being defined as symbols
`t_`_`token`_. These are defined in the following files:

* GenericTokens.py

By a quirk of Lex, most keywords actually match the token `ID` because of its
generality. `t_ID` uses the recommended PLY technique for getting around this by
checking the token value against a set of keywords. These keywords are defined
in the following files and are then added to and managed in `util.keywords`.

* ADLKeywords.py
* IDLKeywords.py

For documentation on the format of `t_*`
functions, refer to the [PLY manual](http://www.dabeaz.com/ply/ply.html).

#### Parsing

Parsing via `yacc.yacc()` relies on a set of rules being defined as symbols
`p_`_`rule`_.
These are defined in the following files:

* ADLRules.py
* CAmkESRules.py
* GenericRules.py
* IDLRules.py

There is no easy way to build the parser without the `p_`_`rule`_ rules in the global
context so camkestr.py imports these files into its own namespace. Note that
the parser also expects the `t_`_`token`_ token symbols to be in the global context at
parsing time so these files are forced to import the *Tokens.py files into
their own namespaces.

By default the parser assumes the first `p_`_`rule`_ rule it sees is the starting
symbol. Beyond a simple parser, this behaviour is not what you want. We
override this, based on the input grammar, by defining `start` before building
the parser.

You can observe a recurring pattern in the *Rules.py files, where elements have
a set of rules with common suffixes. This is for greater flexibility in the way
entities can appear and be recognised in the input. The rules loosely map to
the following:

* `entity_sing` - A singleton instantiation of a type. Some CAmkES types are
  only ever instantiated once in a given context, in which the instance is
  usually unnamed. For example, assemblies. This rule encapsulates the forms in
  which this can be done.
* `entity_decl` - A top-level declaration of a type. It may help (or hinder)
  your understanding to think of this as a creation of the type itself. The
  expansion of this rule usually contains a definition of the type.
* `entity_ref` - A reference to an entity of this type. References generally
  come in two forms: a symbol referring to an entity defined elsewhere or a
  definition of the entity inline.
* `entity_block` - The delimiters of an entity definition and the contained
   definition. This is usually just a convenience wrapper for dealing with
   things like lists.
* `entity_defn` - The definition of the entity itself. This contains the
  entity-specific input grammar. While the implementations of the other common
  rules are pretty mechanical, this one actually relies on the syntax of the
  entity itself.

To clarify this pattern, some example rules for structs in C would look like
the following. Note that the `struct_sing` rule doesn't really make sense in
the context of C.

    struct_sing : struct ID SEMI
                | struct_decl
    struct_decl : struct struct_block
                | struct struct_block ID
    struct_ref : ID
               | struct_block
    struct_block : LBRACE struct_defn RBRACE
    struct_defn :
                | member_type ID SEMI struct_defn

### Template Context

The code that renders the templates themselves is all contained under the
runner directory in the CAmkES module. While the rendering itself is driven
from Renderer.py, the more relevant file is actually Context.py. The
`new_context` function returns a dictionary that defines the template
environment, that is, what local variables are present in the template at
instantiation time.

There is some fairly complex functionality here aimed at providing nice
abstractions to template authors. In particular, `alloc_obj`, `alloc_cap`,
`stash`, `pop` and `guard` are intended to provide an abstraction for the
template author to pass variables between templates. Refer to the comments in
this file to understand more about the template context.

Extending the context can be done by adding more items to this dictionary and
there aren't many gotchas here. If you're doing something more complicated than
exposing an existing built-in and having difficulty you may find the
implementations of `breakpoint` or `exec` informative as examples.

### Core Libraries

CAmkES has a notion of "core libraries" as the set of seL4 libraries that may
be relied on to be available from within the template context. These are
defined within the camkes.mk Makefile fragment available in the CAmkES
directory. This set of libraries has been extended on demand to cover all
base seL4 infrastructure. This can be freely expanded to cover more libraries
with no expected surprises.

Be aware that these libraries will be unconditionally depended upon and linked
into all CAmkES components. That is, the user's lists of libraries defined in
their application Makefile will all be silently extended to include the core
libraries.

### Testing

Currently there are only tests for the [parser](#parser); that is, the test
suite does not cover the functionality of the [runner](#runner) or the
[lint](#lint) tool. Unit tests are also lacking and should be implemented in
the future.

The test framework and tests themselves can be found in tests/. Use one
of the following invocations to run the test suite:

```bash
make                  # Run all tests
make explicit         # Run all the executable files in the directory
make explicit_foo     # Run the test in executable tests/foo
make generic          # Run generic tests on all inputs *.{adl|idl|camkes}
make generic_bar.adl  # Run generic tests on the input bar.adl
```

To add a new input file to be used in the generic tests create a file with the
input you want to test and save it in tests/ with an extension indicating what
grammar it is using.

To add a test with other functionality, write a script or program in any
language and save it in the tests/ directory. The framework considers any
executable file in this directory an eligible test.

The functionality that the test suite exercises is not extensive and should be
expanded at some point.

## Legacy Implementation

Prior to the existing CAmkES implementation, there was a previous build system
and initialisation task for running CAmkES applications. This section is a quick
reference for porting applications from the older CAmkES runtime and build
system. If you are not familiar with the older CAmkES you can safely skip this
section.

The directory structure in this repository is similar to the current CAmkES
project repository and it should be obvious where to copy application
directories to when migrating them. In terms of porting actual applications the
main differences you will need to take into account are discussed below.

### Relative imports

[tl;dr](https://en.wikipedia.org/wiki/Wikipedia:Too_long;_didn%27t_read):
`import "foo.idl";` → `import "relative/path/to/foo.idl";`

The new CAmkES parser respects directory structure as namespaces when importing.
This means that a relative import is interpreted relative to the directory the
containing file is in. For example, `import "../foo/bar.adl";` imports the file
bar.adl in the directory foo within the parent directory of the file this line
appears in. This style of import is much more natural and should match your
intuition from C #includes.

The old CAmkES parser had a list of import directories and searched these for a
file matching your import directive. In the case of more than one matching file
the import was ambiguous and the user was expected to resolve this or deal with
the consequences.

### Built-in imports

[tl;dr](https://en.wikipedia.org/wiki/Wikipedia:Too_long;_didn%27t_read):
`import "std_connector.camkes";` → `import <std_connector.camkes>;`

The old environment provided a series of built-in CAmkES files available for
import. These were imported with identical syntax to the user's files and it
was up to the user to ensure they didn't introduce collisions.

The new parser introduces a C-like concept of built-in imports using C's
familiar `<...>` syntax. The namespace for built-in imports is managed by the
import path of the parser/runner (--import-path/-I).

### Generated headers

[tl;dr](https://en.wikipedia.org/wiki/Wikipedia:Too_long;_didn%27t_read):
`#include "Client_s.h";` → `#include "Client.h";`

The old runner generated a header per connection. The new runner generates a
header per component. Functionality-wise, there is very little difference here.
The number of generated headers you need to include is reduced, at the expense
of fine-grained expressiveness.

### Interface blocks

[tl;dr](https://en.wikipedia.org/wiki/Wikipedia:Too_long;_didn%27t_read):
No changes required.

The old parser required a trailing semi-colon for interface blocks. E.g.

    interface foo {
      ...
    };

In the new parser this trailing semi-colon is optional; in fact, it is parsed
as an empty statement following the interface definition.

### Makefile

[tl;dr](https://en.wikipedia.org/wiki/Wikipedia:Too_long;_didn%27t_read):
Refer to one of the existing ported examples.

The old per-application Makefiles were a thin wrapper around the CAmkES build
system. They looked something like the following:

```Makefile
CAMKES_APP=$(patsubst camkes-apps-%--devel,%,$(notdir ${SOURCE_DIR}))
SOURCE_ROOT=${SOURCE_DIR}/..

include ${BUILDSYSTEM_DIR}/Makefile
```

The new CAmkES structure attempts to more closely align these Makefiles with
the structure that should be familiar from other seL4 projects. Your `FILES`
variables need to be prefixed with the component type they pertain to,
`TARGETS` should contain a [CPIO](https://en.wikipedia.org/wiki/Cpio) archive
file for the application as a whole, `ADL` should contain the top-level CAmkES
file that describes this application, and you should include camkes.mk instead
of common.mk. Your resulting Makefile should look something like the following:

```Makefile
TARGETS := simple.cpio
ADL := simple.camkes

Client_CFILES := \
  $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/Client/src/*.c))

Client_ASMFILES := \
  $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/Client/crt/arch-${ARCH}/crt0.S))

Echo_CFILES := \
  $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/Echo/src/*.c))

Echo_ASMFILES := \
  $(patsubst ${SOURCE_DIR}/%,%,$(wildcard ${SOURCE_DIR}/components/Echo/crt/arch-${ARCH}/crt0.S))

include ${SOURCE_DIR}/../../tools/camkes/camkes.mk
```

You can also use the variable `TEMPLATES` to pass a list of directories to be
searched for user-provided connector templates.
