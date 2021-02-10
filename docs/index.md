<!--
     Copyright 2017, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

This document describes the structure and functionality of CAmkES, a platform
for building componentised systems for embedded platforms. The documentation is
broken into sections for users, template authors and developers. The
[Usage](#usage) section is for people wanting to develop systems
using CAmkES as a platform. The [Templating](#templating) section is
for people wanting to write their own CAmkES templates and use more complex
functionality. Finally the [Developers](#developers) section is for
people wanting to modify the internals of CAmkES itself. If you are modifying
the internals of CAmkES, it is recommended that you read the entirety of this
documentation. Regardless of which section is most relevant for you, you should
at least familiarise yourself with the [Terminology](#terminology) section.

CAmkES' primary target platform is the
[seL4 microkernel](http://sel4.systems/). The seL4 kernel and its functionality
are not discussed in this document. It is assumed that the reader has read the
seL4 programming references and is familiar with how this kernel operates and
the mechanisms it provides.

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
  The types of attributes can be constructed as a collection or _struct_ of
  any of the basic CAmkES types: int, unsigned int, char, unsigned char, string.
  It is possible to give an attribute a default value when it is declared.  If
  there are no settings for an attribute, the default setting will be used.  If
  an attribute is aliased to a different attribute that also has a default,
  then the different attribute's default will override the original default.

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

**Exported Interface**

> An interface of an internal instance that is presented under the name of an
  identically typed interface in its containing component. The purpose of
  exported interfaces is to expose a coherent outward-facing set of interfaces
  from a component, while potentially implementing those interfaces within
  nested components.

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

**Internal Instance**

> A component instance declared inside a compound component's composition section.

**Internal Connection**

> A connection declared inside a compound component which connects two internal
  instance interfaces. That is, any connection declared inside a compound
  component.

**Maybe**

> Interfaces of components can be made optional using the `maybe` keyword. Optional
  interfaces do not need to be connected to any other interfaces. C symbols associated
  with optional interfaces (functions and dataport pointers) are declared as weak
  symbols. If nothing is connected to an optional interface, its associated symbols
  lack definitions. That is, functions and dataport pointers associated with unconnected
  optional interfaces take the value `NULL` at runtime.

**Method**

> An item of a procedure. When targeting a conventional programming language,
  methods usually map directly to generated functions.

**Parameter**

> A piece of data referenced by a procedure method. This can be thought of as an
  argument to a function.

**Port**

> The interface type that represents shared memory semantics.

**Procedure**

> An interface with function call semantics. Procedures consist of a series of
  methods that can be invoked independently.

**Provides**

> Procedure interfaces implemented by a component. When targeting a conventional
  programming language this typically means that the component contains
  functions that are implementations of each method in the procedures provided.

**Setting**

> An assignment of an attribute to a specific value. A setting does not specify
  the type of the attribute, because this has already been described by the
  attribute as specified in the component/connector description.

**Struct**

> A collection of named attribute fields that can be used as an attribute type
  for a component _attribute_.

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

> An interface of a compound component that is not implemented by that
  component, but is an alias for internal instance's interface.

A concrete example:

```camkes
struct cat {
    int paws;
    string name;
}

procedure thing {
  int func(in int x);
}

component foo {
  control;
  uses thing t1;
  emits sig s1;
  dataport buffer b1;
  attribute cat kitty;
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
    connection Notification c2(from f.s1, to b.s2);
    connection SharedData c3(from f.b1, to b.b2);
  }
  configuration {
      f.kitty = {"name": "meows", "paws": 4};
  }
}
```

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
* `RPC`, `Notification` and `SharedData` are **connector**s
* `c1`, `c2` and `c3` are **connection**s
* `cat` is a **struct**
* `kitty` is an **attribute**
* `f.kitty` is a **setting**

## Usage

This section is targeted at people building systems on top of the CAmkES
platform. It assumes a basic knowledge of C programming.

### Dependencies

Please see [the docsite](https://docs.sel4.systems/HostDependencies) for information about dependencies.

To check you have the appropriate dependencies installed:

```bash
./tools/check_deps.py
```

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
mkdir build-kzm
cd build-kzm
../init-build.sh -DPLATFORM=kzm -DCROSS_COMPILER_PREFIX=arm-none-eabi- -DCAMKES_APP=simple -DSIMULATE=1
ninja
```

This produces an image images/simple-image-arm-imx31. To run this image in
qemu:

```bash
./simulate
```

You should see debugging output from the system initialisation, followed by:

```
echo_int: 42 -> 42
echo_float: 273421.437500 -> 273421.437500
echo_double: 273421.427400 -> 273421.427400
echo_mix: 273421.427400 -> 273421
echo_string: "hello world" -> "hello world"
echo_parameter: 123 -> 123 (returned = 123)
increment_parameter: 100 -> 101
After the client
```

To understand what this example is doing, open the files
apps/simple/components/Echo/src/echo.c and
apps/simple/components/Client/src/client.c. The implementations of the echo
functions are in echo.c and they are called from client.c. The function call
itself happens over a seL4 endpoint. The connection between the two components
is described in apps/simple/simple.camkes, and the functional interface that
echo is providing is described in apps/simple/interfaces/Simple.idl4.

If you want to run this example on IA32, repeat the above procedure with a new build
directory, replacing the configuration line with the following:

```bash
../init-build.sh -DPLATFORM=ia32 -DCAMKES_APP=simple -DSIMULATE=1
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

```camkes
/* apps/helloworld/interfaces/MyInterface.idl4 */

procedure MyInterface {
  void print(in string message);
}
```

This interface consists of a single method, print that takes an input parameter
of type string. Note that, although we are planning to implement this component
in C, interfaces are defined with abstract types that have equivalents in all
target languages. In the case of C, string maps to `char*`. Each component
needs a description of the interfaces it exposes or needs in so-called
Architecture Description Language. Create these in
apps/helloworld/components/Hello/Hello.camkes and
apps/helloworld/components/Client/Client.camkes.

```camkes
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
```

Note that each component description needs to import the interface file we
created above from apps/helloworld/interfaces. Import statements function
similar to C's `#include`, in that they can be enclosed in double quotes and
are relative to the source file, or enclosed in angle brackets and refer to a
built-in file. The Hello component is to contain an implementation of
MyInterface and the Client component will expect to be provided with an
implementation of MyInterface. The `control` keyword indicates that Client is
what is called an active component. This means it will contain a main function
(prototyped as `run`) and have an active thread of control.

Create a file to describe the instantiation and structure of the system at
apps/helloworld/helloworld.camkes.

```camkes
/* apps/helloworld/helloworld.camkes */

import <std_connector.camkes>;
import "components/Hello/Hello.camkes";
import "components/Client/Client.camkes";

assembly {
  composition {
    component Hello h;
    component Client c;
    connection seL4RPCCall conn(from c.iface, to h.inf);
  }
}
```

This file begins with several import statements that reference other files.
Hello.camkes and Client.camkes are the files we created above, while
std_connector.camkes is a built-in file that defines the standard CAmkES
connector types. The body of the system description instantiates each component
once, `h` of type `Hello` and `c` of type `Client`. The components' interfaces
are connected via a connection, `conn`, of type `seL4RPCCall`.

Now for the implementation of the components. Create a single source file for
Hello as apps/helloworld/components/Hello/src/hello.c:

```c
/* apps/helloworld/components/Hello/src/hello.c */

#include <camkes.h>
#include <stdio.h>

void inf__init(void) {
}

void inf_print(const char *message) {
  printf("Client says: %s\n", message);
}
```

The header camkes.h is generated by the CAmkES build system and contains
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

#include <camkes.h>

int run(void) {
  const char *s = "hello world";
  iface_print(s);
  return 0;
}
```

The entry point of a CAmkES component is `run`.

The final thing is to add some build system boiler plate to be able to build
the system.
Copy one of the `CMakeLists.txt` files from another application or create
`apps/helloworld/CMakeLists.txt` from scratch:

```
cmake_minimum_required(VERSION 3.7.2)

project(helloworld C)

DeclareCAmkESComponent(Client SOURCES components/Client/src/client.c)
DeclareCAmkESComponent(Hello SOURCES components/Hello/src/hello.c)

DeclareCAmkESRootserver(helloworld.camkes)
```

You're now ready to compile and run this application, by entering the `CAMKES_APP` value in the cmake configuration GUI:

```bash
cd build-kzm
cmake . -DCAMKES_APP=helloworld # set `helloworld` as CAMKES_APP
ninja
./simulate
```

If all goes well you should see:

```
Client says: hello world
```

Congratulations, you've just made your first CAmkES application.

#### Under the Hood

We basically just wrote a verbose and roundabout Hello World example, so what
benefit is CAmkES providing here? Note how the function call between the two
components looks just like a normal function invocation in C, even though the
two components are actually in different address spaces. During compilation
so-called glue code is generated to connect the two components via a seL4
endpoint and transparently pass the function invocation and return over this
channel. The communication itself is abstracted in the ADL description in
apps/helloworld/helloworld.camkes. The connection type we used was seL4RPCCall, but
it is possible to use another connection type here without modifying the code of
the components themselves.

CAmkES provides some interface types for other modes of interaction than
function calls. Events can be used for asynchronous communication and dataports
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

```camkes
/* apps/helloevent/components/Emitter/Emitter.camkes */

component Emitter {
  control;
  emits MyEvent e;
}
```

This description says Emitter is an active component (the control keyword) and
it emits a single event called e of type MyEvent. Create some basic source code
for the component that does nothing except emit the event itself:

```c
/* apps/helloevent/components/Emitter/src/main.c */

#include <camkes.h>

int run(void) {
  while (1) {
    e_emit();
  }
  return 0;
}
```

CAmkES provides an emit function to send the event.

Now let's create a description of the Consumer that will handle this event:

```camkes
/* apps/helloevent/components/Consumer/Consumer.camkes */

component Consumer {
  control;
  consumes MyEvent s;
}
```

Note that this component consumes (handles) an event of the same type. Let's
instantiate and connect these components together using another ADL file:

```camkes
/* apps/helloevent/helloevent.camkes */

import <std_connector.camkes>;
import "components/Emitter/Emitter.camkes";
import "components/Consumer/Consumer.camkes";

assembly {
  composition {
    component Emitter source;
    component Consumer sink;
    connection seL4Notification channel(from source.e, to sink.s);
  }
}
```

In this file, seL4Notification is a seL4 specific connector for transmitting
asynchronous signals. The two instantiated components, source and sink are
connected over the connection channel.

As mentioned above, there are several ways for a component to receive an event.
The consumer can register a callback function to be invoked when the event is
received, they can call a blocking function that will return when the event is
received or they can call a polling function that returns whether an event has
arrived or not. Let's add some source code that uses all three:

```c
#include <camkes.h>
#include <stdio.h>

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

We now have everything we need to run this system.

Create the appropriate `apps/helloevent/CMakeLists.txt` as for the previous example. Compile the system and
run it with the simulate script as per the previous example. If all goes well you
should see something like the following:

```
Registering callback...
Callback fired!
Polling...
We didn't find an event
Waiting...
Unblocked by an event!
Callback fired!
```

Whether you find an event during polling will be a matter of the schedule that
seL4 uses to run the components. This covers all the functionality available
when using events. One final point that may not be obvious from the example is
that callbacks will always be fired in preference to polling/waiting. That is,
if a component registers a callback and then waits on an event to arrive, the
callback will be fired when the first instance of the event arrives and the wait
will return when/if the second instance of the event arrives.

#### An Example of Dataports

Dataports are CAmkES' abstraction of shared memory. All
components participating in a connection involving dataports get read/write
access to the dataport by default. The default dataport type is
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
  bool ready;
} MyData_t;

#endif
```

Now let's create an ADL description of the Ping component:

```camkes
/* apps/hellodataport/components/Ping/Ping.camkes */

import "Porttype.idl4";

component Ping {
  include "porttype.h";
  control;
  dataport Buf d1;
  dataport MyData_t d2;
}
```

Note that we need to include the C header in the ADL. CAmkES does not actually
parse this header, but it needs to know to `#include` it whenever it references
the `MyData_t` type. Add a similar description for Pong:

```camkes
/* apps/hellodataport/components/Pong/Pong.camkes */

import "Porttype.idl4";

component Pong {
  include "porttype.h";
  control;
  dataport Buf s1;
  dataport MyData_t s2;
}
```

Now we'll create some basic code for each component to use the dataports:

```c
/* apps/components/Ping/src/main.c */

#include <camkes.h>
#include <porttype.h>
#include <stdio.h>
#include <string.h>

// index in d1 to use to signal pong
#define D1_READY_IDX 20

int run(void) {
  char *hello = "hello";

  printf("Ping: sending %s...\n", hello);
  strncpy((char*)d1, hello, D1_READY_IDX - 1);

  d1_release(); // ensure the assignment below occurs after the strcpy above
  ((*char)d1)[D1_READY_IDX] = 1;

  /* Wait for Pong to reply. We can assume d2_data is
   * zeroed on startup by seL4.
   */
  while (!d2->ready) {
    d2_acquire(); // ensure d2 is read from in each iteration
  }

  printf("Ping: received %s.\n", d2->data);

  return 0;
}
```

```c
/* apps/components/Pong/src/main.c */

#include <camkes.h>
#include <porttype.h>
#include <stdio.h>
#include <string.h>

// index in s1 to use to signal ping
#define S1_READY_IDX 20

int run(void) {
  char *world = "world";

  /* Wait for Ping to message us. We can assume s1_data is
   * zeroed on startup by seL4.
   */
  while (!((char*)s1)[S1_READY_IDX]) {
    s1_acquire(); // ensure s1 is read from in each iteration
  }

  printf("Pong: received %s\n", (char*)s1);

  printf("Pong: sending %s...\n", world);
  strcpy(s2->data, world);

  s2_release(); // ensure the assignment below occurs after the strcpy above
  s2->ready = true;

  return 0;
}
```

Note the use of `*_acquire()` and `*_release()` functions. These are used to maintain
coherency of shared memory between components. Call `*_acquire()` between multiple
reads from a dataport, where the correct behaviour of the program depends on the
contents of the dataport possibly changing between reads. Call `*_release()` between
multiple writes to a dataport, where the correct behaviour of the program depends
on writes preceding the `*_release()` in the program code being performed strictly
before the writes following it.

Typically, a real system would have a more complete communication protocol between
the two components, but for the purposes of this example spinning until a byte
changes is good enough. We're ready to connect all these sources together with a
top-level ADL file:

```camkes
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
```

Add the now familiar `apps/hellodataport/CMakeLists.txt`:

```cmake
cmake_minimum_required(VERSION 3.7.2)

project(hellodataport C)

# Interface library for our dataport
add_library(MyData INTERFACE)
target_include_directories(MyData INTERFACE "${CMAKE_CURRENT_LIST_DIR}/include")

DeclareCAmkESComponent(Ping SOURCES components/Ping/src/main.c LIBS MyData)
DeclareCAmkESComponent(Pong SOURCES components/Pong/src/main.c LIBS MyData)

DeclareCAmkESRootserver(hellodataport.camkes)

```
We added an interface library containing the shared header file. The LIBS field in DeclareCAmkESComponent can be
used to specify any argument that can be ordinarily given to CMake's `target_link_libraries()`.

If you now compile and run the resulting
image you should see some output like the following:

```
Ping: sending hello...
Pong: received hello
Pong: sending world...
Ping: received world.
```
#### An example of structs and arrays for collections

A struct can be defined with the `struct` keyword.  The attributes that make
up the struct are listed in a `type` `name` format (similar to C).

Arrays are specified by appending the attribute name with a `[]`.  The size of
an array is set at code generation time when the setting for the attribute is
specified.

This is an example of a valid camkes specification.  The corresponding C file
is shown after.  To find a size of an attribute array, the sizeof macro can be
used as shown in the example.

```camkes
struct client_config {
    string name;
    int age;
    int height;
}
struct cat {
    int b[];
    int c;
}

component Client {
    control;
    attribute client_config config;
    attribute cat array_in_struct;
}

assembly {
    composition {
        component Client client;
    }

    configuration {
        client.config = {"name": "Zed","age": 39, "height": 34+4};
        client.array_in_struct = {"b": [3,4,5,6], "c": 4};
    }
}

```

```c
#include <camkes.h>
#include <stdio.h>

int run(void)
{
    printf("struct: %s: height plus age is %d\n", config.name, config.age + config.height);
    printf("array_in_struct: array length: %d, first element %d\n", sizeof(array_in_struct.b) / sizeof(array_in_struct.b[0]), array_in_struct.b[0]);
    return 0;
}
```

#### Tutorial Summary

You should now have a reasonably comprehensive understanding of the basic
connector functionality available in CAmkES. The other apps in the CAmkES
project repository provide some more diverse system examples.

### Overview

The various parts that comprise CAmkES can be used in several ways, including
executing a standalone tool as an end user or importing a Python module to
perform programmatic operations. These two uses are broken up into the sections
below. [Command Line Arguments](#command-line-arguments) describes how to invoke
standalone CAmkES functionality, and [Modules](#modules) describes how to import
and use the various functional units. Importing CAmkES functionality as a module
is strictly more powerful than running the command line tool, but usage
is more complicated. Note that these sections only describe external
interaction with these artefacts. If you are interested in the internals of
these you will need to refer to the [Developers](#developers) section.

### Command Line Arguments

This section discusses the standalone tool that is part of the CAmkES
ecosystem. This can be run from the command line with a shell script wrapper
that checks its dependencies:

```bash
camkes.sh args...
```

The following command line arguments are available.

**--cache**, **-c**
**--cache-dir**

> In a complicated system, the compilation itself can be quite time intensive.
  CAmkES implements a template cache that reduces recompilation time within and
  across builds. The --cache option enables it.

**--cpp**
**--nocpp**

> Whether or not to run the C pre-processor over the ADL input specification
  before processing it. The ADL input specification, strictly, is not C source
  code, but sometimes it can be useful to have the ability to pre-process it as
  if it was. The CAmkES ADL grammar is sufficiently similar to C that you are
  unlikely to run into any problems in this respect.

**-D**, **--debug**
**-q**, **--quiet**
**-v**, **--verbose**

> Set the level of information and error reporting emitted. The last one of
  these options encountered on the command line takes precedence. Note that
  there is no option to set the default verbosity (which is more than --quiet,
  but less than --verbose). The verbosity setting is applied globally during
  execution. For example, applying --debug to inspect a parsing problem in the
  runner will also generate debugging output from the lexing phase.

**--default-priority**

> Threads in a seL4 system are all configured with an initial priority. This
  can be tuned via attributes, but otherwise threads inherit a global default.
  This parameter allows you to set the global default.

**--default-affinity**

> Threads and sched-contexts in a seL4 system are all configured with an initial
  affinity. This can be tuned via attributes, but otherwise threads inherit a
  global default, which is CPU index 0.

**--elf**, **-E**

> Pass an ELF file that is to contribute to the final CapDL specification of a
  system. This parameter allows you to pass in the compiled ELF binary of one of
  your component instances. The CAmkES build system should take care of passing
  this option.

**-f FILE**, **--file FILE**

> This argument sets FILE as the input to parse. This argument is required and
  only a single input file is supported.

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

**--largeframe**

> Back large virtual address space regions with large frames when possible. On
  ARM and IA32 platforms, multiple frame sizes are supported for mapping
  physical memory into address spaces. It is more efficient to use a single
  large frame to cover a region than many small frames. This flag controls
  whether this promotion to large frames happens automatically. Note that this
  does not affect DMA pools, for which mappings are controlled by the
  --largeframe-dma option below.

**--largeframe-dma**

> Back components' DMA pools with large frames when possible. This works
  entirely independently to the --largeframe option. The reason for this
  separation is that large frame promotion of a DMA pool on ARM can be a
  little complicated to achieve. For more information, see
  [Efficient DMA](#efficient-dma).

**--platform**, **-p**

> The target output platform. This determines some aspects of the environment
  that the template being rendered is expected to function in. This option is
  only relevant to the runner. Valid platforms are "architecture-semantics",
  "autocorres", "CIMP", "GraphViz" and "seL4". The "GraphViz" option is for
  producing visual representations of a system and the "seL4" option is for
  producing binaries. All other platforms are verification frameworks.

**--templates**, **-t**

> You can use this option to add an extra directory to search for templates
  before the built-in location. This can allow you to extend the available
  templates or even override the built-in templates.

**--version**

> Print basic version information and then exit.

The following options are all related to runtime optimisations within the
templates. Note that most of these are highly seL4 specific and would make no
sense in the context of another platform.

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

The following options are all related to verification of templates outputs.

**--fprovide-tcb-caps**
**--fno-provide-tcb-caps**

> By default each thread gets a cap to its own TCB. The only purpose of this is
  to allow it to suspend itself when it exits. These TCBs can complicate
  reasoning about a generated CapDL specification. This option elides these TCB
  caps at the cost of threads messily VM faulting when they exit.

### Modules

Each subset of CAmkES functionality is encapsulated in a Python module that
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

The result of parsing a CAmkES specification is an Abstract Syntax Tree (AST),
representing the input as a set of interconnected nodes. When using the default
parser, the object returned is of type, `LiftedAST`, which is defined in this
module. `LiftedAST` and its children all inherit from a base type, `ASTObject`,
that provides common functionality like traversal and comparison.

One of the AST objects is a class, `Reference`. Objects of this class are used
in the AST to represent symbols that refer to entities that are defined
elsewhere. During parsing, references are removed from the AST as they are
resolved to the entities to which they refer. In particular, if you are using
the default parser, the returned AST will never contain any `Reference`
objects.

In the code and in this document there is some discussion of 'collapsing' AST
references. This is meant to refer to replacing the `Reference` object in the
AST by the entity to which it refers. Note that this needs to be done by
reference so that you still only end up with a single copy of the entity, but
multiple pointers to it.

If you are not using the default CAmkES parser, but are assembling your own
from the [parser module](#camkes.parser), it is important to note that objects
of the classes in the AST module are only created in the stage 3 parser. If you
are inspecting the output of any low-level parser prior to stage 3, you will
not see objects from camkes.ast.

#### camkes.parser

If you need to manipulate the AST, rather than just simply printing it
out, you will want to import the parser as a module into your own code. After
importing this module, you can interact with the parser through the following
high-level API.

**`parse_file(filename, options=None)`**

> Parse a file into a `LiftedAST`. The `options` arguments is expected to be a
  namespace as constructed by the runner. If you have non-standard parsing
  requirements, you may find this function is insufficiently flexible for your
  needs. In this case, you will need to compose the low-level parsers. You can
  see a rough guide of how to do this in camkes/parser/parser.py.

**`parse_string(string, options=None)`**

> Parse a string into a `LiftedAST`. This function works identically to the
  previous in all respects, except obviously you will not have accurate
  filename information.

#### camkes.templates

This module contains functionality for looking up builtin templates. The
templates themselves are actually stored in this directory (camkes/templates)
as well to reduce confusion. The description below only describes the externally
facing behaviour of this module. If you need to understand how template lookups
actually work you will need to read the source code and comments.

The API only contains a single class through which all access is intended to
flow.

`Templates.`**`__init__(self, platform)`**

> Create a new template store in which templates can later be looked up. The
  category of templates that are available from this store is specialised via
  **`platform`**. At time of writing the valid values of **`platform`** are
  'seL4', 'CIMP' and 'GraphViz'.

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
  'seL4RPCCall.from.source'. If you provide an **`entity`** this is used as a guard
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

**_`dataport`_** (`#include <camkes.h>`)

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

**`void`&nbsp;_`dataport`_`_acquire(void)`**

> An acquire memory fence. Any read from the dataport preceding this fence in
  program order will take place before any read or write following this fence in
  program order. In uniprocessor environments, this is always a compiler memory
  fence. In multiprocessor environments, memory barrier instructions will be
  emitted if necessary, depending on the affinities of component instances
  connected by the dataport.

**`void`&nbsp;_`dataport`_`_release(void)`**

> A release memory fence. Any write to the dataport following this fence in
  program order will take place after any read or write preceding this fence in
  program order. In uniprocessor environments, this is always a compiler memory
  fence. In multiprocessor environments, memory barrier instructions will be
  emitted if necessary, depending on the affinities of component instances
  connected by the dataport.

**`size_t`&nbsp;_`dataport`_`_get_size(void)`**

> Returns the size for the specific dataport this function gets called for. In
  addition to this function, every component that has a dataport will be
  provided with a macro _`dataport`_`_size` that is defined to the size of the
  invdividual dataport. This macro allows declaring fixed size arrays, as the
  `C` language requires a constant-expression for this.

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

**`const char *get_instance_name(void)`** (`#include <camkes.h>`)

> Returns the name of this component instance. This can be helpful if you want
  to write component functionality that has different behaviour depending on
  which instance it is.

**`int`&nbsp;_`instance`_`_main(int thread_id)`**

> A component instance's entry point. This is generated by the platform and
  invokes the user's `run` function when complete.

**`int main(int thread_id)`** (in libsel4camkes.a)

> This function &mdash; the C entry point to a component &mdash; is provided by
  the platform. Components should not provide their own `main`.

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

**_`return`_&nbsp;_`procedure`_`_`_`method`_`(`_`args...`_`)`** (`#include <camkes.h>`)

> In a component that provides a procedure interface, things are somewhat
  reversed and the implementation calls functions that you are expected to
  provide. For each method in the procedure you are expected to provide a
  matching implementation. In a component that uses a procedure interface,
  functions of this form are available for you to call.

**`void`&nbsp;_`event`_`_emit(void)`** (`#include <camkes.h>`)

> In a component that emits an event a function prefixed with the event's name
  is available that causes the event to be sent.

**`void`&nbsp;_`event`_`_poll(void)`** (`#include <camkes.h>`)

> In a component that consumes an event a function prefixed with the event's
  name is available that returns whether there is a pending event. Note, this
  function never blocks.

**`int`&nbsp;_`event`_`_reg_callback(void (*callback)(void*), void *arg)`** (`#include <camkes.h>`)

> In a component that consumes an event a function prefixed with the event's
  name is available for registering a callback for this event. When the event
  is received, the provided function will be invoked with the argument provided
  when registering the callback. Note that registered
  callbacks take precedence over threads blocked on calls to _`event`_`_wait`.
  _`event`_`_reg_callback` returns 0 on success and non-zero if the callback
  could not be registered.

**`void`&nbsp;_`event`_`_wait(void)`** (`#include <camkes.h>`)

> In a component that consumes an event a function prefixed with the event's
  name is available that blocks until the event is received.

### Synchronization Primitives

CAmkES provides three primitives for intra-component mutual exclusion and synchronization.
Mutexes, semaphores, and binary semaphores are declared similarly to properties of a component definition:

```camkes
component Foo {
  has mutex m;
  has semaphore s;
  has binary_semaphore b;
}
```

By default semaphores have a count (initial value) of 1, and binary semaphores have an initial value
of 0. This can be adjusted using an attribute:

```camkes
assembly {
  composition {
    component Foo f;
    ...
  }
  configuration {
    f.s_value = 4;
    f.b_value = 1; // must be either 0 or 1
    ...
  }
}
```

An application can lock or unlock a declared mutex and call post or wait on a
declared semaphore or binary semaphore. For example, for the above declarations, the following
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

/* Wait on a binary semaphore b */
int b_wait(void);

/* Post to a binary semaphore b */
int b_post(void);
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

```camkes
assembly {
  composition {
    component Foo f;
    ...
  }
  configuration {
    f.dma_pool = 8192;
  }
}
```

This declares an 8KB pool of memory that is available for DMA operations.
Within the component you must allocate and release pointers into this region
with the `camkes_dma_alloc` and `camkes_dma_free` functions described above.
The allocation function accepts a size and alignment constraint, but be aware
that allocation may not be efficient or guaranteed when requesting more than
4Kb. Note that if you declare a DMA pool that is not page-aligned (4K on the
platforms we support) it will automatically be rounded up.

#### Efficient DMA

For components that need to perform large DMA operations, you will need to
allocate a large DMA pool. Backing the virtual address space mappings for such
a pool with 4KB frames can lead to performance issues. For this reason, you may
wish to use the command line option --largeframe-dma to back DMA pools with
large frames.

This is relatively straightforward on IA32, but on an ARM platform you may run
into a limitation of the GNU Assembler that prevents the large alignments
required by the DMA pool. Support for working around this is provided by the
CAmkES build system, but is a little complicated, so the precise steps for
achieving this in a CAmkES project are documented below.

Enable large frame promotion for the DMA pool in your build configuration:

```bash
cmake . -DCAmkESDMALargeFramePromotion=ON
```

On older versions of binutils, if you were using a large enough DMA pool
to get promoted to large frames with an alignment constraint that was rejected
by the GNU Assembler, you should see output like the following:

```
/tmp/ccfGhK5Z.s: Assembler messages:
/tmp/ccfGhK5Z.s:1483: Error: alignment too large: 15 assumed
```
Updating binutils should fix this issue.

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

```camkes
component Foo {
  attribute string a;
  attribute int b;
}
```

These attributes are set in the configuration section of the assembly:

```camkes
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
```

This results in the specified values being available as global variables
in the glue code with the same name as the attribute.

```c
const char * a = "Hello, World!";
const int b = 42;
```

#### Attribute's conversion to literal

Unfortunately, the `C` language (in contrast to C++) does not support using
`lvalues` as literals (e.g. when declaring an array), even if declared as const,
so we need to introduce a "mechanism" for converting CAmkES attributes to
literals.

The `CAMKES_CONST_ATTR` macro has been introduced for that purpose.

Actually, the macro does not really convert arbitrary variables, but rather
CAmkES declares a const variable and also adds a respective macro to the code,
which is then used for that purpose.

Usage example is presented below:

```C
/* main.camkes */
assembly {
    composition {
        component FOO foo;
    }
    configuration {
        foo.lenData  = 16;
    }
}

/* Foo.c */
const int foo[CAMKES_CONST_ATTR(lenData)] = { 0 };

int run()
{
#if CAMKES_CONST_ATTR(lenData) < 0xF0
    return 0;
#else
    return 1;
#endif
}
```

### Hardware Components

A hardware component represents an interface to hardware in the form of a component.
Declaring a component with the `hardware` keyword creates a hardware component.

```camkes
component Device {
  hardware;

  provides IOPort io_port;
  emits Interrupt irq;
  dataport Buf mem;
}
```

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

```camkes
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
```

#### Configuration

Each type of hardware component interface has some configuration required for it
to work. This is done by setting attributes of instances of device components.

##### MMIO

The physical address of the memory, and size (in bytes) to make available
to a connected component must be specified. The example below specifies that
the port named `mem` of the component instance `d` is a 0x1000 byte region
starting at physical address 0xE0000000.

```camkes
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
    d.mem_paddr = 0xE0000000;
    d.mem_size = 0x1000;
    ...
  }
}
```

##### Interrupts

Depending on the platform different information needs to specified to
connect a hardware interrupt source with a components interrupt handler.

On ARM and if you are using the legacy x86 PIC controller then simply an
interrupt number must be specified. The example below specifies that
the event will be emitted when interrupt number 2 is received.

```camkes
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
    d.irq_irq_number = 2;
    ...
  }
}
```

If using the newer I/O APIC controller on x86 then you need to describe
the I/O APIC source and provide a destination vector. An I/O APIC source
is described in terms of

* Physical I/O APIC controller indexed starting at 0. Typically a system
  only has one of these
* Pin, ranging from 0 to 23, on the I/O APIC controller that the interrupt
  will come in on
* The trigger mode and polarity of the interrupt

The destination vector is a number in the range of 0 to 107 and must be unique
across all destination vectors defined in an assembly.

Selecting between edge and level trigger modes is done by setting the
`*_irq_ioapic_level` attribute where a value of `1` means level triggered and
`0` means edge triggered. Similarly the active polarity is configured by
the `*_irq_ioapic_polarity` attribute where a value of `1` means active
low and `0` means active high.

To change the previous example to connect an interrupt on I/O APIC 0, pin 2
that is edge triggered with active high polarity you would change

```camkes
d.irq_irq_number = 2;
```

To become

```camkes
d.irq_irq_type = "ioapic";
d.irq_irq_ioapic = 0;
d.irq_irq_ioapic_pin = 2;
d.irq_irq_ioapic_polarity = 0;
d.irq_irq_ioapic_level = 0;
d.irq_irq_vector = 42;
```

With the `vector` being arbitrarily chosen as `42`

An interrupt that is edge triggered and active high can be more concisely
declared as an ISA interrupt by

```camkes
d.irq_irq_type = "isa";
d.irq_irq_ioapic = 0;
d.irq_irq_ioapic_pin = 2;
d.irq_irq_vector = 42;
```

Similarly if this interrupt were to be level triggered and active low it
could be declared as a PCI interrupt by

```camkes
d.irq_irq_type = "pci";
d.irq_irq_ioapic = 0;
d.irq_irq_ioapic_pin = 2;
d.irq_irq_vector = 42;
```

##### IO Ports

The allowable range of IO Ports must be specified.
The example below specifies that the hardware component instance
`d` may access IO ports greater than or equal to 0x60, and less
than 0x64.

```camkes
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
```

### Port Privileges

CAmkES allows the programmer to specify access rights that instances have over
the ports connecting them to other instances. This is done by setting the
`*_access` attribute of the port. The value of the attribute must be a string
containing the letters "R", "W" and "X", giving the port read, write and execute
privileges, respectively. If left unspecified, full access will be given.

In the example below, instance `f` has read-only access to `port_a`, and
instance `b` has read/write access to `port_a`. Instance `b` has read-only
access to `port_b`. Instance `a` has read/write/execute access to `port_b` even
though it's not explicitly stated, as this is the default.

```camkes
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
    connection seL4SharedData port_a(from f.data_a, to b.data_a);
    connection seL4SharedData port_b(from f.data_b, to b.data_b);
    ...
  }
  configuration {
    f.data_a_access = "R";
    b.data_a_access = "RW;
    f.data_b_access = "R";
    ...
  }
}
```

### Thread Model

CAmkES components are typically multithreaded and, to prevent race conditions,
it is often necessary to understand what threads exist in your system.

Firstly there is a single active thread. This is the thread of control that
calls the component's entry point for components declared `control`. This
thread is present even in non-control components in order to perform
initialisation actions.

Each interface your component interacts with, either as an incoming or outgoing
interface, induces another thread within the component. Initial synchronisation
of these threads and their various setup activities is all handled by generated
code. Note that this per-interface thread is present even for interfaces that
you may think of as passive. For example, dataports. This is merely an
implementation artefact and may change in future.

One thing that may not be intuitive for users is that you have no guarantee as
to which thread will invoke an event callback. If you have registered a
callback for an event you are receiving, you should not assume that any
thread-local state persists between invocations. This is because the thread
which invokes a callback may not be the same thread as was used last time the
callback was invoked.

### Thread Priorities

Each thread in a CAmkES system has a priority that determines how it is
scheduled by seL4. These priorities default to a value given by the
`--default-priority` command-line argument to the runner. In a given system, it
it possible to adjust the priority of a specific thread with an attribute that
has specific semantics. To adjust the priority of the control thread (the
thread that calls `run`), use the `_priority` attribute:

```camkes
assembly {
  composition {
    component Foo f;
    ...
  }
  configuration {
    f._priority = 100;
  }
}
```

To adjust the priority of an interface thread, use an attribute named with the
name of the interface and the suffix ``_priority'':

```camkes
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
```

If you want to adjust the priority of every thread within a given component
instance, you can use a general component attribute:

```camkes
configuration {
  f.priority = 100;
}
```

For more information about the specifics of the seL4 scheduler, please refer to
the seL4 documentation.

### Thread CPU affinity

Each thread in a CAmkES system also has a processor affinity. This affinity will
by default bind all threads to CPU index 0, bootstrap-processor. In a system
where seL4 is built without multicore, setting this value above 0 is illegal.

```camkes
component Mycomponent {
    /* ... */
    uses Myinterface i;
}

assembly {
    composition {
        component Mycomponent c;
    }
    configuration {
        /* Run all threads in "c" on CPU 1 */
        c.affinity = 1;
    }
}
```

Alternatively:

```camkes
configuration {
    /* Run only the control thread on CPU 1, but run the rest of the threads
     * in this component on the "default" CPU (index 0).
     */
    c._affinity = 1;
}
```

Or perhaps:

```camkes
configuration {
    /* Run only the interface thread for "i" on CPU 1, but run the rest of the
     * threads in this component on the "default" CPU (index 0).
     */
    c.i_affinity = 1;
}
```

### Thread Stacks

Each CAmkES thread has a stack provided for it for use at runtime, as is
typical. Stack size defaults to 4K, but this default can be adjusted through
the relevant build system configuration option. Additionally the stacks of
individual threads within a component can be set with attributes:

```camkes
configuration {

  // Assign foo's control thread an 8K stack
  foo._stack_size = 8192;

  // Assign the interface thread for inf in foo a 16K stack
  foo.inf_stack_size = 16384;

}
```

Note that stacks must have a size that is 4K aligned, so if you assign a thread
a stack size that is not 4K aligned it will be rounded up. Stacks have a 4K
unmapped "guard page" either side of them. This is a debugging aid to force a
virtual memory fault when threads underrun or overrun their stacks.

### Scheduling Domains

In CAmkES, it is possible to specify the domain each thread belongs to, by setting attributes.
Each interface of each component instance will have an associated thread, and
there will be an additional thread per-component to perform initialisation and
optionally act as the control thread. For interface threads, their domain can be
specified by setting the attribute `<interface>_domain` of the instance. For
control threads, the attribute `_domain` of the instance can be set.

```camkes
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
    connection seL4RPCCall c(from f.i, to b.o);
    ...
  }
  configuration {
    f._domain = 0;  // domain of control thread of f
    b.o_domain = 1; // domain of o interface of b
    ...
  }
}
```

### Userspace RPC Transfer Buffers

By default, the majority of RPC connectors exchange data through a
kernel-managed IPC buffer. RPC communication involving longer messages can be
optimised by exchanging data through userspace buffers instead of the IPC
buffer. To achieve this, set up an `seL4SharedData` connection and assign a
custom attribute:

```camkes
component Foo {
  uses iface i;
  dataport Buf d;
}

component Bar {
  provides iface j;
  dataport Buf e;
}

assembly {
  composition {
    component Foo foo;
    component Bar bar;

    connection seL4RPCCall conn(from foo.i, to bar.j);
    connection seL4SharedData ubuf(from foo.d, to bar.e);
  }
  configuration {
    conn.buffer = "ubuf";
  }
}
```

There are a few limitations to be aware of when using this technique. The only
RPC connector that supports this style of userspace communication at time of
writing is `seL4RPCCall`. The RPC connection must be 1-to-1 and the
`seL4SharedData` connection must connect the same two component instances. The
size of the buffer (determined by the dataports' type) is flexible, but if you
use a buffer that is too small to accommodate RPC data you will trigger runtime
errors during parameter marshalling.

### Multi-Assembly Applications

CAmkES allows programmers to define an arbitrary number of assemblies for their application.
Different assemblies may appear in different files, provided that they are appropriately
included in the main ADL file. At compile time, the bodies of each
assembly are merged together, with all declared names remaining the same.
Thus, naming conflicts can occur on items declared in different assemblies.

```camkes
assembly {
  composition {
    component Foo f;
  }
}

assembly {
  composition {
    component Bar b;
    connection seL4RPCCall c(from f.a, to b.a);
  }
  configuration {
    f.some_attribute = 0;
  }
}
```

The example above is equivalent to:

```camkes
assembly {
  composition {
    component Foo f;
    component Bar b;
    connection seL4RPCCall c(from f.a, to b.a);
  }
  configuration {
    f.some_attribute = 0;
  }
}
```

### Hierarchical Components

#### Syntax

A component definition may include a composition and configuration section.
The composition and configuration sections must be the last items in the component definition.
The composition and configuration sections may appear in any order. A composition section
can be included without a configuration, however a configuration section is only allowed
if there is a composition.

```camkes
component Foo_Impl {
  provides iface_a a_impl;
  attribute string str;
}

component Foo {
  provides iface_a a;

  composition {
    component Foo_Impl fi;
    export fi.a_impl -> a;
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
    connection seL4RPCCall c(from b.a, to f.a);
  }
}
```

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

```camkes
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
    component Foo_Impl f.fi;
    connection seL4RPCCall c(from b.a, to f.fi.a_impl);
  }
  configuration {
    f.fi.str = "Hello, World!";
  }
}
```

#### Examples

##### Connecting multiple compound components

It's possible for both sides of a connection to be virtual interfaces:

```camkes
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
    export fi.a_impl -> a;
  }
}

component Bar {
  uses iface_a a;

  composition {
    component Bar_Impl bi;
    export bi.a_usage -> a;
  }
}

assembly {
  composition {
    component Foo f;
    component Bar b;
    connection seL4RPCCall c(from b.a, to f.a);
  }
}
```

This example compiles to:

```camkes
component Foo_Impl {
  provides iface_a a_impl;
}

component Bar_Impl {
  uses iface_a a_usage;
}

assembly {
  composition {
    component Foo_Impl f.fi;
    component Bar_Impl b.bi;
    connection seL4RPCCall c(from b.bi.a_usage, to f.fi.a_impl);
  }
}
```

##### Compound component with non-virtual interfaces

A component can have both virtual and implemented interfaces:

```camkes
component Foo_Impl {
  provides iface_a a_impl;
}

component Foo {
  provides iface_a a;
  provides iface_b b;

  composition {
    component Foo_Impl fi;
    export fi.a_impl -> a;
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
    connection seL4RPCCall c(from b.a, to f.a);
    connection seL4RPCCall c(from b.b, to f.b);
  }
}
```

This example compiles to:

```camkes
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
    component Foo_Impl f.fi;
    connection seL4RPCCall c(from b.a, to f.fi.a_impl);
    connection seL4RPCCall c(from b.b, to f.b);
  }
}
```

##### Deeper Hierarchy

So far, each example has had a compound component containing only non-compound component instances.
It's possible to have a hierarchy of components of an arbitrary depth.

```camkes
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
    connection seL4RPCCall c(from a1.ap, to a2.ap);
    export a2.a_impl -> a_impl;
  }
}

component Foo {
  provides iface_a a;

  composition {
    component Foo_Impl fi;
    export fi.a_impl -> a;
  }
}

component Bar {
  uses iface_a a;
}

assembly {
  composition {
    component Foo f;
    component Bar b;
    connection seL4RPCCall c(from b.a, to f.a);
  }
}
```

This example compiles to:

```camkes
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

    component A_Piece1 f.fi.a1;
    component A_Piece2 f.fi.a2;

    connection seL4RPCCall f.fi.c(from f.fi.a1.ap, to f.fi.a2.ap);
    connection seL4RPCCall c(from b.a, to f.fi.a2.a_impl);
  }
}
```

### Hierarchical Attributes

Attributes of internal instances and internal connections declared in the composition section
of a compound component may be set to refer to attributes of that compound component. During
hierarchy resolution, values of referring attributes are set to copies of the values of
their corresponding referent attributes.

#### Syntax

The `<-` operator is used to set an attribute to refer to another. Lines of the following form
may appear in the configuration section of a compound component:

```camkes
entity_name.attribute_name <- local_attribute_name;
```

Here, `entity_name` is the name of a component instance or connection declared in the component's
composition section, `attribute_name` is the name of an attribute of the entity, and
`local_attribute_name` is the name of an attribute of the composition component.

#### Example

```camkes
component B {
  ...
  attribute string b_str;
}

component A {
  ...
  attribute string a_str;

  composition {
    ...
    component B b;
  }
  configuration {
    ...
    b.b_str <- a_str;
  }
}

assembly {
  composition {
    ...
    component A a;
  }
  configuration {
    ...
    a.a_str = "Hello, World!";
  }
}
```

This example is resolved to the following:

```camkes
component B {
  ...
  attribute string b_str;
}

component A {
  ...
  attribute string a_str;
}

assembly {
  composition {
    ...
    component A a;
    component B a_b;
  }
  configuration {
    ...
    a.a_str = "Hello, World!";
    a_b.b_str = "Hello, World!";
  }
}
```

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

```camkes
procedure algebra_iface {
  include <vector.h>;
  Vector add(Vector a, Vector b);
}
```

C source files that need access to this data type can include the file with:

```c
#include <vector.h>
```

To make the build system aware of the header file, for each component that uses it, the following must be added
to the application's `CMakeLists.txt` (replacing the name `Component` with the name of the component):

```
DeclareCAmkESComponent(Component INCLUDES include/vector.h)
```

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

```camkes
component A {
  control;

  include "int_array.h";
  dataport IntArray int_arr;
}
```

This would give the implementation access to a global pointer, which points to
an appropriately large region of memory for the data type:

```c
extern volatile IntArray * int_arr;
```

### Single Address Space Components (Groups)

By default, each component instance in an application is given its own address
space. This is ideal for isolation, but this separation does not come for free
and inter-address space communication is necessarily more expensive than local
communication. To colocate two component instances in a single address space,
they can be grouped together:

```camkes
assembly {
  composition {
    group my_group {
      component Foo foo;
      component Bar bar;
    }
  }
}
```

Any references to such instances now need to be qualified by their group name.
For example, to connect the above two instances:

```camkes
...
connection seL4RPCCall conn(from my_group.foo.inf1,
  to my_group.bar.inf2);
...
```

When component instances are colocated, another connector becomes available.
The `seL4DirectCall` connector collapses RPC communication into a direct
function call. Its usage is identical to other connectors:

```camkes
...
connection seL4DirectCall conn(from my_group.foo.inf1,
  to my_group.bar.inf2);
...
```

Using this connector between two components that are not colocated is incorrect
and will trigger an error.

#### Caveats

When colocating component instances in a single address space, the intent is
for the environment of the instances to be as close to indistinguishable as
possible (with the exception of performance characteristics) from full
separation. This abstraction is not perfect and there are some mechanisms that
have slightly different semantics when used in a single address space scenario
and in an isolated scenario.

Parameters of direction `out` of certain types are typically heap-located in an
isolated component instance. This is still true in a colocated environment, but
when using the `seL4DirectCall` connector, these are located in the _callee's_
heap, not the caller's as may be otherwise expected. Freeing one of these
pointers to the incorrect heap will result in heap corruption and should be
avoided. Conversely, _not_ freeing this pointer will leak memory and should also
be avoided. The recommended technique to work around this is to introduce a back
channel to the callee when necessary:

```camkes
procedure my_proc {
  /* The following procedure will return a parameter, `x`,
   * that is a pointer into the callee's heap. It cannot
   * be directly freed by the caller and needs to be
   * passed back to the callee.
   */
  void foo(out string x);

  /* We provide a back channel for this. */
  include <stdint.h>;
  void remote_free(uintptr_t p);
}

component Caller {
  control;
  uses my_proc f;
}

component Callee {
  provides my_proc g;
}

assembly {
  composition {
    component Caller caller;
    component Callee callee;

    connection seL4DirectCall conn(from caller.f, to callee.g);
  }
}
```

It is then possible to implement both components' code in such a way that
memory is always freed to the correct heap:

```c
/* Caller.c */

int run(void) {
  char *x;
  f_foo(&x);
  printf("received %s\n", x);
  f_remote_free((uintptr_t)x);
  return 0;
}
```

```c
/* Callee.c */

void g_foo(char **x) {
  *x = strdup("hello world");
}

void g_remote_free(uintptr_t p) {
  free((void*)p);
}
```

This is cumbersome, but at least allows one to write safe code. In a
continually evolving project, it may not be known in advance whether
`seL4DirectCall` will be used. In these situations, it is recommended to use a
free wrapper that detects where a pointer is hosted. In the case of a simple
static heap region (the default), a wrapper can be constructed as follows:

```c
/* Caller.c */

static void safe_free(void *p) {
  /* These symbols are defined by generated code and
   * specify the bounds of the heap.
   */
  extern char *morecore_area;
  extern size_t morecore_size;

  if ((uintptr_t)p >= (uintptr_t)morecore_area &&
      (uintptr_t)p < (uintptr_t)morecore_area + morecore_size) {
    /* The pointer is in our heap. */
    free(p);
  } else {
    /* The pointer is in the callee's heap. */
    f_remote_free((uintptr_t)p);
  }
}

int run(void) {
  char *x;
  f_foo(&x);
  printf("received %s\n", x);
  safe_free(x);
  return 0;
}
```

The preceding discussion dealt with `out` parameters, but note that the same
issue exists on _both_ sides of an `seL4DirectCall` connection using `inout`
parameters. That is, the argument to the callee and the final value to the
caller are both pointers that would normally point into a local heap, but now
potentially point into a remote heap.

As a result of toolchain limitations,
[link-time optimisations](https://gcc.gnu.org/wiki/LinkTimeOptimization) cannot
be applied to a component group. If you have LTO enabled in your build settings
it will be ignored for component groups.

### Global Include Directories

CAmkES allows users to define a list of directories that will be searched
when resolving imports of .camkes files (components and interfaces).
`CAmkESAddImportPath(interfaces)` will append a directory to this search path.
There is an additional path for templates which can be modified by calling
`CAmkESAddTemplatesPath(templates)`. The repository global-components repository
is an example of these mechanisms being used to import components, interfaces
and templates into a project. The target project simply needs to include
`global-components.cmake` to enable these modules to be referred to from within
the project's camkes files. Below is an example of importing global-components:
```cmake
find_file(GLOBAL_COMPONENTS_PATH global-components.cmake PATHS ${CMAKE_SOURCE_DIR}/projects/global-components/ CMAKE_FIND_ROOT_PATH_BOTH)
mark_as_advanced(FORCE GLOBAL_COMPONENTS_PATH)
if("${GLOBAL_COMPONENTS_PATH}" STREQUAL "GLOBAL_COMPONENTS_PATH-NOTFOUND")
    message(FATAL_ERROR "Failed to find global-components.cmake. Consider cmake -DGLOBAL_COMPONENTS_PATH=/path/to/global-components.cmake")
endif()
include(${GLOBAL_COMPONENTS_PATH})

```

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

### Cached Hardware Dataports

By default, memory backing hardware dataports (`seL4HardwareMMIO`) is mapped uncached.
Typically such a dataport will be backed by a device's memory mapped registers rather
than main memory. In such cases it's generally desired that after writing to a register
the effect of the write is felt immediately, and changes to device registers are observable
as soon as they occur, so mapping this memory uncached makes sense. There are however,
cases where it is preferable to map this memory cached instead.

For example, consider a system that updates a large memory mapped frame buffer for
a display, by writing to it one word at a time. If this buffer was mapped uncached,
each word written to the buffer would incur the full time taken to write to memory.
If instead, the buffer was mapped cached, each word would be written to the cache,
incurring a much shorter write time. Cache lines would then be written back to memory
at a later point. This optimization works on the assumption that the throughput of
the cache being written back to memory is higher than that of the CPU writing
directly to memory a word at a time. After all the data has been written to the buffer,
the cache must be flushed to ensure the data is actually in the buffer.

CAmkES provides a mechanism for flushing the cache, but currently it is a no-op
on all architectures other than ARM. On x86, the DMA engine is cache-coherent,
so there's no reason to explicitly flush the cache after writing to a cached
hardware dataport.

#### Marking a hardware dataport as cached

To map a hardware dataport cached, set the `<instance>.<interface>_hardware_cached` attribute to `true`:

    component DisplayDevice {
      hardware;
      dataport FrameBuffer framebuffer;
    }

    component DisplayDriver {
      ...
      dataport FrameBuffer framebuffer;
    }

    assembly {
      composition {
        component DisplayDevice display_device;
        component DisplayDriver display_driver;
        ...

        connection seL4HardwareMMIO fbconn(
          from display_driver.framebuffer,
          to display_device.framebuffer
        );
      }
      configuration {
        ...
        display_device.framebuffer_hardware_cached = true; /* <-- set this attribute
                                                   *     to mark dataport
                                                   *     as cached
                                                   */
      }
    }

#### Manipulating the cache

After writing to a cached hardware dataport, or potentially prior to reading from it,
it is necessary to manipulate the cache to ensure a consistent view of the memory
between the CPU and any devices. CAmkES provides a function for each hardware dataport
for doing cache operations on the range of addresses inside the dataport.

For a dataport interface named `framebuffer`, the function that operates on the cache
will be

```c
int framebuffer_cache_op(size_t start_offset, size_t size, dma_cache_op_t cache_op)
```

`start_offset` and `size` are the offset in bytes into the dataport to start flushing,
and the number of bytes to flush respectively. `cache_op` is one of the three defined
cache operations: `DMA_CACHE_OP_CLEAN`, `DMA_CACHE_OP_INVALIDATE`, `DMA_CACHE_OP_CLEAN_INVALIDATE`.
The function returns 0 on success and non-zero on error

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
syntax and functionality. Note that the default Jinja delimiters have been modified
to `/*` and `*/` to let syntax highlighting in C work more naturally.

Within a given template you have a variable `me` that functions like native
Python's `self`. It refers to the object of relevance to the current template.
So, for example, during instantiation of the component source file, it refers
to the component instance being instantiated. In certain general "top-level"
templates, there is no particular "subject." In these templates, for example
`camkes-gen.cmake`, `me` will be `None`.

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
these are only usable for passing objects between templates that share related
`me` references.

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

### Reply Capabilities

The seL4 system call, `seL4_Call`, generates transient capabilities called
reply capabilities (see the seL4 documentation for more specific details). Care
must be taken when writing template code in order to avoid interfering with the
functionality of another piece of template code that may have created reply
capabilities. If you are not using reply capabilities yourself, there is a
simple rule to remember:

* always call `camkes_protect_reply_cap()` before performing an operation that
  would cause a wait on a synchronous endpoint.

This call is idempotent (you can call it multiple times in sequence with no ill
effects), though be aware it may modify the contents of your IPC buffer. You
do not need to perform this operation when sending on a synchronous endpoint or
waiting on a notification, however it _is_ necessary when performing
batched system calls like `seL4_ReplyRecv` or `seL4_Call` on a synchronous
endpoint.

If you are _receiving_ reply capabilities in your own template and calling
external functionality before using them, you need to be aware that they can be
overwritten when execution is outside your template. To safe guard yourself
against this, there is a complementary rule:

* always call `camkes_declare_reply_cap(...)` when you have just received a
  reply capability.

Note that you need to pass this function an empty capability slot into which to
save the reply capability if it is about to be overwritten. In order to support
saving of this reply capability on demand, CAmkES needs a capability to the
current thread's CNode. This needs to be setup by your template code. Some
variant of the following code needs to be executed for each thread that could
receive a reply capability:

```c
/*# Allocate a cap to our own CNode. #*/
/*- set cnode = alloc_cap('cnode', my_cnode) -*/
/* Configure a TLS pointer to our own CNode cap. */
camkes_get_tls()->cnode_cap = /*? cnode ?*/;
```

When you need to use a reply capability you have protected, you should check
the `reply_cap_in_tcb` member of the CAmkES TLS structure and, if the capability
is no longer in your TCB, call `camkes_unprotect_reply_cap()` and deal with any
possible error that may have occurred. The functional API for dealing with
reply capabilities is provided below. Though this is technically part of the
[runtime API](#runtime-api), it is included here because user code is never
expected to call these functions.

**`int camkes_declare_reply_cap(seL4_CPtr shadow_slot)`** (`#include <camkes/tls.h>`)

> Identify to the CAmkES library that you are in possession of a reply
  capability in your TCB. CAmkES only handles a single reply capability
  currently and, as such, you should not call this function when you have
  previously declared a pending reply capability you have not yet discarded.
  This essentially says to CAmkES, "I have a reply cap in my TCB; please save
  it to `shadow_slot` if it is in risk of being deleted."

**`void camkes_protect_reply_cap(void)`** (`#include <camkes/tls.h>`)

> Guard any potential pending reply capability against deletion by saving it
  now. Note that this function accepts no arguments and returns nothing. It is
  designed to be called unconditionally from generated code that believes it
  may be about to overwrite a reply capability. There is no point providing a
  result to the caller because the caller is not the conceptual "owner" of
  the capability and does not know how to deal with a failure to protect it.
  You should always call this code in your template if you believe a reply
  capability could be present and the operation you are about to perform has a
  chance of deleting it.

**`seL4_Error camkes_unprotect_reply_cap(void)`** (`#include <camkes/tls.h>`)

> Discard any information relating to a current pending reply capability. This
  is designed to be called by the original declarer of a reply capability when
  it is about to use (or discard) that capability. Note that this returns a
  potential error that was encountered when some intermediate code tried to
  protect the capability and it failed. The return value is essentially a
  result from `seL4_CNode_SaveCaller`. This should _only_ be called when you
  know the reply cap you need is no longer in your TCB. That is, you should
  check the `reply_cap_in_tcb` member of the CAmkES TLS structure to determine
  if calling this function is necessary.

To get a more concrete idea of how these functions are used, you can refer to
the seL4RPCCall connector that uses this mechanism.

One final thing to note is that this functionality assumes cooperative
templates. There is nothing to prevent a malicious template omitting a call to
`camkes_protect_reply_cap()` and wilfully destroying pending reply
capabilities.

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
to leave helpful comments. I've occasionally used tags in the comments that
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

### Parser Internals

* camkes/parser/*

The previous section, [camkes.parser](#camkes.parser), describes the high-level
interface to the CAmkES parser. This parser is assembled from a pipeline of
lower-level parsers. These are each described as a "stage" in parsing. To
understand them, it is necessary to understand a few variants of Abstract
Syntax Tree representations that are referred to in the source code. The
following representations are described in order from least to most abstract:

* **Augmented input** This is not an AST, as such, but rather a tuple of source
  data and a set of read files.
* **Raw AST** This is a tree of `plyplus.stree`s.
* **Augmented AST** This is a list of `plyplus.stree`s with attached
  information about their original source data and the file they came from.
* **Lifted AST** This is the most abstract programmatic representation of an
  input specification and the form developers will come to be most familiar
  with. It is a tree of objects from [camkes.ast](#camkes.ast).

The various low-level parsers are each responsible for a specific AST
transformation, with the high-level parser stringing them all together for ease
of use. The low-level parsers are:

* **Stage 0** Reads an input file and optionally runs the C pre-processor over
  it. This "parser" is really just a more full featured version of the `open`
  call.
* **Stage 1** Parses input using `plyplus`. Note that this is where the CAmkES
  grammer (camkes/parser/camkes.g) comes into play.
* **Stage 2** Resolves `import` statements. This parser repeatedly calls back
  into the stage 1 parser to parse further sources. Note that from here on,
  `import` statements do not appear in the AST.
* **Stage 3** Lifts the `plyplus` AST into the objects of
  [camkes.ast](#camkes.ast). This is generally the most intensive parse phase
  and inherently the most fragile as it encodes much of the semantics of the
  CAmkES input language.
* **Stage 4** Resolves semantic references. From here on, no
  `camkes.ast.Reference`s remain in the AST.
* **Stage 5** Collapses `group`s. The `group` keyword is used to colocate
  component instances into a single address space. This stage removes groups
  from the AST, assigning the same address space to their contained instances.
* **Stage 6** Combines multiple assemblies. It is possible for more than one
  `assembly` block to be specified in a CAmkES input specification, in which
  case the intended assembly is the concatentaion of all of them. This stage
  performs that concatenation.
* **Stage 7** Flattens component hierarchies. Component instances that are
  nested inside other components are hoisted to the top-level assembly by this
  stage.
* **Stage 8** Resolves attribute references. Settings can be given a value that
  references another attribute (using the `<-` operator). This stage resolves
  these references to concrete values.
* **Stage 9** Freezes the AST. This stage transforms various AST internal data
  structures into optimised forms and makes AST modification from this point on
  impossible.

With this information, looking back at the high-level parser, one can see that
it simply chains these stages together. It is possible to programmatically
construct a differing or partial parser by composing the low-level parsers in a
different manner.

#### Pre-Compiled Templates

 * camkes/runner/Renderer.py

The Jinja templating engine works by compiling template code to native Python
code, which it then runs to produce the generated output. This compilation to
Python code is normally performed in each execution. To speed up this process,
when caching is enabled, the templates are compiled to the cache directory. In
future executions, template rendering optimistically fetches pre-compiled
templates from this cache. On a cache miss, it falls back to the original
template sources.

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
defined within the camkes-gen.cmake template. This set of libraries has been extended on demand to cover all
base seL4 infrastructure. This can be freely expanded to cover more libraries
with no expected surprises.

Be aware that these libraries will be unconditionally depended upon and linked
into all CAmkES components. That is, the user's lists of libraries defined in
their application CMakeLists.txt will all be silently extended to include the core
libraries.

### Testing

CAmkES has a set of unit tests and a set of integration tests. The unit tests
are structured per-module, with each module's tests in a subdirectory of its
source:

 * camkes/ast/tests
 * camkes/internal/tests
 * camkes/parser/tests
 * camkes/runner/tests
 * camkes/templates/tests

The unit tests use Python's
[unittest](https://docs.python.org/2/library/unittest.html) framework. The
simplest way to execute them is from the top-level wrapper script:

```bash
./alltests.py
```

Alternatively, any finer granularity of test cases may be selected:

```bash
# Run all AST unit tests
./camkes/ast/tests/runall.py

# Run only AST hashing assumption tests
./camkes/ast/tests/runall.py TestHashingAssumptions

# Run only the specific test for hashing None
./camkes/ast/tests/runall.py TestHashingAssumptions.test_none
```

The integration tests are contained in the CAmkES project repository under the
directory tests/. Again, the simplest way to execute these is with a wrapper
script:

```bash
./tests/run-all.py
```

Alternatively, you can run individual integration tests:

```bash
# Test simple RPC
./tests/arm-simple.tcl
```
