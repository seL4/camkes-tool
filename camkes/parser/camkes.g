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

/* The grammar for CAmkES architecture specifications. This is intended to be
 * consumed by a plyplus parser.
 */

start: (assembly_decl | component_decl | composition_decl |
        configuration_decl | connector_decl | import |
        procedure_decl | struct_decl | /* Allow empty statements: */ ';')*;

ID: '[a-zA-Z_]\w*'
        /* Everything that's a keyword ends up matching ID, so we need to
         * explicitly spell out exceptions here. Note that we don't bother with
         * native types because any context they can appear in accepts
         * arbitrary IDs to represent C typedefs.
         */
        (%unless
            ASSEMBLY: 'assembly';
            ATTRIBUTE: 'attribute';
            BUF: 'Buf';
            CHAR: 'char';
            COMPONENT: 'component';
            COMPOSITION: 'composition';
            CONFIGURATION: 'configuration';
            CONNECTION: 'connection';
            CONNECTOR: 'connector';
            CONSUMES: 'consumes';
            CONTROL: 'control';
            DATAPORT: 'dataport';
            DATAPORT_TYPE: 'Dataport';
            DATAPORTS_TYPE: 'Dataports';
            EMITS: 'emits';
            EVENT_TYPE: 'Event';
            EVENTS_TYPE: 'Events';
            EXPORT: 'export';
            FALSE1: 'False';
            FALSE2: 'false';
            FROM: 'from';
            GROUP: 'group';
            HARDWARE: 'hardware';
            HAS: 'has';
            IMPORT: 'import';
            IN: 'in';
            INCLUDE: 'include';
            INOUT: 'inout';
            INT: 'int';
            INTEGER: 'integer';
            MAYBE: 'maybe';
            MUTEX: 'mutex';
            OUT: 'out';
            PROCEDURE: 'procedure';
            PROCEDURE_TYPE: 'Procedure';
            PROCEDURES_TYPE: 'Procedures';
            PROVIDES: 'provides';
            REFIN: 'refin';
            SEMAPHORE: 'semaphore';
            BINARY_SEMAPHORE: 'binary_semaphore';
            SIGNED: 'signed';
            STRUCT: 'struct';
            STRING: 'string';
            TEMPLATE: 'template';
            THREAD: 'thread';
            THREADS: 'threads';
            TRUE1: 'True';
            TRUE2: 'true';
            TO: 'to';
            UNSIGNED: 'unsigned';
            USES: 'uses';
            VOID: 'void';
            WITH: 'with';
            );
/* For the case where we need an AST-visible ID */
id: ID | BUF;

assembly_decl: ASSEMBLY id? assembly_defn;
assembly_defn: '\{' composition_sing configuration_sing? '\}'
             | '\{' configuration_sing composition_sing '\}';

composition_sing: COMPOSITION reference ';'
                | composition_decl;

configuration_sing: CONFIGURATION reference ';'
                  | configuration_decl;

attribute_decl: attribute_parameter ('=' item)? ;

component_decl: COMPONENT id? component_defn;
component_defn: '\{' (attribute | consumes | control | dataport | emits |
                      hardware | include | mutex | provides | semaphore | binary_semaphore |
                      uses)*
                    ((composition_sing configuration_sing?) | configuration_sing composition_sing)? '\}';
component_ref: reference | component_defn;

struct_decl: STRUCT id struct_defn;
struct_defn: '\{' (attribute_decl ';')* '\}';
struct_ref: reference | struct_defn;
@attribute: ATTRIBUTE attribute_decl ';';
consumes: maybe? CONSUMES id id ';';
control: CONTROL ';';
dataport: maybe? DATAPORT dataport_type id ';';
dataport_type: id | BUF '\(' numeric_expr '\)';
emits: EMITS id id ';';
hardware: HARDWARE ';';
mutex: HAS MUTEX id ';';
provides: PROVIDES reference id ';';
semaphore: HAS SEMAPHORE id ';';
binary_semaphore: HAS BINARY_SEMAPHORE id ';';
uses: maybe? USES reference id ';';
maybe: MAYBE;

composition_decl: COMPOSITION id? composition_defn;
composition_defn: '\{' (instance_defn | connection_defn | group_decl | export)* '\}';

instance_defn: COMPONENT component_ref id ';';
connection_defn: CONNECTION connector_ref id '\(' (connection_end (',' connection_end)* ','?)? '\)' ';';
connection_end: (from | to) reference;
from: FROM;
to: TO;

group_decl: GROUP id? group_defn;
group_defn: '\{' instance_defn* '\}';

export: EXPORT reference '->' reference ';';

configuration_decl: CONFIGURATION id? configuration_defn;
configuration_defn: '\{' setting* '\}';
setting: id '\.' id (('=' item) | ('<-' attribute_reference)) ';';
attribute_reference: id ('\.' id)*;

connector_decl: CONNECTOR id? connector_defn;
connector_defn: '\{' FROM hardware_bare? connector_end_type connector_properties ';' TO hardware_bare? connector_end_type connector_properties ';' '\}';
hardware_bare: HARDWARE;
connector_ref: reference | connector_defn;
connector_end_type: DATAPORT_TYPE | EVENT_TYPE | PROCEDURE_TYPE
                  | DATAPORTS_TYPE | EVENTS_TYPE | PROCEDURES_TYPE;
@connector_properties:
                     | template
                     | threads
                     | template threads
                     | threads template;
@template: TEMPLATE multi_string;
@threads: WITH numeric_expr (THREAD | THREADS);

import: IMPORT (multi_string | angle_string) ';';

include: INCLUDE (multi_string | angle_string) ';';

method_decl: (VOID | type) id '\(' (VOID | (method_parameter (',' method_parameter)* ','?)?) '\)' ';';
@method_parameter: method_array_parameter | method_scalar_parameter;
method_array_parameter: method_scalar_parameter '\[' '\]';
method_scalar_parameter: direction? type id;
direction: IN | INOUT | OUT | REFIN;
@attribute_parameter: attribute_array_parameter | attribute_scalar_parameter;
attribute_array_parameter: attribute_scalar_parameter '\[' '\]';
attribute_scalar_parameter: type id;
type: signed_int | unsigned_int | struct_type | char | signed_char | unsigned_char | STRING | struct_ref | ID;
signed_int: (SIGNED? (INT | INTEGER)) | SIGNED;
unsigned_int: UNSIGNED (INT | INTEGER)?;
char: CHAR;
signed_char: SIGNED CHAR;
unsigned_char: UNSIGNED CHAR;
struct_type: STRUCT id;

procedure_decl: PROCEDURE id? procedure_defn;
procedure_defn: '\{' (method_decl | attribute_decl | include)* '\}';

reference: id ('\.' id)*;

/* Numeric expressions */
@numeric_expr: precedence11;
precedence11: precedence10 ('\?' numeric_expr ':' precedence10)?;
precedence10: precedence9 (lor precedence9)*;
lor: '\|\|';
precedence9: precedence8 (land precedence8)*;
land: '&&';
precedence8: precedence7 (bor precedence7)*;
bor: '\|';
precedence7: precedence6 (xor precedence6)*;
xor: '\^';
precedence6: precedence5 (band precedence5)*;
band: '&';
precedence5: precedence4 ((eq | neq) precedence4)*;
eq: '==';
neq: '!=';
precedence4: precedence3 ((lt | lte | gt | gte) precedence3)*;
lt: '<';
lte: '<=';
gt: '>';
gte: '>=';
precedence3: precedence2 ((ls | rs) precedence2)*;
ls: '\<\<';
rs: '\>\>';
precedence2: precedence1 ((add | sub) precedence1)*;
add: '\+';
sub: '-';
precedence1: precedence0 ((mul | div | mod | pow) precedence0)*;
mod: '%';
mul: '\*';
div: '/';
pow: '\*\*';
@precedence0: number | '\(' numeric_expr '\)' | unary_minus | unary_plus
            | logical_not | bitwise_not | boolean_literal;
unary_minus: '-' precedence0;
@unary_plus: '\+' precedence0;
logical_not: '!' precedence0;
bitwise_not: '~' precedence0;

/* Literals */
number: '(0x[0-9a-fA-F]+|\d+(\.\d+)?)';
multi_string: quoted_string+;
quoted_string: '"[^"]*"'; // "
angle_string: '<[^>]*>';
list: '\[' (item (',' item)* ','?)? '\]';
dict: '\{' (key ':' item (',' key ':' item)* ','?)? '\}';
@key: numeric_expr | multi_string;
@item: numeric_expr | multi_string | list | dict;
boolean_literal: TRUE1 | TRUE2 | FALSE1 | FALSE2;

/* Things to ignore */
SINGLE_LINE_COMMENT: '//.*' (%ignore);
MULTILINE_COMMENT: '/\*(.|\n)*?\*/' (%ignore) (%newline);
WHITESPACE: '[ \t\f]+' (%ignore);
NEWLINE: '\r?\n' (%ignore) (%newline);
CPP_DIRECTIVE: '\#.*' (%ignore);
