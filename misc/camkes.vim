"
" Copyright 2017, Data61
" Commonwealth Scientific and Industrial Research Organisation (CSIRO)
" ABN 41 687 119 230.
"
" This software may be distributed and modified according to the terms of
" the BSD 2-Clause license. Note that NO WARRANTY is provided.
" See "LICENSE_BSD2.txt" for details.
"
" @TAG(DATA61_BSD)
"

" Vim syntax for ADL. Copy this to ~/.vim/syntax/ and add the following line to
" ~/.vim/filetype.vim:
"
"  augroup filetypedetect
"      au BufRead,BufNewFile *.camkes setfiletype camkes
"  augroup END

syn match CamkesCPP "^[ \t]*#.*$"
syn keyword CamkesKeyword assembly composition from to configuration control
    \ procedure hardware maybe dma_pool has mutex semaphore binary_semaphore group tcb_pool
    \ ep_pool notification_pool template untyped_mmios trusted with thread threads
    \ cnode_size_bits
syn match CamkesUntypedPool "\<simple_untyped[0-9]\+_pool\>"
syn match CamkesStackSize "\<[a-zA-Z0-9_]\+_stack_size\>"
syn match CamkesPriority "\<\(priority\|[a-zA-Z_][a-zA-Z0-9_]*_priority\|_priority\)\>"
syn match CamkesAffinity "\<\(affinity\|[a-zA-Z_][a-zA-Z0-9_]*_affinity\|_affinity\)\>"
syn match CamkesDataportAccess "\<[a-zA-Z_][a-zA-Z0-9_]*_access\>"
syn keyword CamkesType component connection attribute connector Procedure Event
    \ Dataport Events Procedures Dataports export
syn keyword CamkesCType int string char character unsigned signed
    \ void long refin in out inout int8_t uint8_t int16_t uint16_t int32_t uint32_t
    \ int64_t uint64_t integer struct Buf
syn keyword CamkesDependency uses provides emits consumes dataport
syn keyword CamkesImport import include
syn region Foldable start="{" end="}" fold transparent
syn match CamkesMultiLineComment "\/\*\_.\{-}\*\/"
syn match CamkesSingleLineComment "\/\/.*$"
syn match CamkesExportOperator "->"
syn match CamkesAttributeReferenceOperator "<-"
syn region CamkesString start='"' end='"'
syn region CamkesBuiltin start='<[^-]' end='>'
syn match CamkesNumber "\<\(0x\x\+\|-\?\d\+\(\.\d\+\)\?\)\>"
syn keyword CKeyword auto break case const continue default do else enum extern
    \ for goto if inline register restrict return sizeof static switch typedef
    \ union volatile while _Alignas _Alignof _Atomic _Bool _Complex _Generic
    \ _Imaginary _Noreturn _Static_assert _Thread_local __func__ __objc_yes
    \ __objc_no asm _Decimal32 _Decimal64 _Decimal128 __alignof __attribute
    \ __builtin_choose_expr __builtin_offsetof __builtin_types_compatible_p
    \ __builtin_va_arg __extension__ __imag __int128 __label__ __real __thread
    \ __FUNCTION__ __PRETTY_FUNCTION__ typeof __private_extern__
    \ __module_private__ __declspec __cdecl __stdcall __fastcall __thiscall
    \ __vectorcall __pascal __fp16 __alignof__ __asm __asm__ __attribute__
    \ __complex __complex__ __const __const__ __imag__ __inline __inline__
    \ __real__ __restrict __restrict__ __signed __signed__ __typeof __typeof__
    \ __volatile __volatile__ __builtin_convertvector __unknown_anytype
syn keyword CamkesBoolean true True false False

hi def link CamkesCPP PreProc
hi def link CamkesKeyword Statement
hi def link CamkesUntypedPool Statement
hi def link CamkesStackSize Statement
hi def link CamkesPriority Statement
hi def link CamkesDataportAccess Statement
hi def link CamkesType Type
hi def link CamkesCType Type
hi def link CamkesDependency Type
hi def link CamkesImport PreProc
hi def link CamkesMultiLineComment Comment
hi def link CamkesSingleLineComment Comment
hi def link CamkesString Constant
hi def link CamkesBuiltin Constant
hi def link CamkesNumber Constant
hi def link CamkesBoolean Constant
hi def link CamkesExportOperator Statement
hi def link CamkesAttributeReferenceOperator Statement
hi def link CKeyword Error
