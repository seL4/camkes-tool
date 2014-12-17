"
" Copyright 2014, NICTA
"
" This software may be distributed and modified according to the terms of
" the BSD 2-Clause license. Note that NO WARRANTY is provided.
" See "LICENSE_BSD2.txt" for details.
"
" @TAG(NICTA_BSD)
"

" Vim syntax for ADL. Copy this to ~/.vim/syntax/ and add the following line to
" ~/.vim/filetype.vim:
"
"  augroup filetypedetect
"      au BufRead,BufNewFile *.camkes setfiletype camkes
"  augroup END

syn match CamkesCPP "^[ \t]*#.*$"
syn keyword CamkesKeyword assembly composition from to configuration control
    \ procedure hardware maybe dma_pool has mutex semaphore group tcb_pool
    \ ep_pool aep_pool from_access to_access template
syn match CamkesUntypedPool "untyped[0-9]\+_pool"
syn keyword CamkesType component connection attribute connector Procedure Event
    \ Dataport
syn keyword CamkesCType int string char character unsigned signed
    \ void long in out inout
syn keyword CamkesDependency uses provides emits consumes
syn keyword CamkesImport import include
syn region Foldable start="{" end="}" fold transparent
syn match CamkesMultiLineComment "\/\*\_.\{-}\*\/"
syn match CamkesSingleLineComment "\/\/.*$"
syn region CamkesString start='"' end='"'
syn region CamkesBuiltin start='<' end='>'

hi def link CamkesCPP PreProc
hi def link CamkesKeyword Statement
hi def link CamkesUntypedPool Statement
hi def link CamkesType Type
hi def link CamkesCType Type
hi def link CamkesDependency Type
hi def link CamkesImport PreProc
hi def link CamkesMultiLineComment Comment
hi def link CamkesSingleLineComment Comment
hi def link CamkesString Constant
hi def link CamkesBuiltin Constant
