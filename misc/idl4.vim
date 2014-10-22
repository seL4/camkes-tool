"
" Copyright 2014, NICTA
"
" This software may be distributed and modified according to the terms of
" the BSD 2-Clause license. Note that NO WARRANTY is provided.
" See "LICENSE_BSD2.txt" for details.
"
" @TAG(NICTA_BSD)
"

" Vim syntax for IDL. Copy this to ~/.vim/syntax/ and add the following line to
" ~/.vim/filetype.vim:
"
"  augroup filetypedetect
"      au BufRead,BufNewFile *.idl4 setfiletype idl4
"  augroup END

syn keyword IDLType interface in out inout procedure
syn keyword IDLCType int string smallstring char void unsigned signed integer character float double real boolean bool pointer int8_t int16_t int32_t int64_t uint8_t uint16_t uint32_t uint64_t
syn keyword IDLImport import include
syn region Foldable start="{" end="}" fold transparent
syn match IDLMultiLineComment "\/\*\_.\{-}\*\/"
syn match IDLSingleLineComment "\/\/.*$"
syn region IDLString start='"' end='"'

hi def link IDLType Type
hi def link IDLCType Type
hi def link IDLImport PreProc
hi def link IDLMultiLineComment Comment
hi def link IDLSingleLineComment Comment
hi def link IDLString Constant
