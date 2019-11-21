
syntax keyword muleKeywords
	\ fn
	\ let
	\ in
	\ match
	\ with
	\ end
	\ where

syntax keyword muleType
	\ type
	\ rec
	\ all

syntax keyword muleImport
	\ import
	\ embed

syntax keyword muleTodo contained TODO FIXME XXX BUG

syntax match muleComment "\v#.*$" contains=muleTodo

syntax match muleVar "\v<[a-z_][a-zA-Z0-9_!?-]*"

syntax match muleOperator "\v\.\.\."
syntax match muleOperator "\v\{"
syntax match muleOperator "\v\}"
syntax match muleOperator "\v:"
syntax match muleOperator "\v\-\>"
syntax match muleOperator "\v\="
syntax match muleOperator "\v\|"

syntax match muleCtor "\v<[A-Z][a-zA-Z0-9_]*"

syntax match muleUnQuote "\v\~(\@?)[a-z_][.a-zA-Z0-9_?!-]*"

syntax match muleNumber "\v<[0-9]([_0-9]*)(\.[0-9]+)?([eE][0-9]+)?"

syntax region muleString start=/\v"/ skip=/v\\./ end=/\v"/ contains=muleEscape,muleBadEscape
syntax region muleCharacter start=/\v'/ skip=/v\\./ end=/\v'/ contains=muleEscape,muleBadEscape
syntax region muleDocString start=/\v"""/ end=/\v"""/

syntax match muleEscape "\v\\[\\\"'trn]" contained
syntax match muleBadEscape "\v\\[^\\\"'trn]" contained


highlight default link muleTodo Todo
highlight default link muleComment Comment
highlight default link muleKeywords Keyword
highlight default link muleOperator Operator
highlight default link muleCtor Constant
highlight default link muleVar Identifier
highlight default link muleType Typedef
highlight default link muleUnQuote Macro
highlight default link muleImport Include
highlight default link muleDocString String
highlight default link muleString String
highlight default link muleCharacter Character
highlight default link muleNumber Number
highlight default link muleEscape Special
highlight default link muleBadEscape Error
