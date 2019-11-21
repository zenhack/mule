if exists('b:did_indent')
	finish
endif
let b:did_indent = 1

setlocal indentexpr=MuleIndent()
setlocal indentkeys+==end,=let,=in,0\,0\|

" Get the contents of line number lnum, minus any trailing whitespace and
" comment.
function! GetStrippedLine(lnum)
	return substitute(getline(a:lnum), '\v\s*#.*$', '', '')
endfunction

function EndsWith(line, options)
	for pat in a:options
		if a:line =~ ('\v' . pat . '$')
			return 1
		endif
	endfor
	return 0
endfunction

function StartsWith(line, options)
	for pat in a:options
		if a:line =~ ('\v^\s*' . pat)
			return 1
		endif
	endfor
	return 0
endfunction

function Is(line, options)
	for pat in a:options
		if a:line =~ ('\v^\s*' . pat . '$')
			return 1
		endif
	endfor
endfunction

function NotId(kwd)
	return a:kwd
endfunction

function! MuleIndent()

	let comma_start = '\v^\s*,'
	let pipe_start = '\v^\s*\|'

	let open_end = '\v(\[|\{|\)|let|with|\=)$'
	let close_end = '\v(\]|\}|\)|in|end)$'

	if v:lnum ==# 1
		" Top of the file
		return 0
	endif

	let prev_line = GetStrippedLine(v:lnum - 1)
	let this_line = GetStrippedLine(v:lnum)

	let ind = indent(v:lnum - 1)

	if prev_line =~ comma_start && this_line =~ comma_start
		return ind
	endif
	if prev_line =~ pipe_start && this_line =~ pipe_start
		return ind
	endif

	if prev_line =~ pipe_start && this_line =~ comma_start
		let ind -= 2 * &sw
		return ind
	endif

	if prev_line =~ open_end
		" '\v\=$' " && this_line =~ pipe_start
		if prev_line =~ '\v^\s*,'
			" Something like
			" , type t =
			"     | Foo ...
			let ind += 2 * &sw
		else
			" Not part of a comma list; probably
			"
			" let type t =
			"   | Foo ...
			let ind += &sw
		endif
		return ind
	endif

	if this_line =~ close_end
		let ind -= &sw
	endif

	if prev_line =~ close_end && this_line =~ comma_start
		let ind -= &sw
		if prev_line =~ '\vend$'
			let ind -= &sw
		endif
	end

	return ind
endfunction
