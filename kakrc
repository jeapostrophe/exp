source "%val{config}/plugins/plug.kak/rc/plug.kak"

plug alexherbo2/auto-pairs.kak
hook global WinCreate .* %{
    auto-pairs-enable
}
# XXX debug this
# XXX Customize racket to not insert two 's but add |

plug andreyorst/fzf.kak
map global normal <c-p> ': fzf-mode<ret>'
set-option global fzf_file_command 'fd'
# XXX Add Racket support to bat
set-option global fzf_highlighter 'bat'
# XXX Add Racket support to universal-ctags

# https://bitbucket.org/KJ_Duncan/kakoune-racket.kak/src

plug occivink/kakoune-sudo-write

# XXX Use personal wiki instead of org?

set global tabstop 2
set global indentwidth 2

# unicode insertion
map global insert  'λ'
map global normal  '<a-f>\|xargs uni<ret>'

# XXX Uses taskwarrior or todotxt

colorscheme solarized-light-termcolors

# Highlight matching parens/etc
# XXX highlight entire region
add-highlighter global/ show-matching
# XXX / register isn't empty when you delete everything in it
add-highlighter global/ dynregex '%reg{/}' 0:+u

set global makecmd 'mk' # XXX make mk better
set global grepcmd 'ag --column'
# XXX set search relative to current buffer path

# XXX Use ranger.kak
# XXX support bat in ranger - https://github.com/ranger/ranger/issues/1288

# Wrapping stuff
set global autowrap_column 72
set global autowrap_fmtcmd 'par w%c'
# XXX Make this only turn on when line is actually too long
# add-highlighter global/ column '%opt{autowrap_column}' default,red
# XXX Select entire paragraph first
# XXX defer to autowrap_fmtcmd (see how it does it)
map global normal = ' |par w$kak_opt_autowrap_column<ret>'

# Highlight note words
add-highlighter global/ regex \b(TODO|FIXME|XXX|NOTE)\b 0:default+rb

# Highlight search results
set-face global search +bi
add-highlighter global/search dynregex '%reg{/}' 0:search

# Notes:
# <c-n> <c-p> to select completions
# FIFO buffer for REPL (or tmux-repl)
# | to send to command
# Use a hook for BufCreate fn to put fn in recent
# Turn on linting
# Make Racket mode (look at scheme.kak)

# Disable indenting while pasting with \i

# XXX spelling not working

# Questions
# - How do I cancel a selection?
# - How can I get alt-arrows to do what I want?
#   map global normal <s-left> or <a-right>
# - How do I move between matching things

# XXX https://github.com/eraserhd/parinfer-rust/blob/master/rc/parinfer.kak

# XXX https://github.com/alexherbo2/distraction-free.kak
# 
# This is a long test string is it too long that I will try to use with par to see if it works.

# Keys how I like
map global normal <backspace> <a-d>
map global normal <del> d
map global insert <s-left> '<esc>H'
map global insert <s-right> '<esc>L'
map global insert <s-up> '<esc>K'
map global normal <a-up> ''
map global insert <s-down> '<esc>J'
map global normal <a-down> ''
map global normal <end> gl
map global insert <s-end> '<esc><s-end>'
map global normal <home> gh
map global insert <s-home> '<esc><s-home>'
map global prompt <c-g> '<esc>'

# XXX Use terminal cursor when kak only has one cursor - https://github.com/mawww/kakoune/issues/2194

# XXX use bracketed paste --- https://github.com/mawww/kakoune/pull/2465

# XXX alt arrows and S-alt arrows (normal & insert)

# XXX https://mail.google.com/mail/u/0/#search/!in%3Aspam+is%3Aunread+OR+is%3Astarred/FMfcgxvzLrKdpsVbVRJDjCvCVQlGHFMV

# XXX https://github.com/mawww/kakoune/issues/2611

# XXX https://discuss.kakoune.com/t/more-flexible-m/211

define-command -params 2 -docstring "match_pair_move [01] [01]" match_pair_move %{
  execute-keys %sh{
    SHIFT=$1
    DIRECTION=$2
    CURSOR=$(printf "\x$(printf %x ${kak_cursor_char_value})")
    PAIRS="$kak_opt_matching_pairs"

		ISPAIR=0
		PARITY=1
		LAST=
		OTHER=
		for i in $PAIRS ; do
			P=$(echo $i | sed "s/'//g")
			if [ -z "$OTHER" -a $ISPAIR == "1" ] ; then
				OTHER=$P
			fi
			if [ $PARITY == $DIRECTION ] ; then
				if [ $P == $CURSOR ] ; then
					ISPAIR=1
					if [ $DIRECTION -eq 0 ] ; then
						OTHER=$LAST
					fi
				fi
			fi
			LAST=$P
			PARITY=$(expr \( $PARITY + 1 \) % 2)
		done

		if [ $ISPAIR -eq 1 ] ; then
			if [ $DIRECTION -eq 0 ] ; then
				echo '<a-f>'${OTHER}
			else
				echo f${OTHER}
			fi
		else
			if [ $DIRECTION -eq 0 ] ; then
				echo '<a-b>'
			else
				echo '<a-e>'
			fi
	  fi
  }
}
map global normal <a-left> ':match_pair_move 0 0<ret>'
map global normal <a-right> ':match_pair_move 0 1<ret>'
map global normal <s-a-left> ':match_pair_move 1 0<ret>'
map global normal <s-a-right> ':match_pair_move 1 1<ret>'

# Filetypes
hook global WinSetOption filetype=(c|cpp) %{
  clang-enable-autocomplete
  clang-enable-diagnostics
  alias window lint clang-parse
  alias window lint-next-error clang-diagnostics-next                 
}

# System Clipboard
hook global NormalKey y|d|c %{ nop %sh{
  printf %s "$kak_main_reg_dquote" | pbcopy
}}
map global normal p '!pbpaste<ret>'
map global normal P '<a-!>pbpaste<ret>'
# XXX <a-p> <a-P> R <a-R>

# Simple Mappings
# XXX Shift down next line?
map global normal '#' :comment-line<ret>

# Modeline and focus info
# XXX Change the cursor shape instead
decl str focused
hook global FocusIn .* %{ set window focused ""  }
hook global FocusOut .* %{ set window focused " [UNFOCUSED]" }
set global modelinefmt '%val{bufname} %val{cursor_line}:%val{cursor_char_column} {{context_info}} {{mode_info}} %opt{filetype}%opt{focused}'

# XXX Use kitty

# XXX Use raart/kitty-init for running Racket testing
