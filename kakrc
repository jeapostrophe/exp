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

plug occivink/kakoune-sudo-write

# XXX Use personal wiki instead of org?

# XXX change tab width to 4

# XXX insert lambda (and other unicode)
# Use jwm/uni and send text back to \ to it as $1

# XXX Uses taskwarrior or todotxt

colorscheme solarized-light-termcolors

# Highlight matching parens/etc
# XXX highlight entire region
add-highlighter global/ show-matching
# XXX / register isn't empty when you delete everything in it
add-highlighter global/ dynregex '%reg{/}' 0:+u

set global makecmd 'mk'
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

# XXX spelling not working

# Questions
# - How do I cancel a selection?
# - How can I get alt-arrows to do what I want?
#   map global normal <s-left> or <a-right>
# - How do I move between matching things

# This is a long test string is it too long that I will try to use with par to see if it works.

# Filetypes
hook global WinSetOption filetype=(c|cpp) %{
  clang-enable-autocomplete
  clang-enable-diagnostics
  alias window lint clang-parse
  alias window lint-next-error clang-diagnostics-next                 
}

# System Clipboard
map global user -docstring 'paste (after) from clipboard' p '!pbpaste<ret>'
map global user -docstring 'paste (before) from clipboard' P '<a-!>pbpaste<ret>'
map global user -docstring 'yank to clipboard' y '<a-|>pbcopy<ret>'
map global user -docstring 'replace from clipboard' R '|pbcopy<ret>'

# Simple Mappings
# XXX Shift down next line?
map global normal '#' :comment-line<ret>
