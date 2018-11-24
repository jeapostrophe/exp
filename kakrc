source "%val{config}/plugins/plug.kak/rc/plug.kak"

plug "alexherbo2/auto-pairs.kak"
hook global WinCreate .* %{
    auto-pairs-enable
}
# XXX Customize racket to not insert two 's

# XXX These colors are slightly wrong --- main text is too light
colorscheme solarized-light-termcolors

# Highlight matching parens/etc
add-highlighter global/ show-matching

# Wrapping stuff
set global autowrap_column 80
# XXX Make this only turn on when line is actually too long
# add-highlighter global/ column '%opt{autowrap_column}' default,red
# XXX Select entire paragraph first
map global normal = ' |par -w $kak_opt_autowrap_column<ret>'

# Highlight note words
add-highlighter global/ regex \b(TODO|FIXME|XXX|NOTE)\b 0:default+rb

# Highlight search results
set-face global search +bi
add-highlighter global/search dynregex '%reg{/}' 0:search

# Notes:
# <c-n> <c-p> to select completions
# FIFO buffer for REPL
# | to send to command
# Use a hook for BufCreate fn to put fn in recent
# Turn on linting
# Make Racket mode

# Questions
# - How do I cancel a selection?
# - How can I get alt-arrows to do what I want?
#   map global normal <s-left> or <a-right>
# - How do I move between matching things

# This is a long test string is it too long that I will try to use with par to see if it works.
