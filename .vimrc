call plug#begin()
Plug 'tpope/vim-sensible'
Plug 'chrisbra/unicode.vim'
Plug 'junegunn/fzf', { 'dir': '~/.fzf', 'do': './install --all' }
call plug#end()



set backupskip=/tmp/*,/private/tmp/*
set backspace=indent,eol,start
nnoremap <Esc>A <up>
nnoremap <Esc>B <down>
nnoremap <Esc>C <right>
nnoremap <Esc>D <left>
inoremap <Esc>A <up>
inoremap <Esc>B <down>
inoremap <Esc>C <right>
inoremap <Esc>D <left>

execute pathogen#infect()
syntax on
filetype plugin indent on
