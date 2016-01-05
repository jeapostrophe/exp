call plug#begin()
Plug 'tpope/vim-sensible' " XXX Untested
Plug 'chrisbra/unicode.vim'
Plug 'junegunn/fzf', { 'dir': '~/.fzf', 'do': './install --all' }
Plug 'junegunn/fzf.vim'
Plug 'benekastah/neomake'  " XXX Untested
Plug 'bling/vim-airline'
Plug 'tpope/vim-fugitive'  " XXX Doesn't seem to work with plug
Plug 'tpope/vim-obsession' " XXX Untested
Plug 'tpope/vim-eunuch'
Plug 'tmux-plugins/vim-tmux' " XXX Untested
Plug 'kassio/neoterm' " XXX Untested
Plug 'Shougo/unite.vim' " XXX Untested
Plug 'Shougo/deoplete.vim' " XXX Untested
" Plug 'Shougo/vimshell.vim' " not ported to neovim yet?
Plug 'altercation/vim-colors-solarized'
call plug#end()

" XXX Intended to make ESC instant, but doesn't work
set esckeys
set timeoutlen=0 ttimeoutlen=0

" XXX need to have alt-arrows

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

syntax on
" XXX Doesn't seem to work in various ways... statusline is unreadable and
" comments aren't enabled
"set background=light
"colorscheme solarized
filetype plugin indent on

let g:deoplete#enable_at_startup = 1
