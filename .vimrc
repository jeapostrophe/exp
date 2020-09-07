" XXX Consider using neovim-lsp: https://jdhao.github.io/2019/11/20/neovim_builtin_lsp_hands_on/

" Use "hybrid" (both absolute and relative) line numbers
" set number relativenumber

" Use the system clipboard
set clipboard=unnamed

" Use a color column on the 80-character mark
set colorcolumn=80

" Press <tab>, get two spaces
set expandtab shiftwidth=2

" Show `▸▸` for tabs: 	, `·` for tailing whitespace: 
set list listchars=tab:▸▸,trail:·

set nocompatible            " disable compatibility to old-time vi
set showmatch               " show matching brackets.
set ignorecase              " case insensitive matching
set hlsearch                " highlight search results
set autoindent              " indent a new line the same amount as the line just typed

let g:python_host_prog  = '/usr/bin/python'
let g:python3_host_prog = '/usr/local/bin/python3'

call plug#begin()
Plug 'iCyMind/NeoSolarized'
Plug '/usr/local/opt/fzf'
Plug 'junegunn/fzf.vim'
Plug 'ledger/vim-ledger' " XXX Completion doesn't work

"Plug 'chrisbra/unicode.vim' " XXX Need to understand better
"Plug 'junegunn/vim-easy-align' " XXX Untested
"Plug 'benekastah/neomake'  " XXX Untested
"Plug 'bling/vim-airline' " XXX Need to configure
"Plug 'tpope/vim-fugitive'  " XXX Doesn't seem to work with plug
"Plug 'tpope/vim-obsession' " XXX Untested
"Plug 'tpope/vim-eunuch' " XXX Need to understand
"Plug 'tmux-plugins/vim-tmux' " XXX Untested
"Plug 'kassio/neoterm' " XXX Untested
"Plug 'Shougo/unite.vim' " XXX Untested
"Plug 'Shougo/deoplete.nvim' " XXX Untested
"Plug 'Shougo/neopairs.vim' " XXX Untested
"Plug 'Shougo/echodoc.vim' " XXX Untested
"Plug 'Shougo/context_filetype.vim' " XXX Untested
" Plug 'Shougo/vimshell.vim' " not ported to neovim yet?
" Plug 'let-def/vimbufsync'         " pathogen
" Plug 'the-lambda-church/coquille' " pathogen
call plug#end()

" fzf.vim
" :Files
" :Buffers
" :Ag
" :[B]Lines
" :Commands
" --- Add ! to run in fullscreen
" --- CTRL-[T: Tab][X: Split][V: Vert Split] to open

" call pathogen#infect()

" set esckeys
set timeoutlen=300 ttimeoutlen=100

" Simulate some Emacs keys
" XXX Not working
inoremap <M-x> :
nnoremap <M-x> :
cnoremap <C-g> <Esc>

" Turn on mouse
set mouse=a

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

set termguicolors
syntax on
set background=light
colorscheme NeoSolarized

filetype plugin indent on

"let g:deoplete#enable_at_startup = 1

let mapleader = ';'
let g:mapleader = ';'
inoremap ;; <Esc>
nnoremap <leader>r :!jrun %<CR>

function! s:word_sink(w)
  call append(line('.'), a:w)
endfunction

command! -bang PU call fzf#run({'source': 'cat /Users/jay/Dev/scm/github.jeapostrophe/shakes/apat/hard', 'sink': function('s:word_sink')})

" Notes
" v/V/C-V visual selection
" G - end of file
" :e - revert file
