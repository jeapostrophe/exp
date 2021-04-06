set clipboard=unnamedplus " system keyboard
let g:clipboard = {
          \   'name': 'wsl',
          \   'copy': {
          \      '+': 'pbcopy',
          \      '*': 'pbcopy',
          \    },
          \   'paste': {
          \      '+': 'pbpaste',
          \      '*': 'pbpaste',
          \   },
          \   'cache_enabled': 0,
          \ }

set colorcolumn=80 " mark 80
set expandtab shiftwidth=2 " Press <tab>, get two spaces

set textwidth=79
set wrap linebreak
" ^ XXX It would be nice to have some indication that a line is wrapped
set formatoptions-=t

set list listchars=tab:▸▸,trail:·

set nocompatible " disable compatibility to old-time vi
set showmatch    " show matching brackets.
set ignorecase   " case insensitive matching
set hlsearch     " highlight search results
set autoindent   " indent a new line the same amount as the line just typed

set shellcmdflag=-ic

let g:fzf_command_prefix = 'Fzf'
let g:dispatch_no_maps = 1

call plug#begin()
Plug 'iCyMind/NeoSolarized'
Plug '/usr/share/doc/fzf/examples'
Plug 'junegunn/fzf.vim'
Plug 'itchyny/lightline.vim'
" Plug 'neovim/nvim-lspconfig' " Works, but slow
Plug 'wlangstroth/vim-racket'
" Plug 'sunaku/vim-dasht'
" Plug 'wellle/context.vim'
" Plug 'tpope/vim-dispatch' " XXX :Make hides successful output
" Plug 'lervag/wiki.vim'
" Plug 'lervag/wiki-ft.vim'
Plug 'tpope/vim-commentary' " gcc
Plug 'neovimhaskell/haskell-vim'
Plug 'ledger/vim-ledger' " XXX Completion doesn't work
" Plug 'jiangmiao/auto-pairs' " XXX annoying
Plug 'Lenovsky/nuake'
" Plug 'junegunn/goyo.vim'

"Plug 'chrisbra/unicode.vim' " XXX Need to understand better
"Plug 'junegunn/vim-easy-align' " XXX Untested
"Plug 'benekastah/neomake'  " XXX Untested
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
" Plug 'reedes/vim-pencil'
" Plug 'junegunn/limelight.vim'
" Plug 'reedes/vim-lexical'
" Plug 'reedes/vim-litecorrect'
" Plug 'reedes/vim-one'
" Plug 'Shougo/vimshell.vim' " not ported to neovim yet?
" Plug 'let-def/vimbufsync'         " pathogen
" Plug 'the-lambda-church/coquille' " pathogen
" tpope/vim-surround
call plug#end()

" racket
let g:racket_hash_lang_regexp="^$" " don't guess filetype

" Fzf
let g:fzf_preview_window = ['right:50%:hidden', 'ctrl-/']
let g:fzf_layout = { 'window': {
      \ 'width': 0.9,
      \ 'height': 0.7,
      \ 'highlight': 'Comment',
      \ 'rounded': v:false } }
command! -nargs=* -bang FzfRgLike call fzf#vim#grep("rg --column --line-number --no-heading --color=always --smart-case -t".expand('%:e')." -- ".shellescape(<q-args>), 1, <bang>0)

" lightline
let g:lightline = {}
let g:lightline.colorscheme = 'solarized'
let g:lightline.active = {
      \ 'left': [ [ 'mode', 'paste' ],
      \           [ 'readonly', 'filename', 'modified' ] ],
      \ 'right': [ [ 'lineinfo' ], [ 'filetype' ] ] }
let g:lightline.inactive = {
      \ 'left': [ [ 'filename' ] ],
      \ 'right': [ [ 'lineinfo' ] ] }
let g:lightline.component_function = {
      \ 'readonly': 'LightlineReadonly' }
let g:lightline.mode_map = {
      \ 'n' : 'N',
      \ 'i' : 'I',
      \ 'R' : 'R',
      \ 'v' : 'v',
      \ 'V' : 'V',
      \ "\<C-v>": 'Cv',
      \ 'c' : 'C',
      \ 's' : 's',
      \ 'S' : 'S',
      \ "\<C-s>": 'Cs',
      \ 't': 'T',
      \ }
function! LightlineReadonly()
  return &readonly && &filetype !=# 'help' ? 'RO' : ''
endfunction
set noshowmode " hide mode re: lightline

" XXX use ~/.jwm/bin/uni

set timeoutlen=300 ttimeoutlen=100

set backupskip=/tmp/*,/private/tmp/*
set backspace=indent,eol,start
set whichwrap+=<,>,h,l,[,] " left goes to prev line

set mouse=a

" Emacs keys
vnoremap <Del> d
vnoremap <Backspace> d
" this is M-x on OS X
nnoremap ≈ <C-o>:
inoremap ≈ <C-o>:
cnoremap ≈ <C-o>:
cnoremap <C-g> <C-c>
onoremap <C-g> <C-c>
nnoremap <Up> gk
inoremap <Up> <C-o>gk
nnoremap <Esc>A gk
inoremap <Esc>A <C-o>gk
nnoremap <Down> gj
inoremap <Down> <C-o>gj
nnoremap <Esc>B gj
inoremap <Esc>B <C-o>gj
nnoremap <Esc>C <right>
inoremap <Esc>C <right>
nnoremap <Esc>D <left>
inoremap <Esc>D <left>
imap <C-a> <Home>
vmap <C-a> <Home>
omap <C-a> <Home>
nmap <C-a> <Home>
imap <C-e> <End>
vmap <C-e> <End>
omap <C-e> <End>
nmap <C-e> <End>
inoremap <C-l> <C-o>zz<C-o><C-l>
nnoremap <C-l> zz
nmap <C-s> :w<CR>
imap <C-s> <C-o>:w<CR>
nmap <C-w> :q<CR>
nmap <C-w><C-w> :q!<CR>
imap <C-d> <Esc>
nnoremap <S-Tab> <<
inoremap <S-Tab> <C-d>
set makeprg=jrun\ %:p " XXX change to autocmd on filetype?
nnoremap <C-Space> :w<CR>:make!<CR>
nnoremap <C-m> :w<CR>:make!<CR>

nnoremap <C-g> :FzfRgLike<CR>
nnoremap <C-g><C-g> :FzfRg<CR>
nnoremap <C-f> :FzfBLines<CR>
nnoremap <C-f><C-f> :FzfFiles %:h<CR>
nnoremap <C-b> :FzfFiles<CR>
nnoremap <C-b><C-b> :FzfBuffers<CR>
nnoremap <C-h> :FzfCommands<CR>
" nnoremap K :call Dasht(dasht#cursor_search_terms())<Return>
" ^ Ctrl-T to get a new tab

nnoremap <C-i> gg=G<C-o><C-o>
" ^ XXX defer to external tool, maybe with https://github.com/Chiel92/vim-autoformat

nnoremap <C-left> <C-W><C-H>
nnoremap <C-right> <C-W><C-L>
nnoremap <C-up> <C-W><C-K>
nnoremap <C-down> <C-W><C-J>
inoremap <C-left> <Esc><C-W><C-H>
inoremap <C-right> <Esc><C-W><C-L>
inoremap <C-up> <Esc><C-W><C-K>
inoremap <C-down> <Esc><C-W><C-J>
tnoremap <C-left> <C-\><C-n><C-W><C-H>
tnoremap <C-right> <C-\><C-n><C-W><C-L>
tnoremap <C-up> <C-\><C-n><C-W><C-K>
tnoremap <C-down> <C-\><C-n><C-W><C-J>
" M-w
nnoremap ∑ :only<CR>
" M-/
inoremap <M-/> <C-n>
inoremap ÷ <C-n>
" ^ XXX the menu is really annoying. I want to fuzzy complete
inoremap <C-n> <C-o>n

" Terminal stuff
tnoremap <Esc> <C-\><C-n>
au BufEnter term://* startinsert

" Nuake
" XXX make this a command that focuses on it if it is open
nnoremap <C-x> :Nuake<CR>
inoremap <C-x> <C-o>:Nuake<CR>
tnoremap <C-x> <C-\><C-n>:Nuake<CR>

" XXX shift doesn't work on these and they don't follow Sexprs
nnoremap <M-Left> b
inoremap <M-Left> <C-o>b
nnoremap <M-Right> w
inoremap <M-Right> <C-o>w

" XXX how to comment out region

" enable shift-select
set keymodel=startsel,stopsel
set sel=exclusive
set selectmode=key

" Colors
set termguicolors
syntax on
set background=light
colorscheme NeoSolarized
let g:neosolarized_visibility = "high"
let g:neosolarized_contrast = "high"

" Highlight TODO, FIXME, NOTE, etc.
if has('autocmd') && v:version > 701
    augroup todo
        autocmd!
        autocmd Syntax * call matchadd(
                    \ 'Debug',
                    \ '\v\W\zs<(NOTE|TODO|FIXME|XXX)>'
                    \ )
    augroup END
endif

filetype plugin indent on
au! BufRead,BufNewFile *.rktd setfiletype racket
au! BufRead,BufNewFile *.scrbl setfiletype scribble
au! BufRead,BufNewFile *.rsh setfiletype javascript

" Auto load session; maybe use mhinz/vim-startify
let g:session_file = getcwd() . '/.session.vim'
fu! SaveSess()
  execute 'mksession! ' . g:session_file
endfunction
fu! RestoreSess()
  if filereadable(g:session_file)
    execute 'so ' . g:session_file
    if bufexists(1)
      for l in range(1, bufnr('$'))
        if bufwinnr(l) == -1
          exec 'sbuffer ' . l
        endif
      endfor
    endif
  endif
endfunction
if argc() == 0
 autocmd VimLeave * call SaveSess()
 autocmd VimEnter * nested call RestoreSess()
endif

" Helper functions
command! JeCopyFile %w !pbcopy

" Notes
" v/V/C-V visual selection
" G - end of file
" :e - revert file
" / - search
" % - move between delimiters
" " n/N - fwd/bck search
" gq - M-q

" fzf.vim
" --- CTRL-[T: Tab][X: Split][V: Vert Split] to open
"
" :Goyo --- Focus
