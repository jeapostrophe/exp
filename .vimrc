" Use "hybrid" (both absolute and relative) line numbers
" set number relativenumber

set clipboard=unnamed " system keyboard
set colorcolumn=80 " mark 80
set expandtab shiftwidth=2 " Press <tab>, get two spaces

" Show `▸▸` for tabs: 	, `·` for tailing whitespace: 
set list listchars=tab:▸▸,trail:·
" XXX try to get these to be highlighted

set nocompatible " disable compatibility to old-time vi
set showmatch    " show matching brackets.
set ignorecase   " case insensitive matching
set hlsearch     " highlight search results
set autoindent   " indent a new line the same amount as the line just typed

" let g:python_host_prog  = '/usr/bin/python'
" let g:python3_host_prog = '/usr/local/bin/python3'

set shellcmdflag=-ic " read .profile, but I read this might be bad

let g:fzf_command_prefix = 'Fzf'
let g:dispatch_no_maps = 1

call plug#begin()
Plug 'iCyMind/NeoSolarized'
Plug '/usr/local/opt/fzf'
Plug 'junegunn/fzf.vim'
Plug 'itchyny/lightline.vim'
" Plug 'neovim/nvim-lspconfig' " Works, but slow
Plug 'wlangstroth/vim-racket'
Plug 'sunaku/vim-dasht'
Plug 'wellle/context.vim'
"Plug 'tpope/vim-dispatch' " XXX hides successful output

"Plug 'ledger/vim-ledger' " XXX Completion doesn't work
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
call plug#end()

" racket
let g:racket_hash_lang_regexp="^$" " don't guess filetype

" Fzf
let g:fzf_preview_window = 'right:60%'
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
      \ 'right': [ [ 'lineinfo' ],
      \            [ 'percent' ],
      \            [ 'filetype' ] ] }
let g:lightline.inactive = {
      \ 'left': [ [ 'filename' ] ],
      \ 'right': [ [ 'lineinfo' ],
      \            [ 'percent' ] ] }
let g:lightline.component_function = {
      \ 'readonly': 'LightlineReadonly' }
function! LightlineReadonly()
  return &readonly && &filetype !=# 'help' ? 'RO' : ''
endfunction
set noshowmode " hide mode re: lightline
" XXX set laststatus=0 ?
" XXX show the result of tw

" lsp
" lua <<EOF
" require'nvim_lsp'.hls.setup{}
" EOF

" set esckeys
set timeoutlen=300 ttimeoutlen=100

set backupskip=/tmp/*,/private/tmp/*
set backspace=indent,eol,start
set whichwrap+=<,>,h,l,[,] " left goes to prev line

" Turn on mouse
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
nnoremap <Esc>A <up>
inoremap <Esc>A <up>
nnoremap <Esc>B <down>
inoremap <Esc>B <down>
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
nnoremap <C-Space> :w<CR>:make<CR>
" XXX ^ add a keybinding that does this in :sp term://

nnoremap <C-g> :FzfRgLike<CR>
nnoremap <C-g><C-g> :FzfRg<CR>
nnoremap <C-f> :FzfBLines<CR>
nnoremap <C-f><C-f> :FzfFiles %:h<CR>
nnoremap <C-b> :FzfFiles<CR>
nnoremap <C-b><C-b> :FzfBuffers<CR>
nnoremap <C-h> :FzfCommands<CR>
nnoremap K :call Dasht(dasht#cursor_search_terms())<Return>
" XXX defer to external tool, maybe with https://github.com/Chiel92/vim-autoformat
nnoremap <C-i> gg=G<C-o><C-o>

nnoremap <C-left> <C-W><C-H>
nnoremap <C-right> <C-W><C-L>
nnoremap <C-up> <C-W><C-K>
nnoremap <C-down> <C-W><C-J>
inoremap <C-left> <Esc><C-W><C-H>
inoremap <C-right> <Esc><C-W><C-L>
inoremap <C-up> <Esc><C-W><C-K>
inoremap <C-down> <Esc><C-W><C-J>
tnoremap <C-left> <Esc><C-W><C-H>
tnoremap <C-right> <Esc><C-W><C-L>
tnoremap <C-up> <Esc><C-W><C-K>
tnoremap <C-down> <Esc><C-W><C-J>
" M-w
nnoremap ∑ :only<CR>

" Terminal stuff
tnoremap <Esc> <C-\><C-n>
au BufEnter term://* startinsert

" nnoremap <silent> <c-]> <cmd>lua vim.lsp.buf.definition()<CR>
" nnoremap <silent> K     <cmd>lua vim.lsp.buf.hover()<CR>
" nnoremap <silent> gD    <cmd>lua vim.lsp.buf.implementation()<CR>
" nnoremap <silent> <c-k> <cmd>lua vim.lsp.buf.signature_help()<CR>
" nnoremap <silent> 1gD   <cmd>lua vim.lsp.buf.type_definition()<CR>
" nnoremap <silent> gr    <cmd>lua vim.lsp.buf.references()<CR>
" XXX would be nice to push this into Fzf
" nnoremap <silent> g0    <cmd>lua vim.lsp.buf.document_symbol()<CR>
" nnoremap <silent> gW    <cmd>lua vim.lsp.buf.workspace_symbol()<CR>
" nnoremap <silent> gd    <cmd>lua vim.lsp.buf.declaration()<CR>

" XXX I want to take an "excursion" into another file like above and open a
" window to the side of the main one. (I want the main window to be in the
" middle centered, with other windows around it to the side --- like
" junegunn/goyo.vim)

" XXX softline wrap in scribble/text
"

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

filetype plugin indent on
au! BufRead,BufNewFile *.scrbl setfiletype scribble
au! BufRead,BufNewFile *.rsh setfiletype javascript

" Auto load session; maybe use mhinz/vim-startify
fu! SaveSess()
  execute 'mksession! ' . getcwd() . '/.session.vim'
endfunction

fu! RestoreSess()
  if filereadable(getcwd() . '/.session.vim')
    execute 'so ' . getcwd() . '/.session.vim'
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

" let mapleader = ';'
" let g:mapleader = ';'
" inoremap ;; <Esc>
" nnoremap <leader>r :!jrun %<CR>

function! s:word_sink(w)
  call append(line('.'), a:w)
endfunction

command! -bang PU call fzf#run({'source': 'cat /Users/jay/Dev/scm/github.jeapostrophe/shakes/apat/hard', 'sink': function('s:word_sink')})

" Notes
" v/V/C-V visual selection
" G - end of file
" :e - revert file
" / - search
" % - move between delimiters
" " n/N - fwd/bck search

" fzf.vim
" --- CTRL-[T: Tab][X: Split][V: Vert Split] to open
