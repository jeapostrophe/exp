" Vim syntax file
" Language:	Scribble (a racket language)
" Last Change:	2011-09-28
" Author:	Tim Brown <tim.brown@timb.net>
" Revision:      $Revision: 1.2 $
"
" Suggestions and bug reports (and fixes!) are solicited by the author.
"
" This syntax includes scheme.vim (via racket.vim), and therefore I am
" grateful to those that have worked on this.
"
" Issues:
" * I'm not having much luck with syntax.vim/filetype.vim/scripts.vim in
"   recoginsing a scribble file. However a "vi..m:" modeline does the trick
"   for me now
" * Not supporting vim verisons < 7. If it's simple enough to do, send me a
"   patch
" * @foo|{...}| nesting isn't supported. Again, I don't need it *so* much --
"   and if I were to handle *that* then the next step up to arbitrary
"   @foo|<<<{...}>>>| expressions is just a bit too scary for me!
"
" Changes: 
"   1.2: cut and paste job on scribble documentation into my keywords...

" Initializing:
if version < 700
  syntax clear
  finish
elseif exists("b:current_syntax")
  finish
endif

" Scribble is a racket language, is mzscheme... so we set this anyway
syntax include @SchemeBase syntax/racket.vim


""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" I'll declare the scribble/... keywords here, then reproduce them in the
" scribbleMarkup
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" #lang scribble/base
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
syntax keyword racketFunc title
syntax keyword racketFunc section
syntax keyword racketFunc subsection
syntax keyword racketFunc subsubsection
syntax keyword racketFunc subsubsub*section
syntax keyword racketFunc include-section
syntax keyword racketFunc author
syntax keyword racketFunc author+email
syntax keyword racketFunc para
syntax keyword racketFunc nested
syntax keyword racketFunc centered
syntax keyword racketFunc margin-note
syntax keyword racketFunc margin-note*
syntax keyword racketFunc itemlist
syntax keyword racketFunc item
syntax keyword racketFunc item?
syntax keyword racketFunc tabular
syntax keyword racketFunc verbatim
syntax keyword racketFunc elem
syntax keyword racketFunc italic
syntax keyword racketFunc bold
syntax keyword racketFunc tt
syntax keyword racketFunc subscript
syntax keyword racketFunc superscript
syntax keyword racketFunc smaller
syntax keyword racketFunc larger
syntax keyword racketFunc emph
syntax keyword racketFunc literal
syntax keyword racketFunc image
syntax keyword racketFunc linebreak
syntax keyword racketFunc nonbreaking
syntax keyword racketFunc hspace
syntax keyword racketFunc ~
syntax keyword racketFunc -~-
syntax keyword racketFunc ?-
syntax keyword racketFunc ._
syntax keyword racketFunc .__
syntax keyword racketFunc hyperlink
syntax keyword racketFunc url
syntax keyword racketFunc secref
syntax keyword racketFunc Secref
syntax keyword racketFunc seclink
syntax keyword racketFunc other-doc
syntax keyword racketFunc elemtag
syntax keyword racketFunc elemref
syntax keyword racketFunc module-path-prefix->string
syntax keyword racketFunc index
syntax keyword racketFunc index*
syntax keyword racketFunc as-index
syntax keyword racketFunc section-index
syntax keyword racketFunc index-section
syntax keyword racketFunc table-of-contents
syntax keyword racketFunc local-table-of-contents

""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" #lang scribble/sigplan
" #lang scribble/jfp
" #lang scribble/lncs
" (Combined and sorted for uniqueness checking)
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
syntax keyword racketFunc 10pt
syntax keyword racketFunc abstract
syntax keyword racketFunc affiliation
syntax keyword racketFunc affiliation-mark
syntax keyword racketFunc affiliation-sep
syntax keyword racketFunc author
syntax keyword racketFunc authorinfo
syntax keyword racketFunc authors
syntax keyword racketFunc author/short
syntax keyword racketFunc category
syntax keyword racketFunc conferenceinfo
syntax keyword racketFunc copyrightdata
syntax keyword racketFunc copyrightyear
syntax keyword racketFunc email
syntax keyword racketFunc include-abstract
syntax keyword racketFunc institute
syntax keyword racketFunc institutes
syntax keyword racketFunc keywords
syntax keyword racketFunc nocopyright
syntax keyword racketFunc noqcourier
syntax keyword racketFunc notimes
syntax keyword racketFunc onecolumn
syntax keyword racketFunc preprint
syntax keyword racketFunc terms

""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" #lang scribble/manual
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
syntax keyword racketFunc codeblock
syntax keyword racketFunc racketblock
syntax keyword racketFunc RACKETBLOCK
syntax keyword racketFunc racketblock0
syntax keyword racketFunc RACKETBLOCK0
syntax keyword racketFunc racketresultblock
syntax keyword racketFunc racketresultblock0
syntax keyword racketFunc RACKETRESULTBLOCK
syntax keyword racketFunc RACKETRESULTBLOCK0
syntax keyword racketFunc racketinput
syntax keyword racketFunc RACKETINPUT
syntax keyword racketFunc racketinput0
syntax keyword racketFunc RACKETINPUT0
syntax keyword racketFunc racketmod
syntax keyword racketFunc racketmod0
syntax keyword racketFunc racket
syntax keyword racketFunc RACKET
syntax keyword racketFunc racketresult
syntax keyword racketFunc racketid
syntax keyword racketFunc racketmodname
syntax keyword racketFunc racketmodlink
syntax keyword racketFunc litchar
syntax keyword racketFunc racketfont
syntax keyword racketFunc racketvalfont
syntax keyword racketFunc racketresultfont
syntax keyword racketFunc racketidfont
syntax keyword racketFunc racketvarfont
syntax keyword racketFunc racketkeywordfont
syntax keyword racketFunc racketparenfont
syntax keyword racketFunc racketmetafont
syntax keyword racketFunc racketerror
syntax keyword racketFunc racketmodfont
syntax keyword racketFunc racketoutput
syntax keyword racketFunc procedure
syntax keyword racketFunc var
syntax keyword racketFunc svar
syntax keyword racketFunc schemeblock
syntax keyword racketFunc SCHEMEBLOCK
syntax keyword racketFunc schemeblock0
syntax keyword racketFunc SCHEMEBLOCK0
syntax keyword racketFunc schemeinput
syntax keyword racketFunc schememod
syntax keyword racketFunc scheme
syntax keyword racketFunc SCHEME
syntax keyword racketFunc schemeresult
syntax keyword racketFunc schemeid
syntax keyword racketFunc schememodname
syntax keyword racketFunc schememodlink
syntax keyword racketFunc schemefont
syntax keyword racketFunc schemevalfont
syntax keyword racketFunc schemeresultfont
syntax keyword racketFunc schemeidfont
syntax keyword racketFunc schemevarfont
syntax keyword racketFunc schemekeywordfont
syntax keyword racketFunc schemeparenfont
syntax keyword racketFunc schememetafont
syntax keyword racketFunc schemeerror
syntax keyword racketFunc schememodfont
syntax keyword racketFunc schemeoutput

syntax keyword racketFunc defmodule
syntax keyword racketFunc defmodulelang
syntax keyword racketFunc defmodulereader
syntax keyword racketFunc defmodule*
syntax keyword racketFunc defmodulelang*
syntax keyword racketFunc defmodulereader*
syntax keyword racketFunc defmodule*/no-declare
syntax keyword racketFunc defmodulelang*/no-declare
syntax keyword racketFunc defmodulereader*/no-declare
syntax keyword racketFunc declare-exporting

syntax keyword racketFunc defproc
syntax keyword racketFunc defproc*
syntax keyword racketFunc defform
syntax keyword racketFunc defform*
syntax keyword racketFunc defform/subs
syntax keyword racketFunc defform*/subs
syntax keyword racketFunc defform/none
syntax keyword racketFunc defidform
syntax keyword racketFunc defidform/inline
syntax keyword racketFunc specform
syntax keyword racketFunc specsubform
syntax keyword racketFunc specsubform/subs
syntax keyword racketFunc specspecsubform
syntax keyword racketFunc specspecsubform/subs
syntax keyword racketFunc defparam
syntax keyword racketFunc defboolparam
syntax keyword racketFunc defthing
syntax keyword racketFunc defstruct*
syntax keyword racketFunc defstruct
syntax keyword racketFunc deftogether
syntax keyword racketFunc racketgrammar
syntax keyword racketFunc racketgrammar*
syntax keyword racketFunc defidentifier
syntax keyword racketFunc schemegrammar
syntax keyword racketFunc schemegrammar*

syntax keyword racketFunc defclass
syntax keyword racketFunc defclass/title
syntax keyword racketFunc definterface
syntax keyword racketFunc definterface/title
syntax keyword racketFunc defmixin
syntax keyword racketFunc defmixin/title
syntax keyword racketFunc defconstructor
syntax keyword racketFunc defconstructor/make
syntax keyword racketFunc defconstructor*/make
syntax keyword racketFunc defconstructor/auto-super
syntax keyword racketFunc defmethod
syntax keyword racketFunc defmethod*
syntax keyword racketFunc method
syntax keyword racketFunc xmethod
syntax keyword racketFunc this-obj

syntax keyword racketFunc defsignature
syntax keyword racketFunc defsignature/splice
syntax keyword racketFunc signature-desc
syntax keyword racketFunc sigelem

syntax keyword racketFunc aux-elem
syntax keyword racketFunc defterm
syntax keyword racketFunc onscreen
syntax keyword racketFunc menuitem
syntax keyword racketFunc filepath
syntax keyword racketFunc exec
syntax keyword racketFunc envvar
syntax keyword racketFunc Flag
syntax keyword racketFunc DFlag
syntax keyword racketFunc PFlag
syntax keyword racketFunc DPFlag

syntax keyword racketFunc racketlink
syntax keyword racketFunc schemelink
syntax keyword racketFunc link
syntax keyword racketFunc other-manual
syntax keyword racketFunc deftech
syntax keyword racketFunc tech
syntax keyword racketFunc techlink

syntax keyword racketFunc indexed-racket
syntax keyword racketFunc indexed-scheme
syntax keyword racketFunc idefterm
syntax keyword racketFunc pidefterm
syntax keyword racketFunc indexed-file
syntax keyword racketFunc indexed-envvar

syntax keyword racketFunc image/plain

syntax keyword racketFunc cite
syntax keyword racketFunc bibliography
syntax keyword racketFunc bib-entry
syntax keyword racketFunc bib-entry?

syntax keyword racketFunc t
syntax keyword racketFunc etc
syntax keyword racketFunc PLaneT
syntax keyword racketFunc hash-lang
syntax keyword racketFunc void-const
syntax keyword racketFunc undefined-const
syntax keyword racketFunc commandline
syntax keyword racketFunc centerline
syntax keyword racketFunc math
syntax keyword racketFunc filebox

syntax keyword racketFunc module-path-index-desc
syntax keyword racketFunc exported-index-desc
syntax keyword racketFunc form-index-desc
syntax keyword racketFunc procedure-index-desc
syntax keyword racketFunc thing-index-desc
syntax keyword racketFunc struct-index-desc
syntax keyword racketFunc class-index-desc
syntax keyword racketFunc interface-index-desc
syntax keyword racketFunc mixin-index-desc
syntax keyword racketFunc method-index-desc


" (require scribble/racket)
" (require scribble/scheme)
syntax keyword racketFunc define-code
syntax keyword racketFunc to-paragraph
syntax keyword racketFunc to-paragraph/prefix
syntax keyword racketFunc to-element
syntax keyword racketFunc to-element/no-color
syntax keyword racketFunc var-id
syntax keyword racketFunc shaped-parens
syntax keyword racketFunc just-context
syntax keyword racketFunc literal-syntax
syntax keyword racketFunc element-id-transformer?
syntax keyword racketFunc make-element-id-transformer
syntax keyword racketFunc variable-id?
syntax keyword racketFunc make-variable-id
syntax keyword racketFunc output-color
syntax keyword racketFunc input-color
syntax keyword racketFunc input-background-color
syntax keyword racketFunc no-color
syntax keyword racketFunc reader-color
syntax keyword racketFunc result-color
syntax keyword racketFunc keyword-color
syntax keyword racketFunc comment-color
syntax keyword racketFunc paren-color
syntax keyword racketFunc meta-color
syntax keyword racketFunc value-color
syntax keyword racketFunc symbol-color
syntax keyword racketFunc variable-color
syntax keyword racketFunc opt-color
syntax keyword racketFunc error-color
syntax keyword racketFunc syntax-link-color
syntax keyword racketFunc value-link-color
syntax keyword racketFunc module-color
syntax keyword racketFunc module-link-color
syntax keyword racketFunc block-color
syntax keyword racketFunc highlighted-color

" (require scribble/eval)
syntax keyword racketFunc interaction
syntax keyword racketFunc interaction0
syntax keyword racketFunc interaction-eval
syntax keyword racketFunc interaction-eval-show
syntax keyword racketFunc racketblock+eval
syntax keyword racketFunc racketblock0+eval
syntax keyword racketFunc racketmod+eval
syntax keyword racketFunc def+int
syntax keyword racketFunc defs+int
syntax keyword racketFunc examples
syntax keyword racketFunc defexamples
syntax keyword racketFunc make-base-eval
syntax keyword racketFunc make-base-eval-factory
syntax keyword racketFunc make-eval-factory
syntax keyword racketFunc close-eval
syntax keyword racketFunc scribble-eval-handler

" (require scribble/srcdoc)
" (require scribble/extract)

syntax keyword racketFunc provide/doc
syntax keyword racketFunc require/doc
syntax keyword racketFunc proc-doc/names
syntax keyword racketFunc proc-doc
syntax keyword racketFunc thing-doc
syntax keyword racketFunc parameter-doc
syntax keyword racketFunc include-extracted
syntax keyword racketFunc provide-extracted
syntax keyword racketFunc include-previously-extracted


" (require scribble/bnf)
syntax keyword racketFunc BNF
syntax keyword racketFunc nonterm
syntax keyword racketFunc BNF-seq
syntax keyword racketFunc BNF-group
syntax keyword racketFunc optional
syntax keyword racketFunc kleenestar
syntax keyword racketFunc kleeneplus
syntax keyword racketFunc kleenerange
syntax keyword racketFunc BNF-alt
syntax keyword racketFunc BNF-etc

" (require scribble/struct)
" (require scribble/basic)
syntax keyword racketFunc make-part
syntax keyword racketFunc part-flow
syntax keyword racketFunc part-title-content
syntax keyword racketFunc make-versioned-part
syntax keyword racketFunc versioned-part?
syntax keyword racketFunc make-unnumbered-part
syntax keyword racketFunc unnumbered-part?
syntax keyword racketFunc make-paragraph
syntax keyword racketFunc paragraph-content
syntax keyword racketFunc make-styled-paragraph
syntax keyword racketFunc styled-paragraph?
syntax keyword racketFunc styled-paragraph-style
syntax keyword racketFunc make-omitable-paragraph
syntax keyword racketFunc omitable-paragraph?
syntax keyword racketFunc make-table
syntax keyword racketFunc table-flowss
syntax keyword racketFunc make-itemization
syntax keyword racketFunc make-styled-itemization
syntax keyword racketFunc styled-itemization?
syntax keyword racketFunc styled-itemization-style
syntax keyword racketFunc make-blockquote
syntax keyword racketFunc make-auxiliary-table
syntax keyword racketFunc auxiliary-table?
syntax keyword racketFunc make-compound-paragraph
syntax keyword racketFunc make-element
syntax keyword racketFunc make-toc-element
syntax keyword racketFunc make-target-element
syntax keyword racketFunc make-toc-target-element
syntax keyword racketFunc make-page-target-element
syntax keyword racketFunc make-redirect-target-element
syntax keyword racketFunc make-link-element
syntax keyword racketFunc make-index-element
syntax keyword racketFunc element?
syntax keyword racketFunc element-content
syntax keyword racketFunc element-style
syntax keyword racketFunc make-aux-element
syntax keyword racketFunc make-hover-element
syntax keyword racketFunc make-script-element
syntax keyword racketFunc with-attributes
syntax keyword racketFunc target-url
syntax keyword racketFunc image-file
syntax keyword racketFunc element->string
syntax keyword racketFunc span-class
syntax keyword racketFunc itemize

" #lang scribble/lp
" (require scribble/lp-include)
syntax keyword racketFunc chunk
syntax keyword racketFunc lp-include

""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" Because the "@" is an "iskeyword" character (and I don't want to change this
" so much), the scribbleMarkup words include the "@".
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" scribbleMarkup keywords are a little denser than the ones above
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" #lang scribble/base
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
syntax keyword scribbleMarkup @title @section @subsection @subsubsection @subsubsub*section nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @include-section @author @author+email @para @nested nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @centered @margin-note @margin-note* @itemlist @item nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @item?  @tabular @verbatim @elem @italic nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @bold @tt @subscript @superscript @smaller nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @larger @emph @literal @image @linebreak nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @nonbreaking @hspace @~ @-~- @?- nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @._ @.__ @hyperlink @url @secref nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @Secref @seclink @other-doc @elemtag @elemref nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @module-path-prefix->string @index @index* @as-index @section-index nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @index-section @table-of-contents @local-table-of-contents nextgroup=atBraceRange,atBrackRange
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" #lang scribble/sigplan
" #lang scribble/jfp
" #lang scribble/lncs
" (Combined and sorted for uniqueness checking)
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
syntax keyword scribbleMarkup @10pt @abstract @affiliation @affiliation-mark @affiliation-sep nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @author @authorinfo @authors @author/short @category
syntax keyword scribbleMarkup @conferenceinfo @copyrightdata @copyrightyear @email @include-abstract nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @institute @institutes @keywords @nocopyright @noqcourier nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @notimes @onecolumn @preprint @terms  nextgroup=atBraceRange,atBrackRange
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
" #lang scribble/manual
""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""""
syntax keyword scribbleMarkup @codeblock @racketblock @RACKETBLOCK @racketblock0 @RACKETBLOCK0 nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @racketresultblock @racketresultblock0 @RACKETRESULTBLOCK @RACKETRESULTBLOCK0 @racketinput nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @RACKETINPUT @racketinput0 @RACKETINPUT0 @racketmod @racketmod0 nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @racket @RACKET @racketresult @racketid @racketmodname nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @racketmodlink @litchar @racketfont @racketvalfont @racketresultfont nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @racketidfont @racketvarfont @racketkeywordfont @racketparenfont @racketmetafont nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @racketerror @racketmodfont @racketoutput @procedure @var nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @svar @schemeblock @SCHEMEBLOCK @schemeblock0 @SCHEMEBLOCK0 nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @schemeinput @schememod @scheme @SCHEME @schemeresult nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @schemeid @schememodname @schememodlink @schemefont @schemevalfont nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @schemeresultfont @schemeidfont @schemevarfont @schemekeywordfont @schemeparenfont nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @schememetafont @schemeerror @schememodfont @schemeoutput nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defmodule @defmodulelang @defmodulereader @defmodule* @defmodulelang* nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defmodulereader* @defmodule*/no-declare @defmodulelang*/no-declare @defmodulereader*/no-declare @declare-exporting nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defproc @defproc* @defform @defform* @defform/subs nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defform*/subs @defform/none @defidform @defidform/inline @specform nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @specsubform @specsubform/subs @specspecsubform @specspecsubform/subs @defparam nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defboolparam @defthing @defstruct* @defstruct @deftogether nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @racketgrammar @racketgrammar* @defidentifier @schemegrammar @schemegrammar* nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defclass @defclass/title @definterface @definterface/title @defmixin nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defmixin/title @defconstructor @defconstructor/make @defconstructor*/make @defconstructor/auto-super nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defmethod @defmethod* @method @xmethod @this-obj nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defsignature @defsignature/splice @signature-desc @sigelem nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @aux-elem @defterm @onscreen @menuitem @filepath nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @exec @envvar @Flag @DFlag @PFlag @DPFlag nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @racketlink @schemelink @link @other-manual @deftec nextgroup=atBraceRange,atBrackRangeh
syntax keyword scribbleMarkup @tech @techlink nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @indexed-racket @indexed-scheme @idefterm @pidefterm @indexed-file nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @indexed-envvar nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @image/plain nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @cite @bibliography @bib-entry @bib-entry? nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @t @etc @PLaneT @hash-lang @void-const nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @undefined-const @commandline @centerline @math @filebox nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @module-path-index-desc @exported-index-desc @form-index-desc @procedure-index-desc @thing-index-desc nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @struct-index-desc @class-index-desc @interface-index-desc @mixin-index-desc @method-index-desc nextgroup=atBraceRange,atBrackRange
" (require scribble/racket)
" (require scribble/scheme)
syntax keyword scribbleMarkup @define-code @to-paragraph @to-paragraph/prefix @to-element @to-element/no-color nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @var-id @shaped-parens @just-context @literal-syntax @element-id-transformer? nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @make-element-id-transformer @variable-id?  @make-variable-id @output-color @input-color nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @input-background-color @no-color @reader-color @result-color @keyword-color nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @comment-color @paren-color @meta-color @value-color @symbol-color nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @variable-color @opt-color @error-color @syntax-link-color @value-link-color nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @module-color @module-link-color @block-color @highlighted-color  nextgroup=atBraceRange,atBrackRange
" (require scribble/eval)
syntax keyword scribbleMarkup @interaction @interaction0 @interaction-eval @interaction-eval-show @racketblock+eval nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @racketblock0+eval @racketmod+eval @def+int @defs+int @examples nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @defexamples @make-base-eval @make-base-eval-factory @make-eval-factory @close-eval nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @scribble-eval-handler nextgroup=atBraceRange,atBrackRange
" (require scribble/srcdoc)
" (require scribble/extract)
syntax keyword scribbleMarkup @provide/doc @require/doc @proc-doc/names @proc-doc @thing-doc @parameter-doc nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @include-extracted @provide-extracted @include-previously-extracted nextgroup=atBraceRange,atBrackRange
" (require scribble/bnf)
syntax keyword scribbleMarkup @BNF @nonterm @BNF-seq @BNF-group @optional nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @kleenestar @kleeneplus @kleenerange @BNF-alt @BNF-etc nextgroup=atBraceRange,atBrackRange
" (require scribble/struct)
" (require scribble/basic)
syntax keyword scribbleMarkup @make-part @part-flow @part-title-content @make-versioned-part @versioned-part? nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @make-unnumbered-part @unnumbered-part?  @make-paragraph @paragraph-content @make-styled-paragraph nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @styled-paragraph?  @styled-paragraph-style @make-omitable-paragraph @omitable-paragraph?  @make-table nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @table-flowss @make-itemization @make-styled-itemization @styled-itemization?  @styled-itemization-style nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @make-blockquote @make-auxiliary-table @auxiliary-table?  @make-compound-paragraph @make-element nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @make-toc-element @make-target-element @make-toc-target-element @make-page-target-element @make-redirect-target-element nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @make-link-element @make-index-element @element?  @element-content @element-style nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @make-aux-element @make-hover-element @make-script-element @with-attributes @target-url nextgroup=atBraceRange,atBrackRange
syntax keyword scribbleMarkup @image-file @element->string @span-class @itemize  nextgroup=atBraceRange,atBrackRange
" #lang scribble/lp
" (require scribble/lp-include)
syntax keyword scribbleMarkup @chunk @lp-include nextgroup=atBraceRange,atBrackRange
" NO SECTION 7: Low-Level Scribble API

syntax region atBrackRange matchgroup=Delimiter start="\[" end="\]" contains=@SchemeBase,atExprStart,scribbleMarkup contained nextgroup=atBraceRange
syntax region atBraceRange matchgroup=Delimiter start="{" end="}" contains=atExprStart,atInnerBraceRange,scribbleMarkup contained
syntax region atInnerBraceRange matchgroup=atBraceRange start="{" end="}" contains=atExprStart,atInnerBraceRange,scribbleMarkup contained

syntax match atIdentifier /[-<a-z!$%&*\/:<=>?^_~0-9+.@>]\+/ nextgroup=atBraceRange,atBrackRange contained

syntax match atExprStart "@" nextgroup=atBrackRange,atBraceRange,atIdentifier,@SchemeBase containedin=atBraceRange,atInnerBraceRange,@SchemeBase

" scheme itself is ignored in atBraces
command -nargs=+ HiLink highlight def link <args>
HiLink atBraceRange      String
HiLink atInnerBraceRange String
HiLink atExprStart       Delimiter
HiLink scribbleMarkup    Statement
HiLink scribbleFunc      Statement
delcommand HiLink

let b:current_syntax = "scribble"
" vim: ts=8
