#lang racket/base

;; Subtle expressions are parsed into the following structure:
;;
;;  stx := (stx-atom atom)
;;       | (stx-op operator (list stx ...))
;;       | (stx-group group (list stx ...))
;;       | (stx-seq (list stx ...))
;;       | (stx-text stx text)
;;       | (stx-indent (list stx ...))
;; text := (text-esc stx)
;;       | (text-str string)
;;       | (text-seq (list text ...))

;; The concrete syntax of atoms is unspecified at this time.

;; A sequence like `a op b op c` is parsed as
;;  (stx-op op (list a b c))
;; assuming that `a`, `b`, and `c` do not contain any operators with a
;; higher level than `op`. For example,
;;  1 + 2 + 3
;; is parsed as
;;  (+ 1 2 3)
;; and
;;  1*3 + 4*7 + 6*9
;; is parsed as
;;  (+ (* 1 3) (* 4 7) (* 6 9))
;; because `*` is a lower level than `+`. But
;;  1 + 3, 4 + 7
;; is parsed as
;;  (, (+ 1 3) (+ 4 7))
;; because `+` is a lower level than `,`.
;;
;; The set of operators and their hierarchy is fixed for an instance
;; of a subtle expression language. An example is given below.

;; A sequence like `open a b c close` is parsed as
;;  (stx-group open/close (list a b c))
;; assuming that `open` and `close` form a matching pair of grouping
;; characters, like `()` or `[]` or `{}` or `⎩⎭`.
;;
;; The set of grouping characters is fixed for an instance of a subtle
;; expression language. An example is given below.

;; A sequence like `a b c` is parsed as
;;  (stx-seq (list a b c))
;; assuming that no operators occur inside the sequence.

;; A sequence like `@ a { body }` is parsed as
;;  (stx-text a body)
;; using rules similar to that Racket @-reader. However, the `a` must
;; be a "single expression", i.e. an `atom` or `group`, i.e. it cannot
;; be an expression using an operator, sequence, etc. Inside of
;; `body`, the `@` character escapes back into a similar "single"
;; context. However, in a normal context, the `a` may be absent, which
;; is indicated by a `#f` (not a `(stx-atom #f)`).

;; A sequence like `' '[K] a '\n' ' '[K] b '\n' ' '[K] c '\n'` (i.e.)
;;  ___a
;;  ___b
;;  ___c
;; is parsed as
;;  (stx-indent (list a b c))
;; for all K > 1, regardless of the magnitude of K relative to surrounding blocks.
;;
;; In situations where there are multiple levels of adjacent levels of
;; indentation, there will be multiple indent blocks. For example,
;;  ___a
;;  _____b
;;  ___c
;;  ______d
;;  ________e
;;  ___f
;; is parsed as
;;  (stx-indent (list
;;     a
;;     (stx-indent (list
;        b))
;;     c
;;     (stx-indent (list
;;       d
;;       (stx-indent (list
;;         e))
;;     f))
;; Notice in this example how `b` and `d` occur with different numbers
;; of spaces to their left, but this is not observable in the
;; structure of the resulting syntax object.
;;
;; Indentation does not interfere with group closing characters. In
;; other words, group closing characters may appear inside the
;; indentation, or not. For example,
;;  if a {
;;    b }
;;  else {
;;    c }
;; is valid, as well as
;;  if a {
;;    b
;;  } else {
;;    c
;;  }
;; Although only monsters would write the second form.
;;
;; Similarly, a text sequence consumes its own whitespace, which is
;; not part of any indentation. For example:
;;  if a
;;    println @{
;;    Hello World}
;; is parsed as
;;  (stx-seq (list 'if a
;;    (stx-indent (list
;;      (stx-seq (list 'println
;;        (stx-text #f
;;          (text-str "\n  Hello World"))))))))
;;
;; The presence of `stx-indent` allows subtle languages to impose
;; indentation sensitivity to particular forms.
;;
;; We expect that editors will facilitate indentation through the following rules
;;  1. <Enter> --- New line starts at the same indentation level as previous line
;;  2. First <Tab> --- Adds one level of indentation
;;  3. Next <Tab> while indentation to left --- Removes one level of indentation (matching #s of spaces in previous lines)
;;  4. Next <Tab> --- Matches one level of indentation above until last level is matched, then the sequence of <Tab>s is complete and we go back to rule #2

;; This proposal is works without `stx-indent`, but everything else is
;; necessary.

;; http://journal.stuffwithstuff.com/2011/03/19/pratt-parsers-expression-parsing-made-easy/

(struct parser (precedence impl)
  #:property prop:procedure
  (struct-field-index impl))

(define PREFIXES
  (hasheq))
(define INFIXES
  (hasheq))

(define default-prefix #f)
(define default-infix #f)

(define (parse* p lvl)
  (define token (read-char p))
  (define prefix-p (hash-ref PREFIXES token default-prefix))
  (let loop ([left (prefix-p p lvl token)])
    (cond
      [(< lvl (get-level p))
       (define token (read-char p))
       (define infix-p (hash-ref INFIXES token default-infix))
       (loop (infix-p p lvl left token))]
      [else
       left])))

(define (get-level p)
  (parser-precedence
   (hash-ref INFIXES (peek-char p) default-infix)))

(define (parse s)
  (parse* (open-input-string s) +inf.0))

(module+ test
  (require chk)
  (define (pchk s e)
    (chk (parse s) e))
  
  (pchk "a - b - c"
        '(- (- a b) c))
  (pchk "define : f(s) = 
         | printf(\"hi ~a\n\", s),
           \"hi\"
         | f(s, x) = f(x + y)"
        'xxx))

;; Haskell Operators
;;  https://haskell.fpcomplete.com/tutorial/operators
;; Function application
;;  $ :: (a -> b) -> a -> b
;; Composition
;;  ∘ :: (b -> c) -> (a -> b) -> (a -> c)
;; Reverse applications
;;  & :: a -> (a -> b) -> b
;; Append
;;  <> :: Monoid m => m -> m -> m
;; Functor Map
;;  <$> :: Functor f => (a -> b) -> f a -> f b
;;  <$ :: Functor f => a -> f b -> f a
;;  $> :: Functor f => f a -> b -> f b
;; Applicative function application <*>
;;  <*> :: Applicative f => f (a -> b) -> f a -> f b
;;  *> :: Applicative f => f a -> f b -> f b
;;  <* :: Applicative f => f a -> f b -> f a
;; Various monadic binding/composition operators
;;  (>>=) :: Monad m => m a -> (a -> m b) -> m b
;;  (=<<) :: Monad m => (a -> m b) -> m a -> m b
;;  (>>) :: Monad m => m a -> m b -> m b
;;  (>=>) :: Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
;;  (<=<) :: Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
;; Alternative <|>
;;  (<|>) :: Alternative f => f a -> f a -> f a

(define HIERARCHY
  '("::"
    ("." "->")
    ":"
    ("*" "/" "%")
    ("+" "-")
    ("<<" ">>")
    "<=>"
    ("<" "<=" "≤" ">" ">=" "≥")
    ("==" "!=" "≠")
    ("^&" "^^" "^|")
    ("&&" "||")
    "?"
    ","
    (":=" "←" "<-" "=>" "⇒" "=")
    "&"
    "|"
    ";"))
