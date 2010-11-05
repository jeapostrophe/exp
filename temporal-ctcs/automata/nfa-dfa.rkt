#lang racket/base
(require "dfa.rkt"
         racket/list
         (for-syntax syntax/parse
                     syntax/id-table
                     unstable/syntax
                     racket/set
                     racket/dict
                     racket/function
                     racket/match
                     racket/list
                     racket/base))

(struct an-nfa-state (accepting? next))

(define-syntax (nfa stx)
  (syntax-parse
   stx
   [(_ (start:id ...)
       (end:id ...)
       [state:id ([evt:expr (next-state:id ...)]
                  ...)]
       ...)
    (define id->num (make-bound-id-table))
    (define num->id (make-hasheq))
    (define K 0)
    (for ([s (in-list (syntax->list #'(state ...)))])
      (dict-ref! id->num s 
                 (λ () 
                   (begin0 K
                           (dict-set! num->id K s)
                           (set! K (add1 K))))))
    
    (define set->name (make-hash))
    (define (set->list s)
      (for/list ([e (in-set s)]) e))
    (define (set->name! s)
      (dict-ref! set->name s 
                 (λ () 
                   (generate-temporary 
                    (string-append
                     (apply string-append 
                            (add-between (map (compose symbol->string syntax->datum (curry hash-ref num->id))
                                              (set->list s))
                                         "*"))
                     ":")))))
    
    (define (list->set sl)
      (apply seteq (syntax-map (curry dict-ref id->num) sl)))
    
    (define state->nexts (make-bound-id-table))
    (for ([stx (in-list (syntax->list #'([state ([evt (next-state ...)] ...)] ...)))])
      (syntax-case stx ()
        [[state nexts]
         (dict-set! state->nexts #'state 
                    (map (λ (e*ns-stx)
                           (define e*ns (syntax->list e*ns-stx))
                           (list (first e*ns)
                                 (list->set (second e*ns))))
                         (syntax->list #'nexts)))]))
    
    (define state->next (make-hash))
    
    (define start-set
      (list->set #'(start ...)))
    (define start-state
      (set->name! start-set))
    
    (define states empty)    
    ; XXX This generates some impossible matches because
    ;     match patterns are not easy to analyze
    (define (only left right)
      (map (λ (lft)
             (match-define (list evt-left ns-left) lft)
             (list #`(and #,evt-left (not (or #,@(map first right))))
                   ns-left))
           left))
    (define (cross-product left right)
      (append
       (only left right)
       (only right left)
       (for/fold ([l empty])
         ([lft (in-list left)])
         (match-define (list evt-left ns-left) lft)
         (for/fold ([l l])
           ([rht (in-list right)])
           (match-define (list evt-right ns-right) rht)
           (list* (list #`(and #,evt-left #,evt-right)
                        (set-union ns-left ns-right))
                  l)))))
    (define cross-product*
      (match-lambda
        [(list) empty]
        [(list e) e]
        [(list-rest e0 er)
         (cross-product e0 (cross-product* er))]))
    (define (explore! st)
      (unless (dict-has-key? state->next st)
        (set! states (list* st states))
        (define next
          (cross-product*
           (for/list ([n (in-set st)])
             (dict-ref state->nexts (dict-ref num->id n)))))
        (dict-set! state->next st next)
        (for-each explore! (map second next))))
    
    (explore! start-set)
    
    (with-syntax*
        ([start* start-state]
         [(end* ...)
          (map set->name!
               (filter (λ (state)
                         (for/or ([end (in-list (syntax->list #'(end ...)))])
                           (set-member? state (dict-ref id->num end))))
                       states))]
         [((state* ((evt* next-state*) ...)) ...)
          (for/list ([(state evt*next-states) (in-hash state->next)])
            (list (set->name! state) 
                  (for/list ([evt*next-state (in-list evt*next-states)])
                    (match-define (list evt next-state) evt*next-state)
                    (list evt (set->name! next-state)))))])
      
      (syntax/loc stx
        (dfa start*
             (end* ...)
             [state* ([evt* next-state*]
                      ...)]
             ...)))]))

(define nfa-accepting? dfa-accepting?)
(define nfa-advance dfa-advance)
(define nfa-accepts? dfa-accepts?)

(provide
 nfa
 nfa-advance
 nfa-accepting?
 nfa-accepts?)

(require tests/eli-tester)
(define M
  (nfa (s1 s3) (s1 s3)
       [s1 ([0 (s2)]
            [1 (s1)])]
       [s2 ([0 (s1)]
            [1 (s2)])]
       [s3 ([0 (s3)]
            [1 (s4)])]
       [s4 ([0 (s4)]
            [1 (s3)])]))

(test
 (nfa-accepts? M (list 1 0 1 0 1))
 (nfa-accepts? M (list 0 1 0 1 0))
 (nfa-accepts? M (list 1 0 1 1 0 1))
 (nfa-accepts? M (list 0 1 0 0 1 0))
 (nfa-accepts? M (list))
 (nfa-accepts? M (list 1 0)) => #f)

