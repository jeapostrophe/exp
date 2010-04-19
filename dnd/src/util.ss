#lang scheme

(define-for-syntax (generate/format fmt syn)
  (map (lambda (in)
         (datum->syntax in (string->symbol (format fmt (syntax->datum in))) in))
       (syntax->list syn)))