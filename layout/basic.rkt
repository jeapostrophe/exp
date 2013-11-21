#lang racket/base
(require ffi)

(define (ctime->rtime c)
  )

(module+ test
  (ctime->rtime (list))
  (ctime->rtime (list _int8 _int))
  (ctime->rtime (list _int8 _float _int))
  (ctime->rtime (list _int8 _float _int _racket))
  (ctime->rtime (list _int8 _racket _float _int _racket))
  (ctime->rtime (list _int8 _racket _float _int _racket _int))
  (ctime->rtime (list _int8 _racket _float (_array _int 4) _int _racket _int))
  (ctime->rtime (list _int8 _racket _float (_array _int 4 4) _int _racket _int)))
