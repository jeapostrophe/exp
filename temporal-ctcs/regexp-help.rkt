#lang racket
(struct regex-transformer (>regex))

(provide (struct-out regex-transformer))