#lang racket

(require racket/control)


(define (inner) (shift0 k1 (shift0 k2 (string-append "A cat" (k1 (k2 "."))))))

(define (has) (reset0 (string-append " has " (inner) )))

(define (alice) (reset0 (string-append "Alice " (has) )))

(alice)