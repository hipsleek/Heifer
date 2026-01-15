#lang racket

(require racket/control)


(define (foo n) (if (= n 0) "" (string-append (shift k (lambda (x) (k x))) (foo (- n 1)))))

(define (test n) (reset (foo n)))

(define (test1) ((test 1) "a"))

(define (test2) (((test 2) "a") "b"))

(define (test3) ((((test 3) "a") "b")"c"))


(test1)
(test2)
(test3)