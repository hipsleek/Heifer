#lang racket

(require racket/control)

(define (get_int a) (shift k (lambda (x) (k (number->string x)))))

(((reset (string-append "input is " (get_int 1) " " (get_int 2))) 42) 41)