#lang racket

(require racket/control)

; (*@ ex ret; Write(emp, n,  ret); Norm(emp, ret) @*)
(define (get_int a) (shift k (lambda (x) (k (number->string x)))))

(((reset (string-append "input is " (get_int 1) " " (get_int 2))) 42) 41)
