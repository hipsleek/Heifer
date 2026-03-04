#lang racket
(require racket/control)
(define x 0)
(reset
  (let ([c (shift0 k (k (lambda () (set! x (+ x 1)) (shift0 k_ig (k (lambda () x))))))])
    (set! x (+ x 1))
    (c)
  )
)

;; let inc3 x =
;; <
;;   let c =
;;     (shift0 (fun k -> k (fun _ -> x := ! x + 1; shift0 (fun _ -> k ( fun _ -> () )))))
;;   in
;;   x := ! x + 1; c ()
;; >
