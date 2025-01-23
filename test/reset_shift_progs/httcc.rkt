#lang racket
(require racket/control)
(define x 0)
(reset
  (let ([c (shift k (k (lambda () (set! x (+ x 1)) (k (lambda () x)))))])
    (set! x (+ x 1))
    (c)
  )
)


;; let x = ref 0 in
;; <
;;   let c : unit -> unit =
;;     shift k. (k (fun () -> x := !x + 1; k (fun () -> ())))
;;   in
;;   x := !x + 1;
;;   c ()
;; >