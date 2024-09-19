  (import (srfi 1) (srfi 4) (chicken locative) (srfi 18) (chicken bitwise)
          (chicken pretty-print))

(define-syntax → (syntax-rules () ((_ . ω) (begin . ω))))
(define-syntax ∃ (syntax-rules () ((_ . α) (let* . α))))
(define-syntax ? (syntax-rules () ((_ . α) (if . α))))
  (define-syntax λ (syntax-rules () 
    ((_ () ω ...) (lambda () ω ...))
    ((_ . α) (lambda . α))))
(define-syntax ← (syntax-rules (▽)
 ((_ (▽ α ...) ω ...) (begin (define α ω) ...))
 ((_ ((α ω ...) ...)) (begin (define α ω ...) ...))
 ((_ . α) (define . α))))

(← ((□ display) (⇐ foldl) (π 3.141592653589793) (ι iota) (∀ map) (I identity)))
(← ((∀∀ for-each) (↑ car) (↓ cdr) (↑↓ cadr) (∅ '()) (∅? null?) (K constantly)))
(← ((<< arithmetic-shift) (>> (λ (α ω) (<< α (* -1 ω)))) (¦ bitwise-ior)))
(← ((& bitwise-and) (ρ length) (∘ compose) (∈s16 s16vector-ref)))
(← ((ρs16 s16vector-length) ($ apply)))

(← WAV8 (read-u8vector #f (open-input-file "/tmp/c.wav")))
(← WAV16
  (blob->s16vector
    (u8vector->blob (subu8vector WAV8 44 (u8vector-length WAV8)))))

(← (voice vol freq phase) `((vol ,vol) (freq ,freq) (phase ,phase)))

(← (voices freqs) (∀ (λ (freq) (voice 0 freq 0)) freqs))

(← (n⇒ n ω f) (∀ (λ (α m) (? (= n m) (f α) α)) ω (ι (ρ ω))))

(← (k⇒ k ω f) (∀ (λ (α) (? (eq? (↑ α) k) `(,(↑ α) ,(f (↑↓ α))) α)) ω))

(← (modf n m) (- n (* (truncate (/ n m)) m)))

(← (inc n ω) (modf (+ n ω) (ρs16 WAV16)))

(← (lerp n m α) (+ n (* α (- m n))))

(← int (∘ inexact->exact truncate))

(← (∈ α ω) (↑↓ (assoc α ω)))

(← (wav-lerp θ)
  (∃ ((n (int θ)) (f (- θ n)) (s1 (∈s16 WAV16 n)) (s2 (∈s16 WAV16 (inc 1 n))))
    (lerp s1 s2 f)))

(← (inc-θ ω) (∃ ((f (∈ 'freq ω))) (k⇒ 'phase ω (λ (α) (inc f α)))))

(← (read-wav ω) (∃ ((θ (∈ 'phase ω)) (v (∈ 'vol ω))) (* v (wav-lerp θ))))

(← (inc-θs voices) (∀ inc-θ voices))

(← (mix ω) (∃ ((f ($ + (∀ read-wav ω))) (s (int f))) (values s s)))

(← (volume! n α)
  (thread-specific-set! WAMPOO-THREAD
    (k⇒ 'acc (thread-specific WAMPOO-THREAD)
        (λ (ω) (n⇒ n ω (λ (v) (k⇒ 'vol v (K α))))))))

; compile with -s -J
; move "example.so" to same directory as REPL
; make sure you have a mono file at "/tmp/c.wav"
; ./wampoo
; (load "example")
; (set-acc! (voices '(0.25 0.5 0.75 1)))
; (begin 
;   (set-f! inc-θs)
;   (set-g! mix)
;   (volume! 0 2)
;   (volume! 1 0.75)
;   (volume! 2 1)
;   (volume! 3 0.4)
;  )
; other useful commands during runtime
; (pp (assoc 'acc (thread-specific WAMPOO-THREAD)))
; (audio-info)
; (exit)
