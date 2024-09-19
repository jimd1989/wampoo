(import (srfi 1) (srfi 18) (srfi 4) (chicken bitwise) (chicken condition)
        (chicken file posix) (chicken foreign) (chicken locative)
        (chicken type))

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
(← ((& bitwise-and)))

#>
  #include <ao/ao.h>
  #include <string.h>

  ao_device* open_audio(int rate) {
    int driver;
    ao_sample_format fmt;
    ao_initialize();
    ao_option o;
    o.key = "buffer_time";
    o.value = "100"; /* Parameterize this later */
    o.next = NULL;
    driver = ao_default_driver_id();
    memset(&fmt, 0, sizeof(fmt));
    fmt.bits = 16;
    fmt.channels = 2;
    fmt.byte_format = AO_FMT_LITTLE;
    fmt.rate = rate;
    return ao_open_live(driver, &fmt, &o);
  }

  void close_audio(ao_device *d) {
    ao_close(d);
    ao_shutdown();
  }
<#

(define-foreign-type ao (c-pointer (struct "ao_device")))
(← open-audio (foreign-lambda ao "open_audio" int))
(← write-audio (foreign-lambda void "ao_play" ao nonnull-c-pointer int))
(← close-audio (foreign-lambda void "close_audio" ao))

(define-type buffer s16vector)
(define-type fill (('a -> 'a) ('a -> fixnum fixnum) 'a -> 'a))
(define-type mutex (struct mutex))
(define-type condition-variable (struct condition-variable))
(define-type audio-data (list-of (list symbol number)))
(define-type audio (list (list symbol (pointer -> void))
                         (list symbol (-> void))))
(define-type state (list (list symbol ('a -> 'a))
                         (list symbol ('a -> fixnum fixnum))
                         (list symbol 'a)
                         (list symbol audio-data)))

(: audio-data (fixnum fixnum fixnum --> audio-data))
(← (audio-data rate resolution blocks)
  (∃ ((channels 2)
      (bytes 2)
      (writes-per-second (/ resolution blocks))
      (write-buf-samples (/ rate writes-per-second))
      (block-buf-samples (/ rate resolution)))
    `((channels ,channels)
      (bytes ,bytes)
      (sample-rate ,rate)
      (resolution ,resolution)
      (write-blocks ,blocks)
      (write-buf-bytes ,(* write-buf-samples channels bytes))
      (block-buf-bytes ,(* block-buf-samples channels bytes)))))

(: ∈ (symbol (list-of (list symbol 'a)) --> 'a))
(← (∈ α ω) (↑↓ (assoc α ω)))

(: ∈←→ (symbol 'a (list-of (list symbol 'a)) --> (list-of (list symbol 'a))))
(← (∈←→ k v ω) (∀ (λ (α) (? (eq? (↑ α) k) `(,k ,v) α)) ω))

(: make-audio (audio-data -> audio))
(← (make-audio α)
  (∃ ((ao (open-audio (∈ 'sample-rate α)))
      (size (∈ 'write-buf-bytes α)))
    `((writer ,(λ (ω) (write-audio ao ω size)))
      (closer ,(λ () (close-audio ao))))))

(: buffer⇒ (fixnum fixnum s16vector ('a -> 'a) ('a -> fixnum fixnum) 'a -> 'a))
(← (buffer⇒ n m ω f g α)
  (? (= n m) α
    (∃ ((a (f α))) 
      (receive (l r) (g a)
        (s16vector-set! ω n l)
        (s16vector-set! ω (+ n 1) r)
        (buffer⇒ (+ n 2) m ω f g a)))))

(: windows ((list-of fixnum) --> (list-of (list fixnum fixnum))))
(← (windows ω) (↓ (⇐ (λ (acc x) `(,x ,@(↓ acc) ,(list (↑ acc) x))) '(0) ω)))

(: buffer-blocks (s16vector fixnum --> (list-of fill)))
(← (buffer-blocks ω n)
  (∃ ((size (/ (s16vector-length ω) n))
      (slices (windows (ι n size size))))
    (∀ (λ (nm) (λ (f g α) (buffer⇒ (↑ nm) (↑↓ nm) ω f g α))) slices)))

(: clock (condition-variable fixnum -> void))
(← (clock τ div)
  (letrec* ((start (time->seconds (current-time)))
            (sleep (/ 1 div))
            (▽ (λ (n) (condition-variable-specific-set! τ n)
                      (condition-variable-broadcast! τ)
                      (thread-sleep! (seconds->time (+ start (* n sleep))))
                      (▽ (+ n 1)))))
    (▽ 0)))

(: DEFAULT-STATE state)
(← DEFAULT-STATE `((f ,I) (g ,(λ (_) (values 0 0))) (acc 0) (info ())))

(: wampoo (mutex condition-variable audio-data audio -> void))
(← (wampoo lock τ info audio)
  (letrec*
    ((writer (∈ 'writer audio))
     (closer (∈ 'closer audio))
     (blocks (∈ 'write-blocks info))
     (bufsize (/ (∈ 'write-buf-bytes info) 2))
     (buffer (make-s16vector bufsize 0 #f #f))
     (buffer* (make-locative buffer))
     (buffers (buffer-blocks buffer blocks))
     (▽ (λ (ω)
          (? (∅? ω)
            (→ (writer buffer*) (▽ buffers))
            (→ (mutex-lock! lock)
               (call/cc (λ (cc)
                 (receive (i _)
                   (file-select fileno/stdin #f 0)
                   (with-exception-handler 
                     (λ (e) (print 'err) (cc (void)))
                     (λ () (? i (print (eval (read)))))))))
               (∃ ((state (thread-specific (current-thread)))
                   (f (∈ 'f state)) (g (∈ 'g state)) (acc (∈ 'acc state))
                   (fill-buffer (↑ ω)))
                  (state! (∈←→ 'acc (fill-buffer f g acc) state)))
               (mutex-unlock! lock τ)
               (▽ (↓ ω)))))))
    (state! DEFAULT-STATE)
    (set-info! info)
    (writer buffer*) ; lead fill
    (▽ buffers)
    (closer)
    (free-number-vector buffer)))

(: CLOCK-CHANNEL condition-variable)
(← CLOCK-CHANNEL (make-condition-variable))

(: AUDIO-LOCK mutex)
(← AUDIO-LOCK (make-mutex))

(← info (audio-data 48000 300 10))
(← ao (make-audio info))
(print info)
(← CLOCK-THREAD (make-thread (λ () (clock CLOCK-CHANNEL (∈ 'resolution info)))))
(← WAMPOO-THREAD (make-thread (λ () (wampoo AUDIO-LOCK CLOCK-CHANNEL info ao))))
(thread-start! CLOCK-THREAD)

(: state! ('a -> void))
(← (state! ω) (thread-specific-set! WAMPOO-THREAD ω))

(: state⇒ (('a -> 'b) -> void))
(← (state⇒ f) (state! (f (thread-specific WAMPOO-THREAD))))

(: set-f! (('a -> 'a) -> void))
(← (set-f! f) (state⇒ (λ (ω) (∈←→ 'f f ω))))

(: set-g! (('a -> fixnum fixnum) -> void))
(← (set-g! g) (state⇒ (λ (ω) (∈←→ 'g g ω))))

(: set-acc! ('a -> void))
(← (set-acc! acc) (state⇒ (λ (ω) (∈←→ 'acc acc ω))))

(: set-info! ('a -> void))
(← (set-info! α) (state⇒ (λ (ω) (∈←→ 'info α ω))))

(: audio-info (-> audio-data))
(← (audio-info) (∈ 'info (thread-specific WAMPOO-THREAD)))

(thread-start! WAMPOO-THREAD)
(thread-join! WAMPOO-THREAD)
