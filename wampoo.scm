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

(define-type buffer u32vector)
(define-type fill (('a -> 'a) ('a -> fixnum fixnum) 'a -> 'a))
(define-type condition-variable (struct condition-variable))
(define-type audio-data (list-of (list symbol number)))
(define-type audio (list (list symbol (pointer -> void))
                         (list symbol (-> void))))
(define-type state (list (list symbol ('a -> 'a))
                         (list symbol ('a -> fixnum fixnum))
                         (list symbol 'a)))

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

(: stereo-sample (fixnum fixnum --> fixnum))
(← (stereo-sample l r)
  (∃ ((b1 (arithmetic-shift (bitwise-and l 255) 24))
      (b2 (bitwise-ior b1 (arithmetic-shift (arithmetic-shift l -8) 16)))
      (b3 (bitwise-ior b2 (arithmetic-shift (bitwise-and r 255) 8))))
    (bitwise-ior b3 (arithmetic-shift r -8))))

(: buffer⇒ (fixnum fixnum u32vector ('a -> 'a) ('a -> fixnum fixnum) 'a -> 'a))
(← (buffer⇒ n m ω f g α)
  (? (= n m) α
    (∃ ((a (f α)) (s (receive (l r) (g a) (stereo-sample l r))))
      (u32vector-set! ω n s)
      (buffer⇒ (+ n 1) m ω f g a))))

(: windows ((list-of fixnum) --> (list-of (list fixnum fixnum))))
(← (windows ω) (↓ (⇐ (λ (acc x) `(,x ,@(↓ acc) ,(list (↑ acc) x))) '(0) ω)))

(: buffer-blocks (u32vector fixnum --> (list-of fill)))
(← (buffer-blocks ω n)
  (∃ ((size (/ (u32vector-length ω) n))
      (slices (windows (ι n size size))))
    (∀ (λ (nm) (λ (f g α) (buffer⇒ (↑ nm) (↑↓ nm) ω f g α))) slices)))

(: silence (fill fixnum -> fixnum))
(← (silence f ω) (f I (λ (_) (values 0 0)) ω))

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
(← DEFAULT-STATE `((f ,I) (g ,(λ (_) (values 0 0))) (acc 0)))

(: state! ('a -> void))
(← (state! ω) (thread-specific-set! (current-thread) ω))

(: state⇒ (('a -> 'b) -> void))
(← (state⇒ f) (state! (f (thread-specific (current-thread)))))

(: set-f! (('a -> 'a) -> void))
(← (set-f! f) (state⇒ (λ (ω) (∈←→ 'f f ω))))

(: set-g! (('a -> fixnum fixnum) -> void))
(← (set-g! g) (state⇒ (λ (ω) (∈←→ 'g g ω))))

(: set-acc! ('a -> void))
(← (set-acc! acc) (state⇒ (λ (ω) (∈←→ 'acc acc ω))))

(: wampoo (condition-variable audio-data audio -> void))
(← (wampoo τ info audio)
  (letrec*
    ((lock (make-mutex))
     (writer (∈ 'writer audio))
     (closer (∈ 'closer audio))
     (blocks (∈ 'write-blocks info))
     (bufsize (/ (∈ 'write-buf-bytes info) 4))
     (buffer (make-u32vector bufsize 0 #f #f))
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
    (▽ buffers)
    (closer)
    (free-number-vector buffer)))

(: CLOCK-CHANNEL condition-variable)
(← CLOCK-CHANNEL (make-condition-variable))

(← info (audio-data 48000 300 10))
(← ao (make-audio info))
(print info)
(← clock-thread (make-thread (λ () (clock CLOCK-CHANNEL (∈ 'resolution info)))))
(← wampoo-thread (make-thread (λ () (wampoo CLOCK-CHANNEL info ao))))
(thread-start! clock-thread)
(thread-start! wampoo-thread)
(thread-join! wampoo-thread)
