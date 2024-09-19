# Wampoo

Not a synthesizer. Not an audio language. An "audio REPL." That is, a normal Scheme session that happens to be writing audio (silence) in the background. The user has access to the sound buffers, but no technical nor musical conventions are enforced beyond that.

An experiment in C FFI and manual memory management. Not intended for reliable performances.

## Building

Requires Chicken Scheme and libao. Compiles on MacOS with

```
csc -strict-types -O3 -I/opt/homebrew/include -L/opt/homebrew/lib -L -lao -o wampoo wampoo.scm
```

Might need different location for different OS. Can go up to `-O5`. Also look into `-lfa2` and `-specialize`, among others.

libao is sluggish and CPU usage is higher than it should be for something this simple. Might specialize this to use sndio later.

## Usage

User is dropped into a shell living inside a srfi-18 thread. Any Scheme command can be evaluated here, including loading additional libraries. Audio is always playing, and playback state lives within an assoc list of the thread's `(thread-specific)` value. Audio is controlled by manipulating these fields. Helper functions exist, but can always modify this object directly with `(thread-specific-set! (current-thread))`.

The fields:

- `acc`: An arbitrary type `a` that represents running state across multiple audio buffer writes. Anything like wave phase, active/inactive voices, and volume would be stored in a single object here. Modified with helper function `(set-acc! new-acc)`.
- `f`: A function of type `a → a` that adjusts the audio state across an individual sampling period. If a wave's phase were expected to increment, it'd be done here. Can be adjusted with `(set-f! new-f)`.
- `g`: A function of type `a → int16 int16` that renders the current audio state at a given sampling period into a 16 bit stereo signal. Conversion from float to fixnum, dithering, mixing, etc would happen here. Multiple values representing left and right audio samples are returned with `(values l r)`. Modified with `(set-g! new-g)`. Note that these samples have to be little-endian encoded.
- `info`: A readonly struct representing audio configuration. Fetched with `(audio-info)`. Should not need to worry about buffer sizes because `f` and `g` abstract this away, but might need to reference sample rate.

A thread condition representing the global clock is available as `CLOCK-CHANNEL`. It presents a running count of pulses to modulo against. Might be useful in composition. The mutex of the main thread is also presented as `AUDIO-LOCK`. Any direct commands in the main shell do not need to use this mutex, since their evaluation is already behind a lock. Only useful for user-spawned child threads.

Audio is locked to 48,000hz sample rate, 16 bit little-endian audio, stereo channels. Recompile the program with your own desires.

One can write an experimental instrument by having Wampoo listen to a FIFO, then interactively write text editor output to it. The audio performance of this interpreted Scheme will be horrendous. Once the proof of concept is established. This code that runs atop Wampoo can itself be compiled with `csc -s -J`. Running `(load "my-compiled-code")` within Wampoo will expose your instrument with better performance. There's nothing stopping you from mixing in C as well. See `example.scm`.

## Caveats

This still crashes on certain errors despite being wrapped in a handler. This isn't really intended as a live performance envrionment as much as it is interactive scaffolding to build instruments.
