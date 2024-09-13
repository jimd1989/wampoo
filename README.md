# Wampoo

Minimal audio REPL. Experiments in Scheme→C and manual memory management.

Requires Chicken Scheme and libao. Compiles on MacOS with

```
csc -strict-types -O3 -I/opt/homebrew/include -L/opt/homebrew/lib -L -lao -o wampoo wampoo.scm
```

Might need different location for different OS.

Starts by ouputting silence. Can run `(volume 0.001)` and ramp it up from there to hear white noise.

libao response is sluggish even with small buffer sizes. Might go back to sndio.
