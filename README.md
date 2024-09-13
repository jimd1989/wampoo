# Wampoo

Minimal audio REPL. Experiments in Scheme→C and manual memory management.

Requires Chicken Scheme and libao. Compiles on MacOS with

```
csc -strict-types -O3 -I/opt/homebrew/include -L/opt/homebrew/lib -L -lao -o wampoo wampoo.scm
```

Might need different location for different OS.

Currently outputs complete silence, but does output. Tweaking performance of main loop before adding more features.
