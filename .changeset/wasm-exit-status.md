---
"everystate": patch
---

The WebAssembly fallback of the command now exits with the same status as the native binary (12 for an invariant violation, and so on) instead of always 0.
