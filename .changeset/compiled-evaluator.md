---
"everystate": minor
---

Actions and invariants are now compiled once into closures over a frame of slots, with the tree-walking evaluator as the automatic fallback: about 30% less CPU on actor-style models and 6% on the benchmark set, with identical results. `EVERYSTATE_EVAL=tree` selects the tree-walker alone. An experimental bounded cache of local steps is available with `EVERYSTATE_STEP_CACHE=on` (off by default; `EVERYSTATE_STEP_CACHE_MB` sets its fixed size, default 32, per worker).
