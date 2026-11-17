---
"everystate": minor
---

Add a PlusCal translator, `everystate pcal [options] File.tla` (also `java pcal.trans` through the Java stand-in, and `translatePlusCal` in the WebAssembly API), whose output is byte-identical to the Java translator's; the model checker now warns, like TLC, when an algorithm or its translation changed since it was translated.
