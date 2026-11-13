---- MODULE MCBase ----
EXTENDS Base
WiderLimit(v) ==
  LET B == INSTANCE Base IN B!Limit(v) \/ v = 3
====
