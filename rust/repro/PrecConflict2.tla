---- MODULE PrecConflict2 ----
\* SANY's second rule: a prefix operator as right operand of a tighter infix operator.
\* TLC rejects this; everystate (both engines) still accepts it and evaluates 2 * (-x).
EXTENDS Integers
VARIABLE x
Init == x = 1
Next == x' = IF x = 1 THEN 2 * -x ELSE x
====
