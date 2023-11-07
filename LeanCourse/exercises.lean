
import Mathlib.Tactic

--its not obvious that b*c is part of the expression
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw[mul_assoc a b c]
  rw[h]
  rw[←mul_assoc]
