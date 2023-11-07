import Mathlib.Tactic

/- This is a test file. Lean is configured correctly if you see the output "32" when
  mousing over or clicking on the next line, and you see no other errors in this file. -/
#eval 2 ^ 5

example (x : ℝ) : x - x = 0 := by simp

#eval "hello World"



#check 2 + 2

def f (x : ℕ) :=
  x + 3/4

#check f
/- why isn't the fct N-->Q or R -/


#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem



theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard

example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩


example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩


example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say m and n are natural numbers, and assume n=2*k.
  rintro m n ⟨k, hk⟩ --how describes hk n=k+k
  -- We need to prove m*n is twice a natural number. Let's show it's twice m*k.
  use m * k
  -- Substitute for n,
  rw [hk]
  -- and now it's obvious.
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]




example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw[mul_assoc]
  rw[mul_comm]



example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw[mul_comm]
  rw[mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw[←mul_comm]
  rw[mul_comm a]
  rw[mul_assoc]


example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]



  example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
    rw[h]


example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw[hyp]
  rw[hyp']
  rw[mul_comm a b]
  rw[sub_self (a * b at hyp)]




/-
And the next one can use:
  sub_self x : x - x = 0
-/

-- 0004
example (a b c d : ℝ) (hyp : c = b*a - d) (hyp' : d = a*b) : c = 0 :=
begin
  -- sorry
  rw hyp' at hyp,
  rw mul_comm b a at hyp,
  rw sub_self (a*b) at hyp,
  exact hyp,
  -- sorry
end


example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]



example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]


variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]


--its not obvious that b*c is part of the expression
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw[mul_assoc a b c]
  rw[h]
  rw[←mul_assoc]




example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]

  example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
    rw[hyp]
    rw[hyp']
    rw [mul_comm a b]
    rw [sub_self]


section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
#check mul_add
#check add_mul

end

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]



example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]


example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d)= a * c + a * d + (b * c + b * d) := by
      rw [mul_add, add_mul, add_mul]
    a * c + a * d + (b * c + b * d)= a * c + a * d + b * c + b * d := by
      rw[← add_assoc]


example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
