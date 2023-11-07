import LeanCourse.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

-- ¬ A abbreviates A → False
example (h : a < b) : ¬b < a := by
  intro h' --entpackt die Aussage die zu beweisen ist
  have : a < a := lt_trans h h' --führen folgerung von h und h' ein
  apply lt_irrefl a this  --lt_irrefl  ist ein wiederspruch zu this

#check lt_irrefl

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub --entpacken was zu zeigen ist
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=by
  intro fnlb
  rcases fnlb with ⟨a, fnlba⟩
  rcases h a with ⟨x, hx⟩
  have: f x ≥ a := fnlba x
  linarith


example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨a, ha⟩
  rcases h a with ⟨x, hx⟩
  have := ha x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, ha⟩ --rintro entpackt ¬FnHasUb
  have : a + 1 ≤ a := ha (a + 1) --lower bound übergeben
  linarith



#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h
  apply h''

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h' --wenn h' stimmt, ist das gegenteil absurd
  apply not_lt_of_ge (h h'')



example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h' --wegen false kannst du nur was falschen geben
  apply not_lt_of_ge
  apply h''
  apply h

--wenn funktion nicht monoton ist, ist die folgerung  falsch
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ) --ich glaube f:R --> 0
  have monof : Monotone f := by intro a b ab; rfl --f a ≤ f b ist das gleiche wie folgerung der monotonie
  have h' : f 1 ≤ f 0 := le_refl _ --wieos _
  have : (1 : ℝ) ≤ 0 := h monof h' --wieso kein by
  linarith



#check rfl
#check le_refl

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
   apply le_of_not_gt
   intro h'
   linarith [h _ h']

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro alpha eP
  apply h
  use alpha

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨alpha,eP⟩ 
  apply h alpha eP
  

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro ax
  rcases h with ⟨x, nPx⟩
  apply nPx
  apply ax


example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

#check by_contra




example (h : ¬¬Q) : Q := by
  by_contra a
  exact h a --2 sachen die im wiederspruch stehen 
  

example (h : Q) : ¬¬Q := by
  intro a
  exact a h --2 sachen die im wiederspruch stehen 

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h --umschreiben 
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h  --schreibe def von FnHasUb und FnUb
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg  at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso --replaces the current goal with the goal of proving False
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0) --die beide sache zusammen sind falsch

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction --close a goal by finding a contradiction in the hypotheses

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  linarith 
  
end
