/-
HW_IV_1_3.lean
Sukhman Singh
EE598 — Homework IV.3 (Relations)
-/

import Mathlib

namespace Temp

universe u

variable {α : Sort u} {β : Type u}

abbrev Rel := α → α → Prop

def Refl (R : α → α → Prop) := ∀ x, R x x
def Symm (R : α → α → Prop) := ∀ x y, R x y → R y x
def AntiSymm (R : α → α → Prop) := ∀ x y, R x y → R y x → x = y
def Trans (R : α → α → Prop) := ∀ x y z, R x y → R y z → R x z

def te (σ₁ σ₂ : ℕ → α) : Prop := ∃ m, ∀ n > m, σ₁ n = σ₂ n

-- ============================================================
-- Exercise 1
-- Problem (restated):
-- Do the remaining examples left undone on the slide about symmetry.
--
-- Textual explanation:
-- - A relation is symmetric if `R x y` implies `R y x`.
-- - On the symmetry slide, the remaining example is tail equivalence
--   on sequences.
-- - If two sequences are eventually equal after some cutoff `m`,
--   then the equality can simply be reversed termwise after the same
--   cutoff.
-- - So tail equivalence is symmetric.
-- ============================================================

example : Symm (te (α := α)) := by
  intro σ₁ σ₂ h
  rcases h with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro n hn
  exact Eq.symm (hm n hn)

-- ============================================================
-- Exercise 2
-- Problem (restated):
-- Do the remaining examples left undone on the slide about antisymmetry.
--
-- Textual explanation:
-- - A relation is antisymmetric if `R x y` and `R y x` together imply
--   `x = y`.
-- - Subset is antisymmetric: if every element of `A` lies in `B` and
--   every element of `B` lies in `A`, then the two sets are equal.
-- - Tail equivalence on sequences is not antisymmetric: two different
--   sequences can agree from some point onward without being equal
--   everywhere.
-- ============================================================

example : AntiSymm (Set.Subset (α := β)) := by
  intro A B hAB hBA
  ext x
  exact Iff.intro (fun hx => hAB hx) (fun hy => hBA hy)

example : ¬ AntiSymm (te (α := ℕ)) := by
  intro h
  let f : ℕ → ℕ := fun n => if n < 2 then 0 else n
  have hfid : te f id := by
    refine ⟨2, ?_⟩
    intro n hn
    have hnot : ¬ n < 2 := Nat.not_lt.mpr (Nat.le_of_lt hn)
    simp [f, hnot]
  have hidf : te id f := by
    refine ⟨2, ?_⟩
    intro n hn
    have hnot : ¬ n < 2 := Nat.not_lt.mpr (Nat.le_of_lt hn)
    simp [f, hnot]
  have heq : f = id := h f id hfid hidf
  have hne : f 1 ≠ id 1 := by
    simp [f]
  exact hne (congrFun heq 1)

-- ============================================================
-- Exercise 3
-- Problem (restated):
-- Do the remaining examples left undone on the slide about transitivity.
--
-- Textual explanation:
-- - A relation is transitive if `R x y` and `R y z` imply `R x z`.
-- - Subset is transitive because membership can be passed through two
--   inclusions.
-- - Conjunction is transitive in the sense shown on the slide:
--   from `p ∧ q` and `q ∧ r`, we can conclude `p ∧ r`.
-- - Inequality on natural numbers is not transitive, since we can have
--   `1 ≠ 2` and `2 ≠ 1` but not `1 ≠ 1`.
-- ============================================================

example : Trans (Set.Subset (α := β)) := by
  intro A B C hAB hBC x hx
  exact hBC (hAB hx)

example : Trans And := by
  intro p q r hpq hqr
  exact ⟨hpq.left, hqr.right⟩

example : ¬ Trans (Ne (α := ℕ)) := by
  intro h
  have h12 : 1 ≠ 2 := by decide
  have h21 : 2 ≠ 1 := by decide
  have h11 : 1 ≠ 1 := h 1 2 1 h12 h21
  exact h11 rfl

-- ============================================================
-- Exercise 4
-- Problem (restated):
-- Show that the symmetric closure of a symmetric relation is the
-- relation itself:
--
--   example (R : α → α → Prop) :
--     Symm R → ∀ x y, R x y ↔ (SymmC R) x y := ...
--
-- Textual explanation:
-- - If `R` is already symmetric, then adding the symmetric closure
--   does not create any genuinely new edges.
-- - One direction is immediate: any `R x y` gives `SymmC R x y`
--   by the `base` constructor.
-- - For the other direction, a proof of `SymmC R x y` is either
--   already a proof of `R x y`, or it comes from `R y x`.
-- - In the second case, symmetry of `R` turns `R y x` into `R x y`.
-- ============================================================
inductive ReflC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → ReflC R x y
  | refl {x} : ReflC R x x

inductive SymmC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → SymmC R x y
  | symm {x y} : R x y → SymmC R y x

inductive TransC (R : α → α → Prop) : α → α → Prop where
  | base {x y} : R x y → TransC R x y
  | trans {x y z} : R x y → TransC R y z → TransC R x z

example (R : α → α → Prop)
    : Symm R → ∀ x y, R x y ↔ (SymmC R) x y := by
  intro hsym x y
  constructor
  · intro hxy
    exact SymmC.base hxy
  · intro hxy
    cases hxy with
    | base h => exact h
    | symm h => exact hsym _ _ h

-- ============================================================
-- Exercise 5
-- Problem (restated):
-- Show
--
--   example (R : α → α → Prop) : ∀ x y,
--     ReflC (TransC R) x y ↔ TransC (ReflC R) x y := ...
--
-- Textual explanation:
-- - The left-hand side says: either `x = y`, or there is already a
--   transitive chain from `x` to `y` using `R`.
-- - The right-hand side says: there is a transitive chain from `x`
--   to `y` using the reflexive closure of `R`.
-- - From left to right:
--   * a reflexive step becomes a base step using `ReflC.refl`,
--   * a transitive chain over `R` becomes a transitive chain over
--     `ReflC R` by wrapping each `R`-edge with `ReflC.base`.
-- - From right to left:
--   * a base step in `ReflC R` is either reflexive or an `R`-edge,
--   * a transitive chain over `ReflC R` collapses back to a reflexive
--     closure of a transitive chain over `R`.
-- ============================================================

example (R : α → α → Prop) : ∀ x y,
    ReflC (TransC R) x y ↔ TransC (ReflC R) x y := by
  intro x y
  constructor
  · intro h
    cases h with
    | refl =>
        exact TransC.base ReflC.refl
    | base hT =>
        induction hT with
        | base hR =>
            exact TransC.base (ReflC.base hR)
        | trans hR hT ih =>
            exact TransC.trans (ReflC.base hR) ih
  · intro h
    induction h with
    | base hR =>
        cases hR with
        | refl =>
            exact ReflC.refl
        | base h =>
            exact ReflC.base (TransC.base h)
    | trans hxy hyz ih =>
        cases hxy with
        | refl =>
            exact ih
        | base h =>
            cases ih with
            | refl =>
                exact ReflC.base (TransC.base h)
            | base hT =>
                exact ReflC.base (TransC.trans h hT)

-- ============================================================
-- Exercise 6
-- Problem (restated):
-- Given two sequences of natural numbers, define the subsequence
-- order by
--
--   def subseq {α : Type u} (σ τ : ℕ → α) :=
--     ∃ f, StrictMono f ∧ σ = τ ∘ f
--
-- and show that `subseq` is reflexive and transitive, but not
-- antisymmetric.
--
-- Textual explanation:
-- - A sequence `σ` is a subsequence of `τ` if there is a strictly
--   increasing function `f` such that `σ n = τ (f n)` for all `n`.
-- - Reflexivity uses the identity function.
-- - Transitivity uses composition of the two witness functions.
-- - Antisymmetry fails: two different sequences can each be obtained
--   from the other by skipping the first term.
-- - A standard counterexample is the alternating sequences
--   `0,1,0,1,...` and `1,0,1,0,...`, which are mutual subsequences
--   but are not equal.
-- ============================================================

def subseq {α : Type u} (σ τ : ℕ → α) : Prop :=
  ∃ f, StrictMono f ∧ σ = τ ∘ f

example {α : Type u} : Refl (@subseq α) := by
  intro σ
  refine ⟨id, ?_, ?_⟩
  · intro a b hab
    exact hab
  · funext n
    rfl

example {α : Type u} : Trans (@subseq α) := by
  intro σ τ υ hστ hτυ
  rcases hστ with ⟨f, hfmono, hστ⟩
  rcases hτυ with ⟨g, hgmono, hτυ⟩
  refine ⟨g ∘ f, ?_, ?_⟩
  · intro a b hab
    exact hgmono (hfmono hab)
  · rw [hστ, hτυ]
    rfl

example : ¬ AntiSymm (@subseq ℕ) := by
  intro hanti
  let σ : ℕ → ℕ := fun n => n % 2
  let τ : ℕ → ℕ := fun n => (n + 1) % 2

  have hστ : subseq σ τ := by
    refine ⟨Nat.succ, ?_, ?_⟩
    · intro a b hab
      exact Nat.succ_lt_succ hab
    · funext n
      simp [σ, τ, Nat.add_assoc]

  have hτσ : subseq τ σ := by
    refine ⟨Nat.succ, ?_, ?_⟩
    · intro a b hab
      exact Nat.succ_lt_succ hab
    · funext n
      simp [σ, τ, Nat.add_assoc]

  have heq : σ = τ := hanti σ τ hστ hτσ

  have hne : σ 0 ≠ τ 0 := by
    simp [σ, τ]

  exact hne (congrFun heq 0)

-- ============================================================
-- Exercise 10
-- Problem (restated):
-- Define the shift operator on germs by lifting the pre-shift
-- operation on sequences.
-- ============================================================
instance te_equiv {α : Type u} : Equivalence (te (α := α)) := {
  refl := by
    intro σ
    exact ⟨0, by intro n hn; rfl⟩
  symm := by
    intro σ τ h
    rcases h with ⟨m, hm⟩
    exact ⟨m, by intro n hn; exact Eq.symm (hm n hn)⟩
  trans := by
    intro σ τ υ hστ hτυ
    rcases hστ with ⟨m1, h1⟩
    rcases hτυ with ⟨m2, h2⟩
    refine ⟨m1 ⊔ m2, ?_⟩
    intro n hn
    have hn1 : m1 < n := lt_of_le_of_lt (Nat.le_max_left m1 m2) hn
    have hn2 : m2 < n := lt_of_le_of_lt (Nat.le_max_right m1 m2) hn
    rw [h1 n hn1, h2 n hn2]
}

instance te_setoid {α : Type u} : Setoid (ℕ → α) := {
  r := te
  iseqv := te_equiv
}

def Germ (α : Type u) := Quotient (te_setoid (α := α))

def Germ.mk {α : Type u} (σ : ℕ → α) : Germ α := Quotient.mk _ σ


def pre_shift {α : Type u} (σ : ℕ → α) : Germ α := ⟦fun n => σ (n + 1)⟧

theorem te_shift_respects {α : Type u} :
    ∀ (σ τ : ℕ → α), te σ τ → pre_shift σ = pre_shift τ := by
  intro σ τ h
  apply Quotient.sound
  rcases h with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  intro n hn
  exact hm (n + 1) (Nat.lt_trans hn (Nat.lt_succ_self n))

def shift {α : Type u} (σ : Germ α) : Germ α :=
  Quotient.lift pre_shift te_shift_respects σ

-- ============================================================
-- Exercise 11
-- Problem (restated):
-- Show shifting the zero germ gives the zero germ.
-- ============================================================

example : shift (⟦fun _ : ℕ => (0 : ℤ)⟧ : Germ ℤ) = (⟦fun _ : ℕ => (0 : ℤ)⟧ : Germ ℤ) := by
  rfl

-- ============================================================
-- Exercise 12
-- Problem (restated):
-- Give an example of a function on ℕ → ℕ that does not preserve
-- tail equivalence.
-- ============================================================

def my_func (σ : ℕ → ℕ) : ℕ → ℕ := fun _ => σ 0

def σ₁ : ℕ → ℕ := fun n => n

def σ₂ : ℕ → ℕ := fun n => if n = 0 then 1 else n

example : te σ₁ σ₂ ∧ ¬ te (my_func σ₁) (my_func σ₂) := by
  constructor
  · refine ⟨0, ?_⟩
    intro n hn
    have hne : n ≠ 0 := Nat.ne_of_gt hn
    simp [σ₁, σ₂, hne]
  · intro h
    rcases h with ⟨m, hm⟩
    have h01 := hm (m + 1) (Nat.lt_succ_self m)
    have : (0 : ℕ) = 1 := by
      simpa [my_func, σ₁, σ₂] using h01
    exact Nat.zero_ne_one this
end Temp
