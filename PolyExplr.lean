/-
AI-Assisted Project Exploration
Author: Sukhman Singh

This file documents exploratory prompt sessions conducted while selecting
a final Lean formalization project. The goal was to investigate multiple
technical directions and ask clarifying questions before settling on a
project.

The final project chosen is:

  Formalizing the category of polynomial functors
  (Type-level container semantics) in Lean 4.

Only prompts are included below, per assignment instructions.
No AI responses are included.

=====================================================================
CHAT 1 — W-Types vs Polynomial Functors
=====================================================================

1. Does Lean 4 support W-types natively?
2. If not, how are strictly positive inductive families encoded internally?
3. Are polynomial functors equivalent to strictly positive inductive types?
4. What is the categorical definition of a polynomial functor in `Type`?
5. Is every container functor polynomial?
6. What conditions guarantee existence of an initial algebra?
7. Are W-types initial algebras of polynomial functors?
8. How does Lean enforce strict positivity syntactically?
9. Can W-types be reconstructed directly from container data (A, B : A → Type)?
10. What is the precise relationship between polynomial functors and dependent sums/products?
11. Does Mathlib already define containers?
12. Is there an existing category of containers in Lean?
13. If not, what minimal structure is required to define one?
14. Are polynomial functors closed under composition?
15. How difficult is it to formalize composition in Lean?
16. Would formalizing the category of polynomial functors be feasible in ~5 weeks?
17. What typical proof-engineering pitfalls arise in such a project?

=====================================================================
CHAT 2 — Category Structure of Polynomial Functors
=====================================================================

1. How should morphisms between polynomial functors be defined?
2. Is a polynomial morphism equivalent to a natural transformation?
3. What is the forward/backward (lens-style) decomposition of such morphisms?
4. Why is the direction map contravariant in the lens formulation?
5. Does composition of lenses correspond directly to composition of natural transformations?
6. Is associativity straightforward to prove in Lean?
7. What universe constraints arise when defining `Poly : Type u`?
8. Does `Poly` form a category without additional structure?
9. Do we require function extensionality to prove identity laws?
10. How can Yoneda simplify reasoning about polynomial morphisms?
11. Is it better to define morphisms directly or derive them from NatTrans?
12. Is the category of polynomial functors locally cartesian closed?
13. What additional structure is required to show LCCC?
14. Are polynomial functors closed under limits?
15. How do limits act on positions and directions?
16. How do colimits act on positions and directions?
17. Is the container formulation simpler than a set-level formulation?
18. What parts of this theory already exist in Mathlib?
19. Which core constructions must be implemented manually?

=====================================================================
CHAT 3 — Exploration: Categorical Models of AI Architectures
=====================================================================

1. Can neural network layers be modeled as polynomial functors?
2. Do variational autoencoders correspond to coalgebras of some functor?
3. Is there a categorical interpretation of encoder–decoder architectures?
4. Are lenses related to bidirectional transformations in ML systems?
5. Can state machines for training loops be expressed as polynomial functors?
6. Is there existing work connecting category theory and deep learning in Lean?
7. Would formalizing categorical models of VAEs exceed a 5-week scope?
8. Would this require probability theory formalization in Lean?
9. Is it realistic to formalize even a minimal VAE?
10. Compared to this, is formalizing polynomial functor categories more tractable?
11. Does the polynomial route have clearer mathematical boundaries?
12. Would it allow stronger formal guarantees with less analytic overhead?

=====================================================================
CHAT 4 — Internal Polynomial Functors and LCCC Structure
=====================================================================

1. How are polynomial functors defined internally in a locally cartesian closed category?
2. What is the role of Σ (dependent sum), Π (dependent product), and Δ (pullback) in internal polynomials?
3. How does Beck–Chevalley coherence arise in composition?
4. Is Π best treated as per-map right adjoint data rather than global structure?
5. How are polynomial morphisms represented internally in slices?
6. Does the lens decomposition persist in arbitrary LCCCs?
7. What additional coherence conditions must be verified in Lean?
8. How do pullbacks interact with dependent products formally?
9. Are quotients required to compute certain colimits internally?
10. When formalizing colimits of polynomial functors, do positions take limits while directions take colimits?
11. How does pushout structure manifest in the container formulation?
12. Are colimits in `Type` implemented using quotients in Lean?
13. Does Mathlib provide pushouts in `Type` directly?
14. What universe issues arise in internal slice categories?
15. Is it realistic to formalize Beck–Chevalley conditions within project scope?
16. Would a transport theorem connecting container semantics to internal LCCC semantics be feasible?
17. Which of these internal results are minimal and which are optional extensions?

=====================================================================
FINAL PROJECT DECISION
=====================================================================

After exploring multiple directions (W-types, inductive encodings,
categorical models of neural networks, internal polynomial functors),
the selected project is:

  Formalizing the category of polynomial functors
  using Type-level container semantics in Lean 4.

Planned components:

• Definition of polynomial functors as containers.
• Definition of morphisms (lens decomposition).
• Proof of category structure (identity, composition).
• Investigation of limits/colimits behavior on positions/directions.
• Optional: bridge to internal LCCC formulation.

This choice balances theoretical depth with feasible scope
within the course timeline.
-/

-- ============================================================
-- EE 598
-- Homework IV
--
-- This file formalizes natural deduction rules for ∧, ∨, ¬, ↔,
-- and introduces the Nor connective constructively.
--
-- All proofs are term-level only (no tactics).
-- ============================================================

namespace Temp

variable (p q r : Prop)

-- ------------------------------------------------------------
-- Exercise 1
-- Associativity of conjunction:
--
--     p ∧ (q ∧ r) → (p ∧ q) ∧ r
--
-- Logical idea:
--   Conjunction is a structure with projections.
--   We destructure the nested conjunction and rebuild it
--   in the desired grouping.
--
-- Uses:
--   ∧-elim (projection)
--   ∧-intro (constructor)
-- ------------------------------------------------------------

example : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
  fun ⟨hp, hqr⟩ =>
    ⟨⟨hp, hqr.left⟩, hqr.right⟩

-- ------------------------------------------------------------
-- Exercise 2
-- Definition of ↔ as a structure:
--
--     (p ↔ q) ↔ ((p → q) ∧ (q → p))
--
-- Logical idea:
--   Iff.intro packages forward and backward implications.
--   This exercise unpacks and repackages that structure.
--
-- Uses:
--   ↔-intro (structure constructor)
--   projection fields mp and mpr
-- ------------------------------------------------------------

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) :=
  Iff.intro
    (fun hpq =>
      ⟨hpq.mp, hpq.mpr⟩)
    (fun h =>
      Iff.intro h.left h.right)

-- ------------------------------------------------------------
-- Exercise 3
-- Classical logical equivalences proven constructively.
-- Each uses only Or/And elimination and introduction.
-- ------------------------------------------------------------

-- ------------------------------------------------------------
-- 1. Commutativity of disjunction:
--    p ∨ q ↔ q ∨ p
--
-- Strategy:
--   Case split on disjunction and swap constructors.
-- ------------------------------------------------------------
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun hpq =>
      match hpq with
      | Or.inl hp => Or.inr hp
      | Or.inr hq => Or.inl hq)
    (fun hqp =>
      match hqp with
      | Or.inl hq => Or.inr hq
      | Or.inr hp => Or.inl hp)

-- ------------------------------------------------------------
-- 2. Associativity of disjunction:
--    (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
--
-- Strategy:
--   Nested case analysis on outer and inner disjunction.
-- ------------------------------------------------------------
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun h =>
      match h with
      | Or.inl hpq =>
          match hpq with
          | Or.inl hp => Or.inl hp
          | Or.inr hq => Or.inr (Or.inl hq)
      | Or.inr hr => Or.inr (Or.inr hr))
    (fun h =>
      match h with
      | Or.inl hp => Or.inl (Or.inl hp)
      | Or.inr hqr =>
          match hqr with
          | Or.inl hq => Or.inl (Or.inr hq)
          | Or.inr hr => Or.inr hr)

-- ------------------------------------------------------------
-- 3. De Morgan law:
--    ¬(p ∨ q) ↔ (¬p ∧ ¬q)
--
-- Strategy:
--   Left-to-right:
--     assume h : (p ∨ q) → False
--     derive each negation separately.
--
--   Right-to-left:
--     destruct disjunction and apply corresponding negation.
-- ------------------------------------------------------------
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun h =>
      ⟨ (fun hp => h (Or.inl hp)),
        (fun hq => h (Or.inr hq)) ⟩)
    (fun h hpq =>
      match hpq with
      | Or.inl hp => h.left hp
      | Or.inr hq => h.right hq)

-- ------------------------------------------------------------
-- 4. Law of non-contradiction:
--    ¬(p ∧ ¬p)
--
-- Strategy:
--   Extract contradiction directly.
-- ------------------------------------------------------------
example : ¬(p ∧ ¬p) :=
  fun ⟨hp, hnp⟩ => hnp hp

-- ------------------------------------------------------------
-- 5. Disjunction elimination inside implication:
--    (¬p ∨ q) → (p → q)
--
-- Strategy:
--   Case split on disjunction.
-- ------------------------------------------------------------
example : (¬p ∨ q) → (p → q) :=
  fun h hp =>
    match h with
    | Or.inl hnp => False.elim (hnp hp)
    | Or.inr hq  => hq

-- ------------------------------------------------------------
-- 6. Identity of False in disjunction:
--    p ∨ False ↔ p
-- ------------------------------------------------------------
example : p ∨ False ↔ p :=
  Iff.intro
    (fun h =>
      match h with
      | Or.inl hp => hp
      | Or.inr hf => False.elim hf)
    (fun hp => Or.inl hp)

-- ------------------------------------------------------------
-- 7. Absorption of False in conjunction:
--    p ∧ False ↔ False
-- ------------------------------------------------------------
example : p ∧ False ↔ False :=
  Iff.intro
    (fun h => h.right)
    (fun hf => ⟨False.elim hf, hf⟩)

-- ================================================================
-- Exercise 4
-- Classical reasoning:
--   (p → q) → (¬p ∨ q)
--
-- Logical idea:
--   Use excluded middle on p and perform Or-elimination.
-- ================================================================

open Classical

example : (p → q) → (¬p ∨ q) :=
  fun hpq =>
    Or.elim (Classical.em p)
      (fun hp => Or.inr (hpq hp))
      (fun hnp => Or.inl hnp)

end Temp

-- ================================================================
-- Exercise 5
-- Define the Nor connective constructively.
--
-- Nor-intro:
--   ¬p → ¬q → Nor p q
--
-- Nor-elim-left:
--   Nor p q → ¬p
--
-- Nor-elim-right:
--   Nor p q → ¬q
--
-- Nor behaves constructively as ¬p ∧ ¬q.
-- ================================================================

inductive Nor (p q : Prop) : Prop where
| intro : ¬p → ¬q → Nor p q

def Nor.elim_left {p q : Prop} (hnpq : Nor p q) : ¬p :=
  match hnpq with
  | Nor.intro hnp _ => hnp

def Nor.elim_right {p q : Prop} (hnpq : Nor p q) : ¬q :=
  match hnpq with
  | Nor.intro _ hnq => hnq

-- ------------------------------------------------------------
-- Type checks and elimination check for nor
-- ------------------------------------------------------------

#check Nor.intro
-- Nor.intro : ¬p → ¬q → Nor p q

#check Nor.elim_left
-- Nor.elim_left : Nor p q → ¬p

#check Nor.elim_right
-- Nor.elim_right : Nor p q → ¬q

example (hnp : ¬p) (hnq : ¬q) :
  Nor.elim_left (Nor.intro hnp hnq) = hnp :=
rfl

example (hnp : ¬p) (hnq : ¬q) :
  Nor.elim_right (Nor.intro hnp hnq) = hnq :=
rfl

-- ================================================================
-- Exercise 6
-- Show Nor is equivalent to ¬(p ∨ q)
-- ================================================================

-- 1. ¬p → Nor p p
example : ¬p → Nor p p :=
  fun hnp =>
    Nor.intro hnp hnp

-- 2. Nor p q → ¬(p ∨ q)
example : Nor p q → ¬(p ∨ q) :=
  fun hnor hpq =>
    match hpq with
    | Or.inl hp => Nor.elim_left hnor hp
    | Or.inr hq => Nor.elim_right hnor hq

-- 3. ¬(p ∨ q) → Nor p q
example : ¬(p ∨ q) → Nor p q :=
  fun h =>
    Nor.intro
      (fun hp => h (Or.inl hp))
      (fun hq => h (Or.inr hq))
