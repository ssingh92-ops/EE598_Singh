/-
HW I.4 — EE598

Instructions (from slide deck):
- Put solutions in HW_I_4.lean in the same directory as Basic.lean.
- Restate each problem.
- Textual answers should be written as comments.
- Lean code should produce no errors (sorry is allowed for partial credit).
-/


import Mathlib



-- ============================================================
-- Exercise 1
-- Problem (restated):
-- Define an alternative complex number type in terms of its
-- magnitude and argument. Note: nonnegative reals are `NNReal`
-- in Mathlib.
--
-- Textual explanation:
-- - A “polar complex” is determined by:
-- r : NNReal   (magnitude, forced ≥ 0 by the type)
-- θ : ℝ        (argument / angle)
-- - To interpret it as a usual complex number ℂ, use:
--     re = r * cos θ
--     im = r * sin θ
-- - Coercions:
-- (r : ℝ) coerces NNReal → ℝ so can use trig functions.
-- ============================================================

inductive PolarComplex where
  | mk : NNReal → ℝ → PolarComplex

#check PolarComplex
#check PolarComplex.mk


-- ============================================================
-- Exercise 2
-- Problem (restated):
-- Define `or` for `TriBool` (three-valued logic).
--
-- Textual explanation:
-- Mirror the spirit of the slide’s `and`:
--   * For `or`, True is “dominant”: T ∨ x = T
--   * False acts like the neutral element: F ∨ x = x
--   * Unknown (U) propagates unless the other side forces True:
--       U ∨ T = T
--       U ∨ F = U
--       U ∨ U = U
-- This is a standard Kleene-style three-valued OR.
-- ============================================================


inductive TriBool where
  | T : TriBool
  | F : TriBool
  | U : TriBool
deriving Repr, DecidableEq

open TriBool

def or (A B : TriBool) : TriBool :=
  match A, B with
  | T, _ => T
  | F, x => x
  | U, T => T
  | U, _ => U

-- tests
#eval or T U   -- expected: T
#eval or F U   -- expected: U
#eval or U F   -- expected: U
#eval or F F   -- expected: F
#eval or U U   -- expected: U



-- ============================================================
-- Exercise 3
-- Problem (restated):
-- Lean's rational number type `ℚ` defines `1/0` to be `0`.
-- Define:
--   reciprocal (x : ℚ) : Option ℚ
-- that returns `none` when x is zero.

--Textual explanation:
-- - `Option ℚ` represents "might fail":
--   * `some q` means success with value q
--   * `none` means failure / not defined
-- - Guard explicitly:
--   if x = 0 then none else some (1 / x)
-- ============================================================

def reciprocal (x : ℚ) : Option ℚ :=
  if x = 0 then none else some (1 / x)

-- tests
#eval reciprocal 0              -- expected: none
#eval reciprocal (2/3 : ℚ)      -- expected: some (3/2)
#eval reciprocal (-5 : ℚ)       -- expected: some (-1/5)

-- ============================================================
-- Exercise 4
-- Problem (restated):
-- Define a function `swap` that takes a `BTree α` and swaps the
-- left/right children at every `node`, recursively.
--
-- Textual explanation:
-- - Leaves stay the same.
-- - At a node, recursively swap both subtrees and also flip them.
-- ============================================================

inductive BTree (A : Type) where
  | leaf : A → BTree A
  | node : A → BTree A → BTree A → BTree A

open BTree

def my_tree : BTree Nat :=
  node 1 (leaf 2) (node 3 (leaf 4) (leaf 5))

def swap {A : Type} : BTree A → BTree A
  | leaf a => leaf a
  | node a L R => node a (swap R) (swap L)

#eval swap my_tree

-- ============================================================
-- Exercise 5
-- Problem (restated):
-- Write Expr.CountAdds that counts how many `add` constructors
-- occur in an Expr.
--
-- Will need an auxiliary function, and both must be in a
-- mutual block since Term refers to Expr (via paren) and Expr
-- refers to Term (via neg/add/mul).
-- ============================================================

namespace ExprTree

mutual
  inductive Term where
    | var   : String → Term
    | num   : Nat → Term
    | paren : Expr → Term

  inductive Expr where
    | neg : Term → Expr
    | add : Term → Term → Expr
    | mul : Term → Term → Expr
end

mutual
  def Term.CountAdds (t : Term) : Nat :=
    match t with
    | Term.var _     => 0
    | Term.num _     => 0
    | Term.paren e   => Expr.CountAdds e

  def Expr.CountAdds (e : Expr) : Nat :=
    match e with
    | Expr.neg t       => Term.CountAdds t
    | Expr.mul t1 t2    => Term.CountAdds t1 + Term.CountAdds t2
    | Expr.add t1 t2    => Nat.succ (Term.CountAdds t1 + Term.CountAdds t2)
end

-- quick check: 2*(x+1) has exactly 1 add
def ex : Expr :=
  Expr.mul (Term.num 2) (Term.paren (Expr.add (Term.var "x") (Term.num 1)))

#eval Expr.CountAdds ex   -- 1

end ExprTree

-- ============================================================
-- Exercise 6
-- Problem (restated):
-- Define a structure `Vector3D` representing a 3D vector with three
-- real-number components x, y, z.
-- ============================================================

structure Vector3D where
  x : Int
  y : Int
  z : Int

-- ============================================================
-- Exercise 7
-- Problem (restated):
-- Define a function `cross` that takes two `Vector3D` values and returns
-- their cross product, i.e. the vector
--   (u.y*v.z - u.z*v.y,  u.z*v.x - u.x*v.z,  u.x*v.y - u.y*v.x).
-- Then test it on examples using `#eval`.
-- ============================================================

def cross (u v : Vector3D) : Vector3D :=
  {
    x := u.y * v.z - u.z * v.y,
    y := u.z * v.x - u.x * v.z,
    z := u.x * v.y - u.y * v.x
  }

-- tests (evaluate coordinates sodon't need any fancy printing)
def e1 : Vector3D := { x := 1, y := 0, z := 0 }
def e2 : Vector3D := { x := 0, y := 1, z := 0 }

#eval (cross e1 e2).x   -- expected: 0
#eval (cross e1 e2).y   -- expected: 0
#eval (cross e1 e2).z   -- expected: 1

-- ============================================================
-- Exercise 8
-- Problem (restated):
-- Rewrite cross product function in terms of ℚ × ℚ × ℚ.
-- Note: ℚ × ℚ × ℚ is right-associative, i.e. ℚ × (ℚ × ℚ),
-- so components are accessed as v.1, v.2.1, v.2.2.
-- ============================================================

abbrev Vec3 : Type := ℚ × ℚ × ℚ

def x (p : Vec3) : ℚ := p.1
def y (p : Vec3) : ℚ := p.2.1
def z (p : Vec3) : ℚ := p.2.2

def cross' (u v : Vec3) : Vec3 :=
  ( y u * z v - z u * y v,
    z u * x v - x u * z v,
    x u * y v - y u * x v )

-- ============================================================
-- Exercise 9
-- Problem (restated):
-- A shape is either:
--   - a circle specified by a single rational radius r : ℚ, or
--   - a rectangle specified by a pair of rationals x y : ℚ.
-- Define:
--   area      : Shape → ℚ
--   perimeter : Shape → ℚ
-- Approximate π by 22/7 (or another favorite approximation).
-- ============================================================

abbrev Shape : Type := ℚ ⊕ (ℚ × ℚ)

def piApprox : ℚ := (22 : ℚ) / 7

def area (s : Shape) : ℚ :=
  match s with
  | Sum.inl r        => piApprox * r * r
  | Sum.inr (x, y)   => x * y

def perimeter (s : Shape) : ℚ :=
  match s with
  | Sum.inl r        => 2 * piApprox * r
  | Sum.inr (x, y)   => 2 * (x + y)

#eval area (Sum.inl (2 : ℚ))          -- circle r=2
#eval perimeter (Sum.inr (3, 5))      -- rectangle 3x5

-- ================================================================
-- Exercise 10
-- Problem (restated):
-- Define a polymorphic tree type `MyTree α` where each node stores a value
-- of type `α` and may have *any number* of children (so children are a `List`).
-- Then define a few example trees that show: a leaf (0 kids), a unary node
-- (1 kid), and a node with many kids.
-- ================================================================

inductive MyTree (α : Type) where
  | node : α → List (MyTree α) → MyTree α
deriving Repr

namespace MyTree

def leaf {α : Type} (a : α) : MyTree α :=
  MyTree.node a []

-- examples showing 0, 1, and many children
def exLeaf : MyTree Nat :=
  node 7 []

def exUnary : MyTree Nat :=
  node 1 [node 2 []]

def exMany : MyTree Nat :=
  node 10 [node 20 [], node 30 [node 31 [], node 32 []], node 40 []]

#eval exLeaf
#eval exUnary
#eval exMany


-- ================================================================
-- Exercise 11
-- Problem (restated):
-- Define a *method* that maps a function over every label in a `MyTree`.
-- Then demonstrate it by mapping a function that squares its input over
-- a tree of natural numbers.
-- ================================================================

def map {α β : Type} (t : MyTree α) (f : α → β) : MyTree β :=
  match t with
  | node a kids => node (f a) (kids.map (fun k => k.map f))

-- demo: square every Nat in a tree
def sq (n : Nat) : Nat := n * n

def natTree : MyTree Nat :=
  node 2 [node 3 [], node 4 [node 5 []]]

#eval natTree
#eval natTree.map sq


end MyTree


-- ================================================================
-- Exercise 12
-- Problem (restated):
-- Create a function that converts a `BTree α` (binary tree) into a `MyTree α`
-- (n-ary tree). Then test the conversion on examples.
-- ================================================================

namespace BTree

def toMyTree {α : Type} : BTree α → MyTree α
  | .leaf a       => MyTree.node a []
  | .node a l r   => MyTree.node a [toMyTree l, toMyTree r]

-- test on a sample BTree (matches the shape showed earlier)
def btEx : BTree Nat :=
  BTree.node 1 (BTree.node 3 (BTree.leaf 5) (BTree.leaf 4)) (BTree.leaf 2)

#eval btEx
#eval toMyTree btEx

end BTree

-- ================================================================
-- Exercise 13
-- Problem (restated):
-- Consider the Dyadic Rationals, which consist of fractions whose denominators
-- are powers of two, defined inductively as:
--
--   inductive Dyadic where
--   | zero    : Dyadic
--   | add_one : Dyadic → Dyadic   -- x ↦ x + 1
--   | half    : Dyadic → Dyadic   -- x ↦ x / 2
--   | neg     : Dyadic → Dyadic   -- x ↦ -x
--
-- (a) Define `Dyadic.double` that doubles a Dyadic.
-- (b) Define `Dyadic.add` that adds two Dyadic values.
-- (c) Define `Dyadic.mul` that multiplies two Dyadic values.
-- (d) Define `Dyadic.to_rat` that converts a Dyadic to a Rat.
-- (e) Define the Dyadics 5/8 and −7/32 and test your methods on these values.
-- (f) Are Dyadics as defined here unique? Why or why not?
-- ================================================================

namespace Temp

inductive Dyadic where
  | zero    : Dyadic
  | add_one : Dyadic → Dyadic  -- x ↦ x + 1
  | half    : Dyadic → Dyadic  -- x ↦ x / 2
  | neg     : Dyadic → Dyadic  -- x ↦ -x

-- ----------------
-- (a) Dyadic.double
-- ----------------
def double : Dyadic → Dyadic
  | .zero        => .zero
  | .add_one x   => .add_one (.add_one (double x))
  | .half x      => x
  | .neg x       => .neg (double x)

-- -------------
-- (b) Dyadic.add
-- -------------
def add (x y : Dyadic) : Dyadic :=
  match y with
  | .zero        => x
  | .add_one y'  => .add_one (add x y')
  | .half y'     => .half (add (double x) y')
  | .neg y'      => .neg (add (.neg x) y')

-- -------------
-- (c) Dyadic.mul
-- -------------
def mul (x y : Dyadic) : Dyadic :=
  match y with
  | .zero        => .zero
  | .add_one y'  => add (mul x y') x
  | .half y'     => .half (mul x y')
  | .neg y'      => .neg (mul x y')

-- ----------------
-- (d) Dyadic.to_rat
-- ----------------
def to_rat : Dyadic → Rat
  | .zero        => (0 : Rat)
  | .add_one x   => to_rat x + (1 : Rat)
  | .half x      => to_rat x / (2 : Rat)
  | .neg x       => - (to_rat x)

-- ---------------------------------------------------------
-- (e) Build 5/8 and -7/32, and test double/add/mul/to_rat
-- ---------------------------------------------------------
def fromNat : Nat → Dyadic
  | 0     => .zero
  | n+1   => .add_one (fromNat n)

def halfPow : Nat → Dyadic → Dyadic
  | 0,   x => x
  | k+1, x => .half (halfPow k x)
def five_eighths : Dyadic := halfPow 3 (fromNat 5)          -- 5/8
def neg_seven_32 : Dyadic := .neg (halfPow 5 (fromNat 7))    -- -7/32

-- sanity: values as rationals
#eval to_rat five_eighths     -- 5/8
#eval to_rat neg_seven_32     -- -7/32

-- double tests
#eval to_rat (double five_eighths)   -- 5/4
#eval to_rat (double neg_seven_32)   -- -7/16

-- add test: 5/8 + (-7/32) = 13/32
#eval to_rat (add five_eighths neg_seven_32)  -- 13/32

-- mul test: (5/8)*(-7/32) = -35/256
#eval to_rat (mul five_eighths neg_seven_32)  -- -35/256

-- ------------------------------------------
-- (f) Not unique: different terms, same value
-- ------------------------------------------
-- This Dyadic type is "syntax", not a canonical normal form.
-- Different Dyadic expressions can evaluate to the same rational.
def oneA : Dyadic := .add_one .zero
def oneB : Dyadic := .half (.add_one (.add_one .zero))  -- (2)/2 = 1

#eval to_rat oneA  -- 1
#eval to_rat oneB  -- 1

end Temp
