-- ============================================================
-- Exercise 1
-- Problem (restated):
-- Define a function `abs_diff` that takes two natural numbers and returns
-- the absolute value of their difference. Evaluate:
--   #eval abs_diff 23 89
--   #eval abs_diff 101 89
--
-- Textual explanation:
-- - On `Nat`, subtraction is truncated: if x ≥ y then x - y = ℝ+ ∨ 0 else y - x = ℝ+.
-- - Absolute difference is implemented by branching on `x ≥ y` and subtracting
--   in the direction that avoids truncation.
-- ============================================================


import Mathlib


def abs_diff (x y : ℕ) : ℕ :=
  if x ≥ y
  then x - y
  else y - x

#eval abs_diff 23 89
  --expected output: 66
#eval abs_diff 101 89
  --expected output: 12


-- ============================================================
-- Exercise 2
-- Problem (restated):
-- Define a function `apply_twice_when_even` that takes a function `f : Nat → Nat`
-- and a natural number `x : Nat`, returning:
-- - `f (f x)` if `x` is even
-- - `f x` otherwise
-- Evaluate:
--   #eval apply_twice_when_even (abs_diff 10) 8
--   #eval apply_twice_when_even (abs_diff 10) 11
--
-- Textual explanation:
-- - `abs_diff : Nat → Nat → Nat` is curried, so `(abs_diff 10)` has type `Nat → Nat`.
-- - `Even x` is a proposition used to choose between the two branches.
-- - For x = 8 (even):  abs_diff 10 8 = 2, then abs_diff 10 2 = 8.
-- - For x = 11 (odd):  abs_diff 10 11 = 1.
-- ============================================================


def apply_twice_when_even (f : ℕ → ℕ) (x : ℕ) :=
  if Even x
  then f (f x)
  else f x

#eval apply_twice_when_even (abs_diff 10) 8
  --expected output: 8
#eval apply_twice_when_even (abs_diff 10) 11
  --expected output: 1

-- ============================================================
-- Exercise 3
-- Problem (restated):
-- Recall Fibonacci is defined by:
--   fib 0 = 1
--   fib 1 = 1
--   fib n = fib (n-1) + fib (n-2)
-- Define `fib` using head recursion. Test it with a few examples.
--
-- Textual explanation:
-- - “Head recursion” here means the recursive calls happen inside the expression
--   being returned (i.e., `fib (n+2)` is defined in terms of `fib (n+1)` and `fib n`).
-- - This is the classic exponential-time Fibonacci definition.
-- ============================================================

def fib_head : Nat → Nat
  | 0 => 1
  | 1 => 1
  | (n + 2) => fib_head (n + 1) + fib_head n

#eval fib_head 0   -- 1
#eval fib_head 1   -- 1
#eval fib_head 2   -- 2
#eval fib_head 3   -- 3
#eval fib_head 4   -- 5
#eval fib_head 5   -- 8
#eval fib_head 15  -- 987


-- ============================================================
-- Exercise 4
-- Problem (restated):
-- Define `fib` using tail recursion. Test it with a few examples.
-- Hint: define a helper taking three arguments `n a b` where `a` and `b` are the
-- previous two values in the sequence.
--
-- Textual explanation:
-- - “Tail recursion” means the recursive call is the final action.
-- - The helper maintains an invariant:
--     fib_tailAux n a b  computes the nth Fibonacci value assuming:
--       a = fib k and b = fib (k+1) for the current step.
-- - Each step shifts (a,b) ↦ (b, a+b) and decrements n.
-- - This runs in linear time.
-- ============================================================

def fib_tail (n : Nat) : Nat :=
  let rec fib_tailAux : Nat → Nat → Nat → Nat
    | 0, a, _ => a
    | (n + 1), a, b => fib_tailAux n b (a + b)
  fib_tailAux n 1 1

#eval fib_tail 0   -- 1
#eval fib_tail 1   -- 1
#eval fib_tail 2   -- 2
#eval fib_tail 3   -- 3
#eval fib_tail 4   -- 5
#eval fib_tail 5   -- 8
#eval fib_tail 10  -- 89

-- ============================================================
-- Exercise 5
-- Problem (restated):
-- Define a function `mediant (x y : Rat)` that evaluates to
-- (numerator(x) + numerator(y)) / (denominator(x) + denominator(y)).
--
-- Textual explanation:
-- - In this setup, `Rat` is notation for `ℚ`.
-- - Mathlib does not provide `Rat.mkRat` here, so constructing the result is done
--   by working in `ℚ` directly:
--     coerce the integer numerators and natural denominators into `ℚ`,
--     then form the quotient.
-- - For rationals, `x.num : Int` and `x.den : Nat` are available.
-- ============================================================


def mediant (x y : ℚ) : ℚ :=
  ((x.num + y.num : Int) : ℚ) / ((x.den + y.den : Nat) : ℚ)

#check mediant

-- tests
#eval mediant (1/2 : ℚ) (1/3 : ℚ)          -- 2/5
#eval mediant (23/89 : ℚ) (101/89 : ℚ)     -- 62/89
#eval mediant (-3/4 : ℚ) (2/7 : ℚ)         -- -1/11


-- ============================================================
-- Exercise 6
-- Problem (restated):
-- Define a function `rep (c : Char) (n : ℕ)` that evaluates to the string
-- consisting of `n` copies of `c`.
--
-- Textual explanation:
-- - The definition is by recursion on `n`.
-- - Base case: `n = 0` returns the empty string `""`.
-- - Step: `n+1` appends one more `c` to the result for `n`.
-- - `String.push` appends a character to the end of a string.
-- ============================================================

def rep (c : Char) : ℕ → String
  | 0     => ""
  | n+1   => (rep c n).push c

#check rep

-- tests
#eval rep 'a' 0
#eval rep 'a' 5
#eval rep '🙂' 3

-- ============================================================
-- Exercise 7
-- Problem (restated):
-- Define a function `rev_list` that reverses a list of any type.
--
-- Textual explanation:
-- - A tail-recursive helper `revAux` carries an accumulator `acc`.
-- - Each step moves the head of the input list onto the front of `acc`.
-- - When the input list is empty, the accumulator is the reversed list.
-- ============================================================

def rev_list {α : Type} (L : List α) : List α :=
  let rec revAux : List α → List α → List α
    | [], acc => acc
    | x :: xs, acc => revAux xs (x :: acc)
  revAux L []

#check rev_list
#eval rev_list ([1,2,3,4,5] : List ℕ)          -- [5,4,3,2,1]
#eval rev_list (["u","w","x"] : List String)   -- ["x","w","u"]


-- ============================================================
-- Exercise 8
-- Problem (restated):
-- Given a comparison function `lt : α → α → Bool`,
-- define insertion sort on lists of any type `α`.
--
-- Textual explanation:
-- - `insertBy lt x L` inserts `x` into a list `L` assumed to be sorted
--   according to `lt`.
-- - `insertionSortBy lt` sorts by recursively sorting the tail and then
--   inserting the head into the sorted tail.
-- ============================================================


def insertionSortBy {α : Type} (lt : α → α → Bool) : List α → List α := by
  let rec insertBy {α : Type} (lt : α → α → Bool) (x : α) : List α → List α
    | [] => [x]
    | y :: ys =>
        if lt x y
        then x :: y :: ys
        else y :: insertBy lt x ys
  fun
  | [] => []
  | x :: xs => insertBy lt x (insertionSortBy lt xs)

#check insertionSortBy
#eval insertionSortBy (fun a b : ℕ => decide (a ≤ b)) [7,3,5,2,9,1]   -- [1,2,3,5,7,9]


-- ============================================================
-- Exercise 9
-- Problem (restated):
-- Test the polymorphic insertion sort on `String`, using the
-- alphabetical ordering defined by:
--   def str_cmp (a b : String) : Bool := decide (a ≤ b)
--
-- Textual explanation:
-- - `decide (a ≤ b)` produces a `Bool` by deciding the proposition `a ≤ b`.
-- - `insertionSortBy str_cmp` then sorts using that boolean comparator.
-- ============================================================

def str_cmp (a b : String) : Bool :=
  decide (a ≤ b)

#eval insertionSortBy str_cmp ["z", "aa", "b", "a", "az", ""]   -- ["", "a", "aa", "az", "b", "z"]
