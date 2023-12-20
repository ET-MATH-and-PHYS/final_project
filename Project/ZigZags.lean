import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# ZigZags

In this file we define zigzags in an arbitrary category which generalize
the notion of spans and cospans, along with their morphisms,
some general properties, and (co)limits of zig-zag shape.

A zig-zag in a category `C` is a sequence of arrows

A₀ -g₀-> C₀ <-f₀- . . . <-fₙ₋₁- Aₙ

We follow the structure of the file
`Mathlib.CategoryTheory.Limits.Shapes.Pullbacks`
-/

noncomputable section -- Not sure what we need this for yet

open CategoryTheory

namespace CategoryTheory.Limits

universe w v u

/-- A zig-zag shape for any natural number n -/
inductive ZigZag (n : ℕ) where
  | tail (k : Fin (n+1)) : ZigZag n
  | head (l : Fin n) : ZigZag n

variable {n : ℕ}

/-- The type of arrows for the zigzag shape -/
inductive Hom : ZigZag n → ZigZag n → Type w where
  | id : ∀ X, Hom X X
  | term (j : Fin 2) : ∀ l : Fin n, Hom
    (ZigZag.tail ⟨l.1 + j.1, add_lt_add_of_lt_of_le l.2 (Nat.lt_succ.mp j.2)⟩) (ZigZag.head l)
