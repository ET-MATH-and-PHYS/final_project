import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.Tactic
import Mathlib.CategoryTheory.Category.Cat.Limit

/-!
# Double Categories

In this file we define typeclass for (weak) double categories.

A double category `D` consists of
* An object category `D₀`
* An arrow category `D₁`
* A `span` in `Cat`, D₀ <-t- D₁ -s-> D₁
* A morphism of spans `⊙`

          D₁ <-p₁- D₁ ×D₀ D₁ -p₂-> D₁
          ||          |            ||
  D₀ <-t- D₁  - s ->  |D₀  <- t -  D₁ -s-> D₀
  ||                  ⊙                   ||
  ||                  |                    ||
  ||                  ∨                    ||
  D₀ <    t        -  D₁     -     s     > D₀

* A morphism of spans `i`

  D₀ ==== D₀ ==== D₀
  ||      |       ||
  ||      i       ||
  ||      |       ||
  ||      ∨       ||
  D₀ <-t- D₁ -s-> D₀

We use `u` and `v` as universe variables for the objects and arrows of the
object category, and as objects and arrows of the arrow category.
-/

namespace CategoryTheory

universe v u

open Category Iso CategoryTheory.Limits Cat HasLimits

-- variable (X Y Z : Type u) [Category.{v} X] [Category.{v} Y]
--   [Category.{v} Z] (F : (of X) ⟶ (of Z)) (G : (of Y) ⟶ (of Z))

-- #check cospan F G


-- def SrcTgt_obj (D₀ D₁ : Type u) [Category.{v} D₀] [Category.{v} D₁] :
--     WalkingCospan → Cat.{v, u} := fun
--   | .none => of D₀
--   | .some _val => of D₁

-- def SrcTgt_map (D₀ D₁ : Type u) [Category.{v} D₀] [Category.{v} D₁]
--     (src : D₁ ⥤ D₀) (tgt : D₁ ⥤ D₀) {X Y : WalkingCospan} :
--     (X ⟶ Y) → (SrcTgt_obj D₀ D₁ X ⟶ SrcTgt_obj D₀ D₁ Y) := fun
--   | .id X => 𝟭 ((SrcTgt_obj D₀ D₁) X)
--   | .term (.left) => src
--   | .term (.right) => tgt

-- def SrcTgt (D₀ D₁ : Type u) [Category.{v} D₀] [Category.{v} D₁]
--     (src : D₁ ⥤ D₀) (tgt : D₁ ⥤ D₀) :
--     WalkingCospan ⥤ Cat.{v,u} where
--   obj :=  SrcTgt_obj D₀ D₁
--   map := SrcTgt_map D₀ D₁ src tgt
--   map_id := fun
--     | .none => rfl
--     | .some val => rfl
--   map_comp := fun
--     | .id X => by
--       intro g
--       dsimp
--       induction g with
--       | id X => rfl
--       | term j => rfl
--     | .term j => by
--       intro g
--       dsimp
--       cases g with
--       | id X => rfl

-- @[simp]
-- lemma SrcTgt.left (D₀ D₁ : Type u) [Category.{v} D₀] [Category.{v} D₁]
--     (src : D₁ ⥤ D₀) (tgt : D₁ ⥤ D₀) :
--     (SrcTgt D₀ D₁ src tgt).obj WalkingCospan.left = D₁ := rfl

@[simp]
lemma func_assoc_aux {D₀ D₁ : Type u} [Category.{v} D₀] [Category.{v} D₁]
    (f : (of D₁) ⟶ (of D₀)) (g : (of D₀) ⟶ (of D₁))
    (h : (of D₁) ⟶ (of D₀)) (pf : g ≫ h = 𝟙 (of D₀))
    : (f ≫ g) ≫ h = (𝟙 (of D₁)) ≫ f := by
  simp
  rw [pf]
  simp

@[simp]
lemma func_assoc_aux.symm {D₀ D₁ : Type u} [Category.{v} D₀] [Category.{v} D₁]
    (f : (of D₁) ⟶ (of D₀)) (g : (of D₀) ⟶ (of D₁))
    (h : (of D₁) ⟶ (of D₀)) (pf : g ≫ h = 𝟙 (of D₀))
    : (𝟙 (of D₁)) ≫ f = (f ≫ g) ≫ h := by
  simp
  rw [pf]
  simp


-- Intended to be used with explicit universe parameters
/-- In

-/
@[nolint checkUnivs]
class DoubleCategory (D₀ : Type u) (D₁ : Type u) where
  /-- Object category -/
  objCat : Category.{v} D₀
  /-- Arrow category -/
  arrCat : Category.{v} D₁
  /-- Source functor -/
  src : (of D₁) ⟶ (of D₀)
  /-- Target functor -/
  tgt : (of D₁) ⟶ (of D₀)
  /-- Unit -/
  i : (of D₀) ⟶ (of D₁)
  /-- The source of the unit `X` is `X` -/
  src_i : i ⋙ src = 𝟙 (of D₀)
  /-- The target of the unit `X` is `X` -/
  tgt_i : i ⋙ tgt = 𝟙 (of D₀)
  /-- Cone for pullback -/
  pullBack_cone : PullbackCone src tgt
  /-- Proof pullBackCat is a pullback -/
  pullBack_lim : IsLimit (pullBack_cone)
  /-- Horizontal composition functor -/
  hcomp : (of pullBack_cone.pt) ⟶ (of D₁)
  /-- Map of spans condition -/
  hcomp_tgt : pullBack_cone.fst ⋙ tgt = hcomp ⋙ tgt
  hcomp_src : pullBack_cone.snd ⋙ src = hcomp ⋙ src
  /-- Associator -/
  a : () ⟶ ()
  /-- left unitor -/
  ℓ : pullBack_lim.lift (PullbackCone.mk (tgt ≫ i)
    (𝟙 (of D₁)) (func_assoc_aux tgt i src src_i)) ⋙ hcomp
    ⟶ 𝟙 (of D₁)
  /-- right unitor -/
  r : pullBack_lim.lift (PullbackCone.mk (𝟙 (of D₁)) (src ≫ i)
    (func_assoc_aux.symm src i tgt tgt_i)) ⋙ hcomp ⟶ 𝟙 (of D₁)
  /-- globular conditions -/
  a_glob : sorry
  ℓ_glob : sorry -- Need prelim lemma for simplifying domains
