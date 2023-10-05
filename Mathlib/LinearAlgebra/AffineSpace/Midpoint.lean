/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv

#align_import linear_algebra.affine_space.midpoint from "leanprover-community/mathlib"@"2196ab363eb097c008d4497125e0dde23fb36db2"

/-!
# Midpoint of a segment

## Main definitions

* `midpoint R x y`: midpoint of the segment `[x, y]`. We define it for `x` and `y`
  in a module over a ring `R` with invertible `2`.
* `AddMonoidHom.ofMapMidpoint`: construct an `AddMonoidHom` given a map `f` such that
  `f` sends zero to zero and midpoints to midpoints.

## Main theorems

* `midpoint_eq_iff`: `z` is the midpoint of `[x, y]` if and only if `x + y = z + z`,
* `midpoint_unique`: `midpoint R x y` does not depend on `R`;
* `midpoint x y` is linear both in `x` and `y`;
* `pointReflection_midpoint_left`, `pointReflection_midpoint_right`:
  `Equiv.pointReflection (midpoint R x y)` swaps `x` and `y`.

We do not mark most lemmas as `@[simp]` because it is hard to tell which side is simpler.

## Tags

midpoint, AddMonoidHom
-/

open AffineMap AffineEquiv

section

variable (R : Type*) {V V' P P' : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup V]
  [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V'] [AddTorsor V' P']

/-- `midpoint x y` is the midpoint of the segment `[x, y]`. -/
def midpoint (x y : P) : P :=
  lineMap x y (⅟ 2 : R)
#align midpoint midpoint

variable {R} {x y z : P}

@[simp]
theorem AffineMap.map_midpoint (f : P →ᵃ[R] P') (a b : P) :
    f (midpoint R a b) = midpoint R (f a) (f b) :=
  f.apply_lineMap a b _
#align affine_map.map_midpoint AffineMap.map_midpoint

@[simp]
theorem AffineEquiv.map_midpoint (f : P ≃ᵃ[R] P') (a b : P) :
    f (midpoint R a b) = midpoint R (f a) (f b) :=
  f.apply_lineMap a b _
#align affine_equiv.map_midpoint AffineEquiv.map_midpoint

theorem AffineEquiv.pointReflection_midpoint_left (x y : P) :
    pointReflection R (midpoint R x y) x = y := by
  rw [midpoint]; rw [pointReflection_apply]; rw [lineMap_apply]; rw [vadd_vsub]; rw [vadd_vadd]; rw [← add_smul]; rw [← two_mul]; rw [mul_invOf_self]; rw [one_smul]; rw [vsub_vadd]
#align affine_equiv.point_reflection_midpoint_left AffineEquiv.pointReflection_midpoint_left

@[simp] -- Porting note: added variant with `Equiv.pointReflection` for `simp`
theorem Equiv.pointReflection_midpoint_left (x y : P) :
    (Equiv.pointReflection (midpoint R x y)) x = y := by
  rw [midpoint]; rw [pointReflection_apply]; rw [lineMap_apply]; rw [vadd_vsub]; rw [vadd_vadd]; rw [← add_smul]; rw [← two_mul]; rw [mul_invOf_self]; rw [one_smul]; rw [vsub_vadd]

theorem midpoint_comm (x y : P) : midpoint R x y = midpoint R y x := by
  rw [midpoint]; rw [← lineMap_apply_one_sub]; rw [one_sub_invOf_two]; rw [midpoint]
#align midpoint_comm midpoint_comm

theorem AffineEquiv.pointReflection_midpoint_right (x y : P) :
    pointReflection R (midpoint R x y) y = x := by
  rw [midpoint_comm]; rw [AffineEquiv.pointReflection_midpoint_left]
#align affine_equiv.point_reflection_midpoint_right AffineEquiv.pointReflection_midpoint_right

@[simp] -- Porting note: added variant with `Equiv.pointReflection` for `simp`
theorem Equiv.pointReflection_midpoint_right (x y : P) :
    (Equiv.pointReflection (midpoint R x y)) y = x := by
  rw [midpoint_comm]; rw [Equiv.pointReflection_midpoint_left]

theorem midpoint_vsub_midpoint (p₁ p₂ p₃ p₄ : P) :
    midpoint R p₁ p₂ -ᵥ midpoint R p₃ p₄ = midpoint R (p₁ -ᵥ p₃) (p₂ -ᵥ p₄) :=
  lineMap_vsub_lineMap _ _ _ _ _
#align midpoint_vsub_midpoint midpoint_vsub_midpoint

theorem midpoint_vadd_midpoint (v v' : V) (p p' : P) :
    midpoint R v v' +ᵥ midpoint R p p' = midpoint R (v +ᵥ p) (v' +ᵥ p') :=
  lineMap_vadd_lineMap _ _ _ _ _
#align midpoint_vadd_midpoint midpoint_vadd_midpoint

theorem midpoint_eq_iff {x y z : P} : midpoint R x y = z ↔ pointReflection R z x = y :=
  eq_comm.trans
    ((injective_pointReflection_left_of_module R x).eq_iff'
        (AffineEquiv.pointReflection_midpoint_left x y)).symm
#align midpoint_eq_iff midpoint_eq_iff

@[simp]
theorem midpoint_pointReflection_left (x y : P) :
    midpoint R (Equiv.pointReflection x y) y = x :=
  midpoint_eq_iff.2 <| Equiv.pointReflection_involutive _ _

@[simp]
theorem midpoint_pointReflection_right (x y : P) :
    midpoint R y (Equiv.pointReflection x y) = x :=
  midpoint_eq_iff.2 rfl

@[simp]
theorem midpoint_vsub_left (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₁ = (⅟ 2 : R) • (p₂ -ᵥ p₁) :=
  lineMap_vsub_left _ _ _
#align midpoint_vsub_left midpoint_vsub_left

@[simp]
theorem midpoint_vsub_right (p₁ p₂ : P) : midpoint R p₁ p₂ -ᵥ p₂ = (⅟ 2 : R) • (p₁ -ᵥ p₂) := by
  rw [midpoint_comm]; rw [midpoint_vsub_left]
#align midpoint_vsub_right midpoint_vsub_right

@[simp]
theorem left_vsub_midpoint (p₁ p₂ : P) : p₁ -ᵥ midpoint R p₁ p₂ = (⅟ 2 : R) • (p₁ -ᵥ p₂) :=
  left_vsub_lineMap _ _ _
#align left_vsub_midpoint left_vsub_midpoint

@[simp]
theorem right_vsub_midpoint (p₁ p₂ : P) : p₂ -ᵥ midpoint R p₁ p₂ = (⅟ 2 : R) • (p₂ -ᵥ p₁) := by
  rw [midpoint_comm]; rw [left_vsub_midpoint]
#align right_vsub_midpoint right_vsub_midpoint

theorem midpoint_vsub (p₁ p₂ p : P) :
    midpoint R p₁ p₂ -ᵥ p = (⅟ 2 : R) • (p₁ -ᵥ p) + (⅟ 2 : R) • (p₂ -ᵥ p) := by
  rw [← vsub_sub_vsub_cancel_right p₁ p p₂]; rw [smul_sub]; rw [sub_eq_add_neg]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [add_assoc]; rw [invOf_two_smul_add_invOf_two_smul]; rw [← vadd_vsub_assoc]; rw [midpoint_comm]; rw [midpoint]; rw [lineMap_apply]
#align midpoint_vsub midpoint_vsub

theorem vsub_midpoint (p₁ p₂ p : P) :
    p -ᵥ midpoint R p₁ p₂ = (⅟ 2 : R) • (p -ᵥ p₁) + (⅟ 2 : R) • (p -ᵥ p₂) := by
  rw [← neg_vsub_eq_vsub_rev]; rw [midpoint_vsub]; rw [neg_add]; rw [← smul_neg]; rw [← smul_neg]; rw [neg_vsub_eq_vsub_rev]; rw [neg_vsub_eq_vsub_rev]
#align vsub_midpoint vsub_midpoint

@[simp]
theorem midpoint_sub_left (v₁ v₂ : V) : midpoint R v₁ v₂ - v₁ = (⅟ 2 : R) • (v₂ - v₁) :=
  midpoint_vsub_left v₁ v₂
#align midpoint_sub_left midpoint_sub_left

@[simp]
theorem midpoint_sub_right (v₁ v₂ : V) : midpoint R v₁ v₂ - v₂ = (⅟ 2 : R) • (v₁ - v₂) :=
  midpoint_vsub_right v₁ v₂
#align midpoint_sub_right midpoint_sub_right

@[simp]
theorem left_sub_midpoint (v₁ v₂ : V) : v₁ - midpoint R v₁ v₂ = (⅟ 2 : R) • (v₁ - v₂) :=
  left_vsub_midpoint v₁ v₂
#align left_sub_midpoint left_sub_midpoint

@[simp]
theorem right_sub_midpoint (v₁ v₂ : V) : v₂ - midpoint R v₁ v₂ = (⅟ 2 : R) • (v₂ - v₁) :=
  right_vsub_midpoint v₁ v₂
#align right_sub_midpoint right_sub_midpoint

variable (R)

@[simp]
theorem midpoint_eq_left_iff {x y : P} : midpoint R x y = x ↔ x = y := by
  rw [midpoint_eq_iff]; rw [pointReflection_self]
#align midpoint_eq_left_iff midpoint_eq_left_iff

@[simp]
theorem left_eq_midpoint_iff {x y : P} : x = midpoint R x y ↔ x = y := by
  rw [eq_comm]; rw [midpoint_eq_left_iff]
#align left_eq_midpoint_iff left_eq_midpoint_iff

@[simp]
theorem midpoint_eq_right_iff {x y : P} : midpoint R x y = y ↔ x = y := by
  rw [midpoint_comm]; rw [midpoint_eq_left_iff]; rw [eq_comm]
#align midpoint_eq_right_iff midpoint_eq_right_iff

@[simp]
theorem right_eq_midpoint_iff {x y : P} : y = midpoint R x y ↔ x = y := by
  rw [eq_comm]; rw [midpoint_eq_right_iff]
#align right_eq_midpoint_iff right_eq_midpoint_iff

theorem midpoint_eq_midpoint_iff_vsub_eq_vsub {x x' y y' : P} :
    midpoint R x y = midpoint R x' y' ↔ x -ᵥ x' = y' -ᵥ y := by
  rw [← @vsub_eq_zero_iff_eq V]; rw [midpoint_vsub_midpoint]; rw [midpoint_eq_iff]; rw [pointReflection_apply]; rw [vsub_eq_sub]; rw [zero_sub]; rw [vadd_eq_add]; rw [add_zero]; rw [neg_eq_iff_eq_neg]; rw [neg_vsub_eq_vsub_rev]
#align midpoint_eq_midpoint_iff_vsub_eq_vsub midpoint_eq_midpoint_iff_vsub_eq_vsub

theorem midpoint_eq_iff' {x y z : P} : midpoint R x y = z ↔ Equiv.pointReflection z x = y :=
  midpoint_eq_iff
#align midpoint_eq_iff' midpoint_eq_iff'

/-- `midpoint` does not depend on the ring `R`. -/
theorem midpoint_unique (R' : Type*) [Ring R'] [Invertible (2 : R')] [Module R' V] (x y : P) :
    midpoint R x y = midpoint R' x y :=
  (midpoint_eq_iff' R).2 <| (midpoint_eq_iff' R').1 rfl
#align midpoint_unique midpoint_unique

@[simp]
theorem midpoint_self (x : P) : midpoint R x x = x :=
  lineMap_same_apply _ _
#align midpoint_self midpoint_self

@[simp]
theorem midpoint_add_self (x y : V) : midpoint R x y + midpoint R x y = x + y :=
  calc
    midpoint R x y +ᵥ midpoint R x y = midpoint R x y +ᵥ midpoint R y x := by rw [midpoint_comm]
    _ = x + y := by rw [midpoint_vadd_midpoint, vadd_eq_add, vadd_eq_add, add_comm, midpoint_self]
#align midpoint_add_self midpoint_add_self

theorem midpoint_zero_add (x y : V) : midpoint R 0 (x + y) = midpoint R x y :=
  (midpoint_eq_midpoint_iff_vsub_eq_vsub R).2 <| by simp [sub_add_eq_sub_sub_swap]
#align midpoint_zero_add midpoint_zero_add

theorem midpoint_eq_smul_add (x y : V) : midpoint R x y = (⅟ 2 : R) • (x + y) := by
  rw [midpoint_eq_iff]; rw [pointReflection_apply]; rw [vsub_eq_sub]; rw [vadd_eq_add]; rw [sub_add_eq_add_sub]; rw [←
    two_smul R]; rw [smul_smul]; rw [mul_invOf_self]; rw [one_smul]; rw [add_sub_cancel']
#align midpoint_eq_smul_add midpoint_eq_smul_add

@[simp]
theorem midpoint_self_neg (x : V) : midpoint R x (-x) = 0 := by
  rw [midpoint_eq_smul_add]; rw [add_neg_self]; rw [smul_zero]
#align midpoint_self_neg midpoint_self_neg

@[simp]
theorem midpoint_neg_self (x : V) : midpoint R (-x) x = 0 := by simpa using midpoint_self_neg R (-x)
#align midpoint_neg_self midpoint_neg_self

@[simp]
theorem midpoint_sub_add (x y : V) : midpoint R (x - y) (x + y) = x := by
  rw [sub_eq_add_neg]; rw [← vadd_eq_add]; rw [← vadd_eq_add]; rw [← midpoint_vadd_midpoint]; simp
#align midpoint_sub_add midpoint_sub_add

@[simp]
theorem midpoint_add_sub (x y : V) : midpoint R (x + y) (x - y) = x := by
  rw [midpoint_comm]; simp
#align midpoint_add_sub midpoint_add_sub

end

namespace AddMonoidHom

variable (R R' : Type*) {E F : Type*} [Ring R] [Invertible (2 : R)] [AddCommGroup E] [Module R E]
  [Ring R'] [Invertible (2 : R')] [AddCommGroup F] [Module R' F]

/-- A map `f : E → F` sending zero to zero and midpoints to midpoints is an `AddMonoidHom`. -/
def ofMapMidpoint (f : E → F) (h0 : f 0 = 0)
    (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) : E →+ F
    where
  toFun := f
  map_zero' := h0
  map_add' x y :=
    calc
      f (x + y) = f 0 + f (x + y) := by rw [h0, zero_add]
      _ = midpoint R' (f 0) (f (x + y)) + midpoint R' (f 0) (f (x + y)) :=
        (midpoint_add_self _ _ _).symm
      _ = f (midpoint R x y) + f (midpoint R x y) := by rw [← hm, midpoint_zero_add]
      _ = f x + f y := by rw [hm, midpoint_add_self]
#align add_monoid_hom.of_map_midpoint AddMonoidHom.ofMapMidpoint

@[simp]
theorem coe_ofMapMidpoint (f : E → F) (h0 : f 0 = 0)
    (hm : ∀ x y, f (midpoint R x y) = midpoint R' (f x) (f y)) :
    ⇑(ofMapMidpoint R R' f h0 hm) = f :=
  rfl
#align add_monoid_hom.coe_of_map_midpoint AddMonoidHom.coe_ofMapMidpoint

end AddMonoidHom
