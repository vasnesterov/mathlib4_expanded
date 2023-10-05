/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

#align_import linear_algebra.quadratic_form.prod from "leanprover-community/mathlib"@"9b2755b951bc323c962bd072cd447b375cf58101"

/-! # Quadratic form on product and pi types

## Main definitions

* `QuadraticForm.prod Q₁ Q₂`: the quadratic form constructed elementwise on a product
* `QuadraticForm.pi Q`: the quadratic form constructed elementwise on a pi type

## Main results

* `QuadraticForm.Equivalent.prod`, `QuadraticForm.Equivalent.pi`: quadratic forms are equivalent
  if their components are equivalent
* `QuadraticForm.nonneg_prod_iff`, `QuadraticForm.nonneg_pi_iff`: quadratic forms are positive-
  semidefinite if and only if their components are positive-semidefinite.
* `QuadraticForm.posDef_prod_iff`, `QuadraticForm.posDef_pi_iff`: quadratic forms are positive-
  definite if and only if their components are positive-definite.

## Implementation notes

Many of the lemmas in this file could be generalized into results about sums of positive and
non-negative elements, and would generalize to any map `Q` where `Q 0 = 0`, not just quadratic
forms specifically.

-/


universe u v w

variable {ι : Type*} {R : Type*} {M₁ M₂ N₁ N₂ : Type*} {Mᵢ Nᵢ : ι → Type*}

variable [Semiring R]

variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid N₁] [AddCommMonoid N₂]

variable [Module R M₁] [Module R M₂] [Module R N₁] [Module R N₂]

variable [∀ i, AddCommMonoid (Mᵢ i)] [∀ i, AddCommMonoid (Nᵢ i)]

variable [∀ i, Module R (Mᵢ i)] [∀ i, Module R (Nᵢ i)]

namespace QuadraticForm

/-- Construct a quadratic form on a product of two modules from the quadratic form on each module.
-/
@[simps!]
def prod (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) : QuadraticForm R (M₁ × M₂) :=
  Q₁.comp (LinearMap.fst _ _ _) + Q₂.comp (LinearMap.snd _ _ _)
#align quadratic_form.prod QuadraticForm.prod

/-- An isometry between quadratic forms generated by `QuadraticForm.prod` can be constructed
from a pair of isometries between the left and right parts. -/
@[simps toLinearEquiv]
def IsometryEquiv.prod
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₁' : QuadraticForm R N₁} {Q₂' : QuadraticForm R N₂}
    (e₁ : Q₁.IsometryEquiv Q₁') (e₂ : Q₂.IsometryEquiv Q₂') :
    (Q₁.prod Q₂).IsometryEquiv (Q₁'.prod Q₂') where
  map_app' x := congr_arg₂ (· + ·) (e₁.map_app x.1) (e₂.map_app x.2)
  toLinearEquiv := LinearEquiv.prod e₁.toLinearEquiv e₂.toLinearEquiv
#align quadratic_form.isometry.prod QuadraticForm.IsometryEquiv.prod

theorem Equivalent.prod {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    {Q₁' : QuadraticForm R N₁} {Q₂' : QuadraticForm R N₂} (e₁ : Q₁.Equivalent Q₁')
    (e₂ : Q₂.Equivalent Q₂') : (Q₁.prod Q₂).Equivalent (Q₁'.prod Q₂') :=
  Nonempty.map2 IsometryEquiv.prod e₁ e₂
#align quadratic_form.equivalent.prod QuadraticForm.Equivalent.prod

/-- `LinearEquiv.prodComm` is isometric. -/
@[simps!]
def IsometryEquiv.prodComm (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.prod Q₂).IsometryEquiv (Q₂.prod Q₁) where
  toLinearEquiv := LinearEquiv.prodComm _ _ _
  map_app' _ := add_comm _ _

/-- `LinearEquiv.prodProdProdComm` is isometric. -/
@[simps!]
def IsometryEquiv.prodProdProdComm
    (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)
    (Q₃ : QuadraticForm R N₁) (Q₄ : QuadraticForm R N₂) :
    ((Q₁.prod Q₂).prod (Q₃.prod Q₄)).IsometryEquiv ((Q₁.prod Q₃).prod (Q₂.prod Q₄)) where
  toLinearEquiv := LinearEquiv.prodProdProdComm _ _ _ _ _
  map_app' _ := add_add_add_comm _ _ _ _

/-- If a product is anisotropic then its components must be. The converse is not true. -/
theorem anisotropic_of_prod {R} [OrderedRing R] [Module R M₁] [Module R M₂]
    {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (h : (Q₁.prod Q₂).Anisotropic) :
    Q₁.Anisotropic ∧ Q₂.Anisotropic := by
  simp_rw [Anisotropic, prod_apply, Prod.forall, Prod.mk_eq_zero] at h
  constructor
  · intro x hx
    refine' (h x 0 _).1
    rw [hx]; rw [zero_add]; rw [map_zero]
  · intro x hx
    refine' (h 0 x _).2
    rw [hx]; rw [add_zero]; rw [map_zero]
#align quadratic_form.anisotropic_of_prod QuadraticForm.anisotropic_of_prod

theorem nonneg_prod_iff {R} [OrderedRing R] [Module R M₁] [Module R M₂] {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} : (∀ x, 0 ≤ (Q₁.prod Q₂) x) ↔ (∀ x, 0 ≤ Q₁ x) ∧ ∀ x, 0 ≤ Q₂ x := by
  simp_rw [Prod.forall, prod_apply]
  constructor
  · intro h
    constructor
    · intro x; simpa only [add_zero, map_zero] using h x 0
    · intro x; simpa only [zero_add, map_zero] using h 0 x
  · rintro ⟨h₁, h₂⟩ x₁ x₂
    exact add_nonneg (h₁ x₁) (h₂ x₂)
#align quadratic_form.nonneg_prod_iff QuadraticForm.nonneg_prod_iff

theorem posDef_prod_iff {R} [OrderedRing R] [Module R M₁] [Module R M₂] {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} : (Q₁.prod Q₂).PosDef ↔ Q₁.PosDef ∧ Q₂.PosDef := by
  simp_rw [posDef_iff_nonneg, nonneg_prod_iff]
  constructor
  · rintro ⟨⟨hle₁, hle₂⟩, ha⟩
    obtain ⟨ha₁, ha₂⟩ := anisotropic_of_prod ha
    refine' ⟨⟨hle₁, ha₁⟩, ⟨hle₂, ha₂⟩⟩
  · rintro ⟨⟨hle₁, ha₁⟩, ⟨hle₂, ha₂⟩⟩
    refine' ⟨⟨hle₁, hle₂⟩, _⟩
    rintro ⟨x₁, x₂⟩ (hx : Q₁ x₁ + Q₂ x₂ = 0)
    rw [add_eq_zero_iff' (hle₁ x₁) (hle₂ x₂)] at hx; rw [ha₁.eq_zero_iff] at hx; rw [ha₂.eq_zero_iff] at hx
    rwa [Prod.mk_eq_zero]
#align quadratic_form.pos_def_prod_iff QuadraticForm.posDef_prod_iff

theorem PosDef.prod {R} [OrderedRing R] [Module R M₁] [Module R M₂] {Q₁ : QuadraticForm R M₁}
    {Q₂ : QuadraticForm R M₂} (h₁ : Q₁.PosDef) (h₂ : Q₂.PosDef) : (Q₁.prod Q₂).PosDef :=
  posDef_prod_iff.mpr ⟨h₁, h₂⟩
#align quadratic_form.pos_def.prod QuadraticForm.PosDef.prod

open scoped BigOperators

/-- Construct a quadratic form on a family of modules from the quadratic form on each module. -/
def pi [Fintype ι] (Q : ∀ i, QuadraticForm R (Mᵢ i)) : QuadraticForm R (∀ i, Mᵢ i) :=
  ∑ i, (Q i).comp (LinearMap.proj i : _ →ₗ[R] Mᵢ i)
#align quadratic_form.pi QuadraticForm.pi

@[simp]
theorem pi_apply [Fintype ι] (Q : ∀ i, QuadraticForm R (Mᵢ i)) (x : ∀ i, Mᵢ i) :
    pi Q x = ∑ i, Q i (x i) :=
  sum_apply _ _ _
#align quadratic_form.pi_apply QuadraticForm.pi_apply

/-- An isometry between quadratic forms generated by `QuadraticForm.pi` can be constructed
from a pair of isometries between the left and right parts. -/
@[simps toLinearEquiv]
def IsometryEquiv.pi [Fintype ι]
    {Q : ∀ i, QuadraticForm R (Mᵢ i)} {Q' : ∀ i, QuadraticForm R (Nᵢ i)}
    (e : ∀ i, (Q i).IsometryEquiv (Q' i)) : (pi Q).IsometryEquiv (pi Q') where
  map_app' x := by
    simp only [pi_apply, LinearEquiv.piCongrRight, LinearEquiv.toFun_eq_coe,
      IsometryEquiv.coe_toLinearEquiv, IsometryEquiv.map_app]
  toLinearEquiv := LinearEquiv.piCongrRight fun i => (e i : Mᵢ i ≃ₗ[R] Nᵢ i)
#align quadratic_form.isometry.pi QuadraticForm.IsometryEquiv.pi

theorem Equivalent.pi [Fintype ι] {Q : ∀ i, QuadraticForm R (Mᵢ i)}
    {Q' : ∀ i, QuadraticForm R (Nᵢ i)} (e : ∀ i, (Q i).Equivalent (Q' i)) :
    (pi Q).Equivalent (pi Q') :=
  ⟨IsometryEquiv.pi fun i => Classical.choice (e i)⟩
#align quadratic_form.equivalent.pi QuadraticForm.Equivalent.pi

/-- If a family is anisotropic then its components must be. The converse is not true. -/
theorem anisotropic_of_pi [Fintype ι] {R} [OrderedRing R] [∀ i, Module R (Mᵢ i)]
    {Q : ∀ i, QuadraticForm R (Mᵢ i)} (h : (pi Q).Anisotropic) : ∀ i, (Q i).Anisotropic := by
  simp_rw [Anisotropic, pi_apply, Function.funext_iff, Pi.zero_apply] at h
  intro i x hx
  classical
  have := h (Pi.single i x) ?_ i
  · rw [Pi.single_eq_same] at this
    exact this
  apply Finset.sum_eq_zero
  intro j _
  by_cases hji : j = i
  · subst hji; rw [Pi.single_eq_same]; rw [hx]
  · rw [Pi.single_eq_of_ne hji, map_zero]
#align quadratic_form.anisotropic_of_pi QuadraticForm.anisotropic_of_pi

theorem nonneg_pi_iff [Fintype ι] {R} [OrderedRing R] [∀ i, Module R (Mᵢ i)]
    {Q : ∀ i, QuadraticForm R (Mᵢ i)} : (∀ x, 0 ≤ pi Q x) ↔ ∀ i x, 0 ≤ Q i x := by
  simp_rw [pi, sum_apply, comp_apply, LinearMap.proj_apply]
  constructor
  -- TODO: does this generalize to a useful lemma independent of `QuadraticForm`?
  · intro h i x
    classical
    convert h (Pi.single i x) using 1
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) fun j _ hji => ?_]; rw [Pi.single_eq_same]
    rw [Pi.single_eq_of_ne hji]; rw [map_zero]
  · rintro h x
    exact Finset.sum_nonneg fun i _ => h i (x i)
#align quadratic_form.nonneg_pi_iff QuadraticForm.nonneg_pi_iff

theorem posDef_pi_iff [Fintype ι] {R} [OrderedRing R] [∀ i, Module R (Mᵢ i)]
    {Q : ∀ i, QuadraticForm R (Mᵢ i)} : (pi Q).PosDef ↔ ∀ i, (Q i).PosDef := by
  simp_rw [posDef_iff_nonneg, nonneg_pi_iff]
  constructor
  · rintro ⟨hle, ha⟩
    intro i
    exact ⟨hle i, anisotropic_of_pi ha i⟩
  · intro h
    refine' ⟨fun i => (h i).1, fun x hx => funext fun i => (h i).2 _ _⟩
    rw [pi_apply] at hx; rw [Finset.sum_eq_zero_iff_of_nonneg fun j _ => ?_] at hx
    · exact hx _ (Finset.mem_univ _)
    exact (h j).1 _
#align quadratic_form.pos_def_pi_iff QuadraticForm.posDef_pi_iff

end QuadraticForm
