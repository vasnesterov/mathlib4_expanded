/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Topology.Instances.TrivSqZeroExt

#align_import analysis.normed_space.triv_sq_zero_ext from "leanprover-community/mathlib"@"88a563b158f59f2983cfad685664da95502e8cdd"

/-!
# Results on `TrivSqZeroExt R M` related to the norm

For now, this file contains results about `exp` for this type.

## Main results

* `TrivSqZeroExt.fst_exp`
* `TrivSqZeroExt.snd_exp`
* `TrivSqZeroExt.exp_inl`
* `TrivSqZeroExt.exp_inr`

## TODO

* Actually define a sensible norm on `TrivSqZeroExt R M`, so that we have access to lemmas
  like `exp_add`.
* Generalize more of these results to non-commutative `R`. In principle, under sufficient conditions
  we should expect
 `(exp 𝕜 x).snd = ∫ t in 0..1, exp 𝕜 (t • x.fst) • op (exp 𝕜 ((1 - t) • x.fst)) • x.snd`
  ([Physics.SE](https://physics.stackexchange.com/a/41671/185147), and
  https://link.springer.com/chapter/10.1007/978-3-540-44953-9_2).

-/


variable (𝕜 : Type*) {R M : Type*}

local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

section Topology

variable [TopologicalSpace R] [TopologicalSpace M]

/-- If `exp R x.fst` converges to `e` then `(exp R x).fst` converges to `e`. -/
theorem hasSum_fst_expSeries [Field 𝕜] [Ring R] [AddCommGroup M] [Algebra 𝕜 R] [Module R M]
    [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] [Module 𝕜 M] [IsScalarTower 𝕜 R M]
    [IsScalarTower 𝕜 Rᵐᵒᵖ M] [TopologicalRing R] [TopologicalAddGroup M] [ContinuousSMul R M]
    [ContinuousSMul Rᵐᵒᵖ M] (x : tsze R M) {e : R}
    (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => fst (expSeries 𝕜 (tsze R M) n fun _ => x)) e := by
  simpa [expSeries_apply_eq] using h
#align triv_sq_zero_ext.has_sum_fst_exp_series TrivSqZeroExt.hasSum_fst_expSeries

/-- If `exp R x.fst` converges to `e` then `(exp R x).snd` converges to `e • x.snd`. -/
theorem hasSum_snd_expSeries_of_smul_comm [Field 𝕜] [CharZero 𝕜] [Ring R] [AddCommGroup M]
    [Algebra 𝕜 R] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] [Module 𝕜 M]
    [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M] [TopologicalRing R] [TopologicalAddGroup M]
    [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M] (x : tsze R M)
    (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) {e : R}
    (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => snd (expSeries 𝕜 (tsze R M) n fun _ => x)) (e • x.snd) := by
  simp_rw [expSeries_apply_eq] at *
  conv =>
    congr
    ext n
    rw [snd_smul]; rw [snd_pow_of_smul_comm _ _ hx]; rw [nsmul_eq_smul_cast 𝕜 n]; rw [smul_smul]; rw [inv_mul_eq_div]; rw [←
      inv_div]; rw [← smul_assoc]
  apply HasSum.smul_const
  rw [← hasSum_nat_add_iff' 1]
  rw [Finset.range_one]; rw [Finset.sum_singleton]; rw [Nat.cast_zero]; rw [div_zero]; rw [inv_zero]; rw [zero_smul]; rw [sub_zero]
  simp_rw [← Nat.succ_eq_add_one, Nat.pred_succ, Nat.factorial_succ, Nat.cast_mul, ←
    Nat.succ_eq_add_one,
    mul_div_cancel_left _ ((@Nat.cast_ne_zero 𝕜 _ _ _).mpr <| Nat.succ_ne_zero _)]
  exact h
#align triv_sq_zero_ext.has_sum_snd_exp_series_of_smul_comm TrivSqZeroExt.hasSum_snd_expSeries_of_smul_comm

/-- If `exp R x.fst` converges to `e` then `exp R x` converges to `inl e + inr (e • x.snd)`. -/
theorem hasSum_expSeries_of_smul_comm [Field 𝕜] [CharZero 𝕜] [Ring R] [AddCommGroup M] [Algebra 𝕜 R]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] [Module 𝕜 M] [IsScalarTower 𝕜 R M]
    [IsScalarTower 𝕜 Rᵐᵒᵖ M] [TopologicalRing R] [TopologicalAddGroup M] [ContinuousSMul R M]
    [ContinuousSMul Rᵐᵒᵖ M] (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd)
    {e : R} (h : HasSum (fun n => expSeries 𝕜 R n fun _ => x.fst) e) :
    HasSum (fun n => expSeries 𝕜 (tsze R M) n fun _ => x) (inl e + inr (e • x.snd)) := by
  simpa only [inl_fst_add_inr_snd_eq] using
    (hasSum_inl _ <| hasSum_fst_expSeries 𝕜 x h).add
      (hasSum_inr _ <| hasSum_snd_expSeries_of_smul_comm 𝕜 x hx h)
#align triv_sq_zero_ext.has_sum_exp_series_of_smul_comm TrivSqZeroExt.hasSum_expSeries_of_smul_comm

end Topology

section NormedRing

variable [IsROrC 𝕜] [NormedRing R] [AddCommGroup M]

variable [NormedAlgebra 𝕜 R] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

variable [Module 𝕜 M] [IsScalarTower 𝕜 R M] [IsScalarTower 𝕜 Rᵐᵒᵖ M]

variable [TopologicalSpace M] [TopologicalRing R]

variable [TopologicalAddGroup M] [ContinuousSMul R M] [ContinuousSMul Rᵐᵒᵖ M]

variable [CompleteSpace R] [T2Space R] [T2Space M]

theorem exp_def_of_smul_comm (x : tsze R M) (hx : MulOpposite.op x.fst • x.snd = x.fst • x.snd) :
    exp 𝕜 x = inl (exp 𝕜 x.fst) + inr (exp 𝕜 x.fst • x.snd) := by
  simp_rw [exp, FormalMultilinearSeries.sum]
  refine' (hasSum_expSeries_of_smul_comm 𝕜 x hx _).tsum_eq
  exact expSeries_hasSum_exp _
#align triv_sq_zero_ext.exp_def_of_smul_comm TrivSqZeroExt.exp_def_of_smul_comm

@[simp]
theorem exp_inl (x : R) : exp 𝕜 (inl x : tsze R M) = inl (exp 𝕜 x) := by
  rw [exp_def_of_smul_comm]; rw [snd_inl]; rw [fst_inl]; rw [smul_zero]; rw [inr_zero]; rw [add_zero]
  · rw [snd_inl, fst_inl, smul_zero, smul_zero]
#align triv_sq_zero_ext.exp_inl TrivSqZeroExt.exp_inl

@[simp]
theorem exp_inr (m : M) : exp 𝕜 (inr m : tsze R M) = 1 + inr m := by
  rw [exp_def_of_smul_comm]; rw [snd_inr]; rw [fst_inr]; rw [exp_zero]; rw [one_smul]; rw [inl_one]
  · rw [snd_inr, fst_inr, MulOpposite.op_zero, zero_smul, zero_smul]
#align triv_sq_zero_ext.exp_inr TrivSqZeroExt.exp_inr

end NormedRing

section NormedCommRing

variable [IsROrC 𝕜] [NormedCommRing R] [AddCommGroup M]

variable [NormedAlgebra 𝕜 R] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

variable [Module 𝕜 M] [IsScalarTower 𝕜 R M]

variable [TopologicalSpace M] [TopologicalRing R]

variable [TopologicalAddGroup M] [ContinuousSMul R M]

variable [CompleteSpace R] [T2Space R] [T2Space M]

theorem exp_def (x : tsze R M) : exp 𝕜 x = inl (exp 𝕜 x.fst) + inr (exp 𝕜 x.fst • x.snd) :=
  exp_def_of_smul_comm 𝕜 x (op_smul_eq_smul _ _)
#align triv_sq_zero_ext.exp_def TrivSqZeroExt.exp_def

@[simp]
theorem fst_exp (x : tsze R M) : fst (exp 𝕜 x) = exp 𝕜 x.fst := by
  rw [exp_def]; rw [fst_add]; rw [fst_inl]; rw [fst_inr]; rw [add_zero]
#align triv_sq_zero_ext.fst_exp TrivSqZeroExt.fst_exp

@[simp]
theorem snd_exp (x : tsze R M) : snd (exp 𝕜 x) = exp 𝕜 x.fst • x.snd := by
  rw [exp_def]; rw [snd_add]; rw [snd_inl]; rw [snd_inr]; rw [zero_add]
#align triv_sq_zero_ext.snd_exp TrivSqZeroExt.snd_exp

/-- Polar form of trivial-square-zero extension. -/
theorem eq_smul_exp_of_invertible (x : tsze R M) [Invertible x.fst] :
    x = x.fst • exp 𝕜 (⅟ x.fst • inr x.snd) := by
  rw [← inr_smul]; rw [exp_inr]; rw [smul_add]; rw [← inl_one]; rw [← inl_smul]; rw [← inr_smul]; rw [smul_eq_mul]; rw [mul_one]; rw [smul_smul]; rw [mul_invOf_self]; rw [one_smul]; rw [inl_fst_add_inr_snd_eq]
#align triv_sq_zero_ext.eq_smul_exp_of_invertible TrivSqZeroExt.eq_smul_exp_of_invertible

end NormedCommRing

section NormedField

variable [IsROrC 𝕜] [NormedField R] [AddCommGroup M]

variable [NormedAlgebra 𝕜 R] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

variable [Module 𝕜 M] [IsScalarTower 𝕜 R M]

variable [TopologicalSpace M] [TopologicalRing R]

variable [TopologicalAddGroup M] [ContinuousSMul R M]

variable [CompleteSpace R] [T2Space R] [T2Space M]

/-- More convenient version of `TrivSqZeroExt.eq_smul_exp_of_invertible` for when `R` is a
field. -/
theorem eq_smul_exp_of_ne_zero (x : tsze R M) (hx : x.fst ≠ 0) :
    x = x.fst • exp 𝕜 (x.fst⁻¹ • inr x.snd) :=
  letI : Invertible x.fst := invertibleOfNonzero hx
  eq_smul_exp_of_invertible _ _
#align triv_sq_zero_ext.eq_smul_exp_of_ne_zero TrivSqZeroExt.eq_smul_exp_of_ne_zero

end NormedField

end TrivSqZeroExt
