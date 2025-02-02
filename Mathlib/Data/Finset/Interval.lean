/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Finset.LocallyFinite

#align_import data.finset.interval from "leanprover-community/mathlib"@"98e83c3d541c77cdb7da20d79611a780ff8e7d90"

/-!
# Intervals of finsets as finsets

This file provides the `LocallyFiniteOrder` instance for `Finset α` and calculates the cardinality
of finite intervals of finsets.

If `s t : Finset α`, then `Finset.Icc s t` is the finset of finsets which include `s` and are
included in `t`. For example,
`Finset.Icc {0, 1} {0, 1, 2, 3} = {{0, 1}, {0, 1, 2}, {0, 1, 3}, {0, 1, 2, 3}}`
and
`Finset.Icc {0, 1, 2} {0, 1, 3} = {}`.

In addition, this file gives characterizations of monotone and strictly monotone functions
out of `Finset α` in terms of `Finset.insert`
-/


variable {α : Type*}

namespace Finset

section Decidable

variable [DecidableEq α] (s t : Finset α)

instance : LocallyFiniteOrder (Finset α)
    where
  finsetIcc s t := t.powerset.filter ((· ⊆ ·) s)
  finsetIco s t := t.ssubsets.filter ((· ⊆ ·) s)
  finsetIoc s t := t.powerset.filter ((· ⊂ ·) s)
  finsetIoo s t := t.ssubsets.filter ((· ⊂ ·) s)
  finset_mem_Icc s t u := by
    rw [mem_filter]; rw [mem_powerset]
    exact and_comm
  finset_mem_Ico s t u := by
    rw [mem_filter]; rw [mem_ssubsets]
    exact and_comm
  finset_mem_Ioc s t u := by
    rw [mem_filter]; rw [mem_powerset]
    exact and_comm
  finset_mem_Ioo s t u := by
    rw [mem_filter]; rw [mem_ssubsets]
    exact and_comm

theorem Icc_eq_filter_powerset : Icc s t = t.powerset.filter ((· ⊆ ·) s) :=
  rfl
#align finset.Icc_eq_filter_powerset Finset.Icc_eq_filter_powerset

theorem Ico_eq_filter_ssubsets : Ico s t = t.ssubsets.filter ((· ⊆ ·) s) :=
  rfl
#align finset.Ico_eq_filter_ssubsets Finset.Ico_eq_filter_ssubsets

theorem Ioc_eq_filter_powerset : Ioc s t = t.powerset.filter ((· ⊂ ·) s) :=
  rfl
#align finset.Ioc_eq_filter_powerset Finset.Ioc_eq_filter_powerset

theorem Ioo_eq_filter_ssubsets : Ioo s t = t.ssubsets.filter ((· ⊂ ·) s) :=
  rfl
#align finset.Ioo_eq_filter_ssubsets Finset.Ioo_eq_filter_ssubsets

theorem Iic_eq_powerset : Iic s = s.powerset :=
  filter_true_of_mem fun t _ => empty_subset t
#align finset.Iic_eq_powerset Finset.Iic_eq_powerset

theorem Iio_eq_ssubsets : Iio s = s.ssubsets :=
  filter_true_of_mem fun t _ => empty_subset t
#align finset.Iio_eq_ssubsets Finset.Iio_eq_ssubsets

variable {s t}

theorem Icc_eq_image_powerset (h : s ⊆ t) : Icc s t = (t \ s).powerset.image ((· ∪ ·) s) := by
  ext u
  simp_rw [mem_Icc, mem_image, mem_powerset]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_le_sdiff_right ht, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, union_subset h <| hv.trans <| sdiff_subset _ _⟩
#align finset.Icc_eq_image_powerset Finset.Icc_eq_image_powerset

theorem Ico_eq_image_ssubsets (h : s ⊆ t) : Ico s t = (t \ s).ssubsets.image ((· ∪ ·) s) := by
  ext u
  simp_rw [mem_Ico, mem_image, mem_ssubsets]
  constructor
  · rintro ⟨hs, ht⟩
    exact ⟨u \ s, sdiff_lt_sdiff_right ht hs, sup_sdiff_cancel_right hs⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨le_sup_left, sup_lt_of_lt_sdiff_left hv h⟩
#align finset.Ico_eq_image_ssubsets Finset.Ico_eq_image_ssubsets

/-- Cardinality of a non-empty `Icc` of finsets. -/
theorem card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) := by
  rw [← card_sdiff h]; rw [← card_powerset]; rw [Icc_eq_image_powerset h]; rw [Finset.card_image_iff]
  rintro u hu v hv (huv : s ⊔ u = s ⊔ v)
  rw [mem_coe] at hu hv; rw [mem_powerset] at hu hv
  rw [← (disjoint_sdiff.mono_right hu : Disjoint s u).sup_sdiff_cancel_left]; rw [←
    (disjoint_sdiff.mono_right hv : Disjoint s v).sup_sdiff_cancel_left]; rw [huv]
#align finset.card_Icc_finset Finset.card_Icc_finset

/-- Cardinality of an `Ico` of finsets. -/
theorem card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one]; rw [card_Icc_finset h]
#align finset.card_Ico_finset Finset.card_Ico_finset

/-- Cardinality of an `Ioc` of finsets. -/
theorem card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one]; rw [card_Icc_finset h]
#align finset.card_Ioc_finset Finset.card_Ioc_finset

/-- Cardinality of an `Ioo` of finsets. -/
theorem card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two]; rw [card_Icc_finset h]
#align finset.card_Ioo_finset Finset.card_Ioo_finset

/-- Cardinality of an `Iic` of finsets. -/
theorem card_Iic_finset : (Iic s).card = 2 ^ s.card := by rw [Iic_eq_powerset, card_powerset]
#align finset.card_Iic_finset Finset.card_Iic_finset

/-- Cardinality of an `Iio` of finsets. -/
theorem card_Iio_finset : (Iio s).card = 2 ^ s.card - 1 := by
  rw [Iio_eq_ssubsets]; rw [ssubsets]; rw [card_erase_of_mem (mem_powerset_self _)]; rw [card_powerset]
#align finset.card_Iio_finset Finset.card_Iio_finset

end Decidable

variable {s t : Finset α}

section Cons

lemma covby_cons {i : α} (hi : i ∉ s) : s ⋖ cons i s hi :=
  Covby.of_image ⟨⟨((↑) : Finset α → Set α), coe_injective⟩, coe_subset⟩ <| by
    simp only [RelEmbedding.coe_mk, Function.Embedding.coeFn_mk, coe_cons, mem_coe]
    exact_mod_cast Set.covby_insert (show i ∉ (s : Set α) from hi)

lemma covby_iff : s ⋖ t ↔ ∃ i : α, ∃ hi : i ∉ s, t = cons i s hi := by
  constructor
  · intro hst
    obtain ⟨i, hi, his⟩ := ssubset_iff_exists_cons_subset.mp hst.1
    exact ⟨i, hi, .symm <| eq_of_le_of_not_lt his <| hst.2 <| ssubset_cons hi⟩
  · rintro ⟨i, hi, rfl⟩
    exact covby_cons hi

/-- A function `f` from `Finset α` is monotone if and only if `f s ≤ f (cons i s hi)` for all
`s` and `i ∉ s`. -/
theorem monotone_iff {β : Type*} [Preorder β] (f : Finset α → β) :
    Monotone f ↔ ∀ s : Finset α, ∀ {i} (hi : i ∉ s), f s ≤ f (cons i s hi) := by
  classical
  simp only [monotone_iff_forall_covby, covby_iff, forall_exists_index, and_imp]
  aesop

/-- A function `f` from `Finset α` is strictly monotone if and only if `f s < f (insert i s)` for
all `s` and `i ∉ s`. -/
theorem strictMono_iff {β : Type*} [Preorder β] (f : Finset α → β) :
    StrictMono f ↔ ∀ s : Finset α, ∀ {i} (hi : i ∉ s), f s < f (cons i s hi) := by
  classical
  simp only [strictMono_iff_forall_covby, covby_iff, forall_exists_index, and_imp]
  aesop

/-- A function `f` from `Finset α` is antitone if and only if `f (cons i s hi) ≤ f s` for all
`s` and `i ∉ s`. -/
theorem antitone_iff {β : Type*} [Preorder β] (f : Finset α → β) :
    Antitone f ↔ ∀ s : Finset α, ∀ {i} (hi : i ∉ s), f (cons i s hi) ≤ f s :=
  monotone_iff (β := βᵒᵈ) f

/-- A function `f` from `Finset α` is strictly antitone if and only if `f (cons i s hi) < f s` for
all `s` and `i ∉ s`. -/
theorem strictAnti_iff {β : Type*} [Preorder β] (f : Finset α → β) :
    StrictAnti f ↔ ∀ s : Finset α, ∀ {i} (hi : i ∉ s), f (cons i s hi) < f s :=
  strictMono_iff (β := βᵒᵈ) f

end Cons

section Insert

variable [DecidableEq α]

lemma covby_insert {i : α} (hi : i ∉ s) : s ⋖ insert i s := by
  simpa using covby_cons hi

lemma covby_iff' : s ⋖ t ↔ ∃ i : α, i ∉ s ∧ t = insert i s := by
  simp [covby_iff]

/-- A function `f` from `Finset α` is monotone if and only if `f s ≤ f (insert i s)` for all
`s` and `i ∉ s`. -/
theorem monotone_iff' {β : Type*} [Preorder β] (f : Finset α → β) :
    Monotone f ↔ ∀ s : Finset α, ∀ {i} (_hi : i ∉ s), f s ≤ f (insert i s) := by
  simp [monotone_iff]

/-- A function `f` from `Finset α` is strictly monotone if and only if `f s < f (insert i s)` for
all `s` and `i ∉ s`. -/
theorem strictMono_iff' {β : Type*} [Preorder β] (f : Finset α → β) :
    StrictMono f ↔ ∀ s : Finset α, ∀ {i} (_hi : i ∉ s), f s < f (insert i s) := by
  simp [strictMono_iff]

/-- A function `f` from `Finset α` is antitone if and only if `f (insert i s) ≤ f s` for all
`s` and `i ∉ s`. -/
theorem antitone_iff' {β : Type*} [Preorder β] (f : Finset α → β) :
    Antitone f ↔ ∀ s : Finset α, ∀ {i} (_hi : i ∉ s), f (insert i s) ≤ f s :=
  monotone_iff' (β := βᵒᵈ) f

/-- A function `f` from `Finset α` is strictly antitone if and only if `f (insert i s) < f s` for
all `s` and `i ∉ s`. -/
theorem strictAnti_iff' {β : Type*} [Preorder β] (f : Finset α → β) :
    StrictAnti f ↔ ∀ s : Finset α, ∀ {i} (_hi : i ∉ s), f (insert i s) < f s :=
  strictMono_iff' (β := βᵒᵈ) f

end Insert

end Finset
