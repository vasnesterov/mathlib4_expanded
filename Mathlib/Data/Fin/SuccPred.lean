/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Order.SuccPred.Basic

#align_import data.fin.succ_pred from "leanprover-community/mathlib"@"7c523cb78f4153682c2929e3006c863bfef463d0"

/-!
# Successors and predecessors of `Fin n`

In this file, we show that `Fin n` is both a `SuccOrder` and a `PredOrder`. Note that they are
also archimedean, but this is derived from the general instance for well-orderings as opposed
to a specific `Fin` instance.

-/


namespace Fin

instance : ∀ {n : ℕ}, SuccOrder (Fin n)
  | 0 => by constructor <;> first | assumption | intro a; exact elim0 a
  | n + 1 =>
    SuccOrder.ofCore (fun i => if i < Fin.last n then i + 1 else i)
      (by
        intro a ha b
        rw [isMax_iff_eq_top] at ha; rw [eq_top_iff] at ha; rw [not_le] at ha; rw [top_eq_last] at ha
        dsimp
        rw [if_pos ha]; rw [lt_iff_val_lt_val]; rw [le_iff_val_le_val]; rw [val_add_one_of_lt ha]
        exact Nat.lt_iff_add_one_le)
      (by
        intro a ha
        rw [isMax_iff_eq_top] at ha; rw [top_eq_last] at ha
        dsimp
        rw [if_neg ha.not_lt])

@[simp]
theorem succ_eq {n : ℕ} : SuccOrder.succ = fun a => if a < Fin.last n then a + 1 else a :=
  rfl
#align fin.succ_eq Fin.succ_eq

@[simp]
theorem succ_apply {n : ℕ} (a) : SuccOrder.succ a = if a < Fin.last n then a + 1 else a :=
  rfl
#align fin.succ_apply Fin.succ_apply

instance : ∀ {n : ℕ}, PredOrder (Fin n)
  | 0 => by constructor <;> first | assumption | intro a; exact elim0 a
  | n + 1 =>
    PredOrder.ofCore (fun x => if x = 0 then 0 else x - 1)
      (by
        intro a ha b
        rw [isMin_iff_eq_bot] at ha; rw [eq_bot_iff] at ha; rw [not_le] at ha; rw [bot_eq_zero] at ha
        dsimp
        rw [if_neg ha.ne']; rw [lt_iff_val_lt_val]; rw [le_iff_val_le_val]; rw [coe_sub_one]; rw [if_neg ha.ne']; rw [le_tsub_iff_right]; rw [Iff.comm]
        exact Nat.lt_iff_add_one_le
        exact ha)
      (by
        intro a ha
        rw [isMin_iff_eq_bot] at ha; rw [bot_eq_zero] at ha
        dsimp
        rwa [if_pos ha, eq_comm])

@[simp]
theorem pred_eq {n} : PredOrder.pred = fun a : Fin (n + 1) => if a = 0 then 0 else a - 1 :=
  rfl
#align fin.pred_eq Fin.pred_eq

@[simp]
theorem pred_apply {n : ℕ} (a : Fin (n + 1)) : PredOrder.pred a = if a = 0 then 0 else a - 1 :=
  rfl
#align fin.pred_apply Fin.pred_apply

end Fin
