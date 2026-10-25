/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockMoments
import Mathlib.Probability.Independence.Basic

/-! # Independence under replacement by an extra independent block

An injective reindexing selects the extra block at one designated position.
The original prefix and the replaced prefix therefore both retain mutual
independence, as required by the block comparison moment formulas.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Replace one entry of a finite independent prefix by its extra independent entry. -/
theorem iIndepFun_replaceFin_of_extra {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} {n : ℕ} (f : Fin (n + 1) → Ω → X) (hind : iIndepFun f P) (j : Fin n) :
    iIndepFun (fun i : Fin n => if i = j then f (Fin.last n) else f i.castSucc) P := by
  classical
  let idx (i : Fin n) : Fin (n + 1) := if i = j then Fin.last n else i.castSucc
  have hinj : Function.Injective idx := by
    intro a b hab
    by_cases ha : a = j <;> by_cases hb : b = j
    · exact ha.trans hb.symm
    · have hv := congrArg Fin.val hab
      simp only [idx, ite_eq_left ha, ite_eq_right hb, Fin.val_last, Fin.val_castSucc] at hv
      exact False.elim (Nat.ne_of_lt b.is_lt hv.symm)
    · have hv := congrArg Fin.val hab
      simp only [idx, ite_eq_right ha, ite_eq_left hb, Fin.val_last, Fin.val_castSucc] at hv
      exact False.elim (Nat.ne_of_lt a.is_lt hv)
    · have hv := congrArg Fin.val hab
      simp only [idx, ite_eq_right ha, ite_eq_right hb, Fin.val_castSucc] at hv
      exact Fin.ext hv
  have heq : (fun i : Fin n => if i = j then f (Fin.last n) else f i.castSucc) =
      fun i => f (idx i) := by
    funext i
    dsimp only [idx]
    split_ifs <;> rfl
  rw [heq]
  exact hind.precomp hinj

/-- The original blocks are independent when one additional block is included in the independence axiom. -/
theorem iIndepFun_prefix_of_extra {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} (K : ℕ) (B : ℕ → Ω → X) (B' : Ω → X)
    (hind : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then B k else B') P) :
    iIndepFun (fun k : Fin (K + 1) => B k) P := by
  have h := hind.precomp (g := fun k : Fin (K + 1) => k.castSucc) (Fin.castSucc_injective (K + 1))
  have heq : (fun k : Fin (K + 1) =>
      if ((k.castSucc : Fin (K + 2)) : ℕ) ≤ K then B k.castSucc else B') =
      fun k : Fin (K + 1) => B k := by
    funext k
    exact ite_eq_left (Nat.le_of_lt_succ k.is_lt)
  rw [heq] at h
  exact h

/-- Replacing one original block by the independent extra block preserves mutual independence. -/
theorem iIndepFun_update_of_extra {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} (K j : ℕ) (hj : j ≤ K) (B : ℕ → Ω → X) (B' : Ω → X)
    (hind : iIndepFun (fun k : Fin (K + 2) => if (k : ℕ) ≤ K then B k else B') P) :
    iIndepFun (fun k : Fin (K + 1) => fun ω => Function.update (fun k => B k ω) j (B' ω) k) P := by
  classical
  let j' : Fin (K + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have h := iIndepFun_replaceFin_of_extra _ hind j'
  have heq : (fun k : Fin (K + 1) =>
      if k = j' then (if ((Fin.last (K + 1)) : ℕ) ≤ K then B (Fin.last (K + 1)) else B')
      else (if ((k.castSucc : Fin (K + 2)) : ℕ) ≤ K then B k.castSucc else B')) =
      fun k : Fin (K + 1) => fun ω => Function.update (fun k => B k ω) j (B' ω) k := by
    funext k ω
    have hk : (k : ℕ) ≤ K := Nat.le_of_lt_succ k.is_lt
    have hlast : ¬K + 1 ≤ K := by omega
    simp only [Fin.val_last, ite_eq_right hlast, Fin.val_castSucc, ite_eq_left hk]
    by_cases hkj : k = j'
    · have hkn : (k : ℕ) = j := congrArg Fin.val hkj
      simp only [ite_eq_left hkj, hkn, Function.update_self]
    · have hkn : (k : ℕ) ≠ j := fun h => hkj (Fin.ext h)
      simp only [ite_eq_right hkj, Function.update_of_ne hkn]
  rw [heq] at h
  exact h

end Critical2DKPZ.SHF.Tsai

end
