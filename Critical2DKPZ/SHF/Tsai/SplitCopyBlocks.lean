/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainCoordinateCopies

/-! # Splitting the selected coordinate from independent block copies

The outer family inserts the zero measure at the selected block and keeps
all other independent coordinates. Inserting the selected sample restores
the full coordinate-copy family by replacing that one zero block. The same
coordinate insertion preserves the product probability measures.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- The outer coordinate-copy blocks, with zero at the selected coordinate. -/
def outerCopyBlock {Ω : Type*} (K : ℕ) (j : Fin (K + 1))
    (B : ℕ → Ω → Measure (Plane × Plane)) (a : Fin K → Ω) (k : ℕ) : Measure (Plane × Plane) :=
  if hk : k ≤ K then
    (Fin.insertNth (α := fun _ : Fin (K + 1) => Measure (Plane × Plane)) j 0
      (fun i => B (j.succAbove i) (a i))) ⟨k, Nat.lt_succ_of_le hk⟩
  else 0

/-- The outer-copy blocks are measurable in the remaining independent samples. -/
theorem measurable_outerCopyBlock {Ω : Type*} [MeasurableSpace Ω] (K : ℕ)
    (j : Fin (K + 1)) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, Measurable (B k)) (k : ℕ) (hk : k ≤ K) :
    Measurable (fun a => outerCopyBlock K j B a k) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => Measure (Plane × Plane)) j
  have hrest : Measurable (fun a : Fin K → Ω => fun i : Fin K => B (j.succAbove i) (a i)) :=
    Measurable.of_eval fun i =>
      (hB _ (Nat.le_of_lt_succ (j.succAbove i).is_lt)).comp (measurable_pi_apply i)
  have hall : Measurable (fun a : Fin K → Ω => e.symm (0, fun i => B (j.succAbove i) (a i))) :=
    e.symm.measurable.comp (measurable_const.prodMk hrest)
  have h := (measurable_pi_apply (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (K + 1))).comp hall
  simpa only [outerCopyBlock, dite_eq_left hk, Function.comp_def, e,
    MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Equiv.coe_fn_mk] using h

/-- Everywhere locally finite original blocks give everywhere locally finite outer-copy blocks. -/
theorem locallyFinite_outerCopyBlock {Ω : Type*} (K : ℕ) (j : Fin (K + 1))
    (B : ℕ → Ω → Measure (Plane × Plane))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω)) (a : Fin K → Ω) (k : ℕ) :
    IsLocallyFiniteMeasure (outerCopyBlock K j B a k) := by
  have hfin (l : Fin (K + 1)) : IsLocallyFiniteMeasure
      ((Fin.insertNth (α := fun _ : Fin (K + 1) => Measure (Plane × Plane)) j 0
        (fun i => B (j.succAbove i) (a i))) l) := by
    refine Fin.succAboveCases j ?_ (fun i => ?_) l
    · rw [Fin.insertNth_apply_same]
      infer_instance
    · rw [Fin.insertNth_apply_succAbove]
      exact hlf _ (Nat.le_of_lt_succ (j.succAbove i).is_lt) _
  by_cases hk : k ≤ K
  · simpa only [outerCopyBlock, dite_eq_left hk] using hfin ⟨k, Nat.lt_succ_of_le hk⟩
  · simp only [outerCopyBlock, dite_eq_right hk]
    infer_instance

/-- Inserting the selected sample restores the full copy family by one block update. -/
theorem coordinateCopyBlock_insertNth_eq_update_outer {Ω : Type*} (K : ℕ) (j : Fin (K + 1))
    (B : ℕ → Ω → Measure (Plane × Plane)) (a : Fin K → Ω) (ω : Ω) :
    coordinateCopyBlock K B (Fin.insertNth (α := fun _ : Fin (K + 1) => Ω) j ω a) =
      Function.update (outerCopyBlock K j B a) j (B j ω) := by
  classical
  have hfin (l : Fin (K + 1)) : B l (Fin.insertNth (α := fun _ : Fin (K + 1) => Ω) j ω a l) =
      Function.update (outerCopyBlock K j B a) j (B j ω) l := by
    refine Fin.succAboveCases j ?_ (fun i => ?_) l
    · rw [Fin.insertNth_apply_same, Function.update_self]
    · have hne : (j.succAbove i : ℕ) ≠ (j : ℕ) := fun h => (Fin.succAbove_ne j i) (Fin.ext h)
      rw [Fin.insertNth_apply_succAbove, Function.update_of_ne hne]
      simp only [outerCopyBlock, dite_eq_left (Nat.le_of_lt_succ (j.succAbove i).is_lt)]
      exact (Fin.insertNth_apply_succAbove (α := fun _ : Fin (K + 1) => Measure (Plane × Plane))
        j 0 (fun i => B (j.succAbove i) (a i)) i).symm
  funext k
  by_cases hk : k ≤ K
  · simpa only [coordinateCopyBlock, dite_eq_left hk] using hfin ⟨k, Nat.lt_succ_of_le hk⟩
  · have hne : k ≠ (j : ℕ) := fun h => hk (h.symm ▸ Nat.le_of_lt_succ j.is_lt)
    simp only [coordinateCopyBlock, dite_eq_right hk, Function.update_of_ne hne,
      outerCopyBlock]

/-- Replacing the selected original block leaves every outer-copy block unchanged. -/
theorem outerCopyBlock_update {Ω : Type*} (K : ℕ) (j : Fin (K + 1))
    (B : ℕ → Ω → Measure (Plane × Plane)) (B' : Ω → Measure (Plane × Plane)) :
    outerCopyBlock K j (Function.update B j B') = outerCopyBlock K j B := by
  classical
  funext a k
  have hrest : (fun i : Fin K => Function.update B j B' (j.succAbove i) (a i)) =
      fun i : Fin K => B (j.succAbove i) (a i) := by
    funext i
    have hne : (j.succAbove i : ℕ) ≠ (j : ℕ) := fun h => (Fin.succAbove_ne j i) (Fin.ext h)
    rw [Function.update_of_ne hne]
  simp only [outerCopyBlock, hrest]

/-- Inserting the selected sample into the remaining independent coordinates preserves product probability. -/
theorem measurePreserving_insertCopyCoordinate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1)) :
    MeasurePreserving (fun q : (Fin K → Ω) × Ω => Fin.insertNth (α := fun _ : Fin (K + 1) => Ω) j q.2 q.1)
      ((Measure.pi (fun _ : Fin K => P)).prod P) (Measure.pi (fun _ : Fin (K + 1) => P)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => Ω) j
  have he := measurePreserving_piFinSuccAbove (fun _ : Fin (K + 1) => P) j
  exact (he.symm e).comp (Measure.measurePreserving_swap)

end Critical2DKPZ.SHF.Tsai

end
