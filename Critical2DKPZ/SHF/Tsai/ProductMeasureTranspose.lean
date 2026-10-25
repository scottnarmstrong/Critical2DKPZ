/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Transposition of finite product measures

Transposing a finite array of sigma-finite coordinate measures identifies the product
grouped by rows with the product grouped by columns.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Transposing a finite array preserves arbitrary sigma-finite coordinate product measures. -/
theorem measurePreserving_pi_transpose_family {X : Type*} [MeasurableSpace X] (m : ℕ)
    (n : ℕ) (μ : Fin m → Fin n → Measure X) [∀ k i, SigmaFinite (μ k i)] :
    MeasurePreserving (fun p : Fin m → Fin n → X => fun i k => p k i)
      (Measure.pi (fun k => Measure.pi (μ k)))
      (Measure.pi (fun i => Measure.pi (fun k => μ k i))) := by
  induction n with
  | zero =>
    let x : Fin 0 → Fin m → X := Fin.elim0
    have heq : (fun p : Fin m → Fin 0 → X => fun i k => p k i) = fun _ => x := by
      funext p i
      exact Fin.elim0 i
    refine ⟨measurable_pi_iff.mpr (fun i => Fin.elim0 i), ?_⟩
    rw [heq, Measure.map_const, Measure.pi_univ]
    simp only [Measure.pi_empty_univ, Finset.prod_const_one, one_smul]
    exact (Measure.pi_of_empty _ x).symm
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin m → X) 0
    have he := measurePreserving_piFinSuccAbove (fun i : Fin (n + 1) => Measure.pi (fun k => μ k i)) 0
    have hsplit := measurePreserving_pi
      (fun k => Measure.pi (μ k))
      (fun k => (μ k 0).prod (Measure.pi (fun i : Fin n => μ k i.succ)))
      (fun k => measurePreserving_piFinSuccAbove (μ k) 0)
    have hgroup := measurePreserving_arrowProdEquivProdArrow X (Fin n → X) (Fin m)
      (fun k => μ k 0) (fun k => Measure.pi (fun i : Fin n => μ k i.succ))
    have htail := (MeasurePreserving.id (Measure.pi (fun k => μ k 0))).prod
      (ih (fun k i => μ k i.succ))
    have hcomp := (he.symm e).comp (htail.comp (hgroup.comp hsplit))
    have heq : ⇑e.symm ∘ (Prod.map id (fun p : Fin m → Fin n → X => fun i k => p k i)) ∘
        ⇑(MeasurableEquiv.arrowProdEquivProdArrow X (Fin n → X) (Fin m)) ∘
        (fun p : Fin m → Fin (n + 1) → X => fun k =>
          MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0 (p k)) =
        fun p : Fin m → Fin (n + 1) → X => fun i k => p k i := by
      funext p i k
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
          MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]
      · simp [e, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
          MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow, Fin.tail]
    rw [heq] at hcomp
    exact hcomp


end Critical2DKPZ.SHF.Tsai

end
