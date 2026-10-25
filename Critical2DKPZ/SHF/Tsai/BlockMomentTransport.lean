/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockMoments
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Transport of actual block moments to a coupling space

A measure-preserving map pulls back block measurability, local finiteness,
inner integrability, and the first four literal moment identities. This
allows the merge steps to place outer blocks and a flow on a product space.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Pulling a moment block back along a measure-preserving map preserves all its moment data. -/
theorem HasDeltaBoseMoments.comp_measurePreserving {θ τ : ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B)
    {φ : Ω' → Ω} (hφ : MeasurePreserving φ Q P) :
    HasDeltaBoseMoments θ τ Q (fun ω => B (φ ω)) := by
  refine ⟨hB.1.comp hφ.measurable, hφ.quasiMeasurePreserving.ae hB.2.1, ?_⟩
  intro n hn1 hn g g' hg hg'
  have hMom := hB.2.2 n hn1 hn g g' hg hg'
  let F (ω : Ω) := ∏ i, ∫ p, g i p.1 * g' i p.2 ∂B ω
  have hI : Integrable F P := hMom.2.1
  have hMap : AEStronglyMeasurable F (Q.map φ) := by
    rw [hφ.map_eq]
    exact hI.aestronglyMeasurable
  refine ⟨hφ.quasiMeasurePreserving.ae hMom.1,
    hφ.integrable_comp_of_integrable hI, ?_⟩
  calc
    (∫ ω, F (φ ω) ∂Q) = ∫ ω, F ω ∂Q.map φ :=
      (integral_map hφ.measurable.aemeasurable hMap).symm
    _ = ∫ ω, F ω ∂P := by rw [hφ.map_eq]
    _ = _ := hMom.2.2

/-- Appending an independent-coordinate block preserves each prescribed moment predicate on the product coupling. -/
theorem hasDeltaBoseMoments_fin_snoc_prod {θ τ : ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {n : ℕ}
    (A : Ω' → Measure (Plane × Plane)) (hA : HasDeltaBoseMoments θ τ P' A)
    (σ : Fin n → ℝ) (B : Fin n → Ω → Measure (Plane × Plane))
    (hB : ∀ i, HasDeltaBoseMoments θ (σ i) P (B i)) (i : Fin (n + 1)) :
    HasDeltaBoseMoments θ (Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) σ τ i) (P'.prod P)
      (fun ω : Ω' × Ω => Fin.snoc (α := fun _ : Fin (n + 1) => Measure (Plane × Plane))
        (fun j => B j ω.2) (A ω.1) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using hA.comp_measurePreserving
      (measurePreserving_fst : MeasurePreserving Prod.fst (P'.prod P) P')
  · simpa only [Fin.snoc_castSucc] using (hB j).comp_measurePreserving
      (measurePreserving_snd : MeasurePreserving Prod.snd (P'.prod P) P)

end Critical2DKPZ.SHF.Tsai

end
