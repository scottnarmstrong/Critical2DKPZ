/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CommonGridFactors

/-! # Coarse grid increments as functions of elementary blocks

Induction on the terminal index composes the measurable two-block factors.
Canonical modifications handle the single elementary block, so every resulting
factor is measurable and everywhere locally finite on the whole tuple carrier.
-/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace Critical2DKPZ.SHF.Tsai

/-- Any interval of a finite dense-time grid is almost surely a measurable locally finite function of its elementary block tuple. -/
theorem IsDenseSHF.exists_grid_interval_factor {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    (m : ℕ) (t : ℕ → ℝ) (ht : StrictMono t) (htD : ∀ k ≤ m, t k ∈ D)
    {a b : ℕ} (hab : a < b) (hb : b ≤ m) :
    ∃ φ : (Fin m → Measure (Plane × Plane)) → Measure (Plane × Plane),
      Measurable φ ∧ (∀ μ, IsLocallyFiniteMeasure (φ μ)) ∧
      Z (t a) (t b) =ᵐ[P] fun ω => φ (fun k => Z (t k) (t (k + 1)) ω) := by
  obtain ⟨φ, hφ, hφlf, hφAE, _hφAE'⟩ := exists_common_grid_interval_factor P P Z Z hZ hZ
    (fun _ _ _ _ _ => rfl) m t (ht.strictMonoOn _) htD hab hb
  exact ⟨φ, hφ, hφlf, hφAE⟩

end Critical2DKPZ.SHF.Tsai

end
