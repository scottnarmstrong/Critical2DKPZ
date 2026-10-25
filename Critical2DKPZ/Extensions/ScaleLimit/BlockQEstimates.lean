/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockPositivity
import Critical2DKPZ.Extensions.ScaleLimit.LatticeQTails
import Critical2DKPZ.Extensions.ScaleLimit.RatioTailTransfer
import Mathlib.Tactic

/-! # Uniform remaining-interval tails for the geometric flow

The finite lattice-size limit is taken at fixed endpoints and fixed tail level.
Both tails transfer through open events in the numerator and denominator;
positivity of the limiting denominator identifies them with the actual ratio.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Uniform upper and lower tails of the remaining-interval flow ratio. -/
theorem blockQ_estimates (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ (C : ℝ) (ℓ₀ : ℕ),
      ∀ n ℓ : ℕ, ℓ₀ ≤ ℓ → ℓ < n → ∀ u : ℝ, 0 ≤ u →
        P {ω | blockQ Z ρ n ℓ ω < Real.exp (-u)} ≤
          ENNReal.ofReal (C / ℓ + C * ℓ * Real.exp (-u)) ∧
        P {ω | Real.exp u < blockQ Z ρ n ℓ ω} ≤ ENNReal.ofReal (Real.exp (-u)) := by
  obtain ⟨ρ₀, hρ₀, htail⟩ := latticeBlockQ_tail_bounds ϑ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  obtain ⟨C, ℓ₀, hC⟩ := htail ρ hρ
  refine ⟨C, ℓ₀, ?_⟩
  intro n ℓ hℓ hℓn u hu
  let b : Fin 2 → ℕ := Fin.cases 0 (fun _ => ℓ)
  let X : ℕ → Disorder → Fin 2 → ℝ := fun N ω i => latticeGeometricMass ϑ ρ N n (b i) ω
  let Y : Ω → Fin 2 → ℝ := fun ω i => shfPairing Z (tau ρ n) (tau ρ (b i))
    (fun y => heatKernel (tau ρ n) y) (fun _ => 1) ω
  have hab (i : Fin 2) : b i < n := by
    refine Fin.cases ?_ (fun j => ?_) i
    · change 0 < n
      omega
    · exact hℓn
  have hdist : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P :=
    latticeGeometricMass_joint_tendsto ϑ P Z hZ hρ1 2 (fun _ => n) b hab
  have hp : ∀ᵐ ω ∂P, 0 < Y ω 1 := blockA_pos_ae ϑ P Z hZ hρ1 hℓn
  have hXeq (N : ℕ) (ω : Disorder) : X N ω 0 / X N ω 1 = latticeBlockQ ϑ ρ N n ℓ ω := rfl
  have hYeq (ω : Ω) : Y ω 0 / Y ω 1 = blockQ Z ρ n ℓ ω := by
    change shfPairing Z (tau ρ n) (tau ρ 0) (fun y => heatKernel (tau ρ n) y)
      (fun _ => 1) ω / blockA Z ρ n ℓ ω = _
    simp only [tau, pow_zero, blockQ]
  have hlow : ∀ᶠ N : ℕ in atTop,
      disorderLaw {ω | X N ω 0 / X N ω 1 < Real.exp (-u)} ≤
        ENNReal.ofReal (C / ℓ + C * ℓ * Real.exp (-u)) := by
    simpa only [hXeq] using (hC n ℓ hℓ hℓn u hu).mono (fun N hN => hN.1)
  have hupp : ∀ᶠ N : ℕ in atTop,
      disorderLaw {ω | Real.exp u < X N ω 0 / X N ω 1} ≤
        ENNReal.ofReal (Real.exp (-u)) := by
    simpa only [hXeq] using (hC n ℓ hℓ hℓn u hu).mono (fun N hN => hN.2)
  have hl := measure_ratio_lt_le_of_tendstoInDistribution hdist hp (Real.exp (-u))
    (ENNReal.ofReal (C / ℓ + C * ℓ * Real.exp (-u))) hlow
  have hh := measure_lt_ratio_le_of_tendstoInDistribution hdist hp (Real.exp u)
    (ENNReal.ofReal (Real.exp (-u))) hupp
  exact ⟨by simpa only [hYeq] using hl, by simpa only [hYeq] using hh⟩

end Critical2DKPZ.Extensions.ScaleLimit
