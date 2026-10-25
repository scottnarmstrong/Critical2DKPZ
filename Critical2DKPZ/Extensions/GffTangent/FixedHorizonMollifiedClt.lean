/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonClt
public import Critical2DKPZ.Extensions.GffTangent.LinearClt

/-! # Proposition 6.2 from the proved fixed-horizon flow CLT -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- Proposition 6.2: the mollified linear functionals at a slowly growing
horizon converge jointly to their finite-dimensional GFF law. -/
theorem tendstoInDistribution_sqrt_half_shfPairing_mollified
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : Fin n → TestFn) (hfzero : ∀ i, (∫ x : Plane, f i x) = 0)
    (T : ℝ → ℝ) (hTpos : ∀ l, 0 < T l)
    (hT : Tendsto T atTop atTop)
    (hlog : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0))
    (δ : ℝ → ℝ) (hδ : ∀ l, 0 ≤ δ l) (hδlim : Tendsto δ atTop (𝓝 0))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hν : IsFiniteGffLaw f ν) :
    TendstoInDistribution
      (fun l ω => WithLp.toLp 2 (fun i : Fin n => Real.sqrt (l / 2) *
        shfPairing (Z l) 0 (T l) (heatSmooth' (δ l) (f i)) (fun _ => 1) ω))
      atTop id (fun _ => P) ν := by
  exact tendstoInDistribution_mollified_of_fixedHorizon P Z hZ
    (fun {m} g hgzero {T₀} hT₀ =>
      tendstoInDistribution_sqrt_shfPairing_fixedHorizon P Z hZ (n := m) g hgzero (T := T₀) hT₀)
    f hfzero T hTpos hT hlog δ hδ hδlim ν hν

end Critical2DKPZ.Extensions.GffTangent
