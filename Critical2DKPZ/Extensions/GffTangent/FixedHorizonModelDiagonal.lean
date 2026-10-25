/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonArrayDiagonal
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonBlockVariance
import Mathlib.Tactic

/-! # The slowly refined CCR array for the actual polymer -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The actual quasi-critical polymer admits a slowly refined time partition
with vanishing L2 approximation error and total fourth moment, and with the
correct fixed-horizon limiting total variance. -/
theorem exists_slow_cellBlock_partition
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    (n : ℕ → ℕ) {T : ℝ} (hT : 0 < T)
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 T)) (f : TestFn) :
    ∃ M : ℕ → ℕ, (∀ N, 0 < M N) ∧ Tendsto M atTop atTop ∧
      Tendsto (fun N => ∫ ω,
        (finiteEntranceFluctuation (β N) (Real.sqrt (l N)) 0 (n N)
          (fixedHorizonCellSites N f) (signedCellProfile N f) ω -
          ∑ i : Fin (M N), cellBlockFluctuation (β N) (l N) N (n N) (M N) i f ω) ^ 2 ∂disorderLaw)
        atTop (𝓝 0) ∧
      Tendsto (fun N => ∑ i : Fin (M N),
        ∫ ω, cellBlockFluctuation (β N) (l N) N (n N) (M N) i f ω ^ 2 ∂disorderLaw)
        atTop (𝓝 (4 * Real.pi * ∫ t in Ioo 0 T, ∫ p : Plane × Plane,
          f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume))) ∧
      Tendsto (fun N => ∑ i : Fin (M N),
        ∫ ω, cellBlockFluctuation (β N) (l N) N (n N) (M N) i f ω ^ 4 ∂disorderLaw)
        atTop (𝓝 0) := by
  let X : ℕ → Disorder → ℝ := fun N => finiteEntranceFluctuation (β N) (Real.sqrt (l N))
    0 (n N) (fixedHorizonCellSites N f) (signedCellProfile N f)
  let W : ℕ → ℕ → ℕ → Disorder → ℝ := fun M N i =>
    cellBlockFluctuation (β N) (l N) N (n N) M i f
  let R : ℕ → ℕ → ℝ := fun M N => ∫ ω, (X N ω - ∑ i : Fin M, W M N i ω) ^ 2 ∂disorderLaw
  let V : ℕ → ℕ → ℝ := fun M N => ∑ i : Fin M, ∫ ω, W M N i ω ^ 2 ∂disorderLaw
  let F : ℕ → ℕ → ℝ := fun M N => ∑ i : Fin M, ∫ ω, W M N i ω ^ 4 ∂disorderLaw
  let v := 4 * Real.pi * ∫ t in Ioo 0 T, ∫ p : Plane × Plane,
    f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume)
  obtain ⟨Cf, hCf⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hCf0 : 0 ≤ Cf := (norm_nonneg (f 0)).trans (hCf 0)
  have hfC (x : Plane) : |f x| ≤ Cf := by simpa only [Real.norm_eq_abs] using hCf x
  let C := (16 * ((2 : ℝ) ^ 32 * Real.pi ^ 2 * (4 * Cf * ∫ x : Plane, |f x|) ^ 2)) * T ^ 2
  apply exists_slow_array_partition R V F v C
  · intro M N
    exact integral_nonneg (fun _ => sq_nonneg _)
  · intro M N
    exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun _ => by change 0 ≤ W M N i _ ^ 4; positivity))
  · intro M hM
    exact tendsto_integral_sq_quasiCritical_window_error l β hl hratio hβ hσ n hT hn hM f
      (fun N => fixedHorizonCellSites N f) (fun N x hx => latticePoint_mem_fixedHorizonCellSites N f hx)
  · intro M hM
    exact tendsto_sum_variance_cellBlockFluctuation l β hl hratio hβ hσ n hT hn hM f
  · intro M hM ε hε
    exact eventually_sum_fourth_cellBlockFluctuation_le f hCf0 hfC l β hl hratio hβ hσ n hT hn hM hε

end Critical2DKPZ.Extensions.GffTangent
