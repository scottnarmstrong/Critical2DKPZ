/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.RandomMeasure.GeneralTests
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Passing uniform compact approximation through locally finite measures

A common compact support window has finite mass. The canonical compact-test
integral error bound therefore transfers a uniform vanishing error to actual
pairing convergence, without any global finite-mass hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Uniform approximation inside one compact support window gives pairing convergence for every locally finite measure. -/
theorem tendsto_integral_of_uniform_compact_support
    (μ : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ]
    (f : C_c(Plane × Plane, ℝ)) (v : ℕ → C_c(Plane × Plane, ℝ))
    (K : Set (Plane × Plane)) (hK : IsCompact K)
    (hf : tsupport (f : Plane × Plane → ℝ) ⊆ K)
    (hv : ∀ n, tsupport (v n : Plane × Plane → ℝ) ⊆ K)
    (happrox : ∀ n p, |v n p - f p| ≤ 1 / ((n : ℝ) + 1)) :
    Tendsto (fun n => ∫ p, v n p ∂μ) atTop (𝓝 (∫ p, f p ∂μ)) := by
  let E := CompactExhaustion.choice (Plane × Plane)
  obtain ⟨R, hR⟩ := E.exists_superset_of_isCompact hK
  let ν : RandomMeasure.PositiveRadonMeasure (Plane × Plane) := ⟨μ, inferInstance⟩
  have hb (n : ℕ) : |(∫ p, v n p ∂μ) - ∫ p, f p ∂μ| ≤
      (1 / ((n : ℝ) + 1)) * μ.real (E R) :=
    RandomMeasure.vague_test_integral_error E ν R (v n) f ((hv n).trans hR) (hf.trans hR)
      _ (fun p _ => happrox n p)
  have hlim : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) * μ.real (E R)) atTop (𝓝 0) := by
    simpa only [zero_mul] using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (μ.real (E R))
  have hzero : Tendsto (fun n => |(∫ p, v n p ∂μ) - ∫ p, f p ∂μ|) atTop (𝓝 0) :=
    squeeze_zero (fun n => abs_nonneg _) hb hlim
  exact tendsto_iff_norm_sub_tendsto_zero.2 (by simpa only [Real.norm_eq_abs] using hzero)

end Critical2DKPZ.SHF.Tsai

end
