/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockApproximation
public import Critical2DKPZ.SHF.Tsai.HeatKernelStrongL2

/-! # Applicability of the heat-kernel mollifier family

The planar heat kernels at times `1/(ℓ+1)` form an `L²`-applicable mollifier family whose
convolution operators have norm at most one.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- The fixed heat-kernel family in the common block approximation is `L²` applicable. -/
theorem isL2ApplicableMollifier_heatMollifier : IsL2ApplicableMollifier heatMollifier := by
  let t (ℓ : ℕ) : ℝ := 1 / ((ℓ : ℝ) + 1)
  have ht (ℓ : ℕ) : 0 < t ℓ := by dsimp only [t]; positivity
  have htlim : Tendsto t atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have haction (ℓ : ℕ) (φ : Plane → ℝ) : mollifierAction (heatKernel (t ℓ)) φ =
      fun x => ∫ y, heatMollifier ℓ (x - y) * φ y := rfl
  refine ⟨fun ℓ x => heatKernel_nonneg (ht ℓ).le x, fun ℓ => continuous_heatKernel (t ℓ),
    fun ℓ => memLp_heatKernel (ht ℓ), fun ℓ => ?_, ?_⟩
  · refine ⟨1, by norm_num, fun φ hφ => ?_⟩
    have h := mollifierAction_heat_memLp_and_eLpNorm_le (ht ℓ) φ hφ
    simpa only [haction, one_mul] using h
  · intro φ hφ
    have herror (ℓ : ℕ) : mollifierAction (heatKernel (t ℓ)) φ - φ =
        fun x => (∫ y, heatMollifier ℓ (x - y) * φ y) - φ x := rfl
    simpa only [herror] using tendsto_eLpNorm_heat_sub t ht htlim φ hφ

end Critical2DKPZ.SHF.Tsai

end
