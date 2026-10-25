/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.ConditionalGaussianChain
public import Critical2DKPZ.NonGaussian.DenseThreeBlockData
public import Critical2DKPZ.NonGaussian.FlatTerminalMean
public import Critical2DKPZ.SHF.Tsai.HeatMollifier
import Critical2DKPZ.SHF.Tsai.ChainPairingLinearity
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Mathlib.Tactic

/-! # Conditional bounds for the approximating SHF chains -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported BoundedContinuousFunction ENNReal

namespace Critical2DKPZ.NonGaussian

/-- Every Gaussian-smoothed three-block SHF chain satisfies the normalized
conditional estimate, with a constant independent of the smoothing index. -/
theorem condExp_heatStart_chain_div_le_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hdense : DenseSHFAt ϑ P Z)
    {r s t u δ : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) (htu : t < u)
    (hδ : 0 < δ) (x : Plane) (g : C_c(Plane, ℝ)) (hg : ∀ y, 0 ≤ g y) (n : ℕ) :
    Integrable (fun ω => (∫ p, heatKernel δ (p.1 - x) * g p.2
      ∂chainProduct (fun k => if k = 0 then Z r s ω else if k = 1 then Z s t ω else Z t u ω)
        (fun _ => heatMollifier n) 2) /
      shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω) P ∧
    P[fun ω => (∫ p, heatKernel δ (p.1 - x) * g p.2
      ∂chainProduct (fun k => if k = 0 then Z r s ω else if k = 1 then Z s t ω else Z t u ω)
        (fun _ => heatMollifier n) 2) /
      shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω |
        MeasurableSpace.comap (Z r s) inferInstance ⊔ MeasurableSpace.comap (Z t u) inferInstance]
      ≤ᵐ[P] fun ω => (2 * Real.pi * (t - s))⁻¹ * shfPairing Z t u (fun _ => 1) g ω := by
  let B (k : ℕ) := if k = 0 then Z r s else if k = 1 then Z s t else Z t u
  let τ (k : ℕ) := if k = 0 then s - r else if k = 1 then t - s else u - t
  let f : Plane → ℝ := fun y => heatKernel δ (y - x)
  have hData := threeConsecutive_moments_independent_of_dense ϑ P Z hdense hr hrs hst htu
  have hB (k : ℕ) (hk : k ≤ 2) :
      HasDeltaBoseMoments (ϑ - Real.eulerMascheroniConstant) (τ k) P (B k) := by
    interval_cases k
    · simpa [B, τ] using hData.1.1
    · simpa [B, τ] using hData.1.2.1
    · simpa [B, τ] using hData.1.2.2
  have hτ (k : ℕ) (hk : k ≤ 2) : 0 < τ k := by
    interval_cases k <;> simp only [τ] <;> split_ifs <;> linarith only [hrs, hst, htu]
  have hind : iIndepFun (fun k : Fin 3 => B k) P := hData.2
  have hf : Measurable f := (measurable_heatKernel δ).comp (measurable_id.sub measurable_const)
  have hfL2 : MemLp f 2 := by
    simpa only [f, Function.comp_def, sub_eq_add_neg] using
      (memLp_heatKernel hδ).comp_measurePreserving (measurePreserving_add_right volume (-x))
  have hgL2 : MemLp (g : Plane → ℝ) 2 := g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hnum := ae_integrable_chainPairing 2 τ hτ B hB hind (fun _ => heatMollifier)
    (fun _ => isL2ApplicableMollifier_heatMollifier) n f g hfL2 hgL2
  have hden : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => f p.1) (Z r s ω) := by
    have h := (SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hr hrs hδ x
      (1 : Plane →ᵇ ℝ)).1
    simpa only [f, BoundedContinuousFunction.coe_one, Pi.one_apply, mul_one] using h
  have hMean := flat_cc_pairing_integrable_mean ϑ P Z hZ
    (hr.trans (hrs.trans hst).le) htu g hg
  have hLast : (∫⁻ ω, ∫⁻ p, ENNReal.ofReal (g p.2) ∂Z t u ω ∂P) ≠ ∞ := by
    rw [hMean.1]
    exact ENNReal.ofReal_ne_top
  have hEst := condExp_real_normalized_threeBlock_chain_le P (fun k : Fin 3 => B k)
    (fun k => (hB k (by omega)).1) (fun k => (hB k (by omega)).2.1) hind f g hf
    g.continuous.measurable (fun y => heatKernel_nonneg hδ.le (y - x)) hg
    (sub_pos.2 hst) (by positivity : 0 < 1 / ((n : ℝ) + 1))
    (isCriticalSHF_bind_eq_heatBlock ϑ P Z hZ (hr.trans hrs.le) hst) hLast hnum hden
  simpa [B, f, heatMollifier, shfPairing] using hEst

end Critical2DKPZ.NonGaussian

end
