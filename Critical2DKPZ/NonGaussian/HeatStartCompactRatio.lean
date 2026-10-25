/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.NormalizedTwoBlockMean
public import Critical2DKPZ.NonGaussian.DenseThreeBlockData
public import Critical2DKPZ.NonGaussian.DenseThreeBlockLimit
public import Critical2DKPZ.NonGaussian.MeanMeasure
public import Critical2DKPZ.NonGaussian.NonnegativeFatou
import Critical2DKPZ.SHF.Tsai.ChainPairingLinearity
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-! # The normalized heat-start mean for a compact terminal bounded by one -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.NonGaussian

/-- The normalized heat-start ratio against a compact continuous terminal valued in `[0,1]`
is integrable and has expectation at most one. -/
theorem integral_heatStart_cc_div_le_one_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hdense : DenseSHFAt ϑ P Z)
    {r s t δ : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) (hδ : 0 < δ) (x : Plane)
    (g : C_c(Plane, ℝ)) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    Integrable (fun ω => shfPairing Z r t (fun y => heatKernel δ (y - x)) g ω /
      shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω) P ∧
    (∫ ω, shfPairing Z r t (fun y => heatKernel δ (y - x)) g ω /
      shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω ∂P) ≤ 1 := by
  let B (k : ℕ) := if k = 0 then Z r s else Z s t
  let τ (k : ℕ) := if k = 0 then s - r else t - s
  let f : Plane → ℝ := fun y => heatKernel δ (y - x)
  let A (ω : Ω) := ∫ p, f p.1 ∂Z r s ω
  let F (n : ℕ) (ω : Ω) := (∫ p, f p.1 * g p.2
    ∂chainProduct (fun k => B k ω) (fun _ => heatMollifier n) 1) / A ω
  let G (ω : Ω) := (∫ p, f p.1 * g p.2 ∂Z r t ω) / A ω
  have hData := threeConsecutive_moments_independent_of_dense ϑ P Z hdense hr hrs hst
    (by linarith : t < t + 1)
  have hB (k : ℕ) (hk : k ≤ 1) :
      HasDeltaBoseMoments (ϑ - Real.eulerMascheroniConstant) (τ k) P (B k) := by
    interval_cases k
    · simpa [B, τ] using hData.1.1
    · simpa [B, τ] using hData.1.2.1
  have hτ (k : ℕ) (hk : k ≤ 1) : 0 < τ k := by
    interval_cases k <;> simp only [τ] <;> split_ifs <;> linarith only [hrs, hst]
  have hind : iIndepFun (fun k : Fin 2 => B k) P := by
    have h := hData.2.precomp (Fin.castSucc_injective 2)
    convert h using 1
    funext k
    fin_cases k <;> rfl
  have hind01 : IndepFun (Z r s) (Z s t) P := hData.2.indepFun (by decide : (0 : Fin 3) ≠ 1)
  have hf : Measurable f := (measurable_heatKernel δ).comp (measurable_id.sub measurable_const)
  have hfL2 : MemLp f 2 := by
    simpa only [f, Function.comp_def, sub_eq_add_neg] using
      (memLp_heatKernel hδ).comp_measurePreserving (measurePreserving_add_right volume (-x))
  have hgL2 : MemLp (g : Plane → ℝ) 2 := g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hden : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => f p.1) (Z r s ω) := by
    have h := (SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hr hrs hδ x
      (1 : Plane →ᵇ ℝ)).1
    simpa only [f, BoundedContinuousFunction.coe_one, Pi.one_apply, mul_one] using h
  have hEst (n : ℕ) : Integrable (F n) P ∧ (∫ ω, F n ω ∂P) ≤ 1 := by
    have hnum := ae_integrable_chainPairing 1 τ hτ B hB hind (fun _ => heatMollifier)
      (fun _ => isL2ApplicableMollifier_heatMollifier) n f g hfL2 hgL2
    have h := integral_normalized_twoBlock_chain_le_one P (Z r s) (Z s t)
      (hB 0 (by omega)).1 (hB 1 (by omega)).1 (hB 0 (by omega)).2.1 (hB 1 (by omega)).2.1
      hind01 f g hf g.continuous.measurable (fun y => heatKernel_nonneg hδ.le (y - x)) hg0 hg1
      (sub_pos.2 hst) (by positivity : 0 < 1 / ((n : ℝ) + 1))
      (isCriticalSHF_bind_eq_heatBlock ϑ P Z hZ (hr.trans hrs.le) hst) hnum hden
    simpa only [F, A, B, heatMollifier, ite_apply] using h
  have hF0 (n : ℕ) : 0 ≤ᵐ[P] F n := Eventually.of_forall fun ω =>
    div_nonneg (integral_nonneg fun p : Plane × Plane =>
      mul_nonneg (heatKernel_nonneg hδ.le (p.1 - x)) (hg0 p.2))
      (integral_nonneg fun p : Plane × Plane => heatKernel_nonneg hδ.le (p.1 - x))
  have hLimit := tendstoInMeasure_twoBlock_heat_chain_of ϑ P Z hdense hr hrs hst f g hfL2 hgL2
  obtain ⟨ns, _, hns⟩ := hLimit.exists_seq_tendsto_ae
  have hRatioLimit : ∀ᵐ ω ∂P, Tendsto (fun n => F (ns n) ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hns] with ω hω
    exact hω.div_const (A ω)
  let η : Kernel (Measure (Plane × Plane)) (Plane × Plane) := ⟨id, measurable_id⟩
  have hN : Measurable (fun μ : Measure (Plane × Plane) => ∫ p, f p.1 * g p.2 ∂μ) :=
    (((hf.comp measurable_fst).mul (g.continuous.measurable.comp measurable_snd)).stronglyMeasurable.integral_kernel
      (κ := η)).measurable
  have hA : Measurable (fun μ : Measure (Plane × Plane) => ∫ p, f p.1 ∂μ) :=
    ((hf.comp measurable_fst).stronglyMeasurable.integral_kernel (κ := η)).measurable
  have hG : AEMeasurable G P :=
    ((hN.comp (hZ.1 r t hr (hrs.trans hst))).div (hA.comp (hZ.1 r s hr hrs))).aemeasurable
  have hFatou := integrable_and_integral_le_of_ae_tendsto_nonneg P (fun n => F (ns n))
    (fun n => (hEst (ns n)).1) (fun n => hF0 (ns n)) G hG hRatioLimit 1 zero_le_one
    (fun n => (hEst (ns n)).2)
  simpa only [G, A, f, shfPairing, mul_one] using hFatou.2

end Critical2DKPZ.NonGaussian

end
