/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.DenseConditionalChains
public import Critical2DKPZ.NonGaussian.DenseThreeBlockLimit
public import Critical2DKPZ.NonGaussian.ConditionalFatou
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

/-! # The time-separated conditional heat-start ratio bound -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai Critical2DKPZ.LocalSobolev
open scoped CompactlySupported BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- For `0 ≤ r < s < t < u`, the ratio `Z_{r,u}(g_δ^{(x)},g) / Z_{r,s}(g_δ^{(x)},1)`
is integrable and its conditional expectation given the increments on `[r,s]` and `[t,u]`
is at most `(2π(t-s))⁻¹ Z_{t,u}(1,g)`. -/
theorem condExp_heatStart_div_le_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (_hsym : ShfSymmetriesAt ϑ P Z) (hdense : DenseSHFAt ϑ P Z)
    {r s t u δ : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) (htu : t < u) (hδ : 0 < δ) (x : Plane)
    (g : C_c(Plane, ℝ)) (hg : ∀ y, 0 ≤ g y) :
    Integrable (fun ω => shfPairing Z r u (fun y => heatKernel δ (y - x)) g ω /
      shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω) P ∧
    P[fun ω => shfPairing Z r u (fun y => heatKernel δ (y - x)) g ω /
        shfPairing Z r s (fun y => heatKernel δ (y - x)) (fun _ => 1) ω | MeasurableSpace.comap (Z r s) inferInstance ⊔
        MeasurableSpace.comap (Z t u) inferInstance]
      ≤ᵐ[P] fun ω => (2 * Real.pi * (t - s))⁻¹ * shfPairing Z t u (fun _ => 1) g ω := by
  let ambient : MeasurableSpace Ω := inferInstance
  let f : Plane → ℝ := fun y => heatKernel δ (y - x)
  let A : Ω → ℝ := fun ω => ∫ p, f p.1 ∂Z r s ω
  let F (n : ℕ) (ω : Ω) := (∫ p, f p.1 * g p.2
    ∂chainProduct (fun k => if k = 0 then Z r s ω else if k = 1 then Z s t ω else Z t u ω)
      (fun _ => heatMollifier n) 2) / A ω
  let G : Ω → ℝ := fun ω => (∫ p, f p.1 * g p.2 ∂Z r u ω) / A ω
  let Y : Ω → ℝ := fun ω => (2 * Real.pi * (t - s))⁻¹ * ∫ p, g p.2 ∂Z t u ω
  let m : MeasurableSpace Ω := MeasurableSpace.comap (Z r s) inferInstance ⊔
    MeasurableSpace.comap (Z t u) inferInstance
  let : MeasurableSpace Ω := ambient
  have hmiddle : 0 < t - s := sub_pos.2 hst
  have htu0 : 0 ≤ t := hr.trans (hrs.trans hst).le
  have hru : r < u := hrs.trans (hst.trans htu)
  have hf : Measurable f := (measurable_heatKernel δ).comp (measurable_id.sub measurable_const)
  have hfL2 : MemLp f 2 := by
    simpa only [f, Function.comp_def, sub_eq_add_neg] using
      (memLp_heatKernel hδ).comp_measurePreserving (measurePreserving_add_right volume (-x))
  have hgL2 : MemLp (g : Plane → ℝ) 2 := g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hApprox (n : ℕ) : Integrable (F n) P ∧ P[F n | m] ≤ᵐ[P] Y := by
    simpa only [F, A, Y, f, m, shfPairing, one_mul, mul_one] using
      condExp_heatStart_chain_div_le_of ϑ P Z hZ hdense hr hrs hst htu hδ x g hg n
  have hF0 (n : ℕ) : 0 ≤ᵐ[P] F n := Eventually.of_forall fun ω =>
    div_nonneg (integral_nonneg fun p : Plane × Plane => mul_nonneg (heatKernel_nonneg hδ.le (p.1 - x)) (hg p.2))
      (integral_nonneg fun p : Plane × Plane => heatKernel_nonneg hδ.le (p.1 - x))
  have hLimit := tendstoInMeasure_threeBlock_heat_chain_of ϑ P Z hdense hr hrs hst htu f g hfL2 hgL2
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
    ((hN.comp (hZ.1 r u hr hru)).div (hA.comp (hZ.1 r s hr hrs))).aemeasurable
  have hJ : Measurable (fun μ : Measure (Plane × Plane) => ∫ p, g p.2 ∂μ) :=
    ((g.continuous.measurable.comp measurable_snd).stronglyMeasurable.integral_kernel (κ := η)).measurable
  have hMean := flat_cc_pairing_integrable_mean ϑ P Z hZ htu0 htu g hg
  have hY : Integrable Y P := by
    simpa only [Y, shfPairing, one_mul] using hMean.2.2.1.const_mul ((2 * Real.pi * (t - s))⁻¹)
  have hY0 : 0 ≤ᵐ[P] Y := Eventually.of_forall fun ω =>
    mul_nonneg (inv_nonneg.mpr (by positivity)) (integral_nonneg fun p : Plane × Plane => hg p.2)
  have hZm : Measurable[m] (Z t u) := Measurable.of_comap_le le_sup_right
  have hYm : StronglyMeasurable[m] Y := (measurable_const.mul (hJ.comp hZm)).stronglyMeasurable
  have hm : m ≤ ‹MeasurableSpace Ω› := sup_le (hZ.1 r s hr hrs).comap_le (hZ.1 t u htu0 htu).comap_le
  have hConclusion := integrable_and_condExp_le_of_ae_tendsto_nonneg P m hm
    (fun n => F (ns n)) (fun n => (hApprox (ns n)).1) (fun n => hF0 (ns n))
    G hG hRatioLimit Y hY hY0 hYm (fun n => (hApprox (ns n)).2)
  simpa only [G, A, Y, f, m, shfPairing, one_mul, mul_one] using hConclusion

end Critical2DKPZ.NonGaussian

end
