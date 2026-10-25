/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainMomentPaths
public import Critical2DKPZ.SHF.Tsai.KernelChainPaths
public import Critical2DKPZ.SHF.Tsai.ChainKernelLimits

/-! For independent blocks with delta-Bose moments, products of up to four nonnegative chain
pairings have expectations given by the chain moment kernel. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The expected product of nonnegative chain pairings equals its integral against the chain moment kernel. -/
theorem lintegral_prod_chainProduct_eq {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (w : Fin n → ℕ → Plane → ℝ)
    (hw0 : ∀ i k x, 0 ≤ w i k x) (hwm : ∀ i k, Measurable (w i k))
    (f f' : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hf' : ∀ i, Measurable (f' i)) :
    ∫⁻ ω, ∏ i, (∫⁻ p, f i p.1 * f' i p.2 ∂(chainProduct (fun k => B k ω) (w i) K)) ∂P =
      ∫⁻ x, ∫⁻ y, (∏ i, f i (x i)) * chainMomentKernel n θ τ w K x y * ∏ i, f' i (y i) := by
  classical
  -- Nonnegative connector weights are unchanged by taking their positive parts.
  have _ := hw0
  let G (x : Configuration n) := ∏ i, f i (x i)
  let F (y : Configuration n) := ∏ i, f' i (y i)
  have hG : Measurable G := Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  have hF : Measurable F := Finset.measurable_prod _ (fun i _ => (hf' i).comp (measurable_pi_apply i))
  have hH (i) : Measurable (fun p : Plane × Plane => f i p.1 * f' i p.2) :=
    ((hf i).comp measurable_fst).mul ((hf' i).comp measurable_snd)
  let Lb k := if k ≤ K then momentKernel n θ (τ k) else 0
  have hLm (k) : Measurable (Function.uncurry (Lb k)) := by
    by_cases hk : k ≤ K
    · simp only [Lb, ite_eq_left hk]
      exact Measurable.comp
        (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
          momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
        (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
        (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
    · simp only [Lb, ite_eq_right hk]
      exact measurable_const
  have hsf (k) : SigmaFinite (volume.withDensity (Function.uncurry (Lb k))) := by
    by_cases hk : k ≤ K
    · obtain ⟨C, rate, _, hC⟩ := exists_formBound_momentKernel n θ
      have hbound : FormBound volume volume (Lb k)
          (ENNReal.ofReal (C * Real.exp (rate * τ k) * min (τ k) 1 ^ (-(n : ℝ)))) := by
        simpa only [Lb, ite_eq_left hk] using hC θ le_rfl (τ k) (hτ k hk)
      let : IsLocallyFiniteMeasure (volume.withDensity (Function.uncurry (Lb k))) :=
        locallyFinite_kernelMeasure (hLm k) ENNReal.ofReal_ne_top hbound
      infer_instance
    · rw [show Lb k = 0 from ite_eq_right hk]
      change SigmaFinite (volume.withDensity (0 : Configuration n × Configuration n → ℝ≥0∞))
      rw [withDensity_zero]
      infer_instance
  let : ∀ k, SigmaFinite (volume.withDensity (Function.uncurry (Lb k))) := hsf
  have hp (k) (hk : k ≤ K) : Lb k = momentKernel n θ (τ k) := ite_eq_left hk
  have hμ : (fun k : Fin (K + 1) => volume.withDensity (Function.uncurry (Lb k))) =
      fun k : Fin (K + 1) => volume.withDensity (Function.uncurry (momentKernel n θ (τ k))) := by
    funext k
    rw [hp k (Nat.le_of_lt_succ k.is_lt)]
  have hchain := chainKernel_congr_prefix K hp w
  have hpath := lintegral_configurationChainPathTest_eq K Lb hLm w hwm G F hG hF
  rw [hμ, hchain] at hpath
  calc
    _ = ∫⁻ p, tupleChainPathTest K w (fun i q => f i q.1 * f' i q.2) p
        ∂Measure.pi (fun k : Fin (K + 1) =>
          volume.withDensity (Function.uncurry (momentKernel n θ (τ k)))) :=
      lintegral_prod_chainProduct_eq_lintegral_momentPaths K τ hτ B hB hind hn1 hn w hwm _ hH
    _ = ∫⁻ p, configurationChainPathTest K w G F p
        ∂Measure.pi (fun k : Fin (K + 1) =>
          volume.withDensity (Function.uncurry (momentKernel n θ (τ k)))) := by
      apply lintegral_congr
      intro p
      exact tupleChainPathTest_tensor_eq K w f f' p
    _ = _ := hpath

end Critical2DKPZ.SHF.Tsai

end
