/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedChainMomentPaths
public import Critical2DKPZ.SHF.Tsai.KernelChainPaths
public import Critical2DKPZ.SHF.Tsai.ChainKernelLimits

/-! # Exact mixed moments of chains with a partial heat replacement

Independent endpoint tuple means evaluate the stochastic product as a kernel
path integral. The deterministic path recursion identifies that integral
with the literal chain kernel whose selected block is `mixedBlockKernel`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The exact positive mixed chain moment identity of dense-time uniqueness. -/
theorem lintegral_prod_chainProduct_update_heat_eq {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (S : Finset (Fin n)) (w : Fin n → ℕ → Plane → ℝ)
    (hw0 : ∀ i k x, 0 ≤ w i k x) (hwm : ∀ i k, Measurable (w i k))
    (f f' : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hf' : ∀ i, Measurable (f' i)) :
    ∫⁻ ω, ∏ i, (∫⁻ p, f i p.1 * f' i p.2 ∂(chainProduct
        (if i ∈ S then (fun k => B k ω) else Function.update (fun k => B k ω) j (heatBlock (τ j)))
        (w i) K)) ∂P =
      ∫⁻ x, ∫⁻ y, (∏ i, f i (x i)) *
        chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S))
          w K x y * ∏ i, f' i (y i) := by
  classical
  have _ := hw0
  let G (x : Configuration n) := ∏ i, f i (x i)
  let F (y : Configuration n) := ∏ i, f' i (y i)
  have hG : Measurable G := Finset.measurable_prod _ (fun i _ => (hf i).comp (measurable_pi_apply i))
  have hF : Measurable F := Finset.measurable_prod _ (fun i _ => (hf' i).comp (measurable_pi_apply i))
  have hH (i) : Measurable (fun p : Plane × Plane => f i p.1 * f' i p.2) :=
    ((hf i).comp measurable_fst).mul ((hf' i).comp measurable_snd)
  let L (k : ℕ) := Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S) k
  have hLm (k) : Measurable (Function.uncurry (L k)) := by
    by_cases hk : k = j
    · subst k
      simpa only [L, Function.update_self] using measurable_mixedBlockKernel n θ (τ j) S
    · have hL : L k = momentKernel n θ (τ k) := Function.update_of_ne hk _ _
      rw [hL]
      exact Measurable.comp
        (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
          momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
        (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
        (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  let Lb k := if k ≤ K then L k else 0
  have hLbm (k) : Measurable (Function.uncurry (Lb k)) := by
    by_cases hk : k ≤ K
    · simpa only [Lb, ite_eq_left hk] using hLm k
    · simp only [Lb, ite_eq_right hk]
      exact measurable_const
  have hsf (k) : SigmaFinite (volume.withDensity (Function.uncurry (Lb k))) := by
    by_cases hk : k ≤ K
    · have hbound : ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ FormBound volume volume (Lb k) c := by
        by_cases hkj : k = j
        · subst k
          have heq : Lb j = mixedBlockKernel n θ (τ j) S := by
            simp only [Lb, ite_eq_left hj, L, Function.update_self]
          rw [heq]
          exact exists_formBound_mixedBlockKernel n S θ (hτ j hj)
        · obtain ⟨C, rate, _, hC⟩ := exists_formBound_momentKernel n θ
          refine ⟨ENNReal.ofReal (C * Real.exp (rate * τ k) * min (τ k) 1 ^ (-(n : ℝ))),
            ENNReal.ofReal_ne_top, ?_⟩
          have heq : Lb k = momentKernel n θ (τ k) := by
            simp only [Lb, ite_eq_left hk, L, Function.update_of_ne hkj]
          rw [heq]
          exact hC θ le_rfl (τ k) (hτ k hk)
      obtain ⟨c, hc, hbound⟩ := hbound
      let : IsLocallyFiniteMeasure (volume.withDensity (Function.uncurry (Lb k))) :=
        locallyFinite_kernelMeasure (hLbm k) hc hbound
      infer_instance
    · rw [show Lb k = 0 from ite_eq_right hk]
      change SigmaFinite (volume.withDensity (0 : Configuration n × Configuration n → ℝ≥0∞))
      rw [withDensity_zero]
      infer_instance
  let : ∀ k, SigmaFinite (volume.withDensity (Function.uncurry (Lb k))) := hsf
  have hp (k) (hk : k ≤ K) : Lb k = L k := ite_eq_left hk
  have hμ : (fun k : Fin (K + 1) => volume.withDensity (Function.uncurry (Lb k))) =
      fun k : Fin (K + 1) => volume.withDensity (Function.uncurry (L k)) := by
    funext k
    rw [hp k (Nat.le_of_lt_succ k.is_lt)]
  have hchain := chainKernel_congr_prefix K hp w
  have hpath := lintegral_configurationChainPathTest_eq K Lb hLbm w hwm G F hG hF
  rw [hμ, hchain] at hpath
  calc
    _ = ∫⁻ p, tupleChainPathTest K w (fun i q => f i q.1 * f' i q.2) p
        ∂Measure.pi (fun k : Fin (K + 1) => volume.withDensity (Function.uncurry (L k))) :=
      lintegral_prod_chainProduct_update_heat_eq_lintegral_momentPaths
        K j hj τ hτ B hB hind hn1 hn S w hwm _ hH
    _ = ∫⁻ p, configurationChainPathTest K w G F p
        ∂Measure.pi (fun k : Fin (K + 1) => volume.withDensity (Function.uncurry (L k))) := by
      apply lintegral_congr
      intro p
      exact tupleChainPathTest_tensor_eq K w f f' p
    _ = _ := hpath

end Critical2DKPZ.SHF.Tsai

end
