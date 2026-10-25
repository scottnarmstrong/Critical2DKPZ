/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConditionalChainAbsoluteMoments
public import Critical2DKPZ.SHF.Tsai.ChainBlockMeasurability
public import Critical2DKPZ.SHF.Tsai.PositiveChainBlockMeasurability
import Critical2DKPZ.SHF.Tsai.MomentKernelMeasureFiniteness

/-! # Integrability of the conditional joint endpoint tests

The positive conditional moment bounds dominate the absolute values of the
signed endpoint tests. Joint measurability and the moment-kernel density
therefore give actual integrability over the independent outer samples and
the selected block's full endpoint moment measure.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Conditional selected-block endpoint products are integrable against their full joint moment measure. -/
theorem integrable_prod_chainBlockTests {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ) (j : Fin (K + 1))
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hlf : ∀ k ≤ K, ∀ ω, IsLocallyFiniteMeasure (B k ω))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hgm : ∀ i, Measurable (g i)) (hg'm : ∀ i, Measurable (g' i))
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    Integrable (fun aq : (Fin K → Ω) × (Configuration n × Configuration n) =>
      ∏ i, chainBlockTest K j (outerCopyBlock K j B aq.1) (fun k => w i k ℓ)
        (fun p => g i p.1 * g' i p.2) (aq.2.1 i, aq.2.2 i))
      ((Measure.pi (fun _ : Fin K => P)).prod
        (volume.withDensity (Function.uncurry (momentKernel n θ (τ j))))) := by
  classical
  let Q := Measure.pi (fun _ : Fin K => P)
  let ν := volume.withDensity (Function.uncurry (momentKernel n θ (τ j)))
  let C (k : ℕ) (a : Fin K → Ω) := outerCopyBlock K j B a k
  have hCm (k) (hk : k ≤ K) : Measurable (C k) :=
    measurable_outerCopyBlock K j B (fun k hk => (hB k hk).1) k hk
  have hClf (a : Fin K → Ω) (k) (_ : k ≤ K) : IsLocallyFiniteMeasure (C k a) :=
    locallyFinite_outerCopyBlock K j B hlf a k
  let F (i : Fin n) (p : Plane × Plane) := g i p.1 * g' i p.2
  let A (i : Fin n) (p : Plane × Plane) := ENNReal.ofReal |g i p.1| * ENNReal.ofReal |g' i p.2|
  have hF (i) : Measurable (F i) := ((hgm i).comp measurable_fst).mul ((hg'm i).comp measurable_snd)
  have hA (i) : Measurable (A i) := by
    simpa only [A, Real.norm_eq_abs, Function.comp_def, Pi.mul_def] using
      (((hgm i).norm.ennreal_ofReal.comp measurable_fst).mul
        ((hg'm i).norm.ennreal_ofReal.comp measurable_snd))
  have hFA (i) : (fun p => ENNReal.ofReal |F i p|) = A i := by
    funext p
    exact (congrArg ENNReal.ofReal (abs_mul _ _)).trans (ENNReal.ofReal_mul (abs_nonneg _))
  let H (aq : (Fin K → Ω) × (Configuration n × Configuration n)) :=
    ∏ i, chainBlockTest K j (C · aq.1) (fun k => w i k ℓ) (F i) (aq.2.1 i, aq.2.2 i)
  let D (aq : (Fin K → Ω) × (Configuration n × Configuration n)) :=
    ∏ i, positiveChainBlockTest K j (C · aq.1) (fun k => w i k ℓ) (A i) (aq.2.1 i, aq.2.2 i)
  have hindex (i : Fin n) : Measurable (fun aq : (Fin K → Ω) × (Configuration n × Configuration n) =>
      (aq.1, (aq.2.1 i, aq.2.2 i))) := measurable_fst.prodMk
        (((measurable_pi_apply i).comp measurable_snd.fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd.snd))
  have hHm : Measurable H := Finset.measurable_prod _ fun i _ =>
    (measurable_chainBlockTest K j C hCm hClf _ (fun k => ((hw i k).2.1 ℓ).measurable) _ (hF i)).comp
      (hindex i)
  have hDm : Measurable D := Finset.measurable_prod _ fun i _ =>
    (measurable_positiveChainBlockTest K j C hCm hClf _ (fun k => ((hw i k).2.1 ℓ).measurable) _ (hA i)).comp
      (hindex i)
  have hKm : Measurable (Function.uncurry (momentKernel n θ (τ j))) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, τ j), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  let : IsLocallyFiniteMeasure ν :=
    locallyFinite_momentKernelMeasure n θ (hτ j (Nat.le_of_lt_succ j.is_lt))
  have hDfinite : (∫⁻ aq, D aq ∂Q.prod ν) < ⊤ := by
    rw [lintegral_prod _ hDm.aemeasurable]
    have heq (a : Fin K → Ω) : (∫⁻ q, D (a, q) ∂ν) =
        ∫⁻ q : Configuration n × Configuration n, momentKernel n θ (τ j) q.1 q.2 * D (a, q) :=
      lintegral_withDensity_eq_lintegral_mul volume hKm
        (hDm.comp (measurable_const.prodMk measurable_id))
    simp_rw [heq]
    exact lintegral_prod_positiveChainBlockTests_lt_top P K j τ hτ B hB hlf hn1 hn w hw ℓ
      g g' hgm hg'm hg hg'
  have hnorm (aq : (Fin K → Ω) × (Configuration n × Configuration n)) : ‖H aq‖ₑ ≤ D aq := by
    rw [Real.enorm_eq_ofReal_abs, Finset.abs_prod,
      ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg _)]
    apply Finset.prod_le_prod
    intro i _
    simpa only [hFA i] using ofReal_abs_chainBlockTest_le K j (C · aq.1) (fun k => w i k ℓ)
      (F i) (aq.2.1 i, aq.2.2 i)
  refine ⟨hHm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (lintegral_mono hnorm).trans_lt hDfinite

end Critical2DKPZ.SHF.Tsai

end
