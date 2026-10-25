/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.PositiveChainMoments
public import Critical2DKPZ.SHF.Tsai.ChainMomentFormBounds
public import Critical2DKPZ.SHF.Tsai.PositiveKernelForms
public import Critical2DKPZ.SHF.Tsai.ChainPairingMeasurability

/-! # Absolute moments and integrability of measurable chain tests

The positive chain moment formula and a finite form bound give finite absolute
moments. The norm bound for the actual integral then establishes integrability
of products of real pairings. The one-factor case gives absolute integrability
inside the random chain almost surely.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The positive product of absolute chain pairings has finite expectation on measurable `L²` tests. -/
theorem lintegral_prod_abs_chainPairings_lt_top {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hgm : ∀ i, Measurable (g i)) (hg'm : ∀ i, Measurable (g' i))
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    (∫⁻ ω, ∏ i, (∫⁻ p, ENNReal.ofReal |g i p.1| * ENNReal.ofReal |g' i p.2|
      ∂chainProduct (fun k => B k ω) (fun k => w i k ℓ) K) ∂P) < ⊤ := by
  rw [lintegral_prod_chainProduct_eq K τ hτ B hB hind hn1 hn (fun i k => w i k ℓ)
    (fun i k => (hw i k).1 ℓ) (fun i k => ((hw i k).2.1 ℓ).measurable)
    (fun i x => ENNReal.ofReal |g i x|) (fun i x => ENNReal.ofReal |g' i x|)
    (fun i => by simpa only [Real.norm_eq_abs] using (hgm i).norm.ennreal_ofReal)
    (fun i => by simpa only [Real.norm_eq_abs] using (hg'm i).norm.ennreal_ofReal)]
  let F (x : Configuration n) := ∏ i, |g i (x i)|
  let G (y : Configuration n) := ∏ i, |g' i (y i)|
  have hF : MemLp F 2 := memLp_configuration_tensor (fun i x => |g i x|) (fun i => (hg i).abs)
  have hG : MemLp G 2 := memLp_configuration_tensor (fun i x => |g' i x|) (fun i => (hg' i).abs)
  have hF0 (x) : 0 ≤ F x := Finset.prod_nonneg (fun i _ => abs_nonneg _)
  have hG0 (y) : 0 ≤ G y := Finset.prod_nonneg (fun i _ => abs_nonneg _)
  have hprodF (x : Configuration n) : (∏ i, ENNReal.ofReal |g i (x i)|) = ENNReal.ofReal (F x) :=
    (ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg (g i (x i)))).symm
  have hprodG (y : Configuration n) : (∏ i, ENNReal.ofReal |g' i (y i)|) = ENNReal.ofReal (G y) :=
    (ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg (g' i (y i)))).symm
  simp_rw [hprodF, hprodG]
  obtain ⟨C, hCfin, hC⟩ := exists_formBound_chainMomentKernel_uniform θ K τ hτ w hw
  have hKm (k) : Measurable (Function.uncurry (momentKernel n θ (τ k))) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  have hchain := measurable_chainKernel (fun k => momentKernel n θ (τ k)) hKm
    (fun i k => w i k ℓ) (fun i k => ((hw i k).2.1 ℓ).measurable) K
  rw [lintegral_configurationKernel_ofReal hchain hCfin (hC ℓ) F G hF hG hF0 hG0]
  exact ENNReal.ofReal_lt_top



end Critical2DKPZ.SHF.Tsai

end
