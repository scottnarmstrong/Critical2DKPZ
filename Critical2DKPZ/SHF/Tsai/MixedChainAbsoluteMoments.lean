/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedChainMoments
public import Critical2DKPZ.SHF.Tsai.MixedChainFormBounds
public import Critical2DKPZ.SHF.Tsai.PositiveKernelForms

/-! # Absolute moments of partially heat-replaced chain pairings

The exact positive mixed moment identity and a finite form bound give
finite absolute product moments on measurable planar L2 endpoint tests.
The form constant is uniform over the connector approximation index.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The positive product of absolute chain pairings has finite expectation on measurable `L²` tests. -/
theorem lintegral_prod_abs_mixedChainPairings_lt_top {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P) {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (S : Finset (Fin n))
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) (ℓ : ℕ)
    (g g' : Fin n → Plane → ℝ) (hgm : ∀ i, Measurable (g i)) (hg'm : ∀ i, Measurable (g' i))
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    (∫⁻ ω, ∏ i, (∫⁻ p, ENNReal.ofReal |g i p.1| * ENNReal.ofReal |g' i p.2|
      ∂chainProduct (if i ∈ S then (fun k => B k ω) else
        Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w i k ℓ) K) ∂P) < ⊤ := by
  rw [lintegral_prod_chainProduct_update_heat_eq K j hj τ hτ B hB hind hn1 hn S (fun i k => w i k ℓ)
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
  obtain ⟨C, hCfin, hC⟩ := exists_formBound_mixedChainKernel_uniform θ K j hj τ hτ S w hw
  have hchain := measurable_chainKernel
    (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S))
    (measurable_momentKernel_update_mixed n θ τ j S) (fun i k => w i k ℓ)
    (fun i k => ((hw i k).2.1 ℓ).measurable) K
  rw [lintegral_configurationKernel_ofReal hchain hCfin (hC ℓ) F G hF hG hF0 hG0]
  exact ENNReal.ofReal_lt_top

end Critical2DKPZ.SHF.Tsai

end
