/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockMoments
public import Critical2DKPZ.SHF.DeltaBose.FormBounds
import Critical2DKPZ.SHF.DeltaBose.Measurability

/-! # Positive kernels for chain moments

Block kernels compose through particle-dependent connector weights, retaining mixed
moments from different mollifier families. The nonnegative kernel integrals are defined
even when their values are infinite.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Block kernels compose through the connector weights `∏ᵢ wᵢ k (zᵢ - z'ᵢ)`, with the orientation of `smoothedProductMeasure`, as in Tsai (2024), equation (2.33). -/
def chainKernel (n : ℕ) (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (w : Fin n → ℕ → Plane → ℝ) : ℕ → Configuration n → Configuration n → ℝ≥0∞
  | 0 => Kb 0
  | K + 1 => fun x y => ∫⁻ z, ∫⁻ z', chainKernel n Kb w K x z *
      (∏ i, ENNReal.ofReal (w i K (z i - z' i))) * Kb (K + 1) z' y

/-- The connector-free composition of the block kernels. -/
def chainKernelLimit (n : ℕ) (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞) :
    ℕ → Configuration n → Configuration n → ℝ≥0∞
  | 0 => Kb 0
  | K + 1 => fun x y => ∫⁻ z, chainKernelLimit n Kb K x z * Kb (K + 1) z y

/-- The chain kernel of the delta-Bose blocks, `E ∏ᵢ (chain with connectors wᵢ)`. -/
abbrev chainMomentKernel (n : ℕ) (θ : ℝ) (τ : ℕ → ℝ) (w : Fin n → ℕ → Plane → ℝ) :
    ℕ → Configuration n → Configuration n → ℝ≥0∞ :=
  chainKernel n (fun k => momentKernel n θ (τ k)) w

/-- The block kernel when the factors in `S` see a delta-Bose block and the others its mean `heatBlock`:
`Q^{[S]}(τ) ⊗ P^{[n] ∖ S}(τ)`. Tsai's `centeredMomentKernel` is `∑_S (−1)^{n−|S|}` of these. -/
def mixedBlockKernel (n : ℕ) (θ τ : ℝ) (S : Finset (Fin n)) (x y : Configuration n) : ℝ≥0∞ :=
  momentKernel S.card θ τ (fun i => x (S.orderEmbOfFin rfl i)) (fun i => y (S.orderEmbOfFin rfl i)) *
    ∏ i ∈ Sᶜ, ENNReal.ofReal (heatKernel τ (y i - x i))

/-- Connector-free compositions of measurable block kernels are measurable. -/
theorem measurable_chainKernelLimit {n : ℕ}
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k))) (K : ℕ) :
    Measurable (Function.uncurry (chainKernelLimit n Kb K)) := by
  induction K with
  | zero => exact hKb 0
  | succ K ih => exact measurable_spatialKernelComp volume ih (hKb (K + 1))

/-- The positive kernels with measurable connectors are measurable in their two endpoints. -/
theorem measurable_chainKernel {n : ℕ}
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k)))
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k)) (K : ℕ) :
    Measurable (Function.uncurry (chainKernel n Kb w K)) := by
  induction K with
  | zero => exact hKb 0
  | succ K ih =>
    have hm : Measurable (fun q : ((Configuration n × Configuration n) × Configuration n) × Configuration n =>
        chainKernel n Kb w K q.1.1.1 q.1.2 *
          (∏ i, ENNReal.ofReal (w i K (q.1.2 i - q.2 i))) * Kb (K + 1) q.2 q.1.1.2) := by
      apply Measurable.mul
      · apply Measurable.mul
        · exact Measurable.comp (g := Function.uncurry (chainKernel n Kb w K))
            (f := fun q : ((Configuration n × Configuration n) × Configuration n) × Configuration n =>
              (q.1.1.1, q.1.2)) ih (by fun_prop)
        · apply Finset.measurable_prod
          intro i _
          exact ((hw i K).comp
            (((measurable_pi_apply i).comp measurable_fst.snd).sub
              ((measurable_pi_apply i).comp measurable_snd))).ennreal_ofReal
      · exact Measurable.comp (g := Function.uncurry (Kb (K + 1)))
          (f := fun q : ((Configuration n × Configuration n) × Configuration n) × Configuration n =>
            (q.2, q.1.1.2)) (hKb (K + 1)) (by fun_prop)
    exact hm.lintegral_prod_right'.lintegral_prod_right'


/-- The actual delta-Bose chain moment kernel is jointly measurable in its endpoints. -/
theorem measurable_chainMomentKernel (n : ℕ) (θ : ℝ) (τ : ℕ → ℝ)
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k)) (K : ℕ) :
    Measurable (Function.uncurry (chainMomentKernel n θ τ w K)) := by
  apply measurable_chainKernel _ _ w hw K
  intro k
  exact Measurable.comp
    (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
      momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
    (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
    (measurable_momentKernel n) (measurable_const.prodMk measurable_id)

/-- The mixed heat/delta-Bose block kernel is measurable at its two endpoints. -/
theorem measurable_mixedBlockKernel (n : ℕ) (θ τ : ℝ) (S : Finset (Fin n)) :
    Measurable (Function.uncurry (mixedBlockKernel n θ τ S)) := by
  have hx : Measurable (fun q : Configuration n × Configuration n =>
      fun i : Fin S.card => q.1 (S.orderEmbOfFin rfl i)) :=
    Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_fst
  have hy : Measurable (fun q : Configuration n × Configuration n =>
      fun i : Fin S.card => q.2 (S.orderEmbOfFin rfl i)) :=
    Measurable.of_eval fun i => (measurable_pi_apply _).comp measurable_snd
  have hK : Measurable (fun q : Configuration n × Configuration n =>
      momentKernel S.card θ τ (fun i => q.1 (S.orderEmbOfFin rfl i))
        (fun i => q.2 (S.orderEmbOfFin rfl i))) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration S.card × Configuration S.card =>
        momentKernel S.card p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n =>
        ((θ, τ), (fun i => q.1 (S.orderEmbOfFin rfl i)),
          (fun i => q.2 (S.orderEmbOfFin rfl i))))
      (measurable_momentKernel S.card) (measurable_const.prodMk (hx.prodMk hy))
  apply hK.mul
  apply Finset.measurable_prod
  intro i _
  exact ((measurable_heatKernel τ).comp
    (((measurable_pi_apply i).comp measurable_snd).sub
      ((measurable_pi_apply i).comp measurable_fst))).ennreal_ofReal

end Critical2DKPZ.SHF.Tsai

end
