/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TwoIncrementLimits
public import Critical2DKPZ.SHF.Tsai.TwoBlockReadouts
import Critical2DKPZ.SHF.Tsai.FiniteVectorConvergence
import Critical2DKPZ.SHF.Tsai.FourthMomentProbability

/-! # Nonlinear observables under two-increment composition

Bounded continuous observables of finite sums of two-block tensor pairings have integrable
expectations converging to those of the combined flow increment.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Tsai

/-- Bounded continuous expectations of two-block tensor sums converge to the actual coarse increment. -/
theorem IsDenseSHF.tendsto_integral_comp_smoothedProduct {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    {s a t : ℝ} (hs : s ∈ D) (ha : a ∈ D) (ht : t ∈ D) (hsa : s < a) (hat : a < t)
    (u : ℕ → Plane → ℝ) (hu : IsL2ApplicableMollifier u) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : Continuous H) (CH : ℝ) (hCH : ∀ z, ‖H z‖ ≤ CH) :
    (∀ ℓ, Integrable (fun ω => H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
      ∂smoothedProductMeasure (Z s a ω) (u ℓ) (Z a t ω))) P) ∧
    Tendsto (fun ℓ => ∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2
      ∂smoothedProductMeasure (Z s a ω) (u ℓ) (Z a t ω)) ∂P) atTop
      (𝓝 (∫ ω, H (fun i => ∑ k, ∫ p, g i k p.1 * g' i k p.2 ∂Z s t ω) ∂P)) := by
  classical
  let X (ℓ : ℕ) (ω : Ω) (i : Fin m × Fin r) := ∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2
    ∂smoothedProductMeasure (Z s a ω) (u ℓ) (Z a t ω)
  let Y (ω : Ω) (i : Fin m × Fin r) := ∫ p, g i.1 i.2 p.1 * g' i.1 i.2 p.2 ∂Z s t ω
  have hm (ℓ : ℕ) (i : Fin m × Fin r) : AEMeasurable (fun ω => X ℓ ω i) P :=
    aemeasurable_integral_smoothedProduct P (Z s a) (Z a t)
      (hZ.1 s hs a ha hsa).1 (hZ.1 a ha t ht hat).1
      (hZ.1 s hs a ha hsa).2 (hZ.1 a ha t ht hat).2
      (u ℓ) (hu.2.1 ℓ).measurable (fun p => g i.1 i.2 p.1 * g' i.1 i.2 p.2) (by fun_prop)
  have hProb (i : Fin m × Fin r) : TendstoInMeasure P (fun ℓ ω => X ℓ ω i) atTop (fun ω => Y ω i) := by
    have h := isDenseSHF_smoothedProduct_tendsto_tensor θ D P Z hZ hs ha ht hsa hat u hu
      (g i.1 i.2) (g' i.1 i.2)
      ((g i.1 i.2).continuous.memLp_of_hasCompactSupport (g i.1 i.2).hasCompactSupport)
      ((g' i.1 i.2).continuous.memLp_of_hasCompactSupport (g' i.1 i.2).hasCompactSupport)
    exact tendstoInMeasure_of_integrable_fourth_moments P _ _ h.1 h.2
  let J (z : (Fin m × Fin r) → ℝ) := H (fun a => ∑ b, z (a, b))
  have hJ : Continuous J := hH.comp (continuous_pi fun a =>
    continuous_finsetSum _ (fun b _ => continuous_apply (a, b)))
  let Hb : ((Fin m × Fin r) → ℝ) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨J, hJ⟩ (2 * CH) (by
      intro x y
      exact (dist_le_norm_add_norm _ _).trans
        ((add_le_add (hCH _) (hCH _)).trans_eq (two_mul CH).symm))
  have hI (ℓ : ℕ) : Integrable (fun ω => Hb (X ℓ ω)) P :=
    Integrable.of_bound (Hb.continuous.comp_aestronglyMeasurable
      (AEMeasurable.of_eval (hm ℓ)).aestronglyMeasurable) ‖Hb‖
      (Eventually.of_forall (fun ω => Hb.norm_coe_le_norm (X ℓ ω)))
  exact ⟨hI, tendsto_integral_boundedContinuous_of_coordinatewise_tendstoInMeasure P X Y hm hProb Hb⟩

end Critical2DKPZ.SHF.Tsai

end
