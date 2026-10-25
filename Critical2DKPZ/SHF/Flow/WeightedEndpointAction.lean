/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.WeightedCollisionAction
public import Critical2DKPZ.SHF.Flow.KernelMixture
public import Critical2DKPZ.SHF.Flow.EndpointBeta

/-! # Endpoint-time integration on the exponentially weighted space -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Integrate the endpoint times while fixing the collision duration. -/
def weightedEndpointCollisionAction {n : ℕ} (α : CollisionPair n) (θ a s U : ℝ)
    (f : Configuration n → ℝ≥0∞) (x : Configuration n) : ℝ≥0∞ :=
  ∫⁻ r in Ioo 0 U, weightedCollisionSliceAction α θ a r s (U - r) f x

/-- The weighted endpoint collision action is measurable under measurable parameter substitutions. -/
theorem measurable_weightedEndpointCollisionAction_comp {n : ℕ} (α : CollisionPair n) (a : ℝ)
    {X : Type*} [MeasurableSpace X] {θ s U : X → ℝ} {x : X → Configuration n}
    (hθ : Measurable θ) (hs : Measurable s) (hU : Measurable U) (hx : Measurable x)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p => weightedEndpointCollisionAction α (θ p) a (s p) (U p) f (x p)) := by
  unfold weightedEndpointCollisionAction
  apply measurable_lintegral_Ioo measurable_const hU
  exact measurable_weightedCollisionSliceAction_comp α a (hθ.comp measurable_fst) measurable_snd
    (hs.comp measurable_fst) ((hU.comp measurable_fst).sub measurable_snd)
    (hx.comp measurable_fst) hf

/-- The weighted endpoint integration has the same finite beta factor. -/
theorem weightedEndpointCollisionAction_l2_sq_le {n : ℕ} (α : CollisionPair n) (θ : ℝ)
    {a s U T : ℝ} (ha : 0 ≤ a) (hs : 0 < s) (hU : 0 < U) (hsT : s ≤ T) (hUT : U ≤ T)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n, weightedEndpointCollisionAction α θ a s U f x ^ 2) ≤
      endpointBetaConstant ^ 2 * ((ENNReal.ofReal (weightGrowth n a T) ^ 3) ^ 2 *
        (ENNReal.ofReal (scalarDensity θ s) ^ 2 * ∫⁻ y : Configuration n, f y ^ 2)) := by
  let b : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-(1 / 2 : ℝ)) * (U - r) ^ (-(1 / 2 : ℝ)))
  have hb : Measurable b := by
    exact ((measurable_id.pow_const _).mul ((measurable_const.sub measurable_id).pow_const _)).ennreal_ofReal
  have hb0 : ∀ᵐ r ∂volume.restrict (Ioo 0 U), b r ≠ 0 ∧ b r ≠ ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact ⟨(ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos hr.1 _)
      (Real.rpow_pos_of_pos (sub_pos.mpr hr.2) _))).ne', ENNReal.ofReal_ne_top⟩
  have hH : Measurable (Function.uncurry
      (fun r (x : Configuration n) => weightedCollisionSliceAction α θ a r s (U - r) f x)) :=
    measurable_weightedCollisionSliceAction_comp α a measurable_const measurable_fst measurable_const
      (measurable_const.sub measurable_fst) measurable_snd hf
  have hbound : ∀ᵐ r ∂volume.restrict (Ioo 0 U),
      (∫⁻ x : Configuration n, weightedCollisionSliceAction α θ a r s (U - r) f x ^ 2) ≤
        b r ^ 2 * ((ENNReal.ofReal (weightGrowth n a T) ^ 3) ^ 2 *
          (ENNReal.ofReal (scalarDensity θ s) ^ 2 * ∫⁻ y : Configuration n, f y ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have h := oneCollisionSpatialSlice_weighted_l2_majorant α θ ha hr.1 hs (sub_pos.mpr hr.2)
      (by linarith only [hr.2, hUT]) hsT (by linarith only [hr.1, hUT]) hf
    have he : ENNReal.ofReal
        (scalarDensity θ s * r ^ (-(1 / 2 : ℝ)) * (U - r) ^ (-(1 / 2 : ℝ))) =
          ENNReal.ofReal (scalarDensity θ s) * b r := by
      rw [mul_assoc, ENNReal.ofReal_mul (scalarDensity_pos θ hs).le]
    rw [he, mul_pow] at h
    exact h.trans_eq (by ac_rfl)
  have h := lintegral_mixture_sq_le (volume.restrict (Ioo 0 U)) volume hH hb hb0 hbound
  rw [show (∫⁻ r in Ioo 0 U, b r) = endpointBetaConstant from lintegral_endpoint_half_powers hU] at h
  exact h

end Critical2DKPZ.SHF.Flow

end
