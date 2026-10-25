/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.WeightedEndpointAction
public import Critical2DKPZ.SHF.Flow.ScalarCollisionMass

/-! # Duration integration on exponentially weighted configuration spaces -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Integrate the weighted spatial collision action over all positive durations. -/
def weightedCollisionTimeAction {n : ℕ} (α : CollisionPair n) (θ a v : ℝ)
    (f : Configuration n → ℝ≥0∞) (x : Configuration n) : ℝ≥0∞ :=
  ∫⁻ s in Ioo 0 v, weightedEndpointCollisionAction α θ a s (v - s) f x


/-- The two time integrations cost the scalar mass and a bounded window weight. -/
theorem weightedCollisionTimeAction_l2_sq_le {n : ℕ} (α : CollisionPair n) (θ : ℝ)
    {a v T : ℝ} (ha : 0 ≤ a) (hvT : v ≤ T)
    {f : Configuration n → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x : Configuration n, weightedCollisionTimeAction α θ a v f x ^ 2) ≤
      (endpointBetaConstant * ENNReal.ofReal (weightGrowth n a T) ^ 3 *
        ENNReal.ofReal (∫ s in Ioo 0 v, scalarDensity θ s)) ^ 2 *
          ∫⁻ y : Configuration n, f y ^ 2 := by
  let b : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (scalarDensity θ s)
  have hms : Measurable (scalarDensity θ) := by
    change Measurable (fun s : ℝ => scalarDensity θ s)
    exact measurable_scalarDensity.comp (measurable_const.prodMk measurable_id)
  have hb : Measurable b := hms.ennreal_ofReal
  have hb0 : ∀ᵐ s ∂volume.restrict (Ioo 0 v), b s ≠ 0 ∧ b s ≠ ⊤ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact ⟨(ENNReal.ofReal_pos.mpr (scalarDensity_pos θ hs.1)).ne', ENNReal.ofReal_ne_top⟩
  have hH : Measurable (Function.uncurry (fun s (x : Configuration n) =>
      weightedEndpointCollisionAction α θ a s (v - s) f x)) :=
    measurable_weightedEndpointCollisionAction_comp α a measurable_const measurable_fst
      (measurable_const.sub measurable_fst) measurable_snd hf
  have hbound : ∀ᵐ s ∂volume.restrict (Ioo 0 v),
      (∫⁻ x : Configuration n, weightedEndpointCollisionAction α θ a s (v - s) f x ^ 2) ≤
        b s ^ 2 * ((endpointBetaConstant * ENNReal.ofReal (weightGrowth n a T) ^ 3) ^ 2 *
          ∫⁻ y : Configuration n, f y ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have h := weightedEndpointCollisionAction_l2_sq_le α θ (T := T) ha hs.1 (sub_pos.mpr hs.2)
      (by linarith only [hs.2, hvT]) (by linarith only [hs.1, hvT]) hf
    exact h.trans_eq (by simp only [b, mul_pow, mul_assoc, mul_left_comm])
  have hj : IntegrableOn (scalarDensity θ) (Ioo 0 v) :=
    (integral_scalarDensity_Ioo_le_laplace (θ := θ) (v := v)
      (Real.exp_pos (θ + 1)) (by rw [Real.log_exp]; linarith)).1
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) v)] scalarDensity θ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (scalarDensity_pos θ hs.1).le
  have hmass : (∫⁻ s in Ioo 0 v, b s) = ENNReal.ofReal (∫ s in Ioo 0 v, scalarDensity θ s) :=
    (ofReal_integral_eq_lintegral_ofReal hj hn).symm
  have h := lintegral_mixture_sq_le (volume.restrict (Ioo 0 v)) volume hH hb hb0 hbound
  rw [hmass] at h
  exact h.trans_eq (by simp only [mul_pow, mul_assoc, mul_left_comm])

/-- The weighted duration-integrated action has uniform inverse-logarithmic decay. -/
theorem exists_weightedCollisionTimeAction_l2_log_bound (n : ℕ) (B a T : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (α : CollisionPair n) (θ v : ℝ),
      θ ≤ B → 0 < v → v ≤ 1 / 2 → v ≤ T → ∀ f : Configuration n → ℝ≥0∞, Measurable f →
      (∫⁻ x : Configuration n, weightedCollisionTimeAction α θ a v f x ^ 2) ≤
        (C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 * ∫⁻ y : Configuration n, f y ^ 2 := by
  obtain ⟨K, hK, hmass⟩ := exists_integral_scalarDensity_Ioo_le_log B
  let W := endpointBetaConstant * ENNReal.ofReal (weightGrowth n a T) ^ 3
  have hW : W ≠ ⊤ := ENNReal.mul_ne_top endpointBetaConstant_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
  refine ⟨W * ENNReal.ofReal K, ENNReal.mul_ne_top hW ENNReal.ofReal_ne_top,
    fun α θ v hθ hv hvhalf hvT f hf => ?_⟩
  have h := weightedCollisionTimeAction_l2_sq_le α θ (T := T) ha hvT hf
  have hcoef : W * ENNReal.ofReal (∫ s in Ioo 0 v, scalarDensity θ s) ≤
      (W * ENNReal.ofReal K) * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) := by
    calc
      _ ≤ W * ENNReal.ofReal (K / (1 + Real.log v⁻¹)) :=
        mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hmass θ v hθ hv hvhalf).2)
      _ = _ := by
        rw [div_eq_mul_one_div, ENNReal.ofReal_mul hK.le]
        simp only [W, mul_assoc]
  exact h.trans (mul_le_mul' (pow_le_pow_left' hcoef 2) le_rfl)

end Critical2DKPZ.SHF.Flow

end
