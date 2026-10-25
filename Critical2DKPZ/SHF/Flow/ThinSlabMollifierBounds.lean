/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabSmoothedBridgeIdentity
public import Critical2DKPZ.SHF.Flow.TwoParticleCancellation
public import Critical2DKPZ.SHF.DeltaBose.WeightedBlockL2
public import Critical2DKPZ.SHF.Tsai.ChainFormBounds
import Mathlib.Tactic

/-! # Uniform weighted bounds for mollifier tensors

The weighted operator bounds are uniform over positive mollifier scales at most one. -/

@[expose] public noncomputable section

open MeasureTheory Filter Critical2DKPZ.DeltaBose
open scoped CompactlySupported ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Every spatial dilation of a compactly supported continuous profile is bounded by the corresponding dilation of one Gaussian majorant, with a constant independent of the dilation. -/
theorem exists_scaledProfile_le_heatKernel (w : Plane → ℝ) (hw : Continuous w)
    (hwc : HasCompactSupport w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : ℝ, 0 < e → ∀ x : Plane,
      |e⁻¹ ^ 2 * w (e⁻¹ • x)| ≤ C * heatKernel (1 / (2 * Real.pi * e⁻¹ ^ 2)) x := by
  let R : Plane → ℝ := fun x => w x * Real.exp (Real.pi * ‖x‖ ^ 2)
  have hRc : Continuous R := hw.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hRs : HasCompactSupport R := hwc.mul_right
  obtain ⟨C₀, hC₀⟩ := hRc.bounded_above_of_compact_support hRs
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro e he x
  let d : ℝ := e⁻¹
  have hd : 0 < d := inv_pos.mpr he
  have hscaled : ‖d • x‖ ^ 2 = d ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hd, mul_pow]
  have hprofile : |w (d • x)| ≤ C * Real.exp (-(Real.pi * ‖d • x‖ ^ 2)) := by
    have hmul : |w (d • x)| * Real.exp (Real.pi * ‖d • x‖ ^ 2) ≤ C := by
      have h := (hC₀ (d • x)).trans (le_max_left C₀ 0)
      simpa only [R, C, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using h
    have hdiv := (le_div_iff₀ (Real.exp_pos (Real.pi * ‖d • x‖ ^ 2))).mpr hmul
    simpa only [div_eq_mul_inv, ← Real.exp_neg] using hdiv
  have hheat : heatKernel (1 / (2 * Real.pi * d ^ 2)) x =
      d ^ 2 * Real.exp (-(Real.pi * ‖d • x‖ ^ 2)) := by
    rw [heatKernel_eq_exp]
    congr 1
    · field_simp
    · rw [hscaled]
      field_simp
  change |d ^ 2 * w (d • x)| ≤ C * heatKernel (1 / (2 * Real.pi * d ^ 2)) x
  rw [abs_mul, abs_of_nonneg (sq_nonneg d), hheat]
  exact (mul_le_mul_of_nonneg_left hprofile (sq_nonneg d)).trans_eq (by ring)

/-- The explicit tensor connector supplied by a scaled planar mollifier. -/
def slabMollifierTensorKernel (n : ℕ) (e : ℝ) (w : Plane → ℝ)
    (x y : Configuration n) : ℝ≥0∞ :=
  Tsai.connectorKernel (fun _ z => e⁻¹ ^ 2 * w (e⁻¹ • z)) x y

/-- The tensor mollifier is bounded on the exponentially weighted `L²` space,
uniformly over all positive scales at most one. This includes the two-replica
connector `W_e ⊗ W_e` used in the second thin-slab comparison. -/
theorem exists_slabMollifierTensorKernel_weighted_l2_bound (n : ℕ) (a : ℝ)
    (ha : 0 ≤ a) (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ e : ℝ, 0 < e → e ≤ 1 →
      ∀ f : Configuration n → ℝ≥0∞, Measurable f →
        (∫⁻ x : Configuration n, (∫⁻ y : Configuration n,
          expConjugate (fun x => a * configurationOneNorm x)
            (fun y => a * configurationOneNorm y) (slabMollifierTensorKernel n e w) x y * f y) ^ 2) ≤
          M * ∫⁻ y : Configuration n, f y ^ 2 := by
  obtain ⟨C, hC, hmajor⟩ := exists_scaledProfile_le_heatKernel w hw hwc
  let T : ℝ := 1 / (2 * Real.pi)
  let D : ℝ≥0∞ := ENNReal.ofReal (C ^ n)
  let G : ℝ≥0∞ := ENNReal.ofReal (weightGrowth n a T)
  refine ⟨D ^ 2 * G ^ 2, by dsimp [D, G]; finiteness, ?_⟩
  intro e he he1 f hf
  let τ : ℝ := 1 / (2 * Real.pi * e⁻¹ ^ 2)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτT : τ ≤ T := by
    have hi : 1 ≤ e⁻¹ := (one_le_inv₀ he).mpr he1
    have hisq : 1 ≤ e⁻¹ ^ 2 := one_le_pow₀ hi
    dsimp [τ, T]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [hisq, Real.pi_pos]
  have hkernel (x y : Configuration n) : slabMollifierTensorKernel n e w x y ≤
      D * ENNReal.ofReal (freeKernel n τ x y) := by
    have hcoord (i : Fin n) : ENNReal.ofReal (e⁻¹ ^ 2 * w (e⁻¹ • (x i - y i))) ≤
        ENNReal.ofReal C * ENNReal.ofReal (heatKernel τ (x i - y i)) := by
      rw [← ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hmajor e he (x i - y i)))
    calc
      _ ≤ ∏ i : Fin n, ENNReal.ofReal C * ENNReal.ofReal (heatKernel τ (x i - y i)) :=
        Finset.prod_le_prod (fun i _ => hcoord i)
      _ = D * ENNReal.ofReal (freeKernel n τ y x) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (heatKernel_pos hτ _).le)]
        rfl
      _ = _ := by rw [freeKernel_symm]
  have hdom (x y : Configuration n) :
      expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
        (slabMollifierTensorKernel n e w) x y ≤
      D * ENNReal.ofReal (freeKernel n τ x y *
        Real.exp (a * (configurationOneNorm x - configurationOneNorm y))) := by
    unfold expConjugate
    rw [ENNReal.ofReal_mul (freeKernel_pos n hτ x y).le]
    have h := mul_le_mul_of_nonneg_right (hkernel x y)
      (show 0 ≤ ENNReal.ofReal (Real.exp (a * configurationOneNorm x - a * configurationOneNorm y)) from bot_le)
    simpa only [mul_sub, mul_assoc] using h
  have hfree := freeKernel_weighted_l2_sq_le n ha hτ hf
  have hGrowth : ENNReal.ofReal (weightGrowth n a τ) ≤ G := by
    apply ENNReal.ofReal_le_ofReal
    dsimp [weightGrowth, G]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτT (by positivity))
  have hfree' : (∫⁻ x : Configuration n, (∫⁻ y : Configuration n,
      ENNReal.ofReal (freeKernel n τ x y * Real.exp (a * (configurationOneNorm x - configurationOneNorm y))) * f y) ^ 2) ≤
      G ^ 2 * ∫⁻ y : Configuration n, f y ^ 2 :=
    hfree.trans (mul_le_mul' (pow_le_pow_left₀ bot_le hGrowth 2) le_rfl)
  exact lintegral_kernel_sq_dominate volume volume (by dsimp [D]; finiteness) hdom f hfree'

/-- The conjugated tensor mollifier acts on the same weighted coordinates as
the two-particle moment and correction kernels. -/
def slabMollifierWeightedAction (a e : ℝ) (w : Plane → ℝ)
    (f : Configuration 2 → ℝ≥0∞) (x : Configuration 2) : ℝ≥0∞ :=
  ∫⁻ y : Configuration 2,
    expConjugate (fun x => a * configurationOneNorm x)
      (fun y => a * configurationOneNorm y) (slabMollifierTensorKernel 2 e w) x y * f y

/-- Jointly measurable kernels give a measurable mollifier action. -/
theorem measurable_slabMollifierWeightedAction (a e : ℝ) {w : Plane → ℝ}
    (hw : Continuous w) {f : Configuration 2 → ℝ≥0∞} (hf : Measurable f) :
    Measurable (slabMollifierWeightedAction a e w f) := by
  apply measurable_kernelAction volume _ hf
  apply measurable_expConjugate
  · exact measurable_const.mul (measurable_configurationOneNorm 2)
  · exact measurable_const.mul (measurable_configurationOneNorm 2)
  · unfold slabMollifierTensorKernel
    apply Tsai.measurable_connectorKernel
    intro i
    apply Continuous.measurable
    fun_prop


/-- The middle inverse-logarithmic correction estimate remains uniform after
inserting `W_e ⊗ W_e`, for all `0 < e ≤ 1`. This is the deterministic operator
bound used for the smoothed thin-slab error. -/
theorem exists_slabSmoothed_weighted_cancellation_bound (B a T : ℝ) (ha : 0 ≤ a)
    (w : Plane → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (θ r t v e : ℝ), θ ≤ B →
      0 ≤ r → r ≤ T → 0 ≤ t → t ≤ T → 0 < v → v ≤ 1 / 2 → 0 < e → e ≤ 1 →
      ∀ f : Configuration 2 → ℝ≥0∞, Measurable f →
        (∫⁻ x : Configuration 2,
          twoParticleWeightedAction θ a r
            (slabMollifierWeightedAction a e w
              (twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f))) x ^ 2) ≤
          C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹)) ^ 2 *
            ∫⁻ y : Configuration 2, f y ^ 2 := by
  obtain ⟨D, hD, hQ⟩ := exists_twoParticleWeightedAction_l2_bound B a T ha
  obtain ⟨M, hM, hW⟩ := exists_slabMollifierTensorKernel_weighted_l2_bound 2 a ha w hw hwc
  obtain ⟨K, hK, hCorrection⟩ :=
    exists_diagramKernel_singleton_weighted_l2_log_bound 2 B a (1 / 2) ha
  refine ⟨D * M * K ^ 2 * D, by finiteness, ?_⟩
  intro θ r t v e hθ hr hrT ht htT hv hvhalf he he1 f hf
  have hQt := measurable_twoParticleWeightedAction θ a t hf
  have hKQt := measurable_twoParticleCorrectionWeightedAction θ a v hQt
  have hWKQt := measurable_slabMollifierWeightedAction a e hw hKQt
  have hright := hQ θ t hθ ht htT f hf
  have hmiddle : (∫⁻ x : Configuration 2,
      twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f) x ^ 2) ≤
      (K * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 *
        ∫⁻ y : Configuration 2, twoParticleWeightedAction θ a t f y ^ 2 :=
    hCorrection pairTwo θ v hθ hv hvhalf hvhalf _ hQt
  have hmollifier := hW e he he1 _ hKQt
  calc
    _ ≤ D * ∫⁻ x : Configuration 2,
        slabMollifierWeightedAction a e w
          (twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f)) x ^ 2 :=
      hQ θ r hθ hr hrT _ hWKQt
    _ ≤ D * (M * ∫⁻ x : Configuration 2,
        twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f) x ^ 2) :=
      mul_le_mul' le_rfl hmollifier
    _ ≤ D * (M * ((K * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 *
        ∫⁻ y : Configuration 2, twoParticleWeightedAction θ a t f y ^ 2)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hmiddle)
    _ ≤ D * (M * ((K * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 *
        (D * ∫⁻ y : Configuration 2, f y ^ 2))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hright))
    _ = _ := by simp only [mul_pow]; ac_rfl

end Critical2DKPZ.SHF.Flow

end
