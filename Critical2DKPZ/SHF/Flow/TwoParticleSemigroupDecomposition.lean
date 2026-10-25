/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.MomentKernelTwoSemigroup
public import Critical2DKPZ.SHF.Flow.TwoParticleAction
public import Critical2DKPZ.SHF.Flow.TwoParticleCancellation
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! The middle-kernel composition separates into free and collision contributions. -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

private theorem measurable_momentKernel_two_firstVariable (θ h : ℝ) (y : Configuration 2) :
    Measurable (fun x : Configuration 2 => momentKernel 2 θ h x y) := by
  have hparams : Measurable (fun x : Configuration 2 => ((θ, h), (x, y))) := by
    fun_prop
  have hcomp := (measurable_momentKernel 2).comp hparams
  convert hcomp using 1
  funext x
  rfl

private theorem measurable_momentKernel_two_secondVariable (θ h : ℝ) (x : Configuration 2) :
    Measurable (fun y : Configuration 2 => momentKernel 2 θ h x y) := by
  have hparams : Measurable (fun y : Configuration 2 => ((θ, h), (x, y))) := by
    fun_prop
  have hcomp := (measurable_momentKernel 2).comp hparams
  convert hcomp using 1
  funext y
  rfl

/-- The free part of the three-time two-particle kernel composition. -/
def slabTwoParticleFreeMiddleComp (θ a v b : ℝ)
    (x y : Configuration 2) : ℝ≥0∞ :=
  ∫⁻ z : Configuration 2, momentKernel 2 θ a x z *
    (∫⁻ w : Configuration 2,
      ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y)

/-- The one-collision part of the three-time two-particle kernel composition. -/
def slabTwoParticleCorrectionMiddleComp (θ a v b : ℝ)
    (x y : Configuration 2) : ℝ≥0∞ :=
  ∫⁻ z : Configuration 2, momentKernel 2 θ a x z *
    (∫⁻ w : Configuration 2,
      twoParticleCorrection θ v z w * momentKernel 2 θ b w y)

/-- Splitting the middle two-particle kernel into its free and one-collision terms splits every
positive three-time composition into the free-middle and correction-middle contributions. -/
theorem slabMomentKernelTwo_middle_split (θ a v b : ℝ)
    (x y : Configuration 2) :
    (∫⁻ z : Configuration 2, momentKernel 2 θ a x z *
      (∫⁻ w : Configuration 2, momentKernel 2 θ v z w * momentKernel 2 θ b w y)) =
      slabTwoParticleFreeMiddleComp θ a v b x y +
        slabTwoParticleCorrectionMiddleComp θ a v b x y := by
  have hFreeKernelJoint : Measurable (Function.uncurry
      (fun z w : Configuration 2 => ENNReal.ofReal (freeKernel 2 v z w))) := by
    exact ((measurable_freeKernel 2).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))).ennreal_ofReal
  have hFreeTermMeasurable : Measurable (fun z : Configuration 2 =>
      ∫⁻ w : Configuration 2,
        ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y) := by
    apply measurable_kernelAction volume hFreeKernelJoint
    exact measurable_momentKernel_two_firstVariable θ b y
  have hMiddle z :
      (∫⁻ w : Configuration 2,
        momentKernel 2 θ v z w * momentKernel 2 θ b w y) =
        (∫⁻ w : Configuration 2,
          ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y) +
          ∫⁻ w : Configuration 2,
            twoParticleCorrection θ v z w * momentKernel 2 θ b w y := by
    have hFree : Measurable (fun w : Configuration 2 =>
        ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y) :=
      (hFreeKernelJoint.comp (measurable_const.prodMk measurable_id)).mul
        (measurable_momentKernel_two_firstVariable θ b y)
    have hPointwise (w : Configuration 2) :
        momentKernel 2 θ v z w * momentKernel 2 θ b w y =
          ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y +
            twoParticleCorrection θ v z w * momentKernel 2 θ b w y := by
      rw [momentKernel_two]
      simp only [freeKernel, Fin.prod_univ_two, twoParticleCorrection, add_mul]
    rw [show (fun w : Configuration 2 => momentKernel 2 θ v z w * momentKernel 2 θ b w y) =
      (fun w => ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y +
        twoParticleCorrection θ v z w * momentKernel 2 θ b w y) from funext hPointwise,
      lintegral_add_left hFree]
  have hOuterFree : Measurable (fun z : Configuration 2 =>
      momentKernel 2 θ a x z *
        ∫⁻ w : Configuration 2,
          ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y) :=
    (measurable_momentKernel_two_secondVariable θ a x).mul hFreeTermMeasurable
  calc
    _ = ∫⁻ z : Configuration 2, momentKernel 2 θ a x z *
        ((∫⁻ w : Configuration 2,
          ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y) +
          ∫⁻ w : Configuration 2,
            twoParticleCorrection θ v z w * momentKernel 2 θ b w y) := by
          apply lintegral_congr
          intro z
          rw [hMiddle z]
    _ = ∫⁻ z : Configuration 2,
          (momentKernel 2 θ a x z *
            ∫⁻ w : Configuration 2,
              ENNReal.ofReal (freeKernel 2 v z w) * momentKernel 2 θ b w y) +
            (momentKernel 2 θ a x z *
              ∫⁻ w : Configuration 2,
                twoParticleCorrection θ v z w * momentKernel 2 θ b w y) := by
          apply lintegral_congr
          intro z
          exact mul_add _ _ _
    _ = slabTwoParticleFreeMiddleComp θ a v b x y +
        slabTwoParticleCorrectionMiddleComp θ a v b x y := by
          rw [lintegral_add_left hOuterFree]
          rfl

/-- The two-particle semigroup law twice identifies the full interval kernel with the free-middle
term plus the one-collision middle correction. -/
theorem slabMomentKernelTwo_threeTime_split (θ : ℝ) {a v b : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) (x y : Configuration 2) :
    momentKernel 2 θ (a + v + b) x y =
      slabTwoParticleFreeMiddleComp θ a v b x y +
        slabTwoParticleCorrectionMiddleComp θ a v b x y := by
  have houter := momentKernel_two_semigroup_pointwise θ ha (add_pos hv hb) x y
  have hmiddle (z : Configuration 2) :=
    momentKernel_two_semigroup_pointwise θ hv hb z y
  calc
    momentKernel 2 θ (a + v + b) x y =
        momentKernel 2 θ (a + (v + b)) x y := by congr 1; ring
    _ = ∫⁻ z : Configuration 2,
        momentKernel 2 θ a x z * momentKernel 2 θ (v + b) z y := houter.symm
    _ = ∫⁻ z : Configuration 2, momentKernel 2 θ a x z *
        (∫⁻ w : Configuration 2,
          momentKernel 2 θ v z w * momentKernel 2 θ b w y) := by
      apply lintegral_congr
      intro z
      rw [(hmiddle z).symm]
    _ = _ := slabMomentKernelTwo_middle_split θ a v b x y

/-- The correction-middle composition is exactly the zero-weight composition of the three
two-particle actions used in the logarithmic cancellation estimate. -/
theorem slabMomentKernelTwo_correction_action_eq (θ a v b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (f : Configuration 2 → ℝ≥0∞) (x : Configuration 2) :
    (∫⁻ z : Configuration 2, momentKernel 2 θ a x z *
      (∫⁻ w : Configuration 2,
        twoParticleCorrection θ v z w *
          (∫⁻ y : Configuration 2, momentKernel 2 θ b w y * f y))) =
      twoParticleWeightedAction θ 0 a
        (twoParticleCorrectionWeightedAction θ 0 v
          (twoParticleWeightedAction θ 0 b f)) x := by
  simp only [twoParticleWeightedAction, ite_eq_right ha, ite_eq_right hb,
    twoParticleCorrectionWeightedAction, expConjugate]
  simp only [zero_mul, sub_self, Real.exp_zero, ENNReal.ofReal_one, mul_one]

end Critical2DKPZ.SHF.Flow

end
