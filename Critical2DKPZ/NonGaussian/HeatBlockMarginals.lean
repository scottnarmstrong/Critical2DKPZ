/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockMoments
import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The Lebesgue endpoint marginals of a heat block -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- The translated heat kernel has positive-integral mass one. -/
theorem lintegral_ofReal_heatKernel_sub_eq_one {τ : ℝ} (hτ : 0 < τ) (a : Plane) :
    (∫⁻ x : Plane, ENNReal.ofReal (heatKernel τ (x - a))) = 1 := by
  calc
    _ = ∫⁻ x : Plane, ENNReal.ofReal (heatKernel τ x) := by
      simpa only [sub_eq_add_neg] using
        lintegral_add_right_eq_self (fun x : Plane => ENNReal.ofReal (heatKernel τ x)) (-a)
    _ = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal (integrable_heatKernel hτ)
        (Eventually.of_forall (heatKernel_nonneg hτ.le)), integral_heatKernel hτ, ENNReal.ofReal_one]

/-- The final endpoint marginal of a heat block is Lebesgue measure, expressed
on every nonnegative measurable test, including unbounded tests. -/
theorem lintegral_heatBlock_snd_eq {τ : ℝ} (hτ : 0 < τ)
    (g : Plane → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p : Plane × Plane, g p.2 ∂heatBlock τ) = ∫⁻ y, g y := by
  have hden : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel τ (p.2 - p.1))) :=
    ((measurable_heatKernel τ).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  unfold heatBlock
  rw [lintegral_withDensity_eq_lintegral_mul volume hden
      (g := fun p : Plane × Plane => g p.2) (hg.comp measurable_snd),
    Measure.volume_eq_prod]
  change (∫⁻ p : Plane × Plane, ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * g p.2
    ∂volume.prod volume) = _
  rw [lintegral_prod_symm (fun p : Plane × Plane =>
    ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * g p.2)
    ((hden.mul (hg.comp measurable_snd)).aemeasurable)]
  apply lintegral_congr
  intro y
  dsimp only [Pi.mul_apply]
  have hHeat : Measurable (fun x : Plane => ENNReal.ofReal (heatKernel τ (y - x))) :=
    ((measurable_heatKernel τ).comp (measurable_const.sub measurable_id)).ennreal_ofReal
  rw [lintegral_mul_const _ hHeat]
  have hmass : (∫⁻ x : Plane, ENNReal.ofReal (heatKernel τ (y - x))) = 1 := by
    have hsymm (x : Plane) : heatKernel τ (y - x) = heatKernel τ (x - y) := by
      rw [show y - x = -(x - y) by abel, heatKernel_neg]
    simp_rw [hsymm]
    exact lintegral_ofReal_heatKernel_sub_eq_one hτ y
  rw [hmass, one_mul]

/-- The initial endpoint marginal of a heat block is also Lebesgue measure. -/
theorem lintegral_heatBlock_fst_eq {τ : ℝ} (hτ : 0 < τ)
    (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : Plane × Plane, f p.1 ∂heatBlock τ) = ∫⁻ x, f x := by
  have hden : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel τ (p.2 - p.1))) :=
    ((measurable_heatKernel τ).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  unfold heatBlock
  rw [lintegral_withDensity_eq_lintegral_mul volume hden
    (g := fun p : Plane × Plane => f p.1) (hf.comp measurable_fst), Measure.volume_eq_prod]
  change (∫⁻ p : Plane × Plane, ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * f p.1
    ∂volume.prod volume) = _
  rw [lintegral_prod (fun p : Plane × Plane =>
    ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * f p.1)
    ((hden.mul (hf.comp measurable_fst)).aemeasurable)]
  apply lintegral_congr
  intro x
  dsimp only
  have hHeat : Measurable (fun y : Plane => ENNReal.ofReal (heatKernel τ (y - x))) :=
    ((measurable_heatKernel τ).comp (measurable_id.sub measurable_const)).ennreal_ofReal
  rw [lintegral_mul_const _ hHeat, lintegral_ofReal_heatKernel_sub_eq_one hτ x, one_mul]

/-- A heat block started from a translated unit-mass Gaussian has total mass one. -/
theorem lintegral_heatBlock_gaussian_fst_eq_one {τ ε : ℝ}
    (hτ : 0 < τ) (hε : 0 < ε) (a : Plane) :
    (∫⁻ p : Plane × Plane, ENNReal.ofReal (heatKernel ε (p.1 - a)) ∂heatBlock τ) = 1 := by
  rw [lintegral_heatBlock_fst_eq hτ (fun y : Plane => ENNReal.ofReal (heatKernel ε (y - a)))
    (((measurable_heatKernel ε).comp (measurable_id.sub measurable_const)).ennreal_ofReal)]
  exact lintegral_ofReal_heatKernel_sub_eq_one hε a

end Critical2DKPZ.NonGaussian

end
