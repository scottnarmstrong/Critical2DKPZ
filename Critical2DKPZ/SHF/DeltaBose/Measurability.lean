/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Measurability of the collision kernels

The scalar collision integrand, parameter integrals and nonnegative diagram series are jointly measurable. -/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Joint Borel measurability of the real-power operation. -/
theorem measurable_real_rpow : Measurable (fun p : ℝ × ℝ => p.1 ^ p.2) := by
  have heq : (fun p : ℝ × ℝ => p.1 ^ p.2) = fun p =>
      if p.1 = 0 then (if p.2 = 0 then 1 else 0) else
        if p.1 < 0 then Real.exp (Real.log p.1 * p.2) * Real.cos (p.2 * Real.pi)
        else Real.exp (Real.log p.1 * p.2) := by
    funext p
    split_ifs with hx hy hn
    · simp [hx, hy]
    · simp [hx, hy]
    · exact Real.rpow_def_of_neg hn _
    · exact Real.rpow_def_of_pos (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hx)) _
  rw [heq]
  apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
  · exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
      measurable_const measurable_const
  · apply Measurable.ite (measurableSet_lt measurable_fst measurable_const) <;> fun_prop

/-- The reciprocal Gamma function is continuous even at the nonpositive integers. -/
theorem continuous_inv_gamma : Continuous (fun u : ℝ => (Real.Gamma u)⁻¹) := by
  have h := Complex.continuous_re.comp
    (Complex.differentiable_one_div_Gamma.continuous.comp Complex.continuous_ofReal)
  simpa only [Function.comp_def, Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re] using h

/-- The scalar collision integrand is jointly measurable in its parameter, time and integration variable. -/
theorem measurable_scalarIntegrand :
    Measurable (fun p : (ℝ × ℝ) × ℝ => scalarIntegrand p.1.1 p.1.2 p.2) := by
  unfold scalarIntegrand
  simp only [div_eq_mul_inv]
  have hp : Measurable (fun p : (ℝ × ℝ) × ℝ => (p.1.2, p.2 - 1)) := by fun_prop
  exact ((measurable_real_rpow.comp hp).mul (by fun_prop)).mul
    (continuous_inv_gamma.measurable.comp measurable_snd)

/-- The scalar collision density is jointly measurable in its parameter and time. -/
theorem measurable_scalarDensity : Measurable (fun p : ℝ × ℝ => scalarDensity p.1 p.2) := by
  exact (measurable_scalarIntegrand.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioi 0))).measurable

/-- The free kernel is jointly measurable in time and its endpoints. -/
theorem measurable_freeKernel (n : ℕ) :
    Measurable (fun p : ℝ × Configuration n × Configuration n => freeKernel n p.1 p.2.1 p.2.2) := by
  unfold freeKernel heatKernel
  fun_prop

/-- The incoming kernel is jointly measurable in time and both endpoint spaces. -/
theorem measurable_incomingKernel {n : ℕ} (α : CollisionPair n) :
    Measurable (fun p : ℝ × FusedConfiguration α × Configuration n =>
      incomingKernel α p.1 p.2.1 p.2.2) := by
  exact (measurable_freeKernel n).comp (measurable_fst.prodMk (measurable_snd.snd.prodMk
    ((measurable_collisionEmbedding α).comp measurable_snd.fst)))

/-- The swapping kernel is jointly measurable. -/
theorem measurable_swappingKernel {n : ℕ} (α β : CollisionPair n) :
    Measurable (fun p : ℝ × FusedConfiguration α × FusedConfiguration β =>
      swappingKernel α β p.1 p.2.1 p.2.2) := by
  exact (measurable_freeKernel n).comp (measurable_fst.prodMk
    (((measurable_collisionEmbedding α).comp measurable_snd.fst).prodMk
      ((measurable_collisionEmbedding β).comp measurable_snd.snd)))

/-- The repeated-collision kernel is jointly measurable. -/
theorem measurable_collisionKernel {n : ℕ} (α : CollisionPair n) :
    Measurable (fun p : (ℝ × ℝ) × FusedConfiguration α × FusedConfiguration α =>
      collisionKernel α p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold collisionKernel heatKernel
  have hj := measurable_scalarDensity.comp (measurable_fst : Measurable
    (fun p : (ℝ × ℝ) × FusedConfiguration α × FusedConfiguration α => p.1))
  fun_prop

/-- Integrating a jointly measurable function between measurable time boundaries. -/
theorem measurable_lintegral_Ioo {X : Type*} [MeasurableSpace X]
    {a b : X → ℝ} {f : X → ℝ → ℝ≥0∞}
    (ha : Measurable a) (hb : Measurable b)
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun x => ∫⁻ r in Ioo (a x) (b x), f x r) := by
  have hs : MeasurableSet {p : X × ℝ | a p.1 < p.2 ∧ p.2 < b p.1} :=
    (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hb.comp measurable_fst))
  have h := (hf.indicator hs).lintegral_prod_right' (ν := volume)
  convert h using 1
  funext x
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro r
  rfl

/-- Joint measurability of each individual diagram, after measurable substitutions. -/
theorem measurable_diagramKernel_comp {n : ℕ} (w : List (CollisionPair n)) :
    ∀ {X : Type*} [MeasurableSpace X] {θ h : X → ℝ} {x y : X → Configuration n},
      Measurable θ → Measurable h → Measurable x → Measurable y →
      Measurable (fun p => diagramKernel (θ p) w (h p) (x p) (y p)) := by
  induction w with
  | nil =>
    intro X _ θ h x y hθ hh hx hy
    exact ((measurable_freeKernel n).comp (hh.prodMk (hx.prodMk hy))).ennreal_ofReal
  | cons α w ih =>
    intro X _ θ h x y hθ hh hx hy
    simp only [diagramKernel]
    apply measurable_lintegral_Ioo measurable_const hh
    apply measurable_lintegral_Ioo measurable_snd (hh.comp measurable_fst)
    apply Measurable.lintegral_prod_right
    apply Measurable.lintegral_prod_right
    let R := (((X × ℝ) × ℝ) × FusedConfiguration α) × FusedConfiguration α
    have hb : Measurable (fun a : R => a.1.1.1.1) := by fun_prop
    have hR : Measurable (fun a : R => a.1.1.1.2) := by fun_prop
    have hU : Measurable (fun a : R => a.1.1.2) := by fun_prop
    have hZ : Measurable (fun a : R => a.1.2) := by fun_prop
    have hW : Measurable (fun a : R => a.2) := measurable_snd
    have hi : Measurable (fun a : R => ENNReal.ofReal
        (incomingKernel α a.1.1.1.2 a.1.2 (x a.1.1.1.1))) :=
      ((measurable_incomingKernel α).comp (hR.prodMk (hZ.prodMk (hx.comp hb)))).ennreal_ofReal
    have hc : Measurable (fun a : R => ENNReal.ofReal
        (collisionKernel α (θ a.1.1.1.1) (a.1.1.2 - a.1.1.1.2) a.1.2 a.2)) :=
      ((measurable_collisionKernel α).comp
        (((hθ.comp hb).prodMk (hU.sub hR)).prodMk (hZ.prodMk hW))).ennreal_ofReal
    have hr : Measurable (fun a : R => diagramKernel (θ a.1.1.1.1) w
        (h a.1.1.1.1 - a.1.1.2) (collisionEmbedding α a.2) (y a.1.1.1.1)) :=
      ih (hθ.comp hb) ((hh.comp hb).sub hU) ((measurable_collisionEmbedding α).comp hW) (hy.comp hb)
    exact (hi.mul hc).mul hr

/-- Every fixed-length diagram coefficient is jointly measurable. -/
theorem measurable_diagramKernel {n : ℕ} (w : List (CollisionPair n)) :
    Measurable (fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
      diagramKernel p.1.1 w p.1.2 p.2.1 p.2.2) :=
  measurable_diagramKernel_comp w (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- Joint measurability of the entire positive moment-kernel series. -/
theorem measurable_momentKernel (n : ℕ) :
    Measurable (fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
      momentKernel n p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold momentKernel
  have hf : Measurable (fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
      ENNReal.ofReal (freeKernel n p.1.2 p.2.1 p.2.2)) :=
    ((measurable_freeKernel n).comp
      (measurable_fst.snd.prodMk (measurable_snd.fst.prodMk measurable_snd.snd))).ennreal_ofReal
  have hs : Measurable (fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
      ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
        diagramKernel p.1.1 (List.ofFn w.1) p.1.2 p.2.1 p.2.2) := by
    apply Measurable.tsum
    intro m
    apply Finset.measurable_sum
    intro w _
    exact measurable_diagramKernel _
  exact hf.add hs

end Critical2DKPZ.DeltaBose
