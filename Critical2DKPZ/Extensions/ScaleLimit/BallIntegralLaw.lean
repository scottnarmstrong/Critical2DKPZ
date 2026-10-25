/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SetIntegralLaw
public import Critical2DKPZ.Extensions.ScaleLimit.NormField
import Mathlib.MeasureTheory.Group.Integral

/-! # Translation invariance of finite families of ball integrals

The continuity-in-probability premise yields continuous `L¹`-valued fields.
Their finite-family laws can therefore be passed through spatial integration.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Translation of the domain of a spatial ball integral. -/
theorem integral_norm_ball_translate (f : Plane → ℝ) (y : Plane) (r : ℝ) :
    (∫ z in ball (0 : Plane) r, ‖f (z + y)‖) = ∫ z in ball y r, ‖f z‖ := by
  classical
  calc
    (∫ z in ball (0 : Plane) r, ‖f (z + y)‖) =
        ∫ z, (ball y r).indicator (fun w => ‖f w‖) (z + y) := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change (ball (0 : Plane) r).indicator (fun z => ‖f (z + y)‖) z =
          (ball y r).indicator (fun w => ‖f w‖) (z + y)
        have hm : z + y ∈ ball y r ↔ z ∈ ball (0 : Plane) r := by
          simp only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]
        by_cases hz : z ∈ ball (0 : Plane) r
        · rw [indicator_of_mem hz, indicator_of_mem (hm.mpr hz)]
        · rw [indicator_of_notMem hz, indicator_of_notMem (fun h => hz (hm.mp h))]
    _ = ∫ z in ball y r, ‖f z‖ := by
      rw [integral_add_right_eq_self, integral_indicator measurableSet_ball]

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Finite families of centered ball integrals have translation-invariant laws. -/
theorem centered_ballIntegrals_identDistrib {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hstat : ∀ (n : ℕ) (x : Fin n → Plane) (z : Plane),
      IdentDistrib (fun ω i => g (x i + z) ω) (fun ω i => g (x i) ω) P P)
    (hcont : ∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀))
    (hint : Integrable (g 0) P) (n : ℕ) (r : Fin n → ℝ) (y : Plane) :
    IdentDistrib (fun ω i => ∫ z in ball (0 : Plane) (r i), ‖g (z + y) ω‖)
      (fun ω i => ∫ z in ball (0 : Plane) (r i), ‖g z ω‖) P P := by
  classical
  let hp := identDistrib_eval_zero hstat
  let X : Plane → Lp ℝ 1 P := fun z => normL1Field hp hint (z + y)
  let Y : Plane → Lp ℝ 1 P := normL1Field hp hint
  let f : Plane → Ω → ℝ := fun z ω => ‖g (z + y) ω‖
  let f₀ : Plane → Ω → ℝ := fun z ω => ‖g z ω‖
  have hYc : Continuous Y := continuous_normL1Field hp hint hcont
  have hXc : Continuous X := hYc.comp (continuous_id.add continuous_const)
  let R := ∑ i, |r i|
  let K := closedBall (0 : Plane) R
  let μ := volume.restrict K
  have hK : IsCompact K := isCompact_closedBall _ _
  have hfinite : volume K ≠ ⊤ := hK.measure_ne_top
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hfinite
  have hri (i : Fin n) : r i ≤ R :=
    (le_abs_self (r i)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (r j)) (Finset.mem_univ i))
  let A : Fin n → Set Plane := fun i => ball 0 (r i)
  have hA (i : Fin n) : MeasurableSet (A i) := measurableSet_ball
  have hAK (i : Fin n) : A i ⊆ K := fun z hz =>
    (mem_closedBall.mpr ((mem_ball.mp hz).le.trans (hri i)))
  have hμ (i : Fin n) : μ.restrict (A i) = volume.restrict (A i) := by
    dsimp [μ]
    rw [Measure.restrict_restrict (hA i), inter_eq_left.mpr (hAK i)]
  have hXi : Integrable X μ := ContinuousOn.integrableOn_compact hK hXc.continuousOn
  have hYi : Integrable Y μ := ContinuousOn.integrableOn_compact hK hYc.continuousOn
  have hfm : Measurable (Function.uncurry f) :=
    (hg.comp ((measurable_fst.add measurable_const).prodMk measurable_snd)).norm
  have hf₀m : Measurable (Function.uncurry f₀) := hg.norm
  have hfi : Integrable (Function.uncurry f) (μ.prod P) :=
    integrable_stationary_prod μ hfm (fun z => (hp (z + y)).norm) hint.norm
  have hf₀i : Integrable (Function.uncurry f₀) (μ.prod P) :=
    integrable_stationary_prod μ hf₀m (fun z => (hp z).norm) hint.norm
  have hid (m : ℕ) (z : Fin m → Plane) :
      IdentDistrib (fun ω i => f (z i) ω) (fun ω i => f₀ (z i) ω) P P := by
    exact (hstat m z y).comp (show Measurable (fun v : Fin m → ℝ => fun i => ‖v i‖) by fun_prop)
  have hh := identDistrib_setIntegrals μ A hA X Y f f₀ hXc.stronglyMeasurable hYc.stronglyMeasurable
    hXi hYi hfi hf₀i (fun z => normL1Field_ae_eq hp hint (z + y))
    (normL1Field_ae_eq hp hint) hid
  simpa only [A, f, f₀, hμ] using hh

/-- The joint law of finitely many absolute-value ball integrals is independent
of their common center. -/
theorem ballIntegrals_identDistrib {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hstat : ∀ (n : ℕ) (x : Fin n → Plane) (z : Plane),
      IdentDistrib (fun ω i => g (x i + z) ω) (fun ω i => g (x i) ω) P P)
    (hcont : ∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀))
    (hint : Integrable (g 0) P) (n : ℕ) (r : Fin n → ℝ) (y : Plane) :
    IdentDistrib (fun ω i => ∫ z in ball y (r i), ‖g z ω‖)
      (fun ω i => ∫ z in ball (0 : Plane) (r i), ‖g z ω‖) P P := by
  have heq : (fun ω i => ∫ z in ball (0 : Plane) (r i), ‖g (z + y) ω‖) =
      fun ω i => ∫ z in ball y (r i), ‖g z ω‖ :=
    funext fun ω => funext fun i => integral_norm_ball_translate (fun z => g z ω) y (r i)
  rw [← heq]
  exact centered_ballIntegrals_identDistrib hg hstat hcont hint n r y

end Critical2DKPZ.Extensions.ScaleLimit

end
