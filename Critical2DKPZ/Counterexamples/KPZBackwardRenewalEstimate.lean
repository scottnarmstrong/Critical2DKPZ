/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.BackwardRenewal
import Mathlib.Tactic

/-! # Backward renewal integrals

The backward-block estimate of KPZ Lemma A.4 is integrable on `0 < τ < S` and `4 * S ≤ T < 1`, with its quotient-log weight and the density parameter shifted by Euler's constant. -/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Critical2DKPZ.Errata

/-- The real backward-block integral is bounded uniformly on compact parameter
intervals, for `0 < τ < S` and `4 * S ≤ T < 1`. -/
theorem integral_backward_block_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ϑ ∈ Set.Icc (-A) A, ∀ τ S T : ℝ,
      0 < τ → τ < S → 4 * S ≤ T → T < 1 →
      let D : Set (ℝ × ℝ) := {p | S < p.1 ∧ p.1 < p.2 ∧ p.2 < T}
      let f : ℝ × ℝ → ℝ := fun p =>
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
          (τ / (p.1 * (p.1 - τ))) * Real.log (2 * T / (T - p.2))
      IntegrableOn f D ∧ (∫ p in D, f p) ≤
        C / |Real.log T| * (τ / S) * Real.log (2 * S / (S - τ)) := by
  obtain ⟨C, hC, hbound⟩ := Collision.lintegral_backwardBlock_le A
  refine ⟨C, hC, fun ϑ hϑ τ S T hτ hτS hST hT => ?_⟩
  dsimp only
  let D : Set (ℝ × ℝ) := {p | S < p.1 ∧ p.1 < p.2 ∧ p.2 < T}
  let f : ℝ × ℝ → ℝ := fun p =>
    DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1) *
      (τ / (p.1 * (p.1 - τ))) * Real.log (2 * T / (T - p.2))
  have hS : 0 < S := hτ.trans hτS
  have hTp : 0 < T := by linarith
  have hD : MeasurableSet D := by dsimp [D]; measurability
  have hf : Measurable f := by
    have hj : Measurable (fun p : ℝ × ℝ =>
        DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) :=
      DeltaBose.measurable_scalarDensity.comp
        (measurable_const.prodMk (measurable_snd.sub measurable_fst))
    exact (hj.mul (by fun_prop)).mul (by fun_prop)
  have he (p : ℝ × ℝ) (hp : p ∈ D) :
      Collision.backwardWeight T p.2 = Real.log (2 * T / (T - p.2)) :=
    Collision.backwardWeight_eq_log_ratio hTp hp.2.2
  have hb : (∫⁻ p in D, ENNReal.ofReal (f p)) ≤
      ENNReal.ofReal (C / |Real.log T| * (τ / S) * Real.log (2 * S / (S - τ))) := by
    have hb := hbound ϑ hϑ τ S T hτ hτS hST hT
    rw [abs_of_neg (Real.log_neg hTp hT),
      ← Collision.backwardWeight_eq_log_ratio hS hτS]
    apply le_trans _ hb
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hD] with p hp
    simp only [f, ← he p hp]
    exact le_rfl
  have hn : 0 ≤ᵐ[volume.restrict D] f := by
    filter_upwards [ae_restrict_mem hD] with p hp
    have hback := Collision.backwardWeight_nonneg hTp (by linarith [hp.1, hp.2.1]) hp.2.2
    rw [he p hp] at hback
    exact mul_nonneg (mul_nonneg
      (DeltaBose.scalarDensity_pos _ (sub_pos.mpr hp.2.1)).le
      (div_nonneg hτ.le (mul_nonneg (by linarith [hp.1]) (by linarith [hp.1])))) hback
  have hi : IntegrableOn f D :=
    ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hn).mpr
      (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hn hi.aestronglyMeasurable]
  have hlog : 0 ≤ Real.log (2 * S / (S - τ)) := by
    rw [← Collision.backwardWeight_eq_log_ratio hS hτS]
    exact Collision.backwardWeight_nonneg hS hτ.le hτS
  have hR : 0 ≤ C / |Real.log T| * (τ / S) * Real.log (2 * S / (S - τ)) :=
    mul_nonneg (mul_nonneg (div_nonneg hC.le (abs_nonneg _))
      (div_nonneg hτ.le hS.le)) hlog
  simpa only [ENNReal.toReal_ofReal hR] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

end Critical2DKPZ.Errata
