/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockPositiveExtension
import Critical2DKPZ.SHF.DeltaBose.BlockL2
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Finite compactly weighted block marginals

The positive first-moment identity applies to a constant test in the other
endpoint, so each expected marginal is planar volume. Compactly supported
continuous weights consequently give finite weighted marginal mass almost
surely. These masses control the outer-block spatial tests in the merge steps.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal CompactlySupported
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The expected initial marginal is planar volume, for every positive measurable test. -/
theorem HasDeltaBoseMoments.lintegral_initial_marginal {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ p, f p.1 ∂B ω ∂P) = ∫⁻ x : Plane, f x := by
  have h := hB.lintegral_prod_eq hτ (n := 1) (by norm_num) (by norm_num)
    (fun _ => f) (fun _ _ => 1) (fun _ => hf) (fun _ => measurable_const)
  simp only [Fin.prod_univ_one, mul_one, momentKernel_one] at h
  rw [h]
  have hrow (x : Configuration 1) :
      (∫⁻ y : Configuration 1, f (x 0) * ENNReal.ofReal (freeKernel 1 τ x y)) = f (x 0) := by
    have hm : Measurable (fun y : Configuration 1 => ENNReal.ofReal (freeKernel 1 τ x y)) :=
      ((measurable_freeKernel 1).comp (measurable_const.prodMk
        (measurable_const.prodMk measurable_id))).ennreal_ofReal
    rw [lintegral_const_mul _ hm, lintegral_freeKernel_right 1 hτ x, mul_one]
  simp only [freeKernel_one] at hrow
  simp_rw [hrow]
  have he := (volume_preserving_piUnique (fun _ : Fin 1 => Plane)).lintegral_comp hf
  have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simpa only [MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.coe_mk,
    Equiv.coe_fn_mk, hdef] using he

/-- The expected terminal marginal is also planar volume. -/
theorem HasDeltaBoseMoments.lintegral_terminal_marginal {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ p, f p.2 ∂B ω ∂P) = ∫⁻ x : Plane, f x := by
  have h := hB.lintegral_prod_eq hτ (n := 1) (by norm_num) (by norm_num)
    (fun _ _ => 1) (fun _ => f) (fun _ => measurable_const) (fun _ => hf)
  simp only [Fin.prod_univ_one, one_mul, momentKernel_one] at h
  rw [h]
  have hm : Measurable (fun q : Configuration 1 × Configuration 1 =>
      ENNReal.ofReal (heatKernel τ (q.2 0 - q.1 0)) * f (q.2 0)) :=
    (((measurable_heatKernel τ).comp (((measurable_pi_apply 0).comp measurable_snd).sub
      ((measurable_pi_apply 0).comp measurable_fst))).ennreal_ofReal).mul
        (hf.comp ((measurable_pi_apply 0).comp measurable_snd))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hrow (y : Configuration 1) :
      (∫⁻ x : Configuration 1, ENNReal.ofReal (heatKernel τ (y 0 - x 0)) * f (y 0)) = f (y 0) := by
    have hmass : (∫⁻ x : Configuration 1, ENNReal.ofReal (freeKernel 1 τ x y)) = 1 := by
      simp_rw [freeKernel_symm 1 τ]
      exact lintegral_freeKernel_right 1 hτ y
    simp only [freeKernel_one] at hmass
    have hmrow : Measurable (fun x : Configuration 1 => ENNReal.ofReal (heatKernel τ (y 0 - x 0))) :=
      ((measurable_heatKernel τ).comp (measurable_const.sub (measurable_pi_apply 0))).ennreal_ofReal
    rw [lintegral_mul_const _ hmrow, hmass, one_mul]
  simp_rw [hrow]
  have he := (volume_preserving_piUnique (fun _ : Fin 1 => Plane)).lintegral_comp hf
  have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simpa only [MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.coe_mk,
    Equiv.coe_fn_mk, hdef] using he

/-- Compactly weighting the initial endpoint gives finite total mass almost surely. -/
theorem HasDeltaBoseMoments.ae_initial_marginal_mass_lt_top {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ) (g : C_c(Plane, ℝ)) :
    ∀ᵐ ω ∂P, (∫⁻ p, ENNReal.ofReal |g p.1| ∂B ω) < ⊤ := by
  have hgcont : Continuous (g : Plane → ℝ) := map_continuous g
  have hgm : Measurable (fun x => ENNReal.ofReal |g x|) := by
    simpa only [Real.norm_eq_abs] using hgcont.measurable.norm.ennreal_ofReal
  have hm : Measurable (fun ω => ∫⁻ p, ENNReal.ofReal |g p.1| ∂B ω) :=
    (Measure.measurable_lintegral (hgm.comp measurable_fst)).comp hB.1
  apply ae_lt_top hm
  rw [hB.lintegral_initial_marginal hτ _ hgm]
  have hI : Integrable (g : Plane → ℝ) := hgcont.integrable_of_hasCompactSupport g.hasCompactSupport
  simpa only [Real.enorm_eq_ofReal_abs] using
    (hasFiniteIntegral_iff_enorm.1 hI.hasFiniteIntegral).ne

/-- Compactly weighting the terminal endpoint gives finite total mass almost surely. -/
theorem HasDeltaBoseMoments.ae_terminal_marginal_mass_lt_top {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ) (g : C_c(Plane, ℝ)) :
    ∀ᵐ ω ∂P, (∫⁻ p, ENNReal.ofReal |g p.2| ∂B ω) < ⊤ := by
  have hgcont : Continuous (g : Plane → ℝ) := map_continuous g
  have hgm : Measurable (fun x => ENNReal.ofReal |g x|) := by
    simpa only [Real.norm_eq_abs] using hgcont.measurable.norm.ennreal_ofReal
  have hm : Measurable (fun ω => ∫⁻ p, ENNReal.ofReal |g p.2| ∂B ω) :=
    (Measure.measurable_lintegral (hgm.comp measurable_snd)).comp hB.1
  apply ae_lt_top hm
  rw [hB.lintegral_terminal_marginal hτ _ hgm]
  have hI : Integrable (g : Plane → ℝ) := hgcont.integrable_of_hasCompactSupport g.hasCompactSupport
  simpa only [Real.enorm_eq_ofReal_abs] using
    (hasFiniteIntegral_iff_enorm.1 hI.hasFiniteIntegral).ne

end Critical2DKPZ.SHF.Tsai

end
