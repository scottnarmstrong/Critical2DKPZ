/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

/-! # Reciprocal integral lower bounds -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.OnePoint

/-- An inverse-moment lower bound in terms of a good-set second moment. -/
theorem one_sub_le_integral_inv {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] {R : Ω → ℝ} (hR : ∀ ω, 0 < R ω) {G : Set Ω} (hG : MeasurableSet G)
    (hinv : Integrable (fun ω => (R ω)⁻¹) Q)
    (hsq : IntegrableOn (fun ω => (R ω - 1) ^ 2) G Q) :
    1 - (Q Gᶜ).toReal - (∫ ω in G, (R ω - 1) ^ 2 ∂Q) ^ ((1 : ℝ) / 2) ≤
      ∫ ω, (R ω)⁻¹ ∂Q := by
  let μG := Q.restrict G
  let g : Ω → ℝ := fun ω => R ω - 1
  have hRinvAEM : AEMeasurable (fun ω => (R ω)⁻¹) Q := hinv.aemeasurable
  have hRfun : (fun ω => (R ω)⁻¹)⁻¹ = R := by
    funext ω
    exact inv_inv (R ω)
  have hRAEM : AEMeasurable R Q := hRfun ▸ hRinvAEM.inv
  have hgAEM : AEMeasurable g μG := by
    dsimp [g, μG]
    exact (hRAEM.sub_const 1).restrict
  have hsq' : Integrable (fun ω => g ω ^ 2) μG := by
    simpa only [IntegrableOn, μG, g] using hsq
  have hgMem : MemLp g 2 μG :=
    (memLp_two_iff_integrable_sq hgAEM.aestronglyMeasurable).2 hsq'
  have hgInt : Integrable g μG := hgMem.integrable (by norm_num)
  have hRInt : Integrable R μG := by
    have h := hgInt.add (integrable_const (1 : ℝ))
    convert h using 1
    ext ω
    simp [g]
  have hInvIntG : Integrable (fun ω => (R ω)⁻¹) μG :=
    hinv.mono_measure Measure.restrict_le_self
  have hlinInt : Integrable (fun ω => 2 - R ω) μG :=
    (integrable_const (2 : ℝ)).sub hRInt
  have hpoint (ω : Ω) : 2 - R ω ≤ (R ω)⁻¹ := by
    have hsqnonneg : 0 ≤ (R ω - 1) ^ 2 / R ω :=
      div_nonneg (sq_nonneg _) (le_of_lt (hR ω))
    have halg : (R ω - 1) ^ 2 / R ω = R ω + (R ω)⁻¹ - 2 := by
      field_simp [ne_of_gt (hR ω)]
      ring
    rw [halg] at hsqnonneg
    linarith
  have hmono := integral_mono hlinInt hInvIntG hpoint
  have hRformula : ∫ ω, R ω ∂μG = (∫ ω, g ω ∂μG) + μG.real Set.univ := by
    calc
      ∫ ω, R ω ∂μG = ∫ ω, (g ω + 1) ∂μG := by congr 1; funext ω; simp [g]
      _ = (∫ ω, g ω ∂μG) + ∫ _ : Ω, (1 : ℝ) ∂μG := integral_add hgInt (integrable_const 1)
      _ = (∫ ω, g ω ∂μG) + μG.real Set.univ := by simp
  have hlinear : ∫ ω, (2 - R ω) ∂μG = Q.real G - ∫ ω, g ω ∂μG := by
    rw [integral_sub (integrable_const (2 : ℝ)) hRInt, integral_const, hRformula]
    simp only [smul_eq_mul]
    have hrestrict : μG.real Set.univ = Q.real G := by
      simp [μG]
    rw [hrestrict]
    ring
  have hholder :
      ∫ ω, |g ω| ∂μG ≤
        (∫ ω, g ω ^ 2 ∂μG) ^ ((1 : ℝ) / 2) * (μG.real Set.univ) ^ ((1 : ℝ) / 2) := by
    have hconj : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hgMem' : MemLp g (ENNReal.ofReal (2 : ℝ)) μG := by simpa using hgMem
    have hOne : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μG := by
      simpa using (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μG)
    have h := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
      Real.HolderConjugate.two_two hgMem' hOne
    simpa [Real.norm_eq_abs] using h
  have hmass : μG.real Set.univ ≤ 1 := by
    rw [show μG.real Set.univ = Q.real G by simp [μG]]
    exact (measureReal_mono (Set.subset_univ G)).trans_eq (by simp)
  have hholder' : ∫ ω, |g ω| ∂μG ≤ (∫ ω, g ω ^ 2 ∂μG) ^ ((1 : ℝ) / 2) := by
    have hsqrtmass : (μG.real Set.univ) ^ ((1 : ℝ) / 2) ≤ 1 := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.sqrt_le_one.mpr hmass
    have hfirst : 0 ≤ (∫ ω, g ω ^ 2 ∂μG) ^ ((1 : ℝ) / 2) := by positivity
    calc
      ∫ ω, |g ω| ∂μG ≤
          (∫ ω, g ω ^ 2 ∂μG) ^ ((1 : ℝ) / 2) * (μG.real Set.univ) ^ ((1 : ℝ) / 2) := hholder
      _ ≤ (∫ ω, g ω ^ 2 ∂μG) ^ ((1 : ℝ) / 2) * 1 :=
        mul_le_mul_of_nonneg_left hsqrtmass hfirst
      _ = (∫ ω, g ω ^ 2 ∂μG) ^ ((1 : ℝ) / 2) := by ring
  have hgAbsInt : Integrable (fun ω => |g ω|) μG := hgInt.abs
  have hgUpper : ∫ ω, g ω ∂μG ≤ ∫ ω, |g ω| ∂μG :=
    integral_mono hgInt hgAbsInt (fun ω => le_abs_self (g ω))
  have hmassCompl : Q.real G = 1 - (Q Gᶜ).toReal := by
    have hsum := measureReal_add_measureReal_compl (μ := Q) hG
    have huniv : Q.real Set.univ = 1 := by simp
    have hcompl : Q.real Gᶜ = (Q Gᶜ).toReal := rfl
    rw [hcompl, huniv] at hsum
    linarith
  have hglobal : ∫ ω in G, (R ω)⁻¹ ∂Q ≤ ∫ ω, (R ω)⁻¹ ∂Q :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun ω => inv_nonneg.mpr (le_of_lt (hR ω))) hinv
  calc
    1 - (Q Gᶜ).toReal - (∫ ω in G, (R ω - 1) ^ 2 ∂Q) ^ ((1 : ℝ) / 2)
        = Q.real G - (∫ ω, g ω ^ 2 ∂μG) ^ ((1 : ℝ) / 2) := by
          rw [hmassCompl]
    _ ≤ Q.real G - ∫ ω, g ω ∂μG := by linarith [hholder']
    _ = ∫ ω, (2 - R ω) ∂μG := hlinear.symm
    _ ≤ ∫ ω, (R ω)⁻¹ ∂μG := hmono
    _ = ∫ ω in G, (R ω)⁻¹ ∂Q := rfl
    _ ≤ ∫ ω, (R ω)⁻¹ ∂Q := hglobal

end Critical2DKPZ.OnePoint

end
