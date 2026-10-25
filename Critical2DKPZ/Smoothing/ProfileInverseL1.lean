/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.Smoothing.Decomposition
public import Critical2DKPZ.Smoothing.Measurability
import Mathlib.Tactic

/-! # Inverse moments for weighted finite profiles -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.Smoothing

/-- A bounded positive terminal weight transfers the inverse `L¹` bound from the flat profile.
The flat second-moment hypothesis includes its integrability companion. -/
theorem eLpNorm_inv_profile_terminal_le_of_secondMoment (β : ℝ) (hβ : 0 ≤ β)
    (a b : ℕ) (ν : Site → ℝ) (A : Finset Site)
    (hνA : ∀ w ∉ A, ν w = 0) (hν0 : ∀ w, 0 ≤ ν w)
    (hν1 : ∑ w ∈ A, ν w = 1)
    (f : Site → ℝ) (H : ℝ)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H)
    (Q : ℝ)
    (hflatSq : Integrable (fun ω => profileP2Fun β a b ν (fun _ => 1) ω ^ 2)
        disorderLaw ∧
      (∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤ Q) :
    eLpNorm (fun ω => (profileP2Fun β a b ν f ω)⁻¹) 1 disorderLaw ≤
      ENNReal.ofReal (Real.exp H * Q) := by
  classical
  let X : Disorder → ℝ := fun ω => profileP2Fun β a b ν (fun _ => 1) ω
  let Y : Disorder → ℝ := fun ω => profileP2Fun β a b ν f ω
  have hA : A.Nonempty := by
    by_contra hA
    have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    simp [hAempty] at hν1
  have hνpos : ∃ w ∈ A, 0 < ν w := by
    have hsum : 0 < ∑ w ∈ A, ν w := by rw [hν1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hν0 w)).mp hsum
  have hXpos (ω : Disorder) : 0 < X ω := by
    dsimp [X]
    exact OnePoint.profileP2Fun_pos_of_normalized β a b ν A hνA hν0 hν1 ω
  have hYpos (ω : Disorder) : 0 < Y ω := by
    dsimp [Y]
    exact profileP2Fun_pos_terminal β a b ν f A hνA hν0 hνpos (fun z => (hf z).1) ω
  have hXmeas : Measurable X := by
    change Measurable (fun ω => profileP2Fun β a b ν (fun _ => 1) ω)
    exact measurable_profileP2Fun_param β a b (fun _ => 1)
      (fun _ => measurable_const) measurable_id
  have hYmeas : Measurable Y := by
    change Measurable (fun ω => profileP2Fun β a b ν f ω)
    exact measurable_profileP2Fun_param β a b f (fun _ => measurable_const) measurable_id
  have hlogBound (ω : Disorder) : |Real.log (Y ω) - Real.log (X ω)| ≤ H := by
    dsimp [X, Y]
    exact FutureProfiles.abs_log_profileP2Fun_sub_le β a b ν A hνA hν0 hν1 f H hf ω
  have hpoint (ω : Disorder) : (Y ω)⁻¹ ≤ Real.exp H * (X ω)⁻¹ := by
    have hlog : Real.log (X ω) - Real.log (Y ω) ≤ H := by
      have hb := abs_le.mp (hlogBound ω)
      linarith
    have hratio : X ω / Y ω ≤ Real.exp H := by
      have hexp : Real.exp (Real.log (X ω) - Real.log (Y ω)) ≤ Real.exp H :=
        Real.exp_le_exp.mpr hlog
      rw [Real.exp_sub, Real.exp_log (hXpos ω), Real.exp_log (hYpos ω)] at hexp
      exact hexp
    have hmul : X ω * (Y ω)⁻¹ ≤ Real.exp H := by
      simpa [div_eq_mul_inv] using hratio
    calc
      (Y ω)⁻¹ = (X ω / Y ω) * (X ω)⁻¹ := by
        field_simp [ne_of_gt (hXpos ω), ne_of_gt (hYpos ω)]
      _ ≤ Real.exp H * (X ω)⁻¹ :=
        mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr (hXpos ω).le)
  have hXinv : Integrable (fun ω => (X ω)⁻¹) disorderLaw := by
    have hpow := OnePoint.integrable_rpow_profileP2Fun β a b ν A hνA hν0 hν1 (-1)
    have heq : (fun ω => X ω ^ (-1 : ℝ)) = fun ω => (X ω)⁻¹ := by
      funext ω
      rw [Real.rpow_neg_one]
    rw [heq] at hpow
    exact hpow
  have hYinv : Integrable (fun ω => (Y ω)⁻¹) disorderLaw := by
    have hmajor : Integrable (fun ω => Real.exp H * (X ω)⁻¹) disorderLaw :=
      hXinv.const_mul (Real.exp H)
    refine hmajor.mono' (hYmeas.inv.aestronglyMeasurable) ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hYpos ω).le)]
    have hmajor0 : 0 ≤ Real.exp H * (X ω)⁻¹ :=
      mul_nonneg (Real.exp_nonneg _) (inv_nonneg.mpr (hXpos ω).le)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hmajor0] using hpoint ω
  have hXneg := OnePoint.integral_rpow_neg_profileP2Fun_le hβ a b ν A
    hνA hν0 hν1 (p := 1) (by norm_num)
  have hXnegEq : (fun ω => X ω ^ (-1 : ℝ)) = fun ω => (X ω)⁻¹ := by
    funext ω
    rw [Real.rpow_neg_one]
  have hXnegInt : (∫ ω, (X ω)⁻¹ ∂disorderLaw) ≤ Q := by
    have h := hXneg
    rw [hXnegEq] at h
    have hq : 0 ≤ ∫ ω, X ω ^ 2 ∂disorderLaw :=
      integral_nonneg fun ω => sq_nonneg (X ω)
    have hpow : (∫ ω, X ω ^ 2 ∂disorderLaw) ^ (1 : ℝ) =
        ∫ ω, X ω ^ 2 ∂disorderLaw := Real.rpow_one _
    calc
      _ ≤ (∫ ω, X ω ^ 2 ∂disorderLaw) ^ (1 : ℝ) := by simpa [X] using h
      _ = ∫ ω, X ω ^ 2 ∂disorderLaw := hpow
      _ ≤ Q := hflatSq.2
  have hYintBound : (∫ ω, (Y ω)⁻¹ ∂disorderLaw) ≤ Real.exp H * Q := by
    calc
      _ ≤ ∫ ω, Real.exp H * (X ω)⁻¹ ∂disorderLaw :=
        integral_mono hYinv (hXinv.const_mul (Real.exp H)) (fun ω => hpoint ω)
      _ = Real.exp H * ∫ ω, (X ω)⁻¹ ∂disorderLaw := by rw [integral_const_mul]
      _ ≤ Real.exp H * Q := mul_le_mul_of_nonneg_left hXnegInt (Real.exp_nonneg _)
  have hnorm : eLpNorm (fun ω => (Y ω)⁻¹) 1 disorderLaw =
      ENNReal.ofReal (∫ ω, (Y ω)⁻¹ ∂disorderLaw) := by
    calc
      eLpNorm (fun ω => (Y ω)⁻¹) 1 disorderLaw =
          ∫⁻ ω, ‖(Y ω)⁻¹‖ₑ ∂disorderLaw :=
        eLpNorm_one_eq_lintegral_enorm (hYmeas.inv.aestronglyMeasurable)
      _ = ENNReal.ofReal (∫ ω, ‖(Y ω)⁻¹‖ ∂disorderLaw) :=
        (ofReal_integral_norm_eq_lintegral_enorm hYinv).symm
      _ = ENNReal.ofReal (∫ ω, (Y ω)⁻¹ ∂disorderLaw) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hYpos ω).le)]
  rw [hnorm]
  exact ENNReal.ofReal_le_ofReal (hYintBound.trans_eq (by ring))

end Critical2DKPZ.Smoothing

end
