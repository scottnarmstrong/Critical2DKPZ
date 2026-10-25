/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ScalarCutIdentity
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Uniqueness for the scalar cut kernel -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Replacing the extended cut kernel by its real-valued `toReal` representative
does not change its finite double Laplace transform. -/
theorem scalarCutKernel_toReal_doubleLaplaceENN_of_lt {θ rateT rateS : ℝ}
    (hT : 0 < rateT) (hTS : rateT < rateS)
    (hθT : θ < Real.log rateT) (hθS : θ < Real.log rateS) :
    (∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v)) *
        (scalarCutKernelENN θ s v).toReal)) =
      ENNReal.ofReal ((Real.log rateS - θ)⁻¹ *
        ((Real.log rateT - θ)⁻¹ *
          ((Real.log rateS - Real.log rateT) / (rateS - rateT)))) := by
  let μ : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))
  let K : ℝ × ℝ → ℝ≥0∞ := fun p => scalarCutKernelENN θ p.1 p.2
  let W : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-(rateS * p.1 + rateT * p.2))) * K p
  let V : ℝ × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (-(rateS * p.1 + rateT * p.2)) * (K p).toReal)
  have hK : Measurable K := by
    exact measurable_scalarCutKernelENN θ
  have hW : Measurable W := by
    dsimp [W]
    exact (by fun_prop : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(rateS * p.1 + rateT * p.2))))).mul hK
  have hV : Measurable V := by
    dsimp [V]
    exact (((by fun_prop : Measurable (fun p : ℝ × ℝ =>
      Real.exp (-(rateS * p.1 + rateT * p.2)))).mul
        hK.ennreal_toReal).ennreal_ofReal)
  have hprod : (∫⁻ p, W p ∂
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))) =
      ∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ), W (s, v) := by
    exact lintegral_prod (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := volume.restrict (Ioi (0 : ℝ))) W hW.aemeasurable
  have hmass : (∫⁻ p, W p ∂μ) =
      ENNReal.ofReal ((Real.log rateS - θ)⁻¹ *
        ((Real.log rateT - θ)⁻¹ *
          ((Real.log rateS - Real.log rateT) / (rateS - rateT)))) := by
    calc
      (∫⁻ p, W p ∂μ) =
          ∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v))) *
              scalarCutKernelENN θ s v := by
                simpa only [μ, W, K] using hprod
      _ = ENNReal.ofReal ((Real.log rateS - θ)⁻¹ *
            ((Real.log rateT - θ)⁻¹ *
              ((Real.log rateS - Real.log rateT) / (rateS - rateT)))) :=
                scalarCut_doubleLaplaceENN_of_lt hT hTS hθT hθS
  have hmass_ne : (∫⁻ p, W p ∂μ) ≠ ⊤ := by
    rw [hmass]
    exact ENNReal.ofReal_ne_top
  have hWtop : ∀ᵐ p ∂μ, W p < ⊤ := ae_lt_top hW hmass_ne
  have hKtop : ∀ᵐ p ∂μ, K p < ⊤ := by
    filter_upwards [hWtop] with p hp
    by_contra hk
    have hk' : K p = ⊤ := top_unique (le_of_not_gt hk)
    have hweight : ENNReal.ofReal (Real.exp (-(rateS * p.1 + rateT * p.2))) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
    have htop : W p = ⊤ := by
      dsimp [W, K]
      exact ENNReal.mul_eq_top.mpr (Or.inl ⟨hweight, hk'⟩)
    exact (not_lt_of_ge (le_of_eq htop.symm)) hp
  have hVeqW : V =ᵐ[μ] W := by
    filter_upwards [hKtop] with p hp
    dsimp [V, W, K]
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_toReal (ne_of_lt hp)]
  calc
    (∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(rateS * s + rateT * v)) *
          (scalarCutKernelENN θ s v).toReal)) = ∫⁻ p, V p ∂μ := by
      symm
      simpa only [μ, V, K] using lintegral_prod V hV.aemeasurable
    _ = ∫⁻ p, W p ∂μ := lintegral_congr_ae hVeqW
    _ = ENNReal.ofReal ((Real.log rateS - θ)⁻¹ *
        ((Real.log rateT - θ)⁻¹ *
          ((Real.log rateS - Real.log rateT) / (rateS - rateT)))) := hmass

/-- The scalar cut kernel agrees almost everywhere with the scalar density at
the sum of the two time variables. -/
theorem scalarCutKernel_toReal_ae_eq_scalarDensity_sum (θ : ℝ) :
    (fun p : Plane =>
      (scalarCutKernelENN θ (planeCoordEquiv p).1 (planeCoordEquiv p).2).toReal) =ᵐ[
        volume.restrict Critical2DKPZ.Analysis.positiveQuadrant]
      fun p => scalarDensity θ (p 0 + p 1) := by
  let μ : Measure Plane := volume.restrict Critical2DKPZ.Analysis.positiveQuadrant
  let K : Plane → ℝ := fun p =>
    (scalarCutKernelENN θ (planeCoordEquiv p).1 (planeCoordEquiv p).2).toReal
  let J : Plane → ℝ := fun p => scalarDensity θ (p 0 + p 1)
  have hKm : Measurable K := by
    dsimp [K]
    exact (measurable_scalarCutKernelENN θ).comp planeCoordEquiv.measurable
      |>.ennreal_toReal
  have hJm : Measurable J := by
    dsimp [J]
    exact measurable_scalarDensity.comp (by fun_prop :
      Measurable (fun p : Plane => (θ, p 0 + p 1)))
  have hQ : MeasurableSet Critical2DKPZ.Analysis.positiveQuadrant := by
    change MeasurableSet ({p : Plane | 0 < p 0} ∩ {p : Plane | 0 < p 1})
    exact (measurableSet_lt measurable_const (by fun_prop)).inter
      (measurableSet_lt measurable_const (by fun_prop))
  have hK0 : ∀ᵐ p ∂μ, 0 ≤ K p := by
    filter_upwards with p
    exact ENNReal.toReal_nonneg
  have hJ0 : ∀ᵐ p ∂μ, 0 ≤ J p := by
    filter_upwards [ae_restrict_mem hQ] with p hp
    change 0 < p 0 ∧ 0 < p 1 at hp
    exact (scalarDensity_pos θ (by linarith)).le
  let weight : ℝ → ℝ → Plane → ℝ := fun rateA rateB p =>
    Real.exp (-(rateA * p 0 + rateB * p 1))
  have hKweight_meas (rateA rateB : ℝ) :
      Measurable (fun p : Plane => weight rateA rateB p * K p) := by
    dsimp [weight]
    exact (by fun_prop : Measurable (fun p : Plane =>
      Real.exp (-(rateA * p 0 + rateB * p 1)))).mul hKm
  have hJweight_meas (rateA rateB : ℝ) :
      Measurable (fun p : Plane => weight rateA rateB p * J p) := by
    dsimp [weight]
    exact (by fun_prop : Measurable (fun p : Plane =>
      Real.exp (-(rateA * p 0 + rateB * p 1)))).mul hJm
  have hcoordK (rateA rateB : ℝ) : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(rateA * q.1 + rateB * q.2)) *
        (scalarCutKernelENN θ q.1 q.2).toReal)) := by
    exact (((by fun_prop : Measurable (fun q : ℝ × ℝ =>
      Real.exp (-(rateA * q.1 + rateB * q.2)))).mul
        (measurable_scalarCutKernelENN θ).ennreal_toReal).ennreal_ofReal)
  have hcoordJ (rateA rateB : ℝ) : Measurable (fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(rateA * q.1 + rateB * q.2)) *
        scalarDensity θ (q.1 + q.2))) := by
    exact (((by fun_prop : Measurable (fun q : ℝ × ℝ =>
      Real.exp (-(rateA * q.1 + rateB * q.2)))).mul
        (measurable_scalarDensity.comp (by fun_prop :
          Measurable (fun q : ℝ × ℝ => (θ, q.1 + q.2))))).ennreal_ofReal)
  have hKmass (rateA rateB : ℝ) (hB : 0 < rateB) (hBA : rateB < rateA)
      (hθB : θ < Real.log rateB) (hθA : θ < Real.log rateA) :
      (∫⁻ p, ENNReal.ofReal (weight rateA rateB p * K p) ∂μ) =
        ENNReal.ofReal ((Real.log rateA - θ)⁻¹ *
          ((Real.log rateB - θ)⁻¹ *
            ((Real.log rateA - Real.log rateB) / (rateA - rateB)))) := by
    have hplane := lintegral_plane_positiveQuadrant (F := fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(rateA * q.1 + rateB * q.2)) *
        (scalarCutKernelENN θ q.1 q.2).toReal)) (hcoordK rateA rateB)
    calc
      (∫⁻ p, ENNReal.ofReal (weight rateA rateB p * K p) ∂μ) =
          ∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(rateA * s + rateB * v)) *
              (scalarCutKernelENN θ s v).toReal) := by
                change (∫⁻ p in Critical2DKPZ.Analysis.positiveQuadrant,
                  ENNReal.ofReal (Real.exp (-(rateA * p 0 + rateB * p 1)) *
                    (scalarCutKernelENN θ (planeCoordEquiv p).1
                      (planeCoordEquiv p).2).toReal)) = _
                simpa [planeCoordEquiv, MeasurableEquiv.trans_apply] using hplane
      _ = ENNReal.ofReal ((Real.log rateA - θ)⁻¹ *
            ((Real.log rateB - θ)⁻¹ *
              ((Real.log rateA - Real.log rateB) / (rateA - rateB)))) :=
            scalarCutKernel_toReal_doubleLaplaceENN_of_lt hB hBA hθB hθA
  have hJmass (rateA rateB : ℝ) (hB : 0 < rateB) (hBA : rateB < rateA)
      (hθB : θ < Real.log rateB) (hθA : θ < Real.log rateA) :
      (∫⁻ p, ENNReal.ofReal (weight rateA rateB p * J p) ∂μ) =
        ENNReal.ofReal (((Real.log rateB - θ)⁻¹ -
          (Real.log rateA - θ)⁻¹) / (rateA - rateB)) := by
    have hplane := lintegral_plane_positiveQuadrant (F := fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(rateA * q.1 + rateB * q.2)) *
        scalarDensity θ (q.1 + q.2))) (hcoordJ rateA rateB)
    calc
      (∫⁻ p, ENNReal.ofReal (weight rateA rateB p * J p) ∂μ) =
          ∫⁻ s in Ioi (0 : ℝ), ∫⁻ v in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(rateA * s + rateB * v)) *
              scalarDensity θ (s + v)) := by
                change (∫⁻ p in Critical2DKPZ.Analysis.positiveQuadrant,
                  ENNReal.ofReal (Real.exp (-(rateA * p 0 + rateB * p 1)) *
                    scalarDensity θ (p 0 + p 1))) = _
                simpa [planeCoordEquiv, MeasurableEquiv.trans_apply] using hplane
      _ = ENNReal.ofReal (((Real.log rateB - θ)⁻¹ -
            (Real.log rateA - θ)⁻¹) / (rateA - rateB)) :=
            scalarDensity_sum_doubleLaplaceENN_of_lt hB hBA hθB hθA
  have hKint (rateA rateB : ℝ) (hA : rateA ∈ Ioo (Real.exp θ + 2 - (1 / 4 : ℝ))
      (Real.exp θ + 2 + (1 / 4 : ℝ)))
      (hB : rateB ∈ Ioo (Real.exp θ + 1 - (1 / 4 : ℝ))
        (Real.exp θ + 1 + (1 / 4 : ℝ))) :
      Integrable (fun p : Plane => weight rateA rateB p * K p) μ := by
    have hA0 : Real.exp θ < rateA := by rcases hA with ⟨hlo, _⟩; linarith
    have hB0 : Real.exp θ < rateB := by rcases hB with ⟨hlo, _⟩; linarith
    have hBA : rateB < rateA := by
      rcases hA with ⟨hAl, _⟩
      rcases hB with ⟨_, hBu⟩
      linarith
    have hBpos : 0 < rateB := lt_trans (Real.exp_pos θ) hB0
    have hθB : θ < Real.log rateB := (Real.lt_log_iff_exp_lt hBpos).2 hB0
    have hθA : θ < Real.log rateA :=
      (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos θ) hA0)).2 hA0
    have hmass := hKmass rateA rateB hBpos hBA hθB hθA
    apply (lintegral_ofReal_ne_top_iff_integrable
      (hKweight_meas rateA rateB).aestronglyMeasurable
      (by filter_upwards [hK0] with p hp; exact mul_nonneg (Real.exp_pos _).le hp)).mp
    rw [hmass]
    exact ENNReal.ofReal_ne_top
  have hJint (rateA rateB : ℝ) (hA : rateA ∈ Ioo (Real.exp θ + 2 - (1 / 4 : ℝ))
      (Real.exp θ + 2 + (1 / 4 : ℝ)))
      (hB : rateB ∈ Ioo (Real.exp θ + 1 - (1 / 4 : ℝ))
        (Real.exp θ + 1 + (1 / 4 : ℝ))) :
      Integrable (fun p : Plane => weight rateA rateB p * J p) μ := by
    have hA0 : Real.exp θ < rateA := by rcases hA with ⟨hlo, _⟩; linarith
    have hB0 : Real.exp θ < rateB := by rcases hB with ⟨hlo, _⟩; linarith
    have hBA : rateB < rateA := by
      rcases hA with ⟨hAl, _⟩
      rcases hB with ⟨_, hBu⟩
      linarith
    have hBpos : 0 < rateB := lt_trans (Real.exp_pos θ) hB0
    have hθB : θ < Real.log rateB := (Real.lt_log_iff_exp_lt hBpos).2 hB0
    have hθA : θ < Real.log rateA :=
      (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos θ) hA0)).2 hA0
    have hmass := hJmass rateA rateB hBpos hBA hθB hθA
    apply (lintegral_ofReal_ne_top_iff_integrable
      (hJweight_meas rateA rateB).aestronglyMeasurable
      (by filter_upwards [hJ0] with p hp; exact mul_nonneg (Real.exp_pos _).le hp)).mp
    rw [hmass]
    exact ENNReal.ofReal_ne_top
  have hKlap (rateA rateB : ℝ) (hA : rateA ∈ Ioo (Real.exp θ + 2 - (1 / 4 : ℝ))
      (Real.exp θ + 2 + (1 / 4 : ℝ)))
      (hB : rateB ∈ Ioo (Real.exp θ + 1 - (1 / 4 : ℝ))
        (Real.exp θ + 1 + (1 / 4 : ℝ))) :
      (∫ p, weight rateA rateB p * K p ∂μ) =
        (∫⁻ p, ENNReal.ofReal (weight rateA rateB p * K p) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards [hK0] with p hp; exact mul_nonneg (Real.exp_pos _).le hp)
      (hKweight_meas rateA rateB).aestronglyMeasurable
  have hJlap (rateA rateB : ℝ) (hA : rateA ∈ Ioo (Real.exp θ + 2 - (1 / 4 : ℝ))
      (Real.exp θ + 2 + (1 / 4 : ℝ)))
      (hB : rateB ∈ Ioo (Real.exp θ + 1 - (1 / 4 : ℝ))
        (Real.exp θ + 1 + (1 / 4 : ℝ))) :
      (∫ p, weight rateA rateB p * J p ∂μ) =
        (∫⁻ p, ENNReal.ofReal (weight rateA rateB p * J p) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards [hJ0] with p hp; exact mul_nonneg (Real.exp_pos _).le hp)
      (hJweight_meas rateA rateB).aestronglyMeasurable
  have hLap (rateA rateB : ℝ)
      (hA : rateA ∈ Ioo (Real.exp θ + 2 - (1 / 4 : ℝ))
        (Real.exp θ + 2 + (1 / 4 : ℝ)))
      (hB : rateB ∈ Ioo (Real.exp θ + 1 - (1 / 4 : ℝ))
        (Real.exp θ + 1 + (1 / 4 : ℝ))) :
      (∫ p, weight rateA rateB p * K p ∂μ) =
        ∫ p, weight rateA rateB p * J p ∂μ := by
    have hA0 : Real.exp θ < rateA := by rcases hA with ⟨hlo, _⟩; linarith
    have hB0 : Real.exp θ < rateB := by rcases hB with ⟨hlo, _⟩; linarith
    have hBA : rateB < rateA := by
      rcases hA with ⟨hAl, _⟩
      rcases hB with ⟨_, hBu⟩
      linarith
    have hBpos : 0 < rateB := lt_trans (Real.exp_pos θ) hB0
    have hθB : θ < Real.log rateB := (Real.lt_log_iff_exp_lt hBpos).2 hB0
    have hθA : θ < Real.log rateA :=
      (Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos θ) hA0)).2 hA0
    have hform : (Real.log rateA - θ)⁻¹ *
        ((Real.log rateB - θ)⁻¹ *
          ((Real.log rateA - Real.log rateB) / (rateA - rateB))) =
        ((Real.log rateB - θ)⁻¹ - (Real.log rateA - θ)⁻¹) /
          (rateA - rateB) := by
      have hAne : Real.log rateA - θ ≠ 0 := ne_of_gt (sub_pos.mpr hθA)
      have hBne : Real.log rateB - θ ≠ 0 := ne_of_gt (sub_pos.mpr hθB)
      have hdne : rateA - rateB ≠ 0 := ne_of_gt (sub_pos.mpr hBA)
      field_simp
      ring
    rw [hKlap rateA rateB hA hB, hKmass rateA rateB hBpos hBA hθB hθA,
      hJlap rateA rateB hA hB, hJmass rateA rateB hBpos hBA hθB hθA,
      hform]
  exact Critical2DKPZ.Analysis.ae_eq_of_bivariate_laplace_eq_on_boxes
    (rate₁ := Real.exp θ + 2) (rate₂ := Real.exp θ + 1) (ε := 1 / 4)
    (by norm_num) hKm.aemeasurable hJm.aemeasurable hK0 hJ0 hKint hJint hLap

/-- The extended scalar cut kernel is almost everywhere the finite ENNReal
representative of the scalar density at the sum of the two cut durations. -/
theorem scalarCutKernelENN_ae_eq_ofReal_scalarDensity_sum (θ : ℝ) :
    (fun p : Plane => scalarCutKernelENN θ (planeCoordEquiv p).1
      (planeCoordEquiv p).2) =ᵐ[volume.restrict Critical2DKPZ.Analysis.positiveQuadrant]
      fun p => ENNReal.ofReal (scalarDensity θ (p 0 + p 1)) := by
  filter_upwards [scalarCutKernel_toReal_ae_eq_scalarDensity_sum θ,
    ae_restrict_mem (by
      change MeasurableSet ({p : Plane | 0 < p 0} ∩ {p : Plane | 0 < p 1})
      exact (measurableSet_lt measurable_const (by fun_prop)).inter
        (measurableSet_lt measurable_const (by fun_prop)))] with p hp hmem
  change 0 < p 0 ∧ 0 < p 1 at hmem
  let K : ℝ≥0∞ := scalarCutKernelENN θ (planeCoordEquiv p).1 (planeCoordEquiv p).2
  have hj : 0 < scalarDensity θ (p 0 + p 1) :=
    scalarDensity_pos θ (by linarith)
  have hK : K ≠ ⊤ := by
    intro htop
    have hzero : K.toReal = 0 := by rw [htop, ENNReal.toReal_top]
    change K.toReal = scalarDensity θ (p 0 + p 1) at hp
    rw [hzero] at hp
    exact (ne_of_gt hj) hp.symm
  change K = ENNReal.ofReal (scalarDensity θ (p 0 + p 1))
  calc
    K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK).symm
    _ = ENNReal.ofReal (scalarDensity θ (p 0 + p 1)) := by rw [hp]

end Critical2DKPZ.SHF.Flow

end
