/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.GlobalLogErrorBounds
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! # L² log stability from inverse moments -/

@[expose] public section

open MeasureTheory ENNReal
open scoped ENNReal

namespace Critical2DKPZ.Smoothing

/-- For positive measurable profiles with a square-integrable difference and integrable inverses, the `L²` logarithmic difference satisfies a one-third Hölder bound. -/
theorem eLpNorm_log_sub_le_of_sq_diff_inv (μ : Measure Disorder) (X Y : Disorder → ℝ)
    (hXmeas : Measurable X) (hYmeas : Measurable Y)
    (hXpos : ∀ ω, 0 < X ω) (hYpos : ∀ ω, 0 < Y ω)
    (hDsq : Integrable (fun ω => (X ω - Y ω) ^ 2) μ)
    (hXinv : Integrable (fun ω => (X ω)⁻¹) μ)
    (hYinv : Integrable (fun ω => (Y ω)⁻¹) μ) :
    eLpNorm (fun ω => Real.log (X ω) - Real.log (Y ω)) 2 μ ≤
      ENNReal.ofReal logHolderConstant * eLpNorm (fun ω => X ω - Y ω) 2 μ ^ ((1 : ℝ) / 3) *
        (eLpNorm (fun ω => (X ω)⁻¹) 1 μ ^ ((1 : ℝ) / 3) +
          eLpNorm (fun ω => (Y ω)⁻¹) 1 μ ^ ((1 : ℝ) / 3)) := by
  let D : Disorder → ℝ := fun ω => X ω - Y ω
  let U : Disorder → ℝ := fun ω => (X ω)⁻¹
  let V : Disorder → ℝ := fun ω => (Y ω)⁻¹
  let A : Disorder → ℝ := fun ω => ‖D ω‖ ^ ((1 : ℝ) / 3)
  let B : Disorder → ℝ := fun ω => ‖U ω‖ ^ ((1 : ℝ) / 3)
  let C : Disorder → ℝ := fun ω => ‖V ω‖ ^ ((1 : ℝ) / 3)
  let W : Disorder → ℝ := fun ω => B ω + C ω
  have hDmeas : Measurable D := hXmeas.sub hYmeas
  have hUmeas : Measurable U := hXmeas.inv
  have hVmeas : Measurable V := hYmeas.inv
  have hDmem : MemLp D 2 μ := by
    apply (memLp_two_iff_integrable_sq hDmeas.aestronglyMeasurable).2
    simpa only [D] using hDsq
  have hUmem : MemLp U 1 μ := memLp_one_iff_integrable.mpr (by simpa only [U] using hXinv)
  have hVmem : MemLp V 1 μ := memLp_one_iff_integrable.mpr (by simpa only [V] using hYinv)
  have hAmeas : AEStronglyMeasurable A μ := by
    dsimp [A]
    exact (Real.continuous_rpow_const (by norm_num)).comp_aestronglyMeasurable
      (hDmem.aestronglyMeasurable.norm)
  have hBmeas : AEStronglyMeasurable B μ := by
    dsimp [B]
    exact (Real.continuous_rpow_const (by norm_num)).comp_aestronglyMeasurable
      (hUmem.aestronglyMeasurable.norm)
  have hCmeas : AEStronglyMeasurable C μ := by
    dsimp [C]
    exact (Real.continuous_rpow_const (by norm_num)).comp_aestronglyMeasurable
      (hVmem.aestronglyMeasurable.norm)
  have hWmeas : AEStronglyMeasurable W μ := by
    dsimp [W]
    exact hBmeas.add hCmeas
  have hAeq : eLpNorm A 6 μ =
      eLpNorm D 2 μ ^ ((1 : ℝ) / 3) := by
    have h := eLpNorm_norm_rpow D hDmem.aestronglyMeasurable
      (p := ENNReal.ofReal 6) (by norm_num : 0 < (1 : ℝ) / 3)
    have hfrac : ENNReal.ofReal ((1 : ℝ) / 3) = (3 : ℝ≥0∞)⁻¹ := by
      calc
        _ = ENNReal.ofReal ((3 : ℝ)⁻¹) := by congr 1; norm_num
        _ = (ENNReal.ofReal (3 : ℝ))⁻¹ := ENNReal.ofReal_inv_of_pos (by norm_num)
        _ = (3 : ℝ≥0∞)⁻¹ := by norm_num
    have hfactor : ENNReal.ofReal 6 * ENNReal.ofReal ((1 : ℝ) / 3) =
        (2 : ℝ≥0∞) := by
      rw [hfrac]
      have hthree : (3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
      calc
        (ENNReal.ofReal 6 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ =
            6 * (3 : ℝ≥0∞)⁻¹ := by norm_num
        _ = 2 * ((3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹) := by ring
        _ = 2 := by rw [hthree]; norm_num
    rw [hfactor] at h
    simpa [A] using h
  have hBeq : eLpNorm B 3 μ =
      eLpNorm U 1 μ ^ ((1 : ℝ) / 3) := by
    have h := eLpNorm_norm_rpow U hUmem.aestronglyMeasurable
      (p := ENNReal.ofReal 3) (by norm_num : 0 < (1 : ℝ) / 3)
    have hfrac : ENNReal.ofReal ((1 : ℝ) / 3) = (3 : ℝ≥0∞)⁻¹ := by
      calc
        _ = ENNReal.ofReal ((3 : ℝ)⁻¹) := by congr 1; norm_num
        _ = (ENNReal.ofReal (3 : ℝ))⁻¹ := ENNReal.ofReal_inv_of_pos (by norm_num)
        _ = (3 : ℝ≥0∞)⁻¹ := by norm_num
    have hfactor : ENNReal.ofReal 3 * ENNReal.ofReal ((1 : ℝ) / 3) =
        (1 : ℝ≥0∞) := by
      rw [hfrac]
      have hthree : (3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
      calc
        (ENNReal.ofReal 3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ =
            (3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ := by norm_num
        _ = 1 := hthree
    rw [hfactor] at h
    simpa [B, Real.norm_eq_abs] using h
  have hCeq : eLpNorm C 3 μ =
      eLpNorm V 1 μ ^ ((1 : ℝ) / 3) := by
    have h := eLpNorm_norm_rpow V hVmem.aestronglyMeasurable
      (p := ENNReal.ofReal 3) (by norm_num : 0 < (1 : ℝ) / 3)
    have hfrac : ENNReal.ofReal ((1 : ℝ) / 3) = (3 : ℝ≥0∞)⁻¹ := by
      calc
        _ = ENNReal.ofReal ((3 : ℝ)⁻¹) := by congr 1; norm_num
        _ = (ENNReal.ofReal (3 : ℝ))⁻¹ := ENNReal.ofReal_inv_of_pos (by norm_num)
        _ = (3 : ℝ≥0∞)⁻¹ := by norm_num
    have hfactor : ENNReal.ofReal 3 * ENNReal.ofReal ((1 : ℝ) / 3) =
        (1 : ℝ≥0∞) := by
      rw [hfrac]
      have hthree : (3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ = 1 :=
        ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
      calc
        (ENNReal.ofReal 3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ =
            (3 : ℝ≥0∞) * (3 : ℝ≥0∞)⁻¹ := by norm_num
        _ = 1 := hthree
    rw [hfactor] at h
    simpa [C, Real.norm_eq_abs] using h
  have htriple : HolderTriple (6 : ℝ≥0∞) 3 2 := by
    constructor
    have h6 : (6 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 : ℝ) / 6) := by
      calc
        (6 : ℝ≥0∞)⁻¹ = (ENNReal.ofReal (6 : ℝ))⁻¹ := by norm_num
        _ = ENNReal.ofReal ((6 : ℝ)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos (by norm_num)).symm
        _ = ENNReal.ofReal ((1 : ℝ) / 6) := by congr 1; norm_num
    have h3 : (3 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 : ℝ) / 3) := by
      calc
        (3 : ℝ≥0∞)⁻¹ = (ENNReal.ofReal (3 : ℝ))⁻¹ := by norm_num
        _ = ENNReal.ofReal ((3 : ℝ)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos (by norm_num)).symm
        _ = ENNReal.ofReal ((1 : ℝ) / 3) := by congr 1; norm_num
    have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 : ℝ) / 2) := by
      calc
        (2 : ℝ≥0∞)⁻¹ = (ENNReal.ofReal (2 : ℝ))⁻¹ := by norm_num
        _ = ENNReal.ofReal ((2 : ℝ)⁻¹) :=
          (ENNReal.ofReal_inv_of_pos (by norm_num)).symm
        _ = ENNReal.ofReal ((1 : ℝ) / 2) := by congr 1; norm_num
    rw [h6, h3, h2]
    calc
      ENNReal.ofReal ((1 : ℝ) / 6) + ENNReal.ofReal ((1 : ℝ) / 3) =
          ENNReal.ofReal ((1 : ℝ) / 6 + (1 : ℝ) / 3) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ = ENNReal.ofReal ((1 : ℝ) / 2) := by congr 1; norm_num
  have hprod : eLpNorm (fun ω => A ω * W ω) 2 μ ≤
      eLpNorm A 6 μ * eLpNorm W 3 μ := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := (6 : ℝ≥0∞)) (q := 3) (r := 2)
        (hpqr := htriple) (fun x y : ℝ => x * y) 1 (by fun_prop) hAmeas hWmeas <|
        Filter.Eventually.of_forall fun ω => by simp [norm_mul]
    simpa [Pi.mul_apply] using h
  have hWnorm : eLpNorm W 3 μ ≤ eLpNorm B 3 μ + eLpNorm C 3 μ := by
    exact eLpNorm_add_le (p := (3 : ℝ≥0∞)) (μ := μ) (by norm_num)
  have hlogmeas : AEStronglyMeasurable
      (fun ω => Real.log (X ω) - Real.log (Y ω)) μ :=
    (hXmeas.log.sub hYmeas.log).aestronglyMeasurable
  have hpoint (ω : Disorder) :
      |Real.log (X ω) - Real.log (Y ω)| ≤
        logHolderConstant * (A ω * W ω) := by
    have hlog := (Classical.choose_spec abs_log_sub_log_le_rpow).2
      (X ω) (Y ω) (hXpos ω) (hYpos ω)
    have hB : B ω = (X ω) ^ (-(1 : ℝ) / 3) := by
      dsimp [B, U]
      rw [abs_of_nonneg (inv_nonneg.mpr (hXpos ω).le)]
      rw [← Real.rpow_neg_one (X ω), ← Real.rpow_mul (hXpos ω).le]
      congr 1
      ring
    have hC : C ω = (Y ω) ^ (-(1 : ℝ) / 3) := by
      dsimp [C, V]
      rw [abs_of_nonneg (inv_nonneg.mpr (hYpos ω).le)]
      rw [← Real.rpow_neg_one (Y ω), ← Real.rpow_mul (hYpos ω).le]
      congr 1
      ring
    have hA : A ω = |X ω - Y ω| ^ ((1 : ℝ) / 3) := by
      simp [A, D, Real.norm_eq_abs]
    simp only [hA, hB, hC, W]
    calc
      |Real.log (X ω) - Real.log (Y ω)| ≤
          Classical.choose abs_log_sub_log_le_rpow *
            |X ω - Y ω| ^ ((1 : ℝ) / 3) *
              ((X ω) ^ (-(1 : ℝ) / 3) + (Y ω) ^ (-(1 : ℝ) / 3)) := hlog
      _ = logHolderConstant *
          (|X ω - Y ω| ^ ((1 : ℝ) / 3) *
            ((X ω) ^ (-(1 : ℝ) / 3) + (Y ω) ^ (-(1 : ℝ) / 3))) := by
          unfold logHolderConstant
          ring
      _ = _ := by ring
  have hmono : eLpNorm (fun ω => Real.log (X ω) - Real.log (Y ω)) 2 μ ≤
      eLpNorm (fun ω => logHolderConstant * (A ω * W ω)) 2 μ := by
    apply eLpNorm_mono_ae hlogmeas
    filter_upwards [] with ω
    have hnonneg : 0 ≤ logHolderConstant * (A ω * W ω) := by
      apply mul_nonneg logHolderConstant_pos.le
      apply mul_nonneg
      · exact Real.rpow_nonneg (norm_nonneg _) _
      · unfold W B C U V
        exact add_nonneg
          (Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_nonneg (norm_nonneg _) _)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hpoint ω
  calc
    _ ≤ eLpNorm (fun ω => logHolderConstant * (A ω * W ω)) 2 μ := hmono
    _ = ENNReal.ofReal logHolderConstant * eLpNorm (fun ω => A ω * W ω) 2 μ := by
      have hfun : (fun ω => logHolderConstant * (A ω * W ω)) =
          logHolderConstant • (fun ω => A ω * W ω) := by
        funext ω
        simp [smul_eq_mul]
      rw [hfun, eLpNorm_const_smul]
      rw [Real.enorm_eq_ofReal logHolderConstant_pos.le]
    _ ≤ ENNReal.ofReal logHolderConstant * (eLpNorm A 6 μ * eLpNorm W 3 μ) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ ENNReal.ofReal logHolderConstant *
          (eLpNorm A 6 μ * (eLpNorm B 3 μ + eLpNorm C 3 μ)) := by
      gcongr
    _ = _ := by
      rw [hAeq, hBeq, hCeq]
      simp [D, U, V, mul_assoc]

end Critical2DKPZ.Smoothing

end
