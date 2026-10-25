/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! # Logarithmic and interpolation inequalities for smoothing -/

@[expose] public section

open MeasureTheory ENNReal

namespace Critical2DKPZ.Smoothing

private theorem log_one_add_le_three_rpow {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ 3 * x ^ ((1 : ℝ) / 3) := by
  by_cases hx1 : x ≤ 1
  · have hlog : Real.log (1 + x) ≤ x := by
      calc
        Real.log (1 + x) ≤ (1 + x) - 1 :=
          Real.log_le_sub_one_of_pos (by linarith)
        _ = x := by ring
    calc
      Real.log (1 + x) ≤ x := hlog
      _ ≤ x ^ ((1 : ℝ) / 3) :=
        Real.self_le_rpow_of_le_one hx hx1 (by norm_num)
      _ ≤ 3 * x ^ ((1 : ℝ) / 3) := by
        nlinarith [Real.rpow_nonneg hx ((1 : ℝ) / 3)]
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    have hxpos : 0 < x := zero_lt_one.trans_le hx1'
    have htpos : 0 < x ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hxpos _
    have hlogx : Real.log x ≤ 3 * (x ^ ((1 : ℝ) / 3) - 1) := by
      have hlogt := Real.log_le_sub_one_of_pos htpos
      have hident : Real.log x = 3 * Real.log (x ^ ((1 : ℝ) / 3)) := by
        rw [Real.log_rpow hxpos]
        ring
      linarith
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    calc
      Real.log (1 + x) ≤ Real.log (2 * x) :=
        Real.log_le_log (by linarith) (by nlinarith)
      _ = Real.log 2 + Real.log x := by rw [Real.log_mul (by norm_num) hxpos.ne']
      _ ≤ 1 + 3 * (x ^ ((1 : ℝ) / 3) - 1) := add_le_add hlog2 hlogx
      _ ≤ 3 * x ^ ((1 : ℝ) / 3) := by nlinarith

private theorem abs_log_difference_le_ordered {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hvu : v ≤ u) :
    |Real.log u - Real.log v| ≤
      3 * |u - v| ^ ((1 : ℝ) / 3) *
        (u ^ (-(1 : ℝ) / 3) + v ^ (-(1 : ℝ) / 3)) := by
  let d : ℝ := (u - v) / v
  have hd : 0 ≤ d := by dsimp [d]; exact div_nonneg (sub_nonneg.mpr hvu) hv.le
  have hratio : u / v = 1 + d := by
    dsimp [d]
    field_simp
    ring
  have hlogratio : Real.log u - Real.log v = Real.log (1 + d) := by
    rw [← Real.log_div hu.ne' hv.ne', hratio]
  have hpow : d ^ ((1 : ℝ) / 3) =
      |u - v| ^ ((1 : ℝ) / 3) * v ^ (-(1 : ℝ) / 3) := by
    calc
      d ^ ((1 : ℝ) / 3) = (u - v) ^ ((1 : ℝ) / 3) / v ^ ((1 : ℝ) / 3) := by
        dsimp [d]
        exact Real.div_rpow (sub_nonneg.mpr hvu) hv.le _
      _ = |u - v| ^ ((1 : ℝ) / 3) * v ^ (-(1 : ℝ) / 3) := by
        have hexp : (-(1 : ℝ) / 3) = -((1 : ℝ) / 3) := by ring
        rw [abs_of_nonneg (sub_nonneg.mpr hvu), hexp, Real.rpow_neg hv.le]
        ring
  have hlognonneg : 0 ≤ Real.log u - Real.log v := by
    exact sub_nonneg.mpr (Real.log_le_log hv hvu)
  calc
    |Real.log u - Real.log v| = Real.log (1 + d) := by
      rw [abs_of_nonneg hlognonneg, hlogratio]
    _ ≤ 3 * d ^ ((1 : ℝ) / 3) := log_one_add_le_three_rpow hd
    _ = 3 * |u - v| ^ ((1 : ℝ) / 3) * v ^ (-(1 : ℝ) / 3) := by rw [hpow]; ring
    _ ≤ 3 * |u - v| ^ ((1 : ℝ) / 3) *
        (u ^ (-(1 : ℝ) / 3) + v ^ (-(1 : ℝ) / 3)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_add_of_nonneg_left (Real.rpow_nonneg (le_of_lt hu) _)

/-- The logarithm on positive arguments satisfies equation (4.31) with exponent one third. -/
theorem abs_log_sub_log_le_rpow : ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ, 0 < u → 0 < v →
    |Real.log u - Real.log v| ≤
      C * |u - v| ^ ((1 : ℝ) / 3) * (u ^ (-(1 : ℝ) / 3) + v ^ (-(1 : ℝ) / 3)) := by
  refine ⟨3, by norm_num, ?_⟩
  intro u v hu hv
  rcases le_total v u with hvu | huv
  · exact abs_log_difference_le_ordered hu hv hvu
  · have h := abs_log_difference_le_ordered hv hu huv
    simpa [abs_sub_comm, add_comm, mul_comm, mul_left_comm, mul_assoc] using h

/-- The L² norm is bounded by the one-third power of the L¹ norm times the two-thirds power of the L⁴ norm, as in equation (4.36). -/
theorem eLpNorm_two_le_interpolation {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (G : Ω → ℝ)
    (hG : AEStronglyMeasurable G μ) :
    eLpNorm G 2 μ ≤ eLpNorm G 1 μ ^ ((1 : ℝ) / 3) * eLpNorm G 4 μ ^ ((2 : ℝ) / 3) := by
  let F : Ω → ℝ := fun x => ‖G x‖ ^ ((1 : ℝ) / 3)
  let H : Ω → ℝ := fun x => ‖G x‖ ^ ((2 : ℝ) / 3)
  have hF : AEStronglyMeasurable F μ := by
    exact (Real.continuous_rpow_const (by norm_num)).comp_aestronglyMeasurable
      hG.norm
  have hH : AEStronglyMeasurable H μ := by
    exact (Real.continuous_rpow_const (by norm_num)).comp_aestronglyMeasurable
      hG.norm
  have hprod (x : Ω) : F x * H x = ‖G x‖ := by
    change ‖G x‖ ^ ((1 : ℝ) / 3) * ‖G x‖ ^ ((2 : ℝ) / 3) = ‖G x‖
    rw [← Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) (by norm_num)]
    norm_num
  have hFnorm : eLpNorm F 3 μ = eLpNorm G 1 μ ^ ((1 : ℝ) / 3) := by
    have h := eLpNorm_norm_rpow G hG (p := (3 : ℝ≥0∞))
      (q := (1 : ℝ) / 3) (by norm_num)
    have hfactor : (3 : ℝ≥0∞) * ENNReal.ofReal ((1 : ℝ) / 3) = 1 := by
      have hfrac : ENNReal.ofReal ((1 : ℝ) / 3) = (3 : ℝ≥0∞)⁻¹ := by
        rw [show ((1 : ℝ) / 3) = (3 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num
      rw [hfrac]
      exact ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top
    rw [hfactor] at h
    simpa only [F] using h
  have hHnorm : eLpNorm H 6 μ = eLpNorm G 4 μ ^ ((2 : ℝ) / 3) := by
    have h := eLpNorm_norm_rpow G hG (p := (6 : ℝ≥0∞))
      (q := (2 : ℝ) / 3) (by norm_num)
    have hfactor : (6 : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) / 3) = 4 := by
      have hfrac : ENNReal.ofReal ((2 : ℝ) / 3) = (3 : ℝ≥0∞)⁻¹ * 2 := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        rw [div_eq_mul_inv]
        norm_num
        ac_rfl
      rw [hfrac]
      calc
        (6 : ℝ≥0∞) * ((3 : ℝ≥0∞)⁻¹ * 2) =
            (2 * (3 * (3 : ℝ≥0∞)⁻¹)) * 2 := by ring
        _ = 4 := by
          rw [ENNReal.mul_inv_cancel (by norm_num) ENNReal.ofNat_ne_top]
          norm_num
    rw [hfactor] at h
    simpa only [H] using h
  have htriple : HolderTriple (3 : ℝ≥0∞) 6 2 := by
    constructor
    have h3 : (3 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 : ℝ) / 3) := by
      calc
        (3 : ℝ≥0∞)⁻¹ = (ENNReal.ofReal (3 : ℝ))⁻¹ := by norm_num
        _ = ENNReal.ofReal ((3 : ℝ)⁻¹) := (ENNReal.ofReal_inv_of_pos (by norm_num)).symm
        _ = ENNReal.ofReal ((1 : ℝ) / 3) := by congr 1; norm_num
    have h6 : (6 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 : ℝ) / 6) := by
      calc
        (6 : ℝ≥0∞)⁻¹ = (ENNReal.ofReal (6 : ℝ))⁻¹ := by norm_num
        _ = ENNReal.ofReal ((6 : ℝ)⁻¹) := (ENNReal.ofReal_inv_of_pos (by norm_num)).symm
        _ = ENNReal.ofReal ((1 : ℝ) / 6) := by congr 1; norm_num
    have h2 : (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal ((1 : ℝ) / 2) := by
      calc
        (2 : ℝ≥0∞)⁻¹ = (ENNReal.ofReal (2 : ℝ))⁻¹ := by norm_num
        _ = ENNReal.ofReal ((2 : ℝ)⁻¹) := (ENNReal.ofReal_inv_of_pos (by norm_num)).symm
        _ = ENNReal.ofReal ((1 : ℝ) / 2) := by congr 1; norm_num
    rw [h3, h6, h2]
    calc
      ENNReal.ofReal ((1 : ℝ) / 3) + ENNReal.ofReal ((1 : ℝ) / 6) =
          ENNReal.ofReal ((1 : ℝ) / 3 + (1 : ℝ) / 6) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
      _ = ENNReal.ofReal ((1 : ℝ) / 2) := by congr 1; norm_num
  have hholder : eLpNorm (fun x => F x * H x) 2 μ ≤ eLpNorm F 3 μ * eLpNorm H 6 μ := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (p := (3 : ℝ≥0∞)) (q := 6) (r := 2)
        (hpqr := htriple) (fun x y : ℝ => x * y) 1 (by fun_prop) hF hH <|
        Filter.Eventually.of_forall fun x => by simp [norm_mul])
  calc
    eLpNorm G 2 μ = eLpNorm (fun x => ‖G x‖) 2 μ := (eLpNorm_norm G hG).symm
    _ = eLpNorm (fun x => F x * H x) 2 μ := by
      congr 1
      funext x
      exact (hprod x).symm
    _ ≤ eLpNorm F 3 μ * eLpNorm H 6 μ := hholder
    _ = eLpNorm G 1 μ ^ ((1 : ℝ) / 3) * eLpNorm G 4 μ ^ ((2 : ℝ) / 3) := by
      rw [hFnorm, hHnorm]

end Critical2DKPZ.Smoothing

end
