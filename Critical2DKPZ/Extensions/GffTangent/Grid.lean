/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The test-independent geometric grid for GFF localisation

The entrance is chosen by a logarithmic floor on the grid with horizon
`c * exp l`. The padding uses the logarithmic ceiling of equation (6.5) of the note.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- Number of geometric padding blocks in the localisation argument. -/
def gridJ (w l : ℝ) : ℕ := ⌈2 * Real.log l / |Real.log w|⌉₊

/-- Grid index of the last geometric point above the quadratic entrance scale. -/
def gridIndex (c ρ l : ℝ) : ℕ := ⌊Real.logb ρ (c * Real.exp l / l ^ 2)⌋₊

/-- The chosen geometric entrance point; it depends on parameters and scale only. -/
def gridPoint (c ρ l : ℝ) : ℝ := c * Real.exp l / ρ ^ gridIndex c ρ l

/-- Polynomial observation horizon obtained by geometric padding of the entrance. -/
def gridHorizon (c ρ w l : ℝ) : ℝ := gridPoint c ρ l * ρ ^ gridJ w l

/-- Short name for the observation horizon used in ultraviolet removal. -/
abbrev S (c ρ w l : ℝ) : ℝ := gridHorizon c ρ w l

/-- Logarithmic padding gives inverse-square decay of the corrector tail. -/
theorem pow_gridJ_le_inv_sq {w l : ℝ} (hw : 0 < w) (hw1 : w < 1) (hl : 0 < l) :
    w ^ gridJ w l ≤ l⁻¹ ^ 2 := by
  have hwlog : Real.log w < 0 := Real.log_neg hw hw1
  have ha : 0 < |Real.log w| := abs_pos.mpr (ne_of_lt hwlog)
  have hceil := Nat.le_ceil (2 * Real.log l / |Real.log w|)
  change 2 * Real.log l / |Real.log w| ≤ (gridJ w l : ℝ) at hceil
  have hmul := mul_le_mul_of_nonneg_right hceil ha.le
  rw [div_mul_cancel₀ _ (ne_of_gt ha), abs_of_neg hwlog] at hmul
  apply (Real.log_le_log_iff (pow_pos hw _) (sq_pos_of_pos (inv_pos.mpr hl))).mp
  rw [Real.log_pow, Real.log_pow, Real.log_inv]
  norm_num only [Nat.cast_ofNat]
  linarith only [hmul]

/-- The logarithmic ceiling costs less than one extra padding block. -/
theorem gridJ_lt_add_one {w l : ℝ} (hl : 1 ≤ l) :
    (gridJ w l : ℝ) < 2 * Real.log l / |Real.log w| + 1 := by
  exact Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hl)) (abs_nonneg _))


/-- When the unpadded horizon reaches the quadratic scale, the grid point is
between that scale and `ρ` times that scale. -/
theorem gridPoint_bounds {c ρ l : ℝ} (hρ : 1 < ρ) (hl : 0 < l)
    (hh : l ^ 2 ≤ c * Real.exp l) :
    l ^ 2 ≤ gridPoint c ρ l ∧ gridPoint c ρ l ≤ ρ * l ^ 2 := by
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hl2 : 0 < l ^ 2 := sq_pos_of_pos hl
  let q := c * Real.exp l / l ^ 2
  have hq : 1 ≤ q := (one_le_div hl2).mpr hh
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hlogq : 0 ≤ Real.logb ρ q := div_nonneg (Real.log_nonneg hq) (Real.log_pos hρ).le
  have hfloor : (gridIndex c ρ l : ℝ) ≤ Real.logb ρ q := Nat.floor_le hlogq
  have hfloor' : Real.logb ρ q < (gridIndex c ρ l : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlo : ρ ^ gridIndex c ρ l ≤ q := by
    simpa only [Real.rpow_natCast] using (Real.le_logb_iff_rpow_le hρ hq0).mp hfloor
  have hhi : q < ρ ^ (gridIndex c ρ l + 1) := by
    have h := (Real.logb_lt_iff_lt_rpow hρ hq0).mp hfloor'
    rw [← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast] at h
    exact h
  have hpow : 0 < ρ ^ gridIndex c ρ l := pow_pos hρ0 _
  constructor
  · apply (le_div_iff₀ hpow).mpr
    have h := (le_div_iff₀ hl2).mp hlo
    simpa only [mul_comm] using h
  · apply (div_le_iff₀ hpow).mpr
    have h := (div_lt_iff₀ hl2).mp hhi
    rw [pow_succ] at h
    nlinarith only [h]

/-- Any fixed affine function of `log l` is eventually at most `l/2`. -/
theorem eventually_mul_log_add_le_half (a b : ℝ) :
    ∀ᶠ l : ℝ in atTop, a * Real.log l + b ≤ l / 2 := by
  have hlog : Tendsto (fun l : ℝ => Real.log l / l) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hconst : Tendsto (fun l : ℝ => b / l) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hlim : Tendsto (fun l : ℝ => a * (Real.log l / l) + b / l) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hlog.const_mul a).add hconst
  filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_gt_atTop (0 : ℝ)] with l hb hl
  have hratio : (a * Real.log l + b) / l ≤ 1 / 2 := by
    simpa only [add_div, mul_div_assoc] using hb.le
  have h := (div_le_iff₀ hl).mp hratio
  linarith only [h]

/-- The padded horizon is positive for every scale. -/
theorem gridHorizon_pos {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (w l : ℝ) :
    0 < gridHorizon c ρ w l := by
  unfold gridHorizon gridPoint
  positivity

/-- The exponential horizon eventually reaches the quadratic entrance scale. -/
theorem eventually_gridPoint_bounds {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    ∀ᶠ l : ℝ in atTop, l ^ 2 ≤ gridPoint c ρ l ∧ gridPoint c ρ l ≤ ρ * l ^ 2 := by
  filter_upwards [eventually_mul_log_add_le_half 2 (-Real.log c),
    eventually_gt_atTop (0 : ℝ)] with l hlog hl
  apply gridPoint_bounds hρ hl
  apply (Real.log_le_log_iff (sq_pos_of_pos hl) (mul_pos hc (Real.exp_pos l))).mp
  rw [Real.log_pow, Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos l)), Real.log_exp]
  norm_num only [Nat.cast_ofNat]
  linarith only [hlog, hl]

/-- Polynomial exponent used to bound the observation horizon. -/
def gridDegree (ρ w : ℝ) : ℝ := 3 + 2 * Real.log ρ / |Real.log w|

/-- The observation horizon remains polynomial, with an explicit exponent. -/
theorem gridHorizon_le_rpow {c ρ w l : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hl : 1 ≤ l) (hlρ : ρ ^ 2 ≤ l)
    (hpoint : gridPoint c ρ l ≤ ρ * l ^ 2) :
    gridHorizon c ρ w l ≤ l ^ gridDegree ρ w := by
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hp : 0 < gridPoint c ρ l := by unfold gridPoint; positivity
  have hS := gridHorizon_pos hc hρ0 w l
  have hj := (gridJ_lt_add_one (w := w) hl).le
  have hjmul := mul_le_mul_of_nonneg_right hj (Real.log_pos hρ).le
  have hplog : Real.log (gridPoint c ρ l) ≤ Real.log ρ + 2 * Real.log l := by
    have h := Real.log_le_log hp hpoint
    rw [Real.log_mul (ne_of_gt hρ0) (ne_of_gt (sq_pos_of_pos hl0)), Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hlρlog : 2 * Real.log ρ ≤ Real.log l := by
    have h := Real.log_le_log (sq_pos_of_pos hρ0) hlρ
    rw [Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  apply (Real.log_le_log_iff hS (Real.rpow_pos_of_pos hl0 _)).mp
  rw [Real.log_rpow hl0, gridHorizon, Real.log_mul (ne_of_gt hp) (ne_of_gt (pow_pos hρ0 _)),
    Real.log_pow]
  dsimp only [gridDegree]
  have hnorm : (3 + 2 * Real.log ρ / |Real.log w|) * Real.log l =
      (Real.log ρ + 2 * Real.log l) +
        (2 * Real.log l / |Real.log w| + 1) * Real.log ρ +
        (Real.log l - 2 * Real.log ρ) := by ring
  rw [hnorm]
  linarith only [hplog, hjmul, hlρlog]

/-- The full test-independent grid properties, with a quantitative gap to the
exponential horizon. -/
theorem grid_properties {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∃ d : ℝ, 2 ≤ d ∧ ∀ᶠ l : ℝ in atTop,
      0 < l ∧ w ^ gridJ w l ≤ l⁻¹ ^ 2 ∧ l ^ 2 ≤ gridHorizon c ρ w l ∧
      gridHorizon c ρ w l ≤ l ^ d ∧
      l / 2 ≤ Real.log (c * Real.exp l / gridHorizon c ρ w l) ∧
      0 < Real.log (c * Real.exp l / gridHorizon c ρ w l) := by
  have hw1 : w < 1 := hwHalf.trans (by norm_num)
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hd : 2 ≤ gridDegree ρ w := by
    dsimp only [gridDegree]
    have h := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.log_pos hρ).le) (abs_nonneg (Real.log w))
    linarith only [h]
  refine ⟨gridDegree ρ w, hd, ?_⟩
  filter_upwards [eventually_gridPoint_bounds hc hρ,
    eventually_ge_atTop (max 1 (ρ ^ 2)),
    eventually_mul_log_add_le_half (gridDegree ρ w) (-Real.log c)] with l hp hl hlog
  have hl1 : 1 ≤ l := (le_max_left _ _).trans hl
  have hlρ : ρ ^ 2 ≤ l := (le_max_right _ _).trans hl
  have hl0 : 0 < l := zero_lt_one.trans_le hl1
  have hSpos := gridHorizon_pos hc hρ0 w l
  have hupper := gridHorizon_le_rpow (w := w) hc hρ hl1 hlρ hp.2
  have hlower : l ^ 2 ≤ gridHorizon c ρ w l := by
    exact hp.1.trans (le_mul_of_one_le_right (le_trans (sq_nonneg l) hp.1) (one_le_pow₀ hρ.le))
  have hSlog : Real.log (gridHorizon c ρ w l) ≤ gridDegree ρ w * Real.log l := by
    have h := Real.log_le_log hSpos hupper
    rwa [Real.log_rpow hl0] at h
  have hgap : l / 2 ≤ Real.log (c * Real.exp l / gridHorizon c ρ w l) := by
    rw [Real.log_div (ne_of_gt (mul_pos hc (Real.exp_pos l))) (ne_of_gt hSpos),
      Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos l)), Real.log_exp]
    linarith only [hlog, hSlog]
  exact ⟨hl0, pow_gridJ_le_inv_sq hw hw1 hl0, hlower, hupper, hgap,
    (half_pos hl0).trans_le hgap⟩

/-- Uniform lower bound for the remaining block count, even for arbitrarily
small positive observation times below the polynomial horizon. -/
theorem grid_blockCount_lower {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ l : ℝ in atTop, ∀ n : ℝ, 0 < n → n ≤ gridHorizon c ρ w l →
      b * l ≤ Real.logb ρ (c * Real.exp l / n) := by
  obtain ⟨d, _, hgrid⟩ := grid_properties hc hρ hw hwHalf
  refine ⟨(2 * Real.log ρ)⁻¹, inv_pos.mpr (mul_pos two_pos (Real.log_pos hρ)), ?_⟩
  filter_upwards [hgrid] with l hl
  intro n hn hnS
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  have hratio : c * Real.exp l / gridHorizon c ρ w l ≤ c * Real.exp l / n :=
    div_le_div_of_nonneg_left hH.le hn hnS
  have hg := hl.2.2.2.2.1.trans (Real.log_le_log (div_pos hH (gridHorizon_pos hc (zero_lt_one.trans hρ) w l)) hratio)
  rw [Real.logb]
  apply (le_div_iff₀ (Real.log_pos hρ)).mpr
  have he : (2 * Real.log ρ)⁻¹ * l * Real.log ρ = l / 2 := by
    field_simp [ne_of_gt (Real.log_pos hρ)]
  rw [he]
  exact hg

/-- Polynomially sized positive observation times also give a uniform upper
bound on the remaining block count. -/
theorem grid_blockCount_upper {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (A : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ l : ℝ in atTop, ∀ n : ℝ, 0 < n → |Real.log n| ≤ A * Real.log l →
      Real.logb ρ (c * Real.exp l / n) ≤ B * l := by
  refine ⟨2 / Real.log ρ, div_pos two_pos (Real.log_pos hρ), ?_⟩
  filter_upwards [eventually_mul_log_add_le_half A |Real.log c|,
    eventually_gt_atTop (0 : ℝ)] with l hbound hl
  intro n hn hlogn
  have hlog : Real.log (c * Real.exp l / n) ≤ 2 * l := by
    rw [Real.log_div (ne_of_gt (mul_pos hc (Real.exp_pos l))) (ne_of_gt hn),
      Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos l)), Real.log_exp]
    have h1 := le_abs_self (Real.log c)
    have h2 := neg_le_abs (Real.log n)
    linarith only [hbound, hlogn, h1, h2, hl]
  rw [Real.logb]
  apply (div_le_iff₀ (Real.log_pos hρ)).mpr
  convert hlog using 1
  field_simp [ne_of_gt (Real.log_pos hρ)]

/-- The padding is nonempty beyond scale one. -/
theorem gridJ_pos {w l : ℝ} (hw : 0 < w) (hw1 : w < 1) (hl : 1 < l) :
    0 < gridJ w l := by
  unfold gridJ
  exact Nat.ceil_pos.mpr (div_pos (mul_pos two_pos (Real.log_pos hl))
    (abs_pos.mpr (ne_of_lt (Real.log_neg hw hw1))))

/-- At large scales the padded horizon still lies on the original
backwards geometric grid. -/
theorem eventually_gridJ_le_gridIndex {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∀ᶠ l : ℝ in atTop, gridJ w l ≤ gridIndex c ρ l := by
  obtain ⟨d, hd, hgrid⟩ := grid_properties hc hρ hw hwHalf
  filter_upwards [hgrid] with l hl
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  have hS := gridHorizon_pos hc hρ0 w l
  have hgap := hl.2.2.2.2.2
  have hSH : gridHorizon c ρ w l < c * Real.exp l := by
    apply (Real.log_lt_log_iff hS hH).mp
    rw [Real.log_div hH.ne' hS.ne'] at hgap
    linarith only [hgap]
  by_contra hnot
  have hpow : ρ ^ gridIndex c ρ l ≤ ρ ^ gridJ w l :=
    pow_le_pow_right₀ hρ.le (Nat.le_of_lt (Nat.lt_of_not_ge hnot))
  have hHle : c * Real.exp l ≤ gridHorizon c ρ w l := by
    unfold gridHorizon gridPoint
    calc
      _ = c * Real.exp l / ρ ^ gridIndex c ρ l * ρ ^ gridIndex c ρ l := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  exact (not_le_of_gt hSH) hHle

/-- The polynomial horizon is a point of the original exponential grid,
with the padding subtracted from the entrance index. -/
theorem gridHorizon_eq_geometric {c ρ w l : ℝ} (hρ : 0 < ρ)
    (hj : gridJ w l ≤ gridIndex c ρ l) :
    gridHorizon c ρ w l = c * Real.exp l *
      ρ ^ (-((gridIndex c ρ l - gridJ w l : ℕ) : ℝ)) := by
  rw [gridHorizon, gridPoint, Real.rpow_neg hρ.le, Real.rpow_natCast,
    pow_sub₀ ρ hρ.ne' hj]
  field_simp

/-- The number of blocks remaining after the polynomial horizon is at
least two at large scales, as required by the lattice profile estimates. -/
theorem eventually_grid_remaining_ge_two {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∀ᶠ l : ℝ in atTop, 2 ≤ gridIndex c ρ l - gridJ w l := by
  obtain ⟨d, hd, hgrid⟩ := grid_properties hc hρ hw hwHalf
  filter_upwards [hgrid, eventually_gridJ_le_gridIndex hc hρ hw hwHalf,
    eventually_ge_atTop (4 * Real.log ρ)] with l hl hj hlarge
  let k := gridIndex c ρ l - gridJ w l
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  have hratio : c * Real.exp l / gridHorizon c ρ w l = ρ ^ k := by
    rw [gridHorizon_eq_geometric hρ0 hj, Real.rpow_neg hρ0.le, Real.rpow_natCast]
    change c * Real.exp l / (c * Real.exp l * (ρ ^ k)⁻¹) = ρ ^ k
    field_simp
  have hgap := hl.2.2.2.2.1
  rw [hratio, Real.log_pow] at hgap
  have hreal : (2 : ℝ) ≤ (k : ℝ) := by
    have hlog := Real.log_pos hρ
    nlinarith only [hgap, hlarge, hlog]
  exact_mod_cast hreal

/-- Earlier entrances on the grid, counted backwards from `gridPoint`. -/
def gridEntrance (c ρ l : ℝ) (j : ℕ) : ℝ := gridPoint c ρ l / ρ ^ j

/-- The earlier-entrance grid uses the same exponential-horizon indices. -/
theorem gridEntrance_eq_geometric {c ρ l : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    gridEntrance c ρ l j = c * Real.exp l *
      ρ ^ (-((gridIndex c ρ l + j : ℕ) : ℝ)) := by
  rw [gridEntrance, gridPoint, Real.rpow_neg hρ.le, Real.rpow_natCast, pow_add]
  field_simp

/-- The padding leaves arbitrarily many blocks before the exponential horizon. -/
theorem eventually_grid_remaining_ge {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) (L : ℕ) :
    ∀ᶠ l : ℝ in atTop, L ≤ gridIndex c ρ l - gridJ w l := by
  obtain ⟨d, hd, hgrid⟩ := grid_properties hc hρ hw hwHalf
  filter_upwards [hgrid, eventually_gridJ_le_gridIndex hc hρ hw hwHalf,
    eventually_ge_atTop (2 * (L : ℝ) * Real.log ρ)] with l hl hj hlarge
  let k := gridIndex c ρ l - gridJ w l
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  have hratio : c * Real.exp l / gridHorizon c ρ w l = ρ ^ k := by
    rw [gridHorizon_eq_geometric hρ0 hj, Real.rpow_neg hρ0.le, Real.rpow_natCast]
    change c * Real.exp l / (c * Real.exp l * (ρ ^ k)⁻¹) = ρ ^ k
    field_simp
  have hgap := hl.2.2.2.2.1
  rw [hratio, Real.log_pow] at hgap
  have hreal : (L : ℝ) ≤ (k : ℝ) := by
    have hlog := Real.log_pos hρ
    nlinarith only [hgap, hlarge, hlog]
  exact_mod_cast hreal

/-- The number of remaining blocks is bounded above linearly in the scale. -/
theorem grid_remaining_le_linear {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ l : ℝ in atTop,
      ((gridIndex c ρ l - gridJ w l : ℕ) : ℝ) ≤ B * l := by
  obtain ⟨d, hd, hgrid⟩ := grid_properties hc hρ hw hwHalf
  obtain ⟨B, hB, hupper⟩ := grid_blockCount_upper hc hρ d
  refine ⟨B, hB, ?_⟩
  filter_upwards [hgrid, hupper, eventually_gridJ_le_gridIndex hc hρ hw hwHalf,
    eventually_ge_atTop (1 : ℝ)] with l hl hup hj hl1
  have hSpos := gridHorizon_pos hc (zero_lt_one.trans hρ) w l
  have hS1 : 1 ≤ gridHorizon c ρ w l :=
    (one_le_pow₀ hl1).trans hl.2.2.1
  have hlogS : |Real.log (gridHorizon c ρ w l)| ≤ d * Real.log l := by
    rw [abs_of_nonneg (Real.log_nonneg hS1)]
    calc
      _ ≤ Real.log (l ^ d) := Real.log_le_log hSpos hl.2.2.2.1
      _ = d * Real.log l := Real.log_rpow (by linarith : 0 < l) d
  have h := hup (gridHorizon c ρ w l) hSpos hlogS
  have hρ0 := zero_lt_one.trans hρ
  rw [gridHorizon_eq_geometric hρ0 hj, Real.rpow_neg hρ0.le, Real.rpow_natCast] at h
  have hH := mul_pos hc (Real.exp_pos l)
  have heq : c * Real.exp l /
      (c * Real.exp l * (ρ ^ (gridIndex c ρ l - gridJ w l))⁻¹) =
      ρ ^ (gridIndex c ρ l - gridJ w l) := by field_simp
  rw [heq, Real.logb_pow, Real.logb_self_eq_one hρ, mul_one] at h
  exact h

/-- The delayed entrance, padded observation time and exponential horizon
are strictly ordered at large scales. -/
theorem eventually_grid_time_order {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∀ᶠ l : ℝ in atTop, 0 < gridPoint c ρ l ∧
      gridPoint c ρ l < S c ρ w l ∧ S c ρ w l < c * Real.exp l ∧
      l ^ 2 ≤ gridPoint c ρ l := by
  obtain ⟨d, hd, hgrid⟩ := grid_properties hc hρ hw hwHalf
  filter_upwards [hgrid, eventually_gridPoint_bounds hc hρ,
    eventually_gt_atTop (1 : ℝ)] with l hg hp hl
  have hρ0 := zero_lt_one.trans hρ
  have hpp : 0 < gridPoint c ρ l := by unfold gridPoint; positivity
  have hJ := gridJ_pos hw (by linarith : w < 1) hl
  have hpow : 1 < ρ ^ gridJ w l := by
    exact_mod_cast (one_lt_pow₀ hρ hJ.ne')
  have hpS : gridPoint c ρ l < S c ρ w l := by
    change gridPoint c ρ l < gridPoint c ρ l * ρ ^ gridJ w l
    exact (lt_mul_iff_one_lt_right hpp).mpr hpow
  have hS := gridHorizon_pos hc hρ0 w l
  have hH := mul_pos hc (Real.exp_pos l)
  have hSH : S c ρ w l < c * Real.exp l := by
    apply (Real.log_lt_log_iff hS hH).mp
    have hgap := hg.2.2.2.2.2
    rw [Real.log_div hH.ne' hS.ne'] at hgap
    linarith only [hgap]
  exact ⟨hpp, hpS, hSH, hp.1⟩

end Critical2DKPZ.Extensions.GffTangent

end
