/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Critical2DKPZ.Extensions.GffTangent.Grid
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Geometric rounding of the ultraviolet entrance scales -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- Index of the first geometric grid point at or below the target scale. -/
def uvGridIndex (H ρ u : ℝ) : ℕ := ⌈Real.logb ρ (H / u)⌉₊

/-- Geometric rounding of `u` on the grid with top horizon `H`. -/
def uvGridPoint (H ρ u : ℝ) : ℝ := H / ρ ^ uvGridIndex H ρ u

/-- The very fine entrance used to make the regularization error negligible. -/
def uvFineEntrance (c ρ l : ℝ) : ℝ :=
  uvGridPoint (c * Real.exp l) ρ (Real.exp (-(l ^ 40)))

/-- The short observation interval used in the ultraviolet removal. -/
def uvObservation (c ρ l : ℝ) : ℝ :=
  uvGridPoint (c * Real.exp l) ρ (l⁻¹ ^ 200)

/-- The geometric number of padding blocks at the coarse entrance. -/
def uvPadding (ϖ l : ℝ) : ℕ := ⌈2 * Real.log l / |Real.log ϖ|⌉₊

/-- The coarse entrance is exactly a whole number of grid blocks before observation. -/
def uvCoarseEntrance (c ρ ϖ l : ℝ) : ℝ :=
  uvObservation c ρ l / ρ ^ uvPadding ϖ l

/-- Geometric rounding loses at most one factor of the grid ratio. -/
theorem uvGridPoint_bounds {H ρ u : ℝ} (hH : 0 < H) (hρ : 1 < ρ)
    (hu : 0 < u) (huH : u ≤ H) :
    u / ρ < uvGridPoint H ρ u ∧ uvGridPoint H ρ u ≤ u := by
  have hρpos : 0 < ρ := zero_lt_one.trans hρ
  have hx : 0 < H / u := div_pos hH hu
  have hx1 : 1 ≤ H / u := (one_le_div hu).mpr huH
  have hlog : 0 ≤ Real.logb ρ (H / u) := Real.logb_nonneg hρ hx1
  have hlow : H / u ≤ ρ ^ uvGridIndex H ρ u := by
    rw [← Real.rpow_natCast]
    exact (Real.logb_le_iff_le_rpow hρ hx).mp (Nat.le_ceil _)
  have hup : ρ ^ uvGridIndex H ρ u < (H / u) * ρ := by
    calc
      ρ ^ uvGridIndex H ρ u = ρ ^ (uvGridIndex H ρ u : ℝ) := (Real.rpow_natCast _ _).symm
      _ < ρ ^ (Real.logb ρ (H / u) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt hρ (Nat.ceil_lt_add_one hlog)
      _ = (H / u) * ρ := by
        rw [Real.rpow_add hρpos, Real.rpow_logb hρpos hρ.ne' hx, Real.rpow_one]
  have hp : 0 < ρ ^ uvGridIndex H ρ u := pow_pos hρpos _
  constructor
  · apply (lt_div_iff₀ hp).mpr
    have hh := mul_lt_mul_of_pos_left hup (div_pos hu hρpos)
    have he : (u / ρ) * ((H / u) * ρ) = H := by field_simp
    exact hh.trans_eq he
  · apply (div_le_iff₀ hp).mpr
    exact (div_le_iff₀ hu).mp hlow |>.trans_eq (mul_comm _ _)

/-- Every admissible rounded grid point is positive. -/
theorem uvGridPoint_pos {H ρ u : ℝ} (hH : 0 < H) (hρ : 0 < ρ) :
    0 < uvGridPoint H ρ u := div_pos hH (pow_pos hρ _)

/-- The fine entrance is within one geometric block of its prescribed exponential scale. -/
theorem uvFineEntrance_bounds {c ρ l : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hfit : Real.exp (-(l ^ 40)) ≤ c * Real.exp l) :
    Real.exp (-(l ^ 40)) / ρ < uvFineEntrance c ρ l ∧
      uvFineEntrance c ρ l ≤ Real.exp (-(l ^ 40)) :=
  uvGridPoint_bounds (mul_pos hc (Real.exp_pos _)) hρ (Real.exp_pos _) hfit

/-- The observation entrance is within one geometric block of `l⁻²⁰⁰`. -/
theorem uvObservation_bounds {c ρ l : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (hl : 0 < l)
    (hfit : l⁻¹ ^ 200 ≤ c * Real.exp l) :
    l⁻¹ ^ 200 / ρ < uvObservation c ρ l ∧ uvObservation c ρ l ≤ l⁻¹ ^ 200 :=
  uvGridPoint_bounds (mul_pos hc (Real.exp_pos _)) hρ (by positivity) hfit

/-- The exponential horizon eventually contains both prescribed entrance targets. -/
theorem uv_targets_fit {c : ℝ} (hc : 0 < c) :
    ∀ᶠ l : ℝ in atTop, 0 < l ∧
      Real.exp (-(l ^ 40)) ≤ c * Real.exp l ∧ l⁻¹ ^ 200 ≤ c * Real.exp l := by
  have hH : Tendsto (fun l : ℝ => c * Real.exp l) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1 : ℝ), hH.eventually_ge_atTop 1] with l hl hH
  have hlpos : 0 < l := zero_lt_one.trans_le hl
  refine ⟨hlpos, ?_, ?_⟩
  · exact (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (pow_nonneg hlpos.le _))).trans hH
  · exact (pow_le_one₀ (inv_nonneg.mpr hlpos.le) (inv_le_one_of_one_le₀ hl)).trans hH

/-- The very fine rounded entrance tends to zero. -/
theorem uvFineEntrance_tendsto_zero {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    Tendsto (uvFineEntrance c ρ) atTop (𝓝 0) := by
  have hpow : Tendsto (fun l : ℝ => l ^ 40) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 40 ≠ 0)
  have he : Tendsto (fun l : ℝ => Real.exp (-(l ^ 40))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)
  apply squeeze_zero' ?_ ?_ he
  · exact Eventually.of_forall fun l =>
      (uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)).le
  · filter_upwards [uv_targets_fit hc] with l hl
    exact (uvFineEntrance_bounds hc hρ hl.2.1).2

/-- The rounded observation interval tends to zero. -/
theorem uvObservation_tendsto_zero {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    Tendsto (uvObservation c ρ) atTop (𝓝 0) := by
  have hp : Tendsto (fun l : ℝ => l⁻¹ ^ 200) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : 200 ≠ 0)] using
      (tendsto_inv_atTop_zero : Tendsto (fun l : ℝ => l⁻¹) atTop (𝓝 0)).pow 200
  apply squeeze_zero' ?_ ?_ hp
  · exact Eventually.of_forall fun l =>
      (uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)).le
  · filter_upwards [uv_targets_fit hc] with l hl
    exact (uvObservation_bounds hc hρ hl.1 hl.2.2).2

/-- The padded coarse entrance remains positive and does not exceed observation. -/
theorem uvCoarseEntrance_bounds {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (ϖ l : ℝ) :
    0 < uvCoarseEntrance c ρ ϖ l ∧ uvCoarseEntrance c ρ ϖ l ≤ uvObservation c ρ l := by
  have hn : 0 < uvObservation c ρ l :=
    uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)
  refine ⟨div_pos hn (pow_pos (zero_lt_one.trans hρ) _), ?_⟩
  exact div_le_self hn.le (one_le_pow₀ hρ.le)

/-- The coarse entrance vanishes irrespective of the number of padding blocks. -/
theorem uvCoarseEntrance_tendsto_zero {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (ϖ : ℝ) :
    Tendsto (uvCoarseEntrance c ρ ϖ) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (uvObservation_tendsto_zero hc hρ)
  · exact Eventually.of_forall fun l => (uvCoarseEntrance_bounds hc hρ ϖ l).1.le
  · exact Eventually.of_forall fun l => (uvCoarseEntrance_bounds hc hρ ϖ l).2

/-- A clock growing at least as `l⁴⁰` makes the smoothing rate negligible after
multiplication by `l`. This is the exponent budget used at the fine entrance. -/
theorem ultraviolet_clock_rate_tendsto {d : ℝ → ℝ}
    (hd : ∀ᶠ l : ℝ in atTop, l ^ 40 ≤ d l) :
    Tendsto (fun l : ℝ => l * (d l) ^ (-(1 : ℝ) / 20)) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
  · filter_upwards [hd, eventually_ge_atTop (1 : ℝ)] with l hdl hl
    exact mul_nonneg (zero_le_one.trans hl)
      (Real.rpow_nonneg ((pow_nonneg (zero_le_one.trans hl) 40).trans hdl) _)
  · filter_upwards [hd, eventually_ge_atTop (1 : ℝ)] with l hl h1
    have hlpos : 0 < l := zero_lt_one.trans_le h1
    have hb := Real.rpow_le_rpow_of_nonpos (pow_pos hlpos 40) hl
      (by norm_num : -(1 : ℝ) / 20 ≤ 0)
    have heq : (l ^ 40 : ℝ) ^ (-(1 : ℝ) / 20) = l⁻¹ ^ 2 := by
      rw [← Real.rpow_natCast_mul hlpos.le]
      norm_num
    have hh := mul_le_mul_of_nonneg_left hb hlpos.le
    rw [heq] at hh
    have hcancel : l * (l⁻¹ ^ 2) = l⁻¹ := by field_simp
    rwa [hcancel] at hh

/-- The rounded fine entrance has a sufficiently large logarithmic clock. -/
theorem uvFineEntrance_clock {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    ∀ᶠ l : ℝ in atTop,
      l ^ 40 ≤ Real.log ((c * Real.exp l) / uvFineEntrance c ρ l) := by
  have hH : Tendsto (fun l : ℝ => c * Real.exp l) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  filter_upwards [uv_targets_fit hc, hH.eventually_ge_atTop 1] with l hl hH
  have ha : 0 < uvFineEntrance c ρ l :=
    uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)
  have hb := (uvFineEntrance_bounds hc hρ hl.2.1).2
  have hlog := Real.log_le_log ha hb
  rw [Real.log_exp] at hlog
  rw [Real.log_div (mul_pos hc (Real.exp_pos _)).ne' ha.ne']
  linarith only [hlog, Real.log_nonneg hH]

/-- The smoothing rate at the very fine grid entrance is negligible. -/
theorem uvFineEntrance_rate_tendsto {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    Tendsto (fun l : ℝ => l *
      (Real.log ((c * Real.exp l) / uvFineEntrance c ρ l)) ^ (-(1 : ℝ) / 20))
      atTop (𝓝 0) :=
  ultraviolet_clock_rate_tendsto (uvFineEntrance_clock hc hρ)

/-- Coarse padding preserves the exact common geometric grid. -/
theorem uvCoarseEntrance_grid (c ρ ϖ l : ℝ) :
    uvCoarseEntrance c ρ ϖ l = (c * Real.exp l) /
      ρ ^ (uvGridIndex (c * Real.exp l) ρ (l⁻¹ ^ 200) + uvPadding ϖ l) := by
  rw [uvCoarseEntrance, uvObservation, uvGridPoint, pow_add, div_div]


/-- Positive padding makes the coarse entrance strictly earlier than observation. -/
theorem uvCoarseEntrance_lt_observation {c ρ ϖ l : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hϖ : 0 < ϖ) (hϖ1 : ϖ < 1) (hl : 1 < l) :
    uvCoarseEntrance c ρ ϖ l < uvObservation c ρ l := by
  have hlog : 0 < |Real.log ϖ| := abs_pos.mpr (Real.log_neg hϖ hϖ1).ne
  have htarget : 0 < 2 * Real.log l / |Real.log ϖ| :=
    div_pos (mul_pos (by norm_num) (Real.log_pos hl)) hlog
  have hJ : 0 < (uvPadding ϖ l : ℝ) := htarget.trans_le (Nat.le_ceil _)
  have hJnat : 0 < uvPadding ϖ l := by exact_mod_cast hJ
  have hn : 0 < uvObservation c ρ l :=
    uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)
  apply (div_lt_self hn (one_lt_pow₀ hρ hJnat.ne'))


/-- UV padding is the padding used by the localisation grid. -/
theorem uvPadding_eq_gridJ (w l : ℝ) : uvPadding w l = gridJ w l := rfl

/-- The test-independent observation horizon diverges. -/
theorem uvHorizon_tendsto_atTop {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    Tendsto (gridHorizon c ρ w) atTop atTop := by
  obtain ⟨d, _, hgrid⟩ := grid_properties hc hρ hw hwHalf
  apply tendsto_atTop_mono' atTop (hgrid.mono fun _ h => h.2.2.1)
  exact tendsto_pow_atTop (by norm_num : 2 ≠ 0)

/-- The polynomial observation horizon has sublinear logarithm. -/
theorem uvHorizon_log_div_tendsto_zero {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    Tendsto (fun l => Real.log (gridHorizon c ρ w l) / l) atTop (𝓝 0) := by
  obtain ⟨d, _, hgrid⟩ := grid_properties hc hρ hw hwHalf
  have hb : Tendsto (fun l : ℝ => d * (Real.log l / l)) atTop (𝓝 0) := by
    have hlog : Tendsto (fun l : ℝ => Real.log l / l) atTop (𝓝 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    simpa only [mul_zero] using hlog.const_mul d
  apply squeeze_zero' (g := fun l : ℝ => d * (Real.log l / l)) ?_ ?_ hb
  · filter_upwards [hgrid, eventually_ge_atTop (1 : ℝ)] with l h hl
    have hS : 1 ≤ gridHorizon c ρ w l :=
      (one_le_pow₀ hl).trans h.2.2.1
    exact div_nonneg (Real.log_nonneg hS) h.1.le
  · filter_upwards [hgrid] with l h
    have hS := gridHorizon_pos hc (zero_lt_one.trans hρ) w l
    have ht := Real.log_le_log hS h.2.2.2.1
    rw [Real.log_rpow h.1] at ht
    have hv := div_le_div_of_nonneg_right ht h.1.le
    simpa only [mul_div_assoc] using hv

/-- All coarse scales are ordered below the test-independent polynomial horizon. -/
theorem uvScales_horizon_order {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∀ᶠ l : ℝ in atTop,
      0 < uvCoarseEntrance c ρ w l ∧
      uvCoarseEntrance c ρ w l < uvObservation c ρ l ∧
      uvObservation c ρ l < 1 ∧ 1 < gridHorizon c ρ w l ∧
      gridHorizon c ρ w l < c * Real.exp l := by
  obtain ⟨d, _, hgrid⟩ := grid_properties hc hρ hw hwHalf
  filter_upwards [hgrid, eventually_gt_atTop (1 : ℝ),
    (uvObservation_tendsto_zero hc hρ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    (uvHorizon_tendsto_atTop hc hρ hw hwHalf).eventually_gt_atTop 1] with l hg hl hn hS
  refine ⟨(uvCoarseEntrance_bounds hc hρ w l).1,
    uvCoarseEntrance_lt_observation hc hρ hw (hwHalf.trans (by norm_num)) hl,
    hn, hS, ?_⟩
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  have hSp := gridHorizon_pos hc (zero_lt_one.trans hρ) w l
  have hglog := hg.2.2.2.2.2
  rw [Real.log_div hH.ne' hSp.ne'] at hglog
  exact (Real.log_lt_log_iff hSp hH).mp (by linarith only [hglog])



end Critical2DKPZ.Extensions.GffTangent
