/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.ProfileLemmaFlow
public import Critical2DKPZ.Extensions.GffTangent.Scales
public import Critical2DKPZ.Extensions.GffTangent.LogMomentsProfile

import Critical2DKPZ.Extensions.GffTangent.Semiconvexity

/-! # Profile comparison at the ultraviolet entrance scales -/

public noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- A rounded UV scale in the quotient convention is exactly in the
negative-real-exponent convention consumed by `profile_comparison_flow`. -/
theorem uvGridPoint_eq_mul_rpow_neg {H ρ u : ℝ} (hρ : 0 < ρ) :
    uvGridPoint H ρ u = H * ρ ^ (-(uvGridIndex H ρ u : ℝ)) := by
  rw [uvGridPoint, Real.rpow_neg hρ.le, Real.rpow_natCast, div_eq_mul_inv]

theorem uvFineEntrance_eq_mul_rpow_neg {c ρ l : ℝ} (hρ : 0 < ρ) :
    uvFineEntrance c ρ l = c * Real.exp l *
      ρ ^ (-(uvGridIndex (c * Real.exp l) ρ (Real.exp (-(l ^ 40))) : ℝ)) := by
  exact uvGridPoint_eq_mul_rpow_neg hρ

theorem uvObservation_eq_mul_rpow_neg {c ρ l : ℝ} (hρ : 0 < ρ) :
    uvObservation c ρ l = c * Real.exp l *
      ρ ^ (-(uvGridIndex (c * Real.exp l) ρ (l⁻¹ ^ 200) : ℝ)) := by
  exact uvGridPoint_eq_mul_rpow_neg hρ

theorem uvCoarseEntrance_eq_mul_rpow_neg {c ρ w l : ℝ} (hρ : 0 < ρ) :
    uvCoarseEntrance c ρ w l = c * Real.exp l * ρ ^
      (-((uvGridIndex (c * Real.exp l) ρ (l⁻¹ ^ 200) + gridJ w l : ℕ) : ℝ)) := by
  rw [uvCoarseEntrance_grid, uvPadding_eq_gridJ]
  rw [show (c * Real.exp l) /
      ρ ^ (uvGridIndex (c * Real.exp l) ρ (l⁻¹ ^ 200) + gridJ w l) =
      c * Real.exp l * ρ ^
        (-((uvGridIndex (c * Real.exp l) ρ (l⁻¹ ^ 200) + gridJ w l : ℕ) : ℝ)) by
    rw [Real.rpow_neg hρ.le, Real.rpow_natCast, div_eq_mul_inv]]

/-- The padded localisation horizon is an exponential-grid point when its padding
does not exceed the unpadded grid index. -/
theorem gridHorizon_eq_mul_rpow_neg_sub {c ρ w l : ℝ}
    (hρ : 0 < ρ) (hJI : gridJ w l ≤ gridIndex c ρ l) :
    gridHorizon c ρ w l = c * Real.exp l *
      ρ ^ (-((gridIndex c ρ l - gridJ w l : ℕ) : ℝ)) := by
  rw [gridHorizon, gridPoint, Real.rpow_neg hρ.le, Real.rpow_natCast]
  have hp : ρ ^ gridIndex c ρ l =
      ρ ^ (gridIndex c ρ l - gridJ w l) * ρ ^ gridJ w l := by
    rw [← pow_add, Nat.sub_add_cancel hJI]
  rw [hp]
  field_simp [ne_of_gt (pow_pos hρ _)]

/-- Strict ordering of two backward grid points reverses their indices. -/
theorem index_lt_of_div_pow_lt {H ρ : ℝ} (hH : 0 < H) (hρ : 1 < ρ)
    {i j : ℕ} (hij : H / ρ ^ i < H / ρ ^ j) : j < i := by
  by_contra h
  have hijNat : i ≤ j := Nat.le_of_not_gt h
  have hp : ρ ^ i ≤ ρ ^ j := pow_le_pow_right₀ hρ.le hijNat
  have hdiv : H / ρ ^ j ≤ H / ρ ^ i :=
    div_le_div_of_nonneg_left hH.le (pow_pos (zero_lt_one.trans hρ) _) hp
  exact not_lt_of_ge hdiv hij

/-- The observation index has linearly many blocks remaining. -/
theorem uvObservation_index_linear_lower {c ρ w : ℝ}
    (hc : 0 < c) (hρ : 1 < ρ) (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ l : ℝ in atTop,
      b * l ≤ (uvGridIndex (c * Real.exp l) ρ (l⁻¹ ^ 200) : ℝ) := by
  obtain ⟨b, hb, hblocks⟩ := grid_blockCount_lower hc hρ hw hwHalf
  refine ⟨b, hb, ?_⟩
  filter_upwards [hblocks, uvScales_horizon_order hc hρ hw hwHalf] with l hblock hord
  have hnpos : 0 < uvObservation c ρ l :=
    uvGridPoint_pos (mul_pos hc (Real.exp_pos l)) (zero_lt_one.trans hρ)
  have hnS : uvObservation c ρ l ≤ gridHorizon c ρ w l :=
    hord.2.2.1.le.trans hord.2.2.2.1.le
  have hb' := hblock (uvObservation c ρ l) hnpos hnS
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  rw [uvObservation_eq_mul_rpow_neg (zero_lt_one.trans hρ)] at hb'
  rw [profile_grid_remaining_blocks hH hρ] at hb'
  exact hb'

/-- The padded localisation horizon index is eventually defined and no later than the
UV observation index. -/
theorem eventually_gridHorizon_index_le_uvObservation_index {c ρ w : ℝ}
    (hc : 0 < c) (hρ : 1 < ρ) (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∀ᶠ l : ℝ in atTop,
      gridJ w l ≤ gridIndex c ρ l ∧
      gridIndex c ρ l - gridJ w l ≤
        uvGridIndex (c * Real.exp l) ρ (l⁻¹ ^ 200) := by
  filter_upwards [uvScales_horizon_order hc hρ hw hwHalf] with l hord
  let H := c * Real.exp l
  let kn := uvGridIndex H ρ (l⁻¹ ^ 200)
  have hH : 0 < H := mul_pos hc (Real.exp_pos l)
  have hnrep : uvObservation c ρ l = H / ρ ^ kn := rfl
  have hSltH := hord.2.2.2.2
  have hJI : gridJ w l ≤ gridIndex c ρ l := by
    by_contra h
    have hIJ : gridIndex c ρ l < gridJ w l := Nat.lt_of_not_ge h
    have hp : ρ ^ gridIndex c ρ l < ρ ^ gridJ w l :=
      pow_lt_pow_right₀ hρ hIJ
    have hratio : 1 < ρ ^ gridJ w l / ρ ^ gridIndex c ρ l :=
      (one_lt_div (pow_pos (zero_lt_one.trans hρ) _)).mpr hp
    have hS : H < gridHorizon c ρ w l := by
      have ht := mul_lt_mul_of_pos_left hratio hH
      simpa only [mul_one, one_mul, gridHorizon, gridPoint, div_eq_mul_inv, mul_assoc,
        mul_left_comm, mul_comm, H] using ht
    exact (not_lt_of_ge hS.le) hSltH
  refine ⟨hJI, ?_⟩
  have hSrep := gridHorizon_eq_mul_rpow_neg_sub (zero_lt_one.trans hρ) hJI
  have hnS : uvObservation c ρ l < gridHorizon c ρ w l :=
    hord.2.2.1.trans hord.2.2.2.1
  rw [hnrep, hSrep, Real.rpow_neg (zero_lt_one.trans hρ).le,
    Real.rpow_natCast, div_eq_mul_inv] at hnS
  exact (index_lt_of_div_pow_lt hH hρ hnS).le


/-- Quantitative specialization of `profile_comparison_flow` once the four
backward grid indices and their two elementary asymptotic bounds are known. -/
theorem profile_comparison_of_scale_indices
    {c ρ q b l M : ℝ} (hb : 0 < b)
    (hl : 1 ≤ l) (hM0 : 0 ≤ M)
    {ka km kn kT : ℕ}
    (hn2 : 2 ≤ kn)
    (hnlower : b * l ≤ kn)
    (hpadding : q ^ (km - kn) ≤ l⁻¹ ^ 2)
    {Cr Co Cb : ℝ} (hCr : 0 ≤ Cr) (hCo : 0 ≤ Co) (hCb : 0 ≤ Cb)
    {C : ℝ}
    (hC : Cr / (b * Real.sqrt b) + Co / Real.sqrt b + Cb / b ≤ C)
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (x : Plane)
    (hprofile :
      (∫ ω, min
        |profileMass Z (c * Real.exp l * ρ ^ (-(ka : ℝ)))
            (c * Real.exp l * ρ ^ (-(kn : ℝ)))
            (c * Real.exp l * ρ ^ (-(kT : ℝ))) x ω -
          profileMass Z (c * Real.exp l * ρ ^ (-(km : ℝ)))
            (c * Real.exp l * ρ ^ (-(kn : ℝ)))
            (c * Real.exp l * ρ ^ (-(kT : ℝ))) x ω| M ∂P) ≤
        Cr / ((kn : ℝ) * Real.sqrt kn) +
          Co * q ^ (km - kn) / Real.sqrt kn + Cb * M / kn) :
    (∫ ω, min
      |profileMass Z (c * Real.exp l * ρ ^ (-(ka : ℝ)))
          (c * Real.exp l * ρ ^ (-(kn : ℝ)))
          (c * Real.exp l * ρ ^ (-(kT : ℝ))) x ω -
        profileMass Z (c * Real.exp l * ρ ^ (-(km : ℝ)))
          (c * Real.exp l * ρ ^ (-(kn : ℝ)))
          (c * Real.exp l * ρ ^ (-(kT : ℝ))) x ω| M ∂P) ≤
      C * (l ^ (-(3 : ℝ) / 2) + M * l⁻¹) := by
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  have hkn0 : 0 < (kn : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hn2)
  have hbl : 0 < b * l := mul_pos hb hl0
  have hsqrt : Real.sqrt b * Real.sqrt l ≤ Real.sqrt kn := by
    rw [← Real.sqrt_mul hb.le]
    exact Real.sqrt_le_sqrt hnlower
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsl : 0 < Real.sqrt l := Real.sqrt_pos.2 hl0
  have hpow : l ^ (-(3 : ℝ) / 2) = 1 / (l * Real.sqrt l) := by
    rw [show -(3 : ℝ) / 2 = -(1 + (1 / 2 : ℝ)) by norm_num,
      Real.rpow_neg hl0.le, Real.rpow_add hl0, Real.rpow_one, ← Real.sqrt_eq_rpow]
    exact (one_div _).symm
  have hfirst : Cr / ((kn : ℝ) * Real.sqrt kn) ≤
      (Cr / (b * Real.sqrt b)) * l ^ (-(3 : ℝ) / 2) := by
    calc
      _ ≤ Cr / ((b * l) * (Real.sqrt b * Real.sqrt l)) :=
        div_le_div_of_nonneg_left hCr (mul_pos hbl (mul_pos hsb hsl))
          (mul_le_mul hnlower hsqrt (mul_nonneg hsb.le hsl.le) hkn0.le)
      _ = _ := by rw [hpow]; field_simp
  have hsecond : Co * q ^ (km - kn) / Real.sqrt kn ≤
      (Co / Real.sqrt b) * l ^ (-(3 : ℝ) / 2) := by
    have hinv : l⁻¹ ^ 2 ≤ l⁻¹ := by
      nlinarith only [mul_nonneg (inv_nonneg.mpr hl0.le)
        (sub_nonneg.mpr (inv_le_one_of_one_le₀ hl))]
    calc
      _ ≤ Co * l⁻¹ / Real.sqrt kn :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpadding.trans hinv) hCo) (Real.sqrt_nonneg _)
      _ ≤ Co * l⁻¹ / (Real.sqrt b * Real.sqrt l) :=
        div_le_div_of_nonneg_left (mul_nonneg hCo (inv_nonneg.mpr hl0.le))
          (mul_pos hsb hsl) hsqrt
      _ = _ := by rw [hpow]; field_simp
  have hthird : Cb * M / kn ≤ (Cb / b) * (M * l⁻¹) := by
    calc
      _ ≤ Cb * M / (b * l) :=
        div_le_div_of_nonneg_left (mul_nonneg hCb hM0) hbl hnlower
      _ = _ := by field_simp
  have hA : 0 ≤ Cr / (b * Real.sqrt b) + Co / Real.sqrt b :=
    add_nonneg (div_nonneg hCr (mul_nonneg hb.le hsb.le)) (div_nonneg hCo hsb.le)
  have hD : 0 ≤ Cb / b := div_nonneg hCb hb.le
  have hC₁ : Cr / (b * Real.sqrt b) + Co / Real.sqrt b ≤ C :=
    (le_add_of_nonneg_right hD).trans hC
  have hC₂ : Cb / b ≤ C := (le_add_of_nonneg_left hA).trans hC
  calc
    _ ≤ Cr / ((kn : ℝ) * Real.sqrt kn) +
        Co * q ^ (km - kn) / Real.sqrt kn + Cb * M / kn := hprofile
    _ ≤ (Cr / (b * Real.sqrt b) + Co / Real.sqrt b) * l ^ (-(3 : ℝ) / 2) +
        (Cb / b) * (M * l⁻¹) := by linarith only [hfirst, hsecond, hthird]
    _ ≤ C * l ^ (-(3 : ℝ) / 2) + C * (M * l⁻¹) :=
      add_le_add (mul_le_mul_of_nonneg_right hC₁ (Real.rpow_nonneg hl0.le _))
        (mul_le_mul_of_nonneg_right hC₂ (mul_nonneg hM0 (inv_nonneg.mpr hl0.le)))
    _ = _ := by ring

/-- The superexponentially fine entrance eventually precedes the padded
polynomial entrance. -/
theorem eventually_uvFineEntrance_lt_uvCoarseEntrance
    {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∀ᶠ l : ℝ in atTop,
      uvFineEntrance c ρ l < uvCoarseEntrance c ρ w l := by
  have hw1 : w < 1 := hwHalf.trans (by norm_num)
  have hlogw : Real.log w < 0 := Real.log_neg hw hw1
  let A : ℝ := 200 + 2 * Real.log ρ / |Real.log w|
  let B : ℝ := 2 * Real.log ρ
  filter_upwards [uv_targets_fit hc, eventually_gt_atTop (1 : ℝ),
    eventually_mul_log_add_le_half A B] with l hfit hl hclock
  have hl0 : 0 < l := hfit.1
  have hJ := (gridJ_lt_add_one (w := w) hl.le).le
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hpadlog : ((gridJ w l : ℝ) + 1) * Real.log ρ ≤
      (2 * Real.log l / |Real.log w| + 2) * Real.log ρ :=
    mul_le_mul_of_nonneg_right (by linarith only [hJ]) hlogρ.le
  have hlinear : 200 * Real.log l + ((gridJ w l : ℝ) + 1) * Real.log ρ ≤ l / 2 := by
    apply le_trans (add_le_add le_rfl hpadlog)
    dsimp only [A, B] at hclock
    convert hclock using 1; ring
  have hhalfPow : l / 2 < l ^ 40 := by
    have hp : l < l ^ 40 := by
      have := pow_lt_pow_right₀ hl (by norm_num : (1 : ℕ) < 40)
      simpa only [pow_one] using this
    linarith
  have hexp : Real.exp (-(l ^ 40)) <
      (l⁻¹ ^ 200 / ρ) / ρ ^ gridJ w l := by
    apply (Real.log_lt_log_iff (Real.exp_pos _) (by positivity)).mp
    rw [Real.log_exp]
    have hrhs : Real.log ((l⁻¹ ^ 200 / ρ) / ρ ^ gridJ w l) =
        -(200 * Real.log l + ((gridJ w l : ℝ) + 1) * Real.log ρ) := by
      rw [Real.log_div (by positivity) (by positivity),
        Real.log_div (by positivity) (ne_of_gt (zero_lt_one.trans hρ)),
        Real.log_pow, Real.log_inv, Real.log_pow]
      push_cast
      ring
    rw [hrhs]
    linarith only [hlinear, hhalfPow]
  have ha := (uvFineEntrance_bounds hc hρ hfit.2.1).2
  have hn := (uvObservation_bounds hc hρ hl0 hfit.2.2).1
  have hm : (l⁻¹ ^ 200 / ρ) / ρ ^ gridJ w l <
      uvCoarseEntrance c ρ w l := by
    rw [uvCoarseEntrance, uvPadding_eq_gridJ]
    exact div_lt_div_of_pos_right hn (pow_pos (zero_lt_one.trans hρ) _)
  exact ha.trans_lt (hexp.trans hm)

/-- All four indices required by `profile_comparison_flow` have the correct
eventual order at the ultraviolet scales. -/
theorem eventually_uv_profile_index_order
    {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∀ᶠ l : ℝ in atTop,
      let H := c * Real.exp l
      let ka := uvGridIndex H ρ (Real.exp (-(l ^ 40)))
      let kn := uvGridIndex H ρ (l⁻¹ ^ 200)
      let km := kn + gridJ w l
      km ≤ ka ∧ kn < km ∧ 2 ≤ kn := by
  obtain ⟨b, hb, hkn⟩ := uvObservation_index_linear_lower hc hρ hw hwHalf
  filter_upwards [eventually_uvFineEntrance_lt_uvCoarseEntrance hc hρ hw hwHalf,
    uvScales_horizon_order hc hρ hw hwHalf, hkn,
    eventually_gt_atTop (max 1 (2 / b))] with l ham hord hlin hl
  dsimp only
  let H := c * Real.exp l
  let ka := uvGridIndex H ρ (Real.exp (-(l ^ 40)))
  let kn := uvGridIndex H ρ (l⁻¹ ^ 200)
  let km := kn + gridJ w l
  have haRep : uvFineEntrance c ρ l = H / ρ ^ ka := rfl
  have hnRep : uvObservation c ρ l = H / ρ ^ kn := rfl
  have hmRep : uvCoarseEntrance c ρ w l = H / ρ ^ km := by
    simpa only [H, km, kn, uvPadding_eq_gridJ] using uvCoarseEntrance_grid c ρ w l
  have hH : 0 < H := mul_pos hc (Real.exp_pos l)
  have hma : km < ka := by
    apply index_lt_of_div_pow_lt hH hρ
    simpa only [haRep, hmRep] using ham
  have hnm : kn < km := by
    apply index_lt_of_div_pow_lt hH hρ
    simpa only [hnRep, hmRep] using hord.2.1
  have hn2real : (2 : ℝ) ≤ kn := by
    have hlower : 2 / b ≤ l := (le_max_right _ _).trans hl.le
    have := mul_le_mul_of_nonneg_left hlower hb.le
    field_simp [hb.ne'] at this
    exact this.trans hlin
  have hn2 : 2 ≤ kn := by exact_mod_cast hn2real
  exact ⟨hma.le, hnm, hn2⟩

/-- Profile comparison simultaneously at the exponential and
padded polynomial horizons, with the source rate and no scale hypotheses. -/
theorem profile_comparison_at_scales {c : ℝ} (hc : 0 < c) :
    ∃ ρ w C : ℝ, 1 < ρ ∧ 0 < w ∧ w < 1 / 2 ∧ 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
        (_hZ : ∀ l, IsCriticalSHF (-l) P (Z l)),
      ∀ᶠ l : ℝ in atTop, ∀ x : Plane, ∀ M : ℝ, 0 ≤ M → M ≤ 1 →
      ∀ T ∈ ({c * Real.exp l, gridHorizon c ρ w l} : Set ℝ),
        (∫ ω, min
          |profileMass (Z l) (uvFineEntrance c ρ l) (uvObservation c ρ l) T x ω -
           profileMass (Z l) (uvCoarseEntrance c ρ w l) (uvObservation c ρ l) T x ω| M ∂P) ≤
          C * (l ^ (-(3 : ℝ) / 2) + M * l⁻¹) := by
  obtain ⟨ρ₀, w, hρ₀, hw, hwHalf, hflow⟩ := profile_comparison_flow hc
  let ρ := ρ₀
  obtain ⟨Cr, Co, Cb, hCr, hCo, hCb, hbound⟩ := hflow ρ le_rfl
  obtain ⟨b, hb, hkn⟩ := uvObservation_index_linear_lower hc hρ₀ hw hwHalf
  let C := Cr / (b * Real.sqrt b) + Co / Real.sqrt b + Cb / b
  refine ⟨ρ, w, C, hρ₀, hw, hwHalf, ?_, ?_⟩
  · dsimp only [C]
    positivity
  · intro Ω _ P _ Z hZ
    filter_upwards [eventually_uv_profile_index_order hc hρ₀ hw hwHalf,
      eventually_gridHorizon_index_le_uvObservation_index hc hρ₀ hw hwHalf,
      hkn, eventually_ge_atTop (1 : ℝ)] with l hord hSidx hlinear hl
    intro x M hM0 _hM1 T hT
    let H := c * Real.exp l
    let ka := uvGridIndex H ρ (Real.exp (-(l ^ 40)))
    let kn := uvGridIndex H ρ (l⁻¹ ^ 200)
    let km := kn + gridJ w l
    let kS := gridIndex c ρ l - gridJ w l
    rw [uvFineEntrance_eq_mul_rpow_neg (zero_lt_one.trans hρ₀),
      uvObservation_eq_mul_rpow_neg (zero_lt_one.trans hρ₀),
      uvCoarseEntrance_eq_mul_rpow_neg (zero_lt_one.trans hρ₀)]
    have hpadding : w ^ (km - kn) ≤ l⁻¹ ^ 2 := by
      simpa only [km, Nat.add_sub_cancel_left] using
        pow_gridJ_le_inv_sq hw (hwHalf.trans (by norm_num)) (zero_lt_one.trans_le hl)
    rcases hT with rfl | rfl
    · have hp := hbound P l (Z l) (hZ l) ka km kn 0
        hord.1 hord.2.1 hord.2.2 (Nat.zero_le _) x M hM0
      have hr := profile_comparison_of_scale_indices hb hl hM0
        hord.2.2 hlinear hpadding
        hCr hCo hCb (C := C) le_rfl P (Z l) x hp
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hr
    · rw [gridHorizon_eq_mul_rpow_neg_sub (zero_lt_one.trans hρ₀) hSidx.1]
      exact profile_comparison_of_scale_indices hb hl hM0
        hord.2.2 hlinear hpadding
        hCr hCo hCb (C := C) le_rfl P (Z l) x
        (hbound P l (Z l) (hZ l) ka km kn kS
          hord.1 hord.2.1 hord.2.2 hSidx.2 x M hM0)

/-- The padding clock grows at most logarithmically. -/
theorem eventually_gridJ_mul_log_le {ρ w : ℝ} (hρ : 1 < ρ)
    (_hw : 0 < w) (_hwHalf : w < 1 / 2) :
    ∀ᶠ l : ℝ in atTop,
      (gridJ w l : ℝ) * Real.log ρ ≤
        (2 * Real.log ρ / |Real.log w| + Real.log ρ) * Real.log l := by
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with l hl
  have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hl
  have hlogl : 1 ≤ Real.log l := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hl
  have hJ := (gridJ_lt_add_one (w := w) hl1).le
  have hpad := mul_le_mul_of_nonneg_right hJ hρlog.le
  have htail : Real.log ρ ≤ Real.log ρ * Real.log l :=
    le_mul_of_one_le_right hρlog.le hlogl
  calc
    _ ≤ (2 * Real.log l / |Real.log w| + 1) * Real.log ρ := hpad
    _ = (2 * Real.log ρ / |Real.log w|) * Real.log l + Real.log ρ := by ring
    _ ≤ (2 * Real.log ρ / |Real.log w|) * Real.log l + Real.log ρ * Real.log l :=
      add_le_add le_rfl htail
    _ = _ := by ring

/-- Coarse entrance to short observation has variance ratio `O(log l/l)`. -/
theorem uvCoarse_observation_ratio_le {c ρ w : ℝ} (hc : 0 < c)
    (hρ : 1 < ρ) (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ l : ℝ in atTop,
      Real.log (uvObservation c ρ l / uvCoarseEntrance c ρ w l) /
        (l - Real.log (uvObservation c ρ l)) ≤ C * Real.log l / l := by
  let C := 2 * Real.log ρ / |Real.log w| + Real.log ρ
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [uvScales_horizon_order hc hρ hw hwHalf,
    eventually_gridJ_mul_log_le hρ hw hwHalf, eventually_gt_atTop (1 : ℝ)]
    with l hord hJ hl
  have hn0 : 0 < uvObservation c ρ l :=
    uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)
  have hlogn : Real.log (uvObservation c ρ l) < 0 := Real.log_neg hn0 hord.2.2.1
  have hnum : Real.log (uvObservation c ρ l / uvCoarseEntrance c ρ w l) =
      (gridJ w l : ℝ) * Real.log ρ := by
    rw [uvCoarseEntrance, uvPadding_eq_gridJ,
      show uvObservation c ρ l / (uvObservation c ρ l / ρ ^ gridJ w l) =
        ρ ^ gridJ w l by field_simp, Real.log_pow]
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hden : l ≤ l - Real.log (uvObservation c ρ l) := by linarith only [hlogn]
  rw [hnum]
  apply le_trans (div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg _) hρlog.le) hl0 hden)
  exact div_le_div_of_nonneg_right hJ hl0.le

/-- Fine entrance to short observation has variance ratio `O(l^39)`. -/
theorem uvFine_observation_ratio_le {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ l : ℝ in atTop,
      Real.log (uvObservation c ρ l / uvFineEntrance c ρ l) /
        (l - Real.log (uvObservation c ρ l)) ≤ C * l ^ 39 := by
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  refine ⟨1 + Real.log ρ, by positivity, ?_⟩
  filter_upwards [uv_targets_fit hc, eventually_gt_atTop (1 : ℝ),
    (uvObservation_tendsto_zero hc hρ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with l hfit hl hn1
  have hl0 : 0 < l := zero_lt_one.trans hl
  have hn0 : 0 < uvObservation c ρ l :=
    uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)
  have ha0 : 0 < uvFineEntrance c ρ l :=
    uvGridPoint_pos (mul_pos hc (Real.exp_pos _)) (zero_lt_one.trans hρ)
  have hlogn : Real.log (uvObservation c ρ l) < 0 := Real.log_neg hn0 hn1
  have halow := (uvFineEntrance_bounds hc hρ hfit.2.1).1.le
  have halog := Real.log_le_log (div_pos (Real.exp_pos _) (zero_lt_one.trans hρ)) halow
  rw [Real.log_div (Real.exp_pos _).ne' (zero_lt_one.trans hρ).ne', Real.log_exp] at halog
  have hnum : Real.log (uvObservation c ρ l / uvFineEntrance c ρ l) ≤
      l ^ 40 + Real.log ρ := by
    rw [Real.log_div hn0.ne' ha0.ne']
    linarith only [hlogn, halog]
  have hden : l ≤ l - Real.log (uvObservation c ρ l) := by linarith only [hlogn]
  apply (div_le_iff₀ (hl0.trans_le hden)).mpr
  calc
    _ ≤ l ^ 40 + Real.log ρ := hnum
    _ ≤ (1 + Real.log ρ) * l ^ 40 := by
      have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hl.le : 1 ≤ l ^ 40) hρlog.le
      nlinarith only [hh]
    _ = ((1 + Real.log ρ) * l ^ 39) * l := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)

/-- Profile comparison at the UV scales, uniformly for every independently
chosen admissible polynomial-horizon padding. -/
theorem profile_comparison_at_scales_independent_horizon {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧
      ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ wS : ℝ, 0 < wS → wS < 1 / 2 →
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
        (_hZ : ∀ l, IsCriticalSHF (-l) P (Z l)),
      ∀ᶠ l : ℝ in atTop, ∀ x : Plane, ∀ M : ℝ, 0 ≤ M →
      ∀ T ∈ ({c * Real.exp l, gridHorizon c ρ wS l} : Set ℝ),
        (∫ ω, min
          |profileMass (Z l) (uvFineEntrance c ρ l) (uvObservation c ρ l) T x ω -
           profileMass (Z l) (uvCoarseEntrance c ρ q l) (uvObservation c ρ l) T x ω| M ∂P) ≤
          C * (l ^ (-(3 : ℝ) / 2) + M * l⁻¹) := by
  obtain ⟨ρ₀, q, hρ₀, hq, hqHalf, hflow⟩ := profile_comparison_flow hc
  refine ⟨ρ₀, q, hρ₀, hq, hqHalf, ?_⟩
  intro ρ hρle wS hwS hwSHalf
  have hρ : 1 < ρ := hρ₀.trans_le hρle
  obtain ⟨Cr, Co, Cb, hCr, hCo, hCb, hbound⟩ := hflow ρ hρle
  obtain ⟨b, hb, hkn⟩ := uvObservation_index_linear_lower hc hρ hwS hwSHalf
  let C := Cr / (b * Real.sqrt b) + Co / Real.sqrt b + Cb / b
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    positivity
  · intro Ω _ P _ Z hZ
    filter_upwards [eventually_uv_profile_index_order hc hρ hq hqHalf,
      eventually_gridHorizon_index_le_uvObservation_index hc hρ hwS hwSHalf,
      hkn, eventually_ge_atTop (1 : ℝ)] with l hord hSidx hlinear hl
    intro x M hM0 T hT
    let H := c * Real.exp l
    let ka := uvGridIndex H ρ (Real.exp (-(l ^ 40)))
    let kn := uvGridIndex H ρ (l⁻¹ ^ 200)
    let km := kn + gridJ q l
    let kS := gridIndex c ρ l - gridJ wS l
    rw [uvFineEntrance_eq_mul_rpow_neg (zero_lt_one.trans hρ),
      uvObservation_eq_mul_rpow_neg (zero_lt_one.trans hρ),
      uvCoarseEntrance_eq_mul_rpow_neg (zero_lt_one.trans hρ)]
    have hpadding : q ^ (km - kn) ≤ l⁻¹ ^ 2 := by
      simpa only [km, Nat.add_sub_cancel_left] using
        pow_gridJ_le_inv_sq hq (hqHalf.trans (by norm_num))
          (zero_lt_one.trans_le hl)
    rcases hT with rfl | rfl
    · have hp := hbound P l (Z l) (hZ l) ka km kn 0
        hord.1 hord.2.1 hord.2.2 (Nat.zero_le _) x M hM0
      have hr := profile_comparison_of_scale_indices hb hl hM0
        hord.2.2 hlinear hpadding
        hCr hCo hCb (C := C) le_rfl P (Z l) x hp
      simpa only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] using hr
    · rw [gridHorizon_eq_mul_rpow_neg_sub (zero_lt_one.trans hρ) hSidx.1]
      exact profile_comparison_of_scale_indices hb hl hM0
        hord.2.2 hlinear hpadding
        hCr hCo hCb (C := C) le_rfl P (Z l) x
        (hbound P l (Z l) (hZ l) ka km kn kS
          hord.1 hord.2.1 hord.2.2 hSidx.2 x M hM0)

/-- Split the logarithmic comparison into the Lipschitz region `B ≥ r` and
the exceptional lower tail of `B`.  All constants are deterministic, so this
is directly usable uniformly in the spatial parameter. -/
theorem profile_log_difference_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {A B : Ω → ℝ}
    (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hApos : ∀ᵐ ω ∂P, 0 < A ω) (hBpos : ∀ᵐ ω ∂P, 0 < B ω)
    (hLA : MemLp (fun ω => Real.log (A ω)) 4 P)
    (hLB : MemLp (fun ω => Real.log (B ω)) 4 P)
    {r ε L D : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hnA : eLpNorm (fun ω => Real.log (A ω)) 4 P ≤ ENNReal.ofReal L)
    (hnB : eLpNorm (fun ω => Real.log (B ω)) 4 P ≤ ENNReal.ofReal L)
    (hBi : Integrable (fun ω => (B ω)⁻¹ ^ 3) P)
    (hBiD : (∫ ω, (B ω)⁻¹ ^ 3 ∂P) ≤ D)
    (hcap : (∫ ω, min |A ω - B ω| (r / 2) ∂P) ≤ ε) :
    Integrable (fun ω => |Real.log (A ω) - Real.log (B ω)|) P ∧
      (∫ ω, |Real.log (A ω) - Real.log (B ω)| ∂P) ≤
        (2 / r) * ε + 2 * L * (ε / (r / 2)) ^ (3 / 4 : ℝ) +
          2 * L * (D * r ^ 3) ^ (3 / 4 : ℝ) := by
  let E : Set Ω := {ω | B ω < r}
  have hE : NullMeasurableSet E P :=
    nullMeasurableSet_lt hB aemeasurable_const
  have hEinv : Integrable (fun ω => (B ω)⁻¹ ^ 3 / r⁻¹ ^ 3) P :=
    hBi.div_const _
  have hEnonneg : 0 ≤ᵐ[P] fun ω => (B ω)⁻¹ ^ 3 / r⁻¹ ^ 3 := by
    filter_upwards [hBpos] with ω hω
    positivity
  -- Use the positivity premise only almost everywhere; null-modify `E` by
  -- intersecting with `{B>0}` before Markov.
  let E' : Set Ω := E ∩ {ω | 0 < B ω}
  have hEeq : E =ᵐ[P] E' := by
    filter_upwards [hBpos] with ω hω
    simp only [E', Set.mem_inter_iff, Set.mem_ofPred_eq, hω, and_true]
  have hE'm : NullMeasurableSet E' P := hE.inter
    (nullMeasurableSet_lt aemeasurable_const hB)
  have hEthresh' : ∀ ω ∈ E', 1 ≤ (B ω)⁻¹ ^ 3 / r⁻¹ ^ 3 := by
    intro ω hω
    have hb0 : 0 < B ω := hω.2
    have hbr : B ω < r := hω.1
    rw [one_le_div (by positivity)]
    have hi : r⁻¹ ≤ (B ω)⁻¹ := (inv_le_inv₀ hr hb0).mpr hbr.le
    exact pow_le_pow_left₀ (by positivity) hi 3
  have hprob' := hEinv.measure_le_integral hEnonneg hEthresh'
  have hprob : P E ≤ ENNReal.ofReal (D * r ^ 3) := by
    rw [measure_congr hEeq]
    refine hprob'.trans ?_
    rw [integral_div]
    apply ENNReal.ofReal_le_ofReal
    have hr3 : 0 < r⁻¹ ^ 3 := by positivity
    apply (div_le_iff₀ hr3).2
    calc
      (∫ ω, (B ω)⁻¹ ^ 3 ∂P) ≤ D := hBiD
      _ = (D * r ^ 3) * r⁻¹ ^ 3 := by field_simp [hr.ne']
  obtain ⟨herrI, herr⟩ := profile_log_error_integral_bound P hA hB hLA hLB
    hr hε hL hnA hnB hcap
  have hLAE := profile_integral_abs_on_set_le_four P hLA hL
    (by positivity : 0 ≤ D * r ^ 3) hnA E hprob
  have hLBE := profile_integral_abs_on_set_le_four P hLB hL
    (by positivity : 0 ≤ D * r ^ 3) hnB E hprob
  have hlogI : Integrable (fun ω => |Real.log (A ω) - Real.log (B ω)|) P :=
    ((hLA.integrable (by norm_num)).sub
      (hLB.integrable (by norm_num))).abs
  refine ⟨hlogI, ?_⟩
  have hYI : Integrable (fun ω => |Real.log (A ω)| + |Real.log (B ω)|) P := by
    simpa only [Pi.add_def] using
      (hLA.integrable (by norm_num)).abs.add (hLB.integrable (by norm_num)).abs
  have hindI := hYI.indicator₀ hE
  have hpoint : ∀ᵐ ω ∂P,
      |Real.log (A ω) - Real.log (B ω)| ≤
        profileLogComparisonError r (A ω) (B ω) +
          E.indicator (fun ω => |Real.log (A ω)| + |Real.log (B ω)|) ω := by
    filter_upwards [hApos, hBpos] with ω hAω hBω
    by_cases hb : ω ∈ E
    · rw [Set.indicator_of_mem hb]
      have hab := abs_sub (Real.log (A ω)) (Real.log (B ω))
      exact hab.trans (le_add_of_nonneg_left (profileLogComparisonError_nonneg hr _ _))
    · rw [Set.indicator_of_notMem hb, add_zero]
      exact profile_abs_log_sub_le_error hr hAω (le_of_not_gt hb)
  calc
    (∫ ω, |Real.log (A ω) - Real.log (B ω)| ∂P) ≤
        ∫ ω, profileLogComparisonError r (A ω) (B ω) +
          E.indicator (fun ω => |Real.log (A ω)| + |Real.log (B ω)|) ω ∂P := by
      apply integral_mono_ae hlogI
        (herrI.add hindI) hpoint
    _ = (∫ ω, profileLogComparisonError r (A ω) (B ω) ∂P) +
        (∫ ω in E, |Real.log (A ω)| + |Real.log (B ω)| ∂P) := by
      rw [integral_add herrI hindI, integral_indicator₀ hE]
    _ ≤ ((2 / r) * ε + 2 * L * (ε / (r / 2)) ^ (3 / 4 : ℝ)) +
        (L * (D * r ^ 3) ^ (3 / 4 : ℝ) +
          L * (D * r ^ 3) ^ (3 / 4 : ℝ)) := by
      apply add_le_add herr
      rw [integral_add
        ((hLA.integrable (by norm_num)).abs.restrict)
        ((hLB.integrable (by norm_num)).abs.restrict)]
      exact add_le_add hLAE hLBE
    _ = _ := by ring

/-- Deterministic envelope for the full good/bad logarithmic split. -/
@[expose] noncomputable def profileLogDifferenceEnvelope (C L D l : ℝ) : ℝ :=
  profileLogErrorEnvelope C L l +
    2 * L * Real.log l *
      (D * (l ^ (-(5 / 8 : ℝ))) ^ 3) ^ (3 / 4 : ℝ) * Real.sqrt l

/-- The `r=l⁻⁵/⁸` split converts the capped comparison and inverse-third
moment into a vanishing rescaled logarithmic error. -/
theorem profile_log_difference_scale_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {A B : Ω → ℝ}
    (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hApos : ∀ᵐ ω ∂P, 0 < A ω) (hBpos : ∀ᵐ ω ∂P, 0 < B ω)
    (hLA : MemLp (fun ω => Real.log (A ω)) 4 P)
    (hLB : MemLp (fun ω => Real.log (B ω)) 4 P)
    {C L D l : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D) (hl : 1 ≤ l)
    (hnA : eLpNorm (fun ω => Real.log (A ω)) 4 P ≤
      ENNReal.ofReal (L * Real.log l))
    (hnB : eLpNorm (fun ω => Real.log (B ω)) 4 P ≤
      ENNReal.ofReal (L * Real.log l))
    (hBi : Integrable (fun ω => (B ω)⁻¹ ^ 3) P)
    (hBiD : (∫ ω, (B ω)⁻¹ ^ 3 ∂P) ≤ D)
    (hcap : let r := l ^ (-(5 / 8 : ℝ))
      (∫ ω, min |A ω - B ω| (r / 2) ∂P) ≤
        C / (l * Real.sqrt l) + C * (r / 2) / l) :
    Integrable (fun ω => |Real.log (A ω) - Real.log (B ω)|) P ∧
      Real.sqrt l *
        (∫ ω, |Real.log (A ω) - Real.log (B ω)| ∂P) ≤
          profileLogDifferenceEnvelope C L D l := by
  let r := l ^ (-(5 / 8 : ℝ))
  let ε := C / (l * Real.sqrt l) + C * (r / 2) / l
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  have hr : 0 < r := Real.rpow_pos_of_pos hl0 _
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  obtain ⟨hint, hb⟩ := profile_log_difference_integral_le P hA hB hApos hBpos
    hLA hLB hr hε (mul_nonneg hL (Real.log_nonneg hl)) hD hnA hnB hBi hBiD hcap
  refine ⟨hint, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg l)
  have hgood := profile_log_error_scale_bound hC hL hl
  dsimp only [r, ε] at hm ⊢
  dsimp only [profileLogDifferenceEnvelope]
  calc
    _ ≤ Real.sqrt l *
        ((2 / l ^ (-(5 / 8 : ℝ))) *
          (C / (l * Real.sqrt l) + C * (l ^ (-(5 / 8 : ℝ)) / 2) / l) +
        2 * (L * Real.log l) *
          ((C / (l * Real.sqrt l) + C * (l ^ (-(5 / 8 : ℝ)) / 2) / l) /
            (l ^ (-(5 / 8 : ℝ)) / 2)) ^ (3 / 4 : ℝ) +
        2 * (L * Real.log l) *
          (D * (l ^ (-(5 / 8 : ℝ))) ^ 3) ^ (3 / 4 : ℝ)) := hm
    _ = Real.sqrt l *
        ((2 / l ^ (-(5 / 8 : ℝ))) *
          (C / (l * Real.sqrt l) + C * (l ^ (-(5 / 8 : ℝ)) / 2) / l) +
        2 * (L * Real.log l) *
          ((C / (l * Real.sqrt l) + C * (l ^ (-(5 / 8 : ℝ)) / 2) / l) /
            (l ^ (-(5 / 8 : ℝ)) / 2)) ^ (3 / 4 : ℝ)) +
        2 * L * Real.log l *
          (D * (l ^ (-(5 / 8 : ℝ))) ^ 3) ^ (3 / 4 : ℝ) * Real.sqrt l := by ring
    _ ≤ _ := add_le_add hgood le_rfl

/-- The full good/bad deterministic envelope tends to zero. -/
theorem profileLogDifferenceEnvelope_tendsto
    (C L D : ℝ) (hD : 0 ≤ D) :
    Tendsto (profileLogDifferenceEnvelope C L D) atTop (𝓝 0) := by
  have hgood := profileLogErrorEnvelope_tendsto C L
  have hbadbase : Tendsto
      (fun l : ℝ => Real.log l * l ^ (-(29 / 32 : ℝ))) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 29 / 32)).tendsto_div_nhds_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl
    rw [Real.rpow_neg hl.le]
    ring
  have hbad : Tendsto (fun l : ℝ =>
      2 * L * Real.log l *
        (D * (l ^ (-(5 / 8 : ℝ))) ^ 3) ^ (3 / 4 : ℝ) * Real.sqrt l)
      atTop (𝓝 0) := by
    have heq : ∀ᶠ l : ℝ in atTop,
        2 * L * Real.log l *
          (D * (l ^ (-(5 / 8 : ℝ))) ^ 3) ^ (3 / 4 : ℝ) * Real.sqrt l =
        (2 * L * D ^ (3 / 4 : ℝ)) *
          (Real.log l * l ^ (-(29 / 32 : ℝ))) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl
      have he : ((l ^ (-(5 / 8 : ℝ))) ^ (3 : ℕ)) ^ (3 / 4 : ℝ) * Real.sqrt l =
          l ^ (-(29 / 32 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hl.le,
          ← Real.rpow_mul hl.le, Real.sqrt_eq_rpow, ← Real.rpow_add hl]
        norm_num
      rw [Real.mul_rpow hD (by positivity)]
      calc
        _ = (2 * L * D ^ (3 / 4 : ℝ)) * Real.log l *
            (((l ^ (-(5 / 8 : ℝ))) ^ (3 : ℕ)) ^ (3 / 4 : ℝ) * Real.sqrt l) := by ring
        _ = _ := by rw [he]; ring
    have hh := hbadbase.const_mul (2 * L * D ^ (3 / 4 : ℝ))
    simpa only [mul_zero] using hh.congr' (heq.mono fun _ h => h.symm)
  change Tendsto (fun l : ℝ => profileLogErrorEnvelope C L l +
    2 * L * Real.log l * (D * (l ^ (-(5 / 8 : ℝ))) ^ 3) ^ (3 / 4 : ℝ) * Real.sqrt l)
    atTop (𝓝 0)
  simpa only [add_zero] using hgood.add hbad

/-- Spatial integration of the pointwise logarithmic Lipschitz split.  The
joint hypotheses are exactly what `profileMass_joint_regular` supplies. -/
theorem spatial_profile_log_difference_scale_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A B : Plane → Ω → ℝ} {C L D l : ℝ}
    (hAlog : AEStronglyMeasurable
      (fun p : Ω × Plane => Real.log (A p.2 p.1)) (P.prod volume))
    (hBlog : AEStronglyMeasurable
      (fun p : Ω × Plane => Real.log (B p.2 p.1)) (P.prod volume))
    (hAmeas : ∀ x, AEMeasurable (A x) P)
    (hBmeas : ∀ x, AEMeasurable (B x) P)
    (hApos : ∀ᵐ ω ∂P, ∀ x, 0 < A x ω)
    (hBpos : ∀ᵐ ω ∂P, ∀ x, 0 < B x ω)
    (hLA : ∀ x, MemLp (fun ω => Real.log (A x ω)) 4 P)
    (hLB : ∀ x, MemLp (fun ω => Real.log (B x ω)) 4 P)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D) (hl : 1 ≤ l)
    (hnA : ∀ x, eLpNorm (fun ω => Real.log (A x ω)) 4 P ≤
      ENNReal.ofReal (L * Real.log l))
    (hnB : ∀ x, eLpNorm (fun ω => Real.log (B x ω)) 4 P ≤
      ENNReal.ofReal (L * Real.log l))
    (hBi : ∀ x, Integrable (fun ω => (B x ω)⁻¹ ^ 3) P)
    (hBiD : ∀ x, (∫ ω, (B x ω)⁻¹ ^ 3 ∂P) ≤ D)
    (hcap : ∀ x,
      let r := l ^ (-(5 / 8 : ℝ))
      (∫ ω, min |A x ω - B x ω| (r / 2) ∂P) ≤
        C / (l * Real.sqrt l) + C * (r / 2) / l)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    let X := fun ω x => |Real.log (A x ω) - Real.log (B x ω)|
    (∀ᵐ ω ∂P, Integrable (fun x => |f x| * X ω x)) ∧
      Integrable (fun ω => ∫ x, |f x| * X ω x) P ∧
      Real.sqrt l * (∫ ω, (∫ x, |f x| * X ω x) ∂P) ≤
        (∫ x, |f x|) * profileLogDifferenceEnvelope C L D l := by
  dsimp only
  let X : Ω → Plane → ℝ :=
    fun ω x => |Real.log (A x ω) - Real.log (B x ω)|
  have hX : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume) :=
    (hAlog.sub hBlog).norm
  have hX0 (ω : Ω) (x : Plane) : 0 ≤ X ω x := abs_nonneg _
  have hpoint (x : Plane) :
      Integrable (fun ω => X ω x) P ∧
      Real.sqrt l * (∫ ω, X ω x ∂P) ≤ profileLogDifferenceEnvelope C L D l := by
    exact profile_log_difference_scale_bound P
      (hAmeas x) (hBmeas x)
      (hApos.mono fun ω hω => hω x) (hBpos.mono fun ω hω => hω x)
      (hLA x) (hLB x) hC hL hD hl (hnA x) (hnB x)
      (hBi x) (hBiD x) (hcap x)
  have hl0 : 0 < l := zero_lt_one.trans_le hl
  have hsqrt : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl0
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl
  have hEnv : 0 ≤ profileLogDifferenceEnvelope C L D l := by
    unfold profileLogDifferenceEnvelope profileLogErrorEnvelope
    positivity
  have hbound (x : Plane) :
      (∫ ω, X ω x ∂P) ≤ profileLogDifferenceEnvelope C L D l / Real.sqrt l :=
    (le_div_iff₀ hsqrt).mpr (by simpa only [mul_comm] using (hpoint x).2)
  obtain ⟨hpath, hint, hb⟩ := profile_weighted_nonneg_integral_bound
    P hX hX0 (fun x => (hpoint x).1) (div_nonneg hEnv hsqrt.le) hbound hf hfi
  refine ⟨hpath, hint, ?_⟩
  calc
    _ ≤ Real.sqrt l *
        (profileLogDifferenceEnvelope C L D l / Real.sqrt l * ∫ x, |f x|) :=
      mul_le_mul_of_nonneg_left hb hsqrt.le
    _ = _ := by field_simp

/-- The preceding spatial expectation vanishes after multiplication by
`sqrt l`; this is the deterministic-envelope form used by the UV assembly. -/
theorem spatial_profile_log_difference_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A B : ℝ → Plane → Ω → ℝ} {C L D : ℝ}
    (_hC : 0 ≤ C) (_hL : 0 ≤ L) (hD : 0 ≤ D)
    {f : Plane → ℝ} (_hfi : Integrable f)
    (hmain : ∀ᶠ l : ℝ in atTop,
      Integrable (fun ω => ∫ x, |f x| *
        |Real.log (A l x ω) - Real.log (B l x ω)|) P ∧
      Real.sqrt l * (∫ ω, (∫ x, |f x| *
        |Real.log (A l x ω) - Real.log (B l x ω)|) ∂P) ≤
          (∫ x, |f x|) * profileLogDifferenceEnvelope C L D l) :
    Tendsto (fun l => Real.sqrt l * (∫ ω, (∫ x, |f x| *
      |Real.log (A l x ω) - Real.log (B l x ω)|) ∂P)) atTop (𝓝 0) := by
  have henv := (profileLogDifferenceEnvelope_tendsto C L D hD).const_mul (∫ x, |f x|)
  apply squeeze_zero' (g := fun l => (∫ x, |f x|) * profileLogDifferenceEnvelope C L D l)
  · filter_upwards [hmain, eventually_ge_atTop (0 : ℝ)] with l hl hl0
    exact mul_nonneg (Real.sqrt_nonneg _) (integral_nonneg fun ω =>
      integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  · exact hmain.mono fun l hl => hl.2
  · simpa only [mul_zero] using henv


/-- The coarse entrance is eventually less than half the observation time. -/
theorem eventually_two_mul_uvCoarseEntrance_lt_uvObservation
    {c ρ wM : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hwM : 0 < wM) (hwM1 : wM < 1) :
    ∀ᶠ l : ℝ in atTop,
      2 * uvCoarseEntrance c ρ wM l < uvObservation c ρ l := by
  have hlogw : 0 < |Real.log wM| := abs_pos.mpr (Real.log_neg hwM hwM1).ne
  have hJtop : Tendsto (gridJ wM) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    have ht : Tendsto (fun l : ℝ => 2 * Real.log l / |Real.log wM|) atTop atTop :=
      by
      have ht := Real.tendsto_log_atTop.const_mul_atTop (div_pos (by norm_num : (0:ℝ)<2) hlogw)
      simpa only [div_mul_eq_mul_div] using ht
    filter_upwards [ht.eventually_ge_atTop K] with l hl
    exact_mod_cast hl.trans (Nat.le_ceil _)
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt hρ).comp hJtop
  filter_upwards [hpow.eventually_gt_atTop 2] with l hJ
  rw [uvCoarseEntrance, uvPadding_eq_gridJ]
  rw [← mul_div_assoc]
  apply (div_lt_iff₀ (pow_pos (zero_lt_one.trans hρ) _)).mpr
  have hn : 0 < uvObservation c ρ l := uvGridPoint_pos (mul_pos hc (Real.exp_pos l)) (zero_lt_one.trans hρ)
  simpa only [Function.comp_def, mul_comm] using mul_lt_mul_of_pos_left hJ hn

/-- Coarse entrance using `wM` versus the padded horizon using an independent
`wS`: the variance ratio is `O(log l/l)`. -/
theorem uvCoarse_independentHorizon_ratio_le
    {c ρ wM wS : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hwM : 0 < wM) (hwMHalf : wM < 1 / 2)
    (hwS : 0 < wS) (hwSHalf : wS < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ l : ℝ in atTop,
      Real.log (gridHorizon c ρ wS l / uvCoarseEntrance c ρ wM l) /
          (l - Real.log (gridHorizon c ρ wS l)) ≤ C * Real.log l / l := by
  obtain ⟨d, hd, hgrid⟩ := grid_properties hc hρ hwS hwSHalf
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  let C := 2 * (d + 201 + 2 * Real.log ρ / |Real.log wM| + Real.log ρ)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hgrid, uv_targets_fit hc,
    uvScales_horizon_order hc hρ hwS hwSHalf,
    eventually_gridJ_mul_log_le hρ hwM hwMHalf,
    eventually_mul_log_add_le_half d 0,
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop ρ] with l hg hfit hord hJM hpoly hl hlρ
  have hl0 := hfit.1
  have hS0 := gridHorizon_pos hc (zero_lt_one.trans hρ) wS l
  have hm0 := (uvCoarseEntrance_bounds hc hρ wM l).1
  have hden : l / 2 ≤ l - Real.log (gridHorizon c ρ wS l) := by
    have hlogS := Real.log_le_log hS0 hg.2.2.2.1
    rw [Real.log_rpow hl0] at hlogS
    linarith
  have hnum : Real.log (gridHorizon c ρ wS l / uvCoarseEntrance c ρ wM l) ≤
      (d + 201 + 2 * Real.log ρ / |Real.log wM| + Real.log ρ) * Real.log l := by
    rw [Real.log_div hS0.ne' hm0.ne']
    have hlogS := Real.log_le_log hS0 hg.2.2.2.1
    rw [Real.log_rpow hl0] at hlogS
    have hnlow := (uvObservation_bounds hc hρ hl0 hfit.2.2).1
    have hmlow : l⁻¹ ^ 200 / ρ / ρ ^ gridJ wM l < uvCoarseEntrance c ρ wM l := by
      rw [uvCoarseEntrance, uvPadding_eq_gridJ]
      exact div_lt_div_of_pos_right hnlow (pow_pos (zero_lt_one.trans hρ) _)
    have hlo0 : 0 < l⁻¹ ^ 200 / ρ / ρ ^ gridJ wM l := by positivity
    have hlogm := Real.log_le_log hlo0 hmlow.le
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (zero_lt_one.trans hρ).ne', Real.log_pow, Real.log_inv,
      Real.log_pow] at hlogm
    push_cast at hlogm
    have hlogs := Real.log_le_log (zero_lt_one.trans hρ) hlρ
    nlinarith only [hJM, hlogs, hlogm, hlogS]
  have hden0 : 0 < l - Real.log (gridHorizon c ρ wS l) :=
    (half_pos hl0).trans_le hden
  apply (div_le_iff₀ hden0).2
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg ((Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hl)
  have hbase : 0 ≤
      (d + 201 + 2 * Real.log ρ / |Real.log wM| + Real.log ρ) * Real.log l := by
    positivity
  calc
    _ ≤ _ := hnum
    _ ≤ C * Real.log l / l * (l - Real.log (gridHorizon c ρ wS l)) := by
      dsimp only [C]
      have hh := mul_le_mul_of_nonneg_left hden hbase
      field_simp [hl0.ne'] at hh ⊢
      nlinarith

/-- Fine entrance versus an independently padded horizon has the source
`O(l^39)` variance ratio. -/
theorem uvFine_independentHorizon_ratio_le
    {c ρ wS : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hwS : 0 < wS) (hwSHalf : wS < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ l : ℝ in atTop,
      Real.log (gridHorizon c ρ wS l / uvFineEntrance c ρ l) /
          (l - Real.log (gridHorizon c ρ wS l)) ≤ C * l ^ 39 := by
  obtain ⟨d, hd, hgrid⟩ := grid_properties hc hρ hwS hwSHalf
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  refine ⟨4, by norm_num, ?_⟩
  filter_upwards [hgrid, uv_targets_fit hc, eventually_mul_log_add_le_half d (Real.log ρ),
    eventually_ge_atTop (Real.exp 1)] with l hg hfit hpoly hl
  have hl0 := hfit.1
  have hS0 := gridHorizon_pos hc (zero_lt_one.trans hρ) wS l
  have ha0 : 0 < uvFineEntrance c ρ l := uvGridPoint_pos (mul_pos hc (Real.exp_pos l)) (zero_lt_one.trans hρ)
  have hden : l / 2 ≤ l - Real.log (gridHorizon c ρ wS l) := by
    have hlogS := Real.log_le_log hS0 hg.2.2.2.1
    rw [Real.log_rpow hl0] at hlogS
    linarith
  have hnum : Real.log (gridHorizon c ρ wS l / uvFineEntrance c ρ l) ≤ 2 * l ^ 40 := by
    rw [Real.log_div hS0.ne' ha0.ne']
    have hlogS := Real.log_le_log hS0 hg.2.2.2.1
    rw [Real.log_rpow hl0] at hlogS
    have halow := (uvFineEntrance_bounds hc hρ hfit.2.1).1
    have hloa0 : 0 < Real.exp (-(l ^ 40)) / ρ := div_pos (Real.exp_pos _) (zero_lt_one.trans hρ)
    have hloga := Real.log_le_log hloa0 halow.le
    rw [Real.log_div (Real.exp_pos _).ne' (zero_lt_one.trans hρ).ne', Real.log_exp] at hloga
    have hl40 : l / 2 ≤ l ^ 40 := by
      have hl1 : 1 < l := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hl
      have hp : l < l ^ 40 := by
        simpa only [pow_one] using pow_lt_pow_right₀ hl1 (by norm_num : (1 : ℕ) < 40)
      linarith
    linarith
  have hden0 : 0 < l - Real.log (gridHorizon c ρ wS l) :=
    (half_pos hl0).trans_le hden
  apply (div_le_iff₀ hden0).2
  have hp : l ^ 40 = l ^ 39 * l := by ring
  have hh := mul_le_mul_of_nonneg_left hden (pow_nonneg hl0.le 39)
  nlinarith only [hnum, hp, hh]


end Critical2DKPZ.Extensions.GffTangent

end
