/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.Entrance
public import Critical2DKPZ.Extensions.GffTangent.LinearClt
import Critical2DKPZ.Extensions.GffTangent.Localisation
import Critical2DKPZ.Extensions.GffTangent.LinearCovariance
import Critical2DKPZ.Extensions.GffTangent.Semiconvexity
import Critical2DKPZ.Extensions.GffTangent.CompareFutures
import Critical2DKPZ.Extensions.GffTangent.LogMoments

/-! # The scalar logarithm linearization used in ultraviolet removal -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- For a positive mean-one mass, the absolute error in linearizing its logarithm
has expectation exactly minus the mean logarithm. Integrability is explicit. -/
theorem integral_abs_log_linearisation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Integrable X P) (hlog : Integrable (fun ω => Real.log (X ω)) P)
    (hpos : ∀ᵐ ω ∂P, 0 < X ω) (hmean : (∫ ω, X ω ∂P) = 1) :
    Integrable (fun ω => |X ω - 1 - Real.log (X ω)|) P ∧
      (∫ ω, |X ω - 1 - Real.log (X ω)| ∂P) = -(∫ ω, Real.log (X ω) ∂P) := by
  have hsub : Integrable (fun ω => X ω - 1) P := hX.sub (integrable_const 1)
  have herr : Integrable (fun ω => X ω - 1 - Real.log (X ω)) P := hsub.sub hlog
  have heq : (fun ω => |X ω - 1 - Real.log (X ω)|) =ᵐ[P]
      fun ω => X ω - 1 - Real.log (X ω) := by
    filter_upwards [hpos] with ω hω
    exact abs_of_nonneg (sub_nonneg.mpr (Real.log_le_sub_one_of_pos hω))
  refine ⟨herr.abs, ?_⟩
  rw [integral_congr_ae heq, integral_sub hsub hlog, integral_sub hX (integrable_const 1), hmean]
  simp only [integral_const, probReal_univ, one_smul, sub_self, zero_sub]

/-- For a heat-started mass the nonlinear logarithmic error is controlled by
half the logarithm of the second-moment bound. -/
theorem heat_mass_linearisation (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T v : ℝ} (ha : 0 < a) (haT : a < T) (hl : 0 < l - Real.log T)
    (hv : Real.log (T / a) / (l - Real.log T) ≤ v) (x : Plane) :
    let X := shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1)
    Integrable (fun ω => |X ω - 1 - Real.log (X ω)|) P ∧
      (∫ ω, |X ω - 1 - Real.log (X ω)| ∂P) = -(∫ ω, Real.log (X ω) ∂P) ∧
      (∫ ω, |X ω - 1 - Real.log (X ω)| ∂P) ≤ Real.log (1 + v) / 2 := by
  dsimp only
  let X := shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1)
  have hm : MemLp X 2 P := heatStartMass_memLp_two (-l) P Z hZ ha haT x
  have hmean : (∫ ω, X ω ∂P) = 1 := (heatStartMass_integral_eq_one (-l) P Z hZ ha haT x).2
  have hlog := heatStartMass_convexity_moments (-l) P Z hZ ha haT x
  have heq := integral_abs_log_linearisation P (hm.integrable (by norm_num))
    (hlog.2.2.1.integrable (by norm_num)) (heatMass_pos (-l) P Z hZ ha haT x) hmean
  refine ⟨heq.1, heq.2, ?_⟩
  rw [heq.2]
  have hsecond := (entrance_mass_second_moment_le l P Z hZ ha haT hl hv x).2
  have hn := variance_nonneg X P
  rw [variance_eq_sub hm, hmean] at hn
  have hmoment : 0 < ∫ ω, X ω ^ 2 ∂P := by norm_num at hn; linarith only [hn]
  exact hlog.2.2.2.2.trans (div_le_div_of_nonneg_right (Real.log_le_log hmoment hsecond)
    (by norm_num : (0 : ℝ) ≤ 2))

/- The second-moment criterion applies to both entrance scales below. -/
theorem lField_interval_second_moment_tendsto_of_ratio39
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l)) (f : TestFn) (hf : (∫ x, f x) = 0)
    (a T : ℝ → ℝ) {K : ℝ} (hK : 0 < K)
    (hs : ∀ᶠ l : ℝ in atTop, 1 ≤ l ∧ 0 < a l ∧ a l < T l ∧
      0 < l - Real.log (T l) ∧ T l ≤ l⁻¹ ^ 200 ∧
      Real.log (T l / a l) / (l - Real.log (T l)) ≤ K * l ^ 39) :
    Tendsto (fun l => l * ∫ ω, lField (Z l) (a l) (T l) f ω ^ 2 ∂P)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := lField_second_moment_bound
  obtain ⟨B, hB'⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hB : ∀ x, |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB'
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hB 0)
  let D : ℝ := C * (∫ x : Plane, |f x|) * B * (1 + K) ^ 4
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hrate : Tendsto (fun l : ℝ => D * l⁻¹ ^ 43) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (43:ℕ) ≠ 0), mul_zero] using (tendsto_inv_atTop_zero.pow 43).const_mul D
  apply squeeze_zero' (g := fun l => D * l⁻¹ ^ 43) ?_ ?_ hrate
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with l hl
    exact mul_nonneg hl (integral_nonneg fun _ => sq_nonneg _)
  · filter_upwards [hs] with l hl
    let r := Real.log (T l / a l) / (l - Real.log (T l))
    have hr0 : 0 ≤ r := div_nonneg
      (Real.log_nonneg ((one_le_div hl.2.1).2 hl.2.2.1.le)) hl.2.2.2.1.le
    have hone : 1 + r ≤ (1 + K) * l ^ 39 := by
      calc
        1 + r ≤ 1 + K * l ^ 39 := add_le_add le_rfl hl.2.2.2.2.2
        _ ≤ (1 + K) * l ^ 39 := by
          nlinarith [one_le_pow₀ hl.1 (n := 39), hK.le]
    have hsqrt : Real.sqrt (1 + Real.log (1 + r)) ≤ 1 + r := by
      have hp : 0 < 1 + r := by linarith
      have hh := Real.log_le_sub_one_of_pos hp
      have hlog0 : 0 ≤ 1 + Real.log (1 + r) :=
        add_nonneg zero_le_one (Real.log_nonneg (by linarith))
      exact (Real.sqrt_le_sqrt (by linarith)).trans
        ((Real.sqrt_le_self_iff).2 (Or.inr (by linarith)))
    have hm := (hb l (a l) (T l) hl.2.1 hl.2.2.1 hl.2.2.2.1
      P (Z l) (hZ l) f B hB0 hB hf).2
    change (∫ ω, lField (Z l) (a l) (T l) f ω ^ 2 ∂P) ≤
      C * (∫ x, |f x|) * B * T l * (1 + r) ^ 3 *
        Real.sqrt (1 + Real.log (1 + r)) at hm
    have hT0 : 0 < T l := hl.2.1.trans hl.2.2.1
    have hm4 : (∫ ω, lField (Z l) (a l) (T l) f ω ^ 2 ∂P) ≤
        C * (∫ x, |f x|) * B * T l * (1 + r) ^ 4 := by
      calc
        _ ≤ _ := hm
        _ ≤ C * (∫ x, |f x|) * B * T l * (1 + r) ^ 3 * (1 + r) := by
          have hbase : 0 ≤ C * (∫ x, |f x|) * B * T l * (1 + r) ^ 3 := by positivity
          exact mul_le_mul_of_nonneg_left hsqrt hbase
        _ = _ := by ring
    have hp4 : (1 + r) ^ 4 ≤ (1 + K) ^ 4 * l ^ 156 := by
      calc
        _ ≤ ((1 + K) * l ^ 39) ^ 4 := pow_le_pow_left₀ (by linarith) hone 4
        _ = _ := by ring
    calc
      l * (∫ ω, lField (Z l) (a l) (T l) f ω ^ 2 ∂P) ≤
          l * (C * (∫ x, |f x|) * B * T l * (1 + r) ^ 4) :=
        mul_le_mul_of_nonneg_left hm4 (zero_lt_one.trans_le hl.1).le
      _ ≤ l * (C * (∫ x, |f x|) * B * (l⁻¹ ^ 200) *
          ((1 + K) ^ 4 * l ^ 156)) := by
        have hl0 : 0 ≤ l := (zero_lt_one.trans_le hl.1).le
        have hCB : 0 ≤ C * (∫ x, |f x|) * B := by positivity
        have hTK : 0 ≤ (1 + r) ^ 4 := pow_nonneg (by linarith) _
        have hInv : 0 ≤ l⁻¹ ^ 200 := pow_nonneg (inv_nonneg.mpr hl0) _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_left hl.2.2.2.2.1 hCB) hp4
            hTK (mul_nonneg hCB hInv)) hl0
      _ = D * l⁻¹ ^ 43 := by
        dsimp only [D]
        field_simp [ne_of_gt (zero_lt_one.trans_le hl.1)]

theorem fine_interval_zero_observation_second_moment
    {c ρ : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : TestFn) (hf : (∫ x, f x) = 0) :
    Tendsto (fun l => l * ∫ ω, lField (Z l) (uvFineEntrance c ρ l)
      (uvObservation c ρ l) f ω ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨K, hK, hr⟩ := uvFine_observation_ratio_le hc hρ
  apply lField_interval_second_moment_tendsto_of_ratio39 P Z hZ f hf _ _ hK
  filter_upwards [uv_targets_fit hc,
    uvScales_horizon_order (w := (1/4 : ℝ)) hc hρ (by norm_num) (by norm_num), hr,
    eventually_uvFineEntrance_lt_uvCoarseEntrance hc hρ (by norm_num : (0:ℝ)<1/4)
      (by norm_num : (1/4:ℝ)<1/2),
    eventually_ge_atTop (1 : ℝ)] with l hfit ho hratio hfa hl
  refine ⟨hl, uvGridPoint_pos (mul_pos hc (Real.exp_pos l)) (zero_lt_one.trans hρ),
    hfa.trans ho.2.1, ?_, (uvObservation_bounds hc hρ hfit.1 hfit.2.2).2, hratio⟩
  have hlogn : Real.log (uvObservation c ρ l) < 0 :=
    Real.log_neg (uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
      (zero_lt_one.trans hρ)) ho.2.2.1
  linarith [zero_lt_one.trans_le hl]

theorem coarse_interval_zero_observation_second_moment
    {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ) (hw : 0 < w) (hw' : w < 1/2)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : TestFn) (hf : (∫ x, f x) = 0) :
    Tendsto (fun l => l * ∫ ω, lField (Z l) (uvCoarseEntrance c ρ w l)
      (uvObservation c ρ l) f ω ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨K, hK, hr⟩ := uvCoarse_observation_ratio_le hc hρ hw hw'
  apply lField_interval_second_moment_tendsto_of_ratio39 P Z hZ f hf _ _ hK
  filter_upwards [uv_targets_fit hc, uvScales_horizon_order hc hρ hw hw', hr,
    eventually_ge_atTop (Real.exp 1)] with l hfit ho hratio hl
  have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num)).trans hl
  have hlogle : Real.log l ≤ l :=
    (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hl1)).trans (by linarith)
  have hlog : Real.log l / l ≤ l ^ 39 := by
    have hone : Real.log l / l ≤ 1 := (div_le_one (zero_lt_one.trans_le hl1)).2 hlogle
    exact hone.trans (one_le_pow₀ hl1)
  refine ⟨hl1, (uvCoarseEntrance_bounds hc hρ w l).1, ho.2.1, ?_,
    (uvObservation_bounds hc hρ hfit.1 hfit.2.2).2,
    hratio.trans (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hlog hK.le)⟩
  have hlogn : Real.log (uvObservation c ρ l) < 0 :=
    Real.log_neg (uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
      (zero_lt_one.trans hρ)) ho.2.2.1
  linarith [zero_lt_one.trans_le hl1]


/-- Uniform moment package at the independent UV scales.  Constants precede
the probability space, flow and spatial point. -/
theorem exists_uv_heatStartMass_moment_bounds
    {c ρ wM wS : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hwM : 0 < wM) (hwMHalf : wM < 1 / 2)
    (hwS : 0 < wS) (hwSHalf : wS < 1 / 2) :
    ∃ C6 Cm CS Ca : ℝ, 0 ≤ C6 ∧ 0 < Cm ∧ 0 < CS ∧ 0 < Ca ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
      (_hZ : ∀ l, IsCriticalSHF (-l) P (Z l)),
      ∀ᶠ l : ℝ in atTop, ∀ x : Plane,
        let m := uvCoarseEntrance c ρ wM l
        let n := uvObservation c ρ l
        let S := gridHorizon c ρ wS l
        let a := uvFineEntrance c ρ l
        Integrable (fun ω => shfPairing (Z l) m n
          (fun y => heatKernel m (y - x)) (fun _ => 1) ω ^ 6) P ∧
        (∫ ω, shfPairing (Z l) m n (fun y => heatKernel m (y - x))
          (fun _ => 1) ω ^ 6 ∂P) ≤ C6 ∧
        (∫ ω, shfPairing (Z l) m S (fun y => heatKernel m (y - x))
          (fun _ => 1) ω ^ 2 ∂P) ≤ 1 + CS * Real.log l / l ∧
        Integrable (fun ω => (shfPairing (Z l) m S
          (fun y => heatKernel m (y - x)) (fun _ => 1) ω)⁻¹ ^ 6) P ∧
        (∫ ω, (shfPairing (Z l) m S (fun y => heatKernel m (y - x))
          (fun _ => 1) ω)⁻¹ ^ 6 ∂P) ≤ (1 + CS * Real.log l / l) ^ 21 ∧
        (∫ ω, shfPairing (Z l) a S (fun y => heatKernel a (y - x))
          (fun _ => 1) ω ^ 2 ∂P) ≤ 1 + Ca * l ^ 39 := by
  obtain ⟨C6, hC6, hsix⟩ := exists_heatStartMass_sixth_of_ratio
  obtain ⟨Cm, hCm, hmnratio⟩ := uvCoarse_observation_ratio_le
    hc hρ hwM hwMHalf
  obtain ⟨CS, hCS, hmSratio⟩ := uvCoarse_independentHorizon_ratio_le
    hc hρ hwM hwMHalf hwS hwSHalf
  obtain ⟨Ca, hCa, haSratio⟩ := uvFine_independentHorizon_ratio_le
    hc hρ hwS hwSHalf
  obtain ⟨dS, hdS, hgridS⟩ := grid_properties hc hρ hwS hwSHalf
  refine ⟨C6, Cm, CS, Ca, hC6, hCm, hCS, hCa, ?_⟩
  intro Ω _ P _ Z hZ
  have hsmall : ∀ᶠ l : ℝ in atTop, Cm * Real.log l / l < 1 := by
    have ht : Tendsto (fun l : ℝ => Cm * (Real.log l / l)) atTop (𝓝 0) := by
      simpa only [id_eq, mul_zero] using
        Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul Cm
    simpa only [mul_div_assoc] using
      ht.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hmnratio, hmSratio, haSratio, hsmall, hgridS,
    eventually_mul_log_add_le_half dS 0,
    eventually_two_mul_uvCoarseEntrance_lt_uvObservation hc hρ hwM
      (hwMHalf.trans (by norm_num)),
    uvScales_horizon_order hc hρ hwS hwSHalf,
    eventually_uvFineEntrance_lt_uvCoarseEntrance hc hρ hwM hwMHalf,
    eventually_gt_atTop (Real.exp 1)]
      with l hmn hvmS hvaS hsmall hgrid hpoly h2mn hord ham hl
  intro x
  dsimp only
  let m := uvCoarseEntrance c ρ wM l
  let n := uvObservation c ρ l
  let S := gridHorizon c ρ wS l
  let a := uvFineEntrance c ρ l
  have hm0 : 0 < m := uvCoarseEntrance_bounds hc hρ wM l |>.1
  have hn0 : 0 < n := uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
    (zero_lt_one.trans hρ)
  have hS0 : 0 < S := gridHorizon_pos hc (zero_lt_one.trans hρ) wS l
  have ha0 : 0 < a := uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
    (zero_lt_one.trans hρ)
  have hnS : n < S := hord.2.2.1.trans hord.2.2.2.1
  have hmS : m < S := (uvCoarseEntrance_bounds hc hρ wM l).2.trans_lt hnS
  have haS : a < S := ham.trans hmS
  have hln : 0 < l - Real.log n := by
    have hn1 : n < 1 := hord.2.2.1
    have := Real.log_neg hn0 hn1
    linarith [(Real.exp_pos 1).trans hl]
  have hlS : 0 < l - Real.log S := by
    have hl0 : 0 < l := (Real.exp_pos 1).trans hl
    have hlogS := Real.log_le_log hS0 hgrid.2.2.2.1
    rw [Real.log_rpow hl0] at hlogS
    linarith
  have hgapRatio : (l - Real.log m) / (l - Real.log n) < 2 := by
    have heq : (l - Real.log m) / (l - Real.log n) =
        1 + Real.log (n / m) / (l - Real.log n) := by
      rw [Real.log_div hn0.ne' hm0.ne']
      field_simp [hln.ne']
      ring
    rw [heq]
    linarith [hmn]
  have h6 := hsix hm0 h2mn hln hgapRatio P (Z l) (hZ l) x
  have hmS2 := entrance_mass_second_moment_le l P (Z l) (hZ l)
    hm0 hmS hlS hvmS x
  have haS2 := entrance_mass_second_moment_le l P (Z l) (hZ l)
    ha0 haS hlS hvaS x
  have hi6 := heatStartMass_inverse_sixth_moment (-l) P (Z l) (hZ l)
    hm0 hmS x
  exact ⟨h6.1, h6.2, hmS2.2, hi6.1,
    hi6.2.trans (pow_le_pow_left₀
      (integral_nonneg fun ω => sq_nonneg _) hmS2.2 21), haS2.2⟩


/-- The fine/coarse UV profiles at an independently padded final horizon
have vanishing spatially tested logarithmic difference on the GFF scale. -/
theorem uv_profile_log_lipschitz_split {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧
      ∀ ρ, ρ₀ ≤ ρ → ∀ wS, 0 < wS → wS < 1 / 2 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
      (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
      (f : Plane → ℝ) (hf : Measurable f) (_hfi : Integrable f),
      (Tendsto (fun l => Real.sqrt l * ∫ ω, ∫ x, |f x| *
        |Real.log (profileMass (Z l) (uvFineEntrance c ρ l)
          (uvObservation c ρ l) (gridHorizon c ρ wS l) x ω) -
         Real.log (profileMass (Z l) (uvCoarseEntrance c ρ q l)
          (uvObservation c ρ l) (gridHorizon c ρ wS l) x ω)| ∂volume ∂P)
        atTop (𝓝 0)) ∧
      ∀ᶠ l : ℝ in atTop, Integrable (fun ω => ∫ x, |f x| *
        |Real.log (profileMass (Z l) (uvFineEntrance c ρ l)
          (uvObservation c ρ l) (gridHorizon c ρ wS l) x ω) -
         Real.log (profileMass (Z l) (uvCoarseEntrance c ρ q l)
          (uvObservation c ρ l) (gridHorizon c ρ wS l) x ω)|) P := by
  obtain ⟨ρ₀, q, hρ₀, hq, hq2, hcmp⟩ :=
    profile_comparison_at_scales_independent_horizon hc
  refine ⟨ρ₀, q, hρ₀, hq, hq2, ?_⟩
  intro ρ hρ wS hwS hwS2 Ω _ P _ Z hZ f hf hfi
  have hρ' : 1 < ρ := hρ₀.trans_le hρ
  obtain ⟨Cc, hCc, hcmpAll⟩ := hcmp ρ hρ wS hwS hwS2
  have hcmp := hcmpAll P Z hZ
  obtain ⟨C6, Cm, CS, Ca, hC6, hCm, hCS, hCa, hmomAll⟩ :=
    exists_uv_heatStartMass_moment_bounds hc hρ' hq hq2 hwS hwS2
  have hmom := hmomAll P Z hZ
  obtain ⟨Cf, hCf, hfObs⟩ := uvFine_observation_ratio_le hc hρ'
  obtain ⟨Co, hCo, hcoObs⟩ := uvCoarse_observation_ratio_le hc hρ' hq hq2
  let Cpoly := Ca + CS + Cf + Co
  have hCpoly : 0 < Cpoly := by dsimp [Cpoly]; positivity
  let K := 4 * (40 + Real.log (1 + Cpoly)) * (2 + Real.exp 1) ^ ((4 : ℝ)⁻¹)
  let L := 2 * K
  let D := Real.sqrt C6 * Real.sqrt ((1 + CS) ^ 21)
  have hlogCpoly : 0 ≤ Real.log (1 + Cpoly) := Real.log_nonneg (by linarith)
  have hL : 0 ≤ L := by dsimp [L, K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hmain : ∀ᶠ l : ℝ in atTop,
      Integrable (fun ω => ∫ x, |f x| *
        |Real.log (profileMass (Z l) (uvFineEntrance c ρ l)
          (uvObservation c ρ l) (gridHorizon c ρ wS l) x ω) -
         Real.log (profileMass (Z l) (uvCoarseEntrance c ρ q l)
          (uvObservation c ρ l) (gridHorizon c ρ wS l) x ω)|) P ∧
      Real.sqrt l * (∫ ω, ∫ x, |f x| *
        |Real.log (profileMass (Z l) (uvFineEntrance c ρ l)
          (uvObservation c ρ l) (gridHorizon c ρ wS l) x ω) -
         Real.log (profileMass (Z l) (uvCoarseEntrance c ρ q l)
          (uvObservation c ρ l) (gridHorizon c ρ wS l) x ω)| ∂volume ∂P) ≤
        (∫ x, |f x|) * profileLogDifferenceEnvelope Cc L D l := by
    filter_upwards [hcmp, hmom, hfObs, hcoObs,
      uvScales_horizon_order hc hρ' hq hq2,
      uvScales_horizon_order hc hρ' hwS hwS2,
      eventually_uvFineEntrance_lt_uvCoarseEntrance hc hρ' hq hq2,
      eventually_ge_atTop (Real.exp 1)]
      with l hcmp hmom hfObs hcoObs hord hordS hfa hl
    have hl0 : 0 < l := (Real.exp_pos 1).trans_le hl
    have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num : (0:ℝ)≤1)).trans hl
    have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1
    let a := uvFineEntrance c ρ l
    let m := uvCoarseEntrance c ρ q l
    let n := uvObservation c ρ l
    let S := gridHorizon c ρ wS l
    let A := fun x ω => profileMass (Z l) a n S x ω
    let B := fun x ω => profileMass (Z l) m n S x ω
    have ha0 : 0 < a := uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
      (zero_lt_one.trans hρ')
    have hm0 : 0 < m := (uvCoarseEntrance_bounds hc hρ' q l).1
    have han : a < n := hfa.trans hord.2.1
    have hmn : m < n := hord.2.1
    have hnS : n < S := hordS.2.2.1.trans hordS.2.2.2.1
    have hregA := profileMass_joint_regular (-l) P (Z l) (hZ l) ha0 han (han.trans hnS)
    have hregB := profileMass_joint_regular (-l) P (Z l) (hZ l) hm0 hmn (hmn.trans hnS)
    have hln : 0 < l - Real.log n := by
      have hn0 : 0 < n := uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
        (zero_lt_one.trans hρ')
      have hn1 : n < 1 := hord.2.2.1
      linarith [Real.log_neg hn0 hn1]
    have haN2 (x : Plane) :
        (∫ ω, shfPairing (Z l) a n (fun y => heatKernel a (y-x)) (fun _ => 1) ω^2 ∂P)
          ≤ 1 + Cpoly * l^39 := by
      exact (entrance_mass_second_moment_le l P (Z l) (hZ l) ha0 han hln hfObs x).2.trans
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (by dsimp only [Cpoly]; linarith) (by positivity)))
    have hmN2 (x : Plane) :
        (∫ ω, shfPairing (Z l) m n (fun y => heatKernel m (y-x)) (fun _ => 1) ω^2 ∂P)
          ≤ 1 + Cpoly * l^39 := by
      have hh := (entrance_mass_second_moment_le l P (Z l) (hZ l) hm0 hmn hln hcoObs x).2
      have hlog : Real.log l / l ≤ l^39 := by
        have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num)).trans hl
        have hlogle : Real.log l ≤ l := by
          linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hl1)]
        exact ((div_le_one (zero_lt_one.trans_le hl1)).2 hlogle).trans (one_le_pow₀ hl1)
      have hcob : Co * Real.log l / l ≤ Co * l ^ 39 := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hlog hCo.le
      exact hh.trans (add_le_add le_rfl (hcob.trans
        (mul_le_mul_of_nonneg_right (by dsimp only [Cpoly]; linarith) (pow_nonneg hl0.le 39))))
    have hlogdiv : Real.log l / l ≤ l^39 := by
      have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num)).trans hl
      have hlogle : Real.log l ≤ l := by
        linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hl1)]
      exact ((div_le_one (zero_lt_one.trans_le hl1)).2 hlogle).trans (one_le_pow₀ hl1)
    have haS2 (x : Plane) :
        (∫ ω, shfPairing (Z l) a S (fun y => heatKernel a (y-x)) (fun _ => 1) ω^2 ∂P)
          ≤ 1+Cpoly*l^39 :=
      (hmom x).2.2.2.2.2.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (by dsimp only [Cpoly]; linarith) (by positivity)))
    have hmS2 (x : Plane) :
        (∫ ω, shfPairing (Z l) m S (fun y => heatKernel m (y-x)) (fun _ => 1) ω^2 ∂P)
          ≤ 1+Cpoly*l^39 := by
      apply (hmom x).2.2.1.trans
      have hCSle : CS ≤ Cpoly := by dsimp only [Cpoly]; linarith
      have hh1 : CS * Real.log l / l ≤ CS * l ^ 39 := by
        simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hlogdiv hCS.le
      exact add_le_add le_rfl (hh1.trans
        (mul_le_mul_of_nonneg_right hCSle (pow_nonneg hl0.le 39)))
    have hi6 (x : Plane) :
        (∫ ω, (shfPairing (Z l) m S
          (fun y => heatKernel m (y-x)) (fun _ => 1) ω)⁻¹^6 ∂P) ≤ (1+CS)^21 := by
      apply (hmom x).2.2.2.2.1.trans
      have hlogle : Real.log l / l ≤ 1 := (div_le_one hl0).mpr (by
        linarith [Real.log_le_sub_one_of_pos hl0])
      have hb : 1 + CS * Real.log l / l ≤ 1 + CS := by
        have hh := mul_le_mul_of_nonneg_left hlogle hCS.le
        simpa only [mul_div_assoc, mul_one] using add_le_add le_rfl hh
      exact pow_le_pow_left₀ (by positivity) hb 21
    -- The four heat masses (fine/coarse, at n/S) now use the same envelope.
    -- `heatStartMass_log_ratio_memLp_four_of_poly_second` is applied twice,
    -- while `hmom` gives the inverse-third bound for `B`.
    have hAB := profileMass_pair_log_four_inverse_three_of_poly_second P hCpoly hl
      ha0 han (han.trans hnS) hm0 hmn (hmn.trans hnS) (Z l) (hZ l)
      haS2
      haN2
      hmS2
      hmN2
      (fun x => (hmom x).1)
      (fun x => (hmom x).2.1)
      (fun x => (hmom x).2.2.2.1)
      hi6
    have hcap (x : Plane) :
        let r := l ^ (-(5/8 : ℝ))
        (∫ ω, min |A x ω-B x ω| (r/2) ∂P) ≤
          Cc/(l*Real.sqrt l)+Cc*(r/2)/l := by
      intro r
      have hh := hcmp x (r/2) (by positivity) S (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr rfl)
      have he : l ^ (-(3 : ℝ) / 2) = 1 / (l * Real.sqrt l) := by
        rw [show -(3 : ℝ) / 2 = -(1 + 1 / 2) by norm_num, Real.rpow_neg hl0.le,
          Real.rpow_add hl0, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
      rw [he] at hh
      convert hh using 1; ring
    exact (spatial_profile_log_difference_scale_bound P
      hregA.1 hregB.1
      (fun x => aemeasurable_profileMass P (Z l) (hZ l) ha0 han (han.trans hnS) x)
      (fun x => aemeasurable_profileMass P (Z l) (hZ l) hm0 hmn (hmn.trans hnS) x)
      hregA.2.2 hregB.2.2
      (fun x => (hAB x).1) (fun x => (hAB x).2.1) hCc hL hD
      ((Real.one_le_exp (by norm_num)).trans hl)
      (fun x => (hAB x).2.2.1) (fun x => (hAB x).2.2.2.1)
      (fun x => (hAB x).2.2.2.2.1) (fun x => (hAB x).2.2.2.2.2)
      hcap hf hfi).2
  exact ⟨spatial_profile_log_difference_tendsto_zero P hCc hL hD hfi hmain,
    hmain.mono (fun _ h => h.1)⟩


/- Spatial linearisation of a heat-started logarithmic field. -/

theorem integral_heatMass_sub_one_eq_pairing_heatSmooth'
    (l : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T)
    (f : TestFn) (hf0 : (∫ x, f x) = 0) :
    (fun ω => ∫ x, f x *
      (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω - 1)) =ᵐ[P]
      fun ω => shfPairing Z a T (heatSmooth' a f) (fun _ => 1) ω := by
  have hfI : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have habsI : Integrable (fun x : Plane => |f x|) := hfI.abs
  have hsmoothI : Integrable (heatSmooth a (fun x : Plane => |f x|)) :=
    integrable_heatSmooth habsI ha
  have hsmoothM : Measurable (heatSmooth a (fun x : Plane => |f x|)) := by
    have hm : Measurable (fun p : Plane × Plane =>
        heatKernel a (p.1 - p.2) * |f p.2|) :=
      ((measurable_heatKernel a).comp (measurable_fst.sub measurable_snd)).mul
        (f.continuous.measurable.norm.comp measurable_snd)
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  have hpairAbs := integrable_shfPairing_one (-l) P Z hZ ha.le haT hsmoothM hsmoothI
  have hLF := (hZ.2.1 a T ha.le haT).mono fun _ h => h.1
  filter_upwards [hpairAbs.1, hLF] with ω hω hωLF
  let : IsLocallyFiniteMeasure (Z a T ω) := hωLF
  let F : (Plane × Plane) × Plane → ℝ := fun p =>
    f p.2 * heatKernel a (p.1.1 - p.2)
  have hFm : AEStronglyMeasurable F ((Z a T ω).prod volume) := by
    exact (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable.mul
      (((measurable_heatKernel a).comp
        ((measurable_fst.comp measurable_fst).sub measurable_snd)).aestronglyMeasurable)
  have hFI : Integrable F ((Z a T ω).prod volume) := by
    apply (integrable_prod_iff hFm).2
    refine ⟨?_, ?_⟩
    · filter_upwards with p
      simpa only [F, mul_comm] using integrable_heatSmooth_integrand hfI ha p.1
    · have heq : (fun p : Plane × Plane => ∫ x, ‖F (p, x)‖) =
          fun p => heatSmooth a (fun x : Plane => |f x|) p.1 := by
        funext p
        unfold F heatSmooth
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg ha.le _)]
        rw [mul_comm]
      rw [heq]
      exact hω
  have hswap := (integral_integral_swap (f := fun p x => F (p, x)) hFI).symm
  have hmassI : Integrable (fun x : Plane =>
      f x * ∫ p, heatKernel a (p.1 - x) ∂Z a T ω) := by
    apply hFI.integral_prod_right.congr
    filter_upwards [] with x
    dsimp only [F]
    rw [integral_const_mul]
  simp only [F, shfPairing, mul_one] at hswap ⊢
  simp_rw [mul_sub, mul_one]
  rw [integral_sub hmassI hfI, hf0, sub_zero]
  rw [show heatSmooth' a f = heatSmooth a f by simp [heatSmooth', ha.ne']]
  calc
    (∫ x, f x * ∫ p, heatKernel a (p.1 - x) ∂Z a T ω) =
        ∫ x, ∫ p, f x * heatKernel a (p.1 - x) ∂Z a T ω := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [integral_const_mul]
    _ = ∫ p : Plane × Plane, (∫ x, f x * heatKernel a (p.1 - x)) ∂Z a T ω := hswap
    _ = ∫ p, heatSmooth a f p.1 ∂Z a T ω := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold heatSmooth
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mul_comm]

theorem spatial_heat_mass_linearisation
    (l : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T v : ℝ} (ha : 0 < a) (haT : a < T) (hl : 0 < l - Real.log T)
    (hv : Real.log (T / a) / (l - Real.log T) ≤ v)
    (f : TestFn) (hf0 : (∫ x, f x) = 0) :
    Integrable (fun ω => |lField Z a T f ω -
      shfPairing Z a T (heatSmooth' a f) (fun _ => 1) ω|) P ∧
    (∫ ω, |lField Z a T f ω -
      shfPairing Z a T (heatSmooth' a f) (fun _ => 1) ω| ∂P) ≤
      (1 / 2 : ℝ) * (∫ x, |f x|) * Real.log (1 + v) := by
  let X : Ω → Plane → ℝ := fun ω x =>
    shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω
  let E : Ω → Plane → ℝ := fun ω x => |X ω x - 1 - Real.log (X ω x)|
  have hv0 : 0 ≤ v := by
    have hr0 : 0 ≤ Real.log (T / a) / (l - Real.log T) :=
      div_nonneg (Real.log_nonneg ((one_le_div ha).2 haT.le)) hl.le
    exact hr0.trans hv
  have hlogjoint : AEStronglyMeasurable (fun p : Ω × Plane => Real.log (X p.1 p.2))
      (P.prod volume) := by
    have h := JointConvergence.aemeasurable_shfLogField_joint (-l) P Z hZ
      a T a ha.le haT ha (0 : Plane →ᵇ ℝ)
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] at h
    exact (h.comp_quasiMeasurePreserving
      (Measure.measurePreserving_swap (μ := P) (ν := volume)).quasiMeasurePreserving).aestronglyMeasurable
  have hpos := profile_heatMass_ae_pos_semiconvex (-l) P Z hZ ha haT
  have hposProd := (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := (volume : Measure Plane))).ae hpos
  have hXjoint : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2)
      (P.prod volume) := by
    apply (Real.measurable_exp.comp_aemeasurable hlogjoint.aemeasurable).aestronglyMeasurable.congr
    filter_upwards [hposProd] with p hp
    dsimp only [X, Function.comp_def]
    rw [Real.exp_log (hp.1 p.2)]
  have hEjoint : AEStronglyMeasurable (fun p : Ω × Plane => E p.1 p.2)
      (P.prod volume) := by
    exact ((hXjoint.sub aestronglyMeasurable_const).sub hlogjoint).norm
  have hElin (x : Plane) := heat_mass_linearisation l P Z hZ ha haT hl hv x
  have hweighted := profile_weighted_nonneg_integral_bound P hEjoint
    (fun _ _ => abs_nonneg _) (fun x => (hElin x).1)
    (div_nonneg (Real.log_nonneg (by linarith : 1 ≤ 1 + v)) (by norm_num))
    (fun x => (hElin x).2.2) f.continuous.measurable
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
  have hid := integral_heatMass_sub_one_eq_pairing_heatSmooth' l P Z hZ ha haT f hf0
  have hdom : (fun ω => |lField Z a T f ω -
      shfPairing Z a T (heatSmooth' a f) (fun _ => 1) ω|) ≤ᵐ[P]
      fun ω => ∫ x, |f x| * E ω x := by
    have hlogI := (lField_integrable_joint (-l) P Z hZ T ha haT f).prod_left_ae
    have hXsec := hXjoint.prodMk_left
    filter_upwards [hid, hlogI, hweighted.1, hpos, hXsec]
      with ω hidω hlogω hEω hposω hXω
    have hlinI : Integrable (fun x => f x * (X ω x - 1)) := by
      apply (hEω.add hlogω.abs).mono'
        (f.continuous.measurable.aestronglyMeasurable.mul
          (hXω.sub aestronglyMeasurable_const))
      filter_upwards [] with x
      change |f x * (X ω x - 1)| ≤ |f x| * E ω x + |f x * Real.log (X ω x)|
      rw [abs_mul]
      calc
        |f x| * |X ω x - 1| ≤ |f x| *
            (|X ω x - 1 - Real.log (X ω x)| + |Real.log (X ω x)|) := by
          gcongr
          simpa only [sub_add_cancel] using
            abs_add_le (X ω x - 1 - Real.log (X ω x)) (Real.log (X ω x))
        _ = |f x| * E ω x + |f x * Real.log (X ω x)| := by
          dsimp only [E]
          rw [abs_mul]
          ring
    rw [← hidω]
    unfold lField
    rw [← integral_sub hlogω hlinI]
    exact (abs_integral_le_integral_abs).trans_eq (by
      apply integral_congr_ae
      filter_upwards [] with x
      change |f x * Real.log (X ω x) - f x * (X ω x - 1)| =
        |f x| * |X ω x - 1 - Real.log (X ω x)|
      rw [show f x * Real.log (X ω x) - f x * (X ω x - 1) =
        -(f x * (X ω x - 1 - Real.log (X ω x))) by ring, abs_neg, abs_mul])
  have hpairI : Integrable (shfPairing Z a T (heatSmooth' a f) (fun _ => 1)) P := by
    have hfI : Integrable (f : Plane → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    have hm : Measurable (heatSmooth' a f) := by simpa only [heatSmooth', ite_eq_right ha.ne'] using measurable_heatSmooth_testFn f a
    have hi : Integrable (heatSmooth' a f) := by simpa only [heatSmooth', ite_eq_right ha.ne'] using integrable_heatSmooth hfI ha
    exact (integrable_shfPairing_one (-l) P Z hZ ha.le haT hm hi).2
  have herrI : Integrable (fun ω => |lField Z a T f ω -
      shfPairing Z a T (heatSmooth' a f) (fun _ => 1) ω|) P :=
    ((lField_integrable (-l) P Z hZ T ha haT f).sub hpairI).abs
  refine ⟨herrI, ?_⟩
  calc
    _ ≤ (∫ ω, (∫ x, |f x| * E ω x) ∂P) := integral_mono_ae
      herrI hweighted.2.1 hdom
    _ ≤ (Real.log (1 + v) / 2) * ∫ x, |f x| := hweighted.2.2
    _ = _ := by ring

/-- An honest L1/Markov bridge.  The dominating random variables themselves
are required to be integrable; no totalized-integral shortcut is used. -/
theorem tendstoInMeasure_zero_of_ae_abs_le_integrable
    {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {u : Filter ι} {X Y : ι → Ω → ℝ}
    (hYi : ∀ᶠ i in u, Integrable (Y i) P)
    (hY0 : ∀ᶠ i in u, ∀ ω, 0 ≤ Y i ω)
    (hXY : ∀ᶠ i in u, ∀ᵐ ω ∂P, |X i ω| ≤ Y i ω)
    (hmean : Tendsto (fun i => ∫ ω, Y i ω ∂P) u (𝓝 0)) :
    TendstoInMeasure P X u (fun _ => 0) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hlim : Tendsto (fun i => ENNReal.ofReal ((∫ ω, Y i ω ∂P) / (ε / 2)))
      u (𝓝 0) := by
    simpa only [zero_div, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hmean.div_const (ε / 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [hYi, hY0, hXY] with i hi hnonneg hdom
  have hsub : ∀ᵐ ω ∂P, (ω ∈ {ω | ε ≤ ‖X i ω - 0‖}) →
      ω ∈ {ω | ε / 2 < Y i ω} := by
    filter_upwards [hdom] with ω hω hx
    simp only [sub_zero, Real.norm_eq_abs] at hx ⊢
    exact lt_of_lt_of_le (half_lt_self hε) (hx.trans hω)
  exact (measure_mono_ae hsub).trans
    (profile_measure_gt_le_of_integral P hi hnonneg (half_pos hε) le_rfl)

/-- The compare-futures conclusion at the UV scales.  The final horizon and
the coarse entrance are selected independently. -/
theorem compare_futures_at_uv_scales {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ qS qM : ℝ, 1 < ρ₀ ∧ 0 < qS ∧ qS < 1 / 2 ∧
      0 < qM ∧ qM < 1 / 2 ∧
      ∀ ρ, ρ₀ ≤ ρ → ∀ (hρ' : 1 < ρ),
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
      (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
      (f : TestFn) (_hfzero : (∫ x, f x) = 0),
      TendstoInMeasure P (fun l ω => Real.sqrt l *
        (kField (-l) P (Z l) (hZ l) (c * Real.exp l)
            (mul_pos hc (Real.exp_pos l)) f ω -
          kField (-l) P (Z l) (hZ l) (gridHorizon c ρ qS l)
            (gridHorizon_pos hc (zero_lt_one.trans hρ') qS l) f ω))
          atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun l ω => Real.sqrt l *
        (kField (-l) P (Z l) (hZ l) (gridHorizon c ρ qS l)
            (gridHorizon_pos hc (zero_lt_one.trans hρ') qS l) f ω -
          lField (Z l) (uvCoarseEntrance c ρ qM l)
            (gridHorizon c ρ qS l) f ω)) atTop (fun _ => 0) := by
  obtain ⟨ρS, qS, hρS, hqS, hqS2, hjoint⟩ :=
    stepOne_fine_entrance_and_localisation hc
  obtain ⟨ρP, qM, _hρP, hqM, hqM2, hlip⟩ := uv_profile_log_lipschitz_split hc
  refine ⟨max ρS ρP, qS, qM,
    hρS.trans_le (le_max_left _ _), hqS, hqS2, hqM, hqM2, ?_⟩
  intro ρ hρ hρ' Ω _ P _ Z hZ f hfzero
  have hρSle : ρS ≤ ρ := (le_max_left _ _).trans hρ
  have hρPle : ρP ≤ ρ := (le_max_right _ _).trans hρ
  let a : ℝ → ℝ := uvFineEntrance c ρ
  let m : ℝ → ℝ := uvCoarseEntrance c ρ qM
  let n : ℝ → ℝ := uvObservation c ρ
  let T : ℝ → ℝ := gridHorizon c ρ qS
  let KF : ℝ → Ω → ℝ := fun l =>
    kField (-l) P (Z l) (hZ l) (T l)
      (gridHorizon_pos hc (zero_lt_one.trans hρ') qS l) f
  let LA : ℝ → Ω → ℝ := fun l => lField (Z l) (a l) (T l) f
  let LM : ℝ → Ω → ℝ := fun l => lField (Z l) (m l) (T l) f
  let LA0 : ℝ → Ω → ℝ := fun l => lField (Z l) (a l) (n l) f
  let LM0 : ℝ → Ω → ℝ := fun l => lField (Z l) (m l) (n l) f
  let D : ℝ → Ω → ℝ := fun l ω => ∫ x, f x *
    (Real.log (profileMass (Z l) (a l) (n l) (T l) x ω) -
     Real.log (profileMass (Z l) (m l) (n l) (T l) x ω))
  have hJoint := hjoint ρ hρSle hρ' P Z hZ f hfzero
  have hHloc : TendstoInMeasure P (fun l ω => Real.sqrt l *
      (kField (-l) P (Z l) (hZ l) (c * Real.exp l)
          (mul_pos hc (Real.exp_pos l)) f ω - KF l ω))
      atTop (fun _ => 0) := by
    simpa only [KF, T, S] using hJoint.1
  have hStep : TendstoInMeasure P (fun l ω => Real.sqrt l * (KF l ω - LA l ω))
      atTop (fun _ => 0) := by
    simpa only [KF, LA, a, T, S] using hJoint.2
  refine ⟨hHloc, ?_⟩
  have hA2 := fine_interval_zero_observation_second_moment hc hρ' P Z hZ f hfzero
  have hM2 := coarse_interval_zero_observation_second_moment
    hc hρ' hqM hqM2 P Z hZ f hfzero
  obtain ⟨_, _, hfield⟩ := lField_second_moment_bound
  obtain ⟨B, hBraw⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hbound : ∀ x, |f x| ≤ B := by
    simpa only [Real.norm_eq_abs] using hBraw
  have hB0 : 0 ≤ B := (abs_nonneg (f 0)).trans (hbound 0)
  have hMem : ∀ᶠ l : ℝ in atTop,
      MemLp (fun ω => Real.sqrt l * LA0 l ω) 2 P ∧
      MemLp (fun ω => Real.sqrt l * LM0 l ω) 2 P := by
    filter_upwards [uvScales_horizon_order hc hρ' hqM hqM2,
      eventually_uvFineEntrance_lt_uvCoarseEntrance hc hρ' hqM hqM2,
      eventually_ge_atTop (Real.exp 1)] with l hordM ham hl
    have ha0 : 0 < a l := uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
      (zero_lt_one.trans hρ')
    have hm0 : 0 < m l := (uvCoarseEntrance_bounds hc hρ' qM l).1
    have han : a l < n l := ham.trans hordM.2.1
    have hclock : 0 < l - Real.log (n l) := by
      have hlog := Real.log_neg
        (uvGridPoint_pos (mul_pos hc (Real.exp_pos l)) (zero_lt_one.trans hρ'))
        hordM.2.2.1
      change Real.log (n l) < 0 at hlog
      linarith only [hlog, (Real.exp_pos 1).trans_le hl]
    exact ⟨(hfield l (a l) (n l) ha0 han hclock P (Z l) (hZ l)
        f B hB0 hbound hfzero).1.const_mul _,
      (hfield l (m l) (n l) hm0 hordM.2.1 hclock P (Z l) (hZ l)
        f B hB0 hbound hfzero).1.const_mul _⟩
  have hA : TendstoInMeasure P (fun l ω => Real.sqrt l * LA0 l ω)
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_zero_of_integral_sq_eventually (hMem.mono fun _ h => h.1)
    apply hA2.congr'
    filter_upwards [eventually_ge_atTop 0] with l hl
    simp only [LA0, a, n, mul_pow, integral_const_mul, Real.sq_sqrt hl]
  have hM : TendstoInMeasure P (fun l ω => -(Real.sqrt l * LM0 l ω))
      atTop (fun _ => 0) := by
    have hsquare : Tendsto (fun l => ∫ ω, (Real.sqrt l * LM0 l ω) ^ 2 ∂P)
        atTop (𝓝 0) := by
      apply hM2.congr'
      filter_upwards [eventually_ge_atTop 0] with l hl
      simp only [LM0, m, n, mul_pow, integral_const_mul, Real.sq_sqrt hl]
    have hh := tendstoInMeasure_zero_of_integral_sq_eventually
      (hMem.mono fun _ h => h.2) hsquare
    rw [tendstoInMeasure_iff_norm] at hh ⊢
    simpa only [sub_zero, Real.norm_eq_abs, abs_neg] using hh
  have hLip := hlip ρ hρPle qS hqS hqS2 P Z hZ f
    f.continuous.measurable (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
  let Y : ℝ → Ω → ℝ := fun l ω => Real.sqrt l * ∫ x, |f x| *
    |Real.log (profileMass (Z l) (a l) (n l) (T l) x ω) -
     Real.log (profileMass (Z l) (m l) (n l) (T l) x ω)|
  have hProf : TendstoInMeasure P (fun l ω => Real.sqrt l * D l ω)
      atTop (fun _ => 0) := by
    apply tendstoInMeasure_zero_of_ae_abs_le_integrable (Y := Y)
      (hLip.2.and (eventually_ge_atTop 0) |>.mono fun l hl => hl.1.const_mul _)
      ((eventually_ge_atTop 0).mono fun l hl ω => by
        dsimp only [Y]; positivity)
    · filter_upwards [uvScales_horizon_order hc hρ' hqM hqM2,
        uvScales_horizon_order hc hρ' hqS hqS2,
        eventually_uvFineEntrance_lt_uvCoarseEntrance hc hρ' hqM hqM2,
        eventually_ge_atTop 0] with l hordM hordS ham hl
      have ha0 : 0 < a l := uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
        (zero_lt_one.trans hρ')
      have hm0 : 0 < m l := (uvCoarseEntrance_bounds hc hρ' qM l).1
      have han : a l < n l := ham.trans hordM.2.1
      have hnT : n l < T l := hordS.2.2.1.trans hordS.2.2.2.1
      have hfa := flow_decomposition (-l) P (Z l) (hZ l)
        ha0 han (han.trans hnT) f.continuous.measurable
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
      have hfm := flow_decomposition (-l) P (Z l) (hZ l)
        hm0 hordM.2.1 (hordM.2.1.trans hnT) f.continuous.measurable
        (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
      filter_upwards [hfa, hfm] with ω hfa hfm
      dsimp only [D, Y]
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      calc
        |∫ x, f x * (Real.log (profileMass (Z l) (a l) (n l) (T l) x ω) -
          Real.log (profileMass (Z l) (m l) (n l) (T l) x ω))| ≤
            ∫ x, |f x * (Real.log (profileMass (Z l) (a l) (n l) (T l) x ω) -
              Real.log (profileMass (Z l) (m l) (n l) (T l) x ω))| :=
          abs_integral_le_integral_abs
        _ = _ := by congr 1; funext x; rw [abs_mul]
    · simpa only [Y, integral_const_mul] using hLip.1
  have hsum := tendstoInMeasure_add_zero_real hStep
    (tendstoInMeasure_add_zero_real hA
      (tendstoInMeasure_add_zero_real hM hProf))
  apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hsum
  filter_upwards [uvScales_horizon_order hc hρ' hqM hqM2,
    uvScales_horizon_order hc hρ' hqS hqS2,
    eventually_uvFineEntrance_lt_uvCoarseEntrance hc hρ' hqM hqM2]
      with l hordM hordS ham
  have ha0 : 0 < a l := uvGridPoint_pos (mul_pos hc (Real.exp_pos l))
    (zero_lt_one.trans hρ')
  have hm0 : 0 < m l := (uvCoarseEntrance_bounds hc hρ' qM l).1
  have han : a l < n l := ham.trans hordM.2.1
  have hnT : n l < T l := hordS.2.2.1.trans hordS.2.2.2.1
  have hfa := flow_decomposition (-l) P (Z l) (hZ l)
    ha0 han (han.trans hnT) f.continuous.measurable
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
  have hfm := flow_decomposition (-l) P (Z l) (hZ l)
    hm0 hordM.2.1 (hordM.2.1.trans hnT) f.continuous.measurable
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
  filter_upwards [hfa, hfm] with ω hfa hfm
  dsimp only [KF, LA, LM, LA0, LM0, D, a, m, n, T]
  simp_rw [mul_sub]
  rw [integral_sub hfa.1 hfm.1]
  rw [← hfa.2, ← hfm.2]
  dsimp only [lField, a, m, n, T]
  ring


/-- At the selected coarse entrance, the logarithmic field and its linear
heat-mass observable differ by `o(l⁻¹/²)` in L1 and hence in probability. -/
theorem uv_coarse_linearisation_tendstoInMeasure
    {c ρ qM qS : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hqM : 0 < qM) (hqM2 : qM < 1 / 2)
    (hqS : 0 < qS) (hqS2 : qS < 1 / 2)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : TestFn) (hf0 : (∫ x, f x) = 0) :
    TendstoInMeasure P (fun l ω => Real.sqrt l *
      (lField (Z l) (uvCoarseEntrance c ρ qM l) (gridHorizon c ρ qS l) f ω -
       shfPairing (Z l) (uvCoarseEntrance c ρ qM l) (gridHorizon c ρ qS l)
         (heatSmooth' (uvCoarseEntrance c ρ qM l) f) (fun _ => 1) ω))
      atTop (fun _ => 0) := by
  obtain ⟨C, hC, hratio⟩ := uvCoarse_independentHorizon_ratio_le
    hc hρ hqM hqM2 hqS hqS2
  obtain ⟨d, _, hgrid⟩ := grid_properties hc hρ hqS hqS2
  let E : ℝ → Ω → ℝ := fun l ω => Real.sqrt l *
    |lField (Z l) (uvCoarseEntrance c ρ qM l) (gridHorizon c ρ qS l) f ω -
     shfPairing (Z l) (uvCoarseEntrance c ρ qM l) (gridHorizon c ρ qS l)
       (heatSmooth' (uvCoarseEntrance c ρ qM l) f) (fun _ => 1) ω|
  have hrate : Tendsto (fun l : ℝ =>
      ((1 / 2 : ℝ) * (∫ x, |f x|) * C) * (Real.log l / Real.sqrt l))
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa only [id_eq, Real.rpow_one, ← Real.sqrt_eq_rpow, mul_zero, mul_div_assoc] using
      h.const_mul ((1 / 2 : ℝ) * (∫ x, |f x|) * C)
  have hEint : ∀ᶠ l : ℝ in atTop, Integrable (E l) P := by
    filter_upwards [hratio, hgrid, eventually_mul_log_add_le_half d 0,
      uvScales_horizon_order hc hρ hqS hqS2, eventually_gt_atTop 0]
      with l hratio hgrid hpoly hord hl
    have hm0 := (uvCoarseEntrance_bounds hc hρ qM l).1
    have hS0 := gridHorizon_pos hc (zero_lt_one.trans hρ) qS l
    have hmS : uvCoarseEntrance c ρ qM l < gridHorizon c ρ qS l :=
      (uvCoarseEntrance_bounds hc hρ qM l).2.trans_lt
        (hord.2.2.1.trans hord.2.2.2.1)
    have hlogS := Real.log_le_log hS0 hgrid.2.2.2.1
    rw [Real.log_rpow hl] at hlogS
    have hclock : 0 < l - Real.log (gridHorizon c ρ qS l) := by linarith
    exact (spatial_heat_mass_linearisation l P (Z l) (hZ l)
      hm0 hmS hclock hratio f hf0).1.const_mul _
  have hEmean : Tendsto (fun l => ∫ ω, E l ω ∂P) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hrate
    · filter_upwards [eventually_ge_atTop 0] with l hl
      exact integral_nonneg fun ω => by dsimp only [E]; positivity
    · filter_upwards [hratio, hgrid, eventually_mul_log_add_le_half d 0,
        uvScales_horizon_order hc hρ hqS hqS2, eventually_ge_atTop (Real.exp 1)]
        with l hratio hgrid hpoly hord hl
      have hl0 : 0 < l := (Real.exp_pos 1).trans_le hl
      have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num)).trans hl
      have hm0 := (uvCoarseEntrance_bounds hc hρ qM l).1
      have hS0 := gridHorizon_pos hc (zero_lt_one.trans hρ) qS l
      have hmS : uvCoarseEntrance c ρ qM l < gridHorizon c ρ qS l :=
        (uvCoarseEntrance_bounds hc hρ qM l).2.trans_lt
          (hord.2.2.1.trans hord.2.2.2.1)
      have hlogS := Real.log_le_log hS0 hgrid.2.2.2.1
      rw [Real.log_rpow hl0] at hlogS
      have hclock : 0 < l - Real.log (gridHorizon c ρ qS l) := by linarith
      have hlin := spatial_heat_mass_linearisation l P (Z l) (hZ l)
        hm0 hmS hclock hratio f hf0
      rw [show (∫ ω, E l ω ∂P) = Real.sqrt l *
          ∫ ω, |lField (Z l) (uvCoarseEntrance c ρ qM l)
            (gridHorizon c ρ qS l) f ω -
          shfPairing (Z l) (uvCoarseEntrance c ρ qM l)
            (gridHorizon c ρ qS l)
            (heatSmooth' (uvCoarseEntrance c ρ qM l) f) (fun _ => 1) ω| ∂P by
        simp only [E, integral_const_mul]]
      calc
        _ ≤ Real.sqrt l * ((1 / 2 : ℝ) * (∫ x, |f x|) *
            Real.log (1 + C * Real.log l / l)) :=
          mul_le_mul_of_nonneg_left hlin.2 (Real.sqrt_nonneg _)
        _ ≤ Real.sqrt l * ((1 / 2 : ℝ) * (∫ x, |f x|) *
            (C * Real.log l / l)) := by
          have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1
          have hlogle : Real.log (1 + C * Real.log l / l) ≤ C * Real.log l / l := by
            simpa only [add_sub_cancel_left] using
              Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + C * Real.log l / l)
          have hbase : 0 ≤ Real.sqrt l * ((1 / 2 : ℝ) * (∫ x, |f x|)) := by
            positivity
          calc
            _ = (Real.sqrt l * ((1 / 2 : ℝ) * (∫ x, |f x|))) *
                Real.log (1 + C * Real.log l / l) := by ring
            _ ≤ (Real.sqrt l * ((1 / 2 : ℝ) * (∫ x, |f x|))) *
                (C * Real.log l / l) := mul_le_mul_of_nonneg_left hlogle hbase
            _ = _ := by ring
        _ = ((1 / 2 : ℝ) * (∫ x, |f x|) * C) *
            (Real.log l / Real.sqrt l) := by
          have hsqrt : 0 < Real.sqrt l := Real.sqrt_pos.2 hl0
          field_simp [hl0.ne', hsqrt.ne']
          rw [Real.sq_sqrt hl0.le]
          ring
  apply tendstoInMeasure_zero_of_ae_abs_le_integrable
    hEint
    ((eventually_ge_atTop 0).mono fun l hl ω => by dsimp only [E]; positivity)
  · filter_upwards [eventually_ge_atTop 0] with l hl
    filter_upwards with ω
    dsimp only [E]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  · exact hEmean

/-- Proposition UV with a common horizon selected before the test function.
It returns both the common-horizon and full-horizon approximations. -/
theorem prop_uv {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ qS qM : ℝ, 1 < ρ₀ ∧ 0 < qS ∧ qS < 1 / 2 ∧
      0 < qM ∧ qM < 1 / 2 ∧
      ∀ ρ, ρ₀ ≤ ρ → ∀ (hρ : 1 < ρ),
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
      (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
      (f : TestFn) (_hf0 : (∫ x, f x) = 0),
      let A := fun l ω => shfPairing (Z l) (uvCoarseEntrance c ρ qM l)
        (gridHorizon c ρ qS l) (heatSmooth' (uvCoarseEntrance c ρ qM l) f)
        (fun _ => 1) ω
      TendstoInMeasure P (fun l ω => Real.sqrt l *
        (kField (-l) P (Z l) (hZ l) (gridHorizon c ρ qS l)
          (gridHorizon_pos hc (zero_lt_one.trans hρ) qS l) f ω - A l ω))
        atTop (fun _ => 0) ∧
      TendstoInMeasure P (fun l ω => Real.sqrt l *
        (kField (-l) P (Z l) (hZ l) (c * Real.exp l)
          (mul_pos hc (Real.exp_pos l)) f ω - A l ω))
        atTop (fun _ => 0) := by
  obtain ⟨ρ₀, qS, qM, hρ₀, hqS, hqS2, hqM, hqM2, hcompare⟩ :=
    compare_futures_at_uv_scales hc
  refine ⟨ρ₀, qS, qM, hρ₀, hqS, hqS2, hqM, hqM2, ?_⟩
  intro ρ hρle hρ Ω _ P _ Z hZ f hf0
  dsimp only
  have hcmp := hcompare ρ hρle hρ P Z hZ f hf0
  have hlin := uv_coarse_linearisation_tendstoInMeasure
    hc hρ hqM hqM2 hqS hqS2 P Z hZ f hf0
  have hKS := tendstoInMeasure_add_zero_real hcmp.2 hlin
  have hFull := tendstoInMeasure_add_zero_real hcmp.1 hKS
  constructor
  · apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hKS
    filter_upwards with l
    filter_upwards with ω
    ring
  · apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hFull
    filter_upwards with l
    filter_upwards with ω
    ring


end Critical2DKPZ.Extensions.GffTangent
