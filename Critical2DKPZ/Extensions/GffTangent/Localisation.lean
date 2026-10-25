/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.Semiconvexity
public import Critical2DKPZ.Extensions.GffTangent.LogMomentsProfile
public import Critical2DKPZ.Extensions.GffTangent.Locality
public import Critical2DKPZ.Definitions.TestFn
import Critical2DKPZ.Extensions.GffTangent.LogKernelIdentities
import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence

/-! # Localisation of the mean-zero GFF observables in time -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BoundedContinuousFunction BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- A second-moment bound valid at every horizon, including horizons for
which `l-log T` need not be positive. -/
theorem profile_heatMass_secondMoment_le_log (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) (x : Plane) :
    (∫ ω, (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω) ^ 2 ∂P) ≤
      1 + uFun l T * Real.log (T / a) := by
  let F := fun u : ℝ => u⁻¹ * uFun l (T - u)
  let H := fun u : ℝ => u⁻¹ * uFun l T
  have hi : IntegrableOn (fun u : ℝ => u⁻¹) (Icc a T) :=
    (continuousOn_id.inv₀ (fun u hu => (ha.trans_le hu.1).ne')).integrableOn_Icc
  have hHi : IntegrableOn H (Ioc a T) := (hi.mono_set Ioc_subset_Icc_self).mul_const _
  have hFm : Measurable F := measurable_inv.mul
    (measurable_uFun.comp (measurable_const.prodMk (measurable_const.sub measurable_id)))
  have hF0 (u : ℝ) (hu : u ∈ Ioo a T) : 0 ≤ F u :=
    mul_nonneg (inv_nonneg.mpr (ha.trans hu.1).le) (uFun_nonneg _ _)
  have hFH (u : ℝ) (hu : u ∈ Ioo a T) : F u ≤ H u :=
    mul_le_mul_of_nonneg_left (uFun_mono (sub_pos.mpr hu.2)
      (sub_le_self T (ha.trans hu.1).le)) (inv_nonneg.mpr (ha.trans hu.1).le)
  have hFi : IntegrableOn F (Ioo a T) := by
    apply (hHi.mono_set Ioo_subset_Ioc_self).mono' hFm.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 u hu)]
    exact hFH u hu
  have hInt : (∫ u in Ioc a T, F u) ≤ uFun l T * Real.log (T / a) := by
    rw [integral_Ioc_eq_integral_Ioo]
    calc
      _ ≤ ∫ u in Ioo a T, H u := integral_mono_ae hFi (hHi.mono_set Ioo_subset_Ioc_self)
        ((ae_restrict_mem measurableSet_Ioo).mono fun u hu => hFH u hu)
      _ = _ := by
        dsimp only [H]
        rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le haT.le, integral_inv_of_pos ha (ha.trans haT)]
        ring
  have hcov := heatMass_covariance_formula l P Z hZ ha haT x x
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), neg_zero, zero_div,
    Real.exp_zero, mul_one] at hcov
  have hX := heatStartMass_memLp_two (-l) P Z hZ ha haT x
  rw [covariance_eq_sub hX hX] at hcov
  simp only [Pi.mul_apply, ← pow_two] at hcov
  rw [(heatStartMass_integral_eq_one (-l) P Z hZ ha haT x).2] at hcov
  change (∫ ω, _ ∂P) - 1 ^ 2 = ∫ u in Ioc a T, F u at hcov
  linarith only [hcov, hInt]

/-- Scaling identifies the long-horizon renewal factor with a fixed constant. -/
theorem profile_uFun_exponential_horizon {c : ℝ} (hc : 0 < c) (l : ℝ) :
    uFun l (c * Real.exp l) = uFun (-Real.log c) 1 := by
  unfold uFun
  rw [Real.log_mul hc.ne' (Real.exp_pos l).ne', Real.log_exp, Real.log_one]
  congr 1
  funext z
  congr 1
  ring_nf

/-- The long-horizon heat-start second moment grows at most linearly in
`l`, uniformly over all entrances at least `l²`. -/
theorem profile_heatMass_long_secondMoment {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ a : ℝ, l ^ 2 ≤ a → a < c * Real.exp l → ∀ x : Plane,
        (∫ ω, (shfPairing Z a (c * Real.exp l)
          (fun y => heatKernel a (y - x)) (fun _ => 1) ω) ^ 2 ∂P) ≤ C * l := by
  let U := uFun (-Real.log c) 1
  have hU : 0 ≤ U := uFun_nonneg _ _
  refine ⟨1 + 2 * U, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop |Real.log c|] with l hl1 hlc
  intro Ω _ P _ Z hZ a hla haH x
  have ha1 : 1 ≤ a := (one_le_pow₀ hl1).trans hla
  have ha : 0 < a := by linarith
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  have hlog : Real.log (c * Real.exp l / a) ≤ 2 * l := by
    calc
      _ ≤ Real.log (c * Real.exp l) := Real.log_le_log (div_pos hH ha)
        ((div_le_iff₀ ha).mpr (le_mul_of_one_le_right hH.le ha1))
      _ = Real.log c + l := by rw [Real.log_mul hc.ne' (Real.exp_pos l).ne', Real.log_exp]
      _ ≤ 2 * l := by linarith only [hlc, le_abs_self (Real.log c)]
  have h := profile_heatMass_secondMoment_le_log l P Z hZ ha haH x
  rw [profile_uFun_exponential_horizon hc] at h
  change _ ≤ 1 + U * Real.log (c * Real.exp l / a) at h
  nlinarith only [h, mul_le_mul_of_nonneg_left hlog hU, hl1]

/-- At the polynomial horizon the excess heat-start second moment is
`O(log l/l)`, uniformly for entrances at least `l²`. -/
theorem profile_heatMass_short_secondMoment {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ a : ℝ, l ^ 2 ≤ a → a < S c ρ w l → ∀ x : Plane,
        (∫ ω, (shfPairing Z a (S c ρ w l)
          (fun y => heatKernel a (y - x)) (fun _ => 1) ω) ^ 2 ∂P) ≤
            1 + C * Real.log l / l := by
  obtain ⟨d, hd, hgrid⟩ := grid_properties hc hρ hw hwHalf
  refine ⟨2 * d, by linarith, ?_⟩
  filter_upwards [hgrid, eventually_mul_log_add_le_half d 0,
    eventually_ge_atTop (1 : ℝ)] with l hgrid hsmall hl1
  intro Ω _ P _ Z hZ a hla haS x
  have hl : 0 < l := by linarith
  have ha1 : 1 ≤ a := (one_le_pow₀ hl1).trans hla
  have ha : 0 < a := by linarith
  have hS : 0 < S c ρ w l := gridHorizon_pos hc (zero_lt_one.trans hρ) w l
  have hlogS : Real.log (S c ρ w l) ≤ d * Real.log l := by
    calc
      _ ≤ Real.log (l ^ d) := Real.log_le_log hS hgrid.2.2.2.1
      _ = _ := Real.log_rpow hl d
  have hgap : l / 2 ≤ l - Real.log (S c ρ w l) := by linarith only [hsmall, hlogS]
  have hgap0 : 0 < l - Real.log (S c ρ w l) := (half_pos hl).trans_le hgap
  have hlogratio : Real.log (S c ρ w l / a) ≤ d * Real.log l := by
    exact (Real.log_le_log (div_pos hS ha)
      ((div_le_iff₀ ha).mpr (le_mul_of_one_le_right hS.le ha1))).trans hlogS
  have hnum : 0 ≤ d * Real.log l := mul_nonneg (by linarith) (Real.log_nonneg hl1)
  have hdiv : Real.log (S c ρ w l / a) / (l - Real.log (S c ρ w l)) ≤
      2 * d * Real.log l / l := by
    calc
      _ ≤ (d * Real.log l) / (l - Real.log (S c ρ w l)) :=
        div_le_div_of_nonneg_right hlogratio hgap0.le
      _ ≤ (d * Real.log l) / (l / 2) :=
        div_le_div_of_nonneg_left hnum (half_pos hl) hgap
      _ = _ := by ring
  exact (massCovariance_formula_and_bound l P Z hZ ha haS hgap0 x x).2.2.trans
    (add_le_add le_rfl hdiv)

/-- A mean-one heat-start mass has second moment at least one. -/
theorem profile_heatMass_secondMoment_ge_one (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) (x : Plane) :
    1 ≤ ∫ ω, (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω) ^ 2 ∂P := by
  have hX := heatStartMass_memLp_two ϑ P Z hZ ha haT x
  have h := variance_nonneg (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1)) P
  rw [variance_eq_sub hX] at h
  simp only [Pi.pow_apply, (heatStartMass_integral_eq_one ϑ P Z hZ ha haT x).2, one_pow] at h
  linarith only [h]

/-- The logarithmic variance at either delayed future horizon is `O(log l)`. -/
theorem profile_delayed_log_variance {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ T : ℝ, T = S c ρ w l ∨ T = c * Real.exp l → ∀ x : Plane,
        variance (fun ω => Real.log (shfPairing Z (gridPoint c ρ l) T
          (fun y => heatKernel (gridPoint c ρ l) (y - x)) (fun _ => 1) ω)) P ≤ C * Real.log l := by
  obtain ⟨Cl, hCl, hLong⟩ := profile_heatMass_long_secondMoment hc
  obtain ⟨Cs, hCs, hShort⟩ := profile_heatMass_short_secondMoment hc hρ hw hwHalf
  have hlogC : 0 ≤ Real.log Cl := Real.log_nonneg hCl
  refine ⟨Real.log Cl + 1 + Cs, by linarith, ?_⟩
  filter_upwards [hLong, hShort, eventually_grid_time_order hc hρ hw hwHalf,
    eventually_ge_atTop (Real.exp 1)] with l hLong hShort htimes hlExp
  intro Ω _ P _ Z hZ T hT x
  have hl : 1 ≤ l := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hlExp
  have hlogl : 1 ≤ Real.log l := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hlExp
  have ha := htimes.1
  have haS := htimes.2.1
  have haH := haS.trans htimes.2.2.1
  have hla := htimes.2.2.2
  rcases hT with rfl | rfl
  · have hMom := hShort P Z hZ _ hla haS x
    have hVar := (heatStartMass_convexity_moments (-l) P Z hZ ha haS x).2.2.2.1
    have hOne := profile_heatMass_secondMoment_ge_one (-l) P Z hZ ha haS x
    have hLog := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hOne)
    have hdiv : Cs * Real.log l / l ≤ Cs * Real.log l :=
      (div_le_iff₀ (zero_lt_one.trans_le hl)).mpr
        (le_mul_of_one_le_right (mul_nonneg hCs (by linarith)) hl)
    nlinarith only [hVar, hLog, hMom, hdiv,
      mul_nonneg (add_nonneg hlogC zero_le_one) (by linarith : 0 ≤ Real.log l)]
  · have hMom := hLong P Z hZ _ hla haH x
    have hVar := (heatStartMass_convexity_moments (-l) P Z hZ ha haH x).2.2.2.1
    have hOne := profile_heatMass_secondMoment_ge_one (-l) P Z hZ ha haH x
    have hLog := Real.log_le_log (zero_lt_one.trans_le hOne) hMom
    rw [Real.log_mul (by linarith : Cl ≠ 0) (by linarith : l ≠ 0)] at hLog
    nlinarith only [hVar, hLog, mul_le_mul_of_nonneg_left hlogl hlogC,
      mul_nonneg hCs (by linarith : 0 ≤ Real.log l)]

/-- The flow decomposition is an identity of integrable spatial log
pairings; the ratio itself is defined by the two heat-started masses. -/
theorem flow_decomposition (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a n T : ℝ} (ha : 0 < a) (han : a < n) (haT : a < T)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f) :
    ∀ᵐ ω ∂P, Integrable (fun x => f x * Real.log (profileMass Z a n T x ω)) ∧
      (∫ x, f x * Real.log (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) -
      (∫ x, f x * Real.log (shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) =
        ∫ x, f x * Real.log (profileMass Z a n T x ω) := by
  filter_upwards [(profile_heatMass_test_integrable ϑ P Z hZ ha haT hf hfi).1,
    (profile_heatMass_test_integrable ϑ P Z hZ ha han hf hfi).1,
    profile_heatMass_ae_pos_semiconvex ϑ P Z hZ ha haT,
    profile_heatMass_ae_pos_semiconvex ϑ P Z hZ ha han] with ω hT hn hpT hpn
  have heq : (fun x => f x * Real.log (profileMass Z a n T x ω)) =
      fun x => f x * Real.log (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω) -
        f x * Real.log (shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1) ω) := by
    funext x
    rw [profileMass, Real.log_div (hpT.1 x).ne' (hpn.1 x).ne', mul_sub]
  rw [heq]
  exact ⟨hT.sub hn, (integral_sub hT hn).symm⟩

/-- The mean-zero log-ratio estimate follows from semiconvexity at its two
future horizons, with all field regularity supplied by the SHF lemmas. -/
theorem profile_l2_integral_log_ratio_le (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a n T σ : ℝ} (ha : 0 < a) (han : a < n) (haT : a < T) (hσ : 0 ≤ σ)
    (hvarn : variance (fun ω => Real.log
      (shfPairing Z a n (fun y => heatKernel a (y - 0)) (fun _ => 1) ω)) P ≤ σ ^ 2)
    (hvarT : variance (fun ω => Real.log
      (shfPairing Z a T (fun y => heatKernel a (y - 0)) (fun _ => 1) ω)) P ≤ σ ^ 2)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f)
    (hfw : Integrable (fun x => ‖x‖ * |f x|)) (hfzero : ∫ x, f x = 0) :
    eLpNorm (fun ω => ∫ x, f x * Real.log (profileMass Z a n T x ω)) 2 P ≤
      ENNReal.ofReal ((8 * Real.sqrt σ / Real.sqrt a) * ∫ x, ‖x‖ * |f x|) := by
  have hn := profile_heatMass_l2_integral_bound ϑ P Z hZ ha han hσ hvarn hf hfi hfw hfzero
  have hT := profile_heatMass_l2_integral_bound ϑ P Z hZ ha haT hσ hvarT hf hfi hfw hfzero
  have heq : (fun ω => ∫ x, f x * Real.log (profileMass Z a n T x ω)) =ᵐ[P]
      fun ω => (∫ x, f x * Real.log (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) -
        (∫ x, f x * Real.log (shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) :=
    (flow_decomposition ϑ P Z hZ ha han haT hf hfi).mono (fun _ h => h.2.symm)
  rw [eLpNorm_congr_ae heq]
  have hnonneg : 0 ≤ (4 * Real.sqrt σ / Real.sqrt a) * ∫ x, ‖x‖ * |f x| := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun x => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  calc
    _ ≤ _ + _ := eLpNorm_sub_le (by norm_num)
    _ ≤ ENNReal.ofReal ((4 * Real.sqrt σ / Real.sqrt a) * ∫ x, ‖x‖ * |f x|) +
        ENNReal.ofReal ((4 * Real.sqrt σ / Real.sqrt a) * ∫ x, ‖x‖ * |f x|) := add_le_add hT hn
    _ = _ := by rw [← ENNReal.ofReal_add hnonneg hnonneg]; congr 1; ring

/-- The delayed profile ratio has the mean-zero spatial `L²` bound from
Proposition 6.4, with the source rate `(log l)^(1/4)/l`. -/
theorem l2_integral_log_delayedRatio_le {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2)
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f)
    (hfw : Integrable (fun x => ‖x‖ * |f x|)) (hfzero : ∫ x, f x = 0) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
        MemLp (fun ω => ∫ x, f x * Real.log (profileMass Z (gridPoint c ρ l)
          (S c ρ w l) (c * Real.exp l) x ω)) 2 P ∧
        eLpNorm (fun ω => ∫ x, f x * Real.log (profileMass Z (gridPoint c ρ l)
          (S c ρ w l) (c * Real.exp l) x ω)) 2 P ≤
            ENNReal.ofReal (Cf * (Real.log l) ^ (1 / 4 : ℝ) / l) := by
  obtain ⟨V, hV, hVar⟩ := profile_delayed_log_variance hc hρ hw hwHalf
  let M := ∫ x, ‖x‖ * |f x|
  have hM : 0 ≤ M := integral_nonneg fun x => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hV0 : 0 ≤ V := by linarith
  refine ⟨8 * Real.sqrt (Real.sqrt V) * M, by positivity, ?_⟩
  filter_upwards [hVar, eventually_grid_time_order hc hρ hw hwHalf,
    eventually_ge_atTop (1 : ℝ)] with l hVar htimes hl1
  intro Ω _ P _ Z hZ
  have hl : 0 < l := by linarith
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1
  let σ := Real.sqrt (V * Real.log l)
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hσsq : σ ^ 2 = V * Real.log l := Real.sq_sqrt (mul_nonneg hV0 hlogl)
  have hn := hVar P Z hZ (S c ρ w l) (Or.inl rfl) 0
  have hT := hVar P Z hZ (c * Real.exp l) (Or.inr rfl) 0
  rw [← hσsq] at hn hT
  have hnorm := profile_l2_integral_log_ratio_le (-l) P Z hZ htimes.1 htimes.2.1
    (htimes.2.1.trans htimes.2.2.1) hσ hn hT hf hfi hfw hfzero
  have hden : l ≤ Real.sqrt (gridPoint c ρ l) :=
    (Real.le_sqrt hl.le htimes.1.le).mpr htimes.2.2.2
  have hquarter : Real.sqrt (Real.sqrt (Real.log l)) = (Real.log l) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hlogl]
    norm_num
  have hσroot : Real.sqrt σ = Real.sqrt (Real.sqrt V) * (Real.log l) ^ (1 / 4 : ℝ) := by
    dsimp only [σ]
    rw [Real.sqrt_mul hV0, Real.sqrt_mul (Real.sqrt_nonneg V), hquarter]
  have hbound : (8 * Real.sqrt σ / Real.sqrt (gridPoint c ρ l)) * M ≤
      (8 * Real.sqrt (Real.sqrt V) * M) * (Real.log l) ^ (1 / 4 : ℝ) / l := by
    calc
      _ ≤ (8 * Real.sqrt σ / l) * M := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (by positivity) hl hden) hM
      _ = _ := by rw [hσroot]; ring
  have hnorm' := hnorm.trans (ENNReal.ofReal_le_ofReal hbound)
  exact ⟨hnorm'.trans_lt ENNReal.ofReal_lt_top, hnorm'⟩

/-- A union bound over a fixed finite set of evaluations. -/
theorem profile_measure_exists_finite_le {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (s : ι → Set Ω) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i, P (s i) ≤ ENNReal.ofReal B) :
    P {ω | ∃ i, ω ∈ s i} ≤ ENNReal.ofReal ((Fintype.card ι : ℝ) * B) := by
  classical
  have heq : {ω | ∃ i, ω ∈ s i} = ⋃ i, s i := by ext ω; simp only [mem_iUnion, mem_ofPred_eq]
  rw [heq]
  calc
    _ ≤ ∑ i, P (s i) := measure_iUnion_fintype_le P s
    _ ≤ ∑ _i : ι, ENNReal.ofReal B := Finset.sum_le_sum (fun i _ => hbound i)
    _ = _ := by rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB)]; simp

/-- Quantitative lower-tail control for the delayed ratio on a fixed square.
The finite-dimensional good event is supplied by Chebyshev, rather than assumed. -/
theorem profile_delayedRatio_lower_tail {c ρ w R : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
        P {ω | ∃ x : Plane, (∀ i : Fin 2, |x i| ≤ R) ∧
          profileMass Z (gridPoint c ρ l) (S c ρ w l) (c * Real.exp l) x ω < l ^ (-(5 / 8 : ℝ))} ≤
            ENNReal.ofReal (C / Real.log l + C * Real.log l / l) := by
  obtain ⟨Cl, hCl, hLong⟩ := profile_heatMass_long_secondMoment hc
  obtain ⟨Cs, hCs, hShort⟩ := profile_heatMass_short_secondMoment hc hρ hw hwHalf
  obtain ⟨V, hV, hVar⟩ := profile_delayed_log_variance hc hρ hw hwHalf
  let C := 20480 * V + 4 * Cs
  have hV0 : 0 ≤ V := by linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hLong, hShort, hVar, eventually_grid_time_order hc hρ hw hwHalf,
    eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (32 * Real.log Cl)),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (16 * (4 * R ^ 2 + Real.log 2)))]
    with l hLong hShort hVar htimes hl1 hscale hroom
  intro Ω _ P _ Z hZ
  let a := gridPoint c ρ l
  let n := S c ρ w l
  let T := c * Real.exp l
  let F := fun (x : Plane) (ω : Ω) => Real.log
    (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)
  let Q := fun (x : Plane) (ω : Ω) =>
    shfPairing Z a n (fun y => heatKernel a (y - x)) (fun _ => 1) ω
  let G := fun (x : Plane) (ω : Ω) => Real.log (Q x ω)
  let m := ∫ ω, F 0 ω ∂P
  let τ := Real.log l / 64
  let B0 := {ω | τ ≤ |F 0 ω - m|}
  let Bv := {ω | ∃ b : Fin 2 → Bool, τ ≤ |F (profileCubeVertex (l * R) b) ω - m|}
  let Bs := {ω | ∃ b : Fin 2 → Bool, 2 < Q (profileCubeVertex R b) ω}
  have hl : 0 < l := by linarith
  have hlog : 0 < Real.log l := Real.log_pos hl1
  have hτ : 0 < τ := div_pos hlog (by norm_num)
  have ha : 0 < a := htimes.1
  have han : a < n := htimes.2.1
  have haT : a < T := han.trans htimes.2.2.1
  have hmemF (x : Plane) : MemLp (F x) 2 P :=
    (heatStartMass_convexity_moments (-l) P Z hZ ha haT x).2.2.1
  have hmean (x : Plane) : (∫ ω, F x ω ∂P) = m :=
    (profile_heatMass_log_identDistrib (-l) P Z hZ ha haT x).integral_eq
  have hpoint (x : Plane) : P {ω | τ ≤ |F x ω - m|} ≤
      ENNReal.ofReal (V * Real.log l / τ ^ 2) := by
    have h := meas_ge_le_variance_div_sq (hmemF x) hτ
    rw [hmean x] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right
      (hVar P Z hZ T (Or.inr rfl) x) (sq_nonneg τ)))
  have hB0 : P B0 ≤ ENNReal.ofReal (V * Real.log l / τ ^ 2) := hpoint 0
  have hBv : P Bv ≤ ENNReal.ofReal (4 * (V * Real.log l / τ ^ 2)) := by
    have h := profile_measure_exists_finite_le P
      (fun b : Fin 2 → Bool => {ω | τ ≤ |F (profileCubeVertex (l * R) b) ω - m|})
      (by positivity : 0 ≤ V * Real.log l / τ ^ 2) (fun b => hpoint _)
    simpa [Fintype.card_fun] using h
  have hQmem (x : Plane) : MemLp (Q x) 2 P := heatStartMass_memLp_two (-l) P Z hZ ha han x
  have hQmean (x : Plane) : (∫ ω, Q x ω ∂P) = 1 :=
    (heatStartMass_integral_eq_one (-l) P Z hZ ha han x).2
  have hQvar (x : Plane) : variance (Q x) P ≤ Cs * Real.log l / l := by
    rw [variance_eq_sub (hQmem x), hQmean x]
    have h := hShort P Z hZ a htimes.2.2.2 han x
    change (∫ ω, Q x ω ^ 2 ∂P) ≤ _ at h
    change (∫ ω, Q x ω ^ 2 ∂P) - 1 ^ 2 ≤ _
    linarith only [h]
  have hshort (x : Plane) : P {ω | 2 < Q x ω} ≤ ENNReal.ofReal (Cs * Real.log l / l) := by
    have h := meas_ge_le_variance_div_sq (hQmem x) (by norm_num : (0 : ℝ) < 1)
    rw [hQmean x] at h
    have hsub : {ω | 2 < Q x ω} ⊆ {ω | 1 ≤ |Q x ω - 1|} := by
      intro ω hω
      change 2 < Q x ω at hω
      have := le_abs_self (Q x ω - 1)
      change 1 ≤ _
      linarith only [hω, this]
    exact (measure_mono hsub).trans (h.trans (ENNReal.ofReal_le_ofReal
      (by simpa only [one_pow, div_one] using hQvar x)))
  have hBs : P Bs ≤ ENNReal.ofReal (4 * (Cs * Real.log l / l)) := by
    have h := profile_measure_exists_finite_le P
      (fun b : Fin 2 → Bool => {ω | 2 < Q (profileCubeVertex R b) ω})
      (by positivity : 0 ≤ Cs * Real.log l / l) (fun b => hshort _)
    simpa [Fintype.card_fun] using h
  have hMeanLower : -(Real.log Cl + Real.log l) / 2 ≤ m := by
    have hMom := hLong P Z hZ a htimes.2.2.2 haT 0
    have hOne := profile_heatMass_secondMoment_ge_one (-l) P Z hZ ha haT 0
    have hLog := Real.log_le_log (zero_lt_one.trans_le hOne) hMom
    rw [Real.log_mul (by linarith : Cl ≠ 0) hl.ne'] at hLog
    have hmeanB := (heatStartMass_convexity_moments (-l) P Z hZ ha haT 0).2.2.2.2
    change -m ≤ _ at hmeanB
    linarith only [hLog, hmeanB]
  have hsubset : ∀ᵐ ω ∂P, (∃ x : Plane, (∀ i : Fin 2, |x i| ≤ R) ∧
      profileMass Z a n T x ω < l ^ (-(5 / 8 : ℝ))) → ω ∈ B0 ∪ (Bv ∪ Bs) := by
    filter_upwards [profile_heatMass_ae_pos_semiconvex (-l) P Z hZ ha haT,
      profile_heatMass_ae_pos_semiconvex (-l) P Z hZ ha han] with ω hpT hpn
    intro hbad
    by_contra hnot
    have h0 : |F 0 ω - m| < τ := lt_of_not_ge (fun h => hnot (Or.inl h))
    have hv (b : Fin 2 → Bool) : |F (profileCubeVertex (l * R) b) ω - m| < τ :=
      lt_of_not_ge (fun h => hnot (Or.inr (Or.inl ⟨b, h⟩)))
    have hs (b : Fin 2 → Bool) : Q (profileCubeVertex R b) ω ≤ 2 :=
      le_of_not_gt (fun h => hnot (Or.inr (Or.inr ⟨b, h⟩)))
    have hF0 : -(17 / 32 : ℝ) * Real.log l ≤ F 0 ω := by
      have := neg_abs_le (F 0 ω - m)
      dsimp only [τ] at h0
      linarith only [hMeanLower, h0, this, hscale]
    have hFv (b : Fin 2 → Bool) : F (profileCubeVertex (l * R) b) ω - F 0 ω ≤ Real.log l / 32 := by
      have h1 := le_abs_self (F (profileCubeVertex (l * R) b) ω - m)
      have h2 := neg_abs_le (F 0 ω - m)
      have h3 := hv b
      dsimp only [τ] at h0 h3
      linarith only [h0, h1, h2, h3]
    have hGv (b : Fin 2 → Bool) : G (profileCubeVertex R b) ω ≤ Real.log 2 :=
      Real.log_le_log (hpn.1 _) (hs b)
    obtain ⟨x, hx, hbad⟩ := hbad
    have hbound := profile_semiconvex_ratio_cube_bound ha hl1.le htimes.2.2.2 hR
      (by linarith only [hroom]) hpT.2 hpn.2 hF0 hFv hGv hx
    have hpos : 0 < profileMass Z a n T x ω := div_pos (hpT.1 x) (hpn.1 x)
    have hlogbad := Real.log_lt_log hpos hbad
    rw [Real.log_rpow hl] at hlogbad
    rw [profileMass, Real.log_div (hpT.1 x).ne' (hpn.1 x).ne'] at hlogbad
    change F x ω - G x ω < _ at hlogbad
    linarith only [hbound, hlogbad]
  have hmeasure := (measure_mono_ae hsubset).trans
    ((measure_union_le B0 (Bv ∪ Bs)).trans
      (add_le_add hB0 ((measure_union_le Bv Bs).trans (add_le_add hBv hBs))))
  have hsum : ENNReal.ofReal (V * Real.log l / τ ^ 2) +
      (ENNReal.ofReal (4 * (V * Real.log l / τ ^ 2)) +
       ENNReal.ofReal (4 * (Cs * Real.log l / l))) =
      ENNReal.ofReal (20480 * V / Real.log l + 4 * Cs * Real.log l / l) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    dsimp only [τ]
    field_simp
    ring
  apply hmeasure.trans
  rw [hsum]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [C]
  have h1 := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hCs) hlog.le
  have h2 := div_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20480) hV0) hlog.le) hl.le
  calc
    _ ≤ (20480 * V / Real.log l + 4 * Cs * Real.log l / l) +
        4 * Cs / Real.log l + 20480 * V * Real.log l / l := by linarith only [h1, h2]
    _ = _ := by ring

/-- The delayed ratio is at least `l^(-5/8)` everywhere on any fixed
coordinate square, with probability tending to one. -/
theorem lowerBound_delayedRatio {c ρ w R : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2) (hR : 0 ≤ R)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l)) :
    Tendsto (fun l => P {ω | ∃ x : Plane, (∀ i : Fin 2, |x i| ≤ R) ∧
      profileMass (Z l) (gridPoint c ρ l) (S c ρ w l) (c * Real.exp l) x ω < l ^ (-(5 / 8 : ℝ))})
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hBound⟩ := profile_delayedRatio_lower_tail hc hρ hw hwHalf hR
  have hInv : Tendsto (fun l : ℝ => C / Real.log l) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Pi.inv_apply] using Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul C
  have hRatio : Tendsto (fun l : ℝ => Real.log l / l) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hSecond : Tendsto (fun l : ℝ => C * Real.log l / l) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using hRatio.const_mul C
  have hLimit : Tendsto (fun l : ℝ => ENNReal.ofReal (C / Real.log l + C * Real.log l / l))
      atTop (𝓝 0) := by
    simpa only [zero_add, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (hInv.add hSecond)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hLimit
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [hBound] with l hl
  exact hl P (Z l) (hZ l)

/-- Profile masses and their logarithms are jointly measurable in space
and disorder; positivity holds at all centers on one probability-one event. -/
theorem profileMass_joint_regular (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a n T : ℝ} (ha : 0 < a) (han : a < n) (haT : a < T) :
    AEStronglyMeasurable (fun p : Ω × Plane => Real.log (profileMass Z a n T p.2 p.1)) (P.prod volume) ∧
    AEStronglyMeasurable (fun p : Ω × Plane => profileMass Z a n T p.2 p.1) (P.prod volume) ∧
    (∀ᵐ ω ∂P, ∀ x : Plane, 0 < profileMass Z a n T x ω) := by
  have hJ (t : ℝ) (hat : a < t) : AEStronglyMeasurable (fun p : Ω × Plane => Real.log
      (shfPairing Z a t (fun y => heatKernel a (y - p.2)) (fun _ => 1) p.1)) (P.prod volume) := by
    have h := JointConvergence.aemeasurable_shfLogField_joint ϑ P Z hZ a t a ha.le hat ha
      (0 : Plane →ᵇ ℝ)
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] at h
    exact (h.comp_quasiMeasurePreserving
      (Measure.measurePreserving_swap (μ := P) (ν := volume)).quasiMeasurePreserving).aestronglyMeasurable
  have hpT := profile_heatMass_ae_pos_semiconvex ϑ P Z hZ ha haT
  have hpn := profile_heatMass_ae_pos_semiconvex ϑ P Z hZ ha han
  have hpos : ∀ᵐ ω ∂P, ∀ x : Plane, 0 < profileMass Z a n T x ω := by
    filter_upwards [hpT, hpn] with ω hT hn
    intro x
    exact div_pos (hT.1 x) (hn.1 x)
  have hpT' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := (volume : Measure Plane))).ae hpT
  have hpn' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := (volume : Measure Plane))).ae hpn
  have hlog : AEStronglyMeasurable (fun p : Ω × Plane => Real.log (profileMass Z a n T p.2 p.1))
      (P.prod volume) := by
    apply ((hJ T haT).sub (hJ n han)).congr
    filter_upwards [hpT', hpn'] with p hT hn
    change Real.log _ - Real.log _ = Real.log (profileMass Z a n T p.2 p.1)
    rw [profileMass, Real.log_div (hT.1 p.2).ne' (hn.1 p.2).ne']
  refine ⟨hlog, ?_, hpos⟩
  apply (Real.continuous_exp.comp_aestronglyMeasurable hlog).congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := (volume : Measure Plane))).ae hpos] with p hp
  exact Real.exp_log (hp p.2)

/-- Each earlier grid entrance is positive and no later than the delayed entrance. -/
theorem profile_gridEntrance_pos_le {c ρ l : ℝ} (hρ : 1 < ρ) (hp : 0 < gridPoint c ρ l) (j : ℕ) :
    0 < gridEntrance c ρ l j ∧ gridEntrance c ρ l j ≤ gridPoint c ρ l := by
  have hρ0 := zero_lt_one.trans hρ
  have hpow : 1 ≤ ρ ^ j := one_le_pow₀ hρ.le
  unfold gridEntrance
  exact ⟨div_pos hp (pow_pos hρ0 _), (div_le_iff₀ (pow_pos hρ0 _)).mpr
    (le_mul_of_one_le_right hp.le hpow)⟩

/-- The local logarithmic-comparison error has a vanishing scaled first
moment uniformly over earlier entrances and spatial centers. -/
theorem profile_log_error_uniform_expectation {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ j : ℕ, ∀ x : Plane,
        let r := l ^ (-(5 / 8 : ℝ))
        let A := profileMass Z (gridEntrance c ρ l j) (S c ρ q l) (c * Real.exp l) x
        let B := profileMass Z (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x
        Integrable (fun ω => profileLogComparisonError r (A ω) (B ω)) P ∧
          Real.sqrt l * (∫ ω, profileLogComparisonError r (A ω) (B ω) ∂P) ≤
            profileLogErrorEnvelope C L l := by
  obtain ⟨ρc, q, hρc, hq0, hqHalf, hRate⟩ := profile_comparison_localisation_rate hc
  obtain ⟨ρm, hρm, hMom⟩ := logMoments_profile hc
  refine ⟨max ρc ρm, q, hρc.trans_le (le_max_left _ _), hq0, hqHalf, ?_⟩
  intro ρ hρle
  have hρc' := (le_max_left ρc ρm).trans hρle
  have hρm' := (le_max_right ρc ρm).trans hρle
  have hρ : 1 < ρ := hρc.trans_le hρc'
  obtain ⟨C, hC, hRate⟩ := hRate ρ hρc'
  obtain ⟨L, hL, hMom⟩ := hMom ρ hρm' q hq0 hqHalf 4 (by norm_num) (by norm_num)
  refine ⟨C, L, hC, hL, ?_⟩
  filter_upwards [hRate, hMom, eventually_grid_time_order hc hρ hq0 hqHalf,
    eventually_ge_atTop (1 : ℝ)] with l hRate hMom htimes hl1
  intro Ω _ P _ Z hZ j x
  let r := l ^ (-(5 / 8 : ℝ))
  let ε := C / (l * Real.sqrt l) + C * (r / 2) / l
  have hl : 0 < l := by linarith
  have hr : 0 < r := Real.rpow_pos_of_pos hl _
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  obtain ⟨ha, hap⟩ := profile_gridEntrance_pos_le hρ htimes.1 j
  have han := hap.trans_lt htimes.2.1
  have haT := han.trans htimes.2.2.1
  have hMA := hMom P Z hZ j x
  have hMB := hMom P Z hZ 0 x
  simp only [gridEntrance, pow_zero, div_one] at hMB
  have hcap := hRate P Z hZ j (c * Real.exp l) (Or.inr rfl) x (r / 2) (half_pos hr).le
  have he := profile_log_error_integral_bound P
    (aemeasurable_profileMass P Z hZ ha han haT x)
    (aemeasurable_profileMass P Z hZ htimes.1 htimes.2.1 (htimes.2.1.trans htimes.2.2.1) x)
    hMA.1 hMB.1 hr hε (mul_nonneg hL (Real.log_nonneg hl1)) hMA.2 hMB.2 hcap
  refine ⟨he.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left he.2 (Real.sqrt_nonneg _)).trans
    (profile_log_error_scale_bound hC hL hl1)

/-- The uniform first-moment error estimate survives spatial testing, with
integrability established before Fubini. The grid is chosen before the test. -/
theorem profile_log_error_spatial_expectation {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ f : Plane → ℝ, Measurable f → Integrable f → ∀ j : ℕ,
        let r := l ^ (-(5 / 8 : ℝ))
        let X := fun ω x => profileLogComparisonError r
          (profileMass Z (gridEntrance c ρ l j) (S c ρ q l) (c * Real.exp l) x ω)
          (profileMass Z (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω)
        (∀ᵐ ω ∂P, Integrable (fun x => |f x| * X ω x)) ∧
          Integrable (fun ω => ∫ x, |f x| * X ω x) P ∧
          Real.sqrt l * (∫ ω, (∫ x, |f x| * X ω x) ∂P) ≤
            (∫ x, |f x|) * profileLogErrorEnvelope C L l := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hqHalf, hError⟩ := profile_log_error_uniform_expectation hc
  refine ⟨ρ₀, q, hρ₀, hq0, hqHalf, ?_⟩
  intro ρ hρle
  have hρ := hρ₀.trans_le hρle
  obtain ⟨C, L, hC, hL, hError⟩ := hError ρ hρle
  refine ⟨C, L, hC, hL, ?_⟩
  filter_upwards [hError, eventually_grid_time_order hc hρ hq0 hqHalf,
    eventually_ge_atTop (1 : ℝ)] with l hError htimes hl1
  intro Ω _ P _ Z hZ f hf hfi j
  let r := l ^ (-(5 / 8 : ℝ))
  let X := fun ω x => profileLogComparisonError r
    (profileMass Z (gridEntrance c ρ l j) (S c ρ q l) (c * Real.exp l) x ω)
    (profileMass Z (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω)
  have hl : 0 < l := by linarith
  have hsqrt : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hr : 0 < r := Real.rpow_pos_of_pos hl _
  obtain ⟨ha, hap⟩ := profile_gridEntrance_pos_le hρ htimes.1 j
  have hA := profileMass_joint_regular (-l) P Z hZ ha (hap.trans_lt htimes.2.1)
    (hap.trans_lt (htimes.2.1.trans htimes.2.2.1))
  have hB := profileMass_joint_regular (-l) P Z hZ htimes.1 htimes.2.1
    (htimes.2.1.trans htimes.2.2.1)
  have hX : AEStronglyMeasurable (fun p : Ω × Plane => X p.1 p.2) (P.prod volume) :=
    ((measurable_profileLogComparisonError r).comp_aemeasurable
      (hA.2.1.aemeasurable.prodMk hB.2.1.aemeasurable)).aestronglyMeasurable
  have hX0 (ω : Ω) (x : Plane) : 0 ≤ X ω x := profileLogComparisonError_nonneg hr _ _
  have hXi (x : Plane) : Integrable (fun ω => X ω x) P := (hError P Z hZ j x).1
  have hlogl : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hEnv : 0 ≤ profileLogErrorEnvelope C L l := by
    unfold profileLogErrorEnvelope
    positivity
  have hbound (x : Plane) : (∫ ω, X ω x ∂P) ≤ profileLogErrorEnvelope C L l / Real.sqrt l :=
    (le_div_iff₀ hsqrt).mpr (by simpa only [mul_comm] using (hError P Z hZ j x).2)
  obtain ⟨hpath, hi, hb⟩ := profile_weighted_nonneg_integral_bound P hX hX0 hXi
    (div_nonneg hEnv hsqrt.le) hbound hf hfi
  refine ⟨hpath, hi, ?_⟩
  calc
    _ ≤ Real.sqrt l * (profileLogErrorEnvelope C L l / Real.sqrt l * ∫ x, |f x|) :=
      mul_le_mul_of_nonneg_left hb hsqrt.le
    _ = _ := by field_simp

/-- Markov's inequality for a nonnegative real random variable, with an
explicit integrability premise and a strict tail. -/
theorem profile_measure_gt_le_of_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hi : Integrable Y P) (hY : ∀ ω, 0 ≤ Y ω) {ε B : ℝ} (hε : 0 < ε)
    (hbound : (∫ ω, Y ω ∂P) ≤ B) :
    P {ω | ε < Y ω} ≤ ENNReal.ofReal (B / ε) := by
  have h := (hi.div_const ε).measure_le_integral
    (Eventually.of_forall fun ω => div_nonneg (hY ω) hε.le)
    (fun ω hω => (one_le_div hε).mpr (le_of_lt hω))
  rw [integral_div] at h
  exact h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hbound hε.le))

/-- The mass comparison converts to the spatial logarithmic comparison,
uniformly over all earlier grid entrances. The grid is fixed before `f`. -/
theorem sqrt_mul_integral_abs_log_sub_log_tendsto_zero {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane)),
      (∀ l, IsCriticalSHF (-l) P (Z l)) →
      ∀ f : Plane → ℝ, Measurable f → Integrable f →
      ∀ R : ℝ, 0 ≤ R → (∀ x, f x ≠ 0 → ∀ i : Fin 2, |x i| ≤ R) →
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun l => ⨆ j : ℕ, P {ω | ε < Real.sqrt l *
          ∫ x, |f x| * |Real.log (profileMass (Z l) (gridEntrance c ρ l j)
            (S c ρ q l) (c * Real.exp l) x ω) -
            Real.log (profileMass (Z l) (gridPoint c ρ l)
              (S c ρ q l) (c * Real.exp l) x ω)|}) atTop (𝓝 0) := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hqHalf, hSp⟩ := profile_log_error_spatial_expectation hc
  refine ⟨ρ₀, q, hρ₀, hq0, hqHalf, ?_⟩
  intro ρ hρle Ω _ P _ Z hZ f hf hfi R hR hsupp ε hε
  have hρ := hρ₀.trans_le hρle
  obtain ⟨C, L, hC, hL, hSp⟩ := hSp ρ hρle
  let Mf := ∫ x, |f x|
  have hMf : 0 ≤ Mf := integral_nonneg fun x => abs_nonneg _
  let BadB := fun l => {ω | ∃ x : Plane, (∀ i : Fin 2, |x i| ≤ R) ∧
    profileMass (Z l) (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω < l ^ (-(5 / 8 : ℝ))}
  have hLower : Tendsto (fun l => P (BadB l)) atTop (𝓝 0) :=
    lowerBound_delayedRatio hc hρ hq0 hqHalf hR P Z hZ
  have hEnv : Tendsto (fun l => ENNReal.ofReal (Mf * profileLogErrorEnvelope C L l / ε)) atTop (𝓝 0) := by
    have h := ((profileLogErrorEnvelope_tendsto C L).const_mul Mf).div_const ε
    simpa only [mul_zero, zero_div, ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h
  have hSum : Tendsto (fun l => P (BadB l) + ENNReal.ofReal (Mf * profileLogErrorEnvelope C L l / ε))
      atTop (𝓝 0) := by simpa only [zero_add] using hLower.add hEnv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSum
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [hSp, eventually_grid_time_order hc hρ hq0 hqHalf,
    eventually_ge_atTop (1 : ℝ)] with l hSp htimes hl1
  apply iSup_le
  intro j
  let r := l ^ (-(5 / 8 : ℝ))
  let A := fun x ω => profileMass (Z l) (gridEntrance c ρ l j) (S c ρ q l) (c * Real.exp l) x ω
  let B := fun x ω => profileMass (Z l) (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω
  let X := fun ω x => profileLogComparisonError r (A x ω) (B x ω)
  let Y := fun ω => Real.sqrt l * ∫ x, |f x| * X ω x
  have hl : 0 < l := by linarith
  have hr : 0 < r := Real.rpow_pos_of_pos hl _
  have hSpj := hSp P (Z l) (hZ l) f hf hfi j
  have hYi : Integrable Y P := hSpj.2.1.const_mul _
  have hY0 (ω : Ω) : 0 ≤ Y ω := mul_nonneg (Real.sqrt_nonneg _)
    (integral_nonneg fun x => mul_nonneg (abs_nonneg _) (profileLogComparisonError_nonneg hr _ _))
  have hMarkov : P {ω | ε < Y ω} ≤ ENNReal.ofReal (Mf * profileLogErrorEnvelope C L l / ε) := by
    apply profile_measure_gt_le_of_integral P hYi hY0 hε
    rw [integral_const_mul]
    exact hSpj.2.2
  obtain ⟨ha, hap⟩ := profile_gridEntrance_pos_le hρ htimes.1 j
  have hApos := (profileMass_joint_regular (-l) P (Z l) (hZ l) ha
    (hap.trans_lt htimes.2.1) (hap.trans_lt (htimes.2.1.trans htimes.2.2.1))).2.2
  have hsubset : ∀ᵐ ω ∂P,
      (ε < Real.sqrt l * ∫ x, |f x| * |Real.log (A x ω) - Real.log (B x ω)|) →
        ω ∈ BadB l ∪ {ω | ε < Y ω} := by
    filter_upwards [hApos, hSpj.1] with ω hApos hXi
    intro hbad
    by_cases hb : ω ∈ BadB l
    · exact Or.inl hb
    right
    have hpoint (x : Plane) : |f x| * |Real.log (A x ω) - Real.log (B x ω)| ≤ |f x| * X ω x := by
      by_cases hfx : f x = 0
      · simp only [hfx, abs_zero, zero_mul, le_refl]
      · have hBcut : r ≤ B x ω := le_of_not_gt (fun h => hb ⟨x, hsupp x hfx, h⟩)
        exact mul_le_mul_of_nonneg_left (profile_abs_log_sub_le_error hr (hApos x) hBcut) (abs_nonneg _)
    have hInt : (∫ x, |f x| * |Real.log (A x ω) - Real.log (B x ω)|) ≤ ∫ x, |f x| * X ω x :=
      integral_mono_of_nonneg (Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
        hXi (Eventually.of_forall hpoint)
    exact lt_of_lt_of_le hbad (mul_le_mul_of_nonneg_left hInt (Real.sqrt_nonneg _))
  exact (measure_mono_ae hsubset).trans ((measure_union_le (BadB l) {ω | ε < Y ω}).trans
    (add_le_add le_rfl hMarkov))

/-- Spatial testing of the logarithmic heat-started mass. -/
def profileLogPairing {Ω : Type*} [MeasurableSpace Ω]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (a T : ℝ) (f : Plane → ℝ) (ω : Ω) : ℝ :=
  ∫ x, f x * Real.log (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω)

/-- The scaled, mean-zero delayed log ratio vanishes in probability. -/
theorem profile_delayed_log_pairing_tendstoInMeasure {c ρ w : ℝ} (hc : 0 < c) (hρ : 1 < ρ)
    (hw : 0 < w) (hwHalf : w < 1 / 2)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    {f : Plane → ℝ} (hf : Measurable f) (hfi : Integrable f)
    (hfw : Integrable (fun x => ‖x‖ * |f x|)) (hfzero : ∫ x, f x = 0) :
    TendstoInMeasure P (fun l ω => Real.sqrt l * ∫ x, f x * Real.log
      (profileMass (Z l) (gridPoint c ρ l) (S c ρ w l) (c * Real.exp l) x ω)) atTop (fun _ => 0) := by
  obtain ⟨Cf, hCf, hBound⟩ := l2_integral_log_delayedRatio_le hc hρ hw hwHalf hf hfi hfw hfzero
  have hRate : Tendsto (fun l : ℝ => Cf * (Real.log l) ^ (1 / 4 : ℝ) / Real.sqrt l) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (1 / 4 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    simpa only [← Real.sqrt_eq_rpow, mul_zero, mul_div_assoc] using h.const_mul Cf
  have hUpper : Tendsto (fun l : ℝ => ENNReal.ofReal (Cf * (Real.log l) ^ (1 / 4 : ℝ) / Real.sqrt l))
      atTop (𝓝 0) := by simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hRate
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUpper
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [hBound, eventually_gt_atTop (0 : ℝ)] with l hBound hl
  have hB := hBound P (Z l) (hZ l)
  let I := fun ω => ∫ x, f x * Real.log
    (profileMass (Z l) (gridPoint c ρ l) (S c ρ w l) (c * Real.exp l) x ω)
  have heq : (fun ω => Real.sqrt l * I ω - 0) = Real.sqrt l • I := by funext ω; simp only [sub_zero, Pi.smul_apply, smul_eq_mul]
  change eLpNorm (fun ω => Real.sqrt l * I ω - 0) 2 P ≤ _
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
  calc
    _ ≤ ENNReal.ofReal (Real.sqrt l) * ENNReal.ofReal (Cf * (Real.log l) ^ (1 / 4 : ℝ) / l) :=
      mul_le_mul' le_rfl hB.2
    _ = ENNReal.ofReal (Cf * (Real.log l) ^ (1 / 4 : ℝ) / Real.sqrt l) := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      congr 1
      have hs := Real.sq_sqrt hl.le
      have hs0 := Real.sqrt_pos.mpr hl
      have hdiv : Real.sqrt l / l = 1 / Real.sqrt l :=
        (div_eq_div_iff hl.ne' hs0.ne').mpr (by nlinarith only [hs])
      calc
        _ = (Cf * (Real.log l) ^ (1 / 4 : ℝ)) * (Real.sqrt l / l) := by ring
        _ = _ := by rw [hdiv]; ring

/-- Convergence in measure controls each strict absolute-value tail. -/
theorem profile_strict_abs_tail_tendsto {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {F : Filter ι} {X : ι → Ω → ℝ}
    (hX : TendstoInMeasure P X F (fun _ => 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i => P {ω | ε < |X i ω|}) F (𝓝 0) := by
  have h := (tendstoInMeasure_iff_norm.mp hX) ε hε
  simp only [sub_zero, Real.norm_eq_abs] at h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun _ => zero_le)
  refine Eventually.of_forall (fun i => measure_mono ?_)
  intro ω hω
  change ε < |X i ω| at hω
  change ε ≤ |X i ω|
  exact hω.le

/-- A common vanishing remainder may be added to a family whose tails
vanish uniformly in its countable index. -/
theorem profile_uniform_tail_of_ae_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {U E : ℝ → ℕ → Ω → ℝ} {B : ℝ → Ω → ℝ}
    (hbound : ∀ᶠ l : ℝ in atTop, ∀ j, ∀ᵐ ω ∂P, |U l j ω| ≤ E l j ω + |B l ω|)
    (hE : ∀ ε : ℝ, 0 < ε → Tendsto (fun l => ⨆ j : ℕ, P {ω | ε < E l j ω}) atTop (𝓝 0))
    (hB : TendstoInMeasure P B atTop (fun _ => 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun l => ⨆ j : ℕ, P {ω | ε < |U l j ω|}) atTop (𝓝 0) := by
  intro ε hε
  have h1 := hE (ε / 2) (half_pos hε)
  have h2 := profile_strict_abs_tail_tendsto P hB (half_pos hε)
  have hsum : Tendsto (fun l => (⨆ j : ℕ, P {ω | ε / 2 < E l j ω}) + P {ω | ε / 2 < |B l ω|})
      atTop (𝓝 0) := by simpa only [zero_add] using h1.add h2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [hbound] with l hl
  apply iSup_le
  intro j
  have hsub : ∀ᵐ ω ∂P, (ε < |U l j ω|) →
      ω ∈ {ω | ε / 2 < E l j ω} ∪ {ω | ε / 2 < |B l ω|} := by
    filter_upwards [hl j] with ω hω
    intro hu
    by_contra hn
    have he : E l j ω ≤ ε / 2 := le_of_not_gt (fun h => hn (Or.inl h))
    have hb : |B l ω| ≤ ε / 2 := le_of_not_gt (fun h => hn (Or.inr h))
    linarith only [hu, hω, he, hb]
  exact (measure_mono_ae hsub).trans ((measure_union_le _ _).trans
    (add_le_add (le_iSup (fun j => P {ω | ε / 2 < E l j ω}) j) le_rfl))

/-- Localisation in time for the logarithmic observables, uniformly over
all grid entrances, with the grid chosen before the mean-zero test function. -/
theorem localisation_uniform_entrance {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane)),
      (∀ l, IsCriticalSHF (-l) P (Z l)) →
      ∀ f : Plane → ℝ, Measurable f → Integrable f →
      Integrable (fun x => ‖x‖ * |f x|) → (∫ x, f x) = 0 →
      ∀ R : ℝ, 0 ≤ R → (∀ x, f x ≠ 0 → ∀ i : Fin 2, |x i| ≤ R) →
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun l => ⨆ j : ℕ, P {ω | ε < Real.sqrt l *
          |profileLogPairing (Z l) (gridEntrance c ρ l j) (c * Real.exp l) f ω -
            profileLogPairing (Z l) (gridEntrance c ρ l j) (S c ρ q l) f ω|}) atTop (𝓝 0) := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hqHalf, hConv⟩ := sqrt_mul_integral_abs_log_sub_log_tendsto_zero hc
  refine ⟨ρ₀, q, hρ₀, hq0, hqHalf, ?_⟩
  intro ρ hρle Ω _ P _ Z hZ f hf hfi hfw hfzero R hR hsupp ε hε
  have hρ := hρ₀.trans_le hρle
  let U := fun l j ω => Real.sqrt l *
    (profileLogPairing (Z l) (gridEntrance c ρ l j) (c * Real.exp l) f ω -
      profileLogPairing (Z l) (gridEntrance c ρ l j) (S c ρ q l) f ω)
  let E := fun l j ω => Real.sqrt l * ∫ x, |f x| *
    |Real.log (profileMass (Z l) (gridEntrance c ρ l j) (S c ρ q l) (c * Real.exp l) x ω) -
      Real.log (profileMass (Z l) (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω)|
  let B := fun l ω => Real.sqrt l * ∫ x, f x *
    Real.log (profileMass (Z l) (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω)
  have hE : ∀ ε : ℝ, 0 < ε → Tendsto (fun l => ⨆ j : ℕ, P {ω | ε < E l j ω}) atTop (𝓝 0) :=
    hConv ρ hρle P Z hZ f hf hfi R hR hsupp
  have hB : TendstoInMeasure P B atTop (fun _ => 0) :=
    profile_delayed_log_pairing_tendstoInMeasure hc hρ hq0 hqHalf P Z hZ hf hfi hfw hfzero
  have hbound : ∀ᶠ l : ℝ in atTop, ∀ j, ∀ᵐ ω ∂P, |U l j ω| ≤ E l j ω + |B l ω| := by
    filter_upwards [eventually_grid_time_order hc hρ hq0 hqHalf] with l htimes
    intro j
    obtain ⟨ha, hap⟩ := profile_gridEntrance_pos_le hρ htimes.1 j
    have hA := flow_decomposition (-l) P (Z l) (hZ l) ha (hap.trans_lt htimes.2.1)
      (hap.trans_lt (htimes.2.1.trans htimes.2.2.1)) hf hfi
    have hB := flow_decomposition (-l) P (Z l) (hZ l) htimes.1 htimes.2.1
      (htimes.2.1.trans htimes.2.2.1) hf hfi
    filter_upwards [hA, hB] with ω hA hB
    let IA := ∫ x, f x * Real.log (profileMass (Z l) (gridEntrance c ρ l j)
      (S c ρ q l) (c * Real.exp l) x ω)
    let IB := ∫ x, f x * Real.log (profileMass (Z l) (gridPoint c ρ l)
      (S c ρ q l) (c * Real.exp l) x ω)
    have hdiff : IA - IB = ∫ x, f x *
        (Real.log (profileMass (Z l) (gridEntrance c ρ l j) (S c ρ q l) (c * Real.exp l) x ω) -
         Real.log (profileMass (Z l) (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω)) := by
      rw [← integral_sub hA.1 hB.1]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    have hnorm : |IA - IB| ≤ ∫ x, |f x| *
        |Real.log (profileMass (Z l) (gridEntrance c ρ l j) (S c ρ q l) (c * Real.exp l) x ω) -
         Real.log (profileMass (Z l) (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω)| := by
      rw [hdiff]
      simpa only [abs_mul] using (abs_integral_le_integral_abs
        (f := fun x => f x * (Real.log (profileMass (Z l) (gridEntrance c ρ l j) (S c ρ q l) (c * Real.exp l) x ω) -
          Real.log (profileMass (Z l) (gridPoint c ρ l) (S c ρ q l) (c * Real.exp l) x ω))))
    have htri : |IA| ≤ |IA - IB| + |IB| := by
      simpa only [sub_add_cancel] using abs_add_le (IA - IB) IB
    have hsum := htri.trans (add_le_add hnorm le_rfl)
    have hdecomp : profileLogPairing (Z l) (gridEntrance c ρ l j) (c * Real.exp l) f ω -
        profileLogPairing (Z l) (gridEntrance c ρ l j) (S c ρ q l) f ω = IA := hA.2
    dsimp only [U, E, B]
    rw [hdecomp, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    convert mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg l) using 1; ring
  have h := profile_uniform_tail_of_ae_abs_le P hbound hE hB ε hε
  simpa only [U, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using h

/-- The earlier entrance grid approaches zero through strictly positive times. -/
theorem profile_gridEntrance_tendsto_zero {c ρ l : ℝ} (hρ : 1 < ρ)
    (hp : 0 < gridPoint c ρ l) :
    Tendsto (gridEntrance c ρ l) atTop (nhdsWithin 0 (Ioi 0)) := by
  have hρ0 := zero_lt_one.trans hρ
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr hρ0.le)
    ((inv_lt_one₀ hρ0).mpr hρ)
  have hlim : Tendsto (gridEntrance c ρ l) atTop (𝓝 0) := by
    change Tendsto (fun j : ℕ => gridPoint c ρ l / ρ ^ j) atTop (𝓝 0)
    simpa only [div_eq_mul_inv, inv_pow, mul_zero] using hpow.const_mul (gridPoint c ρ l)
  exact tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun j =>
    (profile_gridEntrance_pos_le hρ hp j).1)⟩

/-- Differences of two defining `L²` entrance limits converge in measure,
including after multiplication by a fixed scale. -/
theorem profile_scaled_difference_tendstoInMeasure {ι Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {u : Filter ι} {F G : ι → Ω → ℝ} {f g : Ω → ℝ} (a : ℝ)
    (hF : Tendsto (fun i => eLpNorm (fun ω => F i ω - f ω) 2 P) u (𝓝 0))
    (hG : Tendsto (fun i => eLpNorm (fun ω => G i ω - g ω) 2 P) u (𝓝 0)) :
    TendstoInMeasure P (fun i ω => a * (F i ω - G i ω)) u (fun ω => a * (f ω - g ω)) := by
  have hlim : Tendsto (fun i => ENNReal.ofReal |a| *
      (eLpNorm (fun ω => F i ω - f ω) 2 P + eLpNorm (fun ω => G i ω - g ω) 2 P)) u (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      ENNReal.Tendsto.const_mul (hF.add hG) (Or.inr ENNReal.ofReal_ne_top)
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le)
  refine Eventually.of_forall (fun i => ?_)
  have heq : (fun ω => a * (F i ω - G i ω) - a * (f ω - g ω)) =
      a • ((fun ω => F i ω - f ω) - (fun ω => G i ω - g ω)) := by
    funext ω
    change a * (F i ω - G i ω) - a * (f ω - g ω) = a * ((F i ω - f ω) - (G i ω - g ω))
    ring
  change eLpNorm (fun ω => a * (F i ω - G i ω) - a * (f ω - g ω)) 2 P ≤ _
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  exact mul_le_mul' le_rfl (eLpNorm_sub_le (by norm_num))

/-- A limit in probability inherits a uniform tail bound for its approximants. -/
theorem profile_limit_tail_le_iSup {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : ℕ → Ω → ℝ} {W : Ω → ℝ}
    (hX : TendstoInMeasure P X atTop W) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ε < |W ω|} ≤ ⨆ j : ℕ, P {ω | ε / 2 < |X j ω|} := by
  let B := ⨆ j : ℕ, P {ω | ε / 2 < |X j ω|}
  have h := (tendstoInMeasure_iff_norm.mp hX) (ε / 2) (half_pos hε)
  simp only [Real.norm_eq_abs] at h
  have hlim : Tendsto (fun j => P {ω | ε / 2 ≤ |X j ω - W ω|} + B) atTop (𝓝 B) := by
    simpa only [zero_add] using h.add_const B
  apply ge_of_tendsto hlim
  refine Eventually.of_forall (fun j => ?_)
  have hsub : {ω | ε < |W ω|} ⊆
      {ω | ε / 2 ≤ |X j ω - W ω|} ∪ {ω | ε / 2 < |X j ω|} := by
    intro ω hω
    change ε < |W ω| at hω
    by_contra hn
    have he : |X j ω - W ω| < ε / 2 := lt_of_not_ge (fun he => hn (Or.inl he))
    have hx : |X j ω| ≤ ε / 2 := le_of_not_gt (fun hx => hn (Or.inr hx))
    have ht : |W ω| ≤ |X j ω - W ω| + |X j ω| := by
      simpa only [sub_add_cancel, abs_sub_comm (W ω) (X j ω)] using abs_add_le (W ω - X j ω) (X j ω)
    linarith only [hω, he, hx, ht]
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add le_rfl (le_iSup (fun j => P {ω | ε / 2 < |X j ω|}) j)))

/-- Uniform localisation passes to every family with the defining `L²`
entrance limit. The family is not constructed or assumed to have any further field property. -/
theorem localisation_of_entrance_limit {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane)),
      (∀ l, IsCriticalSHF (-l) P (Z l)) →
      ∀ f : Plane → ℝ, Measurable f → Integrable f →
      Integrable (fun x => ‖x‖ * |f x|) → (∫ x, f x) = 0 →
      ∀ R : ℝ, 0 ≤ R → (∀ x, f x ≠ 0 → ∀ i : Fin 2, |x i| ≤ R) →
      ∀ K : ℝ → ℝ → Ω → ℝ,
      (∀ l T : ℝ, 0 < T → MemLp (K l T) 2 P ∧
        Tendsto (fun a => eLpNorm (fun ω => profileLogPairing (Z l) a T f ω - K l T ω) 2 P)
          (nhdsWithin 0 (Ioi 0)) (𝓝 0)) →
        TendstoInMeasure P (fun l ω => Real.sqrt l * (K l (c * Real.exp l) ω - K l (S c ρ q l) ω))
          atTop (fun _ => 0) := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hqHalf, hUniform⟩ := localisation_uniform_entrance hc
  refine ⟨ρ₀, q, hρ₀, hq0, hqHalf, ?_⟩
  intro ρ hρle Ω _ P _ Z hZ f hf hfi hfw hfzero R hR hsupp K hK
  have hρ := hρ₀.trans_le hρle
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hU := hUniform ρ hρle P Z hZ f hf hfi hfw hfzero R hR hsupp (ε / 4) (by linarith)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [eventually_grid_time_order hc hρ hq0 hqHalf] with l htimes
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  have hS : 0 < S c ρ q l := htimes.1.trans htimes.2.1
  have hGrid := profile_gridEntrance_tendsto_zero hρ htimes.1
  have hF := ((hK l (c * Real.exp l) hH).2).comp hGrid
  have hG := ((hK l (S c ρ q l) hS).2).comp hGrid
  have hconv := profile_scaled_difference_tendstoInMeasure P (Real.sqrt l) hF hG
  have hTail := profile_limit_tail_le_iSup P hconv (half_pos hε)
  have hsub : {ω | ε ≤ ‖Real.sqrt l * (K l (c * Real.exp l) ω - K l (S c ρ q l) ω) - 0‖} ⊆
      {ω | ε / 2 < |Real.sqrt l * (K l (c * Real.exp l) ω - K l (S c ρ q l) ω)|} := by
    intro ω hω
    change ε ≤ ‖_ - 0‖ at hω
    rw [sub_zero, Real.norm_eq_abs] at hω
    change ε / 2 < _
    linarith only [hω, hε]
  apply (measure_mono hsub).trans
  convert hTail using 1
  congr 1
  funext j
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  rw [show ε / 2 / 2 = ε / 4 by ring, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- Proposition 6.4 for every mean-zero smooth compactly supported test,
with `K` specified only by its defining `L²` entrance limit. -/
theorem localisation {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane)),
      (∀ l, IsCriticalSHF (-l) P (Z l)) →
      ∀ f : TestFn, (∫ x, f x) = 0 → ∀ K : ℝ → ℝ → Ω → ℝ,
      (∀ l T : ℝ, 0 < T → MemLp (K l T) 2 P ∧
        Tendsto (fun a => eLpNorm (fun ω => profileLogPairing (Z l) a T f ω - K l T ω) 2 P)
          (nhdsWithin 0 (Ioi 0)) (𝓝 0)) →
        TendstoInMeasure P (fun l ω => Real.sqrt l * (K l (c * Real.exp l) ω - K l (S c ρ q l) ω))
          atTop (fun _ => 0) := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hqHalf, hMain⟩ := localisation_of_entrance_limit hc
  refine ⟨ρ₀, q, hρ₀, hq0, hqHalf, ?_⟩
  intro ρ hρle Ω _ P _ Z hZ f hfzero K hK
  obtain ⟨R, hR, hSupport⟩ := f.hasCompactSupport.isCompact.isBounded.exists_pos_norm_lt
  have hsupp : ∀ x, f x ≠ 0 → ∀ i : Fin 2, |x i| ≤ R := by
    intro x hx i
    have hnorm := hSupport x (subset_tsupport f hx)
    have hcoord : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
    exact hcoord.trans hnorm.le
  exact hMain ρ hρle P Z hZ f f.continuous.measurable
    (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
    (integrable_firstMoment_testFn f) hfzero R hR.le hsupp K hK

end Critical2DKPZ.Extensions.GffTangent

end
