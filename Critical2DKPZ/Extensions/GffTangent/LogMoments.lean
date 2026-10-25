/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.HeatMassMoments
public import Critical2DKPZ.Extensions.GffTangent.ProfileIdentities
public import Critical2DKPZ.Extensions.GffTangent.AssociatedLog
public import Critical2DKPZ.Definitions.ProfileP2Fun
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonRenewal
import Critical2DKPZ.OnePoint.CriticalGap
import Critical2DKPZ.NonGaussian.HeatStartWalkLaw
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Critical2DKPZ.GaussianConvexity.EhrhardMomentBounds
import Critical2DKPZ.EhrhardType.Moments
import Mathlib.Probability.Moments.IntegrableExpMul
import Critical2DKPZ.MomentBounds.CCR25MomentBoundSix
import Critical2DKPZ.MomentBounds.AiiKProfileHypotheses
import Critical2DKPZ.MomentBounds.CSZ25BlockMomentAssembly
import Critical2DKPZ.Extensions.ScaleLimit.DistributionBounds
import Critical2DKPZ.Extensions.GffTangent.ProfileLemmaFlow



/-! # Quantitative logarithmic and inverse moments of entrance masses -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- Parameter-six version of the inverse-moment part of
`convexity_moments_of_positive_mean_one`.  This is internal: no CSZ input. -/
theorem inverse_sixth_moment_of_positive_mean_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Ω → ℝ}
    (hA : MemLp A 2 P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (hmean : (∫ ω, A ω ∂P) = 1)
    (hE : IsEhrhardType (P.map fun ω => Real.log (A ω))) :
    Integrable (fun ω => (A ω)⁻¹ ^ 6) P ∧
      (∫ ω, (A ω)⁻¹ ^ 6 ∂P) ≤ (∫ ω, A ω ^ 2 ∂P) ^ 21 := by
  let L : Ω → ℝ := fun ω => Real.log (A ω)
  have hLm : AEMeasurable L P :=
    Real.measurable_log.comp_aemeasurable hA.aemeasurable
  have hExp : (fun ω => Real.exp (L ω)) =ᵐ[P] A := by
    filter_upwards [hpos] with ω hω
    exact Real.exp_log hω
  have hExpI : Integrable Real.exp (P.map L) :=
    (integrable_map_measure (by fun_prop) hLm).mpr
      ((hA.integrable (by norm_num)).congr hExp.symm)
  have hExpM : (∫ z, Real.exp z ∂P.map L) = 1 := by
    rw [integral_map hLm (by fun_prop), integral_congr_ae hExp, hmean]
  have hExp2 : (fun ω => Real.exp (2 * L ω)) =ᵐ[P] fun ω => A ω ^ 2 := by
    filter_upwards [hpos] with ω hω
    rw [show 2 * L ω = L ω + L ω by ring, Real.exp_add]
    change Real.exp (Real.log (A ω)) * Real.exp (Real.log (A ω)) = _
    rw [Real.exp_log hω, pow_two]
  have hExp2I : Integrable (fun z : ℝ => Real.exp (2 * z)) (P.map L) :=
    (integrable_map_measure (by fun_prop) hLm).mpr
      (hA.integrable_sq.congr hExp2.symm)
  have hExp2M : (∫ z, Real.exp (2 * z) ∂P.map L) = ∫ ω, A ω ^ 2 ∂P := by
    rw [integral_map hLm (by fun_prop), integral_congr_ae hExp2]
  have hExpNeg :
      (fun ω => Real.exp (-6 * L ω)) =ᵐ[P] fun ω => (A ω)⁻¹ ^ 6 := by
    filter_upwards [hpos] with ω hω
    rw [show -6 * L ω = (6 : ℕ) * (-L ω) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_neg]
    change (Real.exp (Real.log (A ω)))⁻¹ ^ 6 = _
    rw [Real.exp_log hω]
  have hInvI : Integrable (fun ω => (A ω)⁻¹ ^ 6) P :=
    ((integrable_map_measure (by fun_prop) hLm).mp
      (EhrhardType.integrable_exp_mul_of_isEhrhardType hE
        (q := -6) (by norm_num))).congr hExpNeg
  have hInvB := GaussianConvexity.negative_moment_le_second_moment_rpow
    hE hExpI hExpM hExp2I (p := 6) (by norm_num)
  have hExpNegM :
      (∫ z, Real.exp (-6 * z) ∂P.map L) = ∫ ω, (A ω)⁻¹ ^ 6 ∂P := by
    rw [integral_map hLm (by fun_prop), integral_congr_ae hExpNeg]
  rw [hExpNegM, hExp2M] at hInvB
  norm_num only [show (6 : ℝ) * (6 + 1) / 2 = 21 by norm_num,
    Real.rpow_ofNat] at hInvB
  exact ⟨hInvI, hInvB⟩

/-- Every heat-started mass has the inverse-sixth moment needed in the
profile-ratio estimate. -/
theorem heatStartMass_inverse_sixth_moment
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {a T : ℝ}
    (ha : 0 < a) (haT : a < T) (x : Plane) :
    let A := shfPairing Z a T
      (fun y => heatKernel a (y - x)) (fun _ => 1)
    Integrable (fun ω => (A ω)⁻¹ ^ 6) P ∧
      (∫ ω, (A ω)⁻¹ ^ 6 ∂P) ≤ (∫ ω, A ω ^ 2 ∂P) ^ 21 := by
  dsimp only
  have hp := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    ϑ P Z hZ a T a x (0 : Plane →ᵇ ℝ) ha.le haT ha
  have hg : (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) =
      fun _ => (1 : ℝ) := by
    funext y
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero]
  rw [hg] at hp
  exact inverse_sixth_moment_of_positive_mean_one P
    (heatStartMass_memLp_two ϑ P Z hZ ha haT x) hp.1
    (heatStartMass_integral_eq_one ϑ P Z hZ ha haT x).2 hp.2.2

/-- Cauchy--Schwarz turns a positive sixth moment of the denominator and an
inverse sixth moment of the numerator into the inverse-third moment of their
ratio. For heat-started masses, take `N = Z'_n` and `S = Z'_S`, so `B=S/N`. -/
theorem integral_inv_ratio_pow_three_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N S : Ω → ℝ} {CN CS : ℝ}
    (hNmeas : AEMeasurable N P) (hSmeas : AEMeasurable S P)
    (hNpos : ∀ᵐ ω ∂P, 0 < N ω) (hSpos : ∀ᵐ ω ∂P, 0 < S ω)
    (hN6 : Integrable (fun ω => N ω ^ 6) P)
    (hSi6 : Integrable (fun ω => (S ω)⁻¹ ^ 6) P)
    (hCN : (∫ ω, N ω ^ 6 ∂P) ≤ CN)
    (hCS : (∫ ω, (S ω)⁻¹ ^ 6 ∂P) ≤ CS) :
    Integrable (fun ω => (S ω / N ω)⁻¹ ^ 3) P ∧
      (∫ ω, (S ω / N ω)⁻¹ ^ 3 ∂P) ≤ Real.sqrt CN * Real.sqrt CS := by
  have hN3m : AEStronglyMeasurable (fun ω => N ω ^ 3) P :=
    (hNmeas.pow_const 3).aestronglyMeasurable
  have hSi3m : AEStronglyMeasurable (fun ω => (S ω)⁻¹ ^ 3) P :=
    (hSmeas.inv.pow_const 3).aestronglyMeasurable
  have hN3sq : Integrable (fun ω => (N ω ^ 3) ^ 2) P := by
    convert hN6 using 1; ring_nf
  have hSi3sq : Integrable (fun ω => ((S ω)⁻¹ ^ 3) ^ 2) P := by
    convert hSi6 using 1; ring_nf
  have hN3 : MemLp (fun ω => N ω ^ 3) 2 P :=
    (memLp_two_iff_integrable_sq hN3m).mpr hN3sq
  have hSi3 : MemLp (fun ω => (S ω)⁻¹ ^ 3) 2 P :=
    (memLp_two_iff_integrable_sq hSi3m).mpr hSi3sq
  have hprod : Integrable (fun ω => N ω ^ 3 * (S ω)⁻¹ ^ 3) P :=
    by simpa only [Pi.mul_def] using hN3.integrable_mul hSi3
  have heq : (fun ω => (S ω / N ω)⁻¹ ^ 3) =ᵐ[P]
      fun ω => N ω ^ 3 * (S ω)⁻¹ ^ 3 := by
    filter_upwards [hNpos, hSpos] with ω hNω hSω
    field_simp
  refine ⟨hprod.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq]
  have hnonneg : 0 ≤ ∫ ω, N ω ^ 3 * (S ω)⁻¹ ^ 3 ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [hNpos, hSpos] with ω hNω hSω
    exact mul_nonneg (pow_nonneg hNω.le 3)
      (pow_nonneg (inv_nonneg.mpr hSω.le) 3)
  have hholder := abs_integral_mul_le_sqrt_sq P hN3 hSi3
  rw [abs_of_nonneg hnonneg] at hholder
  have hsqN : (∫ ω, (N ω ^ 3) ^ 2 ∂P) = ∫ ω, N ω ^ 6 ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    ring
  have hsqS : (∫ ω, ((S ω)⁻¹ ^ 3) ^ 2 ∂P) =
      ∫ ω, (S ω)⁻¹ ^ 6 ∂P := by
    apply integral_congr_ae
    filter_upwards [] with ω
    ring
  rw [hsqN, hsqS] at hholder
  exact hholder.trans (mul_le_mul (Real.sqrt_le_sqrt hCN)
    (Real.sqrt_le_sqrt hCS) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- A normalized Ehrhard logarithm has a fourth moment controlled polynomially
by the logarithm of its second exponential moment. -/
theorem integral_abs_pow_four_le_of_ehrhard
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (hE : IsEhrhardType μ)
    (h1I : Integrable (fun z : ℝ => Real.exp z) μ)
    (h1 : (∫ z, Real.exp z ∂μ) = 1)
    (h2I : Integrable (fun z : ℝ => Real.exp (2 * z)) μ)
    {V : ℝ} (hV : 1 ≤ V)
    (h2V : (∫ z, Real.exp (2 * z) ∂μ) ≤ V) :
    Integrable (fun z : ℝ => |z| ^ 4) μ ∧
      (∫ z, |z| ^ 4 ∂μ) ≤
        (4 * (1 + Real.log V)) ^ 4 * (2 + Real.exp 1) := by
  let L : ℝ := Real.log V
  let q : ℝ := (1 + L)⁻¹
  have hVpos : 0 < V := zero_lt_one.trans_le hV
  have hL : 0 ≤ L := by dsimp [L]; exact Real.log_nonneg hV
  have hden : 0 < 1 + L := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [inv_le_one₀ hden]
    linarith
  have hqI : Integrable (fun z : ℝ => Real.exp (q * z)) μ := by
    apply (integrable_const (1 : ℝ)).add h1I |>.mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    change Real.exp (q * z) ≤ 1 + Real.exp z
    by_cases hz : 0 ≤ z
    · exact (Real.exp_le_exp.mpr (mul_le_of_le_one_left hz hq1)).trans
        (le_add_of_nonneg_left zero_le_one)
    · exact (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_ge hz))).trans
        (le_add_of_nonneg_right (Real.exp_nonneg z))
  have hqM : (∫ z, Real.exp (q * z) ∂μ) ≤ 2 := by
    calc
      (∫ z, Real.exp (q * z) ∂μ) ≤ ∫ z, (1 + Real.exp z) ∂μ := by
        apply integral_mono hqI ((integrable_const (1 : ℝ)).add h1I)
        intro z
        by_cases hz : 0 ≤ z
        · exact (Real.exp_le_exp.mpr (mul_le_of_le_one_left hz hq1)).trans
            (le_add_of_nonneg_left zero_le_one)
        · exact (Real.exp_le_one_iff.mpr
            (mul_nonpos_of_nonneg_of_nonpos hq.le (le_of_not_ge hz))).trans
            (le_add_of_nonneg_right (Real.exp_nonneg z))
      _ = 2 := by rw [integral_add (integrable_const 1) h1I, integral_const, h1]; norm_num
  have hnqI : Integrable (fun z : ℝ => Real.exp (-q * z)) μ :=
    EhrhardType.integrable_exp_mul_of_isEhrhardType hE (neg_nonpos.mpr hq.le)
  have hnq := GaussianConvexity.negative_moment_le_second_moment_rpow
    hE h1I h1 h2I hq.le
  have hexponent : L * (q * (q + 1) / 2) ≤ 1 := by
    dsimp [q]
    field_simp
    nlinarith [sq_nonneg L]
  have hVrpow : V ^ (q * (q + 1) / 2) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hVpos]
    apply Real.exp_le_exp.mpr
    simpa only [L, mul_comm] using hexponent
  have hnqM : (∫ z, Real.exp (-q * z) ∂μ) ≤ Real.exp 1 :=
    hnq.trans ((Real.rpow_le_rpow (by positivity) h2V (by positivity)).trans hVrpow)
  have hmaxI : Integrable
      (fun z : ℝ => max (Real.exp (q * z)) (Real.exp (-q * z))) μ :=
    by
      apply (hqI.add hnqI).mono' (by fun_prop)
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (Real.exp_nonneg _) (le_max_left _ _))]
      exact max_le_add_of_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have habsI : Integrable (fun z : ℝ => |z| ^ 4) μ := by
    apply (hmaxI.const_mul ((4 / |q|) ^ (4 : ℝ))).mono' (by fun_prop)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) 4)]
    simpa only [Real.rpow_ofNat] using
      ProbabilityTheory.rpow_abs_le_mul_max_exp z (by norm_num : (0 : ℝ) ≤ 4) hq.ne'
  refine ⟨habsI, ?_⟩
  calc
    (∫ z, |z| ^ 4 ∂μ) ≤
        ∫ z, (4 / |q|) ^ (4 : ℝ) *
          max (Real.exp (q * z)) (Real.exp (-q * z)) ∂μ := by
      apply integral_mono habsI (hmaxI.const_mul _)
      intro z
      simpa only [Real.rpow_ofNat] using
        ProbabilityTheory.rpow_abs_le_mul_max_exp z (by norm_num : (0 : ℝ) ≤ 4) hq.ne'
    _ ≤ (4 / |q|) ^ (4 : ℝ) * (2 + Real.exp 1) := by
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        (∫ z, max (Real.exp (q * z)) (Real.exp (-q * z)) ∂μ) ≤
            ∫ z, (Real.exp (q * z) + Real.exp (-q * z)) ∂μ := by
          apply integral_mono hmaxI (hqI.add hnqI)
          intro z
          exact max_le_add_of_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
        _ = (∫ z, Real.exp (q * z) ∂μ) +
            ∫ z, Real.exp (-q * z) ∂μ := integral_add hqI hnqI
        _ ≤ 2 + Real.exp 1 := add_le_add hqM hnqM
    _ = (4 * (1 + Real.log V)) ^ 4 * (2 + Real.exp 1) := by
      have habsq : |q| = (1 + L)⁻¹ := abs_of_pos hq
      rw [habsq]
      dsimp [L]
      congr 1
      simp only [div_inv_eq_mul, Real.rpow_ofNat]

/-- The entrance heat mass has the quantitative fourth logarithmic moment used
in the ultraviolet exceptional-set estimate. -/
theorem heatStartMass_log_fourth_moment_le
    (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z)
    {a T V : ℝ} (ha : 0 < a) (haT : a < T) (hV : 1 ≤ V) (x : Plane)
    (hsecond : (∫ ω, shfPairing Z a T
      (fun y => heatKernel a (y - x)) (fun _ => 1) ω ^ 2 ∂P) ≤ V) :
    let X := shfPairing Z a T
      (fun y => heatKernel a (y - x)) (fun _ => 1)
    Integrable (fun ω => |Real.log (X ω)| ^ 4) P ∧
      (∫ ω, |Real.log (X ω)| ^ 4 ∂P) ≤
        (4 * (1 + Real.log V)) ^ 4 * (2 + Real.exp 1) := by
  dsimp only
  let X := shfPairing Z a T
    (fun y => heatKernel a (y - x)) (fun _ => 1)
  let L : Ω → ℝ := fun ω => Real.log (X ω)
  have hXm := heatStartMass_memLp_two (-l) P Z hZ ha haT x
  have hp := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    (-l) P Z hZ a T a x (0 : Plane →ᵇ ℝ) ha.le haT ha
  have hg : (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) = fun _ => (1 : ℝ) := by
    funext y
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero]
  rw [hg] at hp
  have hpos := hp.1
  have hLm : AEMeasurable L P :=
    Real.measurable_log.comp_aemeasurable hXm.aemeasurable
  have hEh : IsEhrhardType (P.map L) := hp.2.2
  have hExp : (fun ω => Real.exp (L ω)) =ᵐ[P] X := by
    filter_upwards [hpos] with ω hω
    exact Real.exp_log hω
  have h1I : Integrable Real.exp (P.map L) :=
    (integrable_map_measure (by fun_prop) hLm).mpr
      ((hXm.integrable (by norm_num)).congr hExp.symm)
  have h1 : (∫ z, Real.exp z ∂P.map L) = 1 := by
    rw [integral_map hLm (by fun_prop), integral_congr_ae hExp]
    exact (heatStartMass_integral_eq_one (-l) P Z hZ ha haT x).2
  have hExp2 : (fun ω => Real.exp (2 * L ω)) =ᵐ[P] fun ω => X ω ^ 2 := by
    filter_upwards [hpos] with ω hω
    rw [show 2 * L ω = L ω + L ω by ring, Real.exp_add,
      Real.exp_log hω, pow_two]
  have h2I : Integrable (fun z => Real.exp (2 * z)) (P.map L) :=
    (integrable_map_measure (by fun_prop) hLm).mpr
      (hXm.integrable_sq.congr hExp2.symm)
  have h2V : (∫ z, Real.exp (2 * z) ∂P.map L) ≤ V := by
    rw [integral_map hLm (by fun_prop), integral_congr_ae hExp2]
    exact hsecond
  have hh := integral_abs_pow_four_le_of_ehrhard hEh h1I h1 h2I hV h2V
  have hmapI := (integrable_map_measure (by fun_prop) hLm).mp hh.1
  refine ⟨?_, ?_⟩
  · simpa only [L, X, Function.comp_def, sub_zero] using hmapI
  · have hb := hh.2
    rw [integral_map hLm (by fun_prop)] at hb
    simpa only [L, X, Function.comp_def, sub_zero] using hb


/-- Raw sixth moments follow from a centered sixth moment at mean one. -/
theorem integral_pow_six_le_of_centered
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable (fun ω => X ω ^ 6) P)
    (hY : Integrable (fun ω => (X ω - 1) ^ 6) P) {C : ℝ}
    (hC : |∫ ω, (X ω - 1) ^ 6 ∂P| ≤ C) :
    (∫ ω, X ω ^ 6 ∂P) ≤ 32 * (max C 0 + 1) := by
  have hpoint (ω : Ω) : X ω ^ 6 ≤ 32 * ((X ω - 1) ^ 6 + 1) := by
    have hXabs : |X ω| ≤ |X ω - 1| + 1 := by
      calc
        |X ω| = |(X ω - 1) + 1| := by congr 1; ring
        _ ≤ |X ω - 1| + 1 := by simpa using abs_add_le (X ω - 1) 1
    have hu : (|X ω - 1| + 1) ^ 6 ≤ 32 * (|X ω - 1| ^ 6 + 1) := by
      have hid : 32 * (|X ω - 1| ^ 6 + 1) - (|X ω - 1| + 1) ^ 6 =
          (|X ω - 1| - 1) ^ 2 *
            (31 * |X ω - 1| ^ 4 + 56 * |X ω - 1| ^ 3 +
              66 * |X ω - 1| ^ 2 + 56 * |X ω - 1| + 31) := by ring
      have hn : 0 ≤ (|X ω - 1| - 1) ^ 2 *
          (31 * |X ω - 1| ^ 4 + 56 * |X ω - 1| ^ 3 +
            66 * |X ω - 1| ^ 2 + 56 * |X ω - 1| + 31) := by positivity
      linarith only [hid, hn]
    calc
      X ω ^ 6 = |X ω| ^ 6 := by
        rw [(show Even 6 from by decide).pow_abs]
      _ ≤ (|X ω - 1| + 1) ^ 6 := by
        exact pow_le_pow_left₀ (abs_nonneg _) hXabs 6
      _ ≤ 32 * (|X ω - 1| ^ 6 + 1) := hu
      _ = 32 * ((X ω - 1) ^ 6 + 1) := by
        rw [(show Even 6 from by decide).pow_abs]
  have hmajor : Integrable (fun ω => 32 * ((X ω - 1) ^ 6 + 1)) P :=
    (hY.add (integrable_const 1)).const_mul 32
  calc
    (∫ ω, X ω ^ 6 ∂P) ≤ ∫ ω, 32 * ((X ω - 1) ^ 6 + 1) ∂P :=
      integral_mono_ae hX hmajor (Filter.Eventually.of_forall hpoint)
    _ = 32 * ((∫ ω, (X ω - 1) ^ 6 ∂P) + 1) := by
      rw [integral_const_mul, integral_add hY (integrable_const 1),
        integral_const, probReal_univ, one_smul]
    _ ≤ 32 * (max C 0 + 1) := by
      gcongr
      exact (le_abs_self _).trans (hC.trans (le_max_left _ _))

/-- CSZ25's proved sixth-order general moment bound, specialized to a simple
walk heat profile.  The constant is uniform in beta, the smoothing width and
the future length once width <= kappa * length and variance <= 1. -/
theorem exists_walkHeatProfile_sixth_moment_bound (κ : ℝ) (hκ : 0 < κ) :
    ∃ L₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ β : ℝ, 0 ≤ β → ∀ s L : ℕ, L₀ ≤ L → 1 ≤ s → (s : ℝ) ≤ κ * L →
      Var[fun ω => profileP2Fun β 0 L (fun z => srwKernel s z)
        (fun _ => 1) ω; disorderLaw] ≤ 1 →
      Integrable (fun ω => profileP2Fun β 0 L (fun z => srwKernel s z)
        (fun _ => 1) ω ^ 6) disorderLaw ∧
      (∫ ω, profileP2Fun β 0 L (fun z => srwKernel s z)
        (fun _ => 1) ω ^ 6 ∂disorderLaw) ≤ C := by
  obtain ⟨t, c₁, c₂, ht, hc₁, hc₂, hprofile⟩ :=
    MomentBounds.srwKernel_profile_hypotheses κ hκ
  have hgen : MomentBounds.GenMomentBound 6 :=
    MomentBounds.genMomentBound_of_ccr 6 (by
      intro h6
      exact MomentBounds.ccrMomentBound_six)
  obtain ⟨L₀, Cgen, hbound⟩ := hgen t c₁ c₂ 1 ht hc₁ hc₂ (by norm_num)
  refine ⟨L₀, 32 * (max (max Cgen 0) 0 + 1), by positivity, ?_⟩
  intro β hβ s L hL hs hsL hvar
  obtain ⟨hmass, hlocal, hsq⟩ := hprofile s L hs hsL
  let X : Disorder → ℝ := fun ω =>
    profileP2Fun β 0 L (fun z => srwKernel s z) (fun _ => 1) ω
  have hmean : (∫ ω, X ω ∂disorderLaw) = 1 := by
    dsimp only [X]
    exact Polymer.integral_profile_flat_probability β 0 L
      (fun z => srwKernel s z)
      (fun z => srwKernel_nonneg s z) hmass.tsum_eq
  have hcenter := hbound β hβ L hL (fun z => srwKernel s z)
    (fun z => srwKernel_nonneg s z) hmass hlocal hsq hvar
  rw [hmean] at hcenter
  have hcenter' : |∫ ω, (X ω - 1) ^ 6 ∂disorderLaw| ≤ max Cgen 0 := by
    have hv0 : 0 ≤ Var[X; disorderLaw] := variance_nonneg X disorderLaw
    have hv : Var[X; disorderLaw] ^ 3 ≤ 1 := pow_le_one₀ hv0 hvar
    have hc := hcenter
    norm_num only [show (6 : ℝ) / 2 = 3 by norm_num, Real.rpow_ofNat] at hc
    apply hc.trans
    calc
      Cgen * Var[X; disorderLaw] ^ 3 ≤ max Cgen 0 * Var[X; disorderLaw] ^ 3 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hv0 _)
      _ ≤ max Cgen 0 * 1 :=
        mul_le_mul_of_nonneg_left hv (le_max_right _ _)
      _ = _ := mul_one _
  have hX6 : Integrable (fun ω => X ω ^ 6) disorderLaw := by
    simpa only [X, (show Even 6 from by decide).pow_abs] using
      Polymer.integrable_abs_pow_profile_probability β 0 L
      (fun z => srwKernel s z) (fun _ => 1)
      (fun z => srwKernel_nonneg s z) hmass.tsum_eq 1 zero_le_one
      (by intro z; norm_num) 6
  have hY6 : Integrable (fun ω => (X ω - 1) ^ 6) disorderLaw := by
    simpa only [X] using MomentBounds.integrable_centeredMoment_profileP2Fun
      6 β L (fun z => srwKernel s z) 1
      (fun z => srwKernel_nonneg s z) hmass
  refine ⟨hX6, ?_⟩
  exact integral_pow_six_le_of_centered disorderLaw hX6 hY6 hcenter'



/-- Fixed-parameter, macroscopic-clock renewal-gap limit.  This is the
variance input missing from the positive-sixth specialization. -/
theorem tendsto_renewalGap_criticalBeta_neg_macroscopic
    (l : ℝ) {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => OnePoint.renewalGap (criticalBeta (-l) N) (m N)) atTop
      (𝓝 (l - Real.log c)) := by
  have hoverN : Tendsto (fun N : ℕ => replicaOverlap N / Real.log (N : ℝ))
      atTop (𝓝 (1 / Real.pi)) := Renewal.tendsto_overlap_div_log
  have hsmall : Tendsto (fun N : ℕ => l / Real.log (N : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul l
  have hden : Tendsto (fun N : ℕ => 1 - l / Real.log (N : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hsmall
  have hcorr : Tendsto (fun N : ℕ =>
      (replicaOverlap N / Real.log (N : ℝ)) *
        (l / (1 - l / Real.log (N : ℝ)))) atTop
      (𝓝 ((1 / Real.pi) * l)) := by
    simpa only [div_one, Pi.div_apply] using
      hoverN.mul ((tendsto_const_nhds (x := l)).div hden one_ne_zero)
  have hinc := tendsto_replicaOverlap_macroscopic_increment hc hm
  have hspec : ∀ᶠ N : ℕ in atTop,
      Polymer.sigmaSq (criticalBeta (-l) N) = criticalSigmaSq (-l) N := by
    filter_upwards [eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |l|]
      with N hN hlog
    simp only [Function.comp_def] at hlog
    simpa only [Polymer.sigmaSq] using
      (OnePoint.criticalBeta_spec_of_abs_lt_log (ϑ := -l) (by omega)
        (by simpa only [Function.comp_def, abs_neg] using hlog))
  have hlim := (hcorr.sub hinc).const_mul Real.pi
  have heq : Real.pi * ((1 / Real.pi) * l - (1 / Real.pi) * Real.log c) =
      l - Real.log c := by field_simp [Real.pi_ne_zero]
  rw [heq] at hlim
  apply hlim.congr' 
  filter_upwards [hspec, eventually_ge_atTop 2,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |l|]
      with N hσ hN hlog
  have hlog0 : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hR : replicaOverlap N ≠ 0 := (replicaOverlap_pos (by omega)).ne'
  have hden0 : 1 - l / Real.log (N : ℝ) ≠ 0 := by
    have habs : |l / Real.log (N : ℝ)| < 1 := by
      rw [abs_div, abs_of_pos (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))]
      exact (div_lt_one (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))).2 hlog
    exact (sub_pos.mpr (lt_of_abs_lt habs)).ne'
  dsimp only [OnePoint.renewalGap]
  rw [hσ]
  simp only [criticalSigmaSq, neg_div, ← sub_eq_add_neg]
  have hdiff : 0 < Real.log (N : ℝ) - l := by
    apply sub_pos.mpr
    exact (le_abs_self l).trans_lt (by simpa only [Function.comp_def] using hlog)
  field_simp [hlog0, hR, hden0, hdiff.ne']
  ring

/-- Consequently the gap ratio of two macroscopic clocks has the exact
continuum variance-ratio limit. -/
theorem tendsto_renewalGap_ratio_criticalBeta_neg
    (l : ℝ) {a b : ℕ → ℕ} {m n : ℝ}
    (hm : 0 < m) (hn : 0 < n) (hln : 0 < l - Real.log n)
    (ha : Tendsto (fun N : ℕ => (a N : ℝ) / N) atTop (𝓝 m))
    (hb : Tendsto (fun N : ℕ => (b N : ℝ) / N) atTop (𝓝 n)) :
    Tendsto (fun N => OnePoint.renewalGap (criticalBeta (-l) N) (a N) /
      OnePoint.renewalGap (criticalBeta (-l) N) (b N)) atTop
      (𝓝 ((l - Real.log m) / (l - Real.log n))) := by
  have hga := tendsto_renewalGap_criticalBeta_neg_macroscopic l hm ha
  have hgb := tendsto_renewalGap_criticalBeta_neg_macroscopic l hn hb
  exact hga.div hgb hln.ne'


/-- Uniform positive sixth moment for a heat-start mass whenever the entrance
is at most half the observation time and the exact renewal-gap ratio is below
two.  The constant is universal for this numerical regime. -/
theorem exists_heatStartMass_sixth_of_ratio :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {l m n : ℝ}, 0 < m → 2 * m < n →
      0 < l - Real.log n → (l - Real.log m) / (l - Real.log n) < 2 →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF (-l) P Z)
      (x : Plane),
      Integrable (fun ω =>
        shfPairing Z m n (fun y => heatKernel m (y - x)) (fun _ => 1) ω ^ 6) P ∧
      (∫ ω, shfPairing Z m n (fun y => heatKernel m (y - x))
        (fun _ => 1) ω ^ 6 ∂P) ≤ C := by
  obtain ⟨L₀, C, hC, hwalk⟩ := exists_walkHeatProfile_sixth_moment_bound 1 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro l m n hm hmn hln hratio Ω _ P _ Z hZ x
  let a : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * m)
  let b : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * n)
  let L : ℕ → ℕ := fun N => b N - a N
  let β : ℕ → ℝ := fun N => criticalBeta (-l) N
  have hab (N : ℕ) : a N ≤ b N := by
    dsimp only [a, b]
    exact evenCeil_mono (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg N))
  have haLim : Tendsto (fun N : ℕ => (a N : ℝ) / N) atTop (𝓝 m) := by
    simpa only [a] using SHF.Moments.tendsto_evenCeil_div m hm.le
  have hbLim : Tendsto (fun N : ℕ => (b N : ℝ) / N) atTop (𝓝 n) := by
    simpa only [b] using SHF.Moments.tendsto_evenCeil_div n (by linarith : 0 ≤ n)
  have hLLim : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 (n - m)) := by
    simpa only [L, a, b] using SHF.Moments.tendsto_evenCeil_gap_div hm.le (by linarith : m ≤ n)
  have hgapRatio := tendsto_renewalGap_ratio_criticalBeta_neg l hm
    (by linarith : 0 < n) hln haLim hbLim
  have hratioEv : ∀ᶠ N : ℕ in atTop,
      OnePoint.renewalGap (β N) (a N) / OnePoint.renewalGap (β N) (b N) < 2 := by
    exact hgapRatio.eventually (Iio_mem_nhds hratio)
  have hgapA := tendsto_renewalGap_criticalBeta_neg_macroscopic l hm haLim
  have hgapB := tendsto_renewalGap_criticalBeta_neg_macroscopic l
    (by linarith : 0 < n) hbLim
  have hgapApos : 0 < l - Real.log m := by
    have hlogmn : Real.log m < Real.log n := Real.log_lt_log hm (by linarith)
    linarith
  have hgapBpos : 0 < l - Real.log n := hln
  have hβpos : ∀ᶠ N : ℕ in atTop, 0 < β N := by
    filter_upwards [eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |l|]
      with N hN hlog
    have hs := OnePoint.criticalSigmaSq_pos_of_abs_lt_log (ϑ := -l) (N := N) (by omega)
      (by simpa only [Function.comp_def, abs_neg] using hlog)
    dsimp only [β, criticalBeta]
    exact Real.sqrt_pos.2 (Real.log_pos (by linarith [hs]))
  have hlarge : ∀ᶠ N : ℕ in atTop,
      L₀ ≤ L N ∧ 1 ≤ a N ∧ (a N : ℝ) ≤ (L N : ℝ) ∧
      0 < OnePoint.renewalGap (β N) (a N) ∧
      0 < OnePoint.renewalGap (β N) (b N) := by
    have hLtop : Tendsto L atTop atTop := by
      apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
      exact (Tendsto.pos_mul_atTop (by linarith : 0 < n - m) hLLim
        tendsto_natCast_atTop_atTop).congr' (by
          filter_upwards [eventually_ge_atTop 1] with N hN
          change ((L N : ℝ) / (N : ℝ)) * (N : ℝ) = (L N : ℝ)
          exact div_mul_cancel₀ _ (by exact_mod_cast (show N ≠ 0 by omega)))
    have hatop : Tendsto a atTop atTop := by
      apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
      exact (Tendsto.pos_mul_atTop hm haLim tendsto_natCast_atTop_atTop).congr' (by
        filter_upwards [eventually_ge_atTop 1] with N hN
        change ((a N : ℝ) / (N : ℝ)) * (N : ℝ) = (a N : ℝ)
        exact div_mul_cancel₀ _ (by exact_mod_cast (show N ≠ 0 by omega)))
    have hwidth : ∀ᶠ N : ℕ in atTop, (a N : ℝ) ≤ L N := by
      have hdiff := hLLim.sub haLim
      have hpos : 0 < (n - m) - m := by linarith
      filter_upwards [hdiff.eventually (Ioi_mem_nhds hpos), eventually_ge_atTop 1]
        with N hNdiff hN
      have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
      apply (div_le_div_iff_of_pos_right hN0).mp
      linarith
    filter_upwards [hLtop.eventually_ge_atTop L₀, hatop.eventually_ge_atTop 1,
      hwidth, hgapA.eventually (Ioi_mem_nhds hgapApos),
      hgapB.eventually (Ioi_mem_nhds hgapBpos)] with N hL haN hw hga hgb
    exact ⟨hL, haN, hw, hga, hgb⟩
  let X : ℕ → Disorder → ℝ := fun N ω => profileP2Fun (β N) (a N) (b N)
    (fun w => srwKernel (a N) (w - latticePoint N x)) (fun _ => 1) ω
  have hX6 : ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => X N ω ^ 6) disorderLaw ∧
      (∫ ω, X N ω ^ 6 ∂disorderLaw) ≤ C := by
    filter_upwards [hlarge, hratioEv, hβpos] with N hN hr hβ
    have hsecond := OnePoint.smoothedP2Plane_secondMoment_renewalGap
    obtain ⟨Cgap, hgap⟩ := hsecond
    have hsmooth := hgap (β N) hβ (a N) (b N) (hab N) hN.2.2.2.2
    have hmoment : (∫ ω, smoothedP2Plane (β N) (a N) (b N) 0 ω ^ 2
        ∂disorderLaw) ≤ 2 := by linarith [hsmooth.1]
    have hSmem : MemLp (smoothedP2Plane (β N) (a N) (b N) 0) 2 disorderLaw :=
      Polymer.memLp_smoothedP2Plane (β N) (a N) (b N) 0 2 (by norm_num)
    have hmean := Polymer.integral_smoothedP2Plane (β N) (a N) (b N) 0
    have hvar : Var[smoothedP2Plane (β N) (a N) (b N) 0; disorderLaw] ≤ 1 := by
      rw [variance_eq_sub hSmem, hmean]
      simp only [Pi.pow_apply, one_pow]
      linarith only [hmoment]
    have hLawBase := NonGaussian.identDistrib_heatStartWalkProfile_smoothed
      (β N) (Nat.zero_le (L N)) (a N) 0
    simp only [sub_zero, Nat.sub_zero] at hLawBase
    have hvarBase : Var[fun ω => profileP2Fun (β N) 0 (L N)
        (fun z => srwKernel (a N) z) (fun _ => 1) ω; disorderLaw] ≤ 1 := by
      rw [hLawBase.variance_eq]
      simpa only [L, Nat.sub_zero, Nat.add_sub_of_le (hab N)] using hvar
    have hbase := hwalk (β N) hβ.le (a N) (L N) hN.1 hN.2.1
      (by simpa only [one_mul] using hN.2.2.1) hvarBase
    have hLaw := NonGaussian.identDistrib_heatStartWalkProfile_smoothed
      (β N) (hab N) (a N) (latticePoint N x)
    have hLaw' : IdentDistrib (X N)
        (fun ω => profileP2Fun (β N) 0 (L N) (fun z => srwKernel (a N) z)
          (fun _ => 1) ω) disorderLaw disorderLaw := by
      -- Both sides have the law of the same smoothed mass.
      simpa only [X, L, Nat.sub_zero, Nat.add_sub_of_le (hab N)] using
        hLaw.trans hLawBase.symm
    exact ⟨(hLaw'.pow.integrable_iff).mpr hbase.1,
      (hLaw'.pow.integral_eq).trans_le hbase.2⟩
  have hdist0 := profile_heatStart_joint_tendsto (-l) P Z hZ 1
    (fun _ => m) (fun _ => n) (fun _ => m) (fun _ => x) 0
    (fun _ => ⟨hm.le, by linarith, hm⟩)
  have hdist : TendstoInDistribution X atTop
      (fun ω => shfPairing Z m n (fun y => heatKernel m (y - x)) (fun _ => 1) ω)
      (fun _ => disorderLaw) P := by
    have hraw := hdist0.continuous_comp (continuous_apply (0 : Fin 1))
    simp only [Function.comp_def, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      Real.exp_zero] at hraw
    refine ⟨fun N => (Polymer.measurable_profileP2Fun (β N) (a N) (b N)
      (fun w => srwKernel (a N) (w - latticePoint N x)) (fun _ => 1)).aemeasurable,
      hraw.aemeasurable_limit, hraw.tendsto.congr' ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    apply ProbabilityMeasure.toMeasure_injective
    apply Measure.map_congr
    filter_upwards [] with ω
    exact NonGaussian.heatStartWalkProfile_cellAverage_one_eq (β N)
      (by omega) (hab N) (evenCeil_even _) (Smoothing.evenCeil_sub_even
        (mul_le_mul_of_nonneg_left (by linarith : m ≤ n) (Nat.cast_nonneg N))) x ω
  exact ScaleLimit.integral_continuous_nonneg_le_of_tendstoInDistribution hdist
    (fun z : ℝ => z ^ 6) (by fun_prop)
    (fun z => (show Even 6 from by decide).pow_nonneg z) C
    (hX6.mono fun N h => h.1) (hX6.mono fun N h => h.2)

/-- An integral fourth-moment estimate, in the exact form produced by
`heatStartMass_log_fourth_moment_le`, gives both `MemLp 4` and its norm bound. -/
theorem memLp_four_eLpNorm_le_of_integral_abs_pow_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {B : ℝ}
    (hX : AEMeasurable X P) (hI : Integrable (fun ω => |X ω| ^ 4) P)
    (hB : (∫ ω, |X ω| ^ 4 ∂P) ≤ B) :
    MemLp X 4 P ∧ eLpNorm X 4 P ≤ ENNReal.ofReal (B ^ ((4 : ℝ)⁻¹)) := by
  have hpow : MemLp (fun ω => ‖X ω‖ ^ (4 : ℝ≥0∞).toReal) (1 : ℝ≥0∞) P := by
    rw [memLp_one_iff_integrable]
    simpa only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_ofNat] using hI
  have hm : MemLp X 4 P := by
    exact ((memLp_norm_rpow_iff (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) hX.aestronglyMeasurable
      (by norm_num) (by norm_num)).mp (by simpa only [ENNReal.div_self (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)] using hpow))
  refine ⟨hm, ?_⟩
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_ofNat]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
    (integral_nonneg fun ω => pow_nonneg (abs_nonneg (X ω)) 4) hB (by norm_num))

/-- Uniform-in-space `L⁴` control of the logarithm of a heat-start mass from
an upper bound on its second moment. -/
theorem heatStartMass_log_memLp_four
    (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z)
    {a T V : ℝ} (ha : 0 < a) (haT : a < T) (hV : 1 ≤ V)
    (hsecond : ∀ x : Plane, (∫ ω, shfPairing Z a T
      (fun y => heatKernel a (y - x)) (fun _ => 1) ω ^ 2 ∂P) ≤ V) :
    ∀ x : Plane,
      MemLp (fun ω => Real.log (shfPairing Z a T
        (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) 4 P ∧
      eLpNorm (fun ω => Real.log (shfPairing Z a T
        (fun y => heatKernel a (y - x)) (fun _ => 1) ω)) 4 P ≤
        ENNReal.ofReal (((4 * (1 + Real.log V)) ^ 4 * (2 + Real.exp 1)) ^ ((4 : ℝ)⁻¹)) := by
  intro x
  let A : Ω → ℝ := fun ω => shfPairing Z a T
    (fun y => heatKernel a (y - x)) (fun _ => 1) ω
  have hm := heatStartMass_memLp_two (-l) P Z hZ ha haT x
  have hlogm : AEMeasurable (fun ω => Real.log (A ω)) P :=
    Real.measurable_log.comp_aemeasurable hm.aemeasurable
  have h4 := heatStartMass_log_fourth_moment_le l P Z hZ ha haT hV x (hsecond x)
  exact memLp_four_eLpNorm_le_of_integral_abs_pow_four hlogm h4.1 h4.2

/-- Taking a log ratio costs only the sum of the two logarithmic `L⁴` norms.
This is the bridge used with independently chosen fine and coarse widths. -/
theorem profile_log_ratio_memLp_four
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A B : Ω → ℝ} (hA : MemLp (fun ω => Real.log (A ω)) 4 P)
    (hB : MemLp (fun ω => Real.log (B ω)) 4 P) {LA LB : ℝ}
    (hnA : eLpNorm (fun ω => Real.log (A ω)) 4 P ≤ ENNReal.ofReal LA)
    (hnB : eLpNorm (fun ω => Real.log (B ω)) 4 P ≤ ENNReal.ofReal LB) :
    MemLp (fun ω => Real.log (A ω) - Real.log (B ω)) 4 P ∧
      eLpNorm (fun ω => Real.log (A ω) - Real.log (B ω)) 4 P ≤
        ENNReal.ofReal LA + ENNReal.ofReal LB := by
  exact ⟨hA.sub hB, (eLpNorm_sub_le (by norm_num)).trans (add_le_add hnA hnB)⟩



/-- The fourth-root bound furnished by the logarithmic fourth-moment estimate
is logarithmic when the second moment grows at most polynomially. -/
theorem logFourthRoot_le_const_mul_log
    {C l : ℝ} (hC : 0 < C) (hl : Real.exp 1 ≤ l) :
    (((4 * (1 + Real.log (1 + C * l ^ (39 : ℕ)))) ^ 4 *
        (2 + Real.exp 1)) ^ ((4 : ℝ)⁻¹)) ≤
      (4 * (40 + Real.log (1 + C)) * (2 + Real.exp 1) ^ ((4 : ℝ)⁻¹)) *
        Real.log l := by
  have hl0 : 0 < l := (Real.exp_pos 1).trans_le hl
  have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hl
  have hlogl : 1 ≤ Real.log l := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hl
  have hCp : 0 < 1 + C := by linarith
  have hpoly : 1 + C * l ^ (39 : ℕ) ≤ (1 + C) * l ^ (39 : ℕ) := by
    nlinarith only [one_le_pow₀ hl1 (n := 39)]
  have hlogpoly : Real.log (1 + C * l ^ (39 : ℕ)) ≤
      Real.log (1 + C) + 39 * Real.log l := by
    calc
      _ ≤ Real.log ((1 + C) * l ^ (39 : ℕ)) :=
        Real.log_le_log (by positivity) hpoly
      _ = _ := by rw [Real.log_mul hCp.ne' (pow_ne_zero _ hl0.ne'), Real.log_pow]; norm_num
  have hlogC : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
  have hone : 1 + Real.log (1 + C * l ^ (39 : ℕ)) ≤
      (40 + Real.log (1 + C)) * Real.log l := by
    calc
      _ ≤ 1 + (Real.log (1 + C) + 39 * Real.log l) := add_le_add le_rfl hlogpoly
      _ ≤ (40 + Real.log (1 + C)) * Real.log l := by
        nlinarith only [hlogl, mul_le_mul_of_nonneg_left hlogl hlogC]
  let a := 4 * (1 + Real.log (1 + C * l ^ (39 : ℕ)))
  let b := 4 * (40 + Real.log (1 + C)) * Real.log l
  have hlogV : 0 ≤ Real.log (1 + C * l ^ (39 : ℕ)) := Real.log_nonneg (by nlinarith [pow_nonneg hl0.le 39])
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    nlinarith only [hone]
  have hb : 0 ≤ b := ha.trans hab
  have he : 0 ≤ 2 + Real.exp 1 := by positivity
  calc
    (a ^ 4 * (2 + Real.exp 1)) ^ ((4 : ℝ)⁻¹)
        = (a ^ 4) ^ ((4 : ℝ)⁻¹) *
            (2 + Real.exp 1) ^ ((4 : ℝ)⁻¹) := by
          rw [Real.mul_rpow (pow_nonneg ha 4) he]
    _ = a * (2 + Real.exp 1) ^ ((4 : ℝ)⁻¹) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
          norm_num
    _ ≤ b * (2 + Real.exp 1) ^ ((4 : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg he _)
    _ = (4 * (40 + Real.log (1 + C)) *
          (2 + Real.exp 1) ^ ((4 : ℝ)⁻¹)) * Real.log l := by
      dsimp [b]
      ring

/-- Two heat-start masses whose second moments obey the same polynomial
envelope give a uniform logarithmic profile-ratio bound. -/
theorem heatStartMass_log_ratio_memLp_four_of_poly_second
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {l C a b TA TB : ℝ} (hC : 0 < C) (hl : Real.exp 1 ≤ l)
    (ha : 0 < a) (haT : a < TA) (hb : 0 < b) (hbT : b < TB)
    (ZA ZB : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZA : IsCriticalSHF (-l) P ZA) (hZB : IsCriticalSHF (-l) P ZB)
    (hAsecond : ∀ x : Plane, (∫ ω, shfPairing ZA a TA
      (fun y => heatKernel a (y - x)) (fun _ => 1) ω ^ 2 ∂P) ≤
        1 + C * l ^ (39 : ℕ))
    (hBsecond : ∀ x : Plane, (∫ ω, shfPairing ZB b TB
      (fun y => heatKernel b (y - x)) (fun _ => 1) ω ^ 2 ∂P) ≤
        1 + C * l ^ (39 : ℕ)) :
    let K := 4 * (40 + Real.log (1 + C)) * (2 + Real.exp 1) ^ ((4 : ℝ)⁻¹)
    ∀ x : Plane,
      let A := fun ω => shfPairing ZA a TA
        (fun y => heatKernel a (y - x)) (fun _ => 1) ω
      let B := fun ω => shfPairing ZB b TB
        (fun y => heatKernel b (y - x)) (fun _ => 1) ω
      MemLp (fun ω => Real.log (A ω / B ω)) 4 P ∧
        eLpNorm (fun ω => Real.log (A ω / B ω)) 4 P ≤
          ENNReal.ofReal (2 * K * Real.log l) := by
  intro K x A B
  have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hl
  have hl0 : 0 < l := zero_lt_one.trans_le hl1
  have hlogC : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hV : 1 ≤ 1 + C * l ^ (39 : ℕ) := le_add_of_nonneg_right (mul_nonneg hC.le (pow_nonneg hl0.le _))
  have hAm := heatStartMass_log_memLp_four l P ZA hZA ha haT hV hAsecond x
  have hBm := heatStartMass_log_memLp_four l P ZB hZB hb hbT hV hBsecond x
  have hroot := logFourthRoot_le_const_mul_log hC hl
  have hnA : eLpNorm (fun ω => Real.log (A ω)) 4 P ≤ ENNReal.ofReal (K * Real.log l) :=
    hAm.2.trans (ENNReal.ofReal_le_ofReal hroot)
  have hnB : eLpNorm (fun ω => Real.log (B ω)) 4 P ≤ ENNReal.ofReal (K * Real.log l) :=
    hBm.2.trans (ENNReal.ofReal_le_ofReal hroot)
  have hd := profile_log_ratio_memLp_four hAm.1 hBm.1 hnA hnB
  have hAp := (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    (-l) P ZA hZA a TA a x (0 : Plane →ᵇ ℝ) ha.le haT ha).1
  have hBp := (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    (-l) P ZB hZB b TB b x (0 : Plane →ᵇ ℝ) hb.le hbT hb).1
  have hzero : (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) = fun _ => (1 : ℝ) := by
    funext y
    simp
  rw [hzero] at hAp hBp
  have heq : (fun ω => Real.log (A ω / B ω)) =ᵐ[P]
      fun ω => Real.log (A ω) - Real.log (B ω) := by
    filter_upwards [hAp, hBp] with ω hAω hBω
    exact Real.log_div hAω.ne' hBω.ne'
  refine ⟨(memLp_congr_ae heq).mpr hd.1, ?_⟩
  rw [eLpNorm_congr_ae heq]
  calc
    _ ≤ ENNReal.ofReal (K * Real.log l) + ENNReal.ofReal (K * Real.log l) := hd.2
    _ = ENNReal.ofReal (2 * K * Real.log l) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hK (Real.log_nonneg hl1))
        (mul_nonneg hK (Real.log_nonneg hl1))]
      congr 1
      ring


/-- Pointwise moment package for two profile masses.  It is obtained from four
heat-mass second moments and the coarse denominator/numerator sixth moments. -/
theorem profileMass_pair_log_four_inverse_three_of_poly_second
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {l C a m n S CN CS6 : ℝ} (hC : 0 < C) (hl : Real.exp 1 ≤ l)
    (ha : 0 < a) (han : a < n) (haS : a < S)
    (hm : 0 < m) (hmn : m < n) (hmS : m < S)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    (hsecond_aS : ∀ x, (∫ ω, shfPairing Z a S
      (fun y => heatKernel a (y-x)) (fun _ => 1) ω^2 ∂P) ≤ 1+C*l^39)
    (hsecond_an : ∀ x, (∫ ω, shfPairing Z a n
      (fun y => heatKernel a (y-x)) (fun _ => 1) ω^2 ∂P) ≤ 1+C*l^39)
    (hsecond_mS : ∀ x, (∫ ω, shfPairing Z m S
      (fun y => heatKernel m (y-x)) (fun _ => 1) ω^2 ∂P) ≤ 1+C*l^39)
    (hsecond_mn : ∀ x, (∫ ω, shfPairing Z m n
      (fun y => heatKernel m (y-x)) (fun _ => 1) ω^2 ∂P) ≤ 1+C*l^39)
    (hN6I : ∀ x, Integrable (fun ω => shfPairing Z m n
      (fun y => heatKernel m (y-x)) (fun _ => 1) ω^6) P)
    (hN6 : ∀ x, (∫ ω, shfPairing Z m n
      (fun y => heatKernel m (y-x)) (fun _ => 1) ω^6 ∂P) ≤ CN)
    (hSi6I : ∀ x, Integrable (fun ω => (shfPairing Z m S
      (fun y => heatKernel m (y-x)) (fun _ => 1) ω)⁻¹^6) P)
    (hSi6 : ∀ x, (∫ ω, (shfPairing Z m S
      (fun y => heatKernel m (y-x)) (fun _ => 1) ω)⁻¹^6 ∂P) ≤ CS6) :
    let K := 4*(40+Real.log (1+C))*(2+Real.exp 1)^((4:ℝ)⁻¹)
    let L := 2*K
    let D := Real.sqrt CN * Real.sqrt CS6
    ∀ x,
      let A := profileMass Z a n S x
      let B := profileMass Z m n S x
      MemLp (fun ω => Real.log (A ω)) 4 P ∧
      MemLp (fun ω => Real.log (B ω)) 4 P ∧
      eLpNorm (fun ω => Real.log (A ω)) 4 P ≤ ENNReal.ofReal (L*Real.log l) ∧
      eLpNorm (fun ω => Real.log (B ω)) 4 P ≤ ENNReal.ofReal (L*Real.log l) ∧
      Integrable (fun ω => (B ω)⁻¹^3) P ∧
      (∫ ω, (B ω)⁻¹^3 ∂P) ≤ D := by
  intro K L D x A B
  have hA := heatStartMass_log_ratio_memLp_four_of_poly_second P hC hl
    ha haS ha han Z Z hZ hZ hsecond_aS hsecond_an x
  have hB := heatStartMass_log_ratio_memLp_four_of_poly_second P hC hl
    hm hmS hm hmn Z Z hZ hZ hsecond_mS hsecond_mn x
  let N : Ω → ℝ := fun ω => shfPairing Z m n
    (fun y => heatKernel m (y-x)) (fun _ => 1) ω
  let Q : Ω → ℝ := fun ω => shfPairing Z m S
    (fun y => heatKernel m (y-x)) (fun _ => 1) ω
  have hNm := heatStartMass_memLp_two (-l) P Z hZ hm hmn x
  have hQm := heatStartMass_memLp_two (-l) P Z hZ hm hmS x
  have hNp := (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    (-l) P Z hZ m n m x (0 : Plane →ᵇ ℝ) hm.le hmn hm).1
  have hQp := (SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    (-l) P Z hZ m S m x (0 : Plane →ᵇ ℝ) hm.le hmS hm).1
  have hzero : (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) = fun _ => (1:ℝ) := by
    funext y; simp
  rw [hzero] at hNp hQp
  have hi := integral_inv_ratio_pow_three_le P hNm.aemeasurable hQm.aemeasurable
    hNp hQp (hN6I x) (hSi6I x) (hN6 x) (hSi6 x)
  exact ⟨hA.1, hB.1, hA.2, hB.2, hi.1, hi.2⟩


end Critical2DKPZ.Extensions.GffTangent

end
