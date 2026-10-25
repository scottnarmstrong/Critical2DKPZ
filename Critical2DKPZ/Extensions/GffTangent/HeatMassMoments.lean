/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Definitions.HeatKernel
public import Critical2DKPZ.Definitions.IsEhrhardType
import Critical2DKPZ.SmallScales.HeatStartMoments
import Critical2DKPZ.SHF.Positivity.LawFatou
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Critical2DKPZ.SHF.Positivity.PolymerHeatSecondMoment
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Critical2DKPZ.GaussianConvexity.EhrhardMomentBounds
import Critical2DKPZ.EhrhardType.Moments
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Integrability and convexity moments of the entrance heat-started masses -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- The entrance mass has integrable mass and annealed mean one. The positive
entrance time also serves as the positive heat smoothing scale. -/
theorem heatStartMass_integral_eq_one (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) (x : Plane) :
    Integrable (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1)) P ∧
      (∫ ω, shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1) ω ∂P) = 1 :=
  SmallScales.heatStart_integral_eq_one ϑ P Z hZ ha.le haT ha x

/-- Uniform integrable second moments along convergence in distribution give
square integrability of the limit. This uses the public Fatou-in-law API. -/
theorem memLp_two_of_tendstoInDistribution_of_sq_bounded
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hd : TendstoInDistribution X atTop Y μ P) {C : ℝ}
    (hb : ∀ᶠ N in atTop, Integrable (fun ω => X N ω ^ 2) (μ N) ∧
      (∫ ω, X N ω ^ 2 ∂μ N) ≤ C) : MemLp Y 2 P := by
  have hsq := hd.continuous_comp (g := fun x : ℝ => x ^ 2) (continuous_id.pow 2)
  have hf := SHF.Positivity.lintegral_ofReal_le_liminf_of_tendstoInDistribution_nonneg
    hsq (fun N ω => sq_nonneg _) (fun ω => sq_nonneg _)
  have hbound : ∀ᶠ N in atTop,
      (∫⁻ ω, ENNReal.ofReal (X N ω ^ 2) ∂μ N) ≤ ENNReal.ofReal C := by
    filter_upwards [hb] with N hN
    rw [← ofReal_integral_eq_lintegral_ofReal hN.1 (Eventually.of_forall fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hN.2
  have hlim : atTop.liminf (fun N => ∫⁻ ω, ENNReal.ofReal (X N ω ^ 2) ∂μ N) ≤
      ENNReal.ofReal C := by
    refine liminf_le_of_le (by isBoundedDefault) (fun b hb => ?_)
    obtain ⟨N, hN⟩ := (hb.and hbound).exists
    exact hN.1.trans hN.2
  have hm : AEStronglyMeasurable Y P := hd.aemeasurable_limit.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  refine ⟨hm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg (Y ω))]
  exact lt_of_le_of_lt (hf.trans hlim) ENNReal.ofReal_lt_top

/-- Entrance heat-started masses have a finite second moment at every positive
entrance time, without a smallness restriction on the smoothing scale. -/
theorem heatStartMass_memLp_two (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) (x : Plane) :
    MemLp (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1)) 2 P := by
  let X : ℕ → Disorder → ℝ := fun N ω =>
    ∫ p, heatKernel a (p.1 - x) ∂(SHF.Limit.polymerMeasure ϑ N a T ω)
  have hpair := SHF.Positivity.isCriticalSHF_heat_bounded_pairing
    ϑ P Z hZ ha.le haT ha x (1 : Plane →ᵇ ℝ)
  have hg : ((1 : Plane →ᵇ ℝ) : Plane → ℝ) = fun _ => (1 : ℝ) := by
    funext y
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply]
  have hd : TendstoInDistribution X atTop
      (shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1))
      (fun _ => disorderLaw) P := by
    simpa only [X, hg, mul_one] using hpair.2.2.2
  obtain ⟨C, hC⟩ := SHF.Positivity.polymer_heat_pairing_sq_integral_bounded ϑ ha.le haT ha x
  exact memLp_two_of_tendstoInDistribution_of_sq_bounded hd hC

/-- Gaussian convexity moments for a positive, mean-one mass whose logarithmic
law is Ehrhard type. No exponential-integrability premise is imposed on the log. -/
theorem convexity_moments_of_positive_mean_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Ω → ℝ}
    (hA : MemLp A 2 P) (hpos : ∀ᵐ ω ∂P, 0 < A ω) (hmean : (∫ ω, A ω ∂P) = 1)
    (hE : IsEhrhardType (P.map fun ω => Real.log (A ω))) :
    Integrable (fun ω => (A ω)⁻¹ ^ 4) P ∧
      (∫ ω, (A ω)⁻¹ ^ 4 ∂P) ≤ (∫ ω, A ω ^ 2 ∂P) ^ 10 ∧
      MemLp (fun ω => Real.log (A ω)) 2 P ∧
      variance (fun ω => Real.log (A ω)) P ≤ Real.log (∫ ω, A ω ^ 2 ∂P) ∧
      -(∫ ω, Real.log (A ω) ∂P) ≤ Real.log (∫ ω, A ω ^ 2 ∂P) / 2 := by
  let L : Ω → ℝ := fun ω => Real.log (A ω)
  have hLm : AEMeasurable L P := Real.measurable_log.comp_aemeasurable hA.aemeasurable
  have hExp : (fun ω => Real.exp (L ω)) =ᵐ[P] A := by
    filter_upwards [hpos] with ω hω using Real.exp_log hω
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
    (integrable_map_measure (by fun_prop) hLm).mpr (hA.integrable_sq.congr hExp2.symm)
  have hExp2M : (∫ z, Real.exp (2 * z) ∂P.map L) = ∫ ω, A ω ^ 2 ∂P := by
    rw [integral_map hLm (by fun_prop), integral_congr_ae hExp2]
  have hExpNeg : (fun ω => Real.exp (-4 * L ω)) =ᵐ[P] fun ω => (A ω)⁻¹ ^ 4 := by
    filter_upwards [hpos] with ω hω
    rw [show -4 * L ω = (4 : ℕ) * (-L ω) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_neg]
    change (Real.exp (Real.log (A ω)))⁻¹ ^ 4 = _
    rw [Real.exp_log hω]
  have hInvI : Integrable (fun ω => (A ω)⁻¹ ^ 4) P :=
    ((integrable_map_measure (by fun_prop) hLm).mp
      (EhrhardType.integrable_exp_mul_of_isEhrhardType hE (q := -4) (by norm_num))).congr hExpNeg
  have hInvB := GaussianConvexity.negative_moment_le_second_moment_rpow
    hE hExpI hExpM hExp2I (p := 4) (by norm_num)
  have hExpNegM : (∫ z, Real.exp (-4 * z) ∂P.map L) = ∫ ω, (A ω)⁻¹ ^ 4 ∂P := by
    rw [integral_map hLm (by fun_prop), integral_congr_ae hExpNeg]
  rw [hExpNegM, hExp2M] at hInvB
  norm_num only [show (4 : ℝ) * (4 + 1) / 2 = 10 by norm_num, Real.rpow_ofNat] at hInvB
  have hLogSqI : Integrable (fun ω => L ω ^ 2) P :=
    (integrable_map_measure (by fun_prop) hLm).mp
      (EhrhardType.integrable_sq_of_isEhrhardType hE hExpI)
  have hLogL2 : MemLp L 2 P := (memLp_two_iff_integrable_sq hLm.aestronglyMeasurable).mpr hLogSqI
  have hMeanB := GaussianConvexity.neg_mean_le_log_second_moment hE hExpI hExpM hExp2I
  rw [hExp2M, integral_map hLm (by fun_prop)] at hMeanB
  have hVarB := GaussianConvexity.variance_le_neg_two_mean hE hExpI hExpM
  rw [variance_id_map hLm, integral_map hLm (by fun_prop)] at hVarB
  refine ⟨hInvI, hInvB, hLogL2, ?_, hMeanB⟩
  have htwice := mul_le_mul_of_nonneg_left hMeanB (by norm_num : 0 ≤ (2 : ℝ))
  linarith only [hVarB, htwice]

/-- The entrance mass satisfies the exact inverse-fourth, logarithmic variance
and logarithmic mean bounds in equation (6.7). -/
theorem heatStartMass_convexity_moments (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 < a) (haT : a < T) (x : Plane) :
    let A := shfPairing Z a T (fun y => heatKernel a (y - x)) (fun _ => 1)
    Integrable (fun ω => (A ω)⁻¹ ^ 4) P ∧
      (∫ ω, (A ω)⁻¹ ^ 4 ∂P) ≤ (∫ ω, A ω ^ 2 ∂P) ^ 10 ∧
      MemLp (fun ω => Real.log (A ω)) 2 P ∧
      variance (fun ω => Real.log (A ω)) P ≤ Real.log (∫ ω, A ω ^ 2 ∂P) ∧
      -(∫ ω, Real.log (A ω) ∂P) ≤ Real.log (∫ ω, A ω ^ 2 ∂P) / 2 := by
  have hp := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType
    ϑ P Z hZ a T a x (0 : Plane →ᵇ ℝ) ha.le haT ha
  have hg : (fun y : Plane => Real.exp ((0 : Plane →ᵇ ℝ) y)) = fun _ => (1 : ℝ) := by
    funext y
    simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero]
  rw [hg] at hp
  exact convexity_moments_of_positive_mean_one P (heatStartMass_memLp_two ϑ P Z hZ ha haT x)
    hp.1 (heatStartMass_integral_eq_one ϑ P Z hZ ha haT x).2 hp.2.2

/-- Convert the convexity variance and mean bounds into the raw logarithmic
second moment required by the associated-log estimate. -/
theorem integral_log_sq_le_of_convexity_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A : Ω → ℝ} {V : ℝ}
    (hA : MemLp A 2 P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (hmean : (∫ ω, A ω ∂P) = 1) (hV : 1 ≤ V)
    (hAV : (∫ ω, A ω ^ 2 ∂P) ≤ V)
    (hL : MemLp (fun ω => Real.log (A ω)) 2 P)
    (hvar : variance (fun ω => Real.log (A ω)) P ≤ Real.log (∫ ω, A ω ^ 2 ∂P))
    (hneg : -(∫ ω, Real.log (A ω) ∂P) ≤ Real.log (∫ ω, A ω ^ 2 ∂P) / 2) :
    (∫ ω, Real.log (A ω) ^ 2 ∂P) ≤ 4 * (1 + Real.log V) ^ 2 := by
  have hQ : 1 ≤ ∫ ω, A ω ^ 2 ∂P := by
    have hn := variance_nonneg A P
    rw [variance_eq_sub hA, hmean] at hn
    norm_num at hn ⊢
    linarith
  have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one hQ) hAV
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hm : (∫ ω, Real.log (A ω) ∂P) ≤ 0 := by
    have hh := integral_mono_ae (hL.integrable (by norm_num))
      ((hA.integrable (by norm_num)).sub (integrable_const 1))
      (hpos.mono fun ω hω => Real.log_le_sub_one_of_pos hω)
    change (∫ ω, Real.log (A ω) ∂P) ≤ ∫ ω, A ω - 1 ∂P at hh
    rw [integral_sub (hA.integrable (by norm_num)) (integrable_const 1), hmean] at hh
    simpa using hh
  have hm' : -(Real.log V / 2) ≤ ∫ ω, Real.log (A ω) ∂P := by linarith
  have hmsq : (∫ ω, Real.log (A ω) ∂P) ^ 2 ≤ (Real.log V / 2) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ -(∫ ω, Real.log (A ω) ∂P))
      (by linarith : 0 ≤ Real.log V / 2 + (∫ ω, Real.log (A ω) ∂P))]
  rw [variance_eq_sub hL] at hvar
  change (∫ ω, Real.log (A ω) ^ 2 ∂P) - (∫ ω, Real.log (A ω) ∂P) ^ 2 ≤ _ at hvar
  nlinarith [sq_nonneg (Real.log V)]

end Critical2DKPZ.Extensions.GffTangent
