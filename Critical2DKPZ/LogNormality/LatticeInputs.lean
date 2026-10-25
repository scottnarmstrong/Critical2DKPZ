/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.OnePointInverseMomentComparison
public import Critical2DKPZ.FutureProfiles.Basic
public import Critical2DKPZ.FutureProfiles.EndpointTranslation
public import Critical2DKPZ.FutureProfiles.SmoothedEndpointProfile
public import Critical2DKPZ.FutureProfiles.ConditionalMoments
public import Critical2DKPZ.FutureProfiles.ConditionalNegativeMoments
public import Critical2DKPZ.FutureProfiles.ProfileLogTails
public import Critical2DKPZ.FutureProfiles.SplitInputs
public import Critical2DKPZ.Gaussian.TimeBlocks
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Smoothing.EndpointDistribution
public import Critical2DKPZ.Analysis.Lattice.Volume
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Critical2DKPZ.Blocks.GridAlignment
import Critical2DKPZ.LogNormality.Probability
import Critical2DKPZ.MomentBounds.CCR25FreeKernelGaussian
import Critical2DKPZ.OnePoint.BlockRatioOriginalLawGoodSet
import Mathlib.Tactic

/-! # Measurability and moments of lattice polymer masses -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.LogNormality

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer
open Critical2DKPZ.FutureProfiles Critical2DKPZ.Gaussian


private theorem integral_abs_cube_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 4 μ)
    (D d : ℝ) (hD1 : 1 ≤ D) (hd : 0 < d)
    (hfourth : ∫ ω, |X ω| ^ 4 ∂μ ≤ D / d ^ 2) :
    Integrable (fun ω => |X ω| ^ 3) μ ∧
      ∫ ω, |X ω| ^ 3 ∂μ ≤ D / d ^ ((3 : ℝ) / 2) := by
  let G : Ω → ℝ := fun ω => |X ω| ^ 3
  have hXmem4 : MemLp X (ENNReal.ofReal (4 : ℝ)) μ := by simpa using hX
  have hGmem : MemLp G (ENNReal.ofReal ((4 : ℝ) / 3)) μ := by
    have h := hXmem4.norm_rpow_div (3 : ENNReal)
    convert h using 1
    · funext ω
      simp [G, Real.norm_eq_abs]
    · rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
      norm_num
  have hGnonneg (ω : Ω) : 0 ≤ G ω := by positivity
  have hOneMem : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (4 : ℝ)) μ :=
    memLp_const (1 : ℝ)
  have hpq : ((4 : ℝ) / 3).HolderConjugate 4 := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hGnonneg)
    (Filter.Eventually.of_forall fun _ => (show (0 : ℝ) ≤ 1 by norm_num))
    hGmem hOneMem
  have hGpow (ω : Ω) : G ω ^ ((4 : ℝ) / 3) = |X ω| ^ 4 := by
    dsimp [G]
    rw [← Real.rpow_natCast (abs (X ω)) 3, ← Real.rpow_mul (abs_nonneg (X ω))]
    norm_num
  have hHolder' : ∫ ω, G ω ∂μ ≤
      (∫ ω, |X ω| ^ 4 ∂μ) ^ ((3 : ℝ) / 4) := by
    have hpow : ∫ ω, G ω ^ ((4 : ℝ) / 3) ∂μ = ∫ ω, |X ω| ^ 4 ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hGpow
    have hHolderEq : ∫ ω, G ω * 1 ∂μ ≤
        (∫ ω, G ω ^ ((4 : ℝ) / 3) ∂μ) ^ ((3 : ℝ) / 4) := by
      have hq : (1 : ℝ) / ((4 : ℝ) / 3) = (3 : ℝ) / 4 := by norm_num
      have hHolder' := hHolder
      rw [hq] at hHolder'
      simpa using hHolder'
    simpa only [mul_one, hpow] using hHolderEq
  have hroot : (∫ ω, |X ω| ^ 4 ∂μ) ^ ((3 : ℝ) / 4) ≤
      (D / d ^ 2) ^ ((3 : ℝ) / 4) := by
    exact Real.rpow_le_rpow
      (integral_nonneg fun ω => pow_nonneg (abs_nonneg (X ω)) 4) hfourth (by norm_num)
  have hdeq : (d ^ 2) ^ ((3 : ℝ) / 4) = d ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_natCast d 2, ← Real.rpow_mul (le_of_lt hd)]
    norm_num
  have hscale : (D / d ^ 2) ^ ((3 : ℝ) / 4) =
      D ^ ((3 : ℝ) / 4) / d ^ ((3 : ℝ) / 2) := by
    rw [Real.div_rpow (le_trans (by norm_num) hD1) (sq_nonneg d), hdeq]
  have hDpow : D ^ ((3 : ℝ) / 4) ≤ D :=
    Real.rpow_le_self_of_one_le hD1 (by norm_num)
  have hbound : ∫ ω, G ω ∂μ ≤ D / d ^ ((3 : ℝ) / 2) := by
    calc
      ∫ ω, G ω ∂μ ≤ (∫ ω, |X ω| ^ 4 ∂μ) ^ ((3 : ℝ) / 4) := hHolder'
      _ ≤ (D / d ^ 2) ^ ((3 : ℝ) / 4) := hroot
      _ = D ^ ((3 : ℝ) / 4) / d ^ ((3 : ℝ) / 2) := hscale
      _ ≤ D / d ^ ((3 : ℝ) / 2) :=
        div_le_div_of_nonneg_right hDpow (Real.rpow_nonneg hd.le _)
  refine ⟨?_, hbound⟩
  simpa [G] using hGmem.integrable (by norm_num)

private theorem log_defect_moment_bound_aux {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z X Ainv : Ω → ℝ)
    (hZmeas : Measurable Z) (hZpos : ∀ ω, 0 < Z ω)
    (hXmeas : Measurable X) (hXeq : ∀ ω, X ω = Z ω - 1)
    (hX4int : Integrable (fun ω => |X ω| ^ 4) μ)
    (D E d : ℝ) (hD1 : 1 ≤ D) (hE1 : 1 ≤ E)
    (hd1 : 1 ≤ d) (hdpos : 0 < d)
    (hAinvEq : ∀ ω, Ainv ω = (Z ω)⁻¹ + 1)
    (hAinvnonneg : ∀ ω, 0 ≤ Ainv ω)
    (hAinvMem8 : MemLp Ainv (ENNReal.ofReal (8 : ℝ)) μ)
    (hAinv8bound : ∫ ω, Ainv ω ^ 8 ∂μ ≤ E)
    (hfourth : ∫ ω, |X ω| ^ 4 ∂μ ≤ D / d ^ 2)
    (hbadProb : (μ {ω | Z ω < 1 / 2}).toReal ≤ 16 * D / d ^ 2) :
    Integrable (fun ω => (Real.log (Z ω) - X ω) ^ 2) μ ∧
      ∫ ω, (Real.log (Z ω) - X ω) ^ 2 ∂μ ≤
        (9 * D + 16 * D * E) / d ^ ((3 : ℝ) / 2) := by
  let R : Ω → ℝ := fun ω => Real.log (Z ω) - X ω
  let Gbad : Ω → ℝ := fun ω => Ainv ω ^ 2
  let bad : Set Ω := {ω | Z ω < 1 / 2}
  let Hbad : Ω → ℝ := bad.indicator (fun _ => (1 : ℝ))
  have hbadMeas : MeasurableSet bad := measurableSet_lt hZmeas measurable_const
  have hHbadMem : MemLp Hbad (ENNReal.ofReal ((4 : ℝ) / 3)) μ :=
    memLp_indicator_const _ hbadMeas (1 : ℝ) (Or.inr (measure_ne_top μ bad))
  have hGbadmem : MemLp Gbad (ENNReal.ofReal 4) μ := by
    have h := hAinvMem8.norm_rpow_div (2 : ENNReal)
    have hfun : Gbad = fun ω => ‖Ainv ω‖ ^ ENNReal.toReal (2 : ENNReal) := by
      funext ω
      dsimp [Gbad]
      rw [abs_of_nonneg (hAinvnonneg ω)]
      norm_num
    rw [hfun]
    have hindex : ENNReal.ofReal (8 : ℝ) / 2 = ENNReal.ofReal (4 : ℝ) := by
      rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [← hindex]
    exact h
  have hGbadnn (ω : Ω) : 0 ≤ Gbad ω := by positivity
  have hHbadnn : ∀ᵐ ω ∂μ, 0 ≤ Hbad ω :=
    Filter.Eventually.of_forall fun ω => by by_cases hω : ω ∈ bad <;> simp [Hbad, hω]
  have hGbadmem' : MemLp Gbad (ENNReal.ofReal (4 : ℝ)) μ := by simpa using hGbadmem
  have hHbadmem' : MemLp Hbad (ENNReal.ofReal ((4 : ℝ) / 3)) μ := by simpa using hHbadMem
  have hpq : (4 : ℝ).HolderConjugate ((4 : ℝ) / 3) := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hHolderBad := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hGbadnn) hHbadnn hGbadmem' hHbadmem'
  have hGbadpow (ω : Ω) : Gbad ω ^ (4 : ℝ) = Ainv ω ^ (8 : ℝ) := by
    rw [show Gbad ω = Ainv ω ^ 2 by rfl,
      ← Real.rpow_natCast (Ainv ω) 2, ← Real.rpow_mul (hAinvnonneg ω)]
    norm_num
  have hHbadpow (ω : Ω) : Hbad ω ^ ((4 : ℝ) / 3) = Hbad ω := by
    by_cases hω : ω ∈ bad <;> simp [Hbad, hω]
  have hHbadint : ∫ ω, Hbad ω ∂μ = (μ bad).toReal := by
    simpa [Hbad, Measure.real] using integral_indicator_const (1 : ℝ) hbadMeas
  have hGbadmoment : ∫ ω, Gbad ω ^ (4 : ℝ) ∂μ = ∫ ω, Ainv ω ^ (8 : ℝ) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hGbadpow
  have hHbadmoment : ∫ ω, Hbad ω ^ ((4 : ℝ) / 3) ∂μ = (μ bad).toReal := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hHbadpow), hHbadint]
  have hHolderBad' : ∫ ω, Gbad ω * Hbad ω ∂μ ≤
      E ^ ((1 : ℝ) / 4) * (μ bad).toReal ^ ((3 : ℝ) / 4) := by
    have hq : 1 / ((4 : ℝ) / 3) = (3 : ℝ) / 4 := by norm_num
    have hHolder' := hHolderBad
    rw [hGbadmoment, hHbadmoment, hq] at hHolder'
    have hAinv8bound' : ∫ ω, Ainv ω ^ (8 : ℝ) ∂μ ≤ E := by
      calc
        ∫ ω, Ainv ω ^ (8 : ℝ) ∂μ = ∫ ω, Ainv ω ^ 8 ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => Real.rpow_natCast (Ainv ω) 8
        _ ≤ E := hAinv8bound
    have hAinv8nonneg : 0 ≤ ∫ ω, Ainv ω ^ (8 : ℝ) ∂μ :=
      integral_nonneg fun ω => Real.rpow_nonneg (hAinvnonneg ω) _
    have hroot : (∫ ω, Ainv ω ^ (8 : ℝ) ∂μ) ^ ((1 : ℝ) / 4) ≤ E ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow hAinv8nonneg hAinv8bound' (by norm_num)
    exact hHolder'.trans (mul_le_mul_of_nonneg_right hroot (by positivity))
  have hbadHolder : ∫ ω, Gbad ω * Hbad ω ∂μ ≤
      (16 * D * E) / d ^ ((3 : ℝ) / 2) := by
    have h16D : 1 ≤ 16 * D := by
      calc 1 ≤ 16 * 1 := by norm_num
           _ ≤ 16 * D := mul_le_mul_of_nonneg_left hD1 (by norm_num)
    have hdeq : (d ^ 2) ^ ((3 : ℝ) / 4) = d ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast d 2, ← Real.rpow_mul (le_of_lt hdpos)]
      norm_num
    have hscale : (16 * D / d ^ 2) ^ ((3 : ℝ) / 4) ≤
        (16 * D) / d ^ ((3 : ℝ) / 2) := by
      rw [Real.div_rpow (by positivity : 0 ≤ 16 * D) (sq_nonneg d), hdeq]
      have hpow : (16 * D) ^ ((3 : ℝ) / 4) ≤ 16 * D :=
        Real.rpow_le_self_of_one_le h16D (by norm_num)
      exact div_le_div_of_nonneg_right hpow (Real.rpow_nonneg hdpos.le _)
    have hEpow : E ^ ((1 : ℝ) / 4) ≤ E :=
      Real.rpow_le_self_of_one_le hE1 (by norm_num)
    calc
      ∫ ω, Gbad ω * Hbad ω ∂μ ≤ E ^ ((1 : ℝ) / 4) * (μ bad).toReal ^ ((3 : ℝ) / 4) := hHolderBad'
      _ ≤ E ^ ((1 : ℝ) / 4) * (16 * D / d ^ 2) ^ ((3 : ℝ) / 4) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow ENNReal.toReal_nonneg hbadProb (by norm_num))
          (Real.rpow_nonneg (by positivity) _)
      _ ≤ E * ((16 * D) / d ^ ((3 : ℝ) / 2)) :=
        mul_le_mul hEpow hscale (by positivity) (by positivity)
      _ = (16 * D * E) / d ^ ((3 : ℝ) / 2) := by ring
  have hpoint (ω : Ω) : R ω ^ 2 ≤ 9 * |X ω| ^ 4 + Gbad ω * Hbad ω := by
    by_cases hgood : 1 / 2 ≤ Z ω
    · have hinv : (Z ω)⁻¹ ≤ 2 := by
        have hmul : 1 ≤ 2 * Z ω := by nlinarith [hgood]
        have hdiv : 1 / Z ω ≤ 2 :=
          (div_le_iff₀ (hZpos ω)).2 (by nlinarith [hmul])
        simpa only [one_div] using hdiv
      have hlog := abs_log_sub_sub_one_le (hZpos ω)
      have hRabs : |R ω| ≤ 3 * |X ω| ^ 2 := by
        have hfac : 1 + (Z ω)⁻¹ ≤ 3 := by linarith
        have hRlog : R ω = Real.log (Z ω) - (Z ω - 1) := by
          change Real.log (Z ω) - X ω = Real.log (Z ω) - (Z ω - 1)
          rw [hXeq ω]
        rw [hRlog]
        calc
          |Real.log (Z ω) - (Z ω - 1)| ≤ (Z ω - 1) ^ 2 * (1 + (Z ω)⁻¹) := hlog
          _ ≤ |Z ω - 1| ^ 2 * 3 := by
            rw [sq_abs]
            exact mul_le_mul_of_nonneg_left hfac (sq_nonneg _)
          _ = 3 * |X ω| ^ 2 := by rw [← hXeq]; ring
      have hR2 : R ω ^ 2 ≤ 9 * |X ω| ^ 4 := by
        have h := (sq_le_sq₀ (abs_nonneg (R ω)) (by positivity : 0 ≤ 3 * |X ω| ^ 2)).2 hRabs
        rw [sq_abs] at h
        have heq : (3 * |X ω| ^ 2) ^ 2 = 9 * |X ω| ^ 4 := by ring
        rw [heq] at h
        exact h
      have hωnot : ω ∉ bad := by change ¬ Z ω < 1 / 2; exact not_lt.mpr hgood
      have hHzero : Hbad ω = 0 := by simp [Hbad, hωnot]
      simpa [hHzero] using hR2
    · have hbad : Z ω < 1 / 2 := by linarith
      have hRnonpos : R ω ≤ 0 := by
        change Real.log (Z ω) - X ω ≤ 0
        rw [hXeq ω]
        exact sub_nonpos.mpr (Real.log_le_sub_one_of_pos (hZpos ω))
      have hRabs : |R ω| ≤ Ainv ω := by
        rw [abs_of_nonpos hRnonpos]
        have hlog := Real.one_sub_inv_le_log_of_pos (hZpos ω)
        change -(Real.log (Z ω) - X ω) ≤ Ainv ω
        rw [hXeq ω]
        rw [hAinvEq ω]
        nlinarith
      have hR2 : R ω ^ 2 ≤ Ainv ω ^ 2 := by
        have h := (sq_le_sq₀ (abs_nonneg (R ω)) (hAinvnonneg ω)).2 hRabs
        simpa [sq_abs, abs_of_nonneg (hAinvnonneg ω)] using h
      have hω : ω ∈ bad := by change Z ω < 1 / 2; exact hbad
      have hHone : Hbad ω = 1 := by simp [Hbad, hω]
      have hG : Gbad ω = Ainv ω ^ 2 := by rfl
      calc
        R ω ^ 2 ≤ Ainv ω ^ 2 := hR2
        _ ≤ 9 * |X ω| ^ 4 + Gbad ω * Hbad ω := by
          rw [hHone, hG, mul_one]
          have hxnonneg : 0 ≤ 9 * |X ω| ^ 4 := by positivity
          exact le_add_of_nonneg_left hxnonneg
  have hRmeas : Measurable R := (Real.measurable_log.comp hZmeas).sub hXmeas
  have hpqENN : ENNReal.HolderTriple (ENNReal.ofReal ((4 : ℝ) / 3))
      (ENNReal.ofReal 4) 1 := hpq.symm.ennrealOfReal
  have hprodmem : MemLp (fun ω => Gbad ω * Hbad ω) 1 μ := by
    have hprod := @MemLp.mul Ω inferInstance ℝ inferInstance μ
      (ENNReal.ofReal ((4 : ℝ) / 3)) (ENNReal.ofReal 4) 1 Gbad Hbad
      hHbadmem' hGbadmem' hpqENN
    have hEq : (fun ω => Hbad ω * Gbad ω) = (fun ω => Gbad ω * Hbad ω) := by
      funext ω
      ring
    rw [← hEq]
    exact hprod
  have hprodint : Integrable (fun ω => Gbad ω * Hbad ω) μ :=
    hprodmem.integrable (by norm_num)
  have hRrhsInt : Integrable (fun ω => 9 * |X ω| ^ 4 + Gbad ω * Hbad ω) μ :=
    (hX4int.const_mul 9).add hprodint
  have hRint : Integrable (fun ω => R ω ^ 2) μ := by
    apply hRrhsInt.mono' (hRmeas.pow_const 2).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (R ω))]
    exact hpoint ω
  have hRbound : ∫ ω, R ω ^ 2 ∂μ ≤ (9 * D + 16 * D * E) / d ^ ((3 : ℝ) / 2) := by
    calc
      ∫ ω, R ω ^ 2 ∂μ ≤ ∫ ω, (9 * |X ω| ^ 4 + Gbad ω * Hbad ω) ∂μ :=
        integral_mono hRint hRrhsInt (fun ω => hpoint ω)
      _ = 9 * (∫ ω, |X ω| ^ 4 ∂μ) + ∫ ω, Gbad ω * Hbad ω ∂μ := by
        rw [integral_add (hX4int.const_mul 9) hprodint, integral_const_mul]
      _ ≤ 9 * (D / d ^ 2) + (16 * D * E) / d ^ ((3 : ℝ) / 2) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hfourth (by norm_num)) hbadHolder
      _ ≤ (9 * D + 16 * D * E) / d ^ ((3 : ℝ) / 2) := by
        have hExponent : ((3 : ℝ) / 2) ≤ (2 : ℝ) := by norm_num
        have hdenleR : d ^ ((3 : ℝ) / 2) ≤ d ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hd1 hExponent
        have hdenle : d ^ ((3 : ℝ) / 2) ≤ d ^ 2 := by
          rw [← Real.rpow_natCast d 2]
          exact hdenleR
        have hdenpos : 0 < d ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hdpos _
        have hfirst : 9 * (D / d ^ 2) ≤ 9 * D / d ^ ((3 : ℝ) / 2) := by
          have hfrac : 9 * D / d ^ 2 ≤ 9 * D / d ^ ((3 : ℝ) / 2) :=
            div_le_div_of_nonneg_left (by positivity) hdenpos hdenle
          calc
            9 * (D / d ^ 2) = 9 * D / d ^ 2 := by ring
            _ = 9 * D / d ^ 2 := rfl
            _ ≤ 9 * D / d ^ ((3 : ℝ) / 2) := hfrac
        have hcombine : 9 * D / d ^ ((3 : ℝ) / 2) +
            (16 * D * E) / d ^ ((3 : ℝ) / 2) =
            (9 * D + 16 * D * E) / d ^ ((3 : ℝ) / 2) := by ring
        rw [← hcombine]
        exact add_le_add hfirst le_rfl
  exact ⟨hRint, hRbound⟩

/-- The block-moment estimate bounds the third absolute centred moment and the second moment of
the logarithmic Taylor remainder, with the stated decay in the remaining number of blocks. -/
theorem blockMass_log_moments_of (hC6 : BlockMomentsBound) (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i ≤ blockCount N ρ →
        Integrable (fun ω => |blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω - 1| ^ 3) disorderLaw ∧
        ∫ ω, |blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω - 1| ^ 3 ∂disorderLaw ≤
          C / ((blockCount N ρ : ℝ) + 1 - i) ^ ((3 : ℝ) / 2) ∧
        Integrable (fun ω => (Real.log (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω) -
          (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω - 1)) ^ 2) disorderLaw ∧
        ∫ ω, (Real.log (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω) -
            (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω - 1)) ^ 2 ∂disorderLaw ≤
          C / ((blockCount N ρ : ℝ) + 1 - i) ^ ((3 : ℝ) / 2) := by
  obtain ⟨C₆, hC₆⟩ := hC6 A ρ₀ ρ₁ hρ
  let D : ℝ := max C₆ 1
  let E : ℝ := 128 * ((1 + D) ^ 36 + 1)
  let C : ℝ := 9 * D + 16 * D * E
  have hD1 : 1 ≤ D := by dsimp [D]; exact le_max_right _ _
  have hDC₆ : C₆ ≤ D := by dsimp [D]; exact le_max_left _ _
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD1
  have hE1 : 1 ≤ E := by
    dsimp [E]
    have hbase : 0 ≤ 1 + D := by linarith
    have hpow : 0 ≤ (1 + D) ^ 36 := pow_nonneg hbase 36
    nlinarith
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, ?_⟩
  intro ρ hρρ
  filter_upwards [hC₆ ρ hρρ] with N hN
  intro ϑ hϑ i hi hiK
  let β : ℝ := criticalBeta ϑ N
  let t : ℕ → ℕ := blockTime N ρ
  let Z : Disorder → ℝ := blockMass β t i
  let X : Disorder → ℝ := fun ω => Z ω - 1
  let d : ℝ := (blockCount N ρ : ℝ) + 1 - i
  have hdcast : ((blockCount N ρ + 1 - i : ℕ) : ℝ) = d := by
    dsimp [d]
    rw [Nat.cast_sub (by omega : i ≤ blockCount N ρ + 1), Nat.cast_add]
    norm_num
  have hd1 : 1 ≤ d := by
    have hnat : 1 ≤ blockCount N ρ + 1 - i := by omega
    rw [← hdcast]
    exact_mod_cast hnat
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd1
  have hZpos (ω : Disorder) : 0 < Z ω := by
    exact blockMass_pos β t i ω
  have hZmeas : Measurable Z := by
    dsimp [Z]
    exact (measurable_blockMass β t i).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hXmeas : Measurable X := by dsimp [X]; exact hZmeas.sub measurable_const
  have hmean : ∫ ω, Z ω ∂disorderLaw = 1 := by
    dsimp [Z, blockMass, β, t]
    exact Polymer.integral_smoothedP2Plane _ _ _ _
  have hZmem2 : MemLp Z 2 disorderLaw := by
    dsimp [Z, blockMass, β, t]
    exact Polymer.memLp_smoothedP2Plane _ _ _ _ 2 (by norm_num)
  have hvarEq : Var[Z; disorderLaw] = (∫ ω, Z ω ^ 2 ∂disorderLaw) - 1 := by
    rw [ProbabilityTheory.variance_eq_sub hZmem2, hmean]
    norm_num
  have hC6at := hN ϑ hϑ i hi hiK
  have hvarD : Var[Z; disorderLaw] ≤ D := by
    have hdiv : C₆ / d ≤ D := by
      rw [div_le_iff₀ hdpos]
      have hDmul : D ≤ D * d := by nlinarith [mul_le_mul_of_nonneg_left hd1 hDpos.le]
      nlinarith [hDC₆]
    have hden : ((blockCount N ρ : ℝ) + 1 - i) = d := by rfl
    rw [hden] at hC6at
    exact hC6at.1.trans hdiv
  have hsecond : ∫ ω, Z ω ^ 2 ∂disorderLaw ≤ 1 + D := by
    rw [hvarEq] at hvarD
    linarith
  have hfourth : ∫ ω, |X ω| ^ 4 ∂disorderLaw ≤ D / d ^ 2 := by
    have hden : ((blockCount N ρ : ℝ) + 1 - i) = d := by rfl
    rw [hden] at hC6at
    have hraw := hC6at.2
    have hraw' : ∫ ω, |X ω| ^ 4 ∂disorderLaw ≤ C₆ / d ^ 2 := by
      simpa [X, Z, β, t, blockMass] using hraw
    calc
      ∫ ω, |X ω| ^ 4 ∂disorderLaw ≤ C₆ / d ^ 2 := hraw'
      _ ≤ D / d ^ 2 := div_le_div_of_nonneg_right hDC₆ (sq_nonneg d)
  have hXmem4 : MemLp X 4 disorderLaw := by
    dsimp [X, Z]
    exact (Polymer.memLp_smoothedP2Plane β (t (i - 1)) (t i) 0 4 (by norm_num)).sub
      (memLp_const (1 : ℝ))
  have hX4int : Integrable (fun ω => |X ω| ^ 4) disorderLaw := by
    have h := hXmem4.integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using h
  have hthirdData := integral_abs_cube_bound disorderLaw X hXmem4 D d hD1 hdpos hfourth
  let ν : Site → ℝ := fun y => srwKernel (t (i - 1)) (y - (0 : Site))
  let F : Finset Site := Polymer.endpoints (0 : Site) (t (i - 1))
  have hνF : ∀ y ∉ F, ν y = 0 := by
    intro y hy
    exact Polymer.srwKernel_eq_zero_of_not_mem _ 0 y (by simpa [F, ν] using hy)
  have hνnn : ∀ y, 0 ≤ ν y := fun y => Polymer.kernel_nonneg _ (y - (0 : Site))
  have hνmass : ∑ y ∈ F, ν y = 1 := Polymer.sum_srwKernel_endpoints _ 0
  have hprofile (ω : Disorder) :
      profileP2Fun β (t (i - 1)) (t i) ν (fun _ => 1) ω = Z ω := by
    dsimp [Z, blockMass, β, t, ν]
    exact Polymer.profileP2Fun_srw_flat _ _ _ _ _
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; exact Real.sqrt_nonneg _
  have hnegative := OnePoint.integral_rpow_neg_profileP2Fun_le hβ
    (t (i - 1)) (t i) ν F hνF hνnn hνmass (p := 8) (by norm_num)
  have hnegative' : ∫ ω, Z ω ^ (-8 : ℝ) ∂disorderLaw ≤
      (∫ ω, Z ω ^ 2 ∂disorderLaw) ^ (36 : ℝ) := by
    have hpow : (8 : ℝ) * (8 + 1) / 2 = 36 := by norm_num
    rw [hpow] at hnegative
    simpa only [hprofile] using hnegative
  have hZnegpow (ω : Disorder) : Z ω ^ (-8 : ℝ) = (Z ω)⁻¹ ^ 8 := by
    calc
      Z ω ^ (-8 : ℝ) = (Z ω ^ (8 : ℝ))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt (hZpos ω))]
      _ = (Z ω ^ 8)⁻¹ := congrArg Inv.inv (Real.rpow_natCast (Z ω) 8)
      _ = (Z ω)⁻¹ ^ 8 := (inv_pow (Z ω) 8).symm
  have hZinv8 : Integrable (fun ω => (Z ω)⁻¹ ^ 8) disorderLaw := by
    have hpow : Integrable (fun ω => Z ω ^ (-8 : ℝ)) disorderLaw := by
      simpa [Z, blockMass, β, t] using
        integrable_rpow_smoothedP2Plane β (t (i - 1)) (t i) 0 (-8 : ℝ)
    rw [← funext hZnegpow]
    exact hpow
  have hZinv8bound : ∫ ω, (Z ω)⁻¹ ^ 8 ∂disorderLaw ≤ (1 + D) ^ 36 := by
    have heq : ∫ ω, (Z ω)⁻¹ ^ 8 ∂disorderLaw = ∫ ω, Z ω ^ (-8 : ℝ) ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => (hZnegpow ω).symm
    calc
      _ = ∫ ω, Z ω ^ (-8 : ℝ) ∂disorderLaw := heq
      _ ≤ (∫ ω, Z ω ^ 2 ∂disorderLaw) ^ (36 : ℝ) := hnegative'
      _ ≤ (1 + D) ^ (36 : ℝ) := by
        apply Real.rpow_le_rpow
        · exact integral_nonneg (fun ω => sq_nonneg (Z ω))
        · exact hsecond
        · norm_num
      _ = (1 + D) ^ 36 := Real.rpow_natCast _ _
  let Ainv : Disorder → ℝ := fun ω => (Z ω)⁻¹ + 1
  have hAinvmeas : Measurable Ainv := by
    dsimp [Ainv]
    exact hZmeas.inv.add measurable_const
  have hAinvnonneg (ω : Disorder) : 0 ≤ Ainv ω := by
    dsimp [Ainv]
    exact add_nonneg (inv_nonneg.mpr (hZpos ω).le) (by norm_num)
  have hAinvMem8 : MemLp Ainv (ENNReal.ofReal (8 : ℝ)) disorderLaw := by
    have hZinvMem8 : MemLp (fun ω => (Z ω)⁻¹) (ENNReal.ofReal (8 : ℝ)) disorderLaw := by
      apply (integrable_norm_rpow_iff (hZmeas.inv.aestronglyMeasurable)
        (by norm_num) (by simp)).mp
      have heq (ω : Disorder) : ‖(Z ω)⁻¹‖ ^ (8 : ℝ) = (Z ω)⁻¹ ^ 8 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hZpos ω).le)]
        exact Real.rpow_natCast _ _
      rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 8)]
      convert hZinv8 using 1
      · funext ω
        exact heq ω
    have hOne : MemLp (fun _ : Disorder => (1 : ℝ)) (ENNReal.ofReal (8 : ℝ)) disorderLaw :=
      memLp_const (1 : ℝ)
    change MemLp ((fun ω => (Z ω)⁻¹) + (fun _ : Disorder => (1 : ℝ)))
      (ENNReal.ofReal (8 : ℝ)) disorderLaw
    exact hZinvMem8.add hOne
  have hAinv8 : Integrable (fun ω => Ainv ω ^ 8) disorderLaw := by
    have hAinvMem8' : MemLp Ainv 8 disorderLaw := by simpa using hAinvMem8
    have h := hAinvMem8'.integrable_norm_pow'
    have heq (ω : Disorder) : ‖Ainv ω‖ ^ 8 = Ainv ω ^ 8 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hAinvnonneg ω)]
    have h' : Integrable (fun ω => ‖Ainv ω‖ ^ 8) disorderLaw := h
    rw [← funext heq]
    exact h'
  have hAinv8bound : ∫ ω, Ainv ω ^ 8 ∂disorderLaw ≤ E := by
    have hpoint (ω : Disorder) : Ainv ω ^ 8 ≤
        128 * ((Z ω)⁻¹ ^ 8 + 1) := by
      dsimp [Ainv]
      have hInvnn : 0 ≤ (Z ω)⁻¹ := inv_nonneg.mpr (hZpos ω).le
      calc
        ((Z ω)⁻¹ + 1) ^ 8 ≤ 2 ^ 7 * ((Z ω)⁻¹ ^ 8 + 1 ^ 8) :=
          add_pow_le hInvnn (by norm_num) 8
        _ = 128 * ((Z ω)⁻¹ ^ 8 + 1) := by norm_num
    have hmajor : Integrable (fun ω => 128 * ((Z ω)⁻¹ ^ 8 + 1)) disorderLaw := by
      exact (hZinv8.add (integrable_const (1 : ℝ))).const_mul 128
    calc
      ∫ ω, Ainv ω ^ 8 ∂disorderLaw ≤
          ∫ ω, 128 * ((Z ω)⁻¹ ^ 8 + 1) ∂disorderLaw :=
        integral_mono hAinv8 hmajor (fun ω => hpoint ω)
      _ = 128 * ((∫ ω, (Z ω)⁻¹ ^ 8 ∂disorderLaw) + 1) := by
        rw [integral_const_mul, integral_add hZinv8 (integrable_const (1 : ℝ)), integral_const]
        simp
      _ ≤ E := by
        dsimp [E]
        have hsum := add_le_add_left hZinv8bound 1
        nlinarith
  let bad : Set Disorder := {ω | Z ω < 1 / 2}
  have hbadProb : (disorderLaw bad).toReal ≤ 16 * D / d ^ 2 := by
    have hmarkov := OnePoint.measure_abs_gt_half_le_integral_four X hXmeas hX4int
    have hsubset : bad ⊆ {ω | (1 / 2 : ℝ) < |X ω|} := by
      intro ω hω
      dsimp [bad] at hω
      dsimp [X]
      rw [abs_of_neg (by linarith [hω])]
      linarith
    have hmeasure : disorderLaw bad ≤ disorderLaw {ω | (1 / 2 : ℝ) < |X ω|} :=
      measure_mono hsubset
    have htoReal := ENNReal.toReal_mono (measure_ne_top disorderLaw _) hmeasure
    calc
      (disorderLaw bad).toReal ≤
          (disorderLaw {ω | (1 / 2 : ℝ) < |X ω|}).toReal := htoReal
      _ ≤ 16 * ∫ ω, |X ω| ^ 4 ∂disorderLaw := hmarkov
      _ ≤ 16 * (D / d ^ 2) := mul_le_mul_of_nonneg_left hfourth (by norm_num)
      _ = 16 * D / d ^ 2 := by ring
  have hlogData := log_defect_moment_bound_aux disorderLaw Z X Ainv hZmeas hZpos hXmeas
    (by intro ω; rfl) hX4int D E d hD1 hE1 hd1 hdpos
    (by intro ω; rfl) hAinvnonneg hAinvMem8 hAinv8bound hfourth hbadProb
  have hGintTarget : Integrable (fun ω =>
      |blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω - 1| ^ 3) disorderLaw := by
    simpa [X, Z, β, t, blockMass] using hthirdData.1
  have hDleC : D ≤ C := by
    change D ≤ 9 * D + 16 * D * E
    calc
      D ≤ 9 * D := le_mul_of_one_le_left hDpos.le (by norm_num)
      _ ≤ 9 * D + 16 * D * E := le_add_of_nonneg_right
        (mul_nonneg (mul_nonneg (by norm_num) hDpos.le) (zero_le_one.trans hE1))
  refine ⟨hGintTarget, ?_, hlogData.1, ?_⟩
  · calc
      ∫ ω, |blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω - 1| ^ 3 ∂disorderLaw ≤
          D / d ^ ((3 : ℝ) / 2) := by
            simpa [X, Z, β, t, blockMass] using hthirdData.2
      _ ≤ C / d ^ ((3 : ℝ) / 2) :=
        div_le_div_of_nonneg_right hDleC (Real.rpow_nonneg hdpos.le _)
  · simpa [X, Z, β, t, blockMass, d, C] using hlogData.2

/-- The logarithm of a smoothed lattice mass has variance bounded by its second-moment log. -/
theorem variance_log_smoothedP2Plane_le {β : ℝ} (hβ : 0 ≤ β) (s n : ℕ) (x : Site) :
    MemLp (fun ω => Real.log (smoothedP2Plane β s n x ω)) 2 disorderLaw ∧
    Var[fun ω => Real.log (smoothedP2Plane β s n x ω); disorderLaw] ≤
      2 * Real.log (∫ ω, smoothedP2Plane β s n x ω ^ 2 ∂disorderLaw) := by
  have _ : 0 ≤ β := hβ
  let Z : Disorder → ℝ := smoothedP2Plane β s n x
  have hZpos (ω : Disorder) : 0 < Z ω := Polymer.smoothedP2Plane_pos β s n x ω
  have hprofileSupport (y : Site) (hy : y ∉ Polymer.endpoints x s) :
      srwKernel s (y - x) = 0 :=
    Polymer.srwKernel_eq_zero_of_not_mem s x y (by simpa using hy)
  have hprofileNonneg (y : Site) : 0 ≤ srwKernel s (y - x) :=
    Polymer.kernel_nonneg s (y - x)
  have hprofileMass : ∑ y ∈ Polymer.endpoints x s, srwKernel s (y - x) = 1 :=
    Polymer.sum_srwKernel_endpoints s x
  let F : Disorder → ℝ := fun ω => Real.log
    (profileP2Fun β s n (fun y => srwKernel s (y - x)) (fun _ => 1) ω)
  have hprofileEq (ω : Disorder) :
      profileP2Fun β s n (fun y => srwKernel s (y - x)) (fun _ => 1) ω = Z ω := by
    exact Polymer.profileP2Fun_srw_flat β s n x ω
  have hF : F = fun ω => Real.log (Z ω) := by
    funext ω
    simp only [F, hprofileEq]
  have hbounds := profileP2Fun_log_moment_bounds β s n
    (fun y => srwKernel s (y - x)) (Polymer.endpoints x s)
    hprofileSupport hprofileNonneg hprofileMass
  have hvar : Var[fun ω => Real.log (Z ω); disorderLaw] ≤
      -2 * (∫ ω, Real.log (Z ω) ∂disorderLaw) := by
    simpa only [← hF] using hbounds.2.1
  have hmgf : mgf F disorderLaw 2 = ∫ ω, Z ω ^ 2 ∂disorderLaw := by
    calc
      _ = ∫ ω, profileP2Fun β s n (fun y => srwKernel s (y - x))
          (fun _ => 1) ω ^ (2 : ℝ) ∂disorderLaw :=
        mgf_log_eq_integral_rpow
          (profileP2Fun_pos_of_normalized β s n _ (Polymer.endpoints x s)
            hprofileSupport hprofileNonneg hprofileMass) 2
      _ = ∫ ω, Z ω ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        calc
          _ = Z ω ^ (2 : ℝ) := congrArg (fun z : ℝ => z ^ (2 : ℝ)) (hprofileEq ω)
          _ = Z ω ^ 2 := Real.rpow_natCast _ _
  have hmeanBound :
      -2 * (∫ ω, Real.log (Z ω) ∂disorderLaw) ≤
        Real.log (∫ ω, Z ω ^ 2 ∂disorderLaw) := by
    calc
      _ = -2 * (∫ ω, F ω ∂disorderLaw) := by rw [← hF]
      _ ≤ Real.log (mgf F disorderLaw 2) := hbounds.2.2.1
      _ = _ := by rw [hmgf]
  have hMmem : MemLp Z 2 disorderLaw :=
    Polymer.memLp_smoothedP2Plane β s n x 2 (by norm_num)
  have hmean : ∫ ω, Z ω ∂disorderLaw = 1 := by
    dsimp [Z]
    exact Polymer.integral_smoothedP2Plane β s n x
  have hMge : 1 ≤ ∫ ω, Z ω ^ 2 ∂disorderLaw := by
    have hv := variance_nonneg Z disorderLaw
    rw [variance_eq_sub hMmem, hmean] at hv
    norm_num at hv ⊢
    linarith
  have hlognonneg : 0 ≤ Real.log (∫ ω, Z ω ^ 2 ∂disorderLaw) :=
    Real.log_nonneg hMge
  have hmeasLog : AEStronglyMeasurable (fun ω => Real.log (Z ω)) disorderLaw :=
    (Real.measurable_log.comp (Polymer.measurable_smoothedP2Plane β s n x)).aestronglyMeasurable
  have hpow2 := integrable_rpow_smoothedP2Plane β s n x (2 : ℝ)
  have hpowNeg2 := integrable_rpow_smoothedP2Plane β s n x (-2 : ℝ)
  have hpow2' : Integrable (fun ω => Z ω ^ 2) disorderLaw := by
    simpa [Z, Real.rpow_natCast] using hpow2
  have hpowNeg2' : Integrable (fun ω => (Z ω)⁻¹ ^ 2) disorderLaw := by
    have heq (ω : Disorder) : Z ω ^ (-2 : ℝ) = (Z ω)⁻¹ ^ 2 := by
      calc
        Z ω ^ (-2 : ℝ) = (Z ω)⁻¹ ^ (2 : ℝ) := Real.rpow_neg_eq_inv_rpow _ _
        _ = (Z ω)⁻¹ ^ 2 := Real.rpow_natCast _ _
    simpa only [Z] using hpowNeg2.congr (Filter.Eventually.of_forall heq)
  have hmajor : Integrable (fun ω => 2 * (Z ω ^ 2 + (Z ω)⁻¹ ^ 2)) disorderLaw := by
    exact (hpow2'.add hpowNeg2').const_mul 2
  have hlogSquared : Integrable (fun ω => Real.log (Z ω) ^ 2) disorderLaw := by
    apply hmajor.mono' (by fun_prop)
    filter_upwards [] with ω
    have hlogabs : |Real.log (Z ω)| ≤ Z ω + (Z ω)⁻¹ := by
      apply abs_le.mpr
      constructor
      · have h := Real.one_sub_inv_le_log_of_pos (hZpos ω)
        have hZnn : 0 ≤ Z ω := (hZpos ω).le
        have hinvnn : 0 ≤ (Z ω)⁻¹ := inv_nonneg.mpr hZnn
        linarith
      · have h := Real.log_le_sub_one_of_pos (hZpos ω)
        have hinvnn : 0 ≤ (Z ω)⁻¹ := inv_nonneg.mpr (hZpos ω).le
        linarith
    have hsumNonneg : 0 ≤ Z ω + (Z ω)⁻¹ :=
      add_nonneg (hZpos ω).le (inv_nonneg.mpr (hZpos ω).le)
    have habsSq : (Real.log (Z ω)) ^ 2 ≤ (Z ω + (Z ω)⁻¹) ^ 2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (Real.log (Z ω))) hsumNonneg).2 hlogabs
    have hsq := sq_nonneg (Z ω - (Z ω)⁻¹)
    have hnorm : ‖Real.log (Z ω) ^ 2‖ = (Real.log (Z ω)) ^ 2 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [hnorm]
    nlinarith
  have hmemLog : MemLp (fun ω => Real.log (Z ω)) 2 disorderLaw :=
    (memLp_two_iff_integrable_sq hmeasLog).2 hlogSquared
  refine ⟨?_, ?_⟩
  · simpa [Z] using hmemLog
  · calc
      Var[fun ω => Real.log (Z ω); disorderLaw] ≤
          -2 * (∫ ω, Real.log (Z ω) ∂disorderLaw) := hvar
      _ ≤ Real.log (∫ ω, Z ω ^ 2 ∂disorderLaw) := hmeanBound
      _ ≤ 2 * Real.log (∫ ω, Z ω ^ 2 ∂disorderLaw) := by linarith
      _ = 2 * Real.log (∫ ω, smoothedP2Plane β s n x ω ^ 2 ∂disorderLaw) := by rfl

/-- The profile-good event through block `s` is measurable with respect to the past at `t s`. -/
theorem measurableSet_profileGoodSet_past (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    MeasurableSet[disorderPast (t s)] (profileGoodSet β t r s) := by
  have hmass (i : ℕ) (hi : i ∈ Finset.Icc r s) :
      Measurable[disorderPast (t s)] (blockMass β t i) := by
    have hi' := Finset.mem_Icc.mp hi
    have hti : t i ≤ t s := ht hi'.2
    have hblock := Gaussian.disorderBlock_mono
      (m := t (i - 1)) (n := t i) (a := 0) (b := t s) (Nat.zero_le _) hti
    change Measurable[Gaussian.disorderBlock 0 (t s)] (blockMass β t i)
    exact (measurable_blockMass β t i).mono hblock le_rfl
  have hgood : MeasurableSet[disorderPast (t s)] (blockGoodSet β t r s) := by
    have h : MeasurableSet[disorderPast (t s)]
        (⋂ i ∈ Finset.Icc r s, {ω | |blockMass β t i ω - 1| ≤ 1 / 2}) := by
      apply Finset.measurableSet_biInter
      intro i hi
      apply measurableSet_le
      · have hdev : Measurable[disorderPast (t s)]
            (fun ω => blockMass β t i ω - (1 : ℝ)) :=
          (measurable_sub_const 1).comp (hmass i hi)
        exact continuous_abs.measurable.comp hdev
      · exact measurable_const
    convert h using 1
    ext ω
    simp [blockGoodSet]
  have hnum : Measurable[disorderPast (t s)]
      (fun ω => smoothedP2Plane β (t (r - 1)) (t s) 0 ω) := by
    have htimes : t (r - 1) ≤ t s := ht (by omega)
    have hblock := Polymer.measurable_smoothedP2Plane_block β
      (t (r - 1)) (t s) htimes 0
    have hsub := Gaussian.disorderBlock_mono
      (m := t (r - 1)) (n := t s) (a := 0) (b := t s) (Nat.zero_le _) le_rfl
    change Measurable[Gaussian.disorderBlock 0 (t s)]
      (fun ω => smoothedP2Plane β (t (r - 1)) (t s) 0 ω)
    exact hblock.mono hsub le_rfl
  have hden : Measurable[disorderPast (t s)]
      (fun ω => ∏ i ∈ Finset.Icc r s, blockMass β t i ω) := by
    apply Finset.measurable_prod
    intro i hi
    exact hmass i hi
  have hratio : Measurable[disorderPast (t s)] (blockRatio β t r s) := by
    change Measurable[disorderPast (t s)]
      (fun ω => smoothedP2Plane β (t (r - 1)) (t s) 0 ω /
        ∏ i ∈ Finset.Icc r s, blockMass β t i ω)
    exact hnum.div hden
  rw [profileGoodSet]
  refine MeasurableSet.inter hgood ?_
  apply measurableSet_le
  · have hdev : Measurable[disorderPast (t s)]
        (fun ω => blockRatio β t r s ω - (1 : ℝ)) :=
      (measurable_sub_const 1).comp hratio
    exact continuous_abs.measurable.comp hdev
  · exact measurable_const


/-- On events measurable up to time `M`, the reciprocal smoothed mass ratio has integral bounded
by the corresponding future profile energy. -/
theorem setIntegral_inv_smoothedP2Plane_div_le {β : ℝ} (hβ : 0 ≤ β) {m M N : ℕ}
    (hmM : m ≤ M) (hMN : M ≤ N) (x : Site) (G : Set Disorder)
    (hG : MeasurableSet[disorderPast M] G) :
    ∫ ω in G, (smoothedP2Plane β m N x ω / smoothedP2Plane β m M x ω)⁻¹ ∂disorderLaw ≤
      ∫ ω in G, futureEnergy β M N (smoothedEndpointDist β m M x ω) ∂disorderLaw := by
  classical
  let A : Finset Site := (Polymer.endpoints x m).biUnion
    (fun y => Polymer.endpoints y (M - m))
  let η : Disorder → Site → ℝ := fun ω => smoothedEndpointDist β m M x ω
  have hprob := Smoothing.smoothedEndpointDist_probability β hmM x
  have hsupp (ω : Disorder) (w : Site) (hw : w ∉ A) : η ω w = 0 := by
    exact (hprob ω).1 w (by simpa [A] using hw)
  have hnn (ω : Disorder) (w : Site) : 0 ≤ η ω w := (hprob ω).2.1 w
  have hmass (ω : Disorder) : ∑ w ∈ A, η ω w = 1 := by
    simpa [A, η] using (hprob ω).2.2
  have hmeas (w : Site) : Measurable[disorderPast M] (η · w) := by
    dsimp [η]
    have hsub : Gaussian.disorderBlock m M ≤ disorderPast M := by
      rw [← Gaussian.disorderBlock_zero M]
      exact Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl
    exact (Polymer.measurable_smoothedEndpointDist_block β m M hmM x w).mono hsub le_rfl
  have hratio (ω : Disorder) :
      smoothedP2Plane β m N x ω / smoothedP2Plane β m M x ω =
        profileP2Fun β M N (η ω) (fun _ => 1) ω := by
    symm
    exact FutureProfiles.profileP2Fun_smoothedEndpointDist_eq_div β hmM hMN x ω
  have hneg := FutureProfiles.setIntegral_rpow_neg_profileP2Fun_le β hβ hMN η A
    hsupp hnn hmass hmeas G hG (p := 1) (by norm_num)
  have hGambient : MeasurableSet G := by
    have hPast : disorderPast M ≤ (inferInstance : MeasurableSpace Disorder) := by
      rw [← Gaussian.disorderBlock_zero M]
      exact Gaussian.disorderBlock_le 0 M
    exact hPast G hG
  have hprofileInvEq :
      ∫ ω in G, (profileP2Fun β M N (η ω) (fun _ => 1) ω)⁻¹ ∂disorderLaw =
        ∫ ω in G, profileP2Fun β M N (η ω) (fun _ => 1) ω ^ (-1 : ℝ) ∂disorderLaw := by
    apply setIntegral_congr_ae hGambient
    filter_upwards with ω hω
    exact (Real.rpow_neg_one _).symm
  have henergyEq :
      ∫ ω in G, futureEnergy β M N (η ω) ^ ((1 : ℝ) * (1 + 1) / 2) ∂disorderLaw =
        ∫ ω in G, futureEnergy β M N (η ω) ∂disorderLaw := by
    apply setIntegral_congr_ae hGambient
    filter_upwards with ω hω
    convert Real.rpow_one (futureEnergy β M N (η ω)) using 1
    norm_num
  have hnegInv :
      ∫ ω in G, (profileP2Fun β M N (η ω) (fun _ => 1) ω)⁻¹ ∂disorderLaw ≤
        ∫ ω in G, futureEnergy β M N (η ω) ∂disorderLaw := by
    calc
      _ = ∫ ω in G, profileP2Fun β M N (η ω) (fun _ => 1) ω ^ (-1 : ℝ) ∂disorderLaw :=
        hprofileInvEq
      _ ≤ ∫ ω in G, futureEnergy β M N (η ω) ^ (1 * (1 + 1) / 2) ∂disorderLaw := hneg
      _ = ∫ ω in G, futureEnergy β M N (η ω) ∂disorderLaw := henergyEq
  calc
    ∫ ω in G, (smoothedP2Plane β m N x ω / smoothedP2Plane β m M x ω)⁻¹ ∂disorderLaw =
        ∫ ω in G, (profileP2Fun β M N (η ω) (fun _ => 1) ω)⁻¹ ∂disorderLaw := by
          apply setIntegral_congr_ae hGambient
          filter_upwards with ω hω
          rw [hratio ω]
    _ ≤ ∫ ω in G, futureEnergy β M N (η ω) ∂disorderLaw := hnegInv

/-- Under the profile estimates, the log mass ratio on the final interval has upper tail at most
`exp (-r)` and lower tail at most `C / ℓ + C * ℓ * exp (-r)`. -/
theorem lastInterval_log_tail_of (hPE : ProfileEstimatesBound) (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ (C : ℝ) (ℓ₀ : ℕ),
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ a ℓ : ℕ, ℓ₀ ≤ ℓ →
          a + ℓ + 1 ≤ blockCount N ρ → ∀ r : ℝ, 0 ≤ r →
            (disorderLaw {ω | Real.log
                (smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ a) N 0 ω /
                  smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ a)
                    (blockTime N ρ (blockCount N ρ - ℓ)) 0 ω) < -r}).toReal ≤
              C / ℓ + C * ℓ * Real.exp (-r) ∧
            (disorderLaw {ω | r < Real.log
                (smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ a) N 0 ω /
                  smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ a)
                    (blockTime N ρ (blockCount N ρ - ℓ)) 0 ω)}).toReal ≤ Real.exp (-r) := by
  obtain ⟨ρ₀, hρ₀, hPEρ⟩ := hPE A
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨C₀, ℓPE, hPEbound⟩ := hPEρ ρ₁
  let C : ℝ := |C₀| + 1
  let ℓ₀ : ℕ := max ℓPE 1
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith [abs_nonneg C₀, le_abs_self C₀]
  refine ⟨C, ℓ₀, ?_⟩
  intro ρ hρρ
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρρ.1
  filter_upwards [hPEbound ρ hρρ, Critical2DKPZ.Blocks.blockTime_monotone hρ,
    (Critical2DKPZ.Blocks.blockCount_tendsto_atTop hρ).eventually_ge_atTop 1]
    with N hPEat htimeMono hKone
  intro ϑ hϑ a ℓ hℓ hindex r hr
  let K : ℕ := blockCount N ρ
  let t : ℕ → ℕ := blockTime N ρ
  let u : ℕ := a + 1
  let s : ℕ := K - ℓ
  let β : ℝ := criticalBeta ϑ N
  let m : ℕ := t a
  let M : ℕ := t s
  let G : Set Disorder := profileGoodSet β t u s
  let η : Disorder → Site → ℝ := fun ω => smoothedEndpointDist β m M 0 ω
  let X : Disorder → ℝ := fun ω => smoothedP2Plane β m N 0 ω / smoothedP2Plane β m M 0 ω
  have hKone : 1 ≤ K := by change 1 ≤ blockCount N ρ at hKone; simpa [K] using hKone
  have hEllOne : 1 ≤ ℓ := le_trans (le_max_right ℓPE 1) hℓ
  have hEllK : ℓ ≤ K := by dsimp [K]; omega
  have hKtime : t K = N := by
    simp [t, K, Critical2DKPZ.blockTime, Nat.ne_of_gt hKone]
  have hus : 1 ≤ u := by dsimp [u]; omega
  have hus' : u ≤ s := by dsimp [u, s, K]; omega
  have hsk : s ≤ K := by dsimp [s]; omega
  have hma : a ≤ s := by dsimp [s, K]; omega
  have hmM : m ≤ M := by dsimp [m, M]; exact htimeMono hma
  have hMN : M ≤ N := by rw [← hKtime]; dsimp [M]; exact htimeMono hsk
  have hsPE : s + ℓPE ≤ K := by dsimp [s]; omega
  have hPEdata := hPEat ϑ hϑ u s hus hus' hsPE
  have hGmeas : MeasurableSet[disorderPast M] G := by
    simpa [G, M] using measurableSet_profileGoodSet_past β htimeMono hus hus'
  have hPast : disorderPast M ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero M]
    exact Gaussian.disorderBlock_le 0 M
  have hGambient : MeasurableSet G := hPast G hGmeas
  let B : Finset Site := (Polymer.endpoints (0 : Site) m).biUnion
    (fun y => Polymer.endpoints y (M - m))
  have hprob := Smoothing.smoothedEndpointDist_probability β hmM (0 : Site)
  have hsupp (ω : Disorder) (w : Site) (hw : w ∉ B) : η ω w = 0 := by
    exact (hprob ω).1 w (by simpa [B, η] using hw)
  have hnn (ω : Disorder) (w : Site) : 0 ≤ η ω w := (hprob ω).2.1 w
  have hmass (ω : Disorder) : ∑ w ∈ B, η ω w = 1 := by
    simpa [B, η] using (hprob ω).2.2
  have hbdd : ∃ D : ℝ, ∀ ω w, |η ω w| ≤ D := by
    refine ⟨1, fun ω w => ?_⟩
    rw [abs_of_nonneg (hnn ω w)]
    by_cases hw : w ∈ B
    · exact (Finset.single_le_sum (fun v hv => hnn ω v) hw).trans_eq (hmass ω)
    · rw [hsupp ω w hw]
      norm_num
  have hmeas (w : Site) : Measurable[disorderPast M] (η · w) := by
    dsimp [η]
    have hsub : Gaussian.disorderBlock m M ≤ disorderPast M := by
      rw [← Gaussian.disorderBlock_zero M]
      exact Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl
    exact (Polymer.measurable_smoothedEndpointDist_block β m M hmM 0 w).mono hsub le_rfl
  have hratio (ω : Disorder) :
      X ω = profileP2Fun β M N (η ω) (fun _ => 1) ω := by
    dsimp [X, η, β, m, M, t]
    exact (FutureProfiles.profileP2Fun_smoothedEndpointDist_eq_div β hmM hMN 0 ω).symm
  have hXpos (ω : Disorder) : 0 < X ω := by
    dsimp [X]
    exact div_pos (Polymer.smoothedP2Plane_pos β m N 0 ω)
      (Polymer.smoothedP2Plane_pos β m M 0 ω)
  have hupper := FutureProfiles.measure_log_profileP2Fun_gt_le β hMN η B
    hsupp hnn hmass hmeas r
  have hupperSet : {ω | r < Real.log (X ω)} =
      {ω | r < Real.log (profileP2Fun β M N (η ω) (fun _ => 1) ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hratio ω]
  have hupper' :
      (disorderLaw {ω | r < Real.log (X ω)}).toReal ≤ Real.exp (-r) := by
    rw [hupperSet]
    exact hupper
  have hprofileInvInt : Integrable
      (fun ω => profileP2Fun β M N (η ω) (fun _ => 1) ω ^ (-1 : ℝ)) disorderLaw :=
    FutureProfiles.integrableOn_rpow_neg_profileP2Fun_pastFrozen β hMN η B
      hsupp hnn hmass hmeas (p := 1) (by norm_num)
  have hXinvInt : Integrable (fun ω => (X ω)⁻¹) disorderLaw := by
    apply hprofileInvInt.congr
    filter_upwards [] with ω
    rw [hratio ω, Real.rpow_neg_one]
  have hInvBound : ∫ ω in G, (X ω)⁻¹ ∂disorderLaw ≤ C₀ * ℓ := by
    have hlocal := setIntegral_inv_smoothedP2Plane_div_le
      (β := β) (by dsimp [β, criticalBeta]; exact Real.sqrt_nonneg _) hmM hMN 0 G hGmeas
    have hPEenergy :
        ∫ ω in G, futureEnergy β M N (η ω) ∂disorderLaw ≤ C₀ * ℓ := by
      have h := hPEdata.2.2.2.2
      have hgap : (K : ℝ) - s = ℓ := by
        have hn : K - (K - ℓ) = ℓ := Nat.sub_sub_self hEllK
        dsimp [s]
        exact_mod_cast hn
      simpa [G, η, β, m, M, t, u, s, K, Nat.add_sub_cancel, hgap] using h
    calc
      _ = ∫ ω in G,
            (smoothedP2Plane β m N 0 ω / smoothedP2Plane β m M 0 ω)⁻¹ ∂disorderLaw := by
          apply setIntegral_congr_ae hGambient
          filter_upwards with ω hω
          rfl
      _ ≤ ∫ ω in G, futureEnergy β M N (η ω) ∂disorderLaw := hlocal
      _ ≤ C₀ * ℓ := hPEenergy
  let S : Set Disorder := G ∩ {ω | X ω < Real.exp (-r)}
  let W : Disorder → ℝ := G.indicator (fun ω => (X ω)⁻¹ * Real.exp (-r))
  have hWint : Integrable W disorderLaw := by
    dsimp [W]
    exact (hXinvInt.mul_const (Real.exp (-r))).indicator hGambient
  have hWnonneg : 0 ≤ᵐ[disorderLaw] W := by
    filter_upwards [] with ω
    by_cases hω : ω ∈ G
    · simpa [W, hω] using
        (mul_nonneg (inv_nonneg.mpr (hXpos ω).le) (Real.exp_nonneg (-r)))
    · simp [W, hω]
  have hSbound : ∀ ω ∈ S, 1 ≤ W ω := by
    intro ω hω
    have hmul : 1 < (X ω)⁻¹ * Real.exp (-r) := by
      have h := mul_lt_mul_of_pos_right hω.2 (inv_pos.mpr (hXpos ω))
      rw [mul_inv_cancel₀ (ne_of_gt (hXpos ω))] at h
      simpa [mul_comm] using h
    dsimp [W]
    rw [Set.indicator_of_mem hω.1]
    exact le_of_lt hmul
  have hWmean : ∫ ω, W ω ∂disorderLaw =
      Real.exp (-r) * ∫ ω in G, (X ω)⁻¹ ∂disorderLaw := by
    dsimp [W]
    rw [integral_indicator hGambient, integral_mul_const]
    ring
  have hSmarkov := hWint.measure_le_integral hWnonneg hSbound
  have hSreal : (disorderLaw S).toReal ≤ C₀ * ℓ * Real.exp (-r) := by
    calc
      (disorderLaw S).toReal ≤ (ENNReal.ofReal (∫ ω, W ω ∂disorderLaw)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hSmarkov
      _ = ∫ ω, W ω ∂disorderLaw := by
        rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hWnonneg)]
      _ = Real.exp (-r) * ∫ ω in G, (X ω)⁻¹ ∂disorderLaw := hWmean
      _ ≤ Real.exp (-r) * (C₀ * ℓ) :=
        mul_le_mul_of_nonneg_left hInvBound (Real.exp_nonneg _)
      _ = C₀ * ℓ * Real.exp (-r) := by ring
  let Bad : Set Disorder := {ω | Real.log (X ω) < -r}
  have hBadEq : Bad = {ω | X ω < Real.exp (-r)} := by
    ext ω
    simp only [Bad, Set.mem_ofPred_eq]
    exact Real.log_lt_iff_lt_exp (hXpos ω)
  have hBadSubset : Bad ⊆ Gᶜ ∪ S := by
    intro ω hω
    rw [hBadEq] at hω
    by_cases hGω : ω ∈ G
    · exact Or.inr ⟨hGω, hω⟩
    · exact Or.inl hGω
  have hBadMeasure : disorderLaw Bad ≤ disorderLaw Gᶜ + disorderLaw S :=
    (measure_mono hBadSubset).trans (measure_union_le _ _)
  have hBadReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top disorderLaw Gᶜ,
      measure_ne_top disorderLaw S⟩) hBadMeasure
  rw [ENNReal.toReal_add (measure_ne_top disorderLaw Gᶜ) (measure_ne_top disorderLaw S)] at hBadReal
  have hcomp : (disorderLaw Gᶜ).toReal ≤ C₀ / ℓ := by
    have h := hPEdata.1
    have hgap : (K : ℝ) - s = ℓ := by
      have hn : K - (K - ℓ) = ℓ := Nat.sub_sub_self hEllK
      dsimp [s]
      exact_mod_cast hn
    simpa [G, β, t, u, s, K, hgap] using h
  have hcomp' : (disorderLaw Gᶜ).toReal ≤ C / ℓ := by
    exact hcomp.trans (div_le_div_of_nonneg_right hC₀C (by positivity))
  have hSreal' : (disorderLaw S).toReal ≤ C * ℓ * Real.exp (-r) := by
    calc
      (disorderLaw S).toReal ≤ C₀ * ℓ * Real.exp (-r) := hSreal
      _ ≤ C * ℓ * Real.exp (-r) := by
        have hmul : C₀ * ℓ ≤ C * ℓ :=
          mul_le_mul_of_nonneg_right hC₀C (by exact_mod_cast (Nat.zero_le ℓ))
        exact mul_le_mul_of_nonneg_right hmul (Real.exp_nonneg _)
  have hlower : (disorderLaw Bad).toReal ≤ C / ℓ + C * ℓ * Real.exp (-r) := by
    calc
      (disorderLaw Bad).toReal ≤ (disorderLaw Gᶜ).toReal + (disorderLaw S).toReal := hBadReal
      _ ≤ C / ℓ + C * ℓ * Real.exp (-r) := add_le_add hcomp' hSreal'
  have hBadTarget : Bad = {ω | Real.log
      (smoothedP2Plane β m N 0 ω / smoothedP2Plane β m M 0 ω) < -r} := by
    ext ω
    rfl
  refine ⟨?_, hupper'⟩
  simpa [hBadTarget, C, ℓ₀] using hlower

/-- The smoothed polymer mass has a translation-invariant law. -/
theorem identDistrib_smoothedP2Plane_translate (β : ℝ) (s n : ℕ) (x : Site) :
    IdentDistrib (smoothedP2Plane β s n x) (smoothedP2Plane β s n 0) disorderLaw disorderLaw := by
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x)
  have hτ : Measurable τ := by fun_prop
  have hMP := Gaussian.measurePreserving_disorder_translation x
  have hF : Measurable (smoothedP2Plane β s n 0) :=
    Polymer.measurable_smoothedP2Plane β s n 0
  have hEq (ω : Disorder) :
      smoothedP2Plane β s n x ω = smoothedP2Plane β s n 0 (τ ω) := by
    exact OnePoint.smoothedP2Plane_translate_env β s n x ω
  refine ⟨(Polymer.measurable_smoothedP2Plane β s n x).aemeasurable,
    hF.aemeasurable, ?_⟩
  calc
    Measure.map (smoothedP2Plane β s n x) disorderLaw =
        Measure.map (smoothedP2Plane β s n 0 ∘ τ) disorderLaw := by
      congr 1
      funext ω
      exact hEq ω
    _ = (Measure.map τ disorderLaw).map (smoothedP2Plane β s n 0) :=
      (AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hτ.aemeasurable).symm
    _ = Measure.map (smoothedP2Plane β s n 0) disorderLaw := by rw [hMP.map_eq]

/-- For even lattice sizes, the polymer pairing with the cell average of the constant terminal
function one equals the smoothed point-to-plane mass. -/
theorem profileP2Fun_cellAverage_one_eq_smoothedP2Plane (β : ℝ) {N : ℕ}
    (hN : Even N) (hN1 : 1 ≤ N) {s : ℝ} (_hs : 0 ≤ s) (hs1 : s ≤ 1)
    (x : Plane) (ω : Disorder) :
    profileP2Fun β (evenCeil (N * s)) (evenCeil (N * 1))
        (fun w => srwKernel (evenCeil (N * s)) (w - latticePoint N x))
        (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω =
      smoothedP2Plane β (evenCeil (s * N)) N (latticePoint N x) ω := by
  have hmEq : evenCeil (N * s) = evenCeil (s * N) :=
    congrArg evenCeil (mul_comm (N : ℝ) s)
  have hceilN : evenCeil (N * 1) = N := by
    obtain ⟨k, hk⟩ := hN
    simp [evenCeil, hk]
    omega
  let m : ℕ := evenCeil (N * s)
  let xN : Site := latticePoint N x
  have hm_le : m ≤ N := by
    dsimp [m]
    have harg : (N : ℝ) * s ≤ (N : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hs1 (by positivity)
    calc
      evenCeil ((N : ℝ) * s) ≤ evenCeil ((N : ℝ) * 1) := evenCeil_mono harg
      _ = N := hceilN
  have hmEven : Even (m : ℤ) := by
    dsimp [m]
    exact_mod_cast evenCeil_even (N * s)
  have hNEven : Even (N : ℤ) := by exact_mod_cast hN
  have htimeEven : Even ((N - m : ℕ) : ℤ) := by
    rw [Nat.cast_sub hm_le]
    exact hNEven.sub hmEven
  have hxEven : Even (xN 0 + xN 1) := by
    exact Critical2DKPZ.latticePoint_mem_evenLattice N x
  have hqSupport (w : Site) (hw : w ∉ Polymer.endpoints xN m) :
      srwKernel m (w - xN) = 0 := Polymer.srwKernel_eq_zero_of_not_mem m xN w hw
  have hterminal (w : Site) (hw : w ∈ Polymer.endpoints xN m) :
      (∑' y : Site, pointToPoint β m (N - m) w y ω *
        cellAverage N (fun z => Real.exp ((0 : Plane →ᵇ ℝ) z)) y) =
        pointToPlane β m (N - m) w ω := by
    have hweven : Even (w 0 + w 1) := by
      obtain ⟨p, hp⟩ := (Polymer.mem_endpoints_iff xN w m).mp hw
      have hpath : Int.ModEq 2 (w 0 + w 1) (xN 0 + xN 1 + (m : ℤ)) := by
        simpa [hp] using Polymer.walkPosition_parity xN p
      have hbase : Even (xN 0 + xN 1 + (m : ℤ)) := Even.add hxEven hmEven
      have hmod : Int.ModEq 2 (w 0 + w 1) 0 :=
        hpath.trans (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp hbase))
      exact even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp hmod)
    have hyEven (y : Site) (hy : y ∈ Polymer.endpoints w (N - m)) :
        Even (y 0 + y 1) := by
      obtain ⟨p, hp⟩ := (Polymer.mem_endpoints_iff w y (N - m)).mp hy
      have hpath : Int.ModEq 2 (y 0 + y 1)
          (w 0 + w 1 + ((N - m : ℕ) : ℤ)) := by
        simpa [hp] using Polymer.walkPosition_parity w p
      have hbase : Even (w 0 + w 1 + ((N - m : ℕ) : ℤ)) :=
        Even.add hweven htimeEven
      have hmod : Int.ModEq 2 (y 0 + y 1) 0 :=
        hpath.trans (Int.modEq_zero_iff_dvd.mpr (even_iff_two_dvd.mp hbase))
      exact even_iff_two_dvd.mpr (Int.modEq_zero_iff_dvd.mp hmod)
    rw [Polymer.tsum_pointToPoint_mul_eq_sum]
    calc
      _ = ∑ y ∈ Polymer.endpoints w (N - m),
          pointToPoint β m (N - m) w y ω := by
        apply Finset.sum_congr rfl
        intro y hy
        have hfun : (fun z : Plane => Real.exp ((0 : Plane →ᵇ ℝ) z)) =
            (fun _ : Plane => (1 : ℝ)) := by
          funext z
          simp
        rw [hfun, Critical2DKPZ.cellAverage_const (by omega) (hyEven y hy)]
        simp
      _ = ∑' y : Site, pointToPoint β m (N - m) w y ω :=
        by simpa only [mul_one] using
          (Polymer.tsum_pointToPoint_mul_eq_sum β m (N - m) w (fun _ => 1) ω).symm
      _ = pointToPlane β m (N - m) w ω := Polymer.tsum_pointToPoint β m (N - m) w ω
  rw [← hmEq, hceilN]
  change profileP2Fun β m N (fun w => srwKernel m (w - xN))
      (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω =
    smoothedP2Plane β m N xN ω
  rw [Polymer.profileP2Fun_eq_sum β m N _ _ (Polymer.endpoints xN m) hqSupport ω,
    Polymer.smoothedP2Plane_eq_sum β m N xN ω]
  apply Finset.sum_congr rfl
  intro w hw
  rw [hterminal w hw]

/-- At each fixed smoothing scale in `(0,1)`, the squared log mass is integrable and its integral
is uniformly bounded for sufficiently large lattice sizes. -/
theorem log_smoothedP2Plane_sq_integral_bounded (ϑ : ℝ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => Real.log
        (smoothedP2Plane (criticalBeta ϑ N) (evenCeil (ε ^ 2 * N)) N 0 ω) ^ 2)
        disorderLaw ∧
      ∫ ω, Real.log
        (smoothedP2Plane (criticalBeta ϑ N) (evenCeil (ε ^ 2 * N)) N 0 ω) ^ 2
        ∂disorderLaw ≤ C := by
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_log
    |ϑ| 1 1 (by norm_num)
  let B : ℝ := 1 + |C₂| * (1 + Real.log ((ε⁻¹) ^ 2))
  have hB : 0 < B := by
    dsimp [B]
    have hlog : 0 ≤ Real.log ((ε⁻¹) ^ 2) := by
      apply Real.log_nonneg
      have hinv : 1 < ε⁻¹ := (one_lt_inv₀ hε).2 hε1
      have hmul := mul_nonneg (sub_nonneg.mpr hinv.le)
        (by positivity : 0 ≤ ε⁻¹ + 1)
      nlinarith
    positivity
  refine ⟨2 * Real.log B + 4 * (Real.log B) ^ 2, ?_⟩
  have hgap : 0 < 1 - ε ^ 2 := by
    have hprod := mul_pos (sub_pos.mpr hε1) (by positivity : 0 < 1 + ε)
    nlinarith
  have hNtime : ∀ᶠ N : ℕ in atTop, 2 / (1 - ε ^ 2) < (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (2 / (1 - ε ^ 2))
  filter_upwards [hC₂, hNtime, eventually_ge_atTop 1] with N hCN hNtimeN hN1
  let sN : ℕ := evenCeil (ε ^ 2 * N)
  let Z : Disorder → ℝ := smoothedP2Plane (criticalBeta ϑ N) sN N 0
  let U : Disorder → ℝ := fun ω => Real.log (Z ω)
  have hsNleN : sN ≤ N := by
    have hscale : 2 < (N : ℝ) * (1 - ε ^ 2) :=
      (div_lt_iff₀ hgap).mp hNtimeN
    have hgapN : ε ^ 2 * (N : ℝ) + 2 < (N : ℝ) := by nlinarith [hscale]
    have hceil : (sN : ℝ) < ε ^ 2 * (N : ℝ) + 2 := by
      dsimp [sN]
      exact evenCeil_lt_add_two (by positivity)
    exact_mod_cast (le_of_lt (hceil.trans hgapN))
  have hdenpos : 0 < ((max sN 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < max sN 1 by omega)
  have hdenLower : ε ^ 2 * (N : ℝ) ≤ ((max sN 1 : ℕ) : ℝ) := by
    have hlower : ε ^ 2 * (N : ℝ) ≤ (sN : ℝ) := by
      exact le_evenCeil _
    exact hlower.trans (by exact_mod_cast (Nat.le_max_left sN 1))
  have hratio : (N : ℝ) / ((max sN 1 : ℕ) : ℝ) ≤ (ε⁻¹) ^ 2 := by
    apply (div_le_iff₀ hdenpos).2
    calc
      (N : ℝ) = (ε⁻¹) ^ 2 * (ε ^ 2 * (N : ℝ)) := by field_simp [ne_of_gt hε]
      _ ≤ (ε⁻¹) ^ 2 * ((max sN 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hdenLower (by positivity)
  have hratioPos : 0 < (N : ℝ) / ((max sN 1 : ℕ) : ℝ) := by
    positivity
  have hlogratio : Real.log ((N : ℝ) / ((max sN 1 : ℕ) : ℝ)) ≤
      Real.log ((ε⁻¹) ^ 2) := by
    exact Real.log_le_log hratioPos hratio
  have hlogratioNonneg : 0 ≤ Real.log
      ((N : ℝ) / ((max sN 1 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    apply (one_le_div hdenpos).2
    exact_mod_cast (show max sN 1 ≤ N by omega)
  have hϑ : ϑ ∈ Set.Icc (-|ϑ|) |ϑ| := by
    constructor <;> nlinarith [abs_nonneg ϑ, le_abs_self ϑ, neg_abs_le ϑ]
  have hsecond := hCN ϑ hϑ sN N hsNleN (by norm_num) (by norm_num)
  have hsecondBound :
      ∫ ω, Z ω ^ 2 ∂disorderLaw ≤ B := by
    dsimp [Z, B]
    calc
      _ ≤ C₂ * (1 + Real.log ((N : ℝ) / ((max sN 1 : ℕ) : ℝ))) := by
        simpa [sN] using hsecond
      _ ≤ |C₂| * (1 + Real.log ((N : ℝ) / ((max sN 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_abs_self C₂) (by linarith)
      _ ≤ |C₂| * (1 + Real.log ((ε⁻¹) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (by simpa [add_comm] using add_le_add_left hlogratio 1) (abs_nonneg C₂)
      _ ≤ 1 + |C₂| * (1 + Real.log (ε⁻¹ ^ 2)) := by linarith
  have hβ : 0 ≤ criticalBeta ϑ N := by
    dsimp [criticalBeta]
    exact Real.sqrt_nonneg _
  have hlogVar := variance_log_smoothedP2Plane_le hβ sN N 0
  have hlogMem : MemLp U 2 disorderLaw := by
    simpa [U, Z] using hlogVar.1
  have hlogInt : Integrable U disorderLaw := hlogMem.integrable (by norm_num)
  have hlogSqInt : Integrable (fun ω => U ω ^ 2) disorderLaw :=
    (memLp_two_iff_integrable_sq hlogMem.aestronglyMeasurable).1 hlogMem
  have hZpos (ω : Disorder) : 0 < Z ω :=
    Polymer.smoothedP2Plane_pos (criticalBeta ϑ N) sN N 0 ω
  have hZmean : ∫ ω, Z ω ∂disorderLaw = 1 := by
    dsimp [Z]
    exact Polymer.integral_smoothedP2Plane (criticalBeta ϑ N) sN N 0
  have hZmem : MemLp Z 2 disorderLaw :=
    Polymer.memLp_smoothedP2Plane (criticalBeta ϑ N) sN N 0 2 (by norm_num)
  have hZint : Integrable Z disorderLaw := hZmem.integrable (by norm_num)
  have hMone : 1 ≤ ∫ ω, Z ω ^ 2 ∂disorderLaw := by
    have hv := variance_nonneg Z disorderLaw
    rw [variance_eq_sub hZmem, hZmean] at hv
    norm_num at hv ⊢
    linarith
  have hMpos : 0 < ∫ ω, Z ω ^ 2 ∂disorderLaw := lt_of_lt_of_le (by norm_num) hMone
  have hLle : Real.log (∫ ω, Z ω ^ 2 ∂disorderLaw) ≤ Real.log B :=
    Real.log_le_log hMpos hsecondBound
  have hvarUpper : Var[U; disorderLaw] ≤ 2 * Real.log B := by
    exact (hlogVar.2.trans (mul_le_mul_of_nonneg_left hLle (by norm_num)))
  have hmeanUpper : ∫ ω, U ω ∂disorderLaw ≤ 0 := by
    have hsubInt : Integrable (fun ω => Z ω - 1) disorderLaw :=
      hZint.sub (integrable_const (1 : ℝ))
    have hmono := integral_mono hlogInt hsubInt (fun ω => by
      simpa [U] using Real.log_le_sub_one_of_pos (hZpos ω))
    rw [integral_sub hZint (integrable_const (1 : ℝ)), hZmean] at hmono
    simpa using hmono
  have hInvone : 1 ≤ ∫ ω, (Z ω)⁻¹ ∂disorderLaw :=
    OnePoint.one_le_integral_inv_smoothedP2Plane (criticalBeta ϑ N) sN N 0
  have hInvpos : 0 < ∫ ω, (Z ω)⁻¹ ∂disorderLaw :=
    lt_of_lt_of_le (by norm_num) hInvone
  have hratioInv :
      (∫ ω, Z ω ^ 2 ∂disorderLaw) / (∫ ω, (Z ω)⁻¹ ∂disorderLaw) ≤
        ∫ ω, Z ω ^ 2 ∂disorderLaw := by
    apply (div_le_iff₀ hInvpos).2
    nlinarith [hMone]
  have hD := OnePoint.gaussianityDefect_log_smoothedP2Plane_bounds hβ sN N 0
  have hDupper : gaussianityDefect disorderLaw U ≤
      Real.log (∫ ω, Z ω ^ 2 ∂disorderLaw) := by
    have hlogD := Real.log_le_log
      (div_pos hMpos hInvpos) hratioInv
    simpa [U, Z] using hD.2.trans hlogD
  have hmeanLower : -(∫ ω, U ω ∂disorderLaw) ≤ 2 * Real.log B := by
    dsimp [gaussianityDefect] at hDupper
    have h := hvarUpper
    nlinarith
  have hmeanSq : (∫ ω, U ω ∂disorderLaw) ^ 2 ≤ 4 * (Real.log B) ^ 2 := by
    have habs : |∫ ω, U ω ∂disorderLaw| ≤ 2 * Real.log B := by
      rw [abs_of_nonpos hmeanUpper]
      exact hmeanLower
    nlinarith [sq_nonneg (2 * Real.log B)]
  have hsecondU : ∫ ω, U ω ^ 2 ∂disorderLaw =
      Var[U; disorderLaw] + (∫ ω, U ω ∂disorderLaw) ^ 2 := by
    have hpow : (fun ω : Disorder => U ω ^ 2) = U ^ 2 := rfl
    rw [hpow, variance_eq_sub hlogMem]
    ring
  have hfinal : ∫ ω, U ω ^ 2 ∂disorderLaw ≤
      2 * Real.log B + 4 * (Real.log B) ^ 2 := by
    rw [hsecondU]
    exact add_le_add hvarUpper hmeanSq
  refine ⟨?_, ?_⟩
  · simpa [U, Z] using hlogSqInt
  · simpa [U, Z] using hfinal

end Critical2DKPZ.LogNormality

end
