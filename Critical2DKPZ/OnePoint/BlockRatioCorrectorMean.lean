/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawMomentBounds
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

/-! # Truncated-inverse and corrector-mean estimates -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- The tilted good-set complement bound, conditional on the block-moment estimate. It follows by factoring each
one-block bad event from the inverse-mass product and summing the inverse-three-halves tail. -/
theorem tilted_blockGoodSet_compl_le_of (hC6 : BlockMomentsBound)
    (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
        (∫ ω in (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ,
            ∏ i ∈ Finset.Icc r s,
              (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) /
          (∫ ω, ∏ i ∈ Finset.Icc r s,
              (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
          C / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨Cb, hbad⟩ := tilted_blockMass_bad_le_of hC6 A ρ₀ ρ₁ hρ
  refine ⟨8 * |Cb|, ?_⟩
  intro ρ hρρ
  have hNclock : ∀ᶠ N : ℕ in atTop, ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N :=
    Filter.eventually_ge_atTop _
  filter_upwards [hbad ρ hρρ, hNclock] with N hbadN hNclock
  intro ϑ hϑ r s hr hrs hsK
  classical
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  have ht : Monotone t := by
    exact Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon
      hρ hρρ.1 hNclock
  let S := Finset.Icc r s
  let f : Disorder → ℝ := fun ω =>
    ∏ i ∈ S, (blockMass β t i ω)⁻¹
  let bad : ℕ → Set Disorder := fun i =>
    {ω | (1 / 2 : ℝ) < |blockMass β t i ω - 1|}
  have hSpos : ∀ i ∈ S, 1 ≤ i := by
    intro i hi
    exact le_trans hr (Finset.mem_Icc.mp hi).1
  have hgoodMeas : MeasurableSet (blockGoodSet β t r s) :=
    measurableSet_blockGoodSet β t r s
  have hbadMeas (i : ℕ) : MeasurableSet (bad i) := by
    dsimp [bad]
    exact measurableSet_lt measurable_const
      (((measurable_blockMass β t i).mono (Gaussian.disorderBlock_le _ _) le_rfl)
        |>.sub measurable_const |>.abs)
  have hbadUnion : (blockGoodSet β t r s)ᶜ = ⋃ i ∈ S, bad i := by
    ext ω
    simp [blockGoodSet, bad, S, Finset.mem_Icc, not_le, and_assoc]
  have hbadUnionMeas : MeasurableSet (⋃ i ∈ S, bad i) := by
    rw [← hbadUnion]
    exact hgoodMeas.compl
  have hint : Integrable f disorderLaw := by
    simpa [f, S] using integrable_prod_inv_blockMass β t (Finset.Icc r s)
  have hfnonneg (ω : Disorder) : 0 ≤ f ω := by
    dsimp [f]
    apply Finset.prod_nonneg
    intro i hi
    exact inv_nonneg.mpr (le_of_lt (blockMass_pos β t i ω))
  have htermInt (i : ℕ) :
      Integrable ((bad i).indicator f) disorderLaw :=
    hint.indicator (hbadMeas i)
  have hsumInt : Integrable (fun ω => ∑ i ∈ S, (bad i).indicator f ω) disorderLaw := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      have heq : (fun ω => ∑ j ∈ insert i S, (bad j).indicator f ω) =
          fun ω => (bad i).indicator f ω + ∑ j ∈ S, (bad j).indicator f ω := by
        funext ω
        simp [Finset.sum_insert, hi]
      rw [heq]
      exact (htermInt i).add ih
  have hpoint (ω : Disorder) :
      ((⋃ i ∈ S, bad i).indicator f) ω ≤ ∑ i ∈ S, (bad i).indicator f ω := by
    by_cases hω : ω ∈ ⋃ i ∈ S, bad i
    · rw [Set.indicator_of_mem hω]
      have hex : ∃ i ∈ S, ω ∈ bad i := by simpa using hω
      obtain ⟨i, hi, hωi⟩ := hex
      calc
        f ω = (bad i).indicator f ω := by simp [hωi]
        _ ≤ ∑ j ∈ S, (bad j).indicator f ω :=
          Finset.single_le_sum (f := fun j => (bad j).indicator f ω) (fun j hj => by
            by_cases hωj : ω ∈ bad j
            · simpa [hωj] using hfnonneg ω
            · simp [hωj]) hi
    · rw [Set.indicator_of_notMem hω]
      exact Finset.sum_nonneg fun i hi => by
        by_cases hωi : ω ∈ bad i <;> simp [hωi, hfnonneg]
  have hsetSum :
      (∫ ω in (blockGoodSet β t r s)ᶜ, f ω ∂disorderLaw) ≤
        ∑ i ∈ S, ∫ ω in bad i, f ω ∂disorderLaw := by
    rw [← integral_indicator hgoodMeas.compl]
    rw [hbadUnion]
    calc
      ∫ ω, (⋃ i ∈ S, bad i).indicator f ω ∂disorderLaw ≤
          ∫ ω, ∑ i ∈ S, (bad i).indicator f ω ∂disorderLaw :=
        integral_mono (hint.indicator hbadUnionMeas) hsumInt hpoint
      _ = ∑ i ∈ S, ∫ ω, (bad i).indicator f ω ∂disorderLaw :=
        integral_finsetSum S (fun i hi => htermInt i)
      _ = ∑ i ∈ S, ∫ ω in bad i, f ω ∂disorderLaw := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_indicator (hbadMeas i)
  have hdenEq :
      ∫ ω, f ω ∂disorderLaw =
        ∏ i ∈ S, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    simpa [f, S] using integral_finset_prod_inv_blockMass β t ht
      (Finset.Icc r s) hSpos
  let m : ℕ → ℝ := fun i => ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw
  have hmpos (i : ℕ) : 0 < m i := by
    dsimp [m]
    exact lt_of_lt_of_le zero_lt_one (one_le_integral_inv_blockMass β t i)
  have hdenPos : 0 < ∫ ω, f ω ∂disorderLaw := by
    rw [hdenEq]
    apply Finset.prod_pos
    intro i hi
    exact hmpos i
  have hbadFactor (i : ℕ) (hi : i ∈ S) :
      (∫ ω in bad i, f ω ∂disorderLaw) =
        (∫ ω in bad i, (blockMass β t i ω)⁻¹ ∂disorderLaw) *
          ∏ j ∈ S.erase i, m j := by
    simpa [f, m, bad, S] using
      setIntegral_prod_inv_blockMass_on_bad β t ht
        (Finset.Icc r s) hSpos i hi
  have htermRatio (i : ℕ) (hi : i ∈ S) :
      (∫ ω in bad i, f ω ∂disorderLaw) / (∫ ω, f ω ∂disorderLaw) ≤
        |Cb| / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) := by
    have hbadRatio := hbadN ϑ hϑ i (hSpos i hi) (by
      have hi' := Finset.mem_Icc.mp hi
      omega)
    have hmi : 1 ≤ m i := by
      dsimp [m]
      exact one_le_integral_inv_blockMass β t i
    have hrestPos : 0 < ∏ j ∈ S.erase i, m j := by
      apply Finset.prod_pos
      intro j hj
      exact hmpos j
    have hdenProd :
        ∫ ω, f ω ∂disorderLaw = m i * ∏ j ∈ S.erase i, m j := by
      rw [hdenEq]
      dsimp [m]
      calc
        ∏ j ∈ S, ∫ ω, (blockMass β t j ω)⁻¹ ∂disorderLaw =
            (∏ j ∈ S.erase i, ∫ ω, (blockMass β t j ω)⁻¹ ∂disorderLaw) *
              ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw :=
          (Finset.prod_erase_mul S
            (fun j => ∫ ω, (blockMass β t j ω)⁻¹ ∂disorderLaw) hi).symm
        _ = (∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw) *
              ∏ j ∈ S.erase i, ∫ ω, (blockMass β t j ω)⁻¹ ∂disorderLaw := by ring
    rw [hbadFactor i hi, hdenProd]
    have hnumNonneg : 0 ≤ ∫ ω in bad i, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
      apply setIntegral_nonneg (hbadMeas i)
      intro ω hω
      exact inv_nonneg.mpr (le_of_lt (blockMass_pos β t i ω))
    have hratio :
        ((∫ ω in bad i, (blockMass β t i ω)⁻¹ ∂disorderLaw) *
          ∏ j ∈ S.erase i, m j) /
        (m i * ∏ j ∈ S.erase i, m j) =
          (∫ ω in bad i, (blockMass β t i ω)⁻¹ ∂disorderLaw) / m i := by
      field_simp [hmpos i |>.ne', hrestPos.ne']
    rw [hratio]
    have hbadRatioAbs :
        (∫ ω in bad i, (blockMass β t i ω)⁻¹ ∂disorderLaw) / m i ≤
          Cb / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) := by
      simpa [m, bad, β, t] using hbadRatio
    have hdpos : 0 < (blockCount N ρ : ℝ) - i := by
      have hi' := Finset.mem_Icc.mp hi
      have hnat : i < blockCount N ρ := by omega
      have hcast : (i : ℝ) < (blockCount N ρ : ℝ) := by exact_mod_cast hnat
      linarith
    have hdenomNonneg : 0 ≤ ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) :=
      le_of_lt (Real.rpow_pos_of_pos hdpos _)
    exact hbadRatioAbs.trans (div_le_div_of_nonneg_right (le_abs_self Cb) hdenomNonneg)
  have hsumRatio :
      (∑ i ∈ S, ∫ ω in bad i, f ω ∂disorderLaw) / (∫ ω, f ω ∂disorderLaw) ≤
        8 * |Cb| / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
    rw [Finset.sum_div]
    calc
      ∑ i ∈ S, (∫ ω in bad i, f ω ∂disorderLaw) / (∫ ω, f ω ∂disorderLaw) ≤
          ∑ i ∈ S, |Cb| * ((blockCount N ρ : ℝ) - i) ^ (-(3 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have h := htermRatio i hi
        have hdpos : 0 < (blockCount N ρ : ℝ) - i := by
          have hi' := Finset.mem_Icc.mp hi
          have hnat : i < blockCount N ρ := by omega
          have hcast : (i : ℝ) < (blockCount N ρ : ℝ) := by exact_mod_cast hnat
          linarith
        have hpow : 1 / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) =
            ((blockCount N ρ : ℝ) - i) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.rpow_neg (le_of_lt hdpos)]
          simp [div_eq_mul_inv]
        calc
          (∫ ω in bad i, f ω ∂disorderLaw) / (∫ ω, f ω ∂disorderLaw) ≤
              |Cb| / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) := h
          _ = |Cb| * ((blockCount N ρ : ℝ) - i) ^ (-(3 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hdpos)]
      _ = |Cb| * ∑ i ∈ S,
          ((blockCount N ρ : ℝ) - i) ^ (-(3 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
      _ ≤ |Cb| * (8 / Real.sqrt ((blockCount N ρ : ℝ) - s)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        simpa [S] using sum_endpoint_inv_three_halves_le hrs (by omega : s < blockCount N ρ)
      _ = 8 * |Cb| / Real.sqrt ((blockCount N ρ : ℝ) - s) := by ring
  have hdenEqSet :
      ((∫ ω in (blockGoodSet β t r s)ᶜ, f ω ∂disorderLaw) /
        (∫ ω, f ω ∂disorderLaw)) ≤
        (∑ i ∈ S, ∫ ω in bad i, f ω ∂disorderLaw) /
          (∫ ω, f ω ∂disorderLaw) := by
    exact div_le_div_of_nonneg_right hsetSum (le_of_lt hdenPos)
  calc
    (∫ ω in (blockGoodSet β t r s)ᶜ, f ω ∂disorderLaw) /
        (∫ ω, f ω ∂disorderLaw) ≤
      (∑ i ∈ S, ∫ ω in bad i, f ω ∂disorderLaw) /
        (∫ ω, f ω ∂disorderLaw) := hdenEqSet
    _ ≤ 8 * |Cb| / Real.sqrt ((blockCount N ρ : ℝ) - s) := hsumRatio



/-- The truncated inverse defect is controlled by the block variance. -/
theorem integral_truncatedInverse_sub_one_sq_le (A ρ₀ : ℝ) (hρ₀ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i + 1 ≤ blockCount N ρ →
        ∫ ω, (truncatedInverse (criticalBeta ϑ N) (blockTime N ρ) i ω - 1) ^ 2
          ∂disorderLaw ≤ C / ((blockCount N ρ : ℝ) - i) := by
  obtain ⟨Cvar, hvar⟩ := variance_blockMass_le_uniform A ρ₀ hρ₀
  refine ⟨4 * Cvar, ?_⟩
  intro ρ hρ
  filter_upwards [hvar ρ hρ] with N hvarN
  intro ϑ hϑ i hi hiK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let Z : Disorder → ℝ := blockMass β t i
  let M : Disorder → ℝ := truncatedInverse β t i
  have hZmem : MemLp Z 2 disorderLaw := by
    dsimp [Z, β, t, blockMass]
    exact Polymer.memLp_smoothedP2Plane _ _ _ _ 2 (by norm_num)
  have hZmean : ∫ ω, Z ω ∂disorderLaw = 1 := by
    dsimp [Z, β, t, blockMass]
    exact Polymer.integral_smoothedP2Plane _ _ _ _
  have hZcenterMem : MemLp (fun ω => Z ω - 1) 2 disorderLaw := by
    exact hZmem.sub (memLp_const (1 : ℝ))
  have hZcenterInt : Integrable (fun ω => (Z ω - 1) ^ 2) disorderLaw := by
    have h := hZcenterMem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hZcenterEq :
      ∫ ω, (Z ω - 1) ^ 2 ∂disorderLaw =
        ProbabilityTheory.variance (fun ω => Z ω) disorderLaw := by
    calc
      ∫ ω, (Z ω - 1) ^ 2 ∂disorderLaw =
          ∫ ω, (Z ω - ∫ ω', Z ω' ∂disorderLaw) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hZmean]
      _ = ProbabilityTheory.variance (fun ω => Z ω) disorderLaw :=
        (ProbabilityTheory.variance_eq_integral hZmem.aemeasurable).symm
  have hMmeas : Measurable M := measurable_truncatedInverse β t i
  have hMrange (ω : Disorder) : 0 ≤ M ω ∧ M ω ≤ 2 :=
    truncatedInverse_nonneg_le_two β t i ω
  have hMcenterMem : MemLp (fun ω => M ω - 1) 2 disorderLaw := by
    apply MemLp.of_bound (hMmeas.sub measurable_const).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    change |M ω - 1| ≤ 1
    apply abs_le.mpr
    exact ⟨by linarith [(hMrange ω).1], by linarith [(hMrange ω).2]⟩
  have hMcenterInt : Integrable (fun ω => (M ω - 1) ^ 2) disorderLaw := by
    have h := hMcenterMem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hpoint (ω : Disorder) : (M ω - 1) ^ 2 ≤ 4 * (Z ω - 1) ^ 2 := by
    have h := abs_truncatedInverse_sub_one_le β t i ω
    have h' : |M ω - 1| ≤ 2 * |Z ω - 1| := by simpa [M, Z] using h
    calc
      (M ω - 1) ^ 2 = |M ω - 1| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * |Z ω - 1|) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) h' 2
      _ = 4 * (Z ω - 1) ^ 2 := by rw [mul_pow, sq_abs]; ring
  have hvarBound : ProbabilityTheory.variance (fun ω => Z ω) disorderLaw ≤
      Cvar / ((blockCount N ρ : ℝ) - i) := by
    simpa [Z, β, t, blockMass] using hvarN ϑ hϑ i hi hiK
  calc
    ∫ ω, (M ω - 1) ^ 2 ∂disorderLaw ≤
        4 * ∫ ω, (Z ω - 1) ^ 2 ∂disorderLaw := by
      calc
        ∫ ω, (M ω - 1) ^ 2 ∂disorderLaw ≤
            ∫ ω, 4 * (Z ω - 1) ^ 2 ∂disorderLaw :=
          integral_mono hMcenterInt (hZcenterInt.const_mul 4) hpoint
        _ = 4 * ∫ ω, (Z ω - 1) ^ 2 ∂disorderLaw := by rw [integral_const_mul]
    _ = 4 * ProbabilityTheory.variance (fun ω => Z ω) disorderLaw := by rw [hZcenterEq]
    _ ≤ 4 * (Cvar / ((blockCount N ρ : ℝ) - i)) :=
      mul_le_mul_of_nonneg_left hvarBound (by norm_num)
    _ = (4 * Cvar) / ((blockCount N ρ : ℝ) - i) := by ring

/-- Cancellation of the first discrepancy block gains one additional inverse square-root
factor over the squared truncated-corrector estimate. -/
theorem abs_integral_truncatedCorrector_le (A : ℝ) :
    ∃ C₀ ρ₀ C : ℝ, 0 < C₀ ∧ 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ u v : ℕ, 1 ≤ u → u < v → v + 1 ≤ blockCount N ρ →
        |∫ ω, truncatedCorrector (criticalBeta ϑ N) (blockTime N ρ) u v ω ∂disorderLaw| ≤
          C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
            ((blockCount N ρ : ℝ) - v) ^ ((3 : ℝ) / 2) := by
  obtain ⟨Ck, Ck₀, hCk₀, hDiscrepancyStringInput⟩ :=
    Critical2DKPZ.Blocks.closedDiscrepancy_sq_integral_le A
  obtain ⟨Cinv, hInv⟩ := integral_truncatedInverse_sub_one_sq_le A 2 (by norm_num)
  let ρ₀ : ℝ := max (Real.exp (Ck₀ ^ 2) + 1) 2
  let C₀ : ℝ := 2 * Ck₀
  let C : ℝ := |Ck| * Real.sqrt (max Cinv 1)
  have hρ₀ : 1 < ρ₀ := by
    dsimp [ρ₀]
    have hexp : 0 < Real.exp (Ck₀ ^ 2) := Real.exp_pos _
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hC₀pos : 0 < C₀ := by dsimp [C₀]; positivity
  have hV : 0 < max Cinv 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C₀, ρ₀, C, hC₀pos, hρ₀, ?_⟩
  intro ρ hρ
  have hρexp : Real.exp (Ck₀ ^ 2) < ρ := by
    have h := le_trans (le_max_left _ _) hρ
    have h' : Real.exp (Ck₀ ^ 2) + 1 ≤ ρ := by simpa [ρ₀] using h
    linarith
  have hρtwo : 2 ≤ ρ := le_trans (le_max_right _ _) hρ
  have hlog : Ck₀ ^ 2 < Real.log ρ := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hρexp
  have hNclock : ∀ᶠ N : ℕ in atTop,
      ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N := Filter.eventually_ge_atTop _
  filter_upwards [hDiscrepancyStringInput ρ hρexp, hInv ρ hρtwo, hNclock] with N hDiscrepancyStringInputN hInvN hNclock
  intro ϑ hϑ u v hu huv hvK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let K := blockCount N ρ
  let dU : ℝ := (K : ℝ) - u
  let d : ℝ := (K : ℝ) - v
  let α : ℝ := Ck₀ / Real.sqrt (Real.log ρ)
  let L : ℝ := 2 ^ (v - u : ℕ)
  let D : Disorder → ℝ := closedDiscrepancy β t u v
  let M : Disorder → ℝ := truncatedInverse β t u
  let Y : Disorder → ℝ := ∏ i ∈ Finset.Icc (u + 1) v, truncatedInverse β t i
  have hρpos : 0 < ρ := by linarith
  have hdpos : 0 < d := by
    dsimp [d, K]
    have hnat : v < blockCount N ρ := by omega
    have hcast : (v : ℝ) < (blockCount N ρ : ℝ) := by exact_mod_cast hnat
    linarith
  have hdUpos : 0 < dU := by
    dsimp [dU, K]
    have hnat : u < blockCount N ρ := by omega
    have hcast : (u : ℝ) < (blockCount N ρ : ℝ) := by exact_mod_cast hnat
    linarith
  have hd_le_dU : d ≤ dU := by
    dsimp [d, dU, K]
    have huvR : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
    linarith
  have hdSqpos : 0 < d ^ 2 := by positivity
  have hαpos : 0 < α := by
    dsimp [α]
    exact div_pos hCk₀ (Real.sqrt_pos.mpr (lt_trans (sq_pos_of_pos hCk₀) hlog))
  have ht : Monotone t := by
    exact Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon hρ₀
      hρ hNclock
  have hYmeas : Measurable[Gaussian.disorderBlock (t u) (t v)] Y := by
    let Yval : Disorder → ℝ := fun ω =>
      ∏ i ∈ Finset.Icc (u + 1) v, truncatedInverse β t i ω
    have hYval : Measurable[Gaussian.disorderBlock (t u) (t v)] Yval := by
      dsimp [Yval]
      apply Finset.measurable_prod
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hstart : t u ≤ t (i - 1) := ht (by omega)
      have hstop : t i ≤ t v := ht hi'.2
      exact (measurable_truncatedInverse_block β t i).mono
        (Gaussian.disorderBlock_mono hstart hstop) le_rfl
    have hYeq : Y = Yval := by
      funext ω
      dsimp [Y, Yval]
      exact Finset.prod_apply _ _ _
    rw [hYeq]
    exact hYval
  have hLpow (ω : Disorder) : |Y ω| ≤ L := by
    dsimp [Y, L]
    rw [Finset.prod_apply]
    rw [Finset.abs_prod]
    calc
      ∏ i ∈ Finset.Icc (u + 1) v, |truncatedInverse β t i ω| ≤
          ∏ _i ∈ Finset.Icc (u + 1) v, (2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          have hM := truncatedInverse_nonneg_le_two β t i ω
          rw [abs_of_nonneg hM.1]
          exact hM.2
      _ = 2 ^ (v - u : ℕ) := by
        rw [Finset.prod_const]
        have hcard : (Finset.Icc (u + 1) v).card = v - u := by
          simp only [Nat.card_Icc]
          omega
        rw [hcard]
  have hYbound : ∃ B : ℝ, ∀ ω, |Y ω| ≤ B := ⟨L, hLpow⟩
  have hcancel := Critical2DKPZ.Blocks.closedDiscrepancy_integral_mul_eq_zero
    β t ht u v hu huv Y hYmeas hYbound
  have hMrange : ∀ ω, 0 ≤ M ω ∧ M ω ≤ 2 := by
    intro ω
    exact truncatedInverse_nonneg_le_two β t u ω
  have hMmeas : Measurable M := measurable_truncatedInverse β t u
  have hMcenterMem : MemLp (fun ω => M ω - 1)
      (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    apply MemLp.of_bound (hMmeas.sub measurable_const).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    change |M ω - 1| ≤ 1
    apply abs_le.mpr
    exact ⟨by linarith [(hMrange ω).1], by linarith [(hMrange ω).2]⟩
  have hDmem : MemLp D (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    dsimp [D, β, t]
    exact memLp_closedDiscrepancy _ _ _ _ (ENNReal.ofReal (2 : ℝ))
      (by norm_num) (by norm_num)
  have hDGmem : MemLp (fun ω => D ω * (M ω - 1)) 1 disorderLaw := by
    have htriple : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) 1 := Real.HolderConjugate.two_two.ennrealOfReal
    exact @MemLp.mul Disorder inferInstance ℝ inferInstance disorderLaw
      (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1
      (fun ω => M ω - 1) D hDmem hMcenterMem htriple
  have hDGint : Integrable (fun ω => D ω * (M ω - 1)) disorderLaw :=
    hDGmem.integrable (by norm_num)
  have hDint : Integrable D disorderLaw := hDmem.integrable (by norm_num)
  have hYas' : AEStronglyMeasurable Y disorderLaw := by
    exact (hYmeas.mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable
  have hYbounded : ∀ᵐ ω ∂disorderLaw, ‖Y ω‖ ≤ L := by
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs] using hLpow ω
  have hFirstInt : Integrable (fun ω => (D ω * (M ω - 1)) * Y ω) disorderLaw :=
    hDGint.mul_bdd hYas' hYbounded
  have hRestInt : Integrable (fun ω => D ω * Y ω) disorderLaw :=
    hDint.mul_bdd hYas' hYbounded
  have hsplit (ω : Disorder) :
      truncatedCorrector β t u v ω =
        (D ω * (M ω - 1)) * Y ω + D ω * Y ω := by
    have hprod : (∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω) =
        M ω * Y ω := by
      have hIcc : Finset.Icc u v = insert u (Finset.Icc (u + 1) v) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : u ∉ Finset.Icc (u + 1) v := by simp
      rw [hIcc, Finset.prod_insert hnot]
      simp [M, Y]
    rw [truncatedCorrector, hprod]
    dsimp [D, M, Y]
    ring
  have hcancel' : ∫ ω, D ω * Y ω ∂disorderLaw = 0 := by
    simpa [D] using hcancel
  have hIntegralSplit :
      ∫ ω, truncatedCorrector β t u v ω ∂disorderLaw =
        ∫ ω, (D ω * (M ω - 1)) * Y ω ∂disorderLaw := by
    calc
      ∫ ω, truncatedCorrector β t u v ω ∂disorderLaw =
          ∫ ω, ((D ω * (M ω - 1)) * Y ω + D ω * Y ω) ∂disorderLaw := by
        apply integral_congr_ae
        exact Eventually.of_forall hsplit
      _ = (∫ ω, (D ω * (M ω - 1)) * Y ω ∂disorderLaw) +
          ∫ ω, D ω * Y ω ∂disorderLaw := integral_add hFirstInt hRestInt
      _ = ∫ ω, (D ω * (M ω - 1)) * Y ω ∂disorderLaw := by rw [hcancel']; ring
  have hD2 : ∫ ω, D ω ^ 2 ∂disorderLaw ≤
      (Ck * α ^ (v - u)) ^ 2 / (dU * d) := by
    simpa [D, β, t, α, dU, d, K] using hDiscrepancyStringInputN ϑ hϑ u v hu huv hvK
  have hM2 : ∫ ω, (M ω - 1) ^ 2 ∂disorderLaw ≤
      Cinv / dU := by
    have h := hInvN ϑ hϑ u hu (by omega)
    simpa [M, β, t, dU, K] using h
  let X : ℝ := ∫ ω, D ω ^ 2 ∂disorderLaw
  let Z : ℝ := ∫ ω, (M ω - 1) ^ 2 ∂disorderLaw
  have hXnonneg : 0 ≤ X := by
    dsimp [X]
    exact integral_nonneg (fun ω => sq_nonneg (D ω))
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z]
    exact integral_nonneg (fun ω => sq_nonneg (M ω - 1))
  have hholder := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    Real.HolderConjugate.two_two hDmem hMcenterMem
  have hnormD : ∫ ω, ‖D ω‖ ^ (2 : ℝ) ∂disorderLaw = X := by
    calc
      ∫ ω, ‖D ω‖ ^ (2 : ℝ) ∂disorderLaw =
          ∫ ω, D ω ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp [Real.norm_eq_abs, sq_abs]
      _ = X := rfl
  have hnormM : ∫ ω, ‖M ω - 1‖ ^ (2 : ℝ) ∂disorderLaw = Z := by
    calc
      ∫ ω, ‖M ω - 1‖ ^ (2 : ℝ) ∂disorderLaw =
          ∫ ω, (M ω - 1) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp [Real.norm_eq_abs, sq_abs]
      _ = Z := rfl
  rw [hnormD, hnormM] at hholder
  have hholder' :
      ∫ ω, |D ω| * |M ω - 1| ∂disorderLaw ≤ Real.sqrt X * Real.sqrt Z := by
    simpa only [Real.norm_eq_abs, Real.sqrt_eq_rpow] using hholder
  have hprodAbsInt : Integrable (fun ω => |D ω| * |M ω - 1|) disorderLaw := by
    apply hDGint.norm.congr
    filter_upwards [] with ω
    simp [Real.norm_eq_abs]
  have hmajor : Integrable (fun ω => L * (|D ω| * |M ω - 1|)) disorderLaw :=
    hprodAbsInt.const_mul L
  have hpointAbs (ω : Disorder) :
      |(D ω * (M ω - 1)) * Y ω| ≤ L * (|D ω| * |M ω - 1|) := by
    rw [abs_mul, abs_mul]
    calc
      |D ω| * |M ω - 1| * |Y ω| ≤
          |D ω| * |M ω - 1| * L :=
        mul_le_mul_of_nonneg_left (hLpow ω) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = L * (|D ω| * |M ω - 1|) := by ring
  have hfirstAbs :
      |∫ ω, (D ω * (M ω - 1)) * Y ω ∂disorderLaw| ≤
        L * (Real.sqrt X * Real.sqrt Z) := by
    calc
      |∫ ω, (D ω * (M ω - 1)) * Y ω ∂disorderLaw| ≤
          ∫ ω, |(D ω * (M ω - 1)) * Y ω| ∂disorderLaw := abs_integral_le_integral_abs
      _ ≤ ∫ ω, L * (|D ω| * |M ω - 1|) ∂disorderLaw :=
        integral_mono (hFirstInt.abs) hmajor hpointAbs
      _ = L * ∫ ω, |D ω| * |M ω - 1| ∂disorderLaw := by rw [integral_const_mul]
      _ ≤ L * (Real.sqrt X * Real.sqrt Z) :=
        mul_le_mul_of_nonneg_left hholder' (by positivity)
  let V : ℝ := max Cinv 1
  let a : ℝ := |Ck| * α ^ (v - u)
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hCinvV : Cinv ≤ V := le_max_left _ _
  have hD2small : X ≤ a ^ 2 / d ^ 2 := by
    have hden : d ^ 2 ≤ dU * d := by nlinarith
    have hdiv : (Ck * α ^ (v - u)) ^ 2 / (dU * d) ≤
        (Ck * α ^ (v - u)) ^ 2 / d ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) hdSqpos hden
    have hnum : (Ck * α ^ (v - u)) ^ 2 = a ^ 2 := by
      dsimp [a]
      rw [mul_pow, mul_pow, sq_abs]
    calc
      X ≤ (Ck * α ^ (v - u)) ^ 2 / (dU * d) := by simpa [X] using hD2
      _ ≤ (Ck * α ^ (v - u)) ^ 2 / d ^ 2 := hdiv
      _ = a ^ 2 / d ^ 2 := by rw [hnum]
  have hM2small : Z ≤ V / d := by
    have hfirst : Z ≤ Cinv / dU := by simpa [Z] using hM2
    have hsecond : Cinv / dU ≤ V / dU :=
      div_le_div_of_nonneg_right hCinvV (le_of_lt hdUpos)
    have hthird : V / dU ≤ V / d :=
      div_le_div_of_nonneg_left (le_of_lt hVpos) hdpos hd_le_dU
    exact hfirst.trans (hsecond.trans hthird)
  have hrootD : Real.sqrt X ≤ a / d := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hαpos.le _)) hdpos.le
    · simpa [div_pow] using hD2small
  have hrootZ : Real.sqrt Z ≤ Real.sqrt V / Real.sqrt d := by
    calc
      Real.sqrt Z ≤ Real.sqrt (V / d) := Real.sqrt_le_sqrt hM2small
      _ = Real.sqrt V / Real.sqrt d := Real.sqrt_div hVpos.le d
  have hrootProd :
      L * (Real.sqrt X * Real.sqrt Z) ≤
        C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) / d ^ ((3 : ℝ) / 2) := by
    have hdrootpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
    have hpowD : d ^ ((3 : ℝ) / 2) = d * Real.sqrt d := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hdpos,
        Real.rpow_one, ← Real.sqrt_eq_rpow]
    have halgebra :
        L * ((a / d) * (Real.sqrt V / Real.sqrt d)) =
          (|Ck| * Real.sqrt V) * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
            d ^ ((3 : ℝ) / 2) := by
      dsimp [L, a, C₀]
      rw [hpowD]
      have hpow : (2 : ℝ) ^ (v - u : ℕ) * α ^ (v - u) =
          (2 * α) ^ (v - u) := by rw [mul_pow]
      field_simp [ne_of_gt hdpos, ne_of_gt hdrootpos]
      calc
        2 ^ (v - u : ℕ) * |Ck| * α ^ (v - u) =
            |Ck| * (2 ^ (v - u : ℕ) * α ^ (v - u)) := by ring
        _ = |Ck| * (2 * α) ^ (v - u) := by rw [hpow]
        _ = |Ck| * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) := by
          congr 2
          dsimp [α, C₀]
          ring
    have hCeq :
        (|Ck| * Real.sqrt V) * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) =
          C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) := by
      rfl
    calc
      L * (Real.sqrt X * Real.sqrt Z) ≤ L * ((a / d) * (Real.sqrt V / Real.sqrt d)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hrootD hrootZ (by positivity) (by positivity)
      _ = C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
            d ^ ((3 : ℝ) / 2) := by rw [halgebra, hCeq]
  calc
    |∫ ω, truncatedCorrector β t u v ω ∂disorderLaw| =
        |∫ ω, (D ω * (M ω - 1)) * Y ω ∂disorderLaw| := by rw [hIntegralSplit]
    _ ≤ L * (Real.sqrt X * Real.sqrt Z) := hfirstAbs
    _ ≤ C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
          d ^ ((3 : ℝ) / 2) := hrootProd
    _ = C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
          ((blockCount N ρ : ℝ) - v) ^ ((3 : ℝ) / 2) := by rfl

/-- A closed discrepancy times a finite product of squared truncated inverses is integrable. -/
theorem integrable_closedDiscrepancy_mul_truncatedInverse_sq_prod
    (β : ℝ) (t : ℕ → ℕ) (u v : ℕ) :
    Integrable (fun ω => closedDiscrepancy β t u v ω *
      ∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω ^ 2) disorderLaw := by
  classical
  let Y : Disorder → ℝ := fun ω =>
    ∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω ^ 2
  have hYmeas : Measurable Y := by
    dsimp [Y]
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_truncatedInverse β t i).pow_const 2
  have hYbound : ∀ ω, ‖Y ω‖ ≤ 4 ^ (Finset.Icc u v).card := by
    intro ω
    have hterm (i : ℕ) : |truncatedInverse β t i ω ^ 2| ≤ 4 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have hM := truncatedInverse_nonneg_le_two β t i ω
      nlinarith
    dsimp [Y]
    rw [Finset.abs_prod]
    calc
      ∏ i ∈ Finset.Icc u v, |truncatedInverse β t i ω ^ 2| ≤
          ∏ _i ∈ Finset.Icc u v, (4 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          exact hterm i
      _ = 4 ^ (Finset.Icc u v).card := by simp
  have hDmem : MemLp (closedDiscrepancy β t u v)
      (ENNReal.ofReal (2 : ℝ)) disorderLaw :=
    memLp_closedDiscrepancy β t u v (ENNReal.ofReal (2 : ℝ)) (by norm_num) (by norm_num)
  have hDint := hDmem.integrable (by norm_num)
  have hYbounded : ∀ᵐ ω ∂disorderLaw, ‖Y ω‖ ≤ 4 ^ (Finset.Icc u v).card :=
    Eventually.of_forall hYbound
  exact hDint.mul_bdd hYmeas.aestronglyMeasurable hYbounded

/-- Cancellation at the first block bounds the mean of a closed discrepancy weighted by squared truncated inverses with an inverse three-halves endpoint-distance factor. -/
theorem abs_integral_closedDiscrepancy_mul_truncatedInverse_sq_prod_le (A : ℝ) :
    ∃ C₀ ρ₀ C : ℝ, 0 < C₀ ∧ 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ u v : ℕ, 1 ≤ u → u < v → v + 1 ≤ blockCount N ρ →
          |∫ ω, closedDiscrepancy (criticalBeta ϑ N) (blockTime N ρ) u v ω *
              ∏ i ∈ Finset.Icc u v,
                truncatedInverse (criticalBeta ϑ N) (blockTime N ρ) i ω ^ 2
              ∂disorderLaw| ≤
            C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
              ((blockCount N ρ : ℝ) - v) ^ ((3 : ℝ) / 2) := by
  obtain ⟨Ck, Ck₀, hCk₀, hDiscrepancyStringInput⟩ :=
    Critical2DKPZ.Blocks.closedDiscrepancy_sq_integral_le A
  obtain ⟨Cinv, hInv⟩ := integral_truncatedInverse_sub_one_sq_le A 2 (by norm_num)
  let ρ₀ : ℝ := max (Real.exp (Ck₀ ^ 2) + 1) 2
  let C₀ : ℝ := 4 * Ck₀
  let V : ℝ := max Cinv 1
  let C : ℝ := 3 * |Ck| * Real.sqrt V
  have hρ₀ : 1 < ρ₀ := by
    dsimp [ρ₀]
    exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hC₀pos : 0 < C₀ := by dsimp [C₀]; positivity
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C₀, ρ₀, C, hC₀pos, hρ₀, ?_⟩
  intro ρ hρ
  have hρexp : Real.exp (Ck₀ ^ 2) < ρ := by
    have h := le_trans (le_max_left _ _) hρ
    have h' : Real.exp (Ck₀ ^ 2) + 1 ≤ ρ := by simpa [ρ₀] using h
    linarith
  have hρtwo : 2 ≤ ρ := le_trans (le_max_right _ _) hρ
  have hlog : Ck₀ ^ 2 < Real.log ρ := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hρexp
  have hNclock : ∀ᶠ N : ℕ in atTop,
      ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N := Filter.eventually_ge_atTop _
  filter_upwards [hDiscrepancyStringInput ρ hρexp, hInv ρ hρtwo, hNclock] with N hDiscrepancyStringInputN hInvN hNclock
  intro ϑ hϑ u v hu huv hvK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let K := blockCount N ρ
  let dU : ℝ := (K : ℝ) - u
  let d : ℝ := (K : ℝ) - v
  let α : ℝ := Ck₀ / Real.sqrt (Real.log ρ)
  let L : ℝ := 4 ^ (v - u : ℕ)
  let D : Disorder → ℝ := closedDiscrepancy β t u v
  let M : Disorder → ℝ := truncatedInverse β t u
  let Y : Disorder → ℝ := fun ω =>
    ∏ i ∈ Finset.Icc (u + 1) v, truncatedInverse β t i ω ^ 2
  have hρpos : 0 < ρ := by linarith
  have hdpos : 0 < d := by
    dsimp [d, K]
    have hnat : v < blockCount N ρ := by omega
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hdUpos : 0 < dU := by
    dsimp [dU, K]
    have hnat : u < blockCount N ρ := by omega
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hd_le_dU : d ≤ dU := by
    dsimp [d, dU, K]
    have huvR : (u : ℝ) < (v : ℝ) := by exact_mod_cast huv
    linarith
  have ht : Monotone t := by
    exact Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon hρ₀
      hρ hNclock
  have hYmeas : Measurable[Gaussian.disorderBlock (t u) (t v)] Y := by
    let Yval : Disorder → ℝ := fun ω =>
      ∏ i ∈ Finset.Icc (u + 1) v, truncatedInverse β t i ω ^ 2
    have hYval : Measurable[Gaussian.disorderBlock (t u) (t v)] Yval := by
      dsimp [Yval]
      apply Finset.measurable_prod
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hstart : t u ≤ t (i - 1) := ht (by omega)
      have hstop : t i ≤ t v := ht hi'.2
      exact (measurable_truncatedInverse_block β t i).pow_const 2 |>.mono
        (Gaussian.disorderBlock_mono hstart hstop) le_rfl
    have hYeq : Y = Yval := by
      funext ω
      rfl
    rw [hYeq]
    exact hYval
  have hLpow (ω : Disorder) : |Y ω| ≤ L := by
    dsimp [Y, L]
    rw [Finset.abs_prod]
    calc
      ∏ i ∈ Finset.Icc (u + 1) v,
          |truncatedInverse β t i ω ^ 2| ≤
        ∏ _i ∈ Finset.Icc (u + 1) v, (4 : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact abs_nonneg _
          · intro i hi
            rw [abs_of_nonneg (sq_nonneg _)]
            have hM := truncatedInverse_nonneg_le_two β t i ω
            nlinarith
      _ = 4 ^ (v - u : ℕ) := by
        rw [Finset.prod_const]
        have hcard : (Finset.Icc (u + 1) v).card = v - u := by
          simp only [Nat.card_Icc]
          omega
        rw [hcard]
  have hYmeas' : AEStronglyMeasurable Y disorderLaw :=
    (hYmeas.mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable
  have hYbounded : ∀ᵐ ω ∂disorderLaw, ‖Y ω‖ ≤ L := by
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs] using hLpow ω
  have hYbound : ∃ B : ℝ, ∀ ω, |Y ω| ≤ B := ⟨L, hLpow⟩
  have hcancel := Critical2DKPZ.Blocks.closedDiscrepancy_integral_mul_eq_zero
    β t ht u v hu huv Y hYmeas hYbound
  have hMrange : ∀ ω, 0 ≤ M ω ∧ M ω ≤ 2 := by
    intro ω
    exact truncatedInverse_nonneg_le_two β t u ω
  have hMmeas : Measurable M := measurable_truncatedInverse β t u
  have hMcenterMem : MemLp (fun ω => M ω - 1)
      (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    apply MemLp.of_bound (hMmeas.sub measurable_const).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    change |M ω - 1| ≤ 1
    apply abs_le.mpr
    exact ⟨by linarith [(hMrange ω).1], by linarith [(hMrange ω).2]⟩
  have hM2centerMem : MemLp (fun ω => M ω ^ 2 - 1)
      (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    apply MemLp.of_bound ((hMmeas.pow_const 2).sub measurable_const).aestronglyMeasurable 3
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    change |M ω ^ 2 - 1| ≤ 3
    apply abs_le.mpr
    have hsquare : 0 ≤ M ω ^ 2 ∧ M ω ^ 2 ≤ 4 := by
      constructor
      · exact sq_nonneg _
      · nlinarith [sq_nonneg (M ω - 2), (hMrange ω).1, (hMrange ω).2]
    exact ⟨by linarith [hsquare.1], by linarith [hsquare.2]⟩
  have hDmem : MemLp D (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
    dsimp [D, β, t]
    exact memLp_closedDiscrepancy _ _ _ _ (ENNReal.ofReal (2 : ℝ))
      (by norm_num) (by norm_num)
  have hDGmem : MemLp (fun ω => D ω * (M ω ^ 2 - 1)) 1 disorderLaw := by
    have htriple : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) 1 := Real.HolderConjugate.two_two.ennrealOfReal
    exact @MemLp.mul Disorder inferInstance ℝ inferInstance disorderLaw
      (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1
      (fun ω => M ω ^ 2 - 1) D hDmem hM2centerMem htriple
  have hDGint : Integrable (fun ω => D ω * (M ω ^ 2 - 1)) disorderLaw :=
    hDGmem.integrable (by norm_num)
  have hDint : Integrable D disorderLaw := hDmem.integrable (by norm_num)
  have hFirstInt : Integrable (fun ω => (D ω * (M ω ^ 2 - 1)) * Y ω) disorderLaw :=
    hDGint.mul_bdd hYmeas' hYbounded
  have hRestInt : Integrable (fun ω => D ω * Y ω) disorderLaw :=
    hDint.mul_bdd hYmeas' hYbounded
  have hsplit (ω : Disorder) :
      D ω * (∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω ^ 2) =
        (D ω * (M ω ^ 2 - 1)) * Y ω + D ω * Y ω := by
    have hIcc : Finset.Icc u v = insert u (Finset.Icc (u + 1) v) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : u ∉ Finset.Icc (u + 1) v := by simp
    have hprod : ∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω ^ 2 = M ω ^ 2 * Y ω := by
      rw [hIcc, Finset.prod_insert hnot]
    rw [hprod]
    dsimp [D, M, Y]
    ring
  have hcancel' : ∫ ω, D ω * Y ω ∂disorderLaw = 0 := by
    simpa [D] using hcancel
  have hIntegralSplit :
      ∫ ω, D ω * (∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω ^ 2)
          ∂disorderLaw = ∫ ω, (D ω * (M ω ^ 2 - 1)) * Y ω ∂disorderLaw := by
    calc
      ∫ ω, D ω * (∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω ^ 2)
          ∂disorderLaw =
        ∫ ω, ((D ω * (M ω ^ 2 - 1)) * Y ω + D ω * Y ω) ∂disorderLaw := by
          apply integral_congr_ae
          exact Eventually.of_forall hsplit
      _ = (∫ ω, (D ω * (M ω ^ 2 - 1)) * Y ω ∂disorderLaw) +
          ∫ ω, D ω * Y ω ∂disorderLaw := integral_add hFirstInt hRestInt
      _ = ∫ ω, (D ω * (M ω ^ 2 - 1)) * Y ω ∂disorderLaw := by rw [hcancel']; ring
  have hD2 : ∫ ω, D ω ^ 2 ∂disorderLaw ≤
      (Ck * α ^ (v - u)) ^ 2 / (dU * d) := by
    simpa [D, β, t, α, dU, d, K] using hDiscrepancyStringInputN ϑ hϑ u v hu huv hvK
  have hMcenterInt : Integrable (fun ω => (M ω - 1) ^ 2) disorderLaw := by
    have hmem : MemLp (fun ω => (M ω - 1) ^ 2) (ENNReal.ofReal (1 : ℝ)) disorderLaw := by
      apply MemLp.of_bound ((hMmeas.sub measurable_const).pow_const 2).aestronglyMeasurable 1
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hM := hMrange ω
      have hAbs : |M ω - 1| ≤ 1 := by
        apply abs_le.mpr
        exact ⟨by linarith [hM.1], by linarith [hM.2]⟩
      calc
        (M ω - 1) ^ 2 = |M ω - 1| ^ 2 := (sq_abs _).symm
        _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAbs 2
        _ = 1 := by norm_num
    exact hmem.integrable (by norm_num)
  have hM2centerInt : Integrable (fun ω => (M ω ^ 2 - 1) ^ 2) disorderLaw := by
    have hmem : MemLp (fun ω => (M ω ^ 2 - 1) ^ 2) (ENNReal.ofReal (1 : ℝ)) disorderLaw := by
      have hmeas : Measurable (fun ω => (M ω ^ 2 - 1) ^ 2) :=
        ((hMmeas.pow_const 2).sub measurable_const).pow_const 2
      apply MemLp.of_bound hmeas.aestronglyMeasurable 9
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hM := hMrange ω
      have hsq : 0 ≤ M ω ^ 2 ∧ M ω ^ 2 ≤ 4 := by
        constructor
        · exact sq_nonneg _
        · nlinarith [sq_nonneg (M ω - 2), hM.1, hM.2]
      have hAbs : |M ω ^ 2 - 1| ≤ 3 := by
        apply abs_le.mpr
        exact ⟨by linarith [hsq.1], by linarith [hsq.2]⟩
      calc
        (M ω ^ 2 - 1) ^ 2 = |M ω ^ 2 - 1| ^ 2 := (sq_abs _).symm
        _ ≤ 3 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hAbs 2
        _ = 9 := by norm_num
    exact hmem.integrable (by norm_num)
  have hMdefect : ∫ ω, (M ω - 1) ^ 2 ∂disorderLaw ≤ Cinv / dU := by
    have h := hInvN ϑ hϑ u hu (by omega)
    simpa [M, β, t, dU, K] using h
  have hM2defect : ∫ ω, (M ω ^ 2 - 1) ^ 2 ∂disorderLaw ≤ 9 * V / d := by
    have hpoint (ω : Disorder) : (M ω ^ 2 - 1) ^ 2 ≤ 9 * (M ω - 1) ^ 2 := by
      have hfactor : M ω ^ 2 - 1 = (M ω - 1) * (M ω + 1) := by ring
      rw [hfactor, mul_pow]
      have hplus : (M ω + 1) ^ 2 ≤ 9 := by nlinarith [(hMrange ω).1, (hMrange ω).2]
      calc
        (M ω - 1) ^ 2 * (M ω + 1) ^ 2 ≤ (M ω - 1) ^ 2 * 9 :=
          mul_le_mul_of_nonneg_left hplus (sq_nonneg _)
        _ = 9 * (M ω - 1) ^ 2 := by ring
    have hfirst : ∫ ω, (M ω ^ 2 - 1) ^ 2 ∂disorderLaw ≤
        9 * ∫ ω, (M ω - 1) ^ 2 ∂disorderLaw := by
      calc
        ∫ ω, (M ω ^ 2 - 1) ^ 2 ∂disorderLaw ≤
            ∫ ω, 9 * (M ω - 1) ^ 2 ∂disorderLaw :=
          integral_mono hM2centerInt (hMcenterInt.const_mul 9) hpoint
        _ = 9 * ∫ ω, (M ω - 1) ^ 2 ∂disorderLaw := by rw [integral_const_mul]
    have hVlarge : Cinv ≤ V := by dsimp [V]; exact le_max_left _ _
    calc
      ∫ ω, (M ω ^ 2 - 1) ^ 2 ∂disorderLaw ≤ 9 * (Cinv / dU) :=
        hfirst.trans (mul_le_mul_of_nonneg_left hMdefect (by norm_num))
      _ = 9 * Cinv / dU := by ring
      _ ≤ 9 * V / dU := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hVlarge (by norm_num)) hdUpos.le
      _ ≤ 9 * V / d := div_le_div_of_nonneg_left
        (by positivity) hdpos hd_le_dU
  let X : ℝ := ∫ ω, D ω ^ 2 ∂disorderLaw
  let Z : ℝ := ∫ ω, (M ω ^ 2 - 1) ^ 2 ∂disorderLaw
  have hXnonneg : 0 ≤ X := by dsimp [X]; exact integral_nonneg fun ω => sq_nonneg (D ω)
  have hZnonneg : 0 ≤ Z := by dsimp [Z]; exact integral_nonneg fun ω => sq_nonneg (M ω ^ 2 - 1)
  have hholder := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    Real.HolderConjugate.two_two hDmem hM2centerMem
  have hnormD : ∫ ω, ‖D ω‖ ^ (2 : ℝ) ∂disorderLaw = X := by
    dsimp [X]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [sq_abs]
  have hnormM : ∫ ω, ‖M ω ^ 2 - 1‖ ^ (2 : ℝ) ∂disorderLaw = Z := by
    dsimp [Z]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [sq_abs]
  rw [hnormD, hnormM] at hholder
  have hholder' :
      ∫ ω, |D ω| * |M ω ^ 2 - 1| ∂disorderLaw ≤ Real.sqrt X * Real.sqrt Z := by
    simpa only [Real.norm_eq_abs, Real.sqrt_eq_rpow] using hholder
  have hprodAbsInt : Integrable (fun ω => |D ω| * |M ω ^ 2 - 1|) disorderLaw := by
    apply hDGint.norm.congr
    filter_upwards [] with ω
    simp [Real.norm_eq_abs]
  have hmajor : Integrable (fun ω => L * (|D ω| * |M ω ^ 2 - 1|)) disorderLaw :=
    hprodAbsInt.const_mul L
  have hpointAbs (ω : Disorder) :
      |(D ω * (M ω ^ 2 - 1)) * Y ω| ≤ L * (|D ω| * |M ω ^ 2 - 1|) := by
    rw [abs_mul, abs_mul]
    calc
      |D ω| * |M ω ^ 2 - 1| * |Y ω| ≤
          |D ω| * |M ω ^ 2 - 1| * L :=
        mul_le_mul_of_nonneg_left (hLpow ω)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = L * (|D ω| * |M ω ^ 2 - 1|) := by ring
  have hfirstAbs :
      |∫ ω, (D ω * (M ω ^ 2 - 1)) * Y ω ∂disorderLaw| ≤
        L * (Real.sqrt X * Real.sqrt Z) := by
    calc
      |∫ ω, (D ω * (M ω ^ 2 - 1)) * Y ω ∂disorderLaw| ≤
          ∫ ω, |(D ω * (M ω ^ 2 - 1)) * Y ω| ∂disorderLaw := abs_integral_le_integral_abs
      _ ≤ ∫ ω, L * (|D ω| * |M ω ^ 2 - 1|) ∂disorderLaw :=
        integral_mono hFirstInt.abs hmajor hpointAbs
      _ = L * ∫ ω, |D ω| * |M ω ^ 2 - 1| ∂disorderLaw := by rw [integral_const_mul]
      _ ≤ L * (Real.sqrt X * Real.sqrt Z) :=
        mul_le_mul_of_nonneg_left hholder' (by positivity)
  let a : ℝ := |Ck| * α ^ (v - u)
  have hD2small : X ≤ a ^ 2 / d ^ 2 := by
    have hden : d ^ 2 ≤ dU * d := by nlinarith
    have hdiv : (Ck * α ^ (v - u)) ^ 2 / (dU * d) ≤
        (Ck * α ^ (v - u)) ^ 2 / d ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hdpos) hden
    have hnum : (Ck * α ^ (v - u)) ^ 2 = a ^ 2 := by
      dsimp [a]
      calc
        (Ck * α ^ (v - u)) ^ 2 = Ck ^ 2 * (α ^ (v - u)) ^ 2 := by rw [mul_pow]
        _ = |Ck| ^ 2 * (α ^ (v - u)) ^ 2 := by rw [← sq_abs]
        _ = (|Ck| * α ^ (v - u)) ^ 2 := by rw [mul_pow]
    calc
      X ≤ (Ck * α ^ (v - u)) ^ 2 / (dU * d) := by simpa [X] using hD2
      _ ≤ (Ck * α ^ (v - u)) ^ 2 / d ^ 2 := hdiv
      _ = a ^ 2 / d ^ 2 := by rw [hnum]
  have hrootD : Real.sqrt X ≤ a / d := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _)) hdpos.le
    · simpa [div_pow] using hD2small
  have hrootZ : Real.sqrt Z ≤ 3 * Real.sqrt V / Real.sqrt d := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hdroot : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hdpos.le
      have hVroot : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hVpos.le
      calc
        Z ≤ 9 * V / d := hM2defect
        _ = (3 * Real.sqrt V / Real.sqrt d) ^ 2 := by
          rw [div_pow, mul_pow, hVroot, hdroot]
          norm_num
  have hpowD : d ^ ((3 : ℝ) / 2) = d * Real.sqrt d := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hdpos,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hrootProd : L * (Real.sqrt X * Real.sqrt Z) ≤
      C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) / d ^ ((3 : ℝ) / 2) := by
    have hdrootpos : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
    have halgebra :
        L * ((a / d) * (3 * Real.sqrt V / Real.sqrt d)) =
          C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
            d ^ ((3 : ℝ) / 2) := by
      dsimp [L, a, C, C₀, V, α]
      rw [hpowD]
      have hpow : (4 : ℝ) ^ (v - u : ℕ) *
          (Ck₀ / Real.sqrt (Real.log ρ)) ^ (v - u) =
            (4 * (Ck₀ / Real.sqrt (Real.log ρ))) ^ (v - u) := by rw [mul_pow]
      field_simp [ne_of_gt hdpos, ne_of_gt hdrootpos]
      calc
        4 ^ (v - u : ℕ) * |Ck| * (Ck₀ / Real.sqrt (Real.log ρ)) ^ (v - u) =
            |Ck| * (4 ^ (v - u : ℕ) *
              (Ck₀ / Real.sqrt (Real.log ρ)) ^ (v - u)) := by ring
        _ = |Ck| * (4 * (Ck₀ / Real.sqrt (Real.log ρ))) ^ (v - u) := by rw [hpow]
        _ = |Ck| * (Ck₀ * 4 / Real.sqrt (Real.log ρ)) ^ (v - u) := by
          congr 2
          ring
    calc
      L * (Real.sqrt X * Real.sqrt Z) ≤ L * ((a / d) *
          (3 * Real.sqrt V / Real.sqrt d)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hrootD hrootZ (by positivity) (by positivity)
      _ = C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
            d ^ ((3 : ℝ) / 2) := halgebra
  calc
    |∫ ω, D ω * (∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω ^ 2)
          ∂disorderLaw| =
        |∫ ω, (D ω * (M ω ^ 2 - 1)) * Y ω ∂disorderLaw| := by rw [hIntegralSplit]
    _ ≤ L * (Real.sqrt X * Real.sqrt Z) := hfirstAbs
    _ ≤ C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
          d ^ ((3 : ℝ) / 2) := hrootProd
    _ = C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
          ((blockCount N ρ : ℝ) - v) ^ ((3 : ℝ) / 2) := by rfl


end Critical2DKPZ.OnePoint

end
