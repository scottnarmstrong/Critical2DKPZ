/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Expansion
public import Critical2DKPZ.FutureProfiles.Basic
public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawMomentBounds
import Critical2DKPZ.LogNormality.LatticeInputs
import Critical2DKPZ.FutureProfiles.ProfileEstimates
import Critical2DKPZ.OnePoint.BlockRatioOriginalLawEstimates
import Critical2DKPZ.Provider.BlockMoments
import Critical2DKPZ.Extensions.GffTangent.ProfileIdentities
import Critical2DKPZ.Blocks.OpenDiscrepancyStringBounds
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lattice endpoint profiles with the common first-order correction removed

The common correction is independent of the entrance. Subtracting it leaves
ratio differences multiplying open activities, as in Lemma 6.3 of the note.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

open Blocks FutureProfiles

/-- Every normalized block ratio is strictly positive. -/
theorem profile_blockRatio_pos (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) (ω : Disorder) :
    0 < blockRatio β t r s ω := by
  unfold blockRatio
  exact div_pos (Polymer.smoothedP2Plane_pos β _ _ _ ω)
    (Finset.prod_pos fun k _ => blockMass_pos β t k ω)

/-- Removing the common first-order correction from the endpoint expansion
leaves only ratio differences. -/
theorem profile_expansion_identity (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) (ω : Disorder) (y : Site) :
    smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
      commonCorrection β t r s ω y =
      (blockRatio β t r s ω)⁻¹ * ∑ u ∈ Finset.Icc r s,
        (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) * openCorrector β t u s ω y := by
  rw [smoothedEndpointDist_block_expansion β t ht r s hr hrs ω y]
  unfold commonCorrection
  have hsum : (∑ u ∈ Finset.Icc r s,
      (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) * openCorrector β t u s ω y) =
      (∑ u ∈ Finset.Icc r s, blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) -
        blockRatio β t r s ω * ∑ u ∈ Finset.Icc r s, openCorrector β t u s ω y := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum]
  field_simp [ne_of_gt (profile_blockRatio_pos β t r s ω)]
  ring

/-- The profile-good event controls the reciprocal endpoint ratio. -/
theorem inv_blockRatio_le_two_of_mem_profileGoodSet (β : ℝ) (t : ℕ → ℕ)
    (r s : ℕ) {ω : Disorder} (hω : ω ∈ profileGoodSet β t r s) :
    (blockRatio β t r s ω)⁻¹ ≤ 2 := by
  have habs := hω.2
  change |blockRatio β t r s ω - 1| ≤ (1 / 2 : ℝ) at habs
  have h := (abs_le.mp habs).1
  rw [← one_div]
  apply (div_le_iff₀ (profile_blockRatio_pos β t r s ω)).mpr
  linarith only [h]

/-- A single past-measurable event works for both entrance profiles. -/
def profileComparisonGoodSet (β : ℝ) (t : ℕ → ℕ) (i j s : ℕ) : Set Disorder :=
  profileGoodSet β t i s ∩ profileGoodSet β t j s

/-- The comparison event is measurable before the observation time. -/
theorem measurableSet_profileComparisonGoodSet_past (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {i j s : ℕ} (hi : 1 ≤ i) (his : i ≤ s) (hj : 1 ≤ j) (hjs : j ≤ s) :
    MeasurableSet[disorderPast (t s)] (profileComparisonGoodSet β t i j s) :=
  (LogNormality.measurableSet_profileGoodSet_past β ht hi his).inter
    (LogNormality.measurableSet_profileGoodSet_past β ht hj hjs)

/-- The probability estimate for profile-good events, with the main-library
block moment input discharged. -/
theorem profileGoodSet_compl_bound (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
          (disorderLaw (profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
            C / ((blockCount N ρ : ℝ) - s) := by
  apply measure_profileGoodSet_compl_le_of ?_ A
  intro B
  obtain ⟨ρ₀, hρ₀, hbound⟩ := OnePoint.blockGoodSet_compl_and_ratio_bound_of Provider.blockMoments B
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨C, hC⟩ := hbound ρ₁
  refine ⟨C, ?_⟩
  intro ρ hρ
  filter_upwards [hC ρ hρ] with N hN
  intro ϑ hϑ r s hr hrs hsK
  exact hN ϑ hϑ r s hr hrs hsK

/-- The block ratio uses only disorder between its entrance and observation times. -/
theorem measurable_profileBlockRatio_block (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)] (blockRatio β t r s) := by
  have hnum := Polymer.measurable_smoothedP2Plane_block β (t (r - 1)) (t s)
    (ht (by omega)) 0
  have hden : Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)]
      (fun ω => ∏ k ∈ Finset.Icc r s, blockMass β t k ω) := by
    apply Finset.measurable_prod
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact (measurable_blockMass β t k).mono
      (Gaussian.disorderBlock_mono (ht (by omega)) (ht hk'.2)) le_rfl
  exact hnum.div hden

/-- The block-good event is measurable in exactly its constituent time block. -/
theorem measurableSet_profileBlockGoodSet_block (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) :
    MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t s)] (blockGoodSet β t r s) := by
  let profileBlockSpace : MeasurableSpace Disorder := Gaussian.disorderBlock (t (r - 1)) (t s)
  have hm (k : ℕ) (hk : k ∈ Finset.Icc r s) :
      Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)] (blockMass β t k) := by
    have hk' := Finset.mem_Icc.mp hk
    exact (measurable_blockMass β t k).mono
      (Gaussian.disorderBlock_mono (ht (by omega)) (ht hk'.2)) le_rfl
  have h : MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t s)]
      (⋂ k ∈ Finset.Icc r s, {ω : Disorder | |blockMass β t k ω - 1| ≤ (1 / 2 : ℝ)}) := by
    apply Finset.measurableSet_biInter
    intro k hk
    exact measurableSet_le ((hm k hk).sub measurable_const).abs measurable_const
  convert h using 1
  ext ω
  simp only [blockGoodSet, Set.mem_ofPred_eq, Set.mem_iInter]

/-- The entrance ratio truncated to its block-good event. Its local measurability
is supplied by `measurable_truncatedProfileRatio_block`. -/
def truncatedProfileRatio (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) : Disorder → ℝ :=
  (blockGoodSet β t r s).indicator (blockRatio β t r s)

/-- Local measurability of the truncated ratio, including an empty prefix. -/
theorem measurable_truncatedProfileRatio_block (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s + 1) :
    Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)] (truncatedProfileRatio β t r s) := by
  by_cases h : r ≤ s
  · exact (measurable_profileBlockRatio_block β ht hr h).indicator
      (measurableSet_profileBlockGoodSet_block β ht hr)
  · have hs : s = r - 1 := by omega
    subst s
    have heq : truncatedProfileRatio β t r (r - 1) = fun _ => 1 := by
      funext ω
      have hg : ω ∈ blockGoodSet β t r (r - 1) := by
        change ∀ k ∈ Finset.Icc r (r - 1), |blockMass β t k ω - 1| ≤ (1 / 2 : ℝ)
        simp only [Finset.Icc_eq_empty_of_lt (show r - 1 < r by omega), Finset.notMem_empty,
          false_implies, implies_true]
      change (blockGoodSet β t r (r - 1)).indicator (blockRatio β t r (r - 1)) ω = 1
      rw [Set.indicator_of_mem hg, blockRatio_empty β t r hr]
    rw [heq]
    exact measurable_const

/-- The truncated closed activity is measurable on its own interval, which
allows independence from the preceding ratio. -/
theorem measurable_profileTruncatedCorrector_block (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {u v : ℕ} (huv : u ≤ v) :
    Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)] (OnePoint.truncatedCorrector β t u v) := by
  have hprod : Measurable[Gaussian.disorderBlock (t (u - 1)) (t v)]
      (fun ω => ∏ k ∈ Finset.Icc u v, OnePoint.truncatedInverse β t k ω) := by
    apply Finset.measurable_prod
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact (OnePoint.measurable_truncatedInverse_block β t k).mono
      (Gaussian.disorderBlock_mono (ht (by omega)) (ht hk'.2)) le_rfl
  exact (measurable_closedDiscrepancy β t ht u v huv).mul hprod

/-- The truncated preceding ratio and the closed activity use disjoint disorder. -/
theorem indepFun_profileRatio_corrector (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r u v : ℕ} (hr : 1 ≤ r) (hru : r ≤ u) (huv : u < v) :
    ProbabilityTheory.IndepFun (truncatedProfileRatio β t r (u - 1))
      (OnePoint.truncatedCorrector β t u v) disorderLaw := by
  rw [ProbabilityTheory.IndepFun_iff_Indep]
  exact ProbabilityTheory.indep_of_indep_of_le
    (Gaussian.indep_disorderBlock_of_le (le_refl (t (u - 1))))
    (measurable_truncatedProfileRatio_block β ht hr (by omega)).comap_le
    (measurable_profileTruncatedCorrector_block β ht huv.le).comap_le

/-- On the block-good event, the preceding ratio is square integrable. -/
theorem memLp_profileBlockRatio_restrict_good (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    MemLp (blockRatio β t r s) 2 (disorderLaw.restrict (blockGoodSet β t r s)) := by
  have hmeas : Measurable (blockRatio β t r s) :=
    (measurable_profileBlockRatio_block β ht hr hrs).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hdev := OnePoint.integrableOn_blockRatio_sub_one_sq β ht hr hrs
  have hmem := (memLp_two_iff_integrable_sq
    (hmeas.sub measurable_const).aestronglyMeasurable.restrict).mpr hdev
  have heq : ((blockRatio β t r s - fun _ => (1 : ℝ)) + fun _ => (1 : ℝ)) =ᵐ[
      disorderLaw.restrict (blockGoodSet β t r s)] blockRatio β t r s := by
    filter_upwards [] with ω
    change blockRatio β t r s ω - 1 + 1 = blockRatio β t r s ω
    ring
  exact (memLp_congr_ae heq).mp (hmem.add (memLp_const (1 : ℝ)))

/-- The square of the truncated ratio is integrable; an empty prefix is included. -/
theorem integrable_sq_truncatedProfileRatio (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s + 1) :
    Integrable (fun ω => truncatedProfileRatio β t r s ω ^ 2) disorderLaw := by
  by_cases h : r ≤ s
  · have hm := (memLp_indicator_iff_restrict (OnePoint.measurableSet_blockGoodSet β t r s)).mpr
      (memLp_profileBlockRatio_restrict_good β ht hr h)
    exact hm.integrable_sq
  · have hs : s = r - 1 := by omega
    subst s
    have heq : (fun ω => truncatedProfileRatio β t r (r - 1) ω ^ 2) = fun _ => 1 := by
      funext ω
      have hg : ω ∈ blockGoodSet β t r (r - 1) := by
        change ∀ k ∈ Finset.Icc r (r - 1), |blockMass β t k ω - 1| ≤ (1 / 2 : ℝ)
        intro k hk
        have hk' := Finset.mem_Icc.mp hk
        omega
      change ((blockGoodSet β t r (r - 1)).indicator (blockRatio β t r (r - 1)) ω) ^ 2 = 1
      rw [Set.indicator_of_mem hg, blockRatio_empty β t r hr, one_pow]
    rw [heq]
    exact integrable_const 1

/-- The good-set second moment of a ratio is uniformly bounded independently
of the length of its earlier entrance prefix. -/
theorem integral_sq_profileBlockRatio_good_le (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
          IntegrableOn (fun ω => blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω ^ 2)
            (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s) disorderLaw ∧
          (∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
            blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω ^ 2 ∂disorderLaw) ≤ C := by
  obtain ⟨ρ₀, hρ₀, hbound⟩ := OnePoint.blockGoodSet_compl_and_ratio_bound_of Provider.blockMoments A
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨B, hB⟩ := hbound ρ₁
  refine ⟨2 * |B| + 2, by positivity, ?_⟩
  intro ρ hρ
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ.1
  filter_upwards [hB ρ hρ, blockTime_monotone hρ1] with N hN ht
  intro ϑ hϑ r s hr hrs hsK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let G := blockGoodSet β t r s
  have hR := (memLp_profileBlockRatio_restrict_good β ht hr hrs).integrable_sq
  refine ⟨hR, ?_⟩
  have hdev := OnePoint.integrableOn_blockRatio_sub_one_sq β ht hr hrs
  have hmaj : Integrable (fun ω => 2 * (blockRatio β t r s ω - 1) ^ 2 + 2)
      (disorderLaw.restrict G) := (hdev.const_mul 2).add (integrable_const 2)
  have hpoly (ω : Disorder) : blockRatio β t r s ω ^ 2 ≤ 2 * (blockRatio β t r s ω - 1) ^ 2 + 2 := by
    nlinarith only [sq_nonneg (blockRatio β t r s ω - 2)]
  have hb := (hN ϑ hϑ r s hr hrs hsK).2
  have hD : (1 : ℝ) ≤ (blockCount N ρ : ℝ) - s := by
    have hcast : (s : ℝ) + 1 ≤ (blockCount N ρ : ℝ) := by exact_mod_cast hsK
    linarith only [hcast]
  have hfrac : B / ((blockCount N ρ : ℝ) - s) ≤ |B| :=
    (div_le_div_of_nonneg_right (le_abs_self B) (by linarith only [hD])).trans
      (div_le_self (abs_nonneg _) hD)
  have hmass : (disorderLaw G).toReal ≤ 1 := by
    exact measureReal_le_one (μ := disorderLaw) (s := G)
  calc
    _ ≤ ∫ ω, 2 * (blockRatio β t r s ω - 1) ^ 2 + 2 ∂(disorderLaw.restrict G) :=
      integral_mono hR hmaj hpoly
    _ = 2 * (∫ ω in G, (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw) +
        (disorderLaw G).toReal * 2 := by
      rw [integral_add (hdev.const_mul 2) (integrable_const 2), integral_const_mul, integral_const]
      simp only [Measure.restrict_apply_univ, Measure.real_def, smul_eq_mul, G, t]
    _ ≤ _ := by linarith only [hb, hfrac, hmass]

/-- Squared moments of the truncated prefix and activity factor exactly. -/
theorem integral_sq_profileRatio_corrector_eq (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r u v : ℕ} (hr : 1 ≤ r) (hru : r ≤ u) (huv : u < v) :
    (∫ ω, (truncatedProfileRatio β t r (u - 1) ω * OnePoint.truncatedCorrector β t u v ω) ^ 2
      ∂disorderLaw) =
      (∫ ω, truncatedProfileRatio β t r (u - 1) ω ^ 2 ∂disorderLaw) *
        (∫ ω, OnePoint.truncatedCorrector β t u v ω ^ 2 ∂disorderLaw) := by
  have hX := integrable_sq_truncatedProfileRatio β ht hr (by omega : r ≤ u - 1 + 1)
  have hY := OnePoint.integrable_sq_truncatedCorrector β t ht u v huv
  have hInd := (indepFun_profileRatio_corrector β ht hr hru huv).comp
    (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
    (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
  simp_rw [mul_pow]
  exact hInd.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable

/-- The product square in the moment factorization is genuinely integrable. -/
theorem integrable_sq_profileRatio_corrector (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r u v : ℕ} (hr : 1 ≤ r) (hru : r ≤ u) (huv : u < v) :
    Integrable (fun ω =>
      (truncatedProfileRatio β t r (u - 1) ω * OnePoint.truncatedCorrector β t u v ω) ^ 2) disorderLaw := by
  have hX := integrable_sq_truncatedProfileRatio β ht hr (by omega : r ≤ u - 1 + 1)
  have hY := OnePoint.integrable_sq_truncatedCorrector β t ht u v huv
  have hInd := (indepFun_profileRatio_corrector β ht hr hru huv).comp
    (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
    (by fun_prop : Measurable (fun x : ℝ => x ^ 2))
  have heqfun : (fun ω => (truncatedProfileRatio β t r (u - 1) ω *
      OnePoint.truncatedCorrector β t u v ω) ^ 2) =
      ((fun x : ℝ => x ^ 2) ∘ truncatedProfileRatio β t r (u - 1)) *
        ((fun x : ℝ => x ^ 2) ∘ OnePoint.truncatedCorrector β t u v) := by
    funext ω
    change (truncatedProfileRatio β t r (u - 1) ω * OnePoint.truncatedCorrector β t u v ω) ^ 2 =
      truncatedProfileRatio β t r (u - 1) ω ^ 2 * OnePoint.truncatedCorrector β t u v ω ^ 2
    exact mul_pow _ _ 2
  rw [heqfun]
  exact hInd.integrable_mul hX hY

/-- Truncations of a prefix ratio and a closed activity agree with their
untruncated values on a good event covering both intervals. -/
theorem profile_increment_eq_truncated_of_good (β : ℝ) (t : ℕ → ℕ)
    {r u v j : ℕ} (hru : r ≤ u) (huv : u < v) (hvj : v ≤ j)
    {ω : Disorder} (hω : ω ∈ blockGoodSet β t r j) :
    blockRatio β t r (u - 1) ω *
      (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω) =
      truncatedProfileRatio β t r (u - 1) ω * OnePoint.truncatedCorrector β t u v ω := by
  have hprefix : ω ∈ blockGoodSet β t r (u - 1) := by
    intro k hk
    apply hω k
    have hk' := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩
  have hInv (k : ℕ) (hk : k ∈ Finset.Icc u v) :
      OnePoint.truncatedInverse β t k ω = (blockMass β t k ω)⁻¹ := by
    apply ite_eq_left
    apply hω k
    have hk' := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hru.trans hk'.1, hk'.2.trans hvj⟩
  change _ = (blockGoodSet β t r (u - 1)).indicator (blockRatio β t r (u - 1)) ω * _
  rw [Set.indicator_of_mem hprefix]
  unfold OnePoint.truncatedCorrector
  rw [Finset.prod_congr rfl hInv, Finset.prod_inv_distrib, div_eq_mul_inv]

/-- A local ratio increment has a second moment controlled by the independent
prefix and closed-activity moments, uniformly in any larger good event. -/
theorem integral_sq_profile_increment_le_product (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r u v j : ℕ} (hr : 1 ≤ r) (hru : r ≤ u) (huv : u < v) (hvj : v ≤ j) :
    IntegrableOn (fun ω => (blockRatio β t r (u - 1) ω *
      (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω)) ^ 2)
      (blockGoodSet β t r j) disorderLaw ∧
    (∫ ω in blockGoodSet β t r j, (blockRatio β t r (u - 1) ω *
      (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω)) ^ 2 ∂disorderLaw) ≤
      (∫ ω, truncatedProfileRatio β t r (u - 1) ω ^ 2 ∂disorderLaw) *
        (∫ ω, OnePoint.truncatedCorrector β t u v ω ^ 2 ∂disorderLaw) := by
  have hT := integrable_sq_profileRatio_corrector β ht hr hru huv
  have hEq : (fun ω => (truncatedProfileRatio β t r (u - 1) ω *
      OnePoint.truncatedCorrector β t u v ω) ^ 2) =ᵐ[
        disorderLaw.restrict (blockGoodSet β t r j)]
      (fun ω => (blockRatio β t r (u - 1) ω *
        (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω)) ^ 2) := by
    filter_upwards [self_mem_ae_restrict (OnePoint.measurableSet_blockGoodSet β t r j)] with ω hω
    rw [profile_increment_eq_truncated_of_good β t hru huv hvj hω]
  refine ⟨hT.restrict.congr hEq, ?_⟩
  rw [← integral_congr_ae hEq, ← integral_sq_profileRatio_corrector_eq β ht hr hru huv]
  exact setIntegral_le_integral hT (Filter.Eventually.of_forall fun ω => sq_nonneg _)

/-- The untruncated ratio increment is in `L²` on the larger block-good event. -/
theorem memLp_profile_increment_restrict_good (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r u v j : ℕ} (hr : 1 ≤ r) (hru : r ≤ u) (huv : u < v) (hvj : v ≤ j) :
    MemLp (fun ω => blockRatio β t r (u - 1) ω *
      (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω)) 2
      (disorderLaw.restrict (blockGoodSet β t r j)) := by
  have hX := (measurable_truncatedProfileRatio_block β ht hr (by omega : r ≤ u - 1 + 1)).mono
    (Gaussian.disorderBlock_le _ _) le_rfl
  have hY := (measurable_profileTruncatedCorrector_block β ht huv.le).mono
    (Gaussian.disorderBlock_le _ _) le_rfl
  have hm := (memLp_two_iff_integrable_sq (hX.mul hY).aestronglyMeasurable).mpr
    (integrable_sq_profileRatio_corrector β ht hr hru huv)
  have heq : (fun ω => truncatedProfileRatio β t r (u - 1) ω *
      OnePoint.truncatedCorrector β t u v ω) =ᵐ[disorderLaw.restrict (blockGoodSet β t r j)]
      (fun ω => blockRatio β t r (u - 1) ω *
        (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω)) := by
    filter_upwards [self_mem_ae_restrict (OnePoint.measurableSet_blockGoodSet β t r j)] with ω hω
    exact (profile_increment_eq_truncated_of_good β t hru huv hvj hω).symm
  exact (memLp_congr_ae heq).mp (hm.mono_measure Measure.restrict_le_self)

/-- Convert an honest square-integral bound into the `L²` seminorm bound used
by the finite-sum Minkowski inequality. -/
theorem profile_eLpNorm_two_le_of_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) {B : ℝ} (hB : 0 ≤ B)
    (hb : (∫ ω, X ω ^ 2 ∂P) ≤ B ^ 2) : eLpNorm X 2 P ≤ ENNReal.ofReal B := by
  have heq : eLpNorm X 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, X ω ^ 2 ∂P)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      Real.sqrt_eq_rpow, one_div] using
      (MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hX)
  rw [heq]
  exact ENNReal.ofReal_le_ofReal ((Real.sqrt_le_iff).mpr ⟨hB, hb⟩)

/-- Total second moment of a truncated ratio equals the good-set square integral. -/
theorem integral_sq_truncatedProfileRatio_eq (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) :
    (∫ ω, truncatedProfileRatio β t r s ω ^ 2 ∂disorderLaw) =
      ∫ ω in blockGoodSet β t r s, blockRatio β t r s ω ^ 2 ∂disorderLaw := by
  have heq : (fun ω => truncatedProfileRatio β t r s ω ^ 2) =
      (blockGoodSet β t r s).indicator (fun ω => blockRatio β t r s ω ^ 2) := by
    funext ω
    by_cases hω : ω ∈ blockGoodSet β t r s
    · simp only [truncatedProfileRatio, Set.indicator_of_mem hω]
    · simp only [truncatedProfileRatio, Set.indicator_of_notMem hω, zero_pow two_ne_zero]
  rw [heq, integral_indicator (OnePoint.measurableSet_blockGoodSet β t r s)]

/-- The truncated empty prefix is the constant unit mass. -/
theorem truncatedProfileRatio_empty (β : ℝ) (t : ℕ → ℕ) {r : ℕ} (hr : 1 ≤ r) :
    truncatedProfileRatio β t r (r - 1) = fun _ => 1 := by
  funext ω
  have hg : ω ∈ blockGoodSet β t r (r - 1) := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    omega
  change (blockGoodSet β t r (r - 1)).indicator (blockRatio β t r (r - 1)) ω = 1
  rw [Set.indicator_of_mem hg, blockRatio_empty β t r hr]

/-- Uniform `L²` control of an individual closed-interval contribution. The
constant is independent of the earlier entrance prefix and observation indices. -/
theorem profile_increment_l2_bound (A : ℝ) :
    ∃ C₀ ρ₀ : ℝ, 0 < C₀ ∧ 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      C₀ / Real.sqrt (Real.log ρ) < 1 / 2 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ r u v j : ℕ,
        1 ≤ r → r ≤ u → u < v → v ≤ j → j + 1 ≤ blockCount N ρ →
          eLpNorm (fun ω => blockRatio (criticalBeta ϑ N) (blockTime N ρ) r (u - 1) ω *
            (closedDiscrepancy (criticalBeta ϑ N) (blockTime N ρ) u v ω /
              ∏ k ∈ Finset.Icc u v, blockMass (criticalBeta ϑ N) (blockTime N ρ) k ω)) 2
            (disorderLaw.restrict (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r j)) ≤
            ENNReal.ofReal (C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u) /
              ((blockCount N ρ : ℝ) - j)) := by
  obtain ⟨C₀, ρa, Ca, hC₀, hρa, hCa⟩ := OnePoint.integral_truncatedCorrector_sq_le A
  obtain ⟨ρr, hρr, hRat⟩ := integral_sq_profileBlockRatio_good_le A
  let ρ₀ := max (max ρa ρr) (Real.exp (4 * C₀ ^ 2) + 1)
  have hρ₀ : 1 < ρ₀ := hρa.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨C₀, ρ₀, hC₀, hρ₀, ?_⟩
  intro ρ hρ
  have hρaρ : ρa ≤ ρ := ((le_max_left ρa ρr).trans (le_max_left _ _)).trans hρ
  have hρrρ : ρr ≤ ρ := ((le_max_right ρa ρr).trans (le_max_left _ _)).trans hρ
  have hρ1 : 1 < ρ := hρr.trans_le hρrρ
  have hexp : Real.exp (4 * C₀ ^ 2) < ρ := by
    have h := (le_max_right (max ρa ρr) (Real.exp (4 * C₀ ^ 2) + 1)).trans hρ
    linarith only [h]
  have hlog : 4 * C₀ ^ 2 < Real.log ρ := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexp
  have hsqrt : 2 * C₀ < Real.sqrt (Real.log ρ) := by
    apply (Real.lt_sqrt (by positivity : 0 ≤ 2 * C₀)).mpr
    nlinarith only [hlog]
  have hsqrtpos := Real.sqrt_pos.mpr (Real.log_pos hρ1)
  have hq : C₀ / Real.sqrt (Real.log ρ) < 1 / 2 := by
    apply (div_lt_iff₀ hsqrtpos).mpr
    linarith only [hsqrt]
  refine ⟨hq, ?_⟩
  obtain ⟨Cr, hCr, hCrBound⟩ := hRat ρ
  let C := Real.sqrt (Cr + 1) * |Ca|
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hCrBound ρ ⟨hρrρ, le_rfl⟩, hCa ρ hρaρ, blockTime_monotone hρ1] with N hCrN hCaN ht
  intro ϑ hϑ r u v j hr hru huv hvj hjK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let K := blockCount N ρ
  let D : ℝ := (K : ℝ) - j
  let q := C₀ / Real.sqrt (Real.log ρ)
  have hq0 : 0 < q := div_pos hC₀ hsqrtpos
  have hD1 : 1 ≤ D := by
    have hcast : (j : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hjK
    dsimp only [D]
    linarith only [hcast]
  have hD0 : 0 < D := zero_lt_one.trans_le hD1
  have hpref : (∫ ω, truncatedProfileRatio β t r (u - 1) ω ^ 2 ∂disorderLaw) ≤ Cr + 1 := by
    rcases hru.eq_or_lt with heq | hlt
    · subst u
      have heq : (∫ ω, truncatedProfileRatio β t r (r - 1) ω ^ 2 ∂disorderLaw) = 1 := by
        rw [truncatedProfileRatio_empty β t hr]
        norm_num
      rw [heq]
      linarith only [hCr]
    · rw [integral_sq_truncatedProfileRatio_eq]
      exact ((hCrN ϑ hϑ r (u - 1) hr (by omega) (by omega)).2).trans (by linarith only [hCr])
  have hAct := hCaN ϑ hϑ u v (hr.trans hru) huv (by omega)
  have hDu : D ≤ (K : ℝ) - u := by
    have h : (u : ℝ) ≤ j := by exact_mod_cast (huv.le.trans hvj)
    dsimp only [D]
    linarith only [h]
  have hDv : D ≤ (K : ℝ) - v := by
    have h : (v : ℝ) ≤ j := by exact_mod_cast hvj
    dsimp only [D]
    linarith only [h]
  have hden : D ^ 2 ≤ ((K : ℝ) - u) * ((K : ℝ) - v) := by
    simpa only [pow_two] using mul_le_mul hDu hDv hD0.le (hD0.le.trans hDu)
  have hfrac : (Ca * q ^ (v - u)) ^ 2 / (((K : ℝ) - u) * ((K : ℝ) - v)) ≤
      (Ca * q ^ (v - u)) ^ 2 / D ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hD0) hden
  have hCsq : (C * q ^ (v - u) / D) ^ 2 =
      (Cr + 1) * ((Ca * q ^ (v - u)) ^ 2 / D ^ 2) := by
    dsimp only [C]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by linarith only [hCr]), sq_abs]
    ring
  apply profile_eLpNorm_two_le_of_integral_sq
    (memLp_profile_increment_restrict_good β ht hr hru huv hvj) (by positivity)
  change (∫ ω in blockGoodSet β t r j, (blockRatio β t r (u - 1) ω *
      (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω)) ^ 2 ∂disorderLaw) ≤
    (C * q ^ (v - u) / D) ^ 2
  rw [hCsq]
  calc
    _ ≤ (∫ ω, truncatedProfileRatio β t r (u - 1) ω ^ 2 ∂disorderLaw) *
        (∫ ω, OnePoint.truncatedCorrector β t u v ω ^ 2 ∂disorderLaw) :=
      (integral_sq_profile_increment_le_product β ht hr hru huv hvj).2
    _ ≤ (Cr + 1) * (∫ ω, OnePoint.truncatedCorrector β t u v ω ^ 2 ∂disorderLaw) :=
      mul_le_mul_of_nonneg_right hpref (integral_nonneg fun ω => sq_nonneg _)
    _ ≤ (Cr + 1) * ((Ca * q ^ (v - u)) ^ 2 / (((K : ℝ) - u) * ((K : ℝ) - v))) :=
      mul_le_mul_of_nonneg_left hAct (by linarith only [hCr])
    _ ≤ _ := mul_le_mul_of_nonneg_left hfrac (by linarith only [hCr])

/-- A geometric sum over possible left endpoints is bounded independently of
the length of the preceding prefix. -/
theorem profile_geometric_sum_le_two {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) (r v : ℕ) :
    (∑ u ∈ Finset.Ico r v, q ^ (v - u)) ≤ 2 := by
  have heq := Finset.sum_Ico_reflect (fun k : ℕ => q ^ k) r (m := v) (n := v) (Nat.le_succ v)
  simp only [Nat.add_sub_cancel_left] at heq
  rw [heq]
  have hsub : Finset.Ico 1 (v + 1 - r) ⊆ Finset.range (v + 1) := by
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    exact Finset.mem_range.mpr (by omega)
  calc
    _ ≤ ∑ k ∈ Finset.range (v + 1), q ^ k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => pow_nonneg hq0 k)
    _ ≤ ∑ k ∈ Finset.range (v + 1), (1 / (2 : ℝ)) ^ k :=
      Finset.sum_le_sum fun k _ => pow_le_pow_left₀ hq0 hq k
    _ ≤ 2 := sum_geometric_two_le _

/-- The reverse conversion from a finite `L²` bound to a square-integral bound. -/
theorem profile_integral_sq_le_of_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : MemLp X 2 P) {B : ℝ} (hB : 0 ≤ B)
    (hb : eLpNorm X 2 P ≤ ENNReal.ofReal B) : (∫ ω, X ω ^ 2 ∂P) ≤ B ^ 2 := by
  have heq : eLpNorm X 2 P = ENNReal.ofReal (Real.sqrt (∫ ω, X ω ^ 2 ∂P)) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
      Real.sqrt_eq_rpow, one_div] using
      (MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num) hX)
  rw [heq] at hb
  have hsqrt := (ENNReal.ofReal_le_ofReal_iff hB).mp hb
  rw [← Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg (X ω))]
  exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt 2

/-- The improved ratio-difference bound. Its constant is uniform in the number
of earlier blocks, and the conclusion includes square integrability. -/
theorem integral_sq_blockRatio_sub_le (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ r l j : ℕ,
        1 ≤ r → r ≤ l → l ≤ j → j + 1 ≤ blockCount N ρ →
          MemLp (fun ω => blockRatio (criticalBeta ϑ N) (blockTime N ρ) r j ω -
            blockRatio (criticalBeta ϑ N) (blockTime N ρ) r (l - 1) ω) 2
            (disorderLaw.restrict (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r j)) ∧
          (∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r j,
            (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r j ω -
              blockRatio (criticalBeta ϑ N) (blockTime N ρ) r (l - 1) ω) ^ 2 ∂disorderLaw) ≤
            (C * ((j : ℝ) - l + 1) / ((blockCount N ρ : ℝ) - j)) ^ 2 := by
  obtain ⟨C₀, ρ₀, hC₀, hρ₀, hBound⟩ := profile_increment_l2_bound A
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  obtain ⟨hqhalf, C, hC, hCN⟩ := hBound ρ hρ
  refine ⟨2 * C, mul_nonneg zero_le_two hC, ?_⟩
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  have hq0 : 0 ≤ C₀ / Real.sqrt (Real.log ρ) := div_nonneg hC₀.le (Real.sqrt_nonneg _)
  filter_upwards [hCN, blockTime_monotone hρ1] with N hN ht
  intro ϑ hϑ r l j hr hrl hlj hjK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let μ := disorderLaw.restrict (blockGoodSet β t r j)
  let D : ℝ := (blockCount N ρ : ℝ) - j
  let q := C₀ / Real.sqrt (Real.log ρ)
  let F (v u : ℕ) (ω : Disorder) : ℝ := blockRatio β t r (u - 1) ω *
    (closedDiscrepancy β t u v ω / ∏ k ∈ Finset.Icc u v, blockMass β t k ω)
  have hD : 0 < D := by
    have hcast : (j : ℝ) + 1 ≤ (blockCount N ρ : ℝ) := by exact_mod_cast hjK
    dsimp only [D]
    linarith only [hcast]
  have hlength : 0 ≤ (j : ℝ) - l + 1 := by
    have hcast : (l : ℝ) ≤ j := by exact_mod_cast hlj
    linarith only [hcast]
  have hfun : (fun ω => blockRatio β t r j ω - blockRatio β t r (l - 1) ω) =
      ∑ v ∈ Finset.Icc l j, ∑ u ∈ Finset.Ico r v, F v u := by
    funext ω
    simp only [Finset.sum_apply]
    exact blockRatio_sub_eq_sum_increments β t ht hr hrl hlj ω
  have hm : MemLp (∑ v ∈ Finset.Icc l j, ∑ u ∈ Finset.Ico r v, F v u) 2 μ := by
    apply memLp_finsetSum'
    intro v hv
    apply memLp_finsetSum'
    intro u hu
    have hu' := Finset.mem_Ico.mp hu
    exact memLp_profile_increment_restrict_good β ht hr hu'.1 hu'.2 (Finset.mem_Icc.mp hv).2
  have hnorm : eLpNorm (∑ v ∈ Finset.Icc l j, ∑ u ∈ Finset.Ico r v, F v u) 2 μ ≤
      ENNReal.ofReal (2 * C * ((j : ℝ) - l + 1) / D) := by
    calc
      _ ≤ ∑ v ∈ Finset.Icc l j, eLpNorm (∑ u ∈ Finset.Ico r v, F v u) 2 μ :=
        eLpNorm_sum_le (by norm_num)
      _ ≤ ∑ v ∈ Finset.Icc l j, ∑ u ∈ Finset.Ico r v, ENNReal.ofReal (C * q ^ (v - u) / D) := by
        apply Finset.sum_le_sum
        intro v hv
        apply (eLpNorm_sum_le (by norm_num)).trans
        apply Finset.sum_le_sum
        intro u hu
        have hu' := Finset.mem_Ico.mp hu
        exact hN ϑ hϑ r u v j hr hu'.1 hu'.2 (Finset.mem_Icc.mp hv).2 hjK
      _ ≤ ∑ _v ∈ Finset.Icc l j, ENNReal.ofReal (2 * C / D) := by
        apply Finset.sum_le_sum
        intro v _
        rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => by positivity)]
        apply ENNReal.ofReal_le_ofReal
        calc
          (∑ u ∈ Finset.Ico r v, C * q ^ (v - u) / D) =
              C / D * ∑ u ∈ Finset.Ico r v, q ^ (v - u) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
          _ ≤ C / D * 2 := mul_le_mul_of_nonneg_left (profile_geometric_sum_le_two hq0 hqhalf.le r v) (by positivity)
          _ = _ := by ring
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.sum_const,
          nsmul_eq_mul, Nat.card_Icc, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
        congr 1
        ring
  rw [← hfun] at hm hnorm
  refine ⟨hm, ?_⟩
  exact profile_integral_sq_le_of_eLpNorm_two hm (by positivity) hnorm


/-- A pointwise bound for the corrected profile on its profile-good event. -/
theorem profile_residual_sqrt_energy_le (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (N r s : ℕ) (hr : 1 ≤ r) (hrs : r ≤ s) {ω : Disorder}
    (hω : ω ∈ profileGoodSet β t r s) :
    Real.sqrt (futureEnergy β (t s) N (fun y =>
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
        commonCorrection β t r s ω y)) ≤
      2 * ∑ u ∈ Finset.Icc r s, |blockRatio β t r (u - 1) ω - blockRatio β t r s ω| *
        Real.sqrt (futureEnergy β (t s) N (openCorrector β t u s ω)) := by
  classical
  let I := Finset.Icc r s
  let A := I.biUnion (fun u => openCorrectorNumeratorSupport t u s)
  let η (u : ℕ) := (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) •
    openCorrector β t u s ω
  have hsupp (u : ℕ) (hu : u ∈ I) (y : Site) (hy : y ∉ A) :
      openCorrector β t u s ω y = 0 := by
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro h
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, h⟩)
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu, zero_div]
  have hηsupp : ∀ u ∈ I, ∀ y ∉ A, η u y = 0 := by
    intro u hu y hy
    change _ * openCorrector β t u s ω y = 0
    rw [hsupp u hu y hy, mul_zero]
  have hsumSupp : ∀ y ∉ A, (∑ u ∈ I, η u) y = 0 := by
    intro y hy
    simp only [Finset.sum_apply]
    exact Finset.sum_eq_zero (fun u hu => hηsupp u hu y hy)
  have hid : (fun y => smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y -
      srwKernel (t s) y - commonCorrection β t r s ω y) =
      (blockRatio β t r s ω)⁻¹ • ∑ u ∈ I, η u := by
    funext y
    simpa only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, η, I] using
      profile_expansion_identity β t ht r s hr hrs ω y
  rw [hid, futureEnergy_smul β (t s) N _ _ A hsumSupp,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (inv_pos.mpr (profile_blockRatio_pos β t r s ω))]
  calc
    _ ≤ 2 * Real.sqrt (futureEnergy β (t s) N (∑ u ∈ I, η u)) :=
      mul_le_mul_of_nonneg_right (inv_blockRatio_le_two_of_mem_profileGoodSet β t r s hω)
        (Real.sqrt_nonneg _)
    _ ≤ 2 * ∑ u ∈ I, Real.sqrt (futureEnergy β (t s) N (η u)) :=
      mul_le_mul_of_nonneg_left (sqrt_futureEnergy_finset_sum_le β (t s) N A I η hηsupp)
        (by norm_num)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      dsimp only [η]
      rw [futureEnergy_smul β (t s) N _ _ A (hsupp u hu),
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The corrected profile has measurable future energy. -/
theorem measurable_profile_residual_futureEnergy (β : ℝ) {t : ℕ → ℕ}
    (ht : Monotone t) {N r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hts : t s ≤ N) :
    Measurable (fun ω => futureEnergy β (t s) N (fun y =>
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
        commonCorrection β t r s ω y)) := by
  classical
  let I := Finset.Icc r s
  let A := I.biUnion (fun u => openCorrectorNumeratorSupport t u s)
  let Q (ω : Disorder) (y : Site) := (blockRatio β t r s ω)⁻¹ * ∑ u ∈ I,
    (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) * openCorrector β t u s ω y
  have hR (v : ℕ) (hv : r ≤ v + 1) : Measurable (blockRatio β t r v) := by
    by_cases hrv : r ≤ v
    · exact (measurable_blockRatio_on_block β t ht r v hrv).mono
        (Gaussian.disorderBlock_le _ _) le_rfl
    · have hv' : v = r - 1 := by omega
      subst v
      have heq : blockRatio β t r (r - 1) = fun _ => 1 := by
        funext ω
        exact blockRatio_empty β t r hr ω
      rw [heq]
      exact measurable_const
  have hcoord (y : Site) : Measurable (fun ω => Q ω y) := by
    apply (hR s (by omega)).inv.mul
    apply Finset.measurable_sum
    intro u hu
    have hu' := Finset.mem_Icc.mp hu
    exact ((hR (u - 1) (by omega)).sub (hR s (by omega))).mul
      ((measurable_openCorrector_on_block β t ht u s (by omega) hu'.2 y).mono
        (Gaussian.disorderBlock_le _ _) le_rfl)
  have hsupp (ω : Disorder) (y : Site) (hy : y ∉ A) : Q ω y = 0 := by
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro u hu
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro h
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, h⟩)
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu,
      zero_div, mul_zero]
  have henergy : (fun ω => futureEnergy β (t s) N (Q ω)) = fun ω =>
      ∑ x ∈ A, ∑ y ∈ A, Q ω x * Q ω y * Polymer.pairMoment β (N - t s) x y := by
    funext ω
    exact futureEnergy_eq_pairMoment_sum β hts _ A (hsupp ω)
  have heq : (fun ω => futureEnergy β (t s) N (fun y =>
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
        commonCorrection β t r s ω y)) = fun ω => futureEnergy β (t s) N (Q ω) := by
    funext ω
    congr 1
    funext y
    exact profile_expansion_identity β t ht r s hr hrs ω y
  rw [heq, henergy]
  exact Finset.measurable_sum _ fun x _ => Finset.measurable_sum _ fun y _ =>
    ((hcoord x).mul (hcoord y)).mul measurable_const

/-- Integrating the corrected expansion costs only the product of the two
second-moment norms for each open activity. -/
theorem profile_residual_integral_le_sum (β : ℝ) {t : ℕ → ℕ}
    (ht : Monotone t) {N r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) (hts : t s ≤ N)
    (hδ : ∀ u ∈ Finset.Icc r s, IntegrableOn
      (fun ω => (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) ^ 2)
        (blockGoodSet β t r s) disorderLaw) :
    IntegrableOn (fun ω => Real.sqrt (futureEnergy β (t s) N (fun y =>
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
        commonCorrection β t r s ω y))) (profileGoodSet β t r s) disorderLaw ∧
    (∫ ω in profileGoodSet β t r s,
      Real.sqrt (futureEnergy β (t s) N (fun y =>
        smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
          commonCorrection β t r s ω y)) ∂disorderLaw) ≤
      2 * ∑ u ∈ Finset.Icc r s,
        Real.sqrt (∫ ω in blockGoodSet β t r s,
          (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) ^ 2 ∂disorderLaw) *
        Real.sqrt (∫ ω in blockGoodSet β t u s,
          futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw) := by
  classical
  let G := profileGoodSet β t r s
  let F (u : ℕ) (ω : Disorder) :=
    |blockRatio β t r (u - 1) ω - blockRatio β t r s ω| *
      Real.sqrt (futureEnergy β (t s) N (openCorrector β t u s ω))
  have hsub : G ⊆ blockGoodSet β t r s := fun _ h => h.1
  have hsubu (u : ℕ) (hu : u ∈ Finset.Icc r s) :
      G ⊆ blockGoodSet β t u s := by
    intro ω hω k hk
    apply hω.1 k
    have hu' := Finset.mem_Icc.mp hu
    have hk' := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, hk'.2⟩
  have hR (v : ℕ) (hv : r ≤ v + 1) : Measurable (blockRatio β t r v) := by
    by_cases hrv : r ≤ v
    · exact (measurable_blockRatio_on_block β t ht r v hrv).mono
        (Gaussian.disorderBlock_le _ _) le_rfl
    · have hv' : v = r - 1 := by omega
      subst v
      have heq : blockRatio β t r (r - 1) = fun _ => 1 := by
        funext ω
        exact blockRatio_empty β t r hr ω
      rw [heq]
      exact measurable_const
  have hterm (u : ℕ) (hu : u ∈ Finset.Icc r s) :
      IntegrableOn (F u) G disorderLaw ∧
      (∫ ω in G, F u ω ∂disorderLaw) ≤
        Real.sqrt (∫ ω in blockGoodSet β t r s,
          (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) ^ 2 ∂disorderLaw) *
        Real.sqrt (∫ ω in blockGoodSet β t u s,
          futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw) := by
    have hu' := Finset.mem_Icc.mp hu
    have hE := (measurable_futureEnergy_openCorrector_on_block β ht
      (by omega : 1 ≤ u) hu'.2 hts).mono (Gaussian.disorderBlock_le _ _) le_rfl
    have hEi := integrableOn_futureEnergy_openCorrector β t N u s ht (by omega) hu'.2 hts
    have hsquare : (fun ω => Real.sqrt (futureEnergy β (t s) N
        (openCorrector β t u s ω)) ^ 2) = fun ω =>
          futureEnergy β (t s) N (openCorrector β t u s ω) := by
      funext ω
      exact Real.sq_sqrt (futureEnergy_nonneg _ _ _ _)
    have hcs := setIntegral_mul_le_sqrt_sq
      (fun ω => |blockRatio β t r (u - 1) ω - blockRatio β t r s ω|)
      (fun ω => Real.sqrt (futureEnergy β (t s) N (openCorrector β t u s ω))) G
      ((hR (u - 1) (by omega)).sub (hR s (by omega))).abs hE.sqrt
      (fun _ => abs_nonneg _) (fun _ => Real.sqrt_nonneg _)
      (by simpa only [sq_abs] using (hδ u hu).mono_set hsub)
      (hsquare.symm ▸ hEi.mono_set (hsubu u hu))
    refine ⟨hcs.1, hcs.2.trans ?_⟩
    simp only [sq_abs, hsquare]
    apply mul_le_mul
    · apply Real.sqrt_le_sqrt
      exact setIntegral_mono_set (hδ u hu) (Eventually.of_forall fun _ => sq_nonneg _)
        (Eventually.of_forall hsub)
    · apply Real.sqrt_le_sqrt
      exact setIntegral_mono_set hEi
        (Eventually.of_forall fun _ => futureEnergy_nonneg _ _ _ _)
        (Eventually.of_forall (hsubu u hu))
    · exact Real.sqrt_nonneg _
    · exact Real.sqrt_nonneg _
  have hsum : IntegrableOn (fun ω => 2 * ∑ u ∈ Finset.Icc r s, F u ω) G disorderLaw :=
    (integrable_finsetSum _ (fun u hu => (hterm u hu).1)).const_mul 2
  have hbound := fun ω (hω : ω ∈ G) => profile_residual_sqrt_energy_le β t ht N r s hr hrs hω
  have hG : MeasurableSet G :=
    (show disorderPast (t s) ≤ (inferInstance : MeasurableSpace Disorder) from by
      rw [← Gaussian.disorderBlock_zero (t s)]
      exact Gaussian.disorderBlock_le _ _) G
      (LogNormality.measurableSet_profileGoodSet_past β ht hr hrs)
  have hpoint := (ae_restrict_mem (μ := disorderLaw) hG).mono hbound
  have hmeas := (measurable_profile_residual_futureEnergy β ht hr hrs hts).sqrt
  have hint := hsum.mono' hmeas.aestronglyMeasurable.restrict (hpoint.mono fun ω h => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h)
  refine ⟨hint, (integral_mono_ae hint hsum hpoint).trans ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun u hu => (hterm u hu).1)]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u hu => (hterm u hu).2) (by norm_num)

/-- The weighted geometric series produced by the residual expansion is
bounded independently of the entrance index. -/
theorem profile_weighted_geometric_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (r s : ℕ) :
    (∑ u ∈ Finset.Icc r s, ((s : ℝ) - u + 1) * q ^ (s - u)) ≤
      1 / (1 - q) ^ 2 := by
  have hnorm : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hseries := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_norm_lt_one hnorm)
  have hseries' : HasSum (fun k : ℕ => ((k : ℝ) + 1) * q ^ k)
      (1 / (1 - q) ^ 2) := by
    convert hseries using 1
    · funext k
      ring
    · field_simp [ne_of_gt (sub_pos.mpr hq1)]
      ring
  have hreflect : (∑ u ∈ Finset.Icc r s, ((s : ℝ) - u + 1) * q ^ (s - u)) =
      ∑ k ∈ Finset.Ico 0 (s + 1 - r), ((k : ℝ) + 1) * q ^ k := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    calc
      _ = ∑ u ∈ Finset.Ico r (s + 1), (((s - u : ℕ) : ℝ) + 1) * q ^ (s - u) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Nat.cast_sub (by have := Finset.mem_Ico.mp hu; omega)]
      _ = _ := by
        simpa only [Nat.sub_self] using
          (Finset.sum_Ico_reflect (fun k => ((k : ℝ) + 1) * q ^ k)
            r (m := s + 1) (n := s) le_rfl)
  rw [hreflect]
  exact hseries'.summable.sum_le_tsum _ (fun k _ => by positivity) |>.trans_eq hseries'.tsum_eq

/-- Numerical summation of the improved ratio bound and the open-corrector
energy bound. These are the two moment estimates used by the residual. -/
theorem profile_residual_integral_bound_of (β : ℝ) {t : ℕ → ℕ}
    (ht : Monotone t) {N r s K : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s)
    (hsK : s < K) (hts : t s ≤ N) {Cr Co q : ℝ}
    (hCr : 0 ≤ Cr) (hCo : 0 ≤ Co) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hδ : ∀ u ∈ Finset.Icc r s,
      IntegrableOn (fun ω => (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) ^ 2)
        (blockGoodSet β t r s) disorderLaw ∧
      (∫ ω in blockGoodSet β t r s,
        (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) ^ 2 ∂disorderLaw) ≤
        (Cr * ((s : ℝ) - u + 1) / ((K : ℝ) - s)) ^ 2)
    (hOpen : ∀ u ∈ Finset.Icc r s,
      (∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw) ≤
          Co * q ^ (2 * (s - u)) / ((K : ℝ) - u)) :
    IntegrableOn (fun ω => Real.sqrt (futureEnergy β (t s) N (fun y =>
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
        commonCorrection β t r s ω y))) (profileGoodSet β t r s) disorderLaw ∧
    (∫ ω in profileGoodSet β t r s,
      Real.sqrt (futureEnergy β (t s) N (fun y =>
        smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
          commonCorrection β t r s ω y)) ∂disorderLaw) ≤
      (2 * Cr * Real.sqrt Co / (1 - q) ^ 2) /
        (((K : ℝ) - s) * Real.sqrt ((K : ℝ) - s)) := by
  let D : ℝ := (K : ℝ) - s
  have hD : 0 < D := sub_pos.mpr (by exact_mod_cast hsK)
  have hrootD : 0 < Real.sqrt D := Real.sqrt_pos.mpr hD
  have hbase := profile_residual_integral_le_sum β ht hr hrs hts (fun u hu => (hδ u hu).1)
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  have hterm (u : ℕ) (hu : u ∈ Finset.Icc r s) :
      Real.sqrt (∫ ω in blockGoodSet β t r s,
        (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) ^ 2 ∂disorderLaw) *
      Real.sqrt (∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw) ≤
        (Cr * Real.sqrt Co / (D * Real.sqrt D)) *
          (((s : ℝ) - u + 1) * q ^ (s - u)) := by
    have hu' := Finset.mem_Icc.mp hu
    have hcast : (u : ℝ) ≤ s := by exact_mod_cast hu'.2
    have hlength : 0 ≤ (s : ℝ) - u + 1 := by linarith
    have hfirst : Real.sqrt (∫ ω in blockGoodSet β t r s,
        (blockRatio β t r (u - 1) ω - blockRatio β t r s ω) ^ 2 ∂disorderLaw) ≤
        Cr * ((s : ℝ) - u + 1) / D := by
      apply (Real.sqrt_le_sqrt (hδ u hu).2).trans_eq
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have hsecond : Real.sqrt (∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw) ≤
        Real.sqrt Co * q ^ (s - u) / Real.sqrt D := by
      have hden : 0 < (K : ℝ) - u := by dsimp only [D] at hD; linarith
      have hbound : Co * q ^ (2 * (s - u)) / ((K : ℝ) - u) ≤
          Co * q ^ (2 * (s - u)) / D :=
        div_le_div_of_nonneg_left (by positivity) hD (by dsimp only [D]; linarith)
      apply (Real.sqrt_le_sqrt ((hOpen u hu).trans hbound)).trans_eq
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul hCo,
        show q ^ (2 * (s - u)) = (q ^ (s - u)) ^ 2 by rw [← pow_mul]; congr 1; omega,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hq0 _)]
    calc
      _ ≤ (Cr * ((s : ℝ) - u + 1) / D) *
          (Real.sqrt Co * q ^ (s - u) / Real.sqrt D) :=
        mul_le_mul hfirst hsecond (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  calc
    _ ≤ 2 * ∑ u ∈ Finset.Icc r s,
        (Cr * Real.sqrt Co / (D * Real.sqrt D)) * (((s : ℝ) - u + 1) * q ^ (s - u)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
    _ = 2 * (Cr * Real.sqrt Co / (D * Real.sqrt D)) *
        ∑ u ∈ Finset.Icc r s, (((s : ℝ) - u + 1) * q ^ (s - u)) := by
      rw [← Finset.mul_sum, mul_assoc]
    _ ≤ 2 * (Cr * Real.sqrt Co / (D * Real.sqrt D)) * (1 / (1 - q) ^ 2) :=
      mul_le_mul_of_nonneg_left (profile_weighted_geometric_sum_le hq0 hq1 r s) (by positivity)
    _ = _ := by ring

/-- The improved expected residual seminorm, uniformly over every earlier
entrance. Both moment inputs are supplied by proved lattice estimates. -/
theorem profile_residual_integral_bound (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ,
        1 ≤ r → r ≤ s → s + 2 ≤ blockCount N ρ →
          IntegrableOn (fun ω => Real.sqrt (futureEnergy (criticalBeta ϑ N)
            (blockTime N ρ s) N (fun y =>
              smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (r - 1))
                (blockTime N ρ s) 0 ω y - srwKernel (blockTime N ρ s) y -
              commonCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω y)))
            (profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s) disorderLaw ∧
          (∫ ω in profileGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
            Real.sqrt (futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N (fun y =>
              smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (r - 1))
                (blockTime N ρ s) 0 ω y - srwKernel (blockTime N ρ s) y -
              commonCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω y)) ∂disorderLaw) ≤
            C / (((blockCount N ρ : ℝ) - s) * Real.sqrt ((blockCount N ρ : ℝ) - s)) := by
  obtain ⟨ρr, hρr, hRatio⟩ := integral_sq_blockRatio_sub_le A
  obtain ⟨ρo, q, hρo, hq0, hqHalf, hOpen⟩ := profile_openCorrector_energy_bound A
  have hq1 : q < 1 := hqHalf.trans (by norm_num)
  refine ⟨max ρr ρo, hρr.trans_le (le_max_left _ _), ?_⟩
  intro ρ hρ
  have hρ1 : 1 < ρ := hρr.trans_le ((le_max_left _ _).trans hρ)
  obtain ⟨Cr, hCr, hCrN⟩ := hRatio ρ ((le_max_left _ _).trans hρ)
  obtain ⟨Co, hCo⟩ := hOpen ρ
  have hCoN := hCo ρ ⟨(le_max_right _ _).trans hρ, le_rfl⟩
  refine ⟨2 * Cr * Real.sqrt |Co| / (1 - q) ^ 2, by positivity, ?_⟩
  filter_upwards [hCrN, hCoN, blockTime_monotone hρ1] with N hR hO ht
  intro ϑ hϑ r s hr hrs hsK
  have hterminal : blockTime N ρ (blockCount N ρ) = N := by
    simp [blockTime, ne_of_gt (by omega : 0 < blockCount N ρ)]
  have hts : blockTime N ρ s ≤ N := (ht (by omega : s ≤ blockCount N ρ)).trans_eq hterminal
  apply profile_residual_integral_bound_of (criticalBeta ϑ N) ht hr hrs
    (by omega : s < blockCount N ρ) hts hCr (abs_nonneg Co) hq0.le hq1
  · intro u hu
    have hu' := Finset.mem_Icc.mp hu
    obtain ⟨hm, hb⟩ := hR ϑ hϑ r u s hr hu'.1 hu'.2 (by omega)
    have heq : (fun ω => (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r (u - 1) ω -
        blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω) ^ 2) =
        fun ω => (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω -
          blockRatio (criticalBeta ϑ N) (blockTime N ρ) r (u - 1) ω) ^ 2 := by
      funext ω
      ring
    rw [heq]
    exact ⟨hm.integrable_sq, hb⟩
  · intro u hu
    have hu' := Finset.mem_Icc.mp hu
    exact (hO ϑ hϑ u s (by omega) hu'.2 hsK).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self Co) (pow_nonneg hq0.le _))
        (by have hcast : (s : ℝ) < blockCount N ρ := by exact_mod_cast (show s < blockCount N ρ by omega)
            have hucast : (u : ℝ) ≤ s := by exact_mod_cast hu'.2
            linarith))

/-- The common correction cancels after the later entrance, for arbitrary
earlier entrance indices. -/
theorem profile_commonCorrection_sub_eq (β : ℝ) (t : ℕ → ℕ)
    {r m s : ℕ} (hrm : r ≤ m) (hms : m ≤ s) (ω : Disorder) (y : Site) :
    commonCorrection β t r s ω y - commonCorrection β t m s ω y =
      ∑ u ∈ Finset.Ico r m, openCorrector β t u s ω y := by
  have hpartition : Finset.Icc r s = Finset.Ico r m ∪ Finset.Icc m s := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_Ico, Finset.mem_union]
    omega
  have hdisjoint : Disjoint (Finset.Ico r m) (Finset.Icc m s) := by
    apply Finset.disjoint_left.mpr
    intro u hu hv
    have := Finset.mem_Ico.mp hu
    have := Finset.mem_Icc.mp hv
    omega
  unfold commonCorrection
  rw [hpartition, Finset.sum_union hdisjoint]
  ring

/-- A triangle inequality with the sign of the second profile removed. -/
theorem profile_sqrt_energy_sub_le (β : ℝ) (a b : ℕ) (η ξ : Site → ℝ)
    (A : Finset Site) (hη : ∀ y ∉ A, η y = 0) (hξ : ∀ y ∉ A, ξ y = 0) :
    Real.sqrt (futureEnergy β a b (η - ξ)) ≤
      Real.sqrt (futureEnergy β a b η) + Real.sqrt (futureEnergy β a b ξ) := by
  have hn : ∀ y ∉ A, (-ξ) y = 0 := by intro y hy; simp [hξ y hy]
  have heq : futureEnergy β a b (-ξ) = futureEnergy β a b ξ := by
    simpa using futureEnergy_smul β a b (-1) ξ A hξ
  simpa only [sub_eq_add_neg, heq] using sqrt_futureEnergy_add_le β a b η (-ξ) A hη hn

/-- Pointwise cancellation of the common correction in the comparison of
two entrance profiles. -/
theorem profile_two_profiles_sqrt_energy_le (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (N r m s : ℕ) (hr : 1 ≤ r) (hrm : r ≤ m) (hms : m ≤ s) (ω : Disorder) :
    Real.sqrt (futureEnergy β (t s) N (fun y =>
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y -
        smoothedEndpointDist β (t (m - 1)) (t s) 0 ω y)) ≤
      Real.sqrt (futureEnergy β (t s) N (fun y =>
        smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
          commonCorrection β t r s ω y)) +
      Real.sqrt (futureEnergy β (t s) N (fun y =>
        smoothedEndpointDist β (t (m - 1)) (t s) 0 ω y - srwKernel (t s) y -
          commonCorrection β t m s ω y)) +
      ∑ u ∈ Finset.Ico r m, Real.sqrt (futureEnergy β (t s) N (openCorrector β t u s ω)) := by
  classical
  let A := (Finset.Icc r s).biUnion (fun u => openCorrectorNumeratorSupport t u s)
  let R (v : ℕ) (y : Site) := smoothedEndpointDist β (t (v - 1)) (t s) 0 ω y -
    srwKernel (t s) y - commonCorrection β t v s ω y
  let O : Site → ℝ := ∑ u ∈ Finset.Ico r m, openCorrector β t u s ω
  have hopen (u : ℕ) (hu : u ∈ Finset.Icc r s) (y : Site) (hy : y ∉ A) :
      openCorrector β t u s ω y = 0 := by
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y (by
      intro h; exact hy (Finset.mem_biUnion.mpr ⟨u, hu, h⟩)), zero_div]
  have hR (v : ℕ) (hv : v ∈ Finset.Icc r m) (y : Site) (hy : y ∉ A) : R v y = 0 := by
    have hv' := Finset.mem_Icc.mp hv
    dsimp only [R]
    rw [profile_expansion_identity β t ht v s (by omega) (by omega) ω y]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := Finset.mem_Icc.mp hu
    rw [hopen u (Finset.mem_Icc.mpr ⟨by omega, hu'.2⟩) y hy, mul_zero]
  have hO (y : Site) (hy : y ∉ A) : O y = 0 := by
    simp only [O, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro u hu
    have hu' := Finset.mem_Ico.mp hu
    exact hopen u (Finset.mem_Icc.mpr ⟨hu'.1, by omega⟩) y hy
  have hdecomp : (fun y => smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y -
      smoothedEndpointDist β (t (m - 1)) (t s) 0 ω y) = R r - R m + O := by
    funext y
    have hc := profile_commonCorrection_sub_eq β t hrm hms ω y
    simp only [R, O, Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
    linarith only [hc]
  rw [hdecomp]
  calc
    _ ≤ Real.sqrt (futureEnergy β (t s) N (R r - R m)) + Real.sqrt (futureEnergy β (t s) N O) :=
      sqrt_futureEnergy_add_le β (t s) N _ _ A
        (fun y hy => by simp only [Pi.sub_apply, hR r (by simp [hrm]) y hy, hR m (by simp [hrm]) y hy, sub_self]) hO
    _ ≤ (Real.sqrt (futureEnergy β (t s) N (R r)) +
        Real.sqrt (futureEnergy β (t s) N (R m))) + Real.sqrt (futureEnergy β (t s) N O) :=
      add_le_add (profile_sqrt_energy_sub_le β (t s) N _ _ A
        (hR r (by simp [hrm])) (hR m (by simp [hrm]))) le_rfl
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply sqrt_futureEnergy_finset_sum_le β (t s) N A (Finset.Ico r m)
      intro u hu y hy
      have hu' := Finset.mem_Ico.mp hu
      exact hopen u (Finset.mem_Icc.mpr ⟨hu'.1, by omega⟩) y hy

/-- The future seminorm of the difference of two heat-started endpoint laws
is integrable for arbitrary entrance times. -/
theorem integrable_sqrt_energy_sub_smoothedEndpointDist (β : ℝ) {a b n N : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (hn : n ≤ N) :
    Integrable (fun ω => Real.sqrt (futureEnergy β n N (fun y =>
      smoothedEndpointDist β a n 0 ω y - smoothedEndpointDist β b n 0 ω y))) disorderLaw := by
  classical
  let S (m : ℕ) := (Polymer.endpoints 0 m).biUnion (fun y => Polymer.endpoints y (n - m))
  have hsupp (m : ℕ) (ω : Disorder) (y : Site) (hy : y ∉ S m) :
      smoothedEndpointDist β m n 0 ω y = 0 :=
    Smoothing.smoothedEndpointDist_eq_zero_of_not_mem β 0 y ω hy
  have hbound (m : ℕ) (hm : m ≤ n) (ω : Disorder) (y : Site) :
      |smoothedEndpointDist β m n 0 ω y| ≤ 1 := by
    have hdata := Smoothing.smoothedEndpointDist_probability β hm 0 ω
    by_cases hy : y ∈ S m
    · rw [abs_of_nonneg (hdata.2.1 y)]
      exact (Finset.single_le_sum (fun z _ => hdata.2.1 z) hy).trans_eq hdata.2.2
    · rw [hsupp m ω y hy]
      norm_num
  apply integrable_sqrt_futureEnergy β hn _ (S a ∪ S b)
  · intro ω y hy
    have hya : y ∉ S a := fun h => hy (Finset.mem_union_left _ h)
    have hyb : y ∉ S b := fun h => hy (Finset.mem_union_right _ h)
    rw [hsupp a ω y hya, hsupp b ω y hyb, sub_self]
  · refine ⟨2, fun ω y => ?_⟩
    exact (abs_sub _ _).trans (by linarith only [hbound a ha ω y, hbound b hb ω y])
  · intro y
    rw [← Gaussian.disorderBlock_zero n]
    exact ((Polymer.measurable_smoothedEndpointDist_block β a n ha 0 y).mono
      (Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl) le_rfl).sub
      ((Polymer.measurable_smoothedEndpointDist_block β b n hb 0 y).mono
        (Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl) le_rfl)

/-- Jensen transfers an open-corrector energy estimate to its expected
seminorm on any smaller good event. -/
theorem profile_openCorrector_integral_sqrt_le (β : ℝ) {t : ℕ → ℕ}
    (ht : Monotone t) {N u s : ℕ} (hu : 1 ≤ u) (hus : u ≤ s) (hts : t s ≤ N)
    (G : Set Disorder) (hG : G ⊆ blockGoodSet β t u s) {Co q D : ℝ}
    (hCo : 0 ≤ Co) (hq : 0 ≤ q)
    (hE : (∫ ω in blockGoodSet β t u s,
      futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw) ≤
        Co * q ^ (2 * (s - u)) / D) :
    IntegrableOn (fun ω => Real.sqrt (futureEnergy β (t s) N (openCorrector β t u s ω)))
      G disorderLaw ∧
    (∫ ω in G, Real.sqrt (futureEnergy β (t s) N (openCorrector β t u s ω)) ∂disorderLaw) ≤
      Real.sqrt Co * q ^ (s - u) / Real.sqrt D := by
  have hi := integrableOn_futureEnergy_openCorrector β t N u s ht hu hus hts
  have hm := (measurable_futureEnergy_openCorrector_on_block β ht hu hus hts).mono
    (Gaussian.disorderBlock_le _ _) le_rfl
  have hj := setIntegral_sqrt_le_sqrt _ G hm
    (fun _ => futureEnergy_nonneg _ _ _ _) (hi.mono_set hG)
  refine ⟨hj.1, hj.2.trans ?_⟩
  have hbound := (setIntegral_mono_set hi
    (Eventually.of_forall fun _ => futureEnergy_nonneg _ _ _ _)
    (Eventually.of_forall hG)).trans hE
  apply (Real.sqrt_le_sqrt hbound).trans_eq
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul hCo,
    show q ^ (2 * (s - u)) = (q ^ (s - u)) ^ 2 by rw [← pow_mul]; congr 1; omega,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (pow_nonneg hq _)]

/-- The uncancelled corrections start at the full padding distance from the
observation block. -/
theorem profile_prefix_geometric_sum_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    {r m s : ℕ} (hrm : r ≤ m) (hms : m ≤ s) :
    (∑ u ∈ Finset.Ico r m, q ^ (s - u)) ≤ q ^ (s - m + 1) / (1 - q) := by
  by_cases hm : m = 0
  · subst m
    simp
    positivity
  have hsum : (∑ u ∈ Finset.Ico r m, q ^ (s - u)) =
      q ^ (s - m + 1) * ∑ u ∈ Finset.Icc r (m - 1), q ^ (m - 1 - u) := by
    rw [Finset.mul_sum]
    have hsets : Finset.Ico r m = Finset.Icc r (m - 1) := by
      ext u
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hsets]
    apply Finset.sum_congr rfl
    intro u hu
    have hu' := Finset.mem_Icc.mp hu
    rw [← pow_add, show s - m + 1 + (m - 1 - u) = s - u by omega]
  rw [hsum, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [one_div] using
      sum_Icc_pow_reverse_le_inv_one_sub_of_le hq0 hq1 (r := r) (s := m - 1))
    (pow_nonneg hq0 _)

/-- The improved two-profile expected seminorm bound. The first term is
uniform in both entrances; the second decays with the later entrance's padding. -/
theorem profile_two_profiles_integral_bound (A : ℝ) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧
      ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ Cr Co : ℝ, 0 ≤ Cr ∧ 0 ≤ Co ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ r m s : ℕ,
        1 ≤ r → r ≤ m → m ≤ s → s + 2 ≤ blockCount N ρ →
          (∫ ω in profileComparisonGoodSet (criticalBeta ϑ N) (blockTime N ρ) r m s,
            Real.sqrt (futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N (fun y =>
              smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (r - 1))
                (blockTime N ρ s) 0 ω y -
              smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (m - 1))
                (blockTime N ρ s) 0 ω y)) ∂disorderLaw) ≤
            Cr / (((blockCount N ρ : ℝ) - s) * Real.sqrt ((blockCount N ρ : ℝ) - s)) +
              Co * q ^ (s - m + 1) / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨ρr, hρr, hResidual⟩ := profile_residual_integral_bound A
  obtain ⟨ρo, q, hρo, hq0, hqHalf, hOpen⟩ := profile_openCorrector_energy_bound A
  have hq1 : q < 1 := hqHalf.trans (by norm_num)
  refine ⟨max ρr ρo, q, hρr.trans_le (le_max_left _ _), hq0, hqHalf, ?_⟩
  intro ρ hρ
  have hρ1 : 1 < ρ := hρr.trans_le ((le_max_left _ _).trans hρ)
  obtain ⟨Cr, hCr, hCrN⟩ := hResidual ρ ((le_max_left _ _).trans hρ)
  obtain ⟨Co, hCo⟩ := hOpen ρ
  refine ⟨2 * Cr, Real.sqrt |Co| / (1 - q), by positivity, by positivity, ?_⟩
  filter_upwards [hCrN, hCo ρ ⟨(le_max_right _ _).trans hρ, le_rfl⟩,
    blockTime_monotone hρ1] with N hR hO ht
  intro ϑ hϑ r m s hr hrm hms hsK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let G := profileComparisonGoodSet β t r m s
  let D : ℝ := (blockCount N ρ : ℝ) - s
  let R (v : ℕ) (ω : Disorder) := Real.sqrt (futureEnergy β (t s) N (fun y =>
    smoothedEndpointDist β (t (v - 1)) (t s) 0 ω y - srwKernel (t s) y -
      commonCorrection β t v s ω y))
  let O (u : ℕ) (ω : Disorder) := Real.sqrt (futureEnergy β (t s) N (openCorrector β t u s ω))
  have hD : 0 < D := sub_pos.mpr (by exact_mod_cast (show s < blockCount N ρ by omega))
  have hterminal : t (blockCount N ρ) = N := by
    simp [t, blockTime, ne_of_gt (by omega : 0 < blockCount N ρ)]
  have hts : t s ≤ N := (ht (by omega : s ≤ blockCount N ρ)).trans_eq hterminal
  have hres (v : ℕ) (hv : v = r ∨ v = m) :
      IntegrableOn (R v) G disorderLaw ∧ (∫ ω in G, R v ω ∂disorderLaw) ≤ Cr / (D * Real.sqrt D) := by
    have hv' : v ∈ Finset.Icc r m := by rcases hv with rfl | rfl <;> simp [hrm]
    have hrv := hR ϑ hϑ v s (by omega) (by omega) hsK
    have hsub : G ⊆ profileGoodSet β t v s := by
      rcases hv with rfl | rfl
      ·
        exact fun _ h => h.1
      · exact fun _ h => h.2
    exact ⟨hrv.1.mono_set hsub, (setIntegral_mono_set hrv.1
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
      (Eventually.of_forall hsub)).trans hrv.2⟩
  have hopen (u : ℕ) (hu : u ∈ Finset.Ico r m) :
      IntegrableOn (O u) G disorderLaw ∧
        (∫ ω in G, O u ω ∂disorderLaw) ≤ Real.sqrt |Co| * q ^ (s - u) / Real.sqrt D := by
    have hu' := Finset.mem_Ico.mp hu
    apply profile_openCorrector_integral_sqrt_le β ht (by omega) (by omega) hts G
      (fun ω hω k hk => hω.1.1 k (Finset.mem_Icc.mpr
        ⟨le_trans hu'.1 (Finset.mem_Icc.mp hk).1, (Finset.mem_Icc.mp hk).2⟩))
      (abs_nonneg Co) hq0.le
    have hbound := hO ϑ hϑ u s (by omega) (by omega) hsK
    have hcast : (u : ℝ) ≤ s := by exact_mod_cast (show u ≤ s by omega)
    have hden : 0 < (blockCount N ρ : ℝ) - u := by dsimp only [D] at hD; linarith
    exact hbound.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self Co) (pow_nonneg hq0.le _)) hden.le).trans
      (div_le_div_of_nonneg_left (by positivity) hD (by dsimp only [D]; linarith)))
  have hrres := hres r (Or.inl rfl)
  have hmres := hres m (Or.inr rfl)
  have hoint : IntegrableOn (fun ω => ∑ u ∈ Finset.Ico r m, O u ω) G disorderLaw :=
    integrable_finsetSum _ (fun u hu => (hopen u hu).1)
  have hdiff := (integrable_sqrt_energy_sub_smoothedEndpointDist β
    (ht (by omega : r - 1 ≤ s)) (ht (by omega : m - 1 ≤ s)) hts).integrableOn (s := G)
  have hpoint : ∀ ω, Real.sqrt (futureEnergy β (t s) N (fun y =>
      smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y -
        smoothedEndpointDist β (t (m - 1)) (t s) 0 ω y)) ≤
      R r ω + R m ω + ∑ u ∈ Finset.Ico r m, O u ω :=
    profile_two_profiles_sqrt_energy_le β t ht N r m s hr hrm hms
  calc
    _ ≤ ∫ ω in G, (R r ω + R m ω + ∑ u ∈ Finset.Ico r m, O u ω) ∂disorderLaw :=
      integral_mono_ae hdiff ((hrres.1.add hmres.1).add hoint) (Eventually.of_forall hpoint)
    _ = (∫ ω in G, R r ω ∂disorderLaw) + (∫ ω in G, R m ω ∂disorderLaw) +
        ∑ u ∈ Finset.Ico r m, ∫ ω in G, O u ω ∂disorderLaw := by
      rw [integral_add (f := fun ω => R r ω + R m ω)
        (g := fun ω => ∑ u ∈ Finset.Ico r m, O u ω) (hrres.1.add hmres.1) hoint,
        integral_add (f := R r) (g := R m) hrres.1 hmres.1,
        integral_finsetSum _ (fun u hu => (hopen u hu).1)]
    _ ≤ Cr / (D * Real.sqrt D) + Cr / (D * Real.sqrt D) +
        ∑ u ∈ Finset.Ico r m, Real.sqrt |Co| * q ^ (s - u) / Real.sqrt D :=
      add_le_add (add_le_add hrres.2 hmres.2) (Finset.sum_le_sum fun u hu => (hopen u hu).2)
    _ ≤ 2 * Cr / (D * Real.sqrt D) +
        (Real.sqrt |Co| / Real.sqrt D) * (q ^ (s - m + 1) / (1 - q)) := by
      rw [show (∑ u ∈ Finset.Ico r m, Real.sqrt |Co| * q ^ (s - u) / Real.sqrt D) =
          (Real.sqrt |Co| / Real.sqrt D) * ∑ u ∈ Finset.Ico r m, q ^ (s - u) by
            rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring]
      have hg := mul_le_mul_of_nonneg_left (profile_prefix_geometric_sum_le hq0.le hq1 hrm hms)
        (show 0 ≤ Real.sqrt |Co| / Real.sqrt D by positivity)
      calc
        _ = 2 * Cr / (D * Real.sqrt D) +
            (Real.sqrt |Co| / Real.sqrt D) * ∑ u ∈ Finset.Ico r m, q ^ (s - u) := by ring
        _ ≤ _ := add_le_add le_rfl hg
    _ = _ := by ring

/-- Two arbitrary entrance profiles have close future masses on a common
past-measurable good event, with the improved residual rate. -/
theorem two_profiles_comparison (A : ℝ) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧
      ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ Cr Co : ℝ, 0 ≤ Cr ∧ 0 ≤ Co ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ r m s : ℕ,
        1 ≤ r → r ≤ m → m ≤ s → s + 2 ≤ blockCount N ρ →
          (∫ ω in profileComparisonGoodSet (criticalBeta ϑ N) (blockTime N ρ) r m s,
            |profileP2Fun (criticalBeta ϑ N) (blockTime N ρ s) N
              (smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (r - 1))
                (blockTime N ρ s) 0 ω) 1 ω -
             profileP2Fun (criticalBeta ϑ N) (blockTime N ρ s) N
              (smoothedEndpointDist (criticalBeta ϑ N) (blockTime N ρ (m - 1))
                (blockTime N ρ s) 0 ω) 1 ω| ∂disorderLaw) ≤
            Cr / (((blockCount N ρ : ℝ) - s) * Real.sqrt ((blockCount N ρ : ℝ) - s)) +
              Co * q ^ (s - m + 1) / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨ρ₀, q, hρ₀, hq0, hq1, hBound⟩ := profile_two_profiles_integral_bound A
  refine ⟨ρ₀, q, hρ₀, hq0, hq1, ?_⟩
  intro ρ hρ
  obtain ⟨Cr, Co, hCr, hCo, hN⟩ := hBound ρ hρ
  refine ⟨Cr, Co, hCr, hCo, ?_⟩
  filter_upwards [hN, blockTime_monotone (hρ₀.trans_le hρ)] with N hB ht
  intro ϑ hϑ r m s hr hrm hms hsK
  have hterminal : blockTime N ρ (blockCount N ρ) = N := by
    simp [blockTime, ne_of_gt (by omega : 0 < blockCount N ρ)]
  exact (profile_future_mass_comparison_le (criticalBeta ϑ N)
    (ht (by omega : r - 1 ≤ s)) (ht (by omega : m - 1 ≤ s))
    ((ht (by omega : s ≤ blockCount N ρ)).trans_eq hterminal) _
    (measurableSet_profileComparisonGoodSet_past _ ht hr (by omega) (by omega) hms)).trans
    (hB ϑ hϑ r m s hr hrm hms hsK)

/-- Intersecting the two entrance-dependent good events costs at most twice
the one-profile exceptional probability. -/
theorem profileComparisonGoodSet_compl_bound (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ r m s : ℕ, 1 ≤ r → r ≤ m → m ≤ s → s + 1 ≤ blockCount N ρ →
          (disorderLaw (profileComparisonGoodSet (criticalBeta ϑ N) (blockTime N ρ) r m s)ᶜ).toReal ≤
            C / ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨ρ₀, hρ₀, hBound⟩ := profileGoodSet_compl_bound A
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨C, hC⟩ := hBound ρ₁
  refine ⟨2 * C, ?_⟩
  intro ρ hρ
  filter_upwards [hC ρ hρ] with N hN
  intro ϑ hϑ r m s hr hrm hms hsK
  rw [profileComparisonGoodSet, Set.compl_inter]
  exact (measureReal_union_le _ _).trans ((add_le_add
    (hN ϑ hϑ r s hr (by omega) hsK) (hN ϑ hϑ m s (by omega) hms hsK)).trans_eq (by ring))

/-- The lattice comparison in the bounded form used in weak convergence,
at every shorter future horizon and every spatial center. -/
theorem profile_comparison_lattice_truncated (A : ℝ) :
    ∃ ρ₀ q : ℝ, 1 < ρ₀ ∧ 0 < q ∧ q < 1 / 2 ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ Cr Co Cb : ℝ, 0 ≤ Cr ∧ 0 ≤ Co ∧ 0 ≤ Cb ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ r m s T : ℕ,
        1 ≤ r → r ≤ m → m ≤ s → s + 2 ≤ blockCount N ρ → blockTime N ρ s ≤ T → T ≤ N →
        ∀ x : Site, ∀ M : ℝ, 0 ≤ M →
          (∫ ω, min
            |smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (r - 1)) T x ω /
                smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (r - 1)) (blockTime N ρ s) x ω -
             smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (m - 1)) T x ω /
                smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (m - 1)) (blockTime N ρ s) x ω|
            M ∂disorderLaw) ≤
              Cr / (((blockCount N ρ : ℝ) - s) * Real.sqrt ((blockCount N ρ : ℝ) - s)) +
              Co * q ^ (s - m + 1) / Real.sqrt ((blockCount N ρ : ℝ) - s) +
              Cb * M / ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨ρr, q, hρr, hq0, hq1, hBound⟩ := two_profiles_comparison A
  obtain ⟨ρb, hρb, hBad⟩ := profileComparisonGoodSet_compl_bound A
  refine ⟨max ρr ρb, q, hρr.trans_le (le_max_left _ _), hq0, hq1, ?_⟩
  intro ρ hρ
  have hρ1 : 1 < ρ := hρr.trans_le ((le_max_left _ _).trans hρ)
  obtain ⟨Cr, Co, hCr, hCo, hRate⟩ := hBound ρ ((le_max_left _ _).trans hρ)
  obtain ⟨Cb, hCb⟩ := hBad ρ
  refine ⟨Cr, Co, |Cb|, hCr, hCo, abs_nonneg _, ?_⟩
  filter_upwards [hRate, hCb ρ ⟨(le_max_right _ _).trans hρ, le_rfl⟩,
    blockTime_monotone hρ1] with N hN hB ht
  intro ϑ hϑ r m s T hr hrm hms hsK hsT hTN x M hM
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let G := profileComparisonGoodSet β t r m s
  have hD : 0 < (blockCount N ρ : ℝ) - s :=
    sub_pos.mpr (by exact_mod_cast (show s < blockCount N ρ by omega))
  have hbad := (hB ϑ hϑ r m s hr hrm hms (by omega)).trans
    (div_le_div_of_nonneg_right (le_abs_self Cb) hD.le)
  rw [profile_lattice_ratio_cap_spatial]
  have htrunc := profile_future_mass_truncated_horizon_le β
    (ht (by omega : r - 1 ≤ s)) (ht (by omega : m - 1 ≤ s)) hsT hTN G
    (measurableSet_profileComparisonGoodSet_past β ht hr (by omega) (by omega) hms) M
  have hfinal := htrunc.trans (add_le_add (hN ϑ hϑ r m s hr hrm hms hsK)
    (mul_le_mul_of_nonneg_left hbad hM))
  have heq (a : ℕ) (ha : a ≤ t s) (ω : Disorder) :
      profileP2Fun β (t s) T (smoothedEndpointDist β a (t s) 0 ω) 1 ω =
        smoothedP2Plane β a T 0 ω / smoothedP2Plane β a (t s) 0 ω :=
    profileMass_lattice_ratio β ha hsT 0 ω
  convert hfinal using 1
  · apply integral_congr_ae
    filter_upwards [] with ω
    rw [heq (t (r - 1)) (ht (by omega)) ω, heq (t (m - 1)) (ht (by omega)) ω]
  · ring

end Critical2DKPZ.Extensions.GffTangent

end
