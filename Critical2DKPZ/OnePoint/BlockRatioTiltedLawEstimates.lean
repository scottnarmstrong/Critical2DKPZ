/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawGoodSet
public import Critical2DKPZ.OnePoint.BlockRatioIntegralExpansion
public import Critical2DKPZ.OnePoint.BlockRatioTiltedPairEstimate
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Mathlib.Tactic

/-! # Block-ratio bounds under the inverse-mass tilted law -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private theorem invBlockProduct_abs_le_two_on_goodSet (β : ℝ) (t : ℕ → ℕ)
    {r s : ℕ} (hrs : r ≤ s) {ω : Disorder}
    (hω : ω ∈ blockGoodSet β t r s) :
    |∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹| ≤ 2 ^ (s - r + 1) := by
  classical
  change ∀ i ∈ Finset.Icc r s, |blockMass β t i ω - 1| ≤ 1 / 2 at hω
  have hterm (i : ℕ) (hi : i ∈ Finset.Icc r s) :
      |(blockMass β t i ω)⁻¹| ≤ 2 := by
    have hgood := hω i hi
    have hpos := blockMass_pos β t i ω
    have hlow : 1 / 2 ≤ blockMass β t i ω := by
      rw [abs_le] at hgood
      linarith
    rw [abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    exact (inv_le_iff_one_le_mul₀' hpos).2 (by nlinarith)
  have hcard : (Finset.Icc r s).card = s - r + 1 := by
    simp only [Nat.card_Icc]
    omega
  rw [Finset.abs_prod]
  calc
    ∏ i ∈ Finset.Icc r s, |(blockMass β t i ω)⁻¹| ≤
        ∏ _i ∈ Finset.Icc r s, (2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact abs_nonneg _
      · intro i hi
        exact hterm i hi
    _ = 2 ^ (Finset.Icc r s).card := by simp
    _ = 2 ^ (s - r + 1) := by rw [hcard]

/-- On the good set the inverse-product density is bounded, so every pair term remains
integrable after multiplication by that density. -/
theorem integrableOn_familyTermPair_mul_invBlockProduct (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {r s : ℕ} (hrs : r ≤ s)
    (F G : Finset (ℕ × ℕ)) (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) :
    IntegrableOn
      (fun ω => familyTerm β t F ω * familyTerm β t G ω *
        ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹)
      (blockGoodSet β t r s) disorderLaw := by
  classical
  let W : Disorder → ℝ := fun ω =>
    ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹
  let P : Disorder → ℝ := fun ω => familyTerm β t F ω * familyTerm β t G ω
  let B : ℝ := 2 ^ (s - r + 1)
  have hB : 0 ≤ B := by positivity
  have hPint : Integrable P (disorderLaw.restrict (blockGoodSet β t r s)) := by
    simpa [P] using integrable_familyTerm_mul_on_goodSet β t ht F G hF hG
  have hPmeas : Measurable P := by
    exact (measurable_familyTerm β t ht F hF).mul
      (measurable_familyTerm β t ht G hG)
  have hWmeas : Measurable W := by
    apply Finset.measurable_prod
    intro i hi
    exact ((measurable_blockMass β t i).mono
      (Gaussian.disorderBlock_le _ _) le_rfl).inv
  have hmajor : Integrable (fun ω => B * ‖P ω‖)
      (disorderLaw.restrict (blockGoodSet β t r s)) := by
    simpa [B, mul_comm] using hPint.norm.const_mul B
  apply hmajor.mono' ((hPmeas.mul hWmeas).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (measurableSet_blockGoodSet β t r s)] with ω hω
  have hW := invBlockProduct_abs_le_two_on_goodSet β t hrs hω
  dsimp [P, W, B]
  calc
    |familyTerm β t F ω * familyTerm β t G ω *
        ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹| =
      |familyTerm β t F ω * familyTerm β t G ω| *
        |∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹| := abs_mul _ _
    _ ≤ |familyTerm β t F ω * familyTerm β t G ω| * 2 ^ (s - r + 1) :=
      mul_le_mul_of_nonneg_left hW (abs_nonneg _)
    _ = 2 ^ (s - r + 1) *
        ‖familyTerm β t F ω * familyTerm β t G ω‖ := by
      rw [Real.norm_eq_abs]
      ring

/-- The squared-ratio expansion with the inverse-product density. Each summand is integrable by
`integrableOn_familyTermPair_mul_invBlockProduct`. -/
theorem setIntegral_blockRatio_sub_one_sq_mul_invProd_eq (β : ℝ)
    {t : ℕ → ℕ} (ht : Monotone t) {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    ∫ ω in blockGoodSet β t r s,
        (blockRatio β t r s ω - 1) ^ 2 *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw =
      ∑ F ∈ (intervalFamilies r s).erase ∅,
        ∑ G ∈ (intervalFamilies r s).erase ∅,
          ∫ ω in blockGoodSet β t r s,
            familyTerm β t F ω * familyTerm β t G ω *
              ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
  classical
  let S := (intervalFamilies r s).erase ∅
  have hempty : ∅ ∈ intervalFamilies r s := by
    rw [intervalFamilies_mem_iff]
    simp
  have hratio : blockRatio β t r s = fun ω =>
      ∑ F ∈ intervalFamilies r s, familyTerm β t F ω := by
    funext ω
    simpa [familyTerm] using
      blockRatio_eq_sum_intervalFamilies β t ht r s hr hrs ω
  have hsum (ω : Disorder) : blockRatio β t r s ω - 1 =
      ∑ F ∈ S, familyTerm β t F ω := by
    rw [hratio]
    calc
      (∑ F ∈ intervalFamilies r s, familyTerm β t F ω) - 1 =
          (familyTerm β t ∅ ω + ∑ F ∈ S, familyTerm β t F ω) - 1 := by
        rw [← Finset.add_sum_erase (s := intervalFamilies r s) (a := ∅)
          (f := fun F => familyTerm β t F ω) hempty]
      _ = ∑ F ∈ S, familyTerm β t F ω := by simp [familyTerm]
  let W : Disorder → ℝ := fun ω =>
    ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹
  have hsq (ω : Disorder) :
      (blockRatio β t r s ω - 1) ^ 2 * W ω =
        ∑ F ∈ S, ∑ G ∈ S,
          familyTerm β t F ω * familyTerm β t G ω * W ω := by
    have hsq0 : (blockRatio β t r s ω - 1) ^ 2 =
        ∑ F ∈ S, ∑ G ∈ S,
          familyTerm β t F ω * familyTerm β t G ω := by
      rw [hsum, pow_two]
      exact Finset.sum_mul_sum S S (fun F => familyTerm β t F ω)
        (fun G => familyTerm β t G ω)
    rw [hsq0]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro F hF
    rw [Finset.sum_mul]
  have htermInt (F G : Finset (ℕ × ℕ)) (hF : F ∈ S) (hG : G ∈ S) :
      Integrable (fun ω => familyTerm β t F ω * familyTerm β t G ω * W ω)
        (disorderLaw.restrict (blockGoodSet β t r s)) := by
    simpa [IntegrableOn, W] using integrableOn_familyTermPair_mul_invBlockProduct β t ht hrs F G
      (Finset.mem_of_mem_erase hF) (Finset.mem_of_mem_erase hG)
  have hsumInt : Integrable
      (fun ω => ∑ F ∈ S, ∑ G ∈ S,
        familyTerm β t F ω * familyTerm β t G ω * W ω)
      (disorderLaw.restrict (blockGoodSet β t r s)) := by
    apply integrable_finsetSum
    intro F hF
    apply integrable_finsetSum
    intro G hG
    exact htermInt F G hF hG
  calc
    ∫ ω in blockGoodSet β t r s,
        (blockRatio β t r s ω - 1) ^ 2 * W ω ∂disorderLaw =
      ∫ ω in blockGoodSet β t r s,
        ∑ F ∈ S, ∑ G ∈ S,
          familyTerm β t F ω * familyTerm β t G ω * W ω ∂disorderLaw :=
        integral_congr_ae (Eventually.of_forall hsq)
    _ = ∑ F ∈ S, ∑ G ∈ S,
          ∫ ω in blockGoodSet β t r s,
            familyTerm β t F ω * familyTerm β t G ω * W ω ∂disorderLaw := by
      rw [integral_finsetSum _ (fun F hF =>
        integrable_finsetSum _ (fun G hG => htermInt F G hF hG))]
      apply Finset.sum_congr rfl
      intro F hF
      rw [integral_finsetSum _ (fun G hG => htermInt F G hF hG)]

/-- The tilted good-set ratio bound from the weighted pair estimate and
`BlockMomentsBound`. -/
theorem blockGoodSet_tilted_compl_and_ratio_bound_pair_of (hC6 : BlockMomentsBound) (A : ℝ)
    (hPair : ∃ C₀ ρp Cpair : ℝ, 0 < C₀ ∧ 1 < ρp ∧ 1 ≤ Cpair ∧
      ∀ ρ : ℝ, ρp ≤ ρ → ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s →
          s + 1 ≤ blockCount N ρ →
          ∀ F ∈ intervalFamilies r s, ∀ G ∈ intervalFamilies r s,
            |∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
                familyTerm (criticalBeta ϑ N) (blockTime N ρ) F ω *
                  familyTerm (criticalBeta ϑ N) (blockTime N ρ) G ω *
                  ∏ i ∈ Finset.Icc r s,
                    (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw| /
              (∫ ω, ∏ i ∈ Finset.Icc r s,
                  (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
                ∏ c ∈ pairComponents r s F G,
                  componentWeight (Cpair * C₀ / Real.sqrt (Real.log ρ))
                    (blockCount N ρ) F G c) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s →
          s + 1 ≤ blockCount N ρ →
            (∫ ω in (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ,
                ∏ i ∈ Finset.Icc r s,
                  (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) /
              (∫ ω, ∏ i ∈ Finset.Icc r s,
                  (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
                C / Real.sqrt ((blockCount N ρ : ℝ) - s) ∧
            (∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
                (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω - 1) ^ 2 *
                  ∏ i ∈ Finset.Icc r s,
                    (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) /
              (∫ ω, ∏ i ∈ Finset.Icc r s,
                  (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
                C / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨C₀, ρp, Cpair, hC₀, hρp, hCpair, hPair⟩ := hPair
  obtain ⟨ε₀, Csum, hε₀, hCsum, hsum⟩ := sum_prod_componentWeight_le
  let q : ℝ := Cpair * C₀ / ε₀
  let ρ₀ : ℝ := max (ρp + 1) (Real.exp (q ^ 2) + 1)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hρ₀ : 1 < ρ₀ := by
    dsimp [ρ₀]
    exact lt_of_lt_of_le (by linarith [hρp]) (le_max_left _ _)
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨Ccomp, hcomp⟩ := tilted_blockGoodSet_compl_le_of hC6 A ρ₀ ρ₁ hρ₀
  let C : ℝ := max Ccomp (Csum * ε₀)
  refine ⟨C, ?_⟩
  intro ρ hρρ
  have hρpρ : ρp ≤ ρ := by
    have hleft : ρp + 1 ≤ ρ := le_trans (le_max_left _ _) hρρ.1
    linarith
  have hexpρ : Real.exp (q ^ 2) < ρ := by
    have hright : Real.exp (q ^ 2) + 1 ≤ ρ := le_trans (le_max_right _ _) hρρ.1
    linarith
  have hlogρ : q ^ 2 < Real.log ρ := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexpρ
  have hqnonneg : 0 ≤ q := le_of_lt hqpos
  have hqle : q ≤ Real.sqrt (Real.log ρ) := by
    have hsqrtq : Real.sqrt (q ^ 2) = q := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hqnonneg]
    rw [← hsqrtq]
    exact Real.sqrt_le_sqrt (le_of_lt hlogρ)
  have hε : 0 ≤ Cpair * C₀ / Real.sqrt (Real.log ρ) := by positivity
  have hεle : Cpair * C₀ / Real.sqrt (Real.log ρ) ≤ ε₀ := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (Real.log_pos (by
      have : 1 < ρ := lt_of_lt_of_le hρ₀ hρρ.1
      linarith)))]
    have hmul := mul_le_mul_of_nonneg_left hqle (le_of_lt hε₀)
    dsimp [q] at hmul
    field_simp [ne_of_gt hε₀] at hmul
    exact hmul
  have hclock : ∀ᶠ N : ℕ in atTop,
      ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N := Filter.eventually_ge_atTop _
  filter_upwards [hcomp ρ hρρ, hPair ρ hρpρ, hclock] with N hcompN hPairN hN
  intro ϑ hϑ r s hr hrs hsK
  have ht : Monotone (blockTime N ρ) :=
    Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon hρ₀ hρρ.1 hN
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let S := (intervalFamilies r s).erase ∅
  let W : Disorder → ℝ := fun ω =>
    ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹
  have hdenEq :
      ∫ ω, W ω ∂disorderLaw =
        ∏ i ∈ Finset.Icc r s,
          ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    simpa [W] using integral_finset_prod_inv_blockMass β t ht (Finset.Icc r s)
      (by intro i hi; exact le_trans hr (Finset.mem_Icc.mp hi).1)
  have hdenPos : 0 < ∫ ω, W ω ∂disorderLaw := by
    rw [hdenEq]
    apply Finset.prod_pos
    intro i hi
    exact lt_of_lt_of_le zero_lt_one (one_le_integral_inv_blockMass β t i)
  have hpairSum :
      (∑ F ∈ S, ∑ G ∈ S,
        (∫ ω in blockGoodSet β t r s,
          familyTerm β t F ω * familyTerm β t G ω * W ω ∂disorderLaw) /
          (∫ ω, W ω ∂disorderLaw)) ≤
        ∑ F ∈ S, ∑ G ∈ S,
          ∏ c ∈ pairComponents r s F G,
            componentWeight (Cpair * C₀ / Real.sqrt (Real.log ρ))
              (blockCount N ρ) F G c := by
    apply Finset.sum_le_sum
    intro F hF
    apply Finset.sum_le_sum
    intro G hG
    have h := hPairN ϑ hϑ r s hr hrs hsK F
      (Finset.mem_of_mem_erase hF) G (Finset.mem_of_mem_erase hG)
    have hterm :
        (∫ ω in blockGoodSet β t r s,
          familyTerm β t F ω * familyTerm β t G ω * W ω ∂disorderLaw) /
          (∫ ω, W ω ∂disorderLaw) ≤
        |∫ ω in blockGoodSet β t r s,
          familyTerm β t F ω * familyTerm β t G ω * W ω ∂disorderLaw| /
          (∫ ω, W ω ∂disorderLaw) :=
      div_le_div_of_nonneg_right (le_abs_self _) (le_of_lt hdenPos)
    exact le_trans hterm (by simpa [W] using h)
  have hcompSum := hsum (Cpair * C₀ / Real.sqrt (Real.log ρ)) hε hεle
    (blockCount N ρ) r s hr hrs (by omega)
  have hsecond :
      (∫ ω in blockGoodSet β t r s,
        (blockRatio β t r s ω - 1) ^ 2 * W ω ∂disorderLaw) /
        (∫ ω, W ω ∂disorderLaw) ≤
        Csum * (Cpair * C₀ / Real.sqrt (Real.log ρ)) /
          ((blockCount N ρ : ℝ) - s) := by
    rw [setIntegral_blockRatio_sub_one_sq_mul_invProd_eq β ht hr hrs]
    simp only [Finset.sum_div]
    exact hpairSum.trans hcompSum
  have hgap : 1 ≤ (blockCount N ρ : ℝ) - s := by
    have hnat : 1 ≤ blockCount N ρ - s := by omega
    rw [← Nat.cast_sub (by omega : s ≤ blockCount N ρ)]
    exact_mod_cast hnat
  have hgapSqrt : Real.sqrt ((blockCount N ρ : ℝ) - s) ≤
      (blockCount N ρ : ℝ) - s := by
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [Real.sq_sqrt (show 0 ≤ (blockCount N ρ : ℝ) - s by linarith)]⟩
  have hsecondBound :
      (∫ ω in blockGoodSet β t r s,
        (blockRatio β t r s ω - 1) ^ 2 * W ω ∂disorderLaw) /
        (∫ ω, W ω ∂disorderLaw) ≤ C / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
    dsimp [C]
    calc
      _ ≤ (Csum * ε₀) / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
        calc
          _ ≤ (Csum * ε₀) / ((blockCount N ρ : ℝ) - s) := by
            exact hsecond.trans (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hεle hCsum.le) (by positivity))
          _ ≤ _ := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hgapSqrt
      _ ≤ max Ccomp (Csum * ε₀) / Real.sqrt ((blockCount N ρ : ℝ) - s) :=
        div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  have hcomplementBound :
      (∫ ω in (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ,
          ∏ i ∈ Finset.Icc r s,
            (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) /
        (∫ ω, ∏ i ∈ Finset.Icc r s,
            (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
        C / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
    dsimp [C]
    exact le_trans (hcompN ϑ hϑ r s hr hrs hsK)
      (div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt (Real.sqrt_pos.2 (by linarith [hgap]))))
  exact ⟨hcomplementBound, hsecondBound⟩

/-- The tilted good-set ratio estimate from the weighted pair bound and block moments. -/
theorem blockGoodSet_tilted_compl_and_ratio_bound_of (hC6 : BlockMomentsBound) (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s →
          s + 1 ≤ blockCount N ρ →
            (∫ ω in (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ,
                ∏ i ∈ Finset.Icc r s,
                  (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) /
              (∫ ω, ∏ i ∈ Finset.Icc r s,
                  (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
                C / Real.sqrt ((blockCount N ρ : ℝ) - s) ∧
            (∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
                (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω - 1) ^ 2 *
                  ∏ i ∈ Finset.Icc r s,
                    (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) /
              (∫ ω, ∏ i ∈ Finset.Icc r s,
                  (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
                C / Real.sqrt ((blockCount N ρ : ℝ) - s) := by
  exact blockGoodSet_tilted_compl_and_ratio_bound_pair_of hC6 A
    (abs_tilted_setIntegral_familyTerm_mul_le A)

end Critical2DKPZ.OnePoint

end
