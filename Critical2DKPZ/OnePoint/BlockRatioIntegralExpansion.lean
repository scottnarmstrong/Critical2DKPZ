/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioExpansion
public import Critical2DKPZ.Blocks.DiscrepancyMoments
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! # Integrability and the block-ratio expansion -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks
noncomputable section

private def familyClosedProduct (β : ℝ) (t : ℕ → ℕ)
    (F : Finset (ℕ × ℕ)) (ω : Disorder) : ℝ :=
  ∏ I ∈ F, closedDiscrepancy β t I.1 I.2 ω

private def familyMassProduct (β : ℝ) (t : ℕ → ℕ)
    (F : Finset (ℕ × ℕ)) (ω : Disorder) : ℝ :=
  ∏ I ∈ F, ∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω

private theorem familyTerm_eq_div_products (β : ℝ) (t : ℕ → ℕ)
    (F : Finset (ℕ × ℕ)) (ω : Disorder) :
    familyTerm β t F ω = familyClosedProduct β t F ω / familyMassProduct β t F ω := by
  simp [familyTerm, familyClosedProduct, familyMassProduct, Finset.prod_div_distrib]

private theorem familyMassProduct_pos (β : ℝ) (t : ℕ → ℕ)
    (F : Finset (ℕ × ℕ)) (ω : Disorder) : 0 < familyMassProduct β t F ω := by
  unfold familyMassProduct
  exact Finset.prod_pos fun I _ =>
    Finset.prod_pos fun i _ => blockMass_pos β t i ω

private theorem measurable_blockMass_global (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Measurable (blockMass β t i) := by
  exact (measurable_blockMass β t i).mono
    (Gaussian.disorderBlock_le _ _) le_rfl

/-- Each interval-family ratio term is measurable. -/
theorem measurable_familyTerm (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {r s : ℕ} (F : Finset (ℕ × ℕ)) (hF : F ∈ intervalFamilies r s) :
    Measurable (familyTerm β t F) := by
  classical
  have hclosed (I : ℕ × ℕ) (hI : I ∈ F) : Measurable (fun ω =>
      closedDiscrepancy β t I.1 I.2 ω) := by
    have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hI
    exact (measurable_closedDiscrepancy β t ht I.1 I.2 (Nat.le_of_lt hbounds.2.2.2.2)).mono
      (Gaussian.disorderBlock_le _ _) le_rfl
  have hdenom (I : ℕ × ℕ) : Measurable (fun ω =>
      ∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω) := by
    apply Finset.measurable_prod
    intro i hi
    exact measurable_blockMass_global β t i
  unfold familyTerm
  apply Finset.measurable_prod
  intro I hI
  exact (hclosed I hI).div (hdenom I)

/-- The finite intersection defining a block good set is measurable. -/
theorem measurableSet_blockGoodSet (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) :
    MeasurableSet (blockGoodSet β t r s) := by
  classical
  have h : MeasurableSet (⋂ i ∈ Finset.Icc r s,
      {ω | |blockMass β t i ω - 1| ≤ 1 / 2}) := by
    apply Finset.measurableSet_biInter
    intro i hi
    apply measurableSet_le
    · exact (measurable_blockMass_global β t i).sub measurable_const |>.abs
    · exact measurable_const
  convert h using 1
  ext ω
  simp [blockGoodSet]

/-- The product of closed discrepancies over one interval family is square integrable. -/
theorem memLp_intervalFamilyClosedProduct (β : ℝ) (t : ℕ → ℕ)
    {r s : ℕ} (F : Finset (ℕ × ℕ)) (hF : F ∈ intervalFamilies r s) :
    MemLp (fun ω => ∏ I ∈ F, closedDiscrepancy β t I.1 I.2 ω) 2 disorderLaw := by
  classical
  by_cases hFempty : F = ∅
  · simpa [hFempty] using (memLp_const (1 : ℝ) :
        MemLp (fun _ : Disorder => (1 : ℝ)) 2 disorderLaw)
  · have hFpos : 0 < F.card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hFempty)
    have hcard : (F.card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hFpos)
    let q : ℝ≥0∞ := 2 * (F.card : ℝ≥0∞)
    have hq0 : q ≠ 0 := by
      dsimp [q]
      intro h
      rcases mul_eq_zero.mp h with htwo | hFcard
      · norm_num at htwo
      · exact hcard hFcard
    have hqTop : q ≠ ∞ := by
      dsimp [q]
      exact ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _)
    have hsumCard : (F.card : ℝ≥0∞) * q⁻¹ = (1 / 2 : ℝ≥0∞) := by
      dsimp [q]
      calc
        (F.card : ℝ≥0∞) * ((2 : ℝ≥0∞) * (F.card : ℝ≥0∞))⁻¹ =
            (2 : ℝ≥0∞)⁻¹ * ((F.card : ℝ≥0∞) * (F.card : ℝ≥0∞)⁻¹) := by
          rw [ENNReal.mul_inv (by left; norm_num) (by left; norm_num)]
          ac_rfl
        _ = (2 : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _)]
          simp
        _ = 1 / 2 := by norm_num
    have hfactor (I : ℕ × ℕ) (hI : I ∈ F) :
        MemLp (fun ω => closedDiscrepancy β t I.1 I.2 ω) q disorderLaw := by
      have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hI
      exact Critical2DKPZ.Blocks.memLp_closedDiscrepancy β t I.1 I.2 q hq0 hqTop
    have hprod : MemLp (fun ω => ∏ I ∈ F, closedDiscrepancy β t I.1 I.2 ω)
        ((∑ I ∈ F, q⁻¹)⁻¹) disorderLaw := by
      apply MemLp.fun_prod
      intro I hI
      exact hfactor I hI
    have hsumInv : ((F.card : ℝ≥0∞) * q⁻¹)⁻¹ = 2 := by
      rw [hsumCard]
      norm_num
    simpa [hsumInv] using hprod

private theorem familyMassProduct_inv_le_on_goodSet (β : ℝ) (t : ℕ → ℕ)
    {r s : ℕ} (F : Finset (ℕ × ℕ)) (hF : F ∈ intervalFamilies r s)
    {ω : Disorder} (hω : ω ∈ blockGoodSet β t r s) :
    (familyMassProduct β t F ω)⁻¹ ≤ 2 ^ ((s + 1) * F.card) := by
  classical
  change ∀ i ∈ Finset.Icc r s, |blockMass β t i ω - 1| ≤ 1 / 2 at hω
  have hdenom (I : ℕ × ℕ) (hI : I ∈ F) :
      (∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω)⁻¹ ≤ 2 ^ (s + 1) := by
    let S := Finset.Icc I.1 I.2
    have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hI
    have hcard : S.card ≤ s + 1 := by
      have hsub : S ⊆ Finset.Icc 0 s := by
        intro i hi
        have hi' := Finset.mem_Icc.mp hi
        exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, le_trans hi'.2 hbounds.2.2.2.1⟩
      calc
        S.card ≤ (Finset.Icc 0 s).card := Finset.card_le_card hsub
        _ = s + 1 := by simp [Nat.card_Icc]
    have hinv (i : ℕ) (hi : i ∈ S) : (blockMass β t i ω)⁻¹ ≤ 2 := by
      have hi' : i ∈ Finset.Icc r s := by
        have hi' := Finset.mem_Icc.mp hi
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hgood := hω i hi'
      have hpos := blockMass_pos β t i ω
      have hlow : 1 / 2 ≤ blockMass β t i ω := by
        rw [abs_le] at hgood
        linarith
      exact (inv_le_iff_one_le_mul₀' hpos).2 (by nlinarith)
    have hprod :
        (∏ i ∈ S, (blockMass β t i ω)⁻¹) ≤ ∏ _i ∈ S, (2 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact inv_nonneg.mpr (le_of_lt (blockMass_pos β t i ω))
      · intro i hi
        exact hinv i hi
    have hprodEq :
        (∏ i ∈ S, (blockMass β t i ω)⁻¹) =
          (∏ i ∈ S, blockMass β t i ω)⁻¹ := by
      simp [Finset.prod_inv_distrib]
    rw [← hprodEq]
    calc
      (∏ i ∈ S, (blockMass β t i ω)⁻¹) ≤ ∏ _i ∈ S, (2 : ℝ) := hprod
      _ = 2 ^ S.card := by simp
      _ ≤ 2 ^ (s + 1) := by exact pow_le_pow_right₀ (by norm_num) hcard
  have hmassInv :
      (familyMassProduct β t F ω)⁻¹ =
        ∏ I ∈ F, (∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω)⁻¹ := by
    simp [familyMassProduct, Finset.prod_inv_distrib]
  rw [hmassInv]
  calc
    (∏ I ∈ F, (∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω)⁻¹) ≤
        ∏ _I ∈ F, (2 ^ (s + 1) : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro I hI
        exact inv_nonneg.mpr (le_of_lt (Finset.prod_pos fun i _ => blockMass_pos β t i ω))
      · intro I hI
        exact hdenom I hI
    _ = 2 ^ ((s + 1) * F.card) := by
      simp only [Finset.prod_const, Finset.card]
      exact (pow_mul 2 (s + 1) F.card).symm

/-- Pair terms from two interval families are integrable after restriction to the block good set.
The good-set lower bound controls every denominator; closed discrepancies have all finite moments. -/
theorem integrable_familyTerm_mul_on_goodSet (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t)
    {r s : ℕ} (F G : Finset (ℕ × ℕ))
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s) :
    Integrable (fun ω => familyTerm β t F ω * familyTerm β t G ω)
      (disorderLaw.restrict (blockGoodSet β t r s)) := by
  classical
  have hFclosed := memLp_intervalFamilyClosedProduct β t F hF
  have hGclosed := memLp_intervalFamilyClosedProduct β t G hG
  have hpairMem : MemLp (fun ω => familyClosedProduct β t F ω *
      familyClosedProduct β t G ω) 1 disorderLaw := by
    simpa [familyClosedProduct] using Polymer.memLp_mul_double 1
      (by simpa only [mul_one] using hFclosed)
      (by simpa only [mul_one] using hGclosed)
  have hpair : Integrable (fun ω => familyClosedProduct β t F ω *
      familyClosedProduct β t G ω) disorderLaw := memLp_one_iff_integrable.mp hpairMem
  let B : ℝ := 2 ^ ((s + 1) * F.card) * 2 ^ ((s + 1) * G.card)
  have hB : 0 ≤ B := by positivity
  have hmajor : Integrable (fun ω => B *
      |familyClosedProduct β t F ω * familyClosedProduct β t G ω|) disorderLaw := by
    simpa [B, mul_comm, mul_left_comm, mul_assoc] using hpair.norm.const_mul B
  have hmajorR : Integrable (fun ω => B *
      |familyClosedProduct β t F ω * familyClosedProduct β t G ω|)
      (disorderLaw.restrict (blockGoodSet β t r s)) :=
    hmajor.mono_measure (Measure.restrict_le_self)
  apply hmajorR.mono'
  · exact ((measurable_familyTerm β t ht F hF).mul
      (measurable_familyTerm β t ht G hG)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurableSet_blockGoodSet β t r s)] with ω hω
    have hmassF := familyMassProduct_pos β t F ω
    have hmassG := familyMassProduct_pos β t G ω
    have hboundF := familyMassProduct_inv_le_on_goodSet β t F hF hω
    have hboundG := familyMassProduct_inv_le_on_goodSet β t G hG hω
    have htermF : |familyTerm β t F ω| ≤
        (2 ^ ((s + 1) * F.card)) * |familyClosedProduct β t F ω| := by
      rw [familyTerm_eq_div_products]
      rw [abs_div, abs_of_pos hmassF]
      calc
        |familyClosedProduct β t F ω| / familyMassProduct β t F ω =
            |familyClosedProduct β t F ω| * (familyMassProduct β t F ω)⁻¹ := by ring
        _ ≤ |familyClosedProduct β t F ω| * 2 ^ ((s + 1) * F.card) :=
            mul_le_mul_of_nonneg_left hboundF (abs_nonneg _)
        _ = 2 ^ ((s + 1) * F.card) * |familyClosedProduct β t F ω| := by ring
    have htermG : |familyTerm β t G ω| ≤
        (2 ^ ((s + 1) * G.card)) * |familyClosedProduct β t G ω| := by
      rw [familyTerm_eq_div_products]
      rw [abs_div, abs_of_pos hmassG]
      calc
        |familyClosedProduct β t G ω| / familyMassProduct β t G ω =
            |familyClosedProduct β t G ω| * (familyMassProduct β t G ω)⁻¹ := by ring
        _ ≤ |familyClosedProduct β t G ω| * 2 ^ ((s + 1) * G.card) :=
            mul_le_mul_of_nonneg_left hboundG (abs_nonneg _)
        _ = 2 ^ ((s + 1) * G.card) * |familyClosedProduct β t G ω| := by ring
    have hterms := mul_le_mul htermF htermG (abs_nonneg _) (by positivity :
      0 ≤ (2 ^ ((s + 1) * F.card)) * |familyClosedProduct β t F ω|)
    have hnorm : |familyTerm β t F ω * familyTerm β t G ω| ≤
        B * |familyClosedProduct β t F ω * familyClosedProduct β t G ω| := by
      rw [abs_mul, abs_mul]
      simpa [B, mul_assoc, mul_left_comm, mul_comm] using hterms
    simpa [Real.norm_eq_abs] using hnorm

/-- The squared deviation of the block ratio from one is integrable on the good set. -/
theorem integrableOn_blockRatio_sub_one_sq (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t)
    {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    IntegrableOn (fun ω => (blockRatio β t r s ω - 1) ^ 2)
      (blockGoodSet β t r s) disorderLaw := by
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
  have hsq (ω : Disorder) : (blockRatio β t r s ω - 1) ^ 2 =
      ∑ F ∈ S, ∑ G ∈ S, familyTerm β t F ω * familyTerm β t G ω := by
    rw [hsum, pow_two]
    exact Finset.sum_mul_sum S S (fun F => familyTerm β t F ω)
      (fun G => familyTerm β t G ω)
  have hint (F G : Finset (ℕ × ℕ)) (hF : F ∈ S) (hG : G ∈ S) :
      Integrable (fun ω => familyTerm β t F ω * familyTerm β t G ω)
        (disorderLaw.restrict (blockGoodSet β t r s)) :=
    integrable_familyTerm_mul_on_goodSet β t ht F G
      (Finset.mem_of_mem_erase hF) (Finset.mem_of_mem_erase hG)
  have hsumInt : Integrable
      (fun ω => ∑ F ∈ S, ∑ G ∈ S,
        familyTerm β t F ω * familyTerm β t G ω)
      (disorderLaw.restrict (blockGoodSet β t r s)) := by
    apply integrable_finsetSum
    intro F hF
    apply integrable_finsetSum
    intro G hG
    exact hint F G hF hG
  have hsqInt : Integrable
      (fun ω => (blockRatio β t r s ω - 1) ^ 2)
      (disorderLaw.restrict (blockGoodSet β t r s)) :=
    hsumInt.congr (Filter.Eventually.of_forall fun ω => (hsq ω).symm)
  simpa only [IntegrableOn] using hsqInt

/-- The good-set second moment of the block-ratio deviation equals the sum of pair integrals over nonempty interval families. -/
theorem setIntegral_blockRatio_sub_one_sq_eq (β : ℝ) {t : ℕ → ℕ} (ht : Monotone t) {r s : ℕ}
    (hr : 1 ≤ r) (hrs : r ≤ s) :
    ∫ ω in blockGoodSet β t r s, (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw =
      ∑ F ∈ (intervalFamilies r s).erase ∅, ∑ G ∈ (intervalFamilies r s).erase ∅,
        ∫ ω in blockGoodSet β t r s,
          familyTerm β t F ω * familyTerm β t G ω ∂disorderLaw := by
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
  have hsq (ω : Disorder) : (blockRatio β t r s ω - 1) ^ 2 =
      ∑ F ∈ S, ∑ G ∈ S, familyTerm β t F ω * familyTerm β t G ω := by
    rw [hsum, pow_two]
    exact Finset.sum_mul_sum S S (fun F => familyTerm β t F ω)
      (fun G => familyTerm β t G ω)
  have hint (F G : Finset (ℕ × ℕ)) (hF : F ∈ S) (hG : G ∈ S) :
      Integrable (fun ω => familyTerm β t F ω * familyTerm β t G ω)
        (disorderLaw.restrict (blockGoodSet β t r s)) :=
    integrable_familyTerm_mul_on_goodSet β t ht F G
      (Finset.mem_of_mem_erase hF) (Finset.mem_of_mem_erase hG)
  calc
    ∫ ω in blockGoodSet β t r s, (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw =
        ∫ ω in blockGoodSet β t r s,
          ∑ F ∈ S, ∑ G ∈ S, familyTerm β t F ω * familyTerm β t G ω ∂disorderLaw :=
      integral_congr_ae (Filter.Eventually.of_forall hsq)
    _ = ∑ F ∈ S, ∑ G ∈ S,
          ∫ ω in blockGoodSet β t r s,
            familyTerm β t F ω * familyTerm β t G ω ∂disorderLaw := by
      rw [integral_finsetSum _ (fun F hF => integrable_finsetSum _ (fun G hG => hint F G hF hG))]
      apply Finset.sum_congr rfl
      intro F hF
      rw [integral_finsetSum _ (fun G hG => hint F G hF hG)]

end

end Critical2DKPZ.OnePoint

end
