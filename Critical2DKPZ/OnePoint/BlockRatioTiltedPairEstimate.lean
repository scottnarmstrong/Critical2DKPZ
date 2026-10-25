/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioTiltedFactorization
public import Critical2DKPZ.OnePoint.BlockRatioPairEstimate
import Critical2DKPZ.OnePoint.BlockRatioInverseExpectation
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! # Tilted component pair estimates -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private theorem coefficient_mul_pow_le_pow_tilted {D a α β : ℝ} {n : ℕ}
    (hD : 1 ≤ D) (ha : a ≤ D) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : 0 ≤ β) (hn : 1 ≤ n) :
    a * α ^ n ≤ (D * β) ^ n := by
  have hpow : α ^ n ≤ β ^ n := pow_le_pow_left₀ hα hαβ n
  have hDn : D ≤ D ^ n := by
    calc
      D = 1 * D := by ring
      _ ≤ D ^ (n - 1) * D :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hD) (by linarith)
      _ = D ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
  calc
    a * α ^ n ≤ D * α ^ n :=
      mul_le_mul_of_nonneg_right ha (pow_nonneg hα _)
    _ ≤ D * β ^ n :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    _ ≤ D ^ n * β ^ n :=
      mul_le_mul_of_nonneg_right hDn (pow_nonneg hβ _)
    _ = (D * β) ^ n := by rw [mul_pow]

/-- On an isolated component, weighting the truncated corrector by the raw inverse masses
produces the squared truncated-inverse product. -/
theorem pairWeightedComponent_eq_closedDiscrepancy_mul_inverseSq_of_isolated
    {r s : ℕ} (β : ℝ) (t : ℕ → ℕ) (hr : 1 ≤ r)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) {c : ℕ × ℕ}
    (hc : c ∈ pairComponents r s F G)
    (hisolated : IsIsolatedComponent F G c) (ω : Disorder) :
    pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩) ω =
      closedDiscrepancy β t c.1 c.2 ω *
        ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω ^ 2 := by
  classical
  change pairComponentFactor β t F G c ω *
      (∏ i ∈ Finset.Icc c.1 c.2, (blockMass β t i ω)⁻¹) = _
  rw [pairComponentFactor_eq_corrector_of_isolated β t hr hF hG hc hisolated ω,
    truncatedCorrector]
  have hprod :
      (∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω) *
          ∏ i ∈ Finset.Icc c.1 c.2, (blockMass β t i ω)⁻¹ =
        ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [truncatedInverse]
    split_ifs <;> ring
  rw [mul_assoc, hprod]

/-- A good-block indicator times the raw inverse mass is bounded by two. -/
theorem abs_pairGoodBlockFactor_mul_invBlockMass_le_two
    (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (ω : Disorder) :
    |pairGoodBlockFactor β t i ω * (blockMass β t i ω)⁻¹| ≤ 2 := by
  change |(if |blockMass β t i ω - 1| ≤ 1 / 2 then (1 : ℝ) else 0) *
      (blockMass β t i ω)⁻¹| ≤ 2
  split_ifs with hgood
  · have hpos := blockMass_pos β t i ω
    have hlow : 1 / 2 ≤ blockMass β t i ω := by
      rw [abs_le] at hgood
      linarith
    have hinv : (blockMass β t i ω)⁻¹ ≤ 2 := by
      exact (inv_le_iff_one_le_mul₀' hpos).2 (by nlinarith)
    rw [one_mul, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    exact hinv
  · simp

/-- A weighted factor on one uncovered block is integrable. -/
theorem integrable_pairWeightedUncoveredFactor (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Integrable (fun ω => pairGoodBlockFactor β t i ω * (blockMass β t i ω)⁻¹)
      disorderLaw := by
  have hmeas : Measurable (fun ω =>
      pairGoodBlockFactor β t i ω * (blockMass β t i ω)⁻¹) := by
    exact ((measurable_goodBlockIndicator β t i).mono
      (Gaussian.disorderBlock_le _ _) le_rfl).mul
        ((measurable_blockMass β t i).mono
          (Gaussian.disorderBlock_le _ _) le_rfl |>.inv)
  have hbound : ∀ ω, ‖pairGoodBlockFactor β t i ω *
      (blockMass β t i ω)⁻¹‖ ≤ 2 := by
    intro ω
    rw [Real.norm_eq_abs]
    exact abs_pairGoodBlockFactor_mul_invBlockMass_le_two β t i ω
  have hmajor : Integrable (fun _ : Disorder => (2 : ℝ)) disorderLaw :=
    integrable_const 2
  exact hmajor.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- A non-isolated weighted component is integrable and its absolute mean is bounded by the component weight with inverse-square endpoint-distance dependence. -/
theorem pairWeightedComponent_abs_integral_le_of_nonisolated {r s K : ℕ}
    (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKs : s < K) (hr : 1 ≤ r)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) {c : ℕ × ℕ}
    (hc : c ∈ pairComponents r s F G)
    (hNotIso : ¬ IsIsolatedComponent F G c)
    (hSq : ∀ I ∈ restrictIntervalFamily F c ∪ restrictIntervalFamily G c,
      ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
        (γ ^ (I.2 - I.1) / ((K : ℝ) - c.2)) ^ 2) :
    Integrable
        (pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩)) disorderLaw ∧
      |∫ ω, pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩) ω ∂disorderLaw| ≤
        componentWeight (4 * γ) K F G c := by
  classical
  let Fc := restrictIntervalFamily F c
  let Gc := restrictIntervalFamily G c
  let U : Disorder → ℝ := fun ω =>
    ∏ I ∈ Fc, truncatedCorrector β t I.1 I.2 ω
  let V : Disorder → ℝ := fun ω =>
    ∏ I ∈ Gc, truncatedCorrector β t I.1 I.2 ω
  let J : Disorder → ℝ := fun ω =>
    ∏ i ∈ Finset.Icc c.1 c.2,
      pairGoodBlockFactor β t i ω * (blockMass β t i ω)⁻¹
  let W : Disorder → ℝ := pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩)
  let L : ℕ := c.2 - c.1
  let B : ℝ := 2 ^ (L + 1)
  let d : ℝ := (K : ℝ) - c.2
  have hc' := Finset.mem_filter.mp hc
  have hcspan := Finset.mem_product.mp hc'.1
  have hstop := Finset.mem_Icc.mp hcspan.2
  have hLpos : 1 ≤ L := by dsimp [L]; omega
  have hdpos : 0 < d := by
    dsimp [d]
    have hnat : c.2 < K := lt_of_le_of_lt hstop.2 hKs
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hPair := pairComponent_correctorProduct_abs_mul_integral_le_of
    β t ht γ hγ0 hγ1 hKs hr hF hG hc hNotIso hSq
  have hrepr (ω : Disorder) : W ω = U ω * V ω * J ω := by
    change pairComponentFactor β t F G c ω *
        (∏ i ∈ Finset.Icc c.1 c.2, (blockMass β t i ω)⁻¹) = _
    simp only [pairComponentFactor]
    dsimp [U, V, J, Fc, Gc]
    calc
      _ =
          (∏ I ∈ restrictIntervalFamily F c,
            truncatedCorrector β t I.1 I.2 ω) *
            (∏ I ∈ restrictIntervalFamily G c,
              truncatedCorrector β t I.1 I.2 ω) *
            ((∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω) *
              ∏ i ∈ Finset.Icc c.1 c.2, (blockMass β t i ω)⁻¹) := by ring
      _ = _ := by rw [← Finset.prod_mul_distrib]
  have hJbound (ω : Disorder) : |J ω| ≤ B := by
    have hterm (i : ℕ) (hi : i ∈ Finset.Icc c.1 c.2) :
        |pairGoodBlockFactor β t i ω * (blockMass β t i ω)⁻¹| ≤ 2 :=
      abs_pairGoodBlockFactor_mul_invBlockMass_le_two β t i ω
    change |∏ i ∈ Finset.Icc c.1 c.2,
      pairGoodBlockFactor β t i ω * (blockMass β t i ω)⁻¹| ≤ B
    rw [Finset.abs_prod]
    have hcard : (Finset.Icc c.1 c.2).card = c.2 - c.1 + 1 := by
      simp only [Nat.card_Icc]
      omega
    calc
      ∏ i ∈ Finset.Icc c.1 c.2,
          |pairGoodBlockFactor β t i ω * (blockMass β t i ω)⁻¹| ≤
        ∏ _i ∈ Finset.Icc c.1 c.2, (2 : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact abs_nonneg _
          · intro i hi
            exact hterm i hi
      _ = B := by simp [B, L, hcard]
  have hWmeas : Measurable W := by
    exact (measurable_pairWeightedFactorValue_block β t ht hF hG
      (Sum.inl ⟨c, hc⟩)).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hBnonneg : 0 ≤ B := by positivity
  have hmajor : Integrable (fun ω => B * (|U ω| * |V ω|)) disorderLaw :=
    hPair.1.const_mul B
  have hpoint (ω : Disorder) : ‖W ω‖ ≤ B * (|U ω| * |V ω|) := by
    rw [Real.norm_eq_abs, hrepr, abs_mul, abs_mul]
    calc
      |U ω| * |V ω| * |J ω| ≤ |U ω| * |V ω| * B :=
        mul_le_mul_of_nonneg_left (hJbound ω)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = B * (|U ω| * |V ω|) := by ring
  have hpointAbs (ω : Disorder) : |W ω| ≤ B * (|U ω| * |V ω|) := by
    simpa [Real.norm_eq_abs] using hpoint ω
  have hWint : Integrable W disorderLaw :=
    hmajor.mono' hWmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall hpoint)
  have hIntegralAbs :
      |∫ ω, W ω ∂disorderLaw| ≤ B *
        ∫ ω, |U ω| * |V ω| ∂disorderLaw := by
    calc
      |∫ ω, W ω ∂disorderLaw| ≤ ∫ ω, |W ω| ∂disorderLaw :=
        abs_integral_le_integral_abs
      _ ≤ ∫ ω, B * (|U ω| * |V ω|) ∂disorderLaw :=
        integral_mono hWint.abs hmajor (fun ω => hpointAbs ω)
      _ = B * ∫ ω, |U ω| * |V ω| ∂disorderLaw := integral_const_mul _ _
  have hPairBound :
      ∫ ω, |U ω| * |V ω| ∂disorderLaw ≤ γ ^ L / d ^ 2 := by
    simpa [U, V, Fc, Gc, L, d] using hPair.2
  have hpowTwo : (2 : ℝ) ^ (L + 1) ≤ 4 ^ L := by
    rw [pow_succ]
    have htwo : (2 : ℝ) ≤ 2 ^ L := by
      simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hLpos)
    calc
      2 ^ L * 2 ≤ 2 ^ L * 2 ^ L :=
        mul_le_mul_of_nonneg_left htwo (pow_nonneg (by norm_num) _)
      _ = 4 ^ L := by rw [← mul_pow]; norm_num
  have hnum : B * γ ^ L ≤ (4 * γ) ^ L := by
    dsimp [B]
    calc
      2 ^ (L + 1) * γ ^ L ≤ 4 ^ L * γ ^ L :=
        mul_le_mul_of_nonneg_right hpowTwo (pow_nonneg hγ0 _)
      _ = (4 * γ) ^ L := by rw [← mul_pow]
  have hbound :
      |∫ ω, W ω ∂disorderLaw| ≤ (4 * γ) ^ L / d ^ 2 := by
    calc
      |∫ ω, W ω ∂disorderLaw| ≤ B *
          ∫ ω, |U ω| * |V ω| ∂disorderLaw := hIntegralAbs
      _ ≤ B * (γ ^ L / d ^ 2) :=
        mul_le_mul_of_nonneg_left hPairBound hBnonneg
      _ = (B * γ ^ L) / d ^ 2 := by ring
      _ ≤ (4 * γ) ^ L / d ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg d)
  have hWeight : componentWeight (4 * γ) K F G c = (4 * γ) ^ L / d ^ 2 := by
    unfold componentWeight
    simp [hNotIso, L, d, Real.rpow_neg (le_of_lt hdpos), div_eq_mul_inv]
  exact ⟨hWint, by rw [hWeight]; simpa [W, L, d] using hbound⟩

/-- An isolated weighted component is integrable and has its first-power component bound. -/
theorem pairWeightedComponent_abs_integral_le_of_isolated {r s K : ℕ}
    (β : ℝ) (t : ℕ → ℕ) (hr : 1 ≤ r)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) {c : ℕ × ℕ}
    (hc : c ∈ pairComponents r s F G)
    (hisolated : IsIsolatedComponent F G c) (hKs : s < K) (γ : ℝ)
    (hMean : |∫ ω, closedDiscrepancy β t c.1 c.2 ω *
        ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω ^ 2 ∂disorderLaw| ≤
      γ ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2)) :
    Integrable
        (pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩)) disorderLaw ∧
      |∫ ω, pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩) ω ∂disorderLaw| ≤
        componentWeight γ K F G c := by
  classical
  let W : Disorder → ℝ := pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩)
  let L : ℕ := c.2 - c.1
  let d : ℝ := (K : ℝ) - c.2
  have hc' := Finset.mem_filter.mp hc
  have hcspan := Finset.mem_product.mp hc'.1
  have hstop := Finset.mem_Icc.mp hcspan.2
  have hdpos : 0 < d := by
    dsimp [d]
    have hnat : c.2 < K := lt_of_le_of_lt hstop.2 hKs
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have heq (ω : Disorder) : W ω =
      closedDiscrepancy β t c.1 c.2 ω *
        ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω ^ 2 := by
    exact pairWeightedComponent_eq_closedDiscrepancy_mul_inverseSq_of_isolated
      β t hr hF hG hc hisolated ω
  have hWint : Integrable W disorderLaw := by
    apply (integrable_closedDiscrepancy_mul_truncatedInverse_sq_prod β t c.1 c.2).congr
    filter_upwards [] with ω
    exact (heq ω).symm
  have hIntEq :
      ∫ ω, W ω ∂disorderLaw =
        ∫ ω, closedDiscrepancy β t c.1 c.2 ω *
          ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω ^ 2 ∂disorderLaw := by
    apply integral_congr_ae
    filter_upwards [] with ω
    exact heq ω
  have hWeight : componentWeight γ K F G c = γ ^ L / d ^ ((3 : ℝ) / 2) := by
    unfold componentWeight
    simp [hisolated, L, d, Real.rpow_neg (le_of_lt hdpos), div_eq_mul_inv]
  have hboundW : |∫ ω, W ω ∂disorderLaw| ≤ componentWeight γ K F G c := by
    rw [hWeight, hIntEq]
    simpa [L, d] using hMean
  exact ⟨hWint, by simpa [W] using hboundW⟩

/-- The tilted good-set pair integral is bounded by the product of its component weights. The
integrability companion for the good-set integrand is
`integrableOn_familyTermPair_mul_invBlockProduct`. -/
theorem abs_tilted_setIntegral_familyTerm_mul_le (A : ℝ) :
    ∃ C₀ ρ₀ C : ℝ, 0 < C₀ ∧ 1 < ρ₀ ∧ 1 ≤ C ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ,
        1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
        ∀ F ∈ intervalFamilies r s, ∀ G ∈ intervalFamilies r s,
          |∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
            familyTerm (criticalBeta ϑ N) (blockTime N ρ) F ω *
              familyTerm (criticalBeta ϑ N) (blockTime N ρ) G ω *
              ∏ i ∈ Finset.Icc r s,
                (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw| /
          (∫ ω, ∏ i ∈ Finset.Icc r s,
            (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
          ∏ c ∈ pairComponents r s F G,
            componentWeight (C * C₀ / Real.sqrt (Real.log ρ))
              (blockCount N ρ) F G c := by
  classical
  obtain ⟨Cs₀, ρs, Cs, hCs₀, hρs, hSq⟩ := integral_truncatedCorrector_sq_le A
  obtain ⟨Ct₀, ρt, Ct, hCt₀, hρt, hTiltMean⟩ :=
    abs_integral_closedDiscrepancy_mul_truncatedInverse_sq_prod_le A
  let C₀ : ℝ := max Cs₀ Ct₀
  let Dsq : ℝ := max 1 |Cs|
  let Dtilt : ℝ := max 1 |Ct|
  let C : ℝ := max 1 (max (4 * Dsq) Dtilt)
  let ρ₀ : ℝ := max ρs (max ρt (Real.exp ((C * C₀) ^ 2) + 1))
  have hC₀pos : 0 < C₀ := by
    dsimp [C₀]
    exact lt_of_lt_of_le hCs₀ (le_max_left _ _)
  have hDsq1 : 1 ≤ Dsq := by dsimp [Dsq]; exact le_max_left _ _
  have hDtilt1 : 1 ≤ Dtilt := by dsimp [Dtilt]; exact le_max_left _ _
  have hCsDsq : |Cs| ≤ Dsq := by dsimp [Dsq]; exact le_max_right _ _
  have hCtDtilt : |Ct| ≤ Dtilt := by dsimp [Dtilt]; exact le_max_right _ _
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_max_left _ _
  have hC4Dsq : 4 * Dsq ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCDtilt : Dtilt ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hC₀s : Cs₀ ≤ C₀ := le_max_left _ _
  have hC₀t : Ct₀ ≤ C₀ := le_max_right _ _
  have hρ₀ : 1 < ρ₀ := by
    dsimp [ρ₀]
    exact lt_of_lt_of_le hρs (le_max_left _ _)
  refine ⟨C₀, ρ₀, C, hC₀pos, hρ₀, hC1, ?_⟩
  intro ρ hρ
  have hρsρ : ρs ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρinner : max ρt (Real.exp ((C * C₀) ^ 2) + 1) ≤ ρ :=
    le_trans (le_max_right _ _) hρ
  have hρtρ : ρt ≤ ρ := le_trans (le_max_left _ _) hρinner
  have hexpPlus : Real.exp ((C * C₀) ^ 2) + 1 ≤ ρ :=
    le_trans (le_max_right _ _) hρinner
  have hexp : Real.exp ((C * C₀) ^ 2) < ρ := by linarith
  have hlog : (C * C₀) ^ 2 < Real.log ρ := by
    calc
      (C * C₀) ^ 2 = Real.log (Real.exp ((C * C₀) ^ 2)) := by rw [Real.log_exp]
      _ < Real.log ρ := Real.log_lt_log (Real.exp_pos _) hexp
  have hlogpos : 0 < Real.log ρ := by nlinarith [sq_nonneg (C * C₀)]
  have hsqrtpos : 0 < Real.sqrt (Real.log ρ) := Real.sqrt_pos.2 hlogpos
  have hsqrtCmp : C * C₀ ≤ Real.sqrt (Real.log ρ) := by
    have hsq := Real.sq_sqrt (le_of_lt hlogpos)
    nlinarith [sq_nonneg (C * C₀)]
  have hNclock : ∀ᶠ N : ℕ in atTop,
      ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N := Filter.eventually_ge_atTop _
  filter_upwards [hSq ρ hρsρ, hTiltMean ρ hρtρ, hNclock]
    with N hSqN hTiltMeanN hNclock
  intro ϑ hϑ r s hr hrs hsK F hF G hG
  let β : ℝ := criticalBeta ϑ N
  let t : ℕ → ℕ := blockTime N ρ
  let K : ℕ := blockCount N ρ
  let γ : ℝ := C * C₀ / Real.sqrt (Real.log ρ)
  let αS : ℝ := Cs₀ / Real.sqrt (Real.log ρ)
  let αT : ℝ := Ct₀ / Real.sqrt (Real.log ρ)
  let α₀ : ℝ := C₀ / Real.sqrt (Real.log ρ)
  let γS : ℝ := Dsq * αS
  have hαS0 : 0 ≤ αS := by dsimp [αS]; positivity
  have hαT0 : 0 ≤ αT := by dsimp [αT]; positivity
  have hα₀0 : 0 ≤ α₀ := by dsimp [α₀]; positivity
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hγS0 : 0 ≤ γS := by dsimp [γS]; positivity
  have hγ1 : γ ≤ 1 := by
    dsimp [γ]
    calc
      C * C₀ / Real.sqrt (Real.log ρ) ≤
          Real.sqrt (Real.log ρ) / Real.sqrt (Real.log ρ) :=
        div_le_div_of_nonneg_right hsqrtCmp hsqrtpos.le
      _ = 1 := div_self hsqrtpos.ne'
  have hαSα₀ : αS ≤ α₀ := by
    dsimp [αS, α₀]
    exact div_le_div_of_nonneg_right hC₀s hsqrtpos.le
  have hαTα₀ : αT ≤ α₀ := by
    dsimp [αT, α₀]
    exact div_le_div_of_nonneg_right hC₀t hsqrtpos.le
  have hγS4 : 4 * γS ≤ γ := by
    have hmul : (4 * Dsq) * Cs₀ ≤ C * C₀ :=
      mul_le_mul hC4Dsq hC₀s (by positivity) (by positivity)
    have hmulDiv : ((4 * Dsq) * Cs₀) / Real.sqrt (Real.log ρ) ≤
        (C * C₀) / Real.sqrt (Real.log ρ) :=
      div_le_div_of_nonneg_right hmul hsqrtpos.le
    calc
      4 * γS = ((4 * Dsq) * Cs₀) / Real.sqrt (Real.log ρ) := by
        simp [γS, αS]
        ring
      _ ≤ (C * C₀) / Real.sqrt (Real.log ρ) := hmulDiv
      _ = γ := rfl
  have hγS1 : γS ≤ 1 := by
    nlinarith [hγS4, hγ1]
  have ht : Monotone t := by
    exact Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon
      hρ₀ hρ hNclock
  have hsK : s < K := by dsimp [K]; omega
  have hSqComponent {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G)
      (I : ℕ × ℕ) (hI : I ∈ restrictIntervalFamily F c ∪ restrictIntervalFamily G c) :
      ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
        (γS ^ (I.2 - I.1) / ((K : ℝ) - c.2)) ^ 2 := by
    have hc' := Finset.mem_filter.mp hc
    have hcspan := Finset.mem_product.mp hc'.1
    have hstop := Finset.mem_Icc.mp hcspan.2
    have hIcontained : c.1 ≤ I.1 ∧ I.2 ≤ c.2 := by
      rcases Finset.mem_union.mp hI with hIF | hIG
      · exact (Finset.mem_filter.mp hIF).2
      · exact (Finset.mem_filter.mp hIG).2
    have hIvalid : 1 ≤ I.1 ∧ I.1 < I.2 ∧ I.2 + 1 ≤ blockCount N ρ := by
      rcases Finset.mem_union.mp hI with hIF | hIG
      · have hB := (intervalFamilies_mem_iff r s F).mp hF |>.1 I
          (Finset.mem_filter.mp hIF).1
        exact ⟨by omega, hB.2.2.2.2, by omega⟩
      · have hB := (intervalFamilies_mem_iff r s G).mp hG |>.1 I
          (Finset.mem_filter.mp hIG).1
        exact ⟨by omega, hB.2.2.2.2, by omega⟩
    let ℓ : ℕ := I.2 - I.1
    have hraw := hSqN ϑ hϑ I.1 I.2 hIvalid.1 hIvalid.2.1 hIvalid.2.2
    have hlen : 1 ≤ ℓ := by dsimp [ℓ]; omega
    have hcoeff := coefficient_mul_pow_le_pow_tilted hDsq1 hCsDsq hαS0
      le_rfl hαS0 hlen
    have hnum : (Cs * αS ^ ℓ) ^ 2 ≤ (γS ^ ℓ) ^ 2 := by
      calc
        (Cs * αS ^ ℓ) ^ 2 = (|Cs| * αS ^ ℓ) ^ 2 := by
          rw [← sq_abs, abs_mul, abs_of_nonneg (pow_nonneg hαS0 _)]
        _ ≤ (γS ^ ℓ) ^ 2 :=
          (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (pow_nonneg hαS0 _))
            (pow_nonneg hγS0 _)).2 hcoeff
    have hI1cast : (I.1 : ℝ) ≤ (c.2 : ℝ) := by
      have hnat : I.1 ≤ c.2 := le_trans (Nat.le_of_lt hIvalid.2.1) hIcontained.2
      exact_mod_cast hnat
    have hI2cast : (I.2 : ℝ) ≤ (c.2 : ℝ) := by exact_mod_cast hIcontained.2
    have hdpos : 0 < (K : ℝ) - c.2 := by
      have hnat : c.2 < K := by dsimp [K]; omega
      exact sub_pos.mpr (by exact_mod_cast hnat)
    have hdenI1 : 0 < (K : ℝ) - I.1 := by
      have hnat : I.1 < K := by dsimp [K]; omega
      exact sub_pos.mpr (by exact_mod_cast hnat)
    have hdenI2 : 0 < (K : ℝ) - I.2 := by
      have hnat : I.2 < K := by dsimp [K]; omega
      exact sub_pos.mpr (by exact_mod_cast hnat)
    have hdenCmp : ((K : ℝ) - c.2) ^ 2 ≤
        ((K : ℝ) - I.1) * ((K : ℝ) - I.2) := by
      have hle1 : (K : ℝ) - c.2 ≤ (K : ℝ) - I.1 := by linarith
      have hle2 : (K : ℝ) - c.2 ≤ (K : ℝ) - I.2 := by linarith
      calc
        ((K : ℝ) - c.2) ^ 2 = ((K : ℝ) - c.2) * ((K : ℝ) - c.2) := by ring
        _ ≤ ((K : ℝ) - I.1) * ((K : ℝ) - I.2) :=
          mul_le_mul hle1 hle2 (le_of_lt hdpos) (le_of_lt hdenI1)
    have hraw' : ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
        (Cs * αS ^ ℓ) ^ 2 /
          (((K : ℝ) - I.1) * ((K : ℝ) - I.2)) := by
      simpa [β, t, K, αS] using hraw
    calc
      ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
          (Cs * αS ^ ℓ) ^ 2 /
            (((K : ℝ) - I.1) * ((K : ℝ) - I.2)) := hraw'
      _ ≤ (γS ^ ℓ) ^ 2 /
            (((K : ℝ) - I.1) * ((K : ℝ) - I.2)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (γS ^ ℓ) ^ 2 / ((K : ℝ) - c.2) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hdenCmp
      _ = (γS ^ (I.2 - I.1) / ((K : ℝ) - c.2)) ^ 2 := by
          dsimp [ℓ]
          rw [← div_pow]
  have hMeanComponent {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G) :
      |∫ ω, closedDiscrepancy β t c.1 c.2 ω *
          ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω ^ 2 ∂disorderLaw| ≤
        γ ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
    have hc' := Finset.mem_filter.mp hc
    have hcspan := Finset.mem_product.mp hc'.1
    have hstart := Finset.mem_Icc.mp hcspan.1
    have hstop := Finset.mem_Icc.mp hcspan.2
    have hstrict : c.1 < c.2 := hc'.2.1
    have hraw := hTiltMeanN ϑ hϑ c.1 c.2 (by omega) hstrict (by omega)
    let ℓ : ℕ := c.2 - c.1
    have hlen : 1 ≤ ℓ := by dsimp [ℓ]; omega
    have hcoeff := coefficient_mul_pow_le_pow_tilted hDtilt1 hCtDtilt hαT0
      hαTα₀ (by positivity) hlen
    have hbase : Dtilt * α₀ ≤ γ := by
      have hmul : Dtilt * C₀ ≤ C * C₀ :=
        mul_le_mul_of_nonneg_right hCDtilt (le_of_lt hC₀pos)
      have hmulDiv : Dtilt * C₀ / Real.sqrt (Real.log ρ) ≤
          C * C₀ / Real.sqrt (Real.log ρ) :=
        div_le_div_of_nonneg_right hmul hsqrtpos.le
      calc
        Dtilt * α₀ = Dtilt * C₀ / Real.sqrt (Real.log ρ) := by
          dsimp [α₀]
          ring
        _ ≤ C * C₀ / Real.sqrt (Real.log ρ) := hmulDiv
        _ = γ := rfl
    have hcoeff' : |Ct| * αT ^ ℓ ≤ γ ^ ℓ := by
      calc
        |Ct| * αT ^ ℓ ≤ (Dtilt * α₀) ^ ℓ := hcoeff
        _ ≤ γ ^ ℓ := pow_le_pow_left₀ (by positivity) hbase ℓ
    have hraw' :
        |∫ ω, closedDiscrepancy β t c.1 c.2 ω *
            ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω ^ 2 ∂disorderLaw| ≤
          |Ct| * αT ^ ℓ / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
      have hraw₀ :
          |∫ ω, closedDiscrepancy β t c.1 c.2 ω *
              ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω ^ 2 ∂disorderLaw| ≤
            Ct * αT ^ ℓ / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
        simpa [β, t, K, αT, ℓ] using hraw
      have hdenpos : 0 < ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
        apply Real.rpow_pos_of_pos
        have hnat : c.2 < K := by dsimp [K]; omega
        exact sub_pos.mpr (by exact_mod_cast hnat)
      exact hraw₀.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self Ct) (pow_nonneg hαT0 _)) hdenpos.le)
    have hdenpos : 0 < ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
      apply Real.rpow_pos_of_pos
      have hnat : c.2 < K := by dsimp [K]; omega
      exact sub_pos.mpr (by exact_mod_cast hnat)
    calc
      _ ≤ |Ct| * αT ^ ℓ / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := hraw'
      _ ≤ γ ^ ℓ / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) :=
        div_le_div_of_nonneg_right hcoeff' hdenpos.le
      _ = γ ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
        simp [ℓ]
  have hComponentBound {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G) :
      Integrable (pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩)) disorderLaw ∧
        |∫ ω, pairWeightedFactorValue β t F G (Sum.inl ⟨c, hc⟩) ω ∂disorderLaw| ≤
          componentWeight γ K F G c := by
    by_cases hiso : IsIsolatedComponent F G c
    · exact pairWeightedComponent_abs_integral_le_of_isolated β t hr hF hG hc hiso hsK γ
        (hMeanComponent hc)
    · have hnon := pairWeightedComponent_abs_integral_le_of_nonisolated
        β t ht γS hγS0 hγS1 hsK hr hF hG hc hiso (hSqComponent hc)
      have hpow : (4 * γS) ^ (c.2 - c.1) ≤ γ ^ (c.2 - c.1) :=
        pow_le_pow_left₀ (by positivity) hγS4 _
      have hdpos : 0 < (K : ℝ) - c.2 := by
        have hc' := Finset.mem_filter.mp hc
        have hcspan := Finset.mem_product.mp hc'.1
        have hstop := Finset.mem_Icc.mp hcspan.2
        have hnat : c.2 < K := lt_of_le_of_lt hstop.2 hsK
        exact sub_pos.mpr (by exact_mod_cast hnat)
      have hweightA : componentWeight (4 * γS) K F G c =
          (4 * γS) ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ 2 := by
        unfold componentWeight
        simp [hiso, Real.rpow_neg (le_of_lt hdpos), div_eq_mul_inv]
      have hweightB : componentWeight γ K F G c =
          γ ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ 2 := by
        unfold componentWeight
        simp [hiso, Real.rpow_neg (le_of_lt hdpos), div_eq_mul_inv]
      refine ⟨hnon.1, ?_⟩
      rw [hweightA] at hnon
      rw [hweightB]
      exact hnon.2.trans (div_le_div_of_nonneg_right hpow (sq_nonneg _))
  let num : pairFactorIndex r s F G → ℝ := fun x =>
    ∫ ω, pairWeightedFactorValue β t F G x ω ∂disorderLaw
  let denFactor : pairFactorIndex r s F G → ℝ := fun x =>
    ∫ ω, pairFactorInverseProduct β t F G x ω ∂disorderLaw
  let weightFactor : pairFactorIndex r s F G → ℝ := fun x =>
    match x with
    | Sum.inl c => componentWeight γ K F G c.1
    | Sum.inr _ => 1
  have hInt : ∀ x : pairFactorIndex r s F G,
      Integrable (pairWeightedFactorValue β t F G x) disorderLaw := by
    intro x
    cases x with
    | inl c =>
        exact (hComponentBound (c := c.1) c.2).1
    | inr i =>
        change Integrable (fun ω => pairGoodBlockFactor β t i.1 ω *
          (blockMass β t i.1 ω)⁻¹) disorderLaw
        exact integrable_pairWeightedUncoveredFactor β t i.1
  have hInvInt : ∀ x : pairFactorIndex r s F G,
      Integrable (pairFactorInverseProduct β t F G x) disorderLaw := by
    intro x
    cases x with
    | inl c =>
        change Integrable (fun ω =>
          ∏ i ∈ Finset.Icc c.1.1 c.1.2, (blockMass β t i ω)⁻¹) disorderLaw
        exact integrable_prod_inv_blockMass β t (Finset.Icc c.1.1 c.1.2)
    | inr i =>
        change Integrable (fun ω => (blockMass β t i.1 ω)⁻¹) disorderLaw
        simpa using integrable_prod_inv_blockMass β t ({i.1} : Finset ℕ)
  have hNumEq :
      ∫ ω in blockGoodSet β t r s,
        familyTerm β t F ω * familyTerm β t G ω *
          ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw =
        ∏ x : pairFactorIndex r s F G, num x := by
    simpa [num] using setIntegral_familyTermPair_mul_invBlockProduct_eq_pairWeightedIntegrals
      β t ht hr hF hG hInt
  have hDenEq :
      ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw =
        ∏ x : pairFactorIndex r s F G, denFactor x := by
    calc
      ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw =
          ∫ ω, ∏ x : pairFactorIndex r s F G,
            pairFactorInverseProduct β t F G x ω ∂disorderLaw := by
              apply integral_congr_ae
              filter_upwards [] with ω
              exact (pairFactorInverseProduct_prod_eq_global β t F G ω).symm
      _ = ∏ x : pairFactorIndex r s F G, denFactor x := by
        simpa [denFactor] using integral_pairFactorInverseProduct_prod_eq_prod_integral
          β t ht hInvInt
  have hLocalDenOne (x : pairFactorIndex r s F G) : 1 ≤ denFactor x := by
    cases x with
    | inl c =>
        change 1 ≤ ∫ ω,
          ∏ i ∈ Finset.Icc c.1.1 c.1.2, (blockMass β t i ω)⁻¹ ∂disorderLaw
        let S := Finset.Icc c.1.1 c.1.2
        have hc' := Finset.mem_filter.mp c.2
        have hcspan := Finset.mem_product.mp hc'.1
        have hcstart := Finset.mem_Icc.mp hcspan.1
        have hSpos : ∀ i ∈ S, 1 ≤ i := by
          intro i hi
          have hi' := Finset.mem_Icc.mp hi
          omega
        rw [integral_finset_prod_inv_blockMass β t ht S hSpos]
        have hm (i : ℕ) (hi : i ∈ S) :
            1 ≤ ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw :=
          one_le_integral_inv_blockMass β t i
        calc
          1 = ∏ i ∈ S, (1 : ℝ) := by simp
          _ ≤ ∏ i ∈ S, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
            apply Finset.prod_le_prod₀
            · intro i hi
              norm_num
            · intro i hi
              exact hm i hi
    | inr i =>
        change 1 ≤ ∫ ω, (blockMass β t i.1 ω)⁻¹ ∂disorderLaw
        exact one_le_integral_inv_blockMass β t i.1
  have hLocalDenPos (x : pairFactorIndex r s F G) : 0 < denFactor x :=
    lt_of_lt_of_le zero_lt_one (hLocalDenOne x)
  have hDenPos :
      0 < ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    rw [hDenEq]
    exact Finset.prod_pos fun x hx => hLocalDenPos x
  have hWeightNonneg (x : pairFactorIndex r s F G) : 0 ≤ weightFactor x := by
    cases x with
    | inl c =>
        dsimp [weightFactor]
        unfold componentWeight
        apply mul_nonneg
        · exact pow_nonneg hγ0 _
        · have hc' := Finset.mem_filter.mp c.2
          have hcspan := Finset.mem_product.mp hc'.1
          have hcend := Finset.mem_Icc.mp hcspan.2
          have hnat : c.1.2 ≤ K := by dsimp [K]; omega
          exact Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hnat)) _
    | inr i => simp [weightFactor]
  have hNumBound (x : pairFactorIndex r s F G) :
      |num x| ≤ weightFactor x * denFactor x := by
    cases x with
    | inl c =>
        have hcBound := hComponentBound (c := c.1) c.2
        calc
          |num (Sum.inl c)| ≤ componentWeight γ K F G c.1 := by
            simpa [num] using hcBound.2
          _ = componentWeight γ K F G c.1 * 1 := by ring
          _ ≤ componentWeight γ K F G c.1 * denFactor (Sum.inl c) := by
            have hw : 0 ≤ componentWeight γ K F G c.1 := by
              simpa [weightFactor] using hWeightNonneg (Sum.inl c)
            exact mul_le_mul_of_nonneg_left (hLocalDenOne (Sum.inl c)) hw
          _ = weightFactor (Sum.inl c) * denFactor (Sum.inl c) := by
            simp [weightFactor]
    | inr i =>
        have hterm (ω : Disorder) :
            0 ≤ pairGoodBlockFactor β t i.1 ω * (blockMass β t i.1 ω)⁻¹ ∧
            pairGoodBlockFactor β t i.1 ω * (blockMass β t i.1 ω)⁻¹ ≤
              (blockMass β t i.1 ω)⁻¹ := by
          have hgood : 0 ≤ pairGoodBlockFactor β t i.1 ω ∧
              pairGoodBlockFactor β t i.1 ω ≤ 1 := by
            unfold pairGoodBlockFactor
            split_ifs <;> norm_num
          have hinv : 0 ≤ (blockMass β t i.1 ω)⁻¹ :=
            inv_nonneg.mpr (le_of_lt (blockMass_pos β t i.1 ω))
          exact ⟨mul_nonneg hgood.1 hinv,
            by simpa only [one_mul] using mul_le_mul_of_nonneg_right hgood.2 hinv⟩
        have hnumNonneg : 0 ≤ num (Sum.inr i) := by
          apply integral_nonneg_of_ae
          filter_upwards [] with ω
          exact (hterm ω).1
        have hnumLe : num (Sum.inr i) ≤ denFactor (Sum.inr i) := by
          change (∫ ω, pairGoodBlockFactor β t i.1 ω *
              (blockMass β t i.1 ω)⁻¹ ∂disorderLaw) ≤
            ∫ ω, (blockMass β t i.1 ω)⁻¹ ∂disorderLaw
          exact integral_mono (hInt (Sum.inr i)) (hInvInt (Sum.inr i))
            (fun ω => (hterm ω).2)
        have habs : |num (Sum.inr i)| ≤ denFactor (Sum.inr i) := by
          rw [abs_of_nonneg hnumNonneg]
          exact hnumLe
        simpa [weightFactor] using habs
  have hWeightProd :
      (∏ x : pairFactorIndex r s F G, weightFactor x) =
        ∏ c ∈ pairComponents r s F G, componentWeight γ K F G c := by
    classical
    have hCattach (f : ℕ × ℕ → ℝ) :
        ∏ c : pairComponentIndex r s F G, f c.1 =
          ∏ c ∈ pairComponents r s F G, f c := by
      rw [Finset.univ_eq_attach, Finset.prod_attach]
    rw [Fintype.prod_sum_type]
    simp only [weightFactor]
    rw [hCattach]
    simp
  have hProdBound :
      (∏ x : pairFactorIndex r s F G, |num x|) ≤
        (∏ x : pairFactorIndex r s F G, weightFactor x) *
          ∏ x : pairFactorIndex r s F G, denFactor x := by
    calc
      ∏ x : pairFactorIndex r s F G, |num x| ≤
          ∏ x : pairFactorIndex r s F G, weightFactor x * denFactor x := by
        apply Finset.prod_le_prod₀
        · intro x hx
          exact abs_nonneg _
        · intro x hx
          exact hNumBound x
      _ = (∏ x : pairFactorIndex r s F G, weightFactor x) *
            ∏ x : pairFactorIndex r s F G, denFactor x :=
        Finset.prod_mul_distrib
  have hAbsNumEq :
      |∫ ω in blockGoodSet β t r s,
          familyTerm β t F ω * familyTerm β t G ω *
            ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw| =
        ∏ x : pairFactorIndex r s F G, |num x| := by
    rw [hNumEq, Finset.abs_prod]
  have hProductBound :
      |∫ ω in blockGoodSet β t r s,
          familyTerm β t F ω * familyTerm β t G ω *
            ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw| ≤
        (∏ c ∈ pairComponents r s F G, componentWeight γ K F G c) *
          ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    calc
      _ = ∏ x : pairFactorIndex r s F G, |num x| := hAbsNumEq
      _ ≤ (∏ x : pairFactorIndex r s F G, weightFactor x) *
            ∏ x : pairFactorIndex r s F G, denFactor x := hProdBound
      _ = (∏ c ∈ pairComponents r s F G, componentWeight γ K F G c) *
            ∫ ω, ∏ i ∈ Finset.Icc r s, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
        rw [hWeightProd, ← hDenEq]
  apply (div_le_iff₀ hDenPos).2
  simpa [β, t, K] using hProductBound

end Critical2DKPZ.OnePoint

end
