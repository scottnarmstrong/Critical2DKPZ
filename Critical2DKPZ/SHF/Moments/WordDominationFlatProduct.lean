/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationCutoff
public import Critical2DKPZ.SHF.Moments.WordDominationMarginalBound
public import Critical2DKPZ.SHF.Moments.WordDominationTestDomination
public import Critical2DKPZ.SHF.Limit.PolymerSixthMoment
public import Critical2DKPZ.SHF.Limit.FlatBound
public import Critical2DKPZ.SHF.Moments.PairingFubini
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Products of up to four compact pairings -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

private theorem integrable_compactPairing_productFlat (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (φ : C_c(Plane × Plane, ℝ)) :
    Integrable (fun ω =>
      ∫ p : Plane × Plane, φ p * rescaledP2P ϑ N s t p ω ∂volume) disorderLaw := by
  let G : (Plane × Plane) × Disorder → ℝ :=
    fun q => φ q.1 * rescaledP2P ϑ N s t q.1 q.2
  have hG : Integrable G (volume.prod disorderLaw) :=
    integrable_pairing_rescaledP2P ϑ N s t φ.continuous φ.hasCompactSupport
  have hGswap : Integrable (fun q : Disorder × (Plane × Plane) => G (q.2, q.1))
      (disorderLaw.prod volume) := hG.swap
  have hPair : AEStronglyMeasurable (fun ω : Disorder =>
      ∫ p : Plane × Plane, G (p, ω) ∂volume) disorderLaw := by
    simpa only [G, Prod.fst, Prod.snd] using
      hGswap.aestronglyMeasurable.integral_prod_right'
  have hUpper : Integrable (fun ω : Disorder =>
      ∫ p : Plane × Plane, ‖G (p, ω)‖ ∂volume) disorderLaw := by
    have h := (integrable_prod_iff hGswap.aestronglyMeasurable).mp hGswap
    simpa only [G, Prod.fst, Prod.snd] using h.2
  have hX : Integrable (fun ω : Disorder =>
      ∫ p : Plane × Plane, G (p, ω) ∂volume) disorderLaw := by
    apply hUpper.mono'
    · exact hPair
    · exact Filter.Eventually.of_forall fun ω => norm_integral_le_integral_norm _
  simpa only [G, Prod.fst, Prod.snd] using hX

private theorem flatMarginal_power_le_one_add_six (h : ℕ) (hh : h ≤ 4)
    (y : ℝ) (hy : 0 ≤ y) : y ^ h ≤ 1 + y ^ 6 := by
  by_cases hy1 : y ≤ 1
  · calc
      y ^ h ≤ 1 := pow_le_one₀ hy hy1
      _ ≤ 1 + y ^ 6 := le_add_of_nonneg_right (pow_nonneg hy 6)
  · have hy' : 1 ≤ y := le_of_not_ge hy1
    have hle : h ≤ 6 := by omega
    calc
      y ^ h ≤ y ^ 6 := pow_le_pow_right₀ hy' hle
      _ ≤ 1 + y ^ 6 := by linarith

/-- Products of up to four absolute compact pairings have a uniformly bounded
integrable disorder expectation on each compact positive-time window. -/
theorem eventually_integral_compactAbs_pairing_product_fin_le (ϑ : ℝ)
    {h : ℕ} (hh : h ≤ 4) (φ : Fin h → C_c(Plane × Plane, ℝ))
    {τ T : ℝ} (hτ : 0 < τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        Integrable (fun ω => ∏ i : Fin h,
          (∫ p : Plane × Plane,
            compactAbs (φ i) p * rescaledP2P ϑ N s t p ω ∂volume)) disorderLaw ∧
        ∫ ω, ∏ i : Fin h,
          (∫ p : Plane × Plane,
            compactAbs (φ i) p * rescaledP2P ϑ N s t p ω ∂volume)
          ∂disorderLaw ≤ B := by
  let Φ : C_c(Plane × Plane, ℝ) := ∑ i : Fin h, compactAbs (φ i)
  have hΦnonneg (p : Plane × Plane) : 0 ≤ Φ p := by
    dsimp only [Φ]
    rw [CompactlySupportedContinuousMap.sum_apply]
    apply Finset.sum_nonneg
    intro i hi
    change 0 ≤ |φ i p|
    positivity
  obtain ⟨M, χ, hM, hχ, hmajor⟩ :=
    exists_pairTest_firstCoordinate_majorant Φ
  obtain ⟨C₆, hC₆⟩ := SHF.Limit.polymerMeasure_flat_sixth_moment_le ϑ χ hτ
  let B : ℝ := M ^ h * (1 + max C₆ 0)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_⟩
  filter_upwards [hC₆] with N hN
  intro s t hs hst ht
  let Y : Disorder → ℝ := fun ω =>
    ∫ x, |χ x| ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst)
  let X : Fin h → Disorder → ℝ := fun i ω =>
    ∫ p : Plane × Plane,
      compactAbs (φ i) p * rescaledP2P ϑ N s t p ω ∂volume
  have hYnn (ω : Disorder) : 0 ≤ Y ω :=
    integral_nonneg (fun x => abs_nonneg (χ x))
  have hXnn (i : Fin h) (ω : Disorder) : 0 ≤ X i ω := by
    apply integral_nonneg
    intro p
    exact mul_nonneg
      (show 0 ≤ compactAbs (φ i) p by change 0 ≤ |φ i p|; positivity)
      (rescaledP2P_nonneg ϑ N s t p ω)
  have htermle (i : Fin h) (p : Plane × Plane) :
      |compactAbs (φ i) p| ≤ M * χ p.1 := by
    have hle : compactAbs (φ i) p ≤ Φ p := by
      dsimp only [Φ]
      rw [CompactlySupportedContinuousMap.sum_apply]
      exact Finset.single_le_sum
        (fun j hj => show 0 ≤ compactAbs (φ j) p by
          change 0 ≤ |φ j p|
          positivity)
        (Finset.mem_univ i)
    calc
      |compactAbs (φ i) p| = compactAbs (φ i) p :=
        abs_of_nonneg (show 0 ≤ compactAbs (φ i) p by change 0 ≤ |φ i p|; positivity)
      _ ≤ Φ p := hle
      _ = |Φ p| := (abs_of_nonneg (hΦnonneg p)).symm
      _ ≤ M * χ p.1 := hmajor p
  have hYeq (ω : Disorder) :
      ∫ x, χ x ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) = Y ω := by
    dsimp [Y]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => (abs_of_nonneg (hχ x)).symm
  have hXle (i : Fin h) (ω : Disorder) : X i ω ≤ M * Y ω := by
    have h := abs_integral_pairTest_rescaledP2P_le_marginal
      ϑ N s t ω (compactAbs (φ i)) χ M (htermle i)
    have hx : X i ω ≤ M *
        ∫ x, χ x ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) := by
      simpa [X, abs_of_nonneg (hXnn i ω)] using h
    rw [← hYeq]
    exact hx
  have hXint (i : Fin h) : Integrable (X i) disorderLaw := by
    dsimp [X]
    exact integrable_compactPairing_productFlat ϑ N s t (compactAbs (φ i))
  have hY6int : Integrable (fun ω => Y ω ^ 6) disorderLaw := by
    simpa [Y] using SHF.Limit.integrable_flat_polymerMeasure_pow ϑ N s t χ 6
  have hY6le : ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ max C₆ 0 := by
    exact (show ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ C₆ by
      simpa [Y] using hN s t hs hst ht).trans (le_max_left _ _)
  have hProdAEMeas : AEStronglyMeasurable (fun ω => ∏ i : Fin h, X i ω) disorderLaw :=
    Finset.aestronglyMeasurable_fun_prod Finset.univ
      (fun i hi => (hXint i).aestronglyMeasurable)
  have hRHSint : Integrable (fun ω => M ^ h * (1 + Y ω ^ 6)) disorderLaw := by
    exact ((integrable_const (1 : ℝ)).add hY6int).const_mul (M ^ h)
  have hProdnn (ω : Disorder) : 0 ≤ ∏ i : Fin h, X i ω :=
    Finset.prod_nonneg (fun i hi => hXnn i ω)
  have hProdle (ω : Disorder) :
      (∏ i : Fin h, X i ω) ≤ M ^ h * (1 + Y ω ^ 6) := by
    have hprod := Finset.prod_le_prod₀ (s := Finset.univ)
      (fun i hi => hXnn i ω) (fun i hi => hXle i ω)
    calc
      (∏ i : Fin h, X i ω) ≤ ∏ i : Fin h, M * Y ω := hprod
      _ = (M * Y ω) ^ h := by simp
      _ = M ^ h * Y ω ^ h := mul_pow M (Y ω) h
      _ ≤ M ^ h * (1 + Y ω ^ 6) :=
        mul_le_mul_of_nonneg_left
          (flatMarginal_power_le_one_add_six h hh (Y ω) (hYnn ω))
          (pow_nonneg hM h)
  have hProdint : Integrable (fun ω => ∏ i : Fin h, X i ω) disorderLaw := by
    apply hRHSint.mono' hProdAEMeas
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hProdnn ω)]
      exact hProdle ω
  refine ⟨hProdint, ?_⟩
  calc
    ∫ ω, ∏ i : Fin h, X i ω ∂disorderLaw ≤
        ∫ ω, M ^ h * (1 + Y ω ^ 6) ∂disorderLaw :=
      integral_mono hProdint hRHSint hProdle
    _ = M ^ h * (1 + ∫ ω, Y ω ^ 6 ∂disorderLaw) := by
      rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hY6int]
      simp
    _ ≤ B := by
      dsimp [B]
      exact mul_le_mul_of_nonneg_left (add_le_add_right hY6le 1) (pow_nonneg hM h)

end Critical2DKPZ.SHF.Moments

end
