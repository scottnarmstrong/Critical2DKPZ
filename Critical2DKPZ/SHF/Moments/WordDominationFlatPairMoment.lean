/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationFlatL2
public import Critical2DKPZ.SHF.Moments.WordDominationCutoff
public import Critical2DKPZ.SHF.Moments.WordDominationMarginalBound
public import Critical2DKPZ.SHF.Moments.WordDominationTestDomination
public import Critical2DKPZ.SHF.Moments.PairingFubini
public import Critical2DKPZ.SHF.Limit.FlatBound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Compact pair-test products controlled by sixth-moment bounds -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Moments

private theorem integrable_compactPairing_rescaledP2P (ϑ : ℝ) (N : ℕ)
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

/-- Two compact pairings tested by absolute compact tests have an integrable
product and a uniform integral bound on a compact positive-time window. -/
theorem eventually_integral_compactAbs_pairing_product_le (ϑ : ℝ)
    (φ₀ φ₁ : C_c(Plane × Plane, ℝ)) {τ T : ℝ} (hτ : 0 < τ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop,
      ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        Integrable (fun ω =>
          (∫ p : Plane × Plane, compactAbs φ₀ p * rescaledP2P ϑ N s t p ω ∂volume) *
          (∫ p : Plane × Plane, compactAbs φ₁ p * rescaledP2P ϑ N s t p ω ∂volume))
          disorderLaw ∧
        ∫ ω,
          (∫ p : Plane × Plane, compactAbs φ₀ p * rescaledP2P ϑ N s t p ω ∂volume) *
          (∫ p : Plane × Plane, compactAbs φ₁ p * rescaledP2P ϑ N s t p ω ∂volume)
          ∂disorderLaw ≤ B := by
  obtain ⟨M₀, χ₀, hM₀, hχ₀, hb₀⟩ :=
    exists_pairTest_firstCoordinate_majorant (compactAbs φ₀)
  obtain ⟨M₁, χ₁, hM₁, hχ₁, hb₁⟩ :=
    exists_pairTest_firstCoordinate_majorant (compactAbs φ₁)
  obtain ⟨C₀, hC₀, hN₀⟩ := eventually_flatMarginal_pairing_sq_integral_le ϑ χ₀ hτ
  obtain ⟨C₁, hC₁, hN₁⟩ := eventually_flatMarginal_pairing_sq_integral_le ϑ χ₁ hτ
  let B : ℝ := (M₀ * M₁ / 2) * (C₀ + C₁)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by positivity) (add_nonneg hC₀ hC₁)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hN₀, hN₁] with N hN₀ hN₁
  intro s t hs hst ht
  let Y₀ : Disorder → ℝ := fun ω =>
    ∫ x, |χ₀ x| ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst)
  let Y₁ : Disorder → ℝ := fun ω =>
    ∫ x, |χ₁ x| ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst)
  let X₀ : Disorder → ℝ := fun ω =>
    ∫ p : Plane × Plane, compactAbs φ₀ p * rescaledP2P ϑ N s t p ω ∂volume
  let X₁ : Disorder → ℝ := fun ω =>
    ∫ p : Plane × Plane, compactAbs φ₁ p * rescaledP2P ϑ N s t p ω ∂volume
  have hY₀nn (ω : Disorder) : 0 ≤ Y₀ ω :=
    integral_nonneg (fun x => abs_nonneg (χ₀ x))
  have hY₁nn (ω : Disorder) : 0 ≤ Y₁ ω :=
    integral_nonneg (fun x => abs_nonneg (χ₁ x))
  have hX₀nn (ω : Disorder) : 0 ≤ X₀ ω :=
    integral_nonneg (fun p => mul_nonneg
      (show 0 ≤ compactAbs φ₀ p by change 0 ≤ |φ₀ p|; positivity)
      (rescaledP2P_nonneg ϑ N s t p ω))
  have hX₁nn (ω : Disorder) : 0 ≤ X₁ ω :=
    integral_nonneg (fun p => mul_nonneg
      (show 0 ≤ compactAbs φ₁ p by change 0 ≤ |φ₁ p|; positivity)
      (rescaledP2P_nonneg ϑ N s t p ω))
  have hX₀le (ω : Disorder) : X₀ ω ≤ M₀ * Y₀ ω := by
    have h := abs_integral_pairTest_rescaledP2P_le_marginal
      ϑ N s t ω (compactAbs φ₀) χ₀ M₀ hb₀
    have hYeq : ∫ x, χ₀ x ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) = Y₀ ω := by
      dsimp [Y₀]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (abs_of_nonneg (hχ₀ x)).symm
    have hX : X₀ ω ≤ M₀ *
        ∫ x, χ₀ x ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) := by
      simpa [X₀, abs_of_nonneg (hX₀nn ω)] using h
    rw [← hYeq]
    exact hX
  have hX₁le (ω : Disorder) : X₁ ω ≤ M₁ * Y₁ ω := by
    have h := abs_integral_pairTest_rescaledP2P_le_marginal
      ϑ N s t ω (compactAbs φ₁) χ₁ M₁ hb₁
    have hYeq : ∫ x, χ₁ x ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) = Y₁ ω := by
      dsimp [Y₁]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (abs_of_nonneg (hχ₁ x)).symm
    have hX : X₁ ω ≤ M₁ *
        ∫ x, χ₁ x ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) := by
      simpa [X₁, abs_of_nonneg (hX₁nn ω)] using h
    rw [← hYeq]
    exact hX
  have hY₀sq : Integrable (fun ω => Y₀ ω ^ 2) disorderLaw := by
    simpa [Y₀] using (hN₀ s t hs hst ht).1
  have hY₁sq : Integrable (fun ω => Y₁ ω ^ 2) disorderLaw := by
    simpa [Y₁] using (hN₁ s t hs hst ht).1
  have hY₀bound : ∫ ω, Y₀ ω ^ 2 ∂disorderLaw ≤ C₀ := by
    simpa [Y₀] using (hN₀ s t hs hst ht).2
  have hY₁bound : ∫ ω, Y₁ ω ^ 2 ∂disorderLaw ≤ C₁ := by
    simpa [Y₁] using (hN₁ s t hs hst ht).2
  have hX₀int : Integrable X₀ disorderLaw := by
    dsimp [X₀]
    exact integrable_compactPairing_rescaledP2P ϑ N s t (compactAbs φ₀)
  have hX₁int : Integrable X₁ disorderLaw := by
    dsimp [X₁]
    exact integrable_compactPairing_rescaledP2P ϑ N s t (compactAbs φ₁)
  have hR : Integrable (fun ω =>
      (M₀ * M₁ / 2) * (Y₀ ω ^ 2 + Y₁ ω ^ 2)) disorderLaw := by
    exact (hY₀sq.add hY₁sq).const_mul (M₀ * M₁ / 2)
  have hprodAEMeas : AEStronglyMeasurable (fun ω => X₀ ω * X₁ ω) disorderLaw :=
    hX₀int.aestronglyMeasurable.mul hX₁int.aestronglyMeasurable
  have hprodle (ω : Disorder) :
      X₀ ω * X₁ ω ≤ (M₀ * M₁ / 2) * (Y₀ ω ^ 2 + Y₁ ω ^ 2) := by
    have hXY : X₀ ω * X₁ ω ≤ (M₀ * Y₀ ω) * (M₁ * Y₁ ω) :=
      mul_le_mul (hX₀le ω) (hX₁le ω)
        (hX₁nn ω) (mul_nonneg hM₀ (hY₀nn ω))
    have hYY : Y₀ ω * Y₁ ω ≤ (Y₀ ω ^ 2 + Y₁ ω ^ 2) / 2 := by
      nlinarith [sq_nonneg (Y₀ ω - Y₁ ω)]
    calc
      X₀ ω * X₁ ω ≤ M₀ * M₁ * (Y₀ ω * Y₁ ω) := by
        calc
          _ ≤ (M₀ * Y₀ ω) * (M₁ * Y₁ ω) := hXY
          _ = M₀ * M₁ * (Y₀ ω * Y₁ ω) := by ring
      _ ≤ M₀ * M₁ * ((Y₀ ω ^ 2 + Y₁ ω ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hYY (mul_nonneg hM₀ hM₁)
      _ = (M₀ * M₁ / 2) * (Y₀ ω ^ 2 + Y₁ ω ^ 2) := by ring
  have hprodint : Integrable (fun ω => X₀ ω * X₁ ω) disorderLaw := by
    apply hR.mono' hprodAEMeas
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hX₀nn ω) (hX₁nn ω))]
    exact hprodle ω
  refine ⟨hprodint, ?_⟩
  calc
    ∫ ω, X₀ ω * X₁ ω ∂disorderLaw ≤
        ∫ ω, (M₀ * M₁ / 2) * (Y₀ ω ^ 2 + Y₁ ω ^ 2) ∂disorderLaw :=
      integral_mono hprodint hR hprodle
    _ = (M₀ * M₁ / 2) *
        ((∫ ω, Y₀ ω ^ 2 ∂disorderLaw) + (∫ ω, Y₁ ω ^ 2 ∂disorderLaw)) := by
      rw [integral_const_mul, integral_add hY₀sq hY₁sq]
    _ ≤ B := by
      dsimp [B]
      exact mul_le_mul_of_nonneg_left
        (add_le_add hY₀bound hY₁bound) (by positivity)

end Critical2DKPZ.SHF.Moments

end
