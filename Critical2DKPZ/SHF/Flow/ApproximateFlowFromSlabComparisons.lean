/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabMollifierConvergence
public import Critical2DKPZ.SHF.Flow.MomentKernelTwoSemigroup
public import Critical2DKPZ.SHF.Flow.ApproximateFlowIntegrability
import Mathlib.Tactic

/-! # Approximate composition from three slab comparisons -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology ENNReal

namespace Critical2DKPZ.SHF.Flow

private theorem sq_sub_le_three_sq_errors (a b c d : ℝ) :
    (a - d) ^ 2 ≤ 3 * ((a - b) ^ 2 + (b - c) ^ 2 + (d - c) ^ 2) := by
  nlinarith only [sq_nonneg ((a - b) - (b - c)),
    sq_nonneg ((a - b) + (d - c)), sq_nonneg ((b - c) + (d - c))]

/-- The three slab comparisons give approximate composition of the smoothed SHF
pairings. -/
theorem smoothedProduct_approx_flow_of_comparisons
    (hComparisonOne : ∀ (ϑ : ℝ) (_hPolymerMomentInput : PolymerMomentLimit ϑ)
      (_hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
      (_hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant)) {s t u : ℝ} (_hs : 0 ≤ s)
      (_hst : s < t) (_htu : t < u) (Φ : C_c(Plane × Plane, ℝ)),
      ∀ ε > 0, ∃ v₀ > 0, ∀ v : ℝ, 0 < v → v < v₀ → ∀ᶠ N : ℕ in atTop,
        ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s u ω) - kernelProductPairing (polymerMeasure ϑ N s t ω)
          (slabMeanKernel ϑ N t (t + v)) (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw ≤ ε)
    (hComparisonTwo : ∀ (ϑ : ℝ) (_hPolymerMomentInput : PolymerMomentLimit ϑ)
      (_hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
      (_hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant)) {s t u : ℝ} (_hs : 0 ≤ s)
      (_hst : s < t) (_htu : t < u) (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
      (_hw : ContDiff ℝ (⊤ : ℕ∞) w) (_hwc : HasCompactSupport w) (_hw0 : ∀ x, 0 ≤ w x) (_hw1 : ∫ x, w x = 1),
      ∀ ε > 0, ∃ v₀ > 0, ∀ v : ℝ, 0 < v → v < v₀ → ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ᶠ N : ℕ in atTop,
        ∫ ω, (smoothedProductPairing (polymerMeasure ϑ N s t ω) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x))
            (polymerMeasure ϑ N t u ω) Φ -
          kernelProductPairing (polymerMeasure ϑ N s t ω)
            (fun a b => ∫ y, e⁻¹ ^ 2 * w (e⁻¹ • (a - y)) * slabMeanKernel ϑ N t (t + v) y b)
            (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw ≤ ε)
    (ϑ : ℝ) (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant))
    {s t u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htu : t < u)
    (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ) (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w)
    (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    ∀ ε > 0, ∃ η > 0, ∀ e : ℝ, 0 < e → e < η → ∀ᶠ N : ℕ in atTop,
      ∫ ω, (smoothedProductPairing (polymerMeasure ϑ N s t ω) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x))
          (polymerMeasure ϑ N t u ω) Φ - ∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)) ^ 2 ∂disorderLaw ≤ ε := by
  intro ε hε
  have hε9 : 0 < ε / 9 := by positivity
  obtain ⟨v₁, hv₁, hOne⟩ := hComparisonOne ϑ hPolymerMomentInput hFlatSixthMomentInput hSG hs hst htu Φ (ε / 9) hε9
  obtain ⟨v₂, hv₂, hTwo⟩ := hComparisonTwo ϑ hPolymerMomentInput hFlatSixthMomentInput hSG hs hst htu Φ w
    hw hwc hw0 hw1 (ε / 9) hε9
  let v := min v₁ (min v₂ (u - t)) / 2
  have hm : 0 < min v₁ (min v₂ (u - t)) :=
    lt_min hv₁ (lt_min hv₂ (sub_pos.mpr htu))
  have hv : 0 < v := by dsimp [v]; positivity
  have hvmin : v < min v₁ (min v₂ (u - t)) := by dsimp [v]; linarith
  have hvone : v < v₁ := hvmin.trans_le (min_le_left _ _)
  have hvtwo : v < v₂ := hvmin.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hvu : t + v < u := by
    have := hvmin.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  obtain ⟨η, hη, hThree⟩ := slabSmoothedProduct_sub_slabProduct_sq_small_of
    ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htu Φ w hw hwc hw0 hw1 hv hvu (ε / 9) hε9
  refine ⟨min η 1, lt_min hη zero_lt_one, ?_⟩
  intro e he heη
  have heη' : e < η := heη.trans_le (min_le_left _ _)
  have heone : e ≤ 1 := (heη.trans_le (min_le_right _ _)).le
  let we : Plane → ℝ := fun x => e⁻¹ ^ 2 * w (e⁻¹ • x)
  have hwe : Continuous we := by
    exact continuous_const.mul (hw.continuous.comp
      ((continuous_const : Continuous fun _ : Plane => e⁻¹).smul continuous_id))
  have hwec : HasCompactSupport we := by
    have hcomp : HasCompactSupport (fun x : Plane => w (e⁻¹ • x)) :=
      hwc.comp_smul (inv_ne_zero he.ne')
    exact HasCompactSupport.smul_left (f := fun _ : Plane => (e⁻¹ ^ 2 : ℝ)) hcomp
  filter_upwards [hOne v hv hvone, hTwo v hv hvtwo e he heone,
    hThree e he heη'] with N hOneN hTwoN hThreeN
  let A : Disorder → ℝ := fun ω => smoothedProductPairing
    (polymerMeasure ϑ N s t ω) we (polymerMeasure ϑ N t u ω) Φ
  let B : Disorder → ℝ := fun ω => kernelProductPairing
    (polymerMeasure ϑ N s t ω)
    (fun a b => ∫ y, we (a - y) * slabMeanKernel ϑ N t (t + v) y b)
    (polymerMeasure ϑ N (t + v) u ω) Φ
  let C : Disorder → ℝ := fun ω => kernelProductPairing
    (polymerMeasure ϑ N s t ω) (slabMeanKernel ϑ N t (t + v))
    (polymerMeasure ϑ N (t + v) u ω) Φ
  let D : Disorder → ℝ := fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s u ω)
  have htv : t < t + v := by linarith
  have hA : MemLp A 2 disorderLaw :=
    memLp_smoothedProductPairing_two ϑ N s t t u Φ we hwe hwec
  have hB : MemLp B 2 disorderLaw :=
    memLp_slabSmoothedProduct_two ϑ N hs hst htv hvu Φ we hwe hwec
  have hC : MemLp C 2 disorderLaw :=
    memLp_slabProduct_two ϑ N hs hst htv hvu Φ
  have hD : MemLp D 2 disorderLaw := memLp_polymerPairing_two ϑ N s u Φ
  have hAB : Integrable (fun ω => (A ω - B ω) ^ 2) disorderLaw :=
    (hA.sub hB).integrable_sq
  have hBC : Integrable (fun ω => (B ω - C ω) ^ 2) disorderLaw :=
    (hB.sub hC).integrable_sq
  have hDC : Integrable (fun ω => (D ω - C ω) ^ 2) disorderLaw :=
    (hD.sub hC).integrable_sq
  change (∫ ω, (D ω - C ω) ^ 2 ∂disorderLaw) ≤ ε / 9 at hOneN
  change (∫ ω, (A ω - B ω) ^ 2 ∂disorderLaw) ≤ ε / 9 at hTwoN
  change (∫ ω, (B ω - C ω) ^ 2 ∂disorderLaw) ≤ ε / 9 at hThreeN
  change (∫ ω, (A ω - D ω) ^ 2 ∂disorderLaw) ≤ ε
  calc
    _ ≤ ∫ ω, 3 * ((A ω - B ω) ^ 2 + (B ω - C ω) ^ 2 +
        (D ω - C ω) ^ 2) ∂disorderLaw := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
        (((hAB.add hBC).add hDC).const_mul 3)
      exact Filter.Eventually.of_forall fun ω => sq_sub_le_three_sq_errors _ _ _ _
    _ = 3 * ((∫ ω, (A ω - B ω) ^ 2 ∂disorderLaw) +
        (∫ ω, (B ω - C ω) ^ 2 ∂disorderLaw) +
        (∫ ω, (D ω - C ω) ^ 2 ∂disorderLaw)) := by
      rw [integral_const_mul]
      congr 1
      exact (integral_add (hAB.add hBC) hDC).trans
        (congrArg (fun z : ℝ => z + ∫ ω, (D ω - C ω) ^ 2 ∂disorderLaw)
          (integral_add hAB hBC))
    _ ≤ ε := by linarith

end Critical2DKPZ.SHF.Flow
