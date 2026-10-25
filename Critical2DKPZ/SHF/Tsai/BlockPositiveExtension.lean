/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.PositiveBlockMoments
import Critical2DKPZ.SHF.Tsai.PositiveApproximation
import Critical2DKPZ.SHF.Tsai.PositiveMonotoneProducts

/-! # Block moments for all positive measurable tests

The finite real `L²` formulas determine the extended positive moments by an
increasing bounded, finite-volume exhaustion. No finiteness is assumed for
the limiting test or its moment. This is the positive moment identity.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The full positive moment identity, obtained by monotone convergence from the real `L²` axiom. -/
theorem HasDeltaBoseMoments.lintegral_prod_eq {θ τ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (f f' : Fin n → Plane → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hf' : ∀ i, Measurable (f' i)) :
    ∫⁻ ω, ∏ i, (∫⁻ p, f i p.1 * f' i p.2 ∂(B ω)) ∂P =
      ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
        (∏ i, f i (x i)) * momentKernel n θ τ x y * ∏ i, f' i (y i) := by
  let a (i : Fin n) (N : ℕ) := positiveTruncation (f i) N
  let b (i : Fin n) (N : ℕ) := positiveTruncation (f' i) N
  have ham (i N) : Measurable (a i N) := measurable_positiveTruncation (hf i) N
  have hbm (i N) : Measurable (b i N) := measurable_positiveTruncation (hf' i) N
  have ha (i) : Monotone (a i) := monotone_positiveTruncation (f i)
  have hb (i) : Monotone (b i) := monotone_positiveTruncation (f' i)
  have hasup (i x) : (⨆ N, a i N x) = f i x := iSup_positiveTruncation (f i) x
  have hbsup (i x) : (⨆ N, b i N x) = f' i x := iSup_positiveTruncation (f' i) x
  have hpair (i) (p : Plane × Plane) :
      (⨆ N, a i N p.1 * b i N p.2) = f i p.1 * f' i p.2 := by
    rw [← iSup_mul_of_monotone (fun N M hNM => ha i hNM p.1)
      (fun N M hNM => hb i hNM p.2), hasup, hbsup]
  have hleft : (∫⁻ ω, ∏ i, (∫⁻ p, f i p.1 * f' i p.2 ∂B ω) ∂P) =
      ⨆ N, ∫⁻ ω, ∏ i, (∫⁻ p, a i N p.1 * b i N p.2 ∂B ω) ∂P := by
    simp_rw [← hpair]
    exact lintegral_prod_lintegral_iSup P B hB.1
      (fun i N p => a i N p.1 * b i N p.2)
      (fun i N => ((ham i N).comp measurable_fst).mul ((hbm i N).comp measurable_snd))
      (fun i N M hNM p => mul_le_mul' (ha i hNM p.1) (hb i hNM p.2))
  have hmoment (N : ℕ) :
      (∫⁻ ω, ∏ i, (∫⁻ p, a i N p.1 * b i N p.2 ∂B ω) ∂P) =
        ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
          (∏ i, a i N (x i)) * momentKernel n θ τ x y * ∏ i, b i N (y i) := by
    have h := hB.lintegral_prod_ofReal_eq hτ hn1 hn
      (fun i x => (a i N x).toReal) (fun i x => (b i N x).toReal)
      (fun i => memLp_positiveTruncation_toReal (hf i) N)
      (fun i => memLp_positiveTruncation_toReal (hf' i) N)
      (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    simpa only [a, b, ofReal_positiveTruncation_toReal] using h
  let A (N : ℕ) (x : Configuration n) := ∏ i, a i N (x i)
  let C (N : ℕ) (y : Configuration n) := ∏ i, b i N (y i)
  have hA : Monotone A := fun N M hNM x => Finset.prod_le_prod fun i _ => ha i hNM (x i)
  have hC : Monotone C := fun N M hNM y => Finset.prod_le_prod fun i _ => hb i hNM (y i)
  have hAm (N) : Measurable (A N) :=
    Finset.measurable_prod _ fun i _ => (ham i N).comp (measurable_pi_apply i)
  have hCm (N) : Measurable (C N) :=
    Finset.measurable_prod _ fun i _ => (hbm i N).comp (measurable_pi_apply i)
  have hAsup (x : Configuration n) : (⨆ N, A N x) = ∏ i, f i (x i) := by
    rw [iSup_finset_prod_of_monotone Finset.univ _ (fun i N M hNM => ha i hNM (x i))]
    simp_rw [hasup]
  have hCsup (y : Configuration n) : (⨆ N, C N y) = ∏ i, f' i (y i) := by
    rw [iSup_finset_prod_of_monotone Finset.univ _ (fun i N M hNM => hb i hNM (y i))]
    simp_rw [hbsup]
  let J (N : ℕ) (x y : Configuration n) := A N x * momentKernel n θ τ x y * C N y
  have hJ : Monotone J := fun N M hNM x y =>
    mul_le_mul' (mul_le_mul' (hA hNM x) le_rfl) (hC hNM y)
  have hJsup (x y : Configuration n) :
      (⨆ N, J N x y) = (∏ i, f i (x i)) * momentKernel n θ τ x y * ∏ i, f' i (y i) := by
    rw [← iSup_mul_of_monotone (fun N M hNM => mul_le_mul' (hA hNM x) le_rfl)
      (fun N M hNM => hC hNM y), ← ENNReal.iSup_mul, hAsup, hCsup]
  have hK : Measurable (fun xy : Configuration n × Configuration n => momentKernel n θ τ xy.1 xy.2) :=
    Measurable.comp
      (g := fun q : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n q.1.1 q.1.2 q.2.1 q.2.2)
      (f := fun xy : Configuration n × Configuration n => ((θ, τ), xy))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  have hJm (N : ℕ) : Measurable (Function.uncurry (J N)) :=
    (((hAm N).comp measurable_fst).mul hK).mul ((hCm N).comp measurable_snd)
  rw [hleft]
  simp_rw [hmoment]
  change (⨆ N, ∫⁻ x, ∫⁻ y, J N x y) = _
  calc
    _ = ∫⁻ x, ⨆ N, ∫⁻ y, J N x y := by
      symm
      apply lintegral_iSup
      · intro N
        exact (hJm N).lintegral_prod_right'
      · intro N M hNM x
        exact lintegral_mono (hJ hNM x)
    _ = ∫⁻ x, ∫⁻ y, ⨆ N, J N x y := by
      apply lintegral_congr
      intro x
      symm
      have hm (N) : Measurable (J N x) :=
        Measurable.comp (g := Function.uncurry (J N)) (f := fun y => (x, y))
          (hJm N) (measurable_const.prodMk measurable_id)
      exact lintegral_iSup (f := fun N y => J N x y) hm (fun N M hNM y => hJ hNM x y)
    _ = _ := by simp_rw [hJsup]

end Critical2DKPZ.SHF.Tsai

end
