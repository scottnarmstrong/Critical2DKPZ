/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockCompositionLocalLimit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Pointwise two-coordinate smoothing for pair-block compositions -/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

private theorem largeBlockGaussianWeight_abs_sum_one
    {C : ℝ} {m₀ mCut m : ℕ}
    (hprofile : ∀ m : ℕ, m₀ ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1),
        normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ))
    (hm₀cut : m₀ ≤ mCut) :
    ∑ k ∈ Finset.range (m + 1), |largeBlockGaussianWeight mCut m k| = 1 := by
  by_cases hm : mCut ≤ m
  · have hsum := (hprofile m (hm₀cut.trans hm)).2.2.1
    have hnonneg : ∀ k ∈ Finset.range (m + 1),
        0 ≤ normalizedSampledHypergeometricGaussianWeight m k := by
      intro k hk
      dsimp [normalizedSampledHypergeometricGaussianWeight,
        sampledHypergeometricGaussianWeight]
      positivity
    simpa [largeBlockGaussianWeight, hm] using (calc
      (∑ k ∈ Finset.range (m + 1),
          |normalizedSampledHypergeometricGaussianWeight m k|) =
        ∑ k ∈ Finset.range (m + 1),
          normalizedSampledHypergeometricGaussianWeight m k := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [abs_of_nonneg (hnonneg k hk)]
      _ = 1 := hsum)
  · have hsum : ∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k| = 1 := by
      calc
        _ = ∑ k ∈ Finset.range (m + 1), WalkTails.hypergeometricWeight m k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [abs_of_nonneg (WalkTails.hypergeometricWeight_nonneg m k)]
        _ = 1 := WalkTails.sum_hypergeometricWeight m
    simpa [largeBlockGaussianWeight, hm] using hsum

private theorem largeBlockGaussianListLaw_abs_sum_one
    {C : ℝ} {mCut : ℕ}
    (hprofile : ∀ m : ℕ, mCut ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1),
        normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ))
    (ms : List ℕ) :
    ∑ j ∈ Finset.range (ms.sum + 1),
      |largeBlockGaussianListLaw mCut ms j| = 1 := by
  have hsum := largeBlockGaussianListLaw_sum_one hprofile ms
  have hnonneg := largeBlockGaussianListLaw_nonneg hprofile ms
  calc
    _ = ∑ j ∈ Finset.range (ms.sum + 1),
        largeBlockGaussianListLaw mCut ms j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_of_nonneg (hnonneg j)]
    _ = 1 := hsum

/-- A Gaussianized composition has maximal atom bounded at the inverse square root of its longest block length. -/
theorem exists_largeBlockGaussianListLaw_max_atom_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ mCut : ℕ, m₀ ≤ mCut → 0 < mCut →
      ∀ ms : List ℕ, ms ≠ [] → (∀ m ∈ ms, 0 < m) →
        mCut ≤ pairBlockListMaxDuration ms →
        ∀ j ∈ Finset.range (ms.sum + 1),
          |largeBlockGaussianListLaw mCut ms j| ≤
            C / Real.sqrt (pairBlockListMaxDuration ms : ℝ) := by
  obtain ⟨Cexact, hCexact, hexact⟩ :=
    exists_hypergeometricBlockListLaw_max_atom_bound
  obtain ⟨Cgauss, hCgauss, mgauss, hgauss⟩ :=
    exists_normalizedSampledHypergeometricGaussian_pointwise_bound
  obtain ⟨Cprofile, hCprofile, mprofile, hprofile⟩ :=
    exists_normalized_hypergeometricGaussian_L1_error
  let C : ℝ := max Cexact Cgauss
  let m₀ := max mgauss mprofile
  have hmaxexact : Cexact ≤ C := le_max_left _ _
  have hmaxgauss : Cgauss ≤ C := le_max_right _ _
  have hmgauss : mgauss ≤ m₀ := le_max_left _ _
  have hmprofile : mprofile ≤ m₀ := le_max_right _ _
  refine ⟨C, lt_max_of_lt_left hCexact, m₀, ?_⟩
  intro mCut hm₀ hmCut
  have hprofileCut : ∀ m : ℕ, mCut ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1),
        normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ Cprofile / Real.sqrt (m : ℝ) := by
    intro m hm
    exact hprofile m (le_trans hmprofile (le_trans hm₀ hm))
  intro ms
  induction ms with
  | nil =>
      intro hne
      cases hne rfl
  | cons m ms ih =>
      intro hne hpositive hcut j hj
      let Mtail := pairBlockListMaxDuration ms
      let M := pairBlockListMaxDuration (m :: ms)
      have hM : M = max m Mtail := rfl
      have hcutM : mCut ≤ M := hcut
      have hheadAbs :
          ∑ k ∈ Finset.range (m + 1), |largeBlockGaussianWeight mCut m k| = 1 :=
        largeBlockGaussianWeight_abs_sum_one hprofileCut le_rfl
      have htailAbs :
          ∑ k ∈ Finset.range (ms.sum + 1),
            |largeBlockGaussianListLaw mCut ms k| = 1 :=
        largeBlockGaussianListLaw_abs_sum_one hprofileCut ms
      by_cases htailLe : Mtail ≤ m
      · have hmax : M = m := by
          rw [hM]
          exact Nat.max_eq_left htailLe
        have hcutm : mCut ≤ m := hmax ▸ hcutM
        have hmpos : 0 < m := hpositive m (by simp)
        have hpoint : ∀ k ∈ Finset.range (m + 1),
            |largeBlockGaussianWeight mCut m k| ≤ C / Real.sqrt (m : ℝ) := by
          intro k hk
          have hlocal := hgauss m (le_trans hmgauss (le_trans hm₀ hcutm)) k hk
          simpa [largeBlockGaussianWeight, hcutm] using
            hlocal.trans (div_le_div_of_nonneg_right hmaxgauss
              (Real.sqrt_nonneg _))
        have hconv := finiteNaturalConvolution_abs_le_leftPointwise
          (largeBlockGaussianWeight mCut m) (largeBlockGaussianListLaw mCut ms)
          (C / Real.sqrt (m : ℝ)) 1 j (by positivity) hpoint htailAbs.le
        have hrewrite : largeBlockGaussianListLaw mCut (m :: ms) j =
            finiteNaturalConvolution m ms.sum
              (largeBlockGaussianWeight mCut m)
              (largeBlockGaussianListLaw mCut ms) j := rfl
        rw [hrewrite]
        change |finiteNaturalConvolution m ms.sum
          (largeBlockGaussianWeight mCut m) (largeBlockGaussianListLaw mCut ms) j| ≤
            C / Real.sqrt (M : ℝ)
        rw [hmax]
        simpa using hconv
      · have hmaxTail : m < Mtail := Nat.lt_of_not_ge htailLe
        have hcutTail : mCut ≤ Mtail := by
          rw [hM, Nat.max_eq_right hmaxTail.le] at hcutM
          exact hcutM
        have htailNe : ms ≠ [] := by
          intro hempty
          subst ms
          simp [Mtail, pairBlockListMaxDuration] at hmaxTail
        have htailPositive : ∀ k ∈ ms, 0 < k := by
          intro k hk
          exact hpositive k (by simp [hk])
        have htailBound := ih htailNe htailPositive hcutTail
        have htailPoint : ∀ k ∈ Finset.range (ms.sum + 1),
            |largeBlockGaussianListLaw mCut ms k| ≤ C / Real.sqrt (Mtail : ℝ) := by
          intro k hk
          simpa [C, Mtail] using htailBound k hk
        have hconv := finiteNaturalConvolution_abs_le_rightPointwise
          (largeBlockGaussianWeight mCut m) (largeBlockGaussianListLaw mCut ms)
          1 (C / Real.sqrt (Mtail : ℝ)) j (by positivity) hheadAbs.le htailPoint
        have hrewrite : largeBlockGaussianListLaw mCut (m :: ms) j =
            finiteNaturalConvolution m ms.sum
              (largeBlockGaussianWeight mCut m)
              (largeBlockGaussianListLaw mCut ms) j := rfl
        have hmax : M = Mtail := by
          rw [hM]
          exact Nat.max_eq_right hmaxTail.le
        rw [hrewrite]
        change |finiteNaturalConvolution m ms.sum
          (largeBlockGaussianWeight mCut m) (largeBlockGaussianListLaw mCut ms) j| ≤
            C / Real.sqrt (M : ℝ)
        rw [hmax]
        simpa using hconv

/-- At a supported pair of rotated marks, the exact composition law differs
from its Gaussianized law by the longest-block pointwise error times one
additional local-CLT atom factor. -/
theorem exists_hypergeometricBlockListPairLaw_pointwise_hybrid_error :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ m₀ : ℕ,
      ∀ mCut : ℕ, m₀ ≤ mCut → 0 < mCut →
      ∀ ms : List ℕ, ms ≠ [] → (∀ m ∈ ms, 0 < m) →
        mCut ≤ pairBlockListMaxDuration ms →
      ∀ j₁ j₂ : ℕ, j₁ ∈ Finset.range (ms.sum + 1) →
        j₂ ∈ Finset.range (ms.sum + 1) →
          |hypergeometricBlockListPairLaw ms j₁ j₂ -
            largeBlockGaussianListPairLaw mCut ms j₁ j₂| ≤
            C₁ / ((pairBlockListMaxDuration ms : ℝ) *
              Real.sqrt (pairBlockListMaxDuration ms : ℝ)) +
            C₂ * (ms.length : ℝ) /
              ((pairBlockListMaxDuration ms : ℝ) *
                Real.sqrt (mCut : ℝ)) := by
  obtain ⟨Cerr₁, hCerr₁, Cerr₂, hCerr₂, merr, herr⟩ :=
    exists_hypergeometricBlockListLaw_hybrid_pointwise_error
  obtain ⟨Cexact, hCexact, hexact⟩ :=
    exists_hypergeometricBlockListLaw_max_atom_bound
  obtain ⟨Cgauss, hCgauss, mgauss, hgauss⟩ :=
    exists_largeBlockGaussianListLaw_max_atom_bound
  let C₁ : ℝ := (Cexact + Cgauss) * Cerr₁
  let C₂ : ℝ := (Cexact + Cgauss) * Cerr₂
  let m₀ := max merr mgauss
  have hmerr : merr ≤ m₀ := le_max_left _ _
  have hmgauss : mgauss ≤ m₀ := le_max_right _ _
  refine ⟨C₁, ?_, C₂, ?_, m₀, ?_⟩
  · dsimp [C₁]
    positivity
  · dsimp [C₂]
    positivity
  · intro mCut hmCut₀ hmCutPos ms hne hpositive hm j₁ j₂ hj₁ hj₂
    let M := pairBlockListMaxDuration ms
    have hMpos : 0 < M := by
      cases ms with
      | nil => cases hne rfl
      | cons m ms =>
          change 0 < max m (pairBlockListMaxDuration ms)
          exact lt_of_lt_of_le (hpositive m (by simp)) (Nat.le_max_left _ _)
    have hM0₁ : merr ≤ mCut := le_trans hmerr hmCut₀
    have hM0₂ : mgauss ≤ mCut := le_trans hmgauss hmCut₀
    have hscalar := herr mCut hM0₁ hmCutPos ms hne hpositive hm
    have hpoint₁ :
        |hypergeometricBlockListLaw ms j₁ - largeBlockGaussianListLaw mCut ms j₁| ≤
          Cerr₁ / (M : ℝ) + Cerr₂ * (ms.length : ℝ) /
            (Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ)) := by
      simpa [M, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hscalar j₁ hj₁
    have hpoint₂ :
        |hypergeometricBlockListLaw ms j₂ - largeBlockGaussianListLaw mCut ms j₂| ≤
          Cerr₁ / (M : ℝ) + Cerr₂ * (ms.length : ℝ) /
            (Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ)) := by
      simpa [M, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hscalar j₂ hj₂
    have hexactAtom₂ :
        |hypergeometricBlockListLaw ms j₂| ≤ Cexact / Real.sqrt (M : ℝ) :=
      hexact ms hne hpositive j₂ hj₂
    have hgaussAtom₁ :
        |largeBlockGaussianListLaw mCut ms j₁| ≤ Cgauss / Real.sqrt (M : ℝ) := by
      exact hgauss mCut hM0₂ hmCutPos ms hne hpositive hm j₁ hj₁
    have hgaussAtom₂ :
        |largeBlockGaussianListLaw mCut ms j₂| ≤ Cgauss / Real.sqrt (M : ℝ) := by
      exact hgauss mCut hM0₂ hmCutPos ms hne hpositive hm j₂ hj₂
    have hprod :
        |hypergeometricBlockListLaw ms j₁ * hypergeometricBlockListLaw ms j₂ -
          largeBlockGaussianListLaw mCut ms j₁ * largeBlockGaussianListLaw mCut ms j₂| ≤
        |hypergeometricBlockListLaw ms j₁ - largeBlockGaussianListLaw mCut ms j₁| *
            |hypergeometricBlockListLaw ms j₂| +
          |largeBlockGaussianListLaw mCut ms j₁| *
            |hypergeometricBlockListLaw ms j₂ - largeBlockGaussianListLaw mCut ms j₂| := by
      calc
        _ = |(hypergeometricBlockListLaw ms j₁ - largeBlockGaussianListLaw mCut ms j₁) *
              hypergeometricBlockListLaw ms j₂ +
            largeBlockGaussianListLaw mCut ms j₁ *
              (hypergeometricBlockListLaw ms j₂ - largeBlockGaussianListLaw mCut ms j₂)| := by
                congr 1
                ring
        _ ≤ |(hypergeometricBlockListLaw ms j₁ - largeBlockGaussianListLaw mCut ms j₁) *
              hypergeometricBlockListLaw ms j₂| +
            |largeBlockGaussianListLaw mCut ms j₁ *
              (hypergeometricBlockListLaw ms j₂ - largeBlockGaussianListLaw mCut ms j₂)| :=
                abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul]
    have hMroot : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hMpos)
    have hM : (M : ℝ) = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) := by
      calc
        (M : ℝ) = Real.sqrt (M : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg M)).symm
        _ = Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) := by ring
    have hrootSq : Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ) = (M : ℝ) := hM.symm
    let E : ℝ := Cerr₁ / (M : ℝ) + Cerr₂ * (ms.length : ℝ) /
      (Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ))
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hbound :
        E * (Cexact / Real.sqrt (M : ℝ)) +
          (Cgauss / Real.sqrt (M : ℝ)) * E ≤
        C₁ / ((M : ℝ) * Real.sqrt (M : ℝ)) +
          C₂ * (ms.length : ℝ) / ((M : ℝ) * Real.sqrt (mCut : ℝ)) := by
      dsimp [E, C₁, C₂]
      have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hMpos)
      have hcutR : 0 < (mCut : ℝ) := by exact_mod_cast hmCutPos
      have hcutroot : 0 < Real.sqrt (mCut : ℝ) := Real.sqrt_pos.mpr hcutR
      have hMterm : (M : ℝ) * Cerr₂ * (ms.length : ℝ) =
          (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) * Cerr₂ * (ms.length : ℝ) := by
        apply congrArg (fun x : ℝ => x * (ms.length : ℝ))
        apply congrArg (fun x : ℝ => x * Cerr₂)
        exact hM
      have hpoly :
          Cerr₁ * Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ) +
              (M : ℝ) * Cerr₂ * (ms.length : ℝ) =
            Real.sqrt (M : ℝ) *
              (Cerr₁ * Real.sqrt (mCut : ℝ) + Cerr₂ * (ms.length : ℝ) * Real.sqrt (M : ℝ)) := by
        calc
          _ = Cerr₁ * Real.sqrt (M : ℝ) * Real.sqrt (mCut : ℝ) +
              (Real.sqrt (M : ℝ) * Real.sqrt (M : ℝ)) * Cerr₂ * (ms.length : ℝ) := by
                rw [hMterm]
          _ = _ := by ring
      field_simp [hMroot.ne', hMR, hcutroot.ne']
      rw [hpoly]
    calc
      _ ≤ |hypergeometricBlockListLaw ms j₁ - largeBlockGaussianListLaw mCut ms j₁| *
            |hypergeometricBlockListLaw ms j₂| +
          |largeBlockGaussianListLaw mCut ms j₁| *
            |hypergeometricBlockListLaw ms j₂ - largeBlockGaussianListLaw mCut ms j₂| := hprod
      _ ≤ E * (Cexact / Real.sqrt (M : ℝ)) +
          (Cgauss / Real.sqrt (M : ℝ)) *
            E := by
            gcongr
      _ ≤ C₁ / ((M : ℝ) * Real.sqrt (M : ℝ)) +
          C₂ * (ms.length : ℝ) / ((M : ℝ) * Real.sqrt (mCut : ℝ)) := hbound



private theorem list_sum_le_length_mul_pairBlockListMaxDuration (ms : List ℕ) :
    ms.sum ≤ ms.length * pairBlockListMaxDuration ms := by
  induction ms with
  | nil => simp [pairBlockListMaxDuration]
  | cons m ms ih =>
      let M := pairBlockListMaxDuration (m :: ms)
      have hM : M = max m (pairBlockListMaxDuration ms) := rfl
      have hm : m ≤ M := by rw [hM]; exact Nat.le_max_left _ _
      have htail : ms.sum ≤ ms.length * M := by
        rw [hM]
        exact le_trans ih (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
      calc
        (m :: ms).sum = m + ms.sum := by simp
        _ ≤ M + ms.length * M := Nat.add_le_add hm htail
        _ = (m :: ms).length * M := by
          simp [List.length_cons, Nat.succ_mul, Nat.add_comm]




/-- The twelfth power of the logarithmic cutoff is negligible on the
diffusive square-root scale. -/
theorem tendsto_ceilLogPow_twelve_div_sqrt :
    Tendsto (fun N : ℕ => (⌈Real.log (N : ℝ)⌉₊ : ℝ) ^ 12 /
      Real.sqrt (N : ℝ)) atTop (𝓝 0) := by
  have hroot : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlogPow : Tendsto (fun x : ℝ => (Real.log x) ^ 12 / x) atTop (𝓝 0) := by
    simpa only [one_mul, add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 12 one_ne_zero)
  have hcompare : Tendsto (fun N : ℕ =>
      (3 : ℝ) ^ 12 * ((Real.log (Real.sqrt (N : ℝ)) ^ 12) /
        Real.sqrt (N : ℝ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (hlogPow.comp hroot).const_mul ((3 : ℝ) ^ 12)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (Real.sqrt (N : ℝ)) := by
    exact (Real.tendsto_log_atTop.comp hroot).eventually_ge_atTop 1
  have hNpos : ∀ᶠ N : ℕ in atTop, 0 < N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    omega
  have hbound : ∀ᶠ N : ℕ in atTop,
      0 ≤ (⌈Real.log (N : ℝ)⌉₊ : ℝ) ^ 12 / Real.sqrt (N : ℝ) ∧
      (⌈Real.log (N : ℝ)⌉₊ : ℝ) ^ 12 / Real.sqrt (N : ℝ) ≤
        (3 : ℝ) ^ 12 * (Real.log (Real.sqrt (N : ℝ)) ^ 12 /
          Real.sqrt (N : ℝ)) := by
    filter_upwards [hlarge, hNpos] with N hlargeN hNposN
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNposN
    have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := by
      have hlogSqrtEq : Real.log (Real.sqrt (N : ℝ)) =
          Real.log (N : ℝ) / 2 := Real.log_sqrt hNreal.le
      rw [hlogSqrtEq] at hlargeN
      linarith
    have hceil : (⌈Real.log (N : ℝ)⌉₊ : ℝ) < Real.log (N : ℝ) + 1 :=
      Nat.ceil_lt_add_one hlogNnonneg
    have hlogSqrtEq : Real.log (Real.sqrt (N : ℝ)) =
        Real.log (N : ℝ) / 2 := Real.log_sqrt hNreal.le
    have hceilBound : (⌈Real.log (N : ℝ)⌉₊ : ℝ) ≤
        3 * Real.log (Real.sqrt (N : ℝ)) := by
      rw [hlogSqrtEq]
      linarith
    have hpow : (⌈Real.log (N : ℝ)⌉₊ : ℝ) ^ 12 ≤
        (3 * Real.log (Real.sqrt (N : ℝ))) ^ 12 :=
      pow_le_pow_left₀ (by positivity) hceilBound 12
    constructor
    · positivity
    · calc
        _ ≤ (3 * Real.log (Real.sqrt (N : ℝ))) ^ 12 /
            Real.sqrt (N : ℝ) :=
              div_le_div_of_nonneg_right hpow (Real.sqrt_nonneg _)
        _ = (3 : ℝ) ^ 12 * (Real.log (Real.sqrt (N : ℝ)) ^ 12 /
            Real.sqrt (N : ℝ)) := by ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcompare
  · filter_upwards with N
    positivity
  · filter_upwards [hbound] with N hN
    exact hN.2


/-- Gaussianizing every block above `(ceil log N)^10` changes the scaled pair
law by a vanishing amount, uniformly over retained compositions on a positive
time slab. -/
theorem eventually_hypergeometricBlockListPairLaw_scaled_error_longBlockCutoff
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ ms : List ℕ, ms ≠ [] →
      (∀ m ∈ ms, 0 < m) → δ * (N : ℝ) ≤ (ms.sum : ℝ) →
      ms.length ≤ ⌈Real.log (N : ℝ)⌉₊ ^ 2 →
      ∀ j₁ j₂ : ℕ, j₁ ∈ Finset.range (ms.sum + 1) →
        j₂ ∈ Finset.range (ms.sum + 1) →
        (N : ℝ) *
          |hypergeometricBlockListPairLaw ms j₁ j₂ -
            largeBlockGaussianListPairLaw (⌈Real.log (N : ℝ)⌉₊ ^ 10) ms j₁ j₂| < ε := by
  obtain ⟨C₁, hC₁, C₂, hC₂, m₀, hpair⟩ :=
    exists_hypergeometricBlockListPairLaw_pointwise_hybrid_error
  let C : ℝ := C₁ + C₂
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall12 : ∀ᶠ N : ℕ in atTop,
      (⌈Real.log (N : ℝ)⌉₊ : ℝ) ^ 12 / Real.sqrt (N : ℝ) < δ :=
    (tendsto_ceilLogPow_twelve_div_sqrt.eventually (Iio_mem_nhds hδ))
  have hlogOne : ∀ᶠ N : ℕ in atTop, 1 < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 1
  have hlogM₀ : ∀ᶠ N : ℕ in atTop, (m₀ : ℝ) < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop m₀
  have hlogThreshold : ∀ᶠ N : ℕ in atTop,
      2 * C / (δ * ε) < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      (2 * C / (δ * ε))
  have hNpos : ∀ᶠ N : ℕ in atTop, 0 < N := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    omega
  filter_upwards [hsmall12, hlogOne, hlogM₀, hlogThreshold, hNpos]
    with N hsmall12N hlogN hlogM₀N hlogThresholdN hN
  intro ms hne hpositive hsum hlength j₁ j₂ hj₁ hj₂
  let K : ℕ := ⌈Real.log (N : ℝ)⌉₊
  let L : ℝ := ms.length
  let n : ℝ := ms.sum
  let M : ℝ := pairBlockListMaxDuration ms
  let mCut : ℕ := K ^ 10
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hKlower : Real.log (N : ℝ) ≤ (K : ℝ) := by
    dsimp [K]
    exact Nat.le_ceil _
  have hKupper : (K : ℝ) < Real.log (N : ℝ) + 1 := by
    dsimp [K]
    exact Nat.ceil_lt_add_one (by linarith)
  have hKgt1 : 1 < (K : ℝ) := by linarith
  have hKpos : 0 < K := by exact_mod_cast (show (0 : ℝ) < (K : ℝ) by linarith)
  have hKrealPos : 0 < (K : ℝ) := by exact_mod_cast hKpos
  have hK2pos : 0 < (K : ℝ) ^ 2 := by positivity
  have hKrealOne : 1 ≤ (K : ℝ) := by linarith
  have hKpow₁₀ : K ≤ K ^ 10 := by
    exact Nat.le_self_pow (by norm_num : 10 ≠ 0) K
  have hm₀leKreal : (m₀ : ℝ) ≤ (K : ℝ) :=
    (le_of_lt hlogM₀N).trans hKlower
  have hm₀leK : m₀ ≤ K := by exact_mod_cast hm₀leKreal
  have hm₀leCut : m₀ ≤ mCut := by
    dsimp [mCut]
    exact le_trans hm₀leK hKpow₁₀
  have hmCutPos : 0 < mCut := by dsimp [mCut]; positivity
  have hrootN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNreal
  have hrootNle : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    have hrootOne : 1 ≤ Real.sqrt (N : ℝ) := by
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hN)
    calc
      Real.sqrt (N : ℝ) = 1 * Real.sqrt (N : ℝ) := by ring
      _ ≤ Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_right hrootOne (Real.sqrt_nonneg _)
      _ = (N : ℝ) := by
        calc
          _ = (Real.sqrt (N : ℝ)) ^ 2 := by ring
          _ = (N : ℝ) := Real.sq_sqrt hNreal.le
  have hDiscrepancyStringInputN : (K : ℝ) ^ 12 / (N : ℝ) < δ := by
    have hdiv : (K : ℝ) ^ 12 / (N : ℝ) ≤
        (K : ℝ) ^ 12 / Real.sqrt (N : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hrootN hrootNle
    exact lt_of_le_of_lt hdiv hsmall12N
  have hK12lt : (K : ℝ) ^ 12 < δ * (N : ℝ) :=
    (div_lt_iff₀ hNreal).1 hDiscrepancyStringInputN
  have hlengthR : L ≤ (K : ℝ) ^ 2 := by
    dsimp [L, K]
    exact_mod_cast hlength
  have hlenNat : 0 < ms.length := by
    cases ms with
    | nil => exact (hne rfl).elim
    | cons m ms => simp
  have hL : 0 < L := by dsimp [L]; exact_mod_cast hlenNat
  have hsumR : δ * (N : ℝ) ≤ n := by simpa [n] using hsum
  have hsumMaxNat := list_sum_le_length_mul_pairBlockListMaxDuration ms
  have hsumMax : n ≤ L * M := by
    dsimp [n, L, M]
    exact_mod_cast hsumMaxNat
  have hMlower : (δ * (N : ℝ)) / L ≤ M := by
    calc
      (δ * (N : ℝ)) / L ≤ n / L := div_le_div_of_nonneg_right hsumR hL.le
      _ ≤ M := by
        rw [div_le_iff₀ hL]
        simpa [mul_comm] using hsumMax
  have hCutRealLeM : (K : ℝ) ^ 10 ≤ M := by
    have hKpower : (K : ℝ) ^ 10 = (K : ℝ) ^ 12 / (K : ℝ) ^ 2 := by
      field_simp [hK2pos.ne']
    calc
      (K : ℝ) ^ 10 = (K : ℝ) ^ 12 / (K : ℝ) ^ 2 := hKpower
      _ ≤ (δ * (N : ℝ)) / (K : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hK12lt.le (by positivity)
      _ ≤ (δ * (N : ℝ)) / L :=
        div_le_div_of_nonneg_left (mul_nonneg hδ.le hNreal.le) hL hlengthR
      _ ≤ M := hMlower
  have hCutLeM : mCut ≤ pairBlockListMaxDuration ms := by
    dsimp [mCut, M] at hCutRealLeM ⊢
    exact_mod_cast hCutRealLeM
  have hMpos : 0 < M := lt_of_lt_of_le
    (by exact_mod_cast hmCutPos) hCutRealLeM
  have hMrealPos : 0 < M := hMpos
  have hMne : M ≠ 0 := hMrealPos.ne'
  have hrootM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMrealPos
  have hcutCastPos : 0 < (mCut : ℝ) := by exact_mod_cast hmCutPos
  have hrootCut : 0 < Real.sqrt (mCut : ℝ) := Real.sqrt_pos.mpr hcutCastPos
  have hrootCutEq : Real.sqrt ((K : ℝ) ^ 10) = (K : ℝ) ^ 5 := by
    rw [show (K : ℝ) ^ 10 = ((K : ℝ) ^ 5) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  have hpairPoint := hpair mCut hm₀leCut hmCutPos ms hne hpositive hCutLeM
    j₁ j₂ hj₁ hj₂
  have hdenLe : M * Real.sqrt (mCut : ℝ) ≤ M * Real.sqrt M :=
    mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by
        change (mCut : ℝ) ≤ (pairBlockListMaxDuration ms : ℝ)
        exact_mod_cast hCutLeM))
      hMrealPos.le
  have hdenCut : 0 < M * Real.sqrt (mCut : ℝ) := mul_pos hMrealPos hrootCut
  have hpairNum : C₁ + C₂ * L ≤ C * (1 + L) := by
    dsimp [C]
    nlinarith [mul_nonneg hC₁.le (show 0 ≤ L by positivity),
      mul_nonneg hC₂.le (show 0 ≤ L by positivity)]
  have hpoint :
      |hypergeometricBlockListPairLaw ms j₁ j₂ -
          largeBlockGaussianListPairLaw mCut ms j₁ j₂| ≤
        C * (1 + L) / (M * Real.sqrt (mCut : ℝ)) := by
    calc
      _ ≤ C₁ / (M * Real.sqrt M) +
          C₂ * L / (M * Real.sqrt (mCut : ℝ)) := by simpa [L, M] using hpairPoint
      _ ≤ C₁ / (M * Real.sqrt (mCut : ℝ)) +
          C₂ * L / (M * Real.sqrt (mCut : ℝ)) := by
            exact add_le_add
              (div_le_div_of_nonneg_left hC₁.le hdenCut hdenLe) le_rfl
      _ = (C₁ + C₂ * L) / (M * Real.sqrt (mCut : ℝ)) := by ring
      _ ≤ C * (1 + L) / (M * Real.sqrt (mCut : ℝ)) :=
        div_le_div_of_nonneg_right hpairNum hdenCut.le
  have hdeltaNleLM : δ * (N : ℝ) ≤ L * M := by
    calc
      δ * (N : ℝ) = L * ((δ * (N : ℝ)) / L) := by
        field_simp [hL.ne']
      _ ≤ L * M := mul_le_mul_of_nonneg_left hMlower hL.le
  have hNM : (N : ℝ) / M ≤ L / δ := by
    apply (div_le_div_iff₀ hMrealPos hδ).2
    nlinarith [hdeltaNleLM]
  have hscaled : (N : ℝ) *
      |hypergeometricBlockListPairLaw ms j₁ j₂ -
        largeBlockGaussianListPairLaw mCut ms j₁ j₂| ≤
      C * (1 + L) * (L / δ) / Real.sqrt (mCut : ℝ) := by
    calc
      _ ≤ (N : ℝ) * (C * (1 + L) / (M * Real.sqrt (mCut : ℝ))) :=
        mul_le_mul_of_nonneg_left hpoint hNreal.le
      _ = C * (1 + L) * ((N : ℝ) / M) / Real.sqrt (mCut : ℝ) := by
        field_simp [hMne, hrootCut.ne']
      _ ≤ C * (1 + L) * (L / δ) / Real.sqrt (mCut : ℝ) := by
        apply div_le_div_of_nonneg_right _ hrootCut.le
        exact mul_le_mul_of_nonneg_left hNM (by positivity)
  have hLdiv : L / δ ≤ (K : ℝ) ^ 2 / δ :=
    div_le_div_of_nonneg_right hlengthR hδ.le
  have hLone : 1 + L ≤ 2 * (K : ℝ) ^ 2 := by
    have hK2one : 1 ≤ (K : ℝ) ^ 2 := one_le_pow₀ hKrealOne
    nlinarith [hlengthR, hK2one]
  have hnum1 : C * (1 + L) ≤ C * (2 * (K : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hLone hC.le
  have hnum2 : C * (1 + L) * (L / δ) ≤
      C * (2 * (K : ℝ) ^ 2) * ((K : ℝ) ^ 2 / δ) := by
    exact mul_le_mul hnum1 hLdiv (div_nonneg (by positivity) hδ.le) (by positivity)
  have hfinalBound :
      C * (1 + L) * (L / δ) / Real.sqrt (mCut : ℝ) ≤
        2 * C / (δ * (K : ℝ)) := by
    calc
      _ ≤ C * (2 * (K : ℝ) ^ 2) * ((K : ℝ) ^ 2 / δ) /
          Real.sqrt (mCut : ℝ) := div_le_div_of_nonneg_right hnum2 hrootCut.le
      _ = 2 * C / (δ * (K : ℝ)) := by
        rw [show (mCut : ℝ) = (K : ℝ) ^ 10 by simp [mCut, Nat.cast_pow], hrootCutEq]
        field_simp [hδ.ne', hKrealPos.ne']
  have hKthreshold : 2 * C / (δ * ε) < (K : ℝ) :=
    lt_of_lt_of_le hlogThresholdN hKlower
  have hstrict : 2 * C < (K : ℝ) * (δ * ε) :=
    (div_lt_iff₀ (mul_pos hδ hε)).1 hKthreshold
  have hfinish : 2 * C / (δ * (K : ℝ)) < ε := by
    apply (div_lt_iff₀ (mul_pos hδ hKrealPos)).2
    calc
      2 * C < (K : ℝ) * (δ * ε) := hstrict
      _ = ε * (δ * (K : ℝ)) := by ring
  calc
    _ ≤ C * (1 + L) * (L / δ) / Real.sqrt (mCut : ℝ) := hscaled
    _ ≤ 2 * C / (δ * (K : ℝ)) := hfinalBound
    _ < ε := hfinish

end Critical2DKPZ.SHF.Moments

end
