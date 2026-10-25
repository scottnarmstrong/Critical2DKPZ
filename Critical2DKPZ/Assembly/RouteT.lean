/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.CriticalSHFExistence
public import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
public import Critical2DKPZ.SHF.Symmetries.DenseSHFAssembly
public import Critical2DKPZ.SHF.TimeContinuity.DiscreteModulusAssembly
public import Critical2DKPZ.SHF.TimeContinuity.LimitPassage
public import Critical2DKPZ.SHF.Tsai.KernelEstimateUniquenessClosure
public import Critical2DKPZ.SHF.Limit.FlatBound
public import Critical2DKPZ.SHF.Limit.PolymerSixthMoment
public import Critical2DKPZ.SHF.Flow.SmoothedProductCutoffTail
public import Critical2DKPZ.SHF.Flow.DenseSubsequenceProductLimit
public import Critical2DKPZ.SHF.Flow.DenseSHFSubsequenceLimits
public import Critical2DKPZ.SHF.Flow.ApproximateFlowFromSlabComparisons
public import Critical2DKPZ.SHF.Flow.PairingSlabComparison
public import Critical2DKPZ.SHF.Flow.MollifiedProductSlabComparison
public import Critical2DKPZ.SHF.Flow.MomentKernelTwoSemigroup
public import Critical2DKPZ.SHF.Moments.WordExpansionLimitBridges
public import Critical2DKPZ.SHF.Moments.WordLimitsFromPairAndLongWordLimits
public import Critical2DKPZ.SHF.Moments.LowReplicaLongWordLimits
public import Critical2DKPZ.SHF.Moments.WordDominationTestedGeometric
public import Critical2DKPZ.SHF.Moments.WordDominationNonpairSmall
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.NonGaussian.Inputs

/-! # Critical stochastic heat flow from fixed-word limits

The single-pair and three- and four-replica long-word limits imply polymer moment convergence, existence of a critical stochastic heat flow and its symmetries. -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.Assembly

open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai Critical2DKPZ.SHF.Existence
  Critical2DKPZ.SHF.Symmetries

/-- Tested collision words satisfy geometric domination for at most four replicas. -/
theorem wordGeometricDomination (ϑ : ℝ) (n : ℕ) (_hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SHF.Moments.WordGeometricDomination ϑ n :=
  fun hτ φ => SHF.Moments.testedBlockWord_geometric_le ϑ hn4 hτ φ

/-- The non-pair remainder vanishes for at most four replicas. -/
theorem nonpairRemainderSmall (ϑ : ℝ) (n : ℕ) (_hn : 1 ≤ n) (hn4 : n ≤ 4) :
    SHF.Moments.NonpairRemainderSmall ϑ n :=
  fun hτ φ => SHF.Moments.testedNonpairRemainder_small ϑ hn4 hτ φ

/-- Single-pair and three- and four-replica long-word limits give all word limits up to four replicas. -/
theorem wordLimits_of_pair_and_long_word_limits (hP : ∀ ϑ, SHF.Moments.PairTwoWordLimit ϑ)
    (hL3 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 3) (hL4 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 4)
    (ϑ : ℝ) (n : ℕ) (_hn : 1 ≤ n) (hn4 : n ≤ 4) : SHF.Moments.WordLimits ϑ n := by
  refine SHF.Moments.wordLimits_of ϑ (hP ϑ) ?_
  rcases Nat.lt_or_ge n 3 with h | h
  · exact SHF.Moments.longWordLimits_of_le_two ϑ (by omega)
  · rcases Nat.lt_or_ge n 4 with h' | h'
    · obtain rfl : n = 3 := by omega
      exact hL3 ϑ
    · obtain rfl : n = 4 := by omega
      exact hL4 ϑ

/-- Fixed-word limits imply convergence of polymer moments. -/
theorem polymerMomentLimit_of_word_limits (hP : ∀ ϑ, SHF.Moments.PairTwoWordLimit ϑ)
    (hL3 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 3) (hL4 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 4)
    (ϑ : ℝ) : SHF.Flow.PolymerMomentLimit ϑ :=
  SHF.Moments.polymerMomentLimit_of_wordStages ϑ (wordGeometricDomination ϑ)
    (nonpairRemainderSmall ϑ)
    (wordLimits_of_pair_and_long_word_limits hP hL3 hL4 ϑ)

/-- Fixed-word limits imply convergence of polymer moments at moving times. -/
theorem polymerMovingMomentLimit_of_word_limits (hP : ∀ ϑ, SHF.Moments.PairTwoWordLimit ϑ)
    (hL3 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 3) (hL4 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 4)
    (ϑ : ℝ) : SHF.TimeContinuity.PolymerMovingMomentLimit ϑ :=
  SHF.Moments.polymerMovingMomentLimit_of_wordStages ϑ (wordGeometricDomination ϑ)
    (nonpairRemainderSmall ϑ)
    (wordLimits_of_pair_and_long_word_limits hP hL3 hL4 ϑ)

/-- Flat polymer measures have uniformly bounded integrable sixth moments. -/
theorem flatSixthMomentBound (ϑ : ℝ) : SHF.Flow.FlatSixthMomentBound ϑ := by
  intro χ τ T hτ
  obtain ⟨C, hC⟩ := polymerMeasure_flat_sixth_moment_le ϑ χ (T := T) hτ
  exact ⟨C, hC.mono fun N hN s t hs hst ht =>
    ⟨integrable_flat_polymerMeasure_pow ϑ N s t χ 6, hN s t hs hst ht⟩⟩

/-- Fixed-word limits make every countable-time subsequential polymer limit a dense stochastic heat flow. -/
theorem isDenseSHF_of_isPolymerSubseqLimit_of_word_limits (hP : ∀ ϑ, SHF.Moments.PairTwoWordLimit ϑ)
    (hL3 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 3) (hL4 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 4)
    (ϑ : ℝ) (D : Set ℝ) (hD : D.Countable) (hD0 : ∀ s ∈ D, 0 ≤ s) (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z :=
  SHF.Flow.isDenseSHF_of_isPolymerSubseqLimit_of ϑ (polymerMomentLimit_of_word_limits hP hL3 hL4 ϑ)
    (flatSixthMomentBound ϑ) (SHF.Flow.momentKernel_two_semigroup _) D hD hD0 ψ hψ P Z hZ

/-- Fixed-word limits imply existence of a critical stochastic heat flow. -/
theorem exists_isCriticalSHF_of_word_limits (hP : ∀ ϑ, SHF.Moments.PairTwoWordLimit ϑ)
    (hL3 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 3) (hL4 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 4)
    (ϑ : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF ϑ P Z :=
  let ⟨Ω, mΩ, P, hP', Z, hZ, _⟩ := exists_isCriticalSHF_isDenseSHF_of ϑ
    (fun D hD hD0 ψ hψ => isDenseSHF_of_isPolymerSubseqLimit_of_word_limits hP hL3 hL4 ϑ D hD hD0 ψ hψ)
    (fun B hB D hDB hdense => isDenseSHF_fdd_eq _ B hB D hDB hdense)
  ⟨Ω, mΩ, P, hP', Z, hZ⟩

/-- Fixed-word limits imply the symmetries of every critical stochastic heat flow. -/
theorem shfSymmetriesAt_of_word_limits (hP : ∀ ϑ, SHF.Moments.PairTwoWordLimit ϑ)
    (hL3 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 3) (hL4 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 4)
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    LocalSobolev.ShfSymmetriesAt ϑ P Z :=
  shf_symmetries_of ϑ P Z hZ
    (fun _ B hB D hDB hdense => isDenseSHF_fdd_eq _ B hB D hDB hdense)
    (fun _ B hB D hDB hdense => isDenseSHF_fdd_eq _ B hB D hDB hdense)
    (fun ϑ' => exists_isCriticalSHF_isDenseSHF_of ϑ'
      (fun D hD hD0 ψ hψ =>
        isDenseSHF_of_isPolymerSubseqLimit_of_word_limits hP hL3 hL4 ϑ' D hD hD0 ψ hψ)
      (fun B hB D hDB hdense => isDenseSHF_fdd_eq _ B hB D hDB hdense))
    (fun Φ _ _ hτ => SHF.TimeContinuity.isCriticalSHF_L2_modulus_of ϑ P Z hZ Φ hτ
      (SHF.TimeContinuity.polymerMeasure_L2_modulus_of ϑ
        (polymerMovingMomentLimit_of_word_limits hP hL3 hL4 ϑ) Φ hτ))
    (fun s t δ x h₀ hs hst hδ =>
      SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ s t δ x h₀ hs hst hδ)

/-- Fixed-word limits imply the dense-time moment properties of every critical stochastic heat flow. -/
theorem denseSHFAt_of_word_limits (hP : ∀ ϑ, SHF.Moments.PairTwoWordLimit ϑ)
    (hL3 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 3) (hL4 : ∀ ϑ, SHF.Moments.LongWordLimits ϑ 4)
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    NonGaussian.DenseSHFAt ϑ P Z :=
  ((isCriticalSHF_iff_isDenseSHF_of ϑ
    (fun B hB D hDB hdense => isDenseSHF_fdd_eq _ B hB D hDB hdense)
    (exists_isCriticalSHF_isDenseSHF_of ϑ
      (fun D hD hD0 ψ hψ =>
        isDenseSHF_of_isPolymerSubseqLimit_of_word_limits hP hL3 hL4 ϑ D hD hD0 ψ hψ)
      (fun B hB D hDB hdense => isDenseSHF_fdd_eq _ B hB D hDB hdense)) P Z).mp hZ).2.2

end Critical2DKPZ.Assembly

end

end
