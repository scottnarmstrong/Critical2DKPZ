/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredChainLimsupClosure
public import Critical2DKPZ.SHF.Tsai.CenteredMomentKernelFourBound
public import Critical2DKPZ.SHF.Tsai.HybridStepClosure
public import Critical2DKPZ.SHF.Tsai.DenseLawClosure
public import Critical2DKPZ.SHF.Tsai.FiniteDimensionalLaws

/-! # Dense-time uniqueness on compact intervals

On a dense subset of a compact time interval, the first four delta-Bose moment formulas,
approximate composition, and independent increments determine all finite-dimensional
increment laws. The four-particle centered estimate gives superlinear control of hybrid
expectation differences.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal CompactlySupported
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

universe u v

/-- The centered-kernel and conjugated weighted moment-semigroup bounds control hybrid expectation increments. -/
theorem isDenseSHF_hybridValue_step_le_of_centered_bound
    (θ B : ℝ) (D : Set ℝ) (hD : D ⊆ Set.Icc 0 B)
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH)
    {p : ℝ≥0∞} (hp : 6 < p) (hp' : p ≠ ⊤)
    (hcentered : ∀ {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤) {a : ℝ}
      (ha : 0 < a) (T : ℝ), ∃ c : ℝ, ∀ t : ℝ, 0 < t → t ≤ T →
      ∀ F G : Configuration 4 → ℝ,
        MemLp (fun x => F x * Real.exp (a * configL1Norm x)) p →
        MemLp (fun y => G y * Real.exp (a * configL1Norm y)) p →
        Integrable (fun xy : Configuration 4 × Configuration 4 =>
          F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2) ∧
        |∫ xy : Configuration 4 × Configuration 4,
            F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2| ≤
          c * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
            (eLpNorm (fun x => F x * Real.exp (a * configL1Norm x)) p).toReal *
            (eLpNorm (fun y => G y * Real.exp (a * configL1Norm y)) p).toReal) :
    ∃ C : ℝ, ∀ a ∈ D, ∀ b ∈ D, s ≤ a → a < b → b ≤ t → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ ℓ in Filter.atTop,
        |hybridValue P P' Z Z' s t g g' H a ℓ -
          hybridValue P P' Z Z' s t g g' H b ℓ| ≤
            C * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε := by
  have hlimsup := limsup_integral_chain_centered_le_of_kernel_bounds
    θ B hp hp' g g' hcentered
  exact isDenseSHF_hybridValue_step_le_of_limsup_integral_chain_centered_le
    θ B D hD P P' Z Z' hZ hZ' hs ht hst g g' H hH CH hCH hp hp' hlimsup

/-- A four-particle centered-kernel bound gives equality of single-interval laws for dense-time flows on a compact time interval. -/
theorem isDenseSHF_law_eq_of_centered_bound
    (θ B : ℝ) (hB : 0 < B) (D : Set ℝ) (hD : D ⊆ Set.Icc 0 B)
    (hdense : Set.Icc 0 B ⊆ closure D)
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    (hcentered : ∀ {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤) {a : ℝ}
      (ha : 0 < a) (T : ℝ), ∃ c : ℝ, ∀ t : ℝ, 0 < t → t ≤ T →
        ∀ F G : Configuration 4 → ℝ,
          MemLp (fun x => F x * Real.exp (a * configL1Norm x)) p →
          MemLp (fun y => G y * Real.exp (a * configL1Norm y)) p →
          Integrable (fun xy : Configuration 4 × Configuration 4 =>
            F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2) ∧
          |∫ xy : Configuration 4 × Configuration 4,
              F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2| ≤
            c * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
              (eLpNorm (fun x => F x * Real.exp (a * configL1Norm x)) p).toReal *
              (eLpNorm (fun y => G y * Real.exp (a * configL1Norm y)) p).toReal) :
    P.map (Z s t) = P'.map (Z' s t) := by
  have hstep : ∀ {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
      (H : (Fin m → ℝ) → ℝ) (_hH : ContDiff ℝ 4 H) (CH : ℝ)
      (_hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH)
      {p : ℝ≥0∞} (_hp : 6 < p) (_hp' : p ≠ ⊤),
      ∃ C : ℝ, ∀ a ∈ D, ∀ b ∈ D, s ≤ a → a < b → b ≤ t → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ ℓ in Filter.atTop,
          |hybridValue P P' Z Z' s t g g' H a ℓ -
            hybridValue P P' Z Z' s t g g' H b ℓ| ≤
              C * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε := by
    intro m r g g' H hH CH hCH p hp hp'
    exact isDenseSHF_hybridValue_step_le_of_centered_bound
      θ B D hD P P' Z Z' hZ hZ' hs ht hst g g' H hH CH hCH hp hp'
      hcentered
  exact isDenseSHF_law_eq_of_hybridValue_step_le θ B hB D hD hdense
    P P' Z Z' hZ hZ' hs ht hst hstep

/-- Two dense-time flows satisfying the same first four delta-Bose moment formulas, approximate composition, and independent increments have equal single-interval laws on a compact time interval. -/
theorem isDenseSHF_law_eq (θ B : ℝ) (hB : 0 < B) (D : Set ℝ)
    (hD : D ⊆ Set.Icc 0 B) (hdense : Set.Icc 0 B ⊆ closure D)
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t) :
    P.map (Z s t) = P'.map (Z' s t) := by
  apply isDenseSHF_law_eq_of_centered_bound θ B hB D hD hdense
    P P' Z Z' hZ hZ' hs ht hst
  intro p hp hp' a ha T
  exact centeredMomentKernel_four_le θ hp hp' ha T

/-- On a dense time set in a compact interval, two flows satisfying the same first four delta-Bose moment formulas, approximate composition, and independent increments have equal finite-dimensional increment laws, the compact-interval form of Tsai (2024), Theorem 1.9. -/
theorem isDenseSHF_fdd_eq (θ B : ℝ) (hB : 0 < B) (D : Set ℝ)
    (hD : D ⊆ Set.Icc 0 B) (hdense : Set.Icc 0 B ⊆ closure D)
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    (k : ℕ) (s t : Fin k → ℝ)
    (hst : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) :
    P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω) := by
  exact isDenseSHF_fdd_eq_of_law_eq θ D P P' Z Z' hZ hZ'
    (fun s hs t ht hst =>
      isDenseSHF_law_eq θ B hB D hD hdense P P' Z Z' hZ hZ' hs ht hst)
    k s t hst

end Critical2DKPZ.SHF.Tsai

end
