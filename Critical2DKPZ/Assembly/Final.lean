/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Assembly.RouteT
public import Critical2DKPZ.SHF.Moments.SinglePairWordLimit
public import Critical2DKPZ.SHF.Moments.LongWordLimitTransfer
public import Critical2DKPZ.SHF.Moments.WordLimitDomination
public import Critical2DKPZ.SHF.Moments.TerminalWordLimit

/-! # Existence and symmetries of the critical stochastic heat flow

Fixed-word polymer limits yield the existence, symmetries and dense-time moment properties of the critical stochastic heat flow. -/

@[expose] public section

noncomputable section

open MeasureTheory

universe u

namespace Critical2DKPZ.Assembly

/-- Long-word limits hold for at most four replicas. -/
theorem longWordLimits (ϑ : ℝ) {h : ℕ} (hh : h ≤ 4) : SHF.Moments.LongWordLimits ϑ h :=
  SHF.Moments.longWordLimits_of_moving_terminal_limits ϑ (SHF.Moments.wordPotentialDomination ϑ hh)
    (fun w hw _ hτ nN hn xN x hx hphase hsep ψ =>
      SHF.Moments.tendsto_wordTerminalTest_of_potentialDomination ϑ
        (SHF.Moments.wordPotentialDomination ϑ hh) w hw hτ nN hn xN x hx hphase hsep ψ)

/-- A critical stochastic heat flow exists for every parameter. -/
theorem exists_isCriticalSHF (ϑ : ℝ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF ϑ P Z :=
  exists_isCriticalSHF_of_word_limits SHF.Moments.pairTwoWordLimit
    (fun ϑ => longWordLimits ϑ (by norm_num)) (fun ϑ => longWordLimits ϑ le_rfl) ϑ

/-- Every critical stochastic heat flow has the stated translation, scaling and reversal symmetries. -/
theorem shfSymmetriesAt (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) : LocalSobolev.ShfSymmetriesAt ϑ P Z :=
  shfSymmetriesAt_of_word_limits SHF.Moments.pairTwoWordLimit
    (fun ϑ => longWordLimits ϑ (by norm_num)) (fun ϑ => longWordLimits ϑ le_rfl)
    ϑ P Z hZ

/-- Every critical stochastic heat flow satisfies the dense-time moment properties. -/
theorem denseSHFAt (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) : NonGaussian.DenseSHFAt ϑ P Z :=
  denseSHFAt_of_word_limits SHF.Moments.pairTwoWordLimit
    (fun ϑ => longWordLimits ϑ (by norm_num)) (fun ϑ => longWordLimits ϑ le_rfl)
    ϑ P Z hZ

end Critical2DKPZ.Assembly

end

end
