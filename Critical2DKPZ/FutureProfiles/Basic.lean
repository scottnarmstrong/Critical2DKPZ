/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Basic

/-!
# Basic future-profile quantities

The seminorm and the block corrections used in the endpoint-profile comparison.
-/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks

/-- The deterministic-profile version of the squared conditional seminorm in equation (7.43). -/
def futureEnergy (β : ℝ) (a b : ℕ) (η : Site → ℝ) : ℝ :=
  ∫ ω, profileP2Fun β a b η (fun _ => 1) ω ^ 2 ∂disorderLaw

/-- The block-good event with its endpoint-ratio condition. -/
def profileGoodSet (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) : Set Disorder :=
  blockGoodSet β t r s ∩ {ω | |blockRatio β t r s ω - 1| ≤ 1 / 2}

/-- The sum of open correctors over a consecutive range of blocks. -/
def commonCorrection (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) (ω : Disorder) (y : Site) : ℝ :=
  ∑ u ∈ Finset.Icc r s, openCorrector β t u s ω y

/-- The ratio-weighted sum of open correctors over a consecutive range of blocks. -/
def weightedCorrection (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) (ω : Disorder) (y : Site) : ℝ :=
  ∑ u ∈ Finset.Icc r s, blockRatio β t r (u - 1) ω * openCorrector β t u s ω y

end Critical2DKPZ.FutureProfiles

end
