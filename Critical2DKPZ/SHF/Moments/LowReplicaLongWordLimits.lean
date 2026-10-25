/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansionStageProps
public import Critical2DKPZ.SHF.Moments.WordLimitSpectators
import Mathlib.Tactic

/-! # Long collision words at low replica orders -/

@[expose] public section

open Filter
open scoped BigOperators CompactlySupported Topology

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose

/-- Collision words of length at least two have the tested continuum limit along moving time endpoints. -/
def LongWordLimits (ϑ : ℝ) (h : ℕ) : Prop :=
  ∀ {s t : ℝ}, 0 ≤ s → s < t → ∀ (sN tN : ℕ → ℝ), Tendsto sN atTop (𝓝 s) → Tendsto tN atTop (𝓝 t) →
    (∀ N, 0 ≤ sN N) → ∀ (φ : Fin h → C_c(Plane × Plane, ℝ)) (m : ℕ) (w : CollisionWord h (m + 2)),
      Tendsto (fun N => testedBlockWord ϑ N (sN N) (tN N) φ (List.ofFn w.1)) atTop
        (𝓝 (∫ x : Configuration h, ∫ y : Configuration h, (∏ i, φ i (x i, y i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) (List.ofFn w.1) (t - s) x y).toReal))

/-- No word of length two or more exists for at most two replicas. -/
theorem longWordLimits_of_le_two (ϑ : ℝ) {h : ℕ} (hh : h ≤ 2) : LongWordLimits ϑ h := by
  intro s t hs hst sN tN hsN htN hsN0 φ m w
  cases h with
  | zero =>
      exact False.elim (collisionPair_impossible (by omega) (w.1 ⟨0, by omega⟩))
  | succ h =>
      cases h with
      | zero =>
          exact False.elim (collisionPair_impossible (by omega) (w.1 ⟨0, by omega⟩))
      | succ h =>
          cases h with
          | zero => exact isEmptyElim w
          | succ h => omega

end Critical2DKPZ.SHF.Moments

