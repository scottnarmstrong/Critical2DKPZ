/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansion
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries

/-! Geometric domination, negligible remainders and individual word limits describe the collision-word expansion. -/

@[expose] public section

open Filter
open scoped BigOperators CompactlySupported Topology

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

/-- The absolute tested word sums admit a uniform geometric majorant on compact positive-time windows. -/
def WordGeometricDomination (ϑ : ℝ) (h : ℕ) : Prop :=
  ∀ {τ T : ℝ}, 0 < τ → ∀ φ : Fin h → C_c(Plane × Plane, ℝ),
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧ ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
      ∀ m : ℕ, ∑ w : CollisionWord h m, |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ C * ρ ^ m

/-- Tested non-pair remainders vanish uniformly on compact time windows bounded away from zero duration. -/
def NonpairRemainderSmall (ϑ : ℝ) (h : ℕ) : Prop :=
  ∀ {τ T : ℝ}, 0 < τ → ∀ φ : Fin h → C_c(Plane × Plane, ℝ), ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
    ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T → |testedNonpairRemainder ϑ N s t φ| ≤ ε

/-- Each collision word has the tested continuum limit along moving time endpoints. -/
def WordLimits (ϑ : ℝ) (h : ℕ) : Prop :=
  ∀ {s t : ℝ}, 0 ≤ s → s < t → ∀ (sN tN : ℕ → ℝ), Tendsto sN atTop (𝓝 s) → Tendsto tN atTop (𝓝 t) →
    (∀ N, 0 ≤ sN N) → ∀ (φ : Fin h → C_c(Plane × Plane, ℝ)) (m : ℕ) (w : CollisionWord h m),
      Tendsto (fun N => testedBlockWord ϑ N (sN N) (tN N) φ (List.ofFn w.1)) atTop
        (𝓝 (∫ x : Configuration h, ∫ y : Configuration h, (∏ i, φ i (x i, y i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) (List.ofFn w.1) (t - s) x y).toReal))

end Critical2DKPZ.SHF.Moments

