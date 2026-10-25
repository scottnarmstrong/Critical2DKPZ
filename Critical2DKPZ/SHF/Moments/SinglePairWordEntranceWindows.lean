/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceFormula
public import Critical2DKPZ.SHF.Moments.SinglePairWordStepIntegral
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialFull
import Mathlib.Tactic

/-! # Clock windows of the exact tested two-particle entrance representation -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter DeltaBose
open scoped CompactlySupported Topology

/-- A clock restriction and collision test in the exact finite first-entrance
representation of the two-particle word. -/
def pairTwoTestedEntranceWindow (ϑ : ℝ) (N L lo hi : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : ℝ × Plane → ℝ) : ℝ :=
  ((N : ℝ)^2)⁻¹ * ∑ x ∈ Fintype.piFinset (fun i : Fin 2 =>
    ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst)),
      collisionEntrance N lo hi (x 0) (x 1)
        (fun q => η q * pairTwoFutureSampleProfile ϑ N L φ x q)

/-- Every tested entrance window has an integrable initial step function, by
`pairTwoCutoffInitialStep_integrable_integral`, and
the same exact coefficient `1/16`. -/
theorem pairTwoTestedEntranceWindow_eq_initialIntegral
    (ϑ : ℝ) {N : ℕ} (hN : 0 < N) (L lo hi : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : ℝ × Plane → ℝ) :
    Integrable (pairTwoCutoffInitialStep ϑ N L lo hi φ η) ∧
      pairTwoTestedEntranceWindow ϑ N L lo hi φ η = (1 / 16 : ℝ) *
        ∫ p : Plane × Plane, pairTwoCutoffInitialStep ϑ N L lo hi φ η p := by
  have hi := pairTwoCutoffInitialStep_integrable_integral ϑ hN L lo hi φ η
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcoeff : ((N : ℝ)^2)⁻¹ = (1 / 16 : ℝ) * (4 / (N : ℝ))^2 := by
    field_simp
    norm_num
  refine ⟨hi.1, ?_⟩
  rw [pairTwoTestedEntranceWindow, hi.2, hcoeff]
  ring




end Critical2DKPZ.SHF.Moments
