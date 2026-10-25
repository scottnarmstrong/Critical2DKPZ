/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordTestedEntrance
public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialSupport
import Mathlib.Tactic

/-! # The exact phase-correct tested two-particle entrance representation -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer DeltaBose
open scoped CompactlySupported Topology

/-- The full tested one-block word is exactly the initial-site average of the
phase-correct scaled future entrance. The factor is `N⁻²`, before the two
initial cell volumes are converted to continuum integrals. -/
theorem eventually_testedBlockWord_pairTwo_eq_sampledEntrance_all_times
    (ϑ : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ,
      testedBlockWord ϑ N s t φ [pairTwo] = ((N : ℝ)^2)⁻¹ *
        ∑ x ∈ Fintype.piFinset (fun i : Fin 2 =>
          ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst)),
          collisionEntrance N 1 (evenCeil (N * t) - evenCeil (N * s)) (x 0) (x 1)
            (pairTwoFutureSampleProfile ϑ N (evenCeil (N * t) - evenCeil (N * s)) φ x) := by
  filter_upwards [criticalBeta_spec ϑ, eventually_gt_atTop 0] with N hspec hN
  intro s t
  have hσ : sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N := hspec
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [testedBlockWord_pairTwo_testedTailEntranceExpansion, hσ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hx₀ : x 0 ∈ evenLattice := cellPairTest_initialSupport_even N (φ 0)
    ((Fintype.mem_piFinset.mp hx) 0)
  have hgrid := collisionEntrance_pairTwoFutureSampleProfile_grid ϑ hN
    (evenCeil (N * t) - evenCeil (N * s)) 1
    (evenCeil (N * t) - evenCeil (N * s))
    (even_evenCeil_sub (N * s) (N * t)) le_rfl φ x hx₀
  rw [hgrid, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hNr), one_mul]


end Critical2DKPZ.SHF.Moments
