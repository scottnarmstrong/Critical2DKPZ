/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.DiscrepancyTail
public import Critical2DKPZ.Blocks.RandomWalkMeans
public import Critical2DKPZ.Blocks.ChaosPropagation
import Critical2DKPZ.Blocks.DiscrepancyCovariance
import Mathlib.Tactic

/-! # Suffix masses after a prescribed last collision -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Blocks

/-- The suffix tested against the difference between a propagated collision and the absolute heat profile. -/
def resetTailMass (β : ℝ) (t : ℕ → ℕ) (b : ℕ) (y : Site) (u v : ℕ)
    (ω : Disorder) : ℝ :=
  Collision.terminalWalkMean (t (u - 1) - b) y (fun x => discrepancyTailMass β t u v x ω) -
    Collision.terminalWalkMean (t (u - 1)) 0 (fun x => discrepancyTailMass β t u v x ω)

/-- Every positive finite moment of a reset suffix exists. -/
theorem memLp_resetTailMass (β : ℝ) (t : ℕ → ℕ) (b : ℕ) (y : Site) (u v : ℕ)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    MemLp (resetTailMass β t b y u v) p disorderLaw :=
  (memLp_randomTerminalWalkMean (t (u - 1) - b) y
    (fun ω x => discrepancyTailMass β t u v x ω) p
    (fun x => memLp_discrepancyTailMass β t u v x p hp0 hp)).sub
      (memLp_randomTerminalWalkMean (t (u - 1)) 0
        (fun ω x => discrepancyTailMass β t u v x ω) p
        (fun x => memLp_discrepancyTailMass β t u v x p hp0 hp))


/-- The reset suffix is its deterministic reset kernel applied to the random suffix. -/
theorem resetTailMass_eq_kernelSum (β : ℝ) (t : ℕ → ℕ) (b : ℕ) (y : Site)
    (u v : ℕ) (ω : Disorder) :
    resetTailMass β t b y u v ω =
      ∑' x, discrepancyHeatKernel b (t (u - 1)) y x * discrepancyTailMass β t u v x ω := by
  have hfirst := Collision.summable_terminalWalkMean (t (u - 1) - b) y
    (fun x => discrepancyTailMass β t u v x ω)
  have hsecond := Collision.summable_terminalWalkMean (t (u - 1)) 0
    (fun x => discrepancyTailMass β t u v x ω)
  simp only [sub_zero] at hsecond
  unfold resetTailMass Collision.terminalWalkMean
  simp only [sub_zero]
  rw [← hfirst.tsum_sub hsecond]
  apply tsum_congr
  intro x
  exact (sub_mul _ _ _).symm

/-- The terminal data at the next block are centered against its absolute heat profile. -/
theorem discrepancyTailMass_eq_reset_terminal (β : ℝ) (t : ℕ → ℕ)
    {u v : ℕ} (huv : u < v) (x : Site) (ω : Disorder) :
    discrepancyTailMass β t u v x ω =
      ∑' y, pointToPoint β (t (u - 1)) (t u - t (u - 1)) x y ω *
        (discrepancyTailMass β t (u + 1) v y ω -
          Collision.terminalWalkMean (t u) 0 (fun z => discrepancyTailMass β t (u + 1) v z ω)) := by
  rw [discrepancyTailMass_leftFactor β t huv x ω, blockDiscrepancy_apply]

end Critical2DKPZ.Blocks
