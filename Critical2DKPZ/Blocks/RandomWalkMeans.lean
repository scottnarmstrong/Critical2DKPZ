/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.FirstNoise
import Mathlib.Tactic

/-! # Walk means of random terminal profiles -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Blocks

/-- Walk averaging preserves a constant terminal profile. -/
theorem terminalWalkMean_const (n : ℕ) (w : Site) (c : ℝ) :
    Collision.terminalWalkMean n w (fun _ => c) = c := by
  rw [terminalWalkMean_walkSum, ← Finset.sum_mul, Polymer.sum_walkProbability, one_mul]

/-- Subtracting a constant commutes with walk averaging. -/
theorem terminalWalkMean_sub_const (n : ℕ) (w : Site) (f : Site → ℝ) (c : ℝ) :
    Collision.terminalWalkMean n w (fun x => f x - c) =
      Collision.terminalWalkMean n w f - c := by
  rw [terminalWalkMean_sub, terminalWalkMean_const]

/-- A finite walk mean preserves block measurability of random terminal data. -/
theorem measurable_randomTerminalWalkMean {m : MeasurableSpace Disorder}
    (n : ℕ) (w : Site) (f : Disorder → Site → ℝ)
    (hf : ∀ x, Measurable[m] (fun ω => f ω x)) :
    Measurable[m] (fun ω => Collision.terminalWalkMean n w (f ω)) := by
  let : MeasurableSpace Disorder := m
  have heq : (fun ω => Collision.terminalWalkMean n w (f ω)) =
      (fun ω => ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * f ω (walkPosition w s n)) := by
    funext ω
    exact terminalWalkMean_walkSum n w (f ω)
  rw [heq]
  exact Finset.measurable_sum _ fun s _ => (hf _).const_mul _

/-- A finite walk mean preserves every available moment of random terminal data. -/
theorem memLp_randomTerminalWalkMean (n : ℕ) (w : Site) (f : Disorder → Site → ℝ)
    (p : ℝ≥0∞) (hf : ∀ x, MemLp (fun ω => f ω x) p disorderLaw) :
    MemLp (fun ω => Collision.terminalWalkMean n w (f ω)) p disorderLaw := by
  have heq : (fun ω => Collision.terminalWalkMean n w (f ω)) =
      (fun ω => ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * f ω (walkPosition w s n)) := by
    funext ω
    exact terminalWalkMean_walkSum n w (f ω)
  rw [heq]
  exact memLp_finsetSum _ fun s _ => (hf _).const_mul _

end Critical2DKPZ.Blocks
