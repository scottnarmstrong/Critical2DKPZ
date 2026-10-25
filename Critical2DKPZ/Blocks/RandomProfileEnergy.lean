/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.ProfileEnergy
public import Critical2DKPZ.Blocks.FutureTerminal
import Mathlib.Tactic

/-! # Collision energies with random future terminal data -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Blocks

/-- Conditional slab annealing for an incoming reset profile, with integrability of the energy. -/
theorem random_resetProfile_sq_integral_energy (β : ℝ) (a n T b : ℕ) (hb : b ≤ a)
    (y : Site) (f : Disorder → Site → ℝ)
    (hfm : ∀ z, Measurable[Gaussian.disorderBlock (a + n) T] (fun ω => f ω z))
    (hf : ∀ z, MemLp (fun ω => f ω z) 4 disorderLaw) :
    Integrable (fun ω => resetProfileEnergy β a n b y (f ω)) disorderLaw ∧
    (∫ ω, (∑ w ∈ resetStartSupport b a y, discrepancyHeatKernel b a y w *
      (∑' z, pointToPoint β a n w z ω *
        (f ω z - Collision.terminalWalkMean (a + n) 0 (f ω)))) ^ 2 ∂disorderLaw) =
      ∫ ω, resetProfileEnergy β a n b y (f ω) ∂disorderLaw := by
  let f' : Disorder → Site → ℝ := fun ω z => f ω z -
    Collision.terminalWalkMean (a + n) 0 (f ω)
  have hm' (z) : Measurable[Gaussian.disorderBlock (a + n) T] (fun ω => f' ω z) :=
    (hfm z).sub (measurable_randomTerminalWalkMean (a + n) 0 f hfm)
  have hf' (z) : MemLp (fun ω => f' ω z) 4 disorderLaw :=
    (hf z).sub (memLp_randomTerminalWalkMean (a + n) 0 f 4 hf)
  have hann := finite_randomTerminalProfile_sq_integral_anneal β a n T
    (resetStartSupport b a y) (fun w => discrepancyHeatKernel b a y w) f' hm' hf'
  have heq (ω : Disorder) :
      (∫ η, (∑ w ∈ resetStartSupport b a y, discrepancyHeatKernel b a y w *
        (∑' z, pointToPoint β a n w z η * f' ω z)) ^ 2 ∂disorderLaw) =
        resetProfileEnergy β a n b y (f ω) :=
    finite_resetProfile_sq_integral β a n b hb y (f ω)
  exact ⟨hann.1.congr (Filter.Eventually.of_forall heq),
    hann.2.trans (integral_congr_ae (Filter.Eventually.of_forall heq))⟩

/-- Conditional slab annealing for an incoming heat profile; the deterministic term cancels. -/
theorem random_heatStartProfile_sq_integral_energy (β : ℝ) (a n T : ℕ)
    (f : Disorder → Site → ℝ)
    (hfm : ∀ z, Measurable[Gaussian.disorderBlock (a + n) T] (fun ω => f ω z))
    (hf : ∀ z, MemLp (fun ω => f ω z) 4 disorderLaw) :
    Integrable (fun ω => heatStartProfileEnergy β a n (f ω)) disorderLaw ∧
    (∫ ω, (∑ w ∈ Polymer.endpoints 0 a, srwKernel a w *
      (∑' z, pointToPoint β a n w z ω *
        (f ω z - Collision.terminalWalkMean (a + n) 0 (f ω)))) ^ 2 ∂disorderLaw) =
      ∫ ω, heatStartProfileEnergy β a n (f ω) ∂disorderLaw := by
  let f' : Disorder → Site → ℝ := fun ω z => f ω z -
    Collision.terminalWalkMean (a + n) 0 (f ω)
  have hm' (z) : Measurable[Gaussian.disorderBlock (a + n) T] (fun ω => f' ω z) :=
    (hfm z).sub (measurable_randomTerminalWalkMean (a + n) 0 f hfm)
  have hf' (z) : MemLp (fun ω => f' ω z) 4 disorderLaw :=
    (hf z).sub (memLp_randomTerminalWalkMean (a + n) 0 f 4 hf)
  have hann := finite_randomTerminalProfile_sq_integral_anneal β a n T
    (Polymer.endpoints 0 a) (srwKernel a) f' hm' hf'
  have heq (ω : Disorder) :
      (∫ η, (∑ w ∈ Polymer.endpoints 0 a, srwKernel a w *
        (∑' z, pointToPoint β a n w z η * f' ω z)) ^ 2 ∂disorderLaw) =
        heatStartProfileEnergy β a n (f ω) :=
    finite_heatStartProfile_sq_integral β a n (f ω)
  exact ⟨hann.1.congr (Filter.Eventually.of_forall heq),
    hann.2.trans (integral_congr_ae (Filter.Eventually.of_forall heq))⟩

end Critical2DKPZ.Blocks
