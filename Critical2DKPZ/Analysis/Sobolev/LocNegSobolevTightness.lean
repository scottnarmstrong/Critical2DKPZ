/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevRellich
public import Critical2DKPZ.Analysis.Sobolev.LocNegSobolevPairing
public import Critical2DKPZ.Analysis.Sobolev.CountableEnergyTightness

/-! # Tightness of local negative Sobolev tuples from expected stronger energies -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Analysis.Sobolev

/-- Finite tuples of local negative Sobolev distributions of order `s > 0` have tight laws if their expected energies of order `s/2` are uniformly bounded along the countable cutoff exhaustion. -/
theorem isTightMeasureSet_of_expected_localEnergy (s : ℝ) (hs : 0 < s) {k : ℕ}
    (μ : ℕ → Measure (Fin k → LocNegSobolevCarrier s)) [∀ n, IsProbabilityMeasure (μ n)]
    (hE : ∀ (i : Fin k) (m : ℕ), ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ n : ℕ,
      ∫⁻ x, localNegSobolevSq (s / 2) (x i).1.toDistr (localizer m) ∂(μ n) ≤ M) :
    IsTightMeasureSet (Set.range μ) := by
  let F : (Fin k × ℕ) → (Fin k → LocNegSobolevCarrier s) → ℝ≥0∞ :=
    fun j x => localNegSobolevSq (s / 2) (x j.1).1.toDistr (localizer j.2)
  apply isTightMeasureSet_of_expected_countable_energies μ F
  · intro j
    exact (measurable_localEnergy_locNegSobolevCarrier s (s / 2) (localizer j.2)).comp
      (measurable_pi_apply j.1)
  · intro K hK
    have hset : {x : Fin k → LocNegSobolevCarrier s | ∀ j, F j x ≤ K j} =
        {x | ∀ i, x i ∈ {T : LocNegSobolevCarrier s |
          ∀ m, localNegSobolevSq (s / 2) T.1.toDistr (localizer m) ≤ K (i, m)}} := by
      ext x
      simp only [Set.mem_ofPred_eq, Prod.forall, F]
    rw [hset]
    exact isCompact_pi_infinite (fun i => isCompact_localizer_energy_sublevels
      (by linarith : 0 ≤ s / 2) (by linarith : s / 2 < s)
      (fun m => K (i, m)) (fun m => hK (i, m)))
  · exact fun j => hE j.1 j.2

end Critical2DKPZ.Analysis.Sobolev

end
