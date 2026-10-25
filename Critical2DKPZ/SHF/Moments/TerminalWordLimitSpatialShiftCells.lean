/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedCells
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialPhaseShift
import Mathlib.Tactic

/-! # Translated fused phase cells for spatial cutoff exhaustion -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- Coordinate parity shifts preserve both fused cell volumes and express the support condition through the shifted phases. -/
theorem integrable_integral_shifted_fusedPairPhaseStep {h N : ℕ} (hN : 0 < N)
    (α : CollisionPair h) (k l : ℕ) (a : Site × (Spectator α → Site))
    (G : ((Site × (Spectator α → Site)) × (Site × (Spectator α → Site))) → ℝ)
    (hG : (Function.support G).Finite)
    (hphase : ∀ z, G z ≠ 0 →
      (Even ((z.1.1 - a.1) 0 + (z.1.1 - a.1) 1 + (k : ℤ)) ∧
        ∀ i, Even ((z.1.2 i - a.2 i) 0 + (z.1.2 i - a.2 i) 1 + (k : ℤ))) ∧
      (Even ((z.2.1 - a.1) 0 + (z.2.1 - a.1) 1 + (l : ℤ)) ∧
        ∀ i, Even ((z.2.2 i - a.2 i) 0 + (z.2.2 i - a.2 i) 1 + (l : ℤ)))) :
    Integrable (fun p : FusedConfiguration α × FusedConfiguration α =>
      G (wordFusedPairSiteSample N k l α p + (a, a))) ∧
    (∫ p : FusedConfiguration α × FusedConfiguration α,
      G (wordFusedPairSiteSample N k l α p + (a, a))) =
      (4 / (N : ℝ)) ^ (2 * (h - 1)) * ∑' z, G z := by
  classical
  let H := fun z : ((Site × (Spectator α → Site)) × (Site × (Spectator α → Site))) =>
    G (z + (a, a))
  have hinj : Function.Injective
      (fun z : ((Site × (Spectator α → Site)) × (Site × (Spectator α → Site))) => z + (a, a)) :=
    (Equiv.addRight (a, a)).injective
  have hfinite : (Function.support H).Finite := hG.preimage hinj.injOn
  let S := hfinite.toFinset
  have hzero (z) (hz : z ∉ S) : H z = 0 := by
    by_contra hn
    exact hz (hfinite.mem_toFinset.mpr hn)
  have hS (z) (hz : z ∈ S) :
      (Even (z.1.1 0 + z.1.1 1 + (k : ℤ)) ∧
        ∀ i, Even (z.1.2 i 0 + z.1.2 i 1 + (k : ℤ))) ∧
      (Even (z.2.1 0 + z.2.1 1 + (l : ℤ)) ∧
        ∀ i, Even (z.2.2 i 0 + z.2.2 i 1 + (l : ℤ))) := by
    have hn : G (z + (a, a)) ≠ 0 := hfinite.mem_toFinset.mp hz
    have hp := hphase (z + (a, a)) hn
    simpa only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_sub_cancel_right] using hp
  obtain ⟨hi, he⟩ := integrable_integral_fusedPairPhaseStep hN α k l S hS H hzero
  have htsum : (∑' z, H z) = ∑' z, G z := (Equiv.addRight (a, a)).tsum_eq G
  have hsum : (∑ z ∈ S, H z) = ∑' z, G z := (tsum_eq_sum hzero).symm.trans htsum
  refine ⟨hi, ?_⟩
  exact he.trans (congrArg (fun q : ℝ => (4 / (N : ℝ)) ^ (2 * (h - 1)) * q) hsum)

end Critical2DKPZ.SHF.Moments
