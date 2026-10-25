/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSamplePotential
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSampleTail
import Mathlib.Tactic

/-! # Fused representatives for spatial cutoffs in the moving-word limit -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The continuum representative of a phase-sampled collision configuration,
with the collision center stored once. -/
def wordFusedPhaseRepresentative {h : ℕ} (N k : ℕ) (α : CollisionPair h)
    (v : FusedConfiguration α) : FusedConfiguration α :=
  (latticeRepresentative N (pairTwoFutureSampleSite N k v.1),
    fun i => latticeRepresentative N (pairTwoFutureSampleSite N k (v.2 i)))

/-- Embedding the fused representative gives the representatives of the
sampled lattice coordinates. -/
theorem collisionEmbedding_wordFusedPhaseRepresentative {h : ℕ}
    (N k : ℕ) (α : CollisionPair h) (v : FusedConfiguration α) (i : Fin h) :
    collisionEmbedding α (wordFusedPhaseRepresentative N k α v) i =
      latticeRepresentative N (wordCollisionPhaseSample N k α v i) := by
  unfold collisionEmbedding wordFusedPhaseRepresentative wordCollisionPhaseSample
  split_ifs <;> rfl

/-- Every fused representative is measurable. -/
theorem measurable_wordFusedPhaseRepresentative {h : ℕ}
    (N k : ℕ) (α : CollisionPair h) : Measurable (wordFusedPhaseRepresentative N k α) := by
  have hs : Measurable (fun y : Plane => latticeRepresentative N (pairTwoFutureSampleSite N k y)) :=
    (measurable_of_countable (latticeRepresentative N)).comp
      (((measurable_latticePoint N).comp (measurable_id.sub_const _)).add_const _)
  exact (hs.comp measurable_fst).prodMk
    (Measurable.of_eval (fun i => hs.comp ((measurable_pi_apply i).comp measurable_snd)))

/-- Fused sampling has the same mesh error as each of its coordinates. -/
theorem norm_wordFusedPhaseRepresentative_sub_le {h N : ℕ} (hN : 0 < N)
    (k : ℕ) (α : CollisionPair h) (v : FusedConfiguration α) :
    ‖wordFusedPhaseRepresentative N k α v - v‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
  rw [Prod.norm_def, max_le_iff]
  constructor
  · simpa only [wordFusedPhaseRepresentative, Prod.fst_sub, norm_sub_rev] using
      norm_sub_pairTwoFutureSampleSite_le hN k v.1
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    simpa only [wordFusedPhaseRepresentative, Prod.snd_sub, Pi.sub_apply, norm_sub_rev] using
      norm_sub_pairTwoFutureSampleSite_le hN k (v.2 i)

/-- Arbitrarily varying phase clocks do not affect the fused continuum limit. -/
theorem tendsto_wordFusedPhaseRepresentative {h : ℕ} (kN : ℕ → ℕ)
    (α : CollisionPair h) (v : FusedConfiguration α) :
    Tendsto (fun N => wordFusedPhaseRepresentative N (kN N) α v) atTop (𝓝 v) := by
  exact (tendsto_pairTwoFutureSampleSite kN _ _ tendsto_const_nhds).prodMk_nhds
    (tendsto_pi_nhds.2 fun i => tendsto_pairTwoFutureSampleSite kN _ _ tendsto_const_nhds)

end Critical2DKPZ.SHF.Moments
