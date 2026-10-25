/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureSampling
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.Tactic

/-! # Phase-correct sampling of collision configurations -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- Sample a collision configuration by sampling its center once and each
spectator once; the two collision coordinates remain identical. -/
def wordCollisionPhaseSample {h : ℕ} (N k : ℕ) (α : CollisionPair h)
    (z : FusedConfiguration α) : Fin h → Site := fun i =>
  if hi : i = α.1.1 ∨ i = α.1.2 then pairTwoFutureSampleSite N k z.1
  else pairTwoFutureSampleSite N k (z.2 ⟨i, not_or.mp hi⟩)

/-- Collision sampling is measurable in the fused center and spectators. -/
theorem measurable_wordCollisionPhaseSample {h : ℕ} (N k : ℕ) (α : CollisionPair h) :
    Measurable (wordCollisionPhaseSample N k α) := by
  have hsample : Measurable (pairTwoFutureSampleSite N k) :=
    ((measurable_latticePoint N).comp (measurable_id.sub_const _)).add_const _
  apply Measurable.of_eval
  intro i
  unfold wordCollisionPhaseSample
  split_ifs
  · exact hsample.comp measurable_fst
  · exact hsample.comp ((measurable_pi_apply _).comp measurable_snd)

/-- The collision pair is exactly coincident at every lattice scale. -/
theorem wordCollisionPhaseSample_pair {h : ℕ} (N k : ℕ) (α : CollisionPair h)
    (z : FusedConfiguration α) :
    wordCollisionPhaseSample N k α z α.1.1 = wordCollisionPhaseSample N k α z α.1.2 := by
  simp [wordCollisionPhaseSample]

/-- All sampled collision coordinates have the same terminal phase. -/
theorem wordCollisionPhaseSample_phase {h : ℕ} (N k : ℕ) (α : CollisionPair h)
    (z : FusedConfiguration α) (i : Fin h) :
    Even (wordCollisionPhaseSample N k α z i 0 + wordCollisionPhaseSample N k α z i 1 + (k : ℤ)) := by
  unfold wordCollisionPhaseSample
  split_ifs <;> exact pairTwoFutureSampleSite_phase N k _

/-- The sampled configuration converges coordinatewise to the collision embedding, including its duplicated center coordinates. -/
theorem tendsto_wordCollisionPhaseSample {h : ℕ} (kN : ℕ → ℕ) (α : CollisionPair h)
    (z : FusedConfiguration α) (i : Fin h) :
    Tendsto (fun N => latticeRepresentative N (wordCollisionPhaseSample N (kN N) α z i))
      atTop (𝓝 (collisionEmbedding α z i)) := by
  unfold wordCollisionPhaseSample collisionEmbedding
  split_ifs <;> exact tendsto_pairTwoFutureSampleSite kN _ _ tendsto_const_nhds

end Critical2DKPZ.SHF.Moments
