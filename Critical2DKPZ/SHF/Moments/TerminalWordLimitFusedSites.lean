/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedCells
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSummand
import Mathlib.Tactic

/-! # Exact reindexing of lattice collision sums by free coordinates -/

@[expose] public noncomputable section

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Duplicate the center of a lattice collision coordinate vector. -/
def wordFusedSiteEmbedding {h : ℕ} (α : CollisionPair h)
    (z : Site × (Spectator α → Site)) : LatticeConfiguration h := fun i =>
  if hi : i = α.1.1 ∨ i = α.1.2 then z.1 else z.2 ⟨i, not_or.mp hi⟩

/-- Read the center and spectators from a lattice configuration. -/
def wordFusedSiteProjection {h : ℕ} (α : CollisionPair h)
    (u : LatticeConfiguration h) : Site × (Spectator α → Site) :=
  (u α.1.1, fun i => u i.1)


/-- Projection is a left inverse of the lattice collision embedding. -/
theorem wordFusedSiteProjection_embedding {h : ℕ} (α : CollisionPair h)
    (z : Site × (Spectator α → Site)) :
    wordFusedSiteProjection α (wordFusedSiteEmbedding α z) = z := by
  apply Prod.ext
  · simp [wordFusedSiteProjection, wordFusedSiteEmbedding]
  · funext i
    simp [wordFusedSiteProjection, wordFusedSiteEmbedding, i.2.1, i.2.2]

/-- On a collision, projection loses no lattice coordinate. -/
theorem wordFusedSiteEmbedding_projection {h : ℕ} (α : CollisionPair h)
    (u : LatticeConfiguration h) (hu : u α.1.1 = u α.1.2) :
    wordFusedSiteEmbedding α (wordFusedSiteProjection α u) = u := by
  funext i
  unfold wordFusedSiteEmbedding wordFusedSiteProjection
  split_ifs with hi
  · rcases hi with rfl | rfl
    · rfl
    · exact hu
  · rfl

/-- Free collision coordinates embed injectively. -/
theorem wordFusedSiteEmbedding_injective {h : ℕ} (α : CollisionPair h) :
    Function.Injective (wordFusedSiteEmbedding α) := by
  have he : Function.LeftInverse (wordFusedSiteProjection α) (wordFusedSiteEmbedding α) :=
    wordFusedSiteProjection_embedding α
  exact he.injective

/-- Sampling then embedding agrees with the canonical phase-correct sampled
full lattice configuration. -/
theorem wordFusedSiteEmbedding_sample {h : ℕ} (N k : ℕ) (α : CollisionPair h)
    (v : FusedConfiguration α) :
    wordFusedSiteEmbedding α (wordFusedSiteSample N k α v) = wordCollisionPhaseSample N k α v := by
  funext i
  unfold wordFusedSiteEmbedding wordFusedSiteSample wordCollisionPhaseSample
  split_ifs <;> rfl

/-- A sum supported on a collision is exactly a sum over its center and
spectators. This uses only the support condition, not summability. -/
theorem tsum_collision_eq_fusedSites {h : ℕ} (α : CollisionPair h)
    (F : LatticeConfiguration h → ℝ)
    (hF : ∀ u, u α.1.1 ≠ u α.1.2 → F u = 0) :
    (∑' z : Site × (Spectator α → Site), F (wordFusedSiteEmbedding α z)) = ∑' u, F u := by
  apply (wordFusedSiteEmbedding_injective α).tsum_eq
  intro u hu
  have hpair : u α.1.1 = u α.1.2 := by
    by_contra hne
    exact hu (hF u hne)
  exact ⟨wordFusedSiteProjection α u, wordFusedSiteEmbedding_projection α u hpair⟩

/-- Two collision-supported lattice sums are jointly reindexed by their
incoming and outgoing free coordinates, in their original order. -/
theorem tsum_collision_pair_eq_fusedSites {h : ℕ} (α : CollisionPair h)
    (F : LatticeConfiguration h → LatticeConfiguration h → ℝ)
    (hleft : ∀ u v, u α.1.1 ≠ u α.1.2 → F u v = 0)
    (hright : ∀ u v, v α.1.1 ≠ v α.1.2 → F u v = 0) :
    (∑' p : Site × (Spectator α → Site), ∑' q : Site × (Spectator α → Site),
      F (wordFusedSiteEmbedding α p) (wordFusedSiteEmbedding α q)) =
      ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h, F u v := by
  calc
    _ = ∑' p : Site × (Spectator α → Site), ∑' v : LatticeConfiguration h,
        F (wordFusedSiteEmbedding α p) v := by
      apply tsum_congr
      intro p
      exact tsum_collision_eq_fusedSites α _ (fun v hv => hright _ v hv)
    _ = _ := tsum_collision_eq_fusedSites α (fun u => ∑' v : LatticeConfiguration h, F u v)
      (fun u hu => by
        calc
          (∑' v : LatticeConfiguration h, F u v) = ∑' _v : LatticeConfiguration h, (0 : ℝ) :=
            tsum_congr (fun v => hleft u v hu)
          _ = 0 := tsum_zero)

end Critical2DKPZ.SHF.Moments
