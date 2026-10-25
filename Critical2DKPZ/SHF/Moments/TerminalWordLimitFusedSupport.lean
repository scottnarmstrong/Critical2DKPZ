/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedSites
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitPhase
import Mathlib.Tactic

/-! # Finite support and phases of the normalized fused lattice summand -/

@[expose] public noncomputable section

open scoped BigOperators CompactlySupported
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Diffusive representatives of the free lattice collision coordinates. -/
def wordFusedCoordinateRepresentative {h : ℕ} (N : ℕ) (α : CollisionPair h)
    (z : Site × (Spectator α → Site)) : FusedConfiguration α :=
  (latticeRepresentative N z.1, fun i => latticeRepresentative N (z.2 i))

/-- The spatially cutoff normalized summand as a function of free lattice
coordinates, before their cell interpolation. -/
def wordFusedSpatialSummand {h : ℕ} (N : ℕ) (β : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (n s r : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ)
    (z : (Site × (Spectator α → Site)) × (Site × (Spectator α → Site))) : ℝ :=
  χ (wordFusedCoordinateRepresentative N α z.1, wordFusedCoordinateRepresentative N α z.2) *
    wordConsScaledSummand N β α w n s r x (wordFusedSiteEmbedding α z.1)
      (wordFusedSiteEmbedding α z.2) Ψ

/-- Every nonzero normalized first-letter summand has reachable entrance
and run endpoints. Normalization and terminal testing cannot enlarge support. -/
theorem wordConsScaledSummand_nonzero_reachable {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ)
    (x u v : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (hne : wordConsScaledSummand N β α w n s r x u v Ψ ≠ 0) :
    u ∈ collisionWordConfigurationEndpointSet s x ∧ v ∈ collisionWordConfigurationEndpointSet r u := by
  constructor
  · by_contra hu
    exact hne (by simp only [wordConsScaledSummand,
      collisionWord_freeProduct_zero_of_not_endpoints s x u hu, mul_zero, zero_mul])
  · by_contra hv
    exact hne (by simp only [wordConsScaledSummand,
      collisionWord_runFactor_zero_of_not_endpoints β α r u v hv, mul_zero, zero_mul])

/-- The two reachable states have the phases for their respective remaining
terminal clocks, including odd entrance and run durations. -/
theorem wordConsScaledSummand_nonzero_phases {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ) (hfit : s + r ≤ n)
    (x u v : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (hx : ∀ i, Even (x i 0 + x i 1 + (n : ℤ)))
    (hne : wordConsScaledSummand N β α w n s r x u v Ψ ≠ 0) :
    (∀ i, Even (u i 0 + u i 1 + ((n - s : ℕ) : ℤ))) ∧
      (∀ i, Even (v i 0 + v i 1 + ((n - s - r : ℕ) : ℤ))) := by
  obtain ⟨hu, hv⟩ := wordConsScaledSummand_nonzero_reachable N β α w n s r x u v Ψ hne
  refine ⟨?_, word_recursion_terminal_phase n s r hfit x u v hx hu hv⟩
  intro i
  have hp := hx i
  have hs := endpoints_accessible_phase s (x i) (u i) (Fintype.mem_piFinset.mp hu i)
  rw [Int.even_iff] at hp hs ⊢
  simp only [Pi.sub_apply] at hs
  omega

/-- The fused normalized summand has finite support without any support or
regularity assumption on the terminal profile. -/
theorem finite_support_wordFusedSpatialSummand {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    (Function.support (wordFusedSpatialSummand N β α w n s r x Ψ χ)).Finite := by
  classical
  let D := (collisionWordConfigurationEndpointSet s x).biUnion fun u =>
    ({u} ×ˢ collisionWordConfigurationEndpointSet r u)
  let E := fun z : (Site × (Spectator α → Site)) × (Site × (Spectator α → Site)) =>
    (wordFusedSiteEmbedding α z.1, wordFusedSiteEmbedding α z.2)
  have hE : Function.Injective E := by
    intro p q hpq
    exact Prod.ext ((wordFusedSiteEmbedding_injective α) (congrArg Prod.fst hpq))
      ((wordFusedSiteEmbedding_injective α) (congrArg Prod.snd hpq))
  apply (D.finite_toSet.preimage hE.injOn).subset
  intro z hz
  have hterm : wordConsScaledSummand N β α w n s r x (wordFusedSiteEmbedding α z.1)
      (wordFusedSiteEmbedding α z.2) Ψ ≠ 0 := (mul_ne_zero_iff.mp hz).2
  obtain ⟨hu, hv⟩ := wordConsScaledSummand_nonzero_reachable N β α w n s r x _ _ Ψ hterm
  exact Finset.mem_biUnion.mpr ⟨_, hu, Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, hv⟩⟩

end Critical2DKPZ.SHF.Moments
