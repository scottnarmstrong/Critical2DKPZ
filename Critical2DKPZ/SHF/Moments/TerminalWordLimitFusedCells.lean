/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFinitePhaseCells
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedPairEquiv
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSampling
public import Critical2DKPZ.SHF.DeltaBose.CollisionScaling
import Mathlib.Tactic

/-! # Exact joint collision-space cell integration -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- Sample the free collision coordinates, storing the center only once. -/
def wordFusedSiteSample {h : ℕ} (N k : ℕ) (α : CollisionPair h)
    (v : FusedConfiguration α) : Site × (Spectator α → Site) :=
  (pairTwoFutureSampleSite N k v.1, fun i => pairTwoFutureSampleSite N k (v.2 i))

/-- Independent phase clocks on the incoming and outgoing free coordinates. -/
def wordFusedPairSiteSample {h : ℕ} (N k l : ℕ) (α : CollisionPair h)
    (p : FusedConfiguration α × FusedConfiguration α) :=
  (wordFusedSiteSample N k α p.1, wordFusedSiteSample N l α p.2)

/-- A finitely supported joint collision-space step has exactly two fused
cell-volume factors. Incoming and outgoing phases may differ. -/
theorem integrable_integral_fusedPairPhaseStep {h N : ℕ} (hN : 0 < N)
    (α : CollisionPair h) (k l : ℕ)
    (S : Finset ((Site × (Spectator α → Site)) × (Site × (Spectator α → Site))))
    (hS : ∀ z ∈ S,
      (Even (z.1.1 0 + z.1.1 1 + (k : ℤ)) ∧
        ∀ i, Even (z.1.2 i 0 + z.1.2 i 1 + (k : ℤ))) ∧
      (Even (z.2.1 0 + z.2.1 1 + (l : ℤ)) ∧
        ∀ i, Even (z.2.2 i 0 + z.2.2 i 1 + (l : ℤ))))
    (G : ((Site × (Spectator α → Site)) × (Site × (Spectator α → Site))) → ℝ)
    (hzero : ∀ z ∉ S, G z = 0) :
    Integrable (fun p : FusedConfiguration α × FusedConfiguration α =>
      G (wordFusedPairSiteSample N k l α p)) ∧
      (∫ p : FusedConfiguration α × FusedConfiguration α,
        G (wordFusedPairSiteSample N k l α p)) =
          (4 / (N : ℝ)) ^ (2 * (h - 1)) * ∑ z ∈ S, G z := by
  classical
  let I := Option (Spectator α) ⊕ Option (Spectator α)
  let es := fusedPairSumMeasurableEquiv (Spectator α) Site
  let ep := fusedPairSumMeasurableEquiv (Spectator α) Plane
  let A := S.image es
  let G' : (I → Site) → ℝ := fun z => G (es.symm z)
  let K : I → ℕ := Sum.elim (fun _ => k) (fun _ => l)
  have hA : ∀ z ∈ A, ∀ i, Even (z i 0 + z i 1 + (K i : ℤ)) := by
    intro z hz i
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    rcases i with i | i <;> cases i with
    | none => first | exact (hS y hy).1.1 | exact (hS y hy).2.1
    | some j => first | exact (hS y hy).1.2 j | exact (hS y hy).2.2 j
  have hG' (z : I → Site) (hz : z ∉ A) : G' z = 0 := by
    apply hzero (es.symm z)
    intro hmem
    exact hz (Finset.mem_image.mpr ⟨es.symm z, hmem, es.apply_symm_apply z⟩)
  obtain ⟨hint, hi⟩ := integrable_integral_finitePhaseStep hN K A hA G' hG'
  have hsum : (∑ z ∈ A, G' z) = ∑ z ∈ S, G z := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro z hz
      exact congrArg G (es.symm_apply_apply z)
    · intro x hx y hy hxy
      exact es.injective hxy
  have he : MeasurePreserving ep := measurePreserving_fusedPairSumMeasurableEquiv (Spectator α) Plane
  let H : (I → Plane) → ℝ := fun x => G' (fun i => pairTwoFutureSampleSite N (K i) (x i))
  have hcomp : H ∘ ep = fun p : FusedConfiguration α × FusedConfiguration α =>
      G (wordFusedPairSiteSample N k l α p) := by
    rfl
  have hcard : Fintype.card I = 2 * (h - 1) := by
    dsimp only [I]
    rw [Fintype.card_sum, Fintype.card_option, card_spectator]
    have ha := α.2
    omega
  refine ⟨hcomp ▸ (he.integrable_comp_emb ep.measurableEmbedding).mpr hint, ?_⟩
  have heq := he.integral_comp' H
  change (∫ p, (H ∘ ep) p) = (∫ x, H x) at heq
  rw [hcomp, hi, hsum, hcard] at heq
  exact heq

end Critical2DKPZ.SHF.Moments
