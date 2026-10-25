/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedSupport
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialIntegrand
import Mathlib.Tactic

/-! # Exact spatial cell representation of a first collision block -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators CompactlySupported
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Cell interpolation of the fused lattice summand is precisely the sampled
spatial integrand used in the compact-limit proof. -/
theorem wordFusedSpatialSummand_sample {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ)
    (p : FusedConfiguration α × FusedConfiguration α) :
    wordFusedSpatialSummand N β α w n s r x Ψ χ
      (wordFusedPairSiteSample N (n - s) (n - s - r) α p) =
      wordFirstLetterSpatialIntegrand N β α w n s r x Ψ χ p := by
  unfold wordFusedSpatialSummand wordFusedPairSiteSample wordFirstLetterSpatialIntegrand
  rw [wordFusedSiteEmbedding_sample, wordFusedSiteEmbedding_sample]
  rfl

/-- The sampled spatial integrand has an exact fused lattice-sum integral.
Each of the two collision spaces contributes `(4/N)^(h-1)`, with its own phase. -/
theorem integrable_integral_wordFirstLetterSpatialIntegrand {h N : ℕ} (hN : 0 < N)
    (β : ℝ) (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ)
    (hfit : s + r ≤ n) (x : LatticeConfiguration h)
    (hx : ∀ i, Even (x i 0 + x i 1 + (n : ℤ)))
    (Ψ : Configuration h → ℝ) (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    Integrable (wordFirstLetterSpatialIntegrand N β α w n s r x Ψ χ) ∧
      (∫ p : FusedConfiguration α × FusedConfiguration α,
        wordFirstLetterSpatialIntegrand N β α w n s r x Ψ χ p) =
        (4 / (N : ℝ)) ^ (2 * (h - 1)) *
          ∑' z : (Site × (Spectator α → Site)) × (Site × (Spectator α → Site)),
            wordFusedSpatialSummand N β α w n s r x Ψ χ z := by
  classical
  let G := wordFusedSpatialSummand N β α w n s r x Ψ χ
  have hfinite := finite_support_wordFusedSpatialSummand N β α w n s r x Ψ χ
  let S := hfinite.toFinset
  have hzero (z : (Site × (Spectator α → Site)) × (Site × (Spectator α → Site)))
      (hz : z ∉ S) : G z = 0 := by
    by_contra hne
    exact hz (hfinite.mem_toFinset.mpr hne)
  have hS : ∀ z ∈ S,
      (Even (z.1.1 0 + z.1.1 1 + ((n - s : ℕ) : ℤ)) ∧
        ∀ i, Even (z.1.2 i 0 + z.1.2 i 1 + ((n - s : ℕ) : ℤ))) ∧
      (Even (z.2.1 0 + z.2.1 1 + ((n - s - r : ℕ) : ℤ)) ∧
        ∀ i, Even (z.2.2 i 0 + z.2.2 i 1 + ((n - s - r : ℕ) : ℤ))) := by
    intro z hz
    have hne : G z ≠ 0 := hfinite.mem_toFinset.mp hz
    have hterm : wordConsScaledSummand N β α w n s r x (wordFusedSiteEmbedding α z.1)
        (wordFusedSiteEmbedding α z.2) Ψ ≠ 0 := (mul_ne_zero_iff.mp hne).2
    obtain ⟨hu, hv⟩ := wordConsScaledSummand_nonzero_phases N β α w n s r hfit x _ _ Ψ hx hterm
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa only [wordFusedSiteEmbedding, true_or, ↓reduceDIte] using hu α.1.1
    · intro i
      simpa [wordFusedSiteEmbedding, i.2.1, i.2.2] using hu i.1
    · simpa only [wordFusedSiteEmbedding, true_or, ↓reduceDIte] using hv α.1.1
    · intro i
      simpa [wordFusedSiteEmbedding, i.2.1, i.2.2] using hv i.1
  obtain ⟨hint, hi⟩ := integrable_integral_fusedPairPhaseStep hN α (n - s) (n - s - r) S hS G hzero
  have heq : (fun p : FusedConfiguration α × FusedConfiguration α =>
      G (wordFusedPairSiteSample N (n - s) (n - s - r) α p)) =
      wordFirstLetterSpatialIntegrand N β α w n s r x Ψ χ :=
    funext (wordFusedSpatialSummand_sample N β α w n s r x Ψ χ)
  rw [heq] at hint hi
  refine ⟨hint, hi.trans ?_⟩
  exact congrArg (fun v : ℝ => (4 / (N : ℝ)) ^ (2 * (h - 1)) * v)
    (tsum_eq_sum hzero).symm

end Critical2DKPZ.SHF.Moments
