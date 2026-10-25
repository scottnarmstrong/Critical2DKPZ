/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairStratumEncoding
public import Critical2DKPZ.MomentBounds.CollisionRowKernel
import Mathlib.Tactic

/-! # Finite weighted row sums on a pair-collision stratum -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- Coordinates on a pair stratum with the spectator labels indexed by `Fin`. -/
def encodePairStratumFin {h : ℕ} {m k l : Fin h}
    (e : PairSpectatorLabels h m k l ≃ Fin (h - 3))
    (y : LatticeConfiguration h) : (Site × Site) × (Fin (h - 3) → Site) :=
  ((y k, y l), fun j => y (e.symm j).val)

/-- The finite-coordinate encoding of a pair stratum is injective. -/
theorem encodePairStratumFin_injective {h : ℕ} (m n k l : Fin h)
    (hmn : m ≠ n)
    (e : PairSpectatorLabels h m k l ≃ Fin (h - 3))
    {y y' : LatticeConfiguration h} (hy : y m = y n) (hy' : y' m = y' n)
    (he : encodePairStratumFin e y = encodePairStratumFin e y') : y = y' := by
  have hfirst : (y k, y l) = (y' k, y' l) := congrArg Prod.fst he
  have hsecond : (fun i : PairSpectatorLabels h m k l => y i.val) =
      (fun i => y' i.val) := by
    funext i
    have hs := congrFun (congrArg Prod.snd he) (e i)
    simpa [encodePairStratumFin] using hs
  have hdirect : encodePairStratum m k l y = encodePairStratum m k l y' := by
    change ((y k, y l), (fun i : PairSpectatorLabels h m k l => y i.val)) =
      ((y' k, y' l), fun i => y' i.val)
    exact Prod.ext hfirst hsecond
  exact encodePairStratum_injective m n k l hmn hy hy' hdirect

/-- The profile sum over a bounded pair stratum satisfies the stated uniform scale-dependent estimate. -/
theorem sum_pairStratum_profile_le {h : ℕ} (m n k l : Fin h)
    (hmn : m ≠ n)
    (e : PairSpectatorLabels h m k l ≃ Fin (h - 3))
    {L a p : ℝ} (hL : 1 ≤ L) (ha : 0 < a) (hp : 0 < p) (hap : a * p < 1)
    (anchor : Fin (h - 3) → Site) (u : Site)
    (s : Finset (LatticeConfiguration h)) (K : ℕ)
    (hcollision : ∀ y ∈ s, y m = y n)
    (hbox : ∀ y ∈ s, ∀ i, y i ∈ latticeBox K) :
    (∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u
      (encodePairStratumFin e y).2 (encodePairStratumFin e y).1) ≤
      (9 : ℝ) ^ (h - 3) * 1188 * L ^ (-(a * p)) / (a * p * (1 - a * p)) := by
  let E : LatticeConfiguration h → (Site × Site) × (Fin (h - 3) → Site) :=
    encodePairStratumFin e
  let P := latticeBox K ×ˢ latticeBox K
  let T := s.image E
  have hinj : Set.InjOn E s := by
    intro y hy y' hy' he
    exact encodePairStratumFin_injective m n k l hmn e
      (hcollision y hy) (hcollision y' hy') he
  have hsum :
      (∑ y ∈ s, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u
        (E y).2 (E y).1) =
      ∑ z ∈ T, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z.2 z.1 := by
    dsimp [T, E]
    symm
    exact Finset.sum_image hinj
  have hTsubset : T ⊆ P ×ˢ finPiBox (h - 3) K := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨hbox y hy k, hbox y hy l⟩
    · change (fun j : Fin (h - 3) => y (e.symm j).val) ∈
        Fintype.piFinset (fun _ : Fin (h - 3) => latticeBox K)
      exact Fintype.mem_piFinset.mpr (fun j => hbox y hy (e.symm j).val)
  have hnonneg (z : (Site × Site) × (Fin (h - 3) → Site)) :
      0 ≤ collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z.2 z.1 := by
    unfold collisionProfileKernel
    have henergy : 0 ≤ replicaEnergy anchor z.2 := by
      unfold replicaEnergy
      apply Finset.sum_nonneg
      intro i hi
      exact sq_nonneg _
    have hbase : 0 ≤ L + replicaEnergy anchor z.2 +
        ‖siteToPlane (z.1.1 - u)‖ ^ 2 + ‖siteToPlane (z.1.2 - u)‖ ^ 2 := by
      positivity
    have hweight : 0 ≤ 1 + ‖siteToPlane (z.1.1 - z.1.2)‖ ^ (2 * a) :=
      add_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)
    exact mul_nonneg (Real.rpow_nonneg hbase _)
      (Real.rpow_nonneg hweight _)
  have hsubset :
      (∑ z ∈ T, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z.2 z.1) ≤
      ∑ z ∈ P ×ˢ finPiBox (h - 3) K,
        collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z.2 z.1 :=
    Finset.sum_le_sum_of_subset_of_nonneg hTsubset (fun z _ _ => hnonneg z)
  have hprod :
      (∑ z ∈ P ×ˢ finPiBox (h - 3) K,
        collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z.2 z.1) =
      ∑ v ∈ P, ∑ z ∈ finPiBox (h - 3) K,
        collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z v := by
    simpa only [Prod.eta] using
      (Finset.sum_product' P (finPiBox (h - 3) K)
        (fun v z => collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z v))
  rw [hsum]
  calc
    (∑ z ∈ T, collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z.2 z.1) ≤
        ∑ z ∈ P ×ˢ finPiBox (h - 3) K,
          collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z.2 z.1 := hsubset
    _ = ∑ v ∈ P, ∑ z ∈ finPiBox (h - 3) K,
          collisionProfileKernel L ((h - 3 : ℕ) + 2) a p anchor u z v := hprod
    _ ≤ (9 : ℝ) ^ (h - 3) * 1188 * L ^ (-(a * p)) / (a * p * (1 - a * p)) := by
      simpa using sum_collisionProfileKernel_le hL ha hp hap anchor u P K

end

end Critical2DKPZ.MomentBounds
