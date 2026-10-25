/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.PairSelection
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-! # Coordinates on a pair-collision stratum -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

/-- The free labels after deleting one representative of a collision pair and
the two labels reserved for the remaining pair sum. -/
abbrev PairSpectatorLabels (h : ℕ) (m k l : Fin h) :=
  {i : Fin h // i ≠ m ∧ i ≠ k ∧ i ≠ l}

/-- Three distinct replica labels require at least three labels in total. -/
theorem three_le_of_distinct_labels {h : ℕ} (m k l : Fin h)
    (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l) : 3 ≤ h := by
  have hcard : 3 ≤ (Finset.univ : Finset (Fin h)).card := by
    calc
      3 = ({m, k, l} : Finset (Fin h)).card := by simp [hmk, hml, hkl]
      _ ≤ _ := Finset.card_le_card (Finset.subset_univ _)
  simpa using hcard

/-- A configuration on the pair stratum, recorded by the two distinguished
coordinates and all remaining free coordinates. -/
def encodePairStratum {h : ℕ} (m k l : Fin h)
    (y : LatticeConfiguration h) : (Site × Site) × (PairSpectatorLabels h m k l → Site) :=
  ((y k, y l), fun i => y i.val)

/-- Removing the three distinguished labels leaves the total label count minus three spectators. -/
theorem card_pairSpectatorLabels {h : ℕ} (m k l : Fin h)
    (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l) :
    Fintype.card (PairSpectatorLabels h m k l) = h - 3 := by
  classical
  rw [Fintype.card_subtype]
  let s : Finset (Fin h) := Finset.univ.filter (fun i => i ≠ m ∧ i ≠ k ∧ i ≠ l)
  have hs : s = ((Finset.univ.erase m).erase k).erase l := by
    ext i
    simp [s, and_assoc, and_comm]
  rw [show (Finset.univ.filter (fun i : Fin h => i ≠ m ∧ i ≠ k ∧ i ≠ l)) = s by rfl,
    hs]
  have hk : k ∈ Finset.univ.erase m := Finset.mem_erase.mpr ⟨hmk.symm, Finset.mem_univ _⟩
  have hl : l ∈ (Finset.univ.erase m).erase k := by
    apply Finset.mem_erase.mpr
    constructor
    · exact hkl.symm
    · exact Finset.mem_erase.mpr ⟨hml.symm, Finset.mem_univ _⟩
  have hthree : 3 ≤ h := by
    have hcard : 3 ≤ (Finset.univ : Finset (Fin h)).card := by
      calc
        3 = ({m, k, l} : Finset (Fin h)).card := by
          simp [hmk, hml, hkl]
        _ ≤ _ := Finset.card_le_card (Finset.subset_univ _)
    simpa using hcard
  rw [Finset.card_erase_of_mem hl, Finset.card_erase_of_mem hk,
    Finset.card_erase_of_mem (Finset.mem_univ m), Finset.card_univ]
  rw [Fintype.card_fin]
  omega

/-- Spectator labels are identified with the corresponding finite ordinal. -/
noncomputable def pairSpectatorEquivFin {h : ℕ} (m k l : Fin h)
    (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l) :
    PairSpectatorLabels h m k l ≃ Fin (h - 3) :=
  Fintype.equivFinOfCardEq (card_pairSpectatorLabels m k l hmk hml hkl)

/-- The pair-stratum coordinates determine the whole configuration whenever
the omitted label is identified with a distinct collision partner. -/
theorem encodePairStratum_injective {h : ℕ} (m n k l : Fin h)
    (hmn : m ≠ n)
    {y y' : LatticeConfiguration h} (hy : y m = y n) (hy' : y' m = y' n)
    (he : encodePairStratum m k l y = encodePairStratum m k l y') : y = y' := by
  have hpair : (y k, y l) = (y' k, y' l) := congrArg Prod.fst he
  have hfree (i : Fin h) (him : i ≠ m) : y i = y' i := by
    by_cases hik : i = k
    · subst i
      exact congrArg Prod.fst hpair
    by_cases hil : i = l
    · subst i
      exact congrArg Prod.snd hpair
    have htail := congrArg Prod.snd he
    have htaili := congrFun htail ⟨i, ⟨him, hik, hil⟩⟩
    exact htaili
  funext i
  by_cases him : i = m
  · subst i
    rw [hy, hy']
    exact hfree n hmn.symm
  · exact hfree i him

end Critical2DKPZ.MomentBounds
