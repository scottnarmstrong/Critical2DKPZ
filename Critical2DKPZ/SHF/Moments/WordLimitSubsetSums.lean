/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.FinsetCoordinateSplit
import Mathlib.Tactic

/-! # Finite coordinate sums along a subset and its complement -/

@[expose] public noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

/-- Regroup a finite rectangular configuration sum by the selected labels
and their complement, allowing dependence between both sets of coordinates. -/
theorem sum_piFinset_split_subset {n : ℕ} (S : Finset (Fin n))
    {X : Type*} [MeasurableSpace X] [DecidableEq X] (D : Fin n → Finset X)
    (H : (Fin S.card → X) → (Fin Sᶜ.card → X) → ℝ) :
    (∑ x ∈ Fintype.piFinset D,
      H (fun i => x (S.orderEmbOfFin rfl i))
        (fun i => x (Sᶜ.orderEmbOfFin rfl i))) =
      ∑ p ∈ Fintype.piFinset (fun i => D (S.orderEmbOfFin rfl i)),
        ∑ q ∈ Fintype.piFinset (fun i => D (Sᶜ.orderEmbOfFin rfl i)), H p q := by
  classical
  let e := Critical2DKPZ.SHF.Tsai.splitFinsetCoordinates S X
  let P := Fintype.piFinset (fun i => D (S.orderEmbOfFin rfl i))
  let Q := Fintype.piFinset (fun i => D (Sᶜ.orderEmbOfFin rfl i))
  have hmem (x : Fin n → X) : x ∈ Fintype.piFinset D ↔ e x ∈ P ×ˢ Q := by
    simp only [Fintype.mem_piFinset, Finset.mem_product, P, Q,
      e, Critical2DKPZ.SHF.Tsai.splitFinsetCoordinates_fst,
      Critical2DKPZ.SHF.Tsai.splitFinsetCoordinates_snd]
    constructor
    · intro hx
      exact ⟨fun i => hx _, fun i => hx _⟩
    · rintro ⟨hp, hq⟩ i
      by_cases hi : i ∈ S
      · obtain ⟨j, hj⟩ : i ∈ Set.range (S.orderEmbOfFin rfl) := by
          simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hi
        simpa only [hj] using hp j
      · have hiC : i ∈ Sᶜ := Finset.mem_compl.mpr hi
        obtain ⟨j, hj⟩ : i ∈ Set.range (Sᶜ.orderEmbOfFin rfl) := by
          simpa only [Finset.range_orderEmbOfFin, Finset.mem_coe] using hiC
        simpa only [hj] using hq j
  have hsum :
      (∑ x ∈ Fintype.piFinset D, H (e x).1 (e x).2) =
        ∑ p ∈ P ×ˢ Q, H p.1 p.2 := by
    apply Finset.sum_bij (fun x _ => e x)
    · intro x hx
      exact (hmem x).mp hx
    · intro x hx y hy hxy
      exact e.injective hxy
    · intro p hp
      refine ⟨e.symm p, (hmem _).mpr ?_, e.apply_symm_apply p⟩
      simpa only [e.apply_symm_apply] using hp
    · intro x hx
      rfl
  calc
    _ = ∑ p ∈ P ×ˢ Q, H p.1 p.2 := hsum
    _ = _ := by
      simp only [Finset.sum_product, P, Q]

/-- A finite rectangular configuration sum factors after splitting its coordinates
into an increasing subset enumeration and its complement. -/
theorem sum_piFinset_subset_mul_compl {n : ℕ} (S : Finset (Fin n))
    {X : Type*} [MeasurableSpace X] [DecidableEq X] (D : Fin n → Finset X)
    (F : (Fin S.card → X) → ℝ) (G : (Fin Sᶜ.card → X) → ℝ) :
    (∑ x ∈ Fintype.piFinset D,
      F (fun i => x (S.orderEmbOfFin rfl i)) *
        G (fun i => x (Sᶜ.orderEmbOfFin rfl i))) =
      (∑ p ∈ Fintype.piFinset (fun i => D (S.orderEmbOfFin rfl i)), F p) *
        ∑ q ∈ Fintype.piFinset (fun i => D (Sᶜ.orderEmbOfFin rfl i)), G q := by
  rw [sum_piFinset_split_subset S D (fun p q => F p * G q)]
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm


end Critical2DKPZ.SHF.Moments
