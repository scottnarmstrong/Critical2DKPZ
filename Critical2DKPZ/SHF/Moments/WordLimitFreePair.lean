/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitFreeCoordinate
public import Critical2DKPZ.SHF.Moments.WordLimitPotentialSmoothing
public import Critical2DKPZ.SHF.Moments.WordLimitSpectators

/-! # Free-spectator smoothing when both next-pair labels are free -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- A rectangular two-coordinate configuration sum is the ordinary iterated
sum over its two entries. -/
theorem sum_piFinset_fin_two {X : Type*} [DecidableEq X]
    (D : Fin 2 → Finset X) (H : (Fin 2 → X) → ℝ) :
    (∑ p ∈ Fintype.piFinset D, H p) = ∑ a ∈ D 0, ∑ b ∈ D 1, H ![a, b] := by
  classical
  have heq : (∑ p ∈ Fintype.piFinset D, H p) =
      ∑ q ∈ (D 0) ×ˢ (D 1), H ![q.1, q.2] := by
    apply Finset.sum_bij (fun p _ => (p 0, p 1))
    · intro p hp
      exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mp hp 0, Fintype.mem_piFinset.mp hp 1⟩
    · intro p hp q hq hpq
      funext i
      fin_cases i
      · exact congrArg Prod.fst hpq
      · exact congrArg Prod.snd hpq
    · intro q hq
      refine ⟨![q.1, q.2], Fintype.mem_piFinset.mpr ?_, rfl⟩
      intro i
      fin_cases i
      · exact (Finset.mem_product.mp hq).1
      · exact (Finset.mem_product.mp hq).2
    · intro p hp
      congr 1
      funext i
      fin_cases i <;> rfl
  rw [heq, Finset.sum_product]

/-- The independent free product tested on a pair gap reduces to the two
walkers in that pair; every other coordinate has unit mass. -/
theorem sum_freeReplicaKernel_pairGap_test {h : ℕ} (α : CollisionPair h)
    (m : ℕ) (x : Fin h → Site) (F : Site → ℝ) :
    (∑ y ∈ Fintype.piFinset (fun i => endpoints (x i) m),
      (∏ i, srwKernel m (y i - x i)) * F (y α.1.2 - y α.1.1)) =
      ∑ a ∈ endpoints (x α.1.1) m, ∑ b ∈ endpoints (x α.1.2) m,
        (srwKernel m (a - x α.1.1) * srwKernel m (b - x α.1.2)) * F (b - a) := by
  classical
  let P : (Fin 2 → Site) → ℝ := fun p =>
    (∏ j, srwKernel m (p j - pairRestrict α x j)) * F (p 1 - p 0)
  have hpoint (y : Fin h → Site) :
      (∏ i, srwKernel m (y i - x i)) * F (y α.1.2 - y α.1.1) =
        P (pairRestrict α y) * ∏ i : Spectator α, srwKernel m (y i.1 - x i.1) := by
    rw [wordLimit_prod_pair_spectators α]
    dsimp only [P]
    simp only [Fin.prod_univ_two]
    simp [pairRestrict]
    ac_rfl
  simp_rw [hpoint]
  rw [wordLimit_sum_pair_spectator_coordinates α (fun i => endpoints (x i) m) P
    (fun i z => srwKernel m (z - x i.1))]
  simp_rw [sum_srwKernel_endpoints]
  simp only [Finset.prod_const_one, mul_one]
  rw [sum_piFinset_fin_two]
  simp [P, pairRestrict, Fin.prod_univ_two]

/-- The potential of one free label relative to a fixed collision center
has the uniform scalar smoothing bound, with all other labels integrated out. -/
theorem exists_freeReplicaKernel_oneGapPotential_bound_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ {h : ℕ} (m n : ℕ) (x : Fin h → Site) (j : Fin h) (b : Site),
      (∑ y ∈ Fintype.piFinset (fun i => endpoints (x i) m),
        (∏ i, srwKernel m (y i - x i)) * wordGapPotential n (y j - b)) ≤
        C * ((∑ k ∈ Finset.Icc 0 m, 1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) +
          2 / Real.sqrt ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hbound⟩ := exists_wordGapPotential_smoothing_bound_explicit
  refine ⟨C, hC, fun {h} m n x j b => ?_⟩
  rw [sum_freeReplicaKernel_oneGapPotential]
  simpa only [tsum_srwKernel_wordGapPotential] using hbound m n (x j) b

/-- If both labels of the next pair are free spectators, smoothing its gap
potential has the same bound as conditioning on either walker first. -/
theorem exists_freeReplicaKernel_pairGapPotential_bound_explicit :
    ∃ C : ℝ, 0 < C ∧ ∀ {h : ℕ} (α : CollisionPair h) (m n : ℕ) (x : Fin h → Site),
      (∑ y ∈ Fintype.piFinset (fun i => endpoints (x i) m),
        (∏ i, srwKernel m (y i - x i)) * wordGapPotential n (y α.1.2 - y α.1.1)) ≤
        C * ((∑ k ∈ Finset.Icc 0 m, 1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) +
          2 / Real.sqrt ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hbound⟩ := exists_wordGapPotential_smoothing_bound_explicit
  refine ⟨C, hC, fun {h} α m n x => ?_⟩
  rw [sum_freeReplicaKernel_pairGap_test]
  let B := C * ((∑ k ∈ Finset.Icc 0 m, 1 / Real.sqrt ((k : ℝ) + 1)) / ((m : ℝ) + 1) +
    2 / Real.sqrt ((m : ℝ) + 1))
  have hslice (a : Site) :
      (∑ b ∈ endpoints (x α.1.2) m,
        (srwKernel m (a - x α.1.1) * srwKernel m (b - x α.1.2)) *
          wordGapPotential n (b - a)) ≤ srwKernel m (a - x α.1.1) * B := by
    have hb := hbound m n (x α.1.2) a
    rw [tsum_srwKernel_wordGapPotential, ← sum_srwKernel_wordGapPotential] at hb
    have hh := mul_le_mul_of_nonneg_left hb (srwKernel_nonneg m (a - x α.1.1))
    simpa only [Finset.mul_sum, mul_assoc, B] using hh
  calc
    _ ≤ ∑ a ∈ endpoints (x α.1.1) m, srwKernel m (a - x α.1.1) * B :=
      Finset.sum_le_sum (fun a _ => hslice a)
    _ = B := by rw [← Finset.sum_mul, sum_srwKernel_endpoints, one_mul]

end Critical2DKPZ.SHF.Moments
