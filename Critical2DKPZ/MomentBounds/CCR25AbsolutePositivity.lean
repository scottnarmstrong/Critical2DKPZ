/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25SignedInteraction
public import Critical2DKPZ.MomentBounds.CCR25PartitionWords
import Mathlib.Tactic

/-! # Positivity of the absolute CCR25 kernels and boundary vectors -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- A finite kernel word preserves nonnegativity when every factor kernel and
the terminal vector are nonnegative. -/
theorem finiteKernelWordApply_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) :
    ∀ (Ks : List (α → α → ℝ)) (f : α → ℝ),
      (∀ K ∈ Ks, ∀ x y, 0 ≤ K x y) →
      (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ finiteKernelWordApply s Ks f x := by
  intro Ks
  induction Ks with
  | nil =>
      intro f hK hf x
      simpa [finiteKernelWordApply] using hf x
  | cons K Ks ih =>
      intro f hK hf x
      simp only [finiteKernelWordApply]
      apply Finset.sum_nonneg
      intro y hy
      exact mul_nonneg (hK K (by simp) x y)
        (ih f (fun K' hK' => hK K' (by simp [hK'])) hf y)

/-- The recursively defined absolute interacting kernel is nonnegative. -/
theorem interactingReplicaKernelAbs_nonneg {h : ℕ} (β : ℝ)
    (I : ReplicaPartition h) :
    ∀ n z x, 0 ≤ interactingReplicaKernelAbs β I n z x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro z x
      cases n with
      | zero =>
          simp only [interactingReplicaKernelAbs]
          split_ifs <;> norm_num
      | succ m =>
          simp only [interactingReplicaKernelAbs]
          apply mul_nonneg
          · exact abs_nonneg _
          · apply Finset.sum_nonneg
            intro r hr
            apply tsum_nonneg
            intro y
            apply mul_nonneg
            · apply ih
              omega
            · exact freeReplicaKernel_nonneg (r + 1) I I y x

/-- Every finite Laplace-free sum of free replica kernels is nonnegative. -/
theorem hattedFreeReplicaKernel_nonneg {h : ℕ} (L : ℕ)
    (I J : ReplicaPartition h) (z x : LatticeConfiguration h) :
    0 ≤ hattedFreeReplicaKernel L I J z x := by
  unfold hattedFreeReplicaKernel
  apply Finset.sum_nonneg
  intro n hn
  exact freeReplicaKernel_nonneg (n + 1) I J z x

/-- The finite Laplace-summed absolute interacting kernel is nonnegative. -/
theorem hattedInteractingReplicaKernelAbs_nonneg {h : ℕ} (L : ℕ)
    (lam β : ℝ) (I : ReplicaPartition h)
    (z x : LatticeConfiguration h) :
    0 ≤ hattedInteractingReplicaKernelAbs L lam β I z x := by
  unfold hattedInteractingReplicaKernelAbs
  apply add_nonneg
  · split_ifs <;> positivity
  · apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (Real.exp_nonneg _)
      (interactingReplicaKernelAbs_nonneg β I (m + 1) z x)

/-- A nonnegative endpoint profile gives a nonnegative finite boundary vector. -/
theorem replicaBoundaryVector_nonneg {h : ℕ} (n : ℕ)
    (I : ReplicaPartition h) (s : Finset Site) (f : Site → ℝ)
    (hf : ∀ y ∈ s, 0 ≤ f y) (x : LatticeConfiguration h) :
    0 ≤ replicaBoundaryVector n I s f x := by
  unfold replicaBoundaryVector
  split_ifs with hx
  · apply Finset.prod_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro y hy
    exact mul_nonneg (Critical2DKPZ.Polymer.kernel_nonneg n (x i - y))
      (hf y hy)
  · exact le_of_eq rfl

/-- Time summation preserves nonnegativity of the boundary vectors. -/
theorem hattedReplicaBoundaryVector_nonneg {h : ℕ} (L : ℕ)
    (I : ReplicaPartition h) (s : Finset Site) (f : Site → ℝ)
    (hf : ∀ y ∈ s, 0 ≤ f y) (x : LatticeConfiguration h) :
    0 ≤ hattedReplicaBoundaryVector L I s f x := by
  unfold hattedReplicaBoundaryVector
  apply Finset.sum_nonneg
  intro n hn
  exact replicaBoundaryVector_nonneg (n + 1) I s f hf x

/-- A finite CCR25 partition-word pairing with nonnegative endpoint vectors is
nonnegative, since both the free and absolute interacting kernels are. -/
theorem ccr25FiniteWordPairing_nonneg {h n : ℕ}
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (I : Fin (n + 1) → ReplicaPartition h)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (hu : ∀ J x, 0 ≤ u J x) (hv : ∀ J x, 0 ≤ v J x) :
    0 ≤ ccr25FiniteWordPairing s L lam β I u v := by
  classical
  let labels := ccr25PartitionWordLabels n I
  have hkernel : ∀ K ∈ (labels.map (ccr25LabelKernel L lam β)),
      ∀ x y, 0 ≤ K x y := by
    intro K hK x y
    obtain ⟨label, hlabel, rfl⟩ := List.mem_map.mp hK
    cases label with
    | interacting J =>
        exact hattedInteractingReplicaKernelAbs_nonneg L lam β J x y
    | free J J' => exact hattedFreeReplicaKernel_nonneg L J J' x y
  have hword : ∀ x,
      0 ≤ finiteKernelWordApply s
        (labels.map (ccr25LabelKernel L lam β))
        (v (I (Fin.last n))) x :=
    finiteKernelWordApply_nonneg s
      (labels.map (ccr25LabelKernel L lam β))
      (v (I (Fin.last n))) hkernel (hv (I (Fin.last n)))
  unfold ccr25FiniteWordPairing
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (hu (I 0) x) (by simpa [labels] using hword x)

end

end Critical2DKPZ.MomentBounds
