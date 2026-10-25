/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FiniteOperators
public import Critical2DKPZ.Definitions.SiteToPlane
public import Critical2DKPZ.Polymer.Chaos
public import Critical2DKPZ.Polymer.WalkKernel
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # CCR25 replica operators and boundary vectors -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- Lattice labels representing the blocks of a replica partition, chosen as
the least label in each equivalence class. -/
noncomputable def replicaBlockRepresentatives {h : ℕ} (I : ReplicaPartition h) : Finset (Fin h) := by
  classical
  exact Finset.univ.filter (fun i => ∀ j, I.r i j → i ≤ j)

/-- The number of replica labels in the block represented by `i`. -/
noncomputable def replicaBlockSize {h : ℕ} (I : ReplicaPartition h) (i : Fin h) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j => I.r i j)).card

/-- The moment of one centred Gaussian disorder coordinate. -/
def gaussianDisorderMoment (β : ℝ) (k : ℕ) : ℝ :=
  ∫ ω : Disorder, Critical2DKPZ.Polymer.xi β (0, 0) ω ^ k ∂disorderLaw

/-- The product of disorder moments over the nonsingleton blocks of a partition,
with singleton coordinates omitted as in CCR25 equation (4.9). -/
noncomputable def replicaPartitionDisorderMoment {h : ℕ} (β : ℝ) (I : ReplicaPartition h) : ℝ := by
  classical
  exact ∏ i ∈ replicaBlockRepresentatives I,
    if 2 ≤ replicaBlockSize I i then gaussianDisorderMoment β (replicaBlockSize I i) else 1

/-- CCR25's free h-replica transition kernel, restricted to the collision spaces
at its two endpoints. -/
noncomputable def freeReplicaKernel {h : ℕ} (n : ℕ) (I J : ReplicaPartition h)
    (z x : LatticeConfiguration h) : ℝ := by
  classical
  exact if IsCollisionConfiguration I z ∧ IsCollisionConfiguration J x then
    ∏ i : Fin h, Critical2DKPZ.srwKernel n (x i - z i)
  else 0

/-- A finite-support convolution of the one-replica walk kernel with a boundary
profile. -/
def finiteBoundaryConvolution (n : ℕ) (s : Finset Site) (f : Site → ℝ) (x : Site) : ℝ :=
  ∑ y ∈ s, Critical2DKPZ.srwKernel n (x - y) * f y

/-- CCR25's boundary vector, restricted to the terminal collision space. -/
noncomputable def replicaBoundaryVector {h : ℕ} (n : ℕ) (I : ReplicaPartition h)
    (s : Finset Site) (f : Site → ℝ) (x : LatticeConfiguration h) : ℝ := by
  classical
  exact if IsCollisionConfiguration I x then
    ∏ i : Fin h, finiteBoundaryConvolution n s f (x i)
  else 0

/-- Absolute interacting kernel. Its recursion splits a composition of a positive
total time at its final free interval; the zero-time term is the identity on the
collision space. -/
noncomputable def interactingReplicaKernelAbs {h : ℕ} (β : ℝ) (I : ReplicaPartition h) :
    ℕ → LatticeConfiguration h → LatticeConfiguration h → ℝ
  | 0, z, x => by
      classical
      exact if z = x ∧ IsCollisionConfiguration I x then 1 else 0
  | m + 1, z, x =>
      |replicaPartitionDisorderMoment β I| *
        ∑ n ∈ Finset.range (m + 1),
          ∑' y : LatticeConfiguration h,
            interactingReplicaKernelAbs β I (m - n) z y *
              freeReplicaKernel (n + 1) I I y x
  termination_by m _ _ => m
  decreasing_by all_goals omega

/-- The summed free kernel `\widehat Q_L`. -/
def hattedFreeReplicaKernel {h : ℕ} (L : ℕ) (I J : ReplicaPartition h)
    (z x : LatticeConfiguration h) : ℝ :=
  ∑ n ∈ Finset.range L, freeReplicaKernel (n + 1) I J z x

/-- The Laplace-summed absolute interacting kernel `|\widehat U|`. -/
noncomputable def hattedInteractingReplicaKernelAbs {h : ℕ} (L : ℕ) (lam β : ℝ)
    (I : ReplicaPartition h) (z x : LatticeConfiguration h) : ℝ := by
  classical
  exact
  (if z = x ∧ IsCollisionConfiguration I x then 1 else 0) +
    ∑ m ∈ Finset.range L,
      Real.exp (-lam * (m + 1 : ℕ)) * interactingReplicaKernelAbs β I (m + 1) z x

/-- The time-summed left boundary vector `\widehat q_L^{f,I}`. -/
def hattedReplicaBoundaryVector {h : ℕ} (L : ℕ) (I : ReplicaPartition h)
    (s : Finset Site) (f : Site → ℝ) (x : LatticeConfiguration h) : ℝ :=
  ∑ n ∈ Finset.range L, replicaBoundaryVector (n + 1) I s f x

/-- Product exponential weight used in CCR25. -/
def replicaExponentialWeight {h : ℕ} (t : ℝ) (x : LatticeConfiguration h) : ℝ :=
  ∏ i : Fin h, Real.exp (-t * ‖siteToPlane (x i)‖)


/-- The replica exponential weight is strictly positive. -/
theorem replicaExponentialWeight_pos {h : ℕ} (t : ℝ) (x : LatticeConfiguration h) :
    0 < replicaExponentialWeight t x := by
  unfold replicaExponentialWeight
  exact Finset.prod_pos fun _ _ => Real.exp_pos _


end

end Critical2DKPZ.MomentBounds
