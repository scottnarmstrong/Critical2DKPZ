/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationKernelList
public import Critical2DKPZ.SHF.Moments.WordDominationTerminalBoundary
public import Critical2DKPZ.MomentBounds.CCR25StartBoundaryIdentity
import Mathlib.Tactic

/-! # Compact endpoint profiles as CCR boundary pairings -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The alternating interaction and free kernels between a collision word's initial and final free transitions. -/
def pairWordInteriorKernels {h : ℕ} (L : ℕ) (lam β : ℝ) :
    List (CollisionPair h) → List (LatticeConfiguration h → LatticeConfiguration h → ℝ)
  | [] => []
  | α :: rest =>
      hattedInteractingReplicaKernelAbs L lam β (pairPartition α) ::
        match rest with
        | [] => []
        | γ :: tail => hattedFreeReplicaKernel L (pairPartition α) (pairPartition γ) ::
            pairWordInteriorKernels L lam β (γ :: tail)

/-- The final collision partition of a pair word (the empty word uses bottom). -/
@[instance_reducible]
def pairWordLastPartition {h : ℕ} : List (CollisionPair h) → ReplicaPartition h
  | [] => ⊥
  | α :: rest =>
      match rest with
      | [] => pairPartition α
      | γ :: tail => pairWordLastPartition (γ :: tail)

private theorem hattedPairWordKernelList_splitAll {h : ℕ}
    (L : ℕ) (lam β : ℝ) :
    ∀ (w : List (CollisionPair h)) (previous : ReplicaPartition h),
      hattedPairWordKernelList L lam β previous w =
        match w with
        | [] => [hattedFreeReplicaKernel L previous ⊥]
        | α :: rest => hattedFreeReplicaKernel L previous (pairPartition α) ::
            (pairWordInteriorKernels L lam β (α :: rest) ++
              [hattedFreeReplicaKernel L (pairWordLastPartition (α :: rest)) ⊥]) := by
  intro w
  induction w with
  | nil =>
      intro previous
      simp [hattedPairWordKernelList]
  | cons α rest ih =>
      intro previous
      cases rest with
      | nil =>
          simp [hattedPairWordKernelList, pairWordInteriorKernels,
            pairWordLastPartition]
      | cons γ tail =>
          change hattedFreeReplicaKernel L previous (pairPartition α) ::
              hattedInteractingReplicaKernelAbs L lam β (pairPartition α) ::
                hattedPairWordKernelList L lam β (pairPartition α) (γ :: tail) =
            hattedFreeReplicaKernel L previous (pairPartition α) ::
              ((hattedInteractingReplicaKernelAbs L lam β (pairPartition α) ::
                hattedFreeReplicaKernel L (pairPartition α) (pairPartition γ) ::
                  pairWordInteriorKernels L lam β (γ :: tail)) ++
                [hattedFreeReplicaKernel L (pairWordLastPartition (γ :: tail)) ⊥])
          rw [ih (pairPartition α)]
          simp only [List.cons_append]

/-- Split a nonempty hatted word into its initial free transition, internal
collision word and final free transition. -/
theorem hattedPairWordKernelList_split {h : ℕ}
    (L : ℕ) (lam β : ℝ) (previous : ReplicaPartition h)
    (α : CollisionPair h) (rest : List (CollisionPair h)) :
    hattedPairWordKernelList L lam β previous (α :: rest) =
      hattedFreeReplicaKernel L previous (pairPartition α) ::
        (pairWordInteriorKernels L lam β (α :: rest) ++
          [hattedFreeReplicaKernel L (pairWordLastPartition (α :: rest)) ⊥]) := by
  exact hattedPairWordKernelList_splitAll L lam β (α :: rest) previous

/-- The real-valued indicator of a finite set of lattice sites. -/
def collisionWordSiteIndicator (A : Finset Site) : Site → ℝ :=
  fun z => if z ∈ A then 1 else 0

private def collisionWordConfigIndicator {h : ℕ} (A : Finset Site) :
    LatticeConfiguration h → ℝ :=
  fun x => if x ∈ Fintype.piFinset (fun _ : Fin h => A) then 1 else 0

private theorem collisionKernelWordAction_append {α : Type*}
    (Ks Ks' : List (α → α → ℝ)) (f : α → ℝ) (x : α) :
    collisionKernelWordAction (Ks ++ Ks') f x =
      collisionKernelWordAction Ks (collisionKernelWordAction Ks' f) x := by
  induction Ks generalizing f x with
  | nil => rfl
  | cons K Ks ih =>
      simp only [List.cons_append, collisionKernelWordAction]
      apply tsum_congr
      intro y
      exact congrArg (fun q : ℝ => K x y * q) (ih f y)

private theorem collisionWord_prod_indicator_eq_one {h : ℕ} (A : Finset Site)
    {x : LatticeConfiguration h}
    (hx : x ∈ Fintype.piFinset (fun _ : Fin h => A)) :
    (∏ i : Fin h, collisionWordSiteIndicator A (x i)) = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  have hxi : x i ∈ A := Fintype.mem_piFinset.mp hx i
  simp [collisionWordSiteIndicator, hxi]

private theorem collisionWord_terminalDeltaSum_eq_configIndicator {h : ℕ}
    (A : Finset Site) (x : LatticeConfiguration h) :
    (∑ z ∈ Fintype.piFinset (fun _ : Fin h => A), if x = z then (1 : ℝ) else 0) =
      collisionWordConfigIndicator A x := by
  classical
  by_cases hx : x ∈ Fintype.piFinset (fun _ : Fin h => A)
  · simp [collisionWordConfigIndicator, hx]
  · simp [collisionWordConfigIndicator, hx]

/-- Summing both compact endpoint indicators against a hatted collision path
gives the CCR boundary pairing of its interior operator word. -/
theorem finite_sum_hattedPairWordPath_eq_boundaryPairing
    {h : ℕ} (L : ℕ) (lam β : ℝ) (A A' : Finset Site)
    (α : CollisionPair h) (rest : List (CollisionPair h)) :
    (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
      ∑ z ∈ Fintype.piFinset (fun _ : Fin h => A'),
        hattedPairWordPath L lam β ⊥ (α :: rest) x z) =
      ∑' u : LatticeConfiguration h,
        hattedReplicaBoundaryVector L (pairPartition α) A (collisionWordSiteIndicator A) u *
          collisionKernelWordAction (pairWordInteriorKernels L lam β (α :: rest))
            (hattedReplicaBoundaryVector L
              (pairWordLastPartition (α :: rest)) A' (collisionWordSiteIndicator A')) u := by
  classical
  let S := Fintype.piFinset (fun _ : Fin h => A)
  let S' := Fintype.piFinset (fun _ : Fin h => A')
  let δ : LatticeConfiguration h → LatticeConfiguration h → ℝ :=
    fun z x => if x = z then 1 else 0
  let Kfull := hattedPairWordKernelList L lam β ⊥ (α :: rest)
  let Kleft : LatticeConfiguration h → LatticeConfiguration h → ℝ :=
    hattedFreeReplicaKernel L ⊥ (pairPartition α)
  let Kright : LatticeConfiguration h → LatticeConfiguration h → ℝ :=
    hattedFreeReplicaKernel L (pairWordLastPartition (α :: rest)) ⊥
  let middle := pairWordInteriorKernels L lam β (α :: rest)
  let endProfile := fun x : LatticeConfiguration h =>
    ∑ z ∈ S', δ z x
  let rightBoundary := hattedReplicaBoundaryVector L
    (pairWordLastPartition (α :: rest)) A' (collisionWordSiteIndicator A')
  have hrow : ∀ K ∈ Kfull, ∀ x, ∃ U : Finset (LatticeConfiguration h),
      ∀ y ∉ U, K x y = 0 := by
    intro K hK x
    refine ⟨configBox h (ccr25ConfigurationCenterSites x) L, ?_⟩
    intro y hy
    have hxbox : x ∈ configBox h (ccr25ConfigurationCenterSites x) 0 :=
      ccr25_mem_configBox_centerSites x
    have hreach := hattedPairWordKernelList_boxStep
      (A := ccr25ConfigurationCenterSites x) (lam := lam) (β := β) (previous := ⊥)
      (α :: rest) K hK 0 x hxbox y
    by_contra hnonzero
    have hybox := hreach hnonzero
    exact hy (by simpa using hybox)
  have hdecomp : Kfull = Kleft :: (middle ++ [Kright]) := by
    dsimp [Kfull, Kleft, Kright, middle]
    exact hattedPairWordKernelList_split L lam β ⊥ α rest
  have hterminal (x : LatticeConfiguration h) :
      collisionKernelWordAction [Kright] endProfile x = rightBoundary x := by
    simp only [collisionKernelWordAction]
    have hprofile (z : LatticeConfiguration h) :
        endProfile z = collisionWordConfigIndicator A' z := by
      exact collisionWord_terminalDeltaSum_eq_configIndicator A' z
    change (∑' z : LatticeConfiguration h, Kright x z * endProfile z) =
      rightBoundary x
    calc
      _ = ∑' z : LatticeConfiguration h, Kright x z * collisionWordConfigIndicator A' z := by
        apply tsum_congr
        intro z
        rw [hprofile z]
      _ = rightBoundary x := by
        rw [tsum_eq_sum (s := S')]
        · have hsum := finite_sum_terminalProfile_mul_hattedFreeReplicaKernel_eq_hattedBoundaryVector
            L (pairWordLastPartition (α :: rest)) A'
            (collisionWordSiteIndicator A') x
          change (∑ z ∈ S',
              (∏ i : Fin h, collisionWordSiteIndicator A' (z i)) *
                hattedFreeReplicaKernel L (pairWordLastPartition (α :: rest)) ⊥ x z) =
            hattedReplicaBoundaryVector L (pairWordLastPartition (α :: rest))
              A' (collisionWordSiteIndicator A') x at hsum
          change (∑ z ∈ S', Kright x z * collisionWordConfigIndicator A' z) =
            hattedReplicaBoundaryVector L (pairWordLastPartition (α :: rest))
              A' (collisionWordSiteIndicator A') x
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro z hz
          have hzPi : z ∈ Fintype.piFinset (fun _ : Fin h => A') := by
            simpa [S'] using hz
          have hzCoords : ∀ i, z i ∈ A' := Fintype.mem_piFinset.mp hzPi
          rw [collisionWord_prod_indicator_eq_one A' hzPi]
          simp [Kright, collisionWordConfigIndicator, hzCoords]
        · intro z hz
          have hz' : z ∉ Fintype.piFinset (fun _ : Fin h => A') := by
            simpa [S'] using hz
          simp [collisionWordConfigIndicator, hz']
  have hfullEnd (x : LatticeConfiguration h) :
      collisionKernelWordAction Kfull endProfile x =
        collisionKernelWordAction (Kleft :: middle) rightBoundary x := by
    calc
      _ = collisionKernelWordAction (Kleft :: (middle ++ [Kright])) endProfile x := by
        rw [hdecomp]
      _ = collisionKernelWordAction ((Kleft :: middle) ++ [Kright]) endProfile x := by
        rfl
      _ = collisionKernelWordAction (Kleft :: middle)
            (collisionKernelWordAction [Kright] endProfile) x :=
        collisionKernelWordAction_append (Kleft :: middle) [Kright] endProfile x
      _ = collisionKernelWordAction (Kleft :: middle) rightBoundary x := by
        exact congrArg (fun f : LatticeConfiguration h → ℝ =>
          collisionKernelWordAction (Kleft :: middle) f x) (funext hterminal)
  calc
    _ = ∑ x ∈ S,
        collisionKernelWordAction Kfull endProfile x := by
          apply Finset.sum_congr rfl
          intro x hx
          have hlin := collisionKernelWordAction_finsetSum Kfull
            (Fintype.piFinset (fun _ : Fin h => A')) (fun _ => (1 : ℝ))
            (fun z => δ z) hrow x
          calc
            (∑ z ∈ S', hattedPairWordPath L lam β ⊥ (α :: rest) x z) =
                ∑ z ∈ S', collisionKernelWordAction Kfull (δ z) x := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  exact hattedPairWordPath_eq_fullKernelWordApply
                    L lam β ⊥ (α :: rest) x z
            _ = collisionKernelWordAction Kfull endProfile x := by
                  simpa [endProfile, δ, S', Fintype.mem_piFinset] using hlin.symm
    _ = ∑ x ∈ S,
        ∑' u : LatticeConfiguration h,
          Kleft x u * collisionKernelWordAction middle rightBoundary u := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hfullEnd x]
          rw [collisionKernelWordAction]
    _ = _ := by
          have hstart := finite_sum_startProfile_hattedFreeReplicaKernel_pairing_eq_hattedBoundaryVector
            L (pairPartition α) A (collisionWordSiteIndicator A)
            (fun u => collisionKernelWordAction middle rightBoundary u)
          have hprod (x : LatticeConfiguration h) (hx : x ∈ S) :
              (∏ i : Fin h, collisionWordSiteIndicator A (x i)) = 1 :=
            collisionWord_prod_indicator_eq_one A hx
          calc
            _ = ∑ x ∈ S,
                (∏ i : Fin h, collisionWordSiteIndicator A (x i)) *
                  (∑' u : LatticeConfiguration h,
                    Kleft x u * collisionKernelWordAction middle rightBoundary u) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      rw [hprod x hx]
                      ring
            _ = _ := by
                      simpa [S, Kleft] using hstart

end Critical2DKPZ.SHF.Moments

end
