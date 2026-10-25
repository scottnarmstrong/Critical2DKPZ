/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25Operators
public import Critical2DKPZ.MomentBounds.CCR25PartitionMoments
public import Critical2DKPZ.MomentBounds.CCR25SignedInteraction
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Polymer.WalkKernel
public import Critical2DKPZ.MomentBounds.CCR25SpatialRenewalBounds
import Critical2DKPZ.Blocks.StringSumPropagation
import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! # Spatial renewal domination for interacting CCR25 kernels -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The free walk kernels of the blocks outside the selected block. -/
def otherBlocksFreeKernel {h : ℕ} (I : ReplicaPartition h) (a : Fin h) (m : ℕ)
    (z x : LatticeConfiguration h) : ℝ := by
  classical
  exact ∏ c ∈ (replicaBlockRepresentatives I).filter (fun c => ¬ I.r c a),
    Critical2DKPZ.srwKernel m (x c - z c)

/-- The free kernel on the spectator blocks is nonnegative. -/
theorem otherBlocksFreeKernel_nonneg {h : ℕ} (I : ReplicaPartition h) (a : Fin h)
    (m : ℕ) (z x : LatticeConfiguration h) : 0 ≤ otherBlocksFreeKernel I a m z x := by
  unfold otherBlocksFreeKernel
  apply Finset.prod_nonneg
  intro c hc
  exact Critical2DKPZ.srwKernel_nonneg _ _

private theorem srwKernel_sum_endpoints_reverse (n : ℕ) (x : Site) :
    (∑ y ∈ Critical2DKPZ.Polymer.endpoints x n,
      Critical2DKPZ.srwKernel n (x - y)) = 1 := by
  calc
    _ = ∑ y ∈ Critical2DKPZ.Polymer.endpoints x n,
        Critical2DKPZ.srwKernel n (y - x) := by
          apply Finset.sum_congr rfl
          intro y hy
          exact Critical2DKPZ.Polymer.srwKernel_sub_swap n x y
    _ = 1 := Critical2DKPZ.Polymer.sum_srwKernel_endpoints n x


private theorem sum_srwKernel_mul_endpoints_eq_convolution (k r : ℕ) (z x : Site) :
    (∑ y ∈ Critical2DKPZ.Polymer.endpoints x r,
      Critical2DKPZ.srwKernel k (y - z) * Critical2DKPZ.srwKernel r (x - y)) =
      Critical2DKPZ.srwKernel (k + r) (x - z) := by
  calc
    _ = ∑' y : Site,
        Critical2DKPZ.srwKernel k (y - z) * Critical2DKPZ.srwKernel r (x - y) := by
          symm
          apply tsum_eq_sum
          intro y hy
          have hzero : Critical2DKPZ.srwKernel r (x - y) = 0 := by
            rw [Critical2DKPZ.Polymer.srwKernel_sub_swap r x y]
            exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem r x y hy
          rw [hzero]
          simp
    _ = Critical2DKPZ.srwKernel (k + r) (x - z) :=
      (Critical2DKPZ.Polymer.srwKernel_convolution k r z x).symm

private theorem sum_pairFilter_prod {h : ℕ} (a b : Fin h) (hab : a ≠ b)
    (T : Fin h → Finset Site) (hTab : T a = T b) (g : Fin h → Site → ℝ) :
    (∑ y ∈ (Fintype.piFinset T).filter (fun y => y a = y b),
        ∏ i : Fin h, g i (y i)) =
      ∏ i : {j : Fin h // j ≠ b},
        ∑ v ∈ T i.1, (if i = ⟨a, hab⟩ then g a v * g b v else g i.1 v) := by
  classical
  let E := {i : Fin h // i ≠ b}
  let ea : E := ⟨a, hab⟩
  let D : Finset (E → Site) := Fintype.piFinset fun i => T i.1
  let S : Finset (Fin h → Site) :=
    (Fintype.piFinset T).filter (fun y => y a = y b)
  let drop : (Fin h → Site) → E → Site := fun y i => y i.1
  let fill : (E → Site) → Fin h → Site := fun u j =>
    if hj : j = b then u ea else u ⟨j, hj⟩
  let f : E → Site → ℝ := fun i v =>
    if i = ea then g a v * g b v else g i.1 v
  have hdrop_mem (y : Fin h → Site) (hy : y ∈ S) : drop y ∈ D := by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hy).1 i.1
  have hfill_mem (u : E → Site) (hu : u ∈ D) : fill u ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro j
      by_cases hj : j = b
      · subst j
        have heu : u ea ∈ T a := Fintype.mem_piFinset.mp hu ea
        simpa [fill, ea, hTab] using heu
      · simpa [fill, hj] using Fintype.mem_piFinset.mp hu ⟨j, hj⟩
    · simp [fill, ea, hab]
  have hfill_drop (y : Fin h → Site) (hy : y ∈ S) : fill (drop y) = y := by
    funext j
    by_cases hj : j = b
    · subst j
      have hpair := (Finset.mem_filter.mp hy).2
      simpa [fill, drop, ea, hab] using hpair
    · simp [fill, drop, hj]
  have hdrop_fill (u : E → Site) : drop (fill u) = u := by
    funext i
    simp [drop, fill, i.2]
  have hprod_fill (u : E → Site) :
      (∏ i : Fin h, g i (fill u i)) =
        ∏ i : E, f i (u i) := by
    have hbmem : b ∈ Finset.univ := Finset.mem_univ b
    have hamem : a ∈ Finset.univ.erase b := Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩
    have hsplitB : (∏ i : Fin h, g i (fill u i)) =
        (∏ i ∈ Finset.univ.erase b, g i (fill u i)) * g b (fill u b) := by
      symm
      exact Finset.prod_erase_mul Finset.univ (fun i => g i (fill u i)) hbmem
    have hsplitA : (∏ i ∈ Finset.univ.erase b, g i (fill u i)) =
        (∏ i ∈ (Finset.univ.erase b).erase a, g i (fill u i)) * g a (fill u a) := by
      symm
      exact Finset.prod_erase_mul (Finset.univ.erase b)
        (fun i => g i (fill u i)) hamem
    have hindex :
        (∏ i ∈ (Finset.univ.erase b).erase a, g i (fill u i)) =
          ∏ i ∈ Finset.univ.erase ea, g i.1 (u i) := by
      apply Finset.prod_bij (fun i hi => ⟨i, by
        have hi' : i ≠ a ∧ i ≠ b := by simpa using hi
        exact hi'.2⟩)
      · intro i hi
        have hi' : i ≠ a ∧ i ≠ b := by simpa using hi
        change ⟨i, hi'.2⟩ ∈ Finset.univ.erase ea
        simp only [Finset.mem_erase, Finset.mem_univ]
        exact ⟨by
          intro heq
          apply hi'.1
          exact congrArg Subtype.val heq, trivial⟩
      · intro i hi j hj hij
        exact congrArg Subtype.val hij
      · intro j hj
        have hje : j ≠ ea := (Finset.mem_erase.mp hj).1
        have hjb : j.1 ≠ b := j.2
        have hja : j.1 ≠ a := by
          intro heq
          apply hje
          exact Subtype.ext heq
        refine ⟨j.1, ?_, ?_⟩
        · simp only [Finset.mem_erase, Finset.mem_univ]
          exact ⟨hja, hjb, trivial⟩
        · apply Subtype.ext
          rfl
      · intro i hi
        have hi' : i ≠ a ∧ i ≠ b := by simpa using hi
        have hne : i ≠ b := hi'.2
        have hval : fill u i = u ⟨i, hne⟩ := by simp [fill, hne]
        rw [hval]
    have hsplitE : (∏ i : E, f i (u i)) =
        (∏ i ∈ Finset.univ.erase ea, f i (u i)) * f ea (u ea) := by
      symm
      exact Finset.prod_erase_mul Finset.univ (fun i => f i (u i))
        (Finset.mem_univ ea)
    have hrest : (∏ i ∈ Finset.univ.erase ea, f i (u i)) =
        ∏ i ∈ Finset.univ.erase ea, g i.1 (u i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hie : i ≠ ea := (Finset.mem_erase.mp hi).1
      simp [f, hie]
    rw [hsplitB, hsplitA, hindex, hsplitE]
    rw [hrest]
    simp [f, fill, ea, hab]
    ring
  have hsum_image :
      (∑ y ∈ S, ∏ i : Fin h, g i (y i)) =
        ∑ u ∈ D, ∏ i : E, f i (u i) := by
    apply Finset.sum_bij (fun y _ => drop y)
    · intro y hy
      exact hdrop_mem y hy
    · intro y hy y' hy' hxy
      have hfill := congrArg fill hxy
      rw [hfill_drop y hy, hfill_drop y' hy'] at hfill
      exact hfill
    · intro u hu
      refine ⟨fill u, hfill_mem u hu, ?_⟩
      exact hdrop_fill u
    · intro y hy
      calc
        (∏ i : Fin h, g i (y i)) =
            ∏ i : Fin h, g i (fill (drop y) i) :=
              congrArg (fun v : Fin h → Site => ∏ i : Fin h, g i (v i))
                (hfill_drop y hy).symm
        _ = ∏ i : E, f i (drop y i) := hprod_fill (drop y)
  rw [show (∑ y ∈ (Fintype.piFinset T).filter (fun y => y a = y b),
      ∏ i : Fin h, g i (y i)) = ∑ y ∈ S, ∏ i : Fin h, g i (y i) by rfl,
    hsum_image]
  simpa [D, f] using
    (Finset.prod_univ_sum (fun i : E => T i.1)
      (fun i v => if i = ea then g a v * g b v else g i.1 v)).symm

private theorem otherBlocksFreeKernel_eq_reducedProduct {h : ℕ}
    (I : ReplicaPartition h) (a b : Fin h) (hrel : I.r a b)
    (m : ℕ) (z y : LatticeConfiguration h) :
    otherBlocksFreeKernel I a m z y =
      ∏ i : {j : Fin h // j ≠ b},
        if i.1 ∈ (replicaBlockRepresentatives I).filter (fun c => ¬ I.r c a)
        then Critical2DKPZ.srwKernel m (y i.1 - z i.1) else 1 := by
  classical
  let E := {j : Fin h // j ≠ b}
  let R := (replicaBlockRepresentatives I).filter (fun c => ¬ I.r c a)
  let P : Finset E := Finset.univ.filter (fun i => i.1 ∈ R)
  have hbrel : I.r b a := I.symm' hrel
  have hRnotb : ∀ c ∈ R, c ≠ b := by
    intro c hc hcb
    subst c
    exact (Finset.mem_filter.mp hc).2 hbrel
  have hbij :
      (∏ c ∈ R, Critical2DKPZ.srwKernel m (y c - z c)) =
        ∏ i ∈ P, Critical2DKPZ.srwKernel m (y i.1 - z i.1) := by
    apply Finset.prod_bij (fun c hc => ⟨c, hRnotb c hc⟩)
    · intro c hc
      simpa [P] using hc
    · intro c hc d hd hcd
      exact congrArg Subtype.val hcd
    · intro i hi
      have hir : i.1 ∈ R := (Finset.mem_filter.mp hi).2
      refine ⟨i.1, hir, ?_⟩
      apply Subtype.ext
      rfl
    · intro c hc
      rfl
  have hfilter :
      (∏ i ∈ P, Critical2DKPZ.srwKernel m (y i.1 - z i.1)) =
        ∏ i : E, if i.1 ∈ R then Critical2DKPZ.srwKernel m (y i.1 - z i.1) else 1 := by
    simp [P, Finset.prod_filter]
  calc
    otherBlocksFreeKernel I a m z y =
        ∏ c ∈ R, Critical2DKPZ.srwKernel m (y c - z c) := rfl
    _ = ∏ i ∈ P, Critical2DKPZ.srwKernel m (y i.1 - z i.1) := hbij
    _ = ∏ i : E, if i.1 ∈ R then Critical2DKPZ.srwKernel m (y i.1 - z i.1) else 1 := hfilter
    _ = _ := by simp [E, R]



private theorem product_srwKernel_zero_of_not_pi {h : ℕ} (r : ℕ)
    (x y : LatticeConfiguration h)
    (hy : y ∉ Fintype.piFinset (fun i : Fin h => Critical2DKPZ.Polymer.endpoints (x i) r)) :
    (∏ i : Fin h, Critical2DKPZ.srwKernel r (x i - y i)) = 0 := by
  classical
  have hnot : ¬∀ i, y i ∈ Critical2DKPZ.Polymer.endpoints (x i) r := by
    simpa only [Fintype.mem_piFinset] using hy
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  have hzero : Critical2DKPZ.srwKernel r (x i - y i) = 0 := by
    rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
    exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem r (x i) (y i) hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

private theorem product_renewalKernelFactors {h : ℕ} (I : ReplicaPartition h)
    (a : Fin h) (σ2 : ℝ) (k r : ℕ) (z x y : LatticeConfiguration h) :
    Collision.spatialRenewal σ2 k (y a - z a) * otherBlocksFreeKernel I a k z y *
        (∏ i : Fin h, Critical2DKPZ.srwKernel r (x i - y i)) =
      ∏ i : Fin h,
        ((if i = a then Collision.spatialRenewal σ2 k (y a - z a) else 1) *
          Critical2DKPZ.srwKernel r (x i - y i) *
          (if i ∈ (replicaBlockRepresentatives I).filter (fun c => ¬ I.r c a)
            then Critical2DKPZ.srwKernel k (y i - z i) else 1)) := by
  classical
  let R := (replicaBlockRepresentatives I).filter (fun c => ¬ I.r c a)
  have hrenewal : (∏ i : Fin h,
      if i = a then Collision.spatialRenewal σ2 k (y a - z a) else 1) =
        Collision.spatialRenewal σ2 k (y a - z a) := by
    calc
      _ = (∏ i ∈ Finset.univ.erase a,
            (if i = a then Collision.spatialRenewal σ2 k (y a - z a) else 1)) *
          (if a = a then Collision.spatialRenewal σ2 k (y a - z a) else 1) := by
            symm
            exact Finset.prod_erase_mul Finset.univ
              (fun i => if i = a then Collision.spatialRenewal σ2 k (y a - z a) else 1)
              (Finset.mem_univ a)
      _ = Collision.spatialRenewal σ2 k (y a - z a) := by
            simp
  have hother : (∏ i : Fin h,
      if i ∈ R then Critical2DKPZ.srwKernel k (y i - z i) else 1) =
        otherBlocksFreeKernel I a k z y := by
    calc
      (∏ i : Fin h,
          if i ∈ R then Critical2DKPZ.srwKernel k (y i - z i) else 1) =
          ∏ i ∈ R, Critical2DKPZ.srwKernel k (y i - z i) := by
            rw [← Finset.prod_filter]
            rw [Finset.filter_univ_mem]
      _ = otherBlocksFreeKernel I a k z y := rfl
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  rw [hrenewal, hother]
  ring

private theorem spatialRenewal_kernelStep_le {h : ℕ} (I : ReplicaPartition h)
    (a b : Fin h) (hab : a ≠ b) (hrel : I.r a b)
    (σ2 : ℝ) (hσ : 0 ≤ σ2) (k r : ℕ) (z x : LatticeConfiguration h)
    (hx : IsCollisionConfiguration I x) :
    (∑' y : LatticeConfiguration h,
      Collision.spatialRenewal σ2 k (y a - z a) * otherBlocksFreeKernel I a k z y *
        Critical2DKPZ.MomentBounds.freeReplicaKernel r I I y x) ≤
      (∑' v : Site,
        Collision.spatialRenewal σ2 k (v - z a) *
          Critical2DKPZ.srwKernel r (x a - v) ^ 2) *
        otherBlocksFreeKernel I a (k + r) z x := by
  classical
  let T : Fin h → Finset Site := fun i => Critical2DKPZ.Polymer.endpoints (x i) r
  let S : Finset (LatticeConfiguration h) := Fintype.piFinset T
  let R := (replicaBlockRepresentatives I).filter (fun c => ¬ I.r c a)
  let B : LatticeConfiguration h → ℝ := fun y =>
    Collision.spatialRenewal σ2 k (y a - z a) * otherBlocksFreeKernel I a k z y
  let Q : LatticeConfiguration h → ℝ := fun y =>
    ∏ i : Fin h, Critical2DKPZ.srwKernel r (x i - y i)
  let F : LatticeConfiguration h → ℝ := fun y =>
    B y * Critical2DKPZ.MomentBounds.freeReplicaKernel r I I y x
  let H : LatticeConfiguration h → ℝ := fun y =>
    if y a = y b then B y * Q y else 0
  let G : Fin h → Site → ℝ := fun i v =>
    (if i = a then Collision.spatialRenewal σ2 k (v - z a) else 1) *
      Critical2DKPZ.srwKernel r (x i - v) *
      (if i ∈ R then Critical2DKPZ.srwKernel k (v - z i) else 1)
  let E := {j : Fin h // j ≠ b}
  let ea : E := ⟨a, hab⟩
  let M : ℝ := ∑' v : Site,
    Collision.spatialRenewal σ2 k (v - z a) *
      Critical2DKPZ.srwKernel r (x a - v) ^ 2
  have haR : a ∉ R := by
    intro ha
    exact (Finset.mem_filter.mp ha).2 (I.refl' a)
  have hbR : b ∉ R := by
    intro hb
    exact (Finset.mem_filter.mp hb).2 (I.symm' hrel)
  have hTab : T a = T b := by
    dsimp [T]
    congr 1
    exact hx.1 a b hrel
  have hprod_nonneg (y : LatticeConfiguration h) : 0 ≤ Q y := by
    dsimp [Q]
    apply Finset.prod_nonneg
    intro i hi
    exact Critical2DKPZ.srwKernel_nonneg r (x i - y i)
  have hB_nonneg (y : LatticeConfiguration h) : 0 ≤ B y := by
    dsimp [B]
    exact mul_nonneg (Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ k _)
      (otherBlocksFreeKernel_nonneg I a k z y)
  have hfree (y : LatticeConfiguration h) :
      Critical2DKPZ.MomentBounds.freeReplicaKernel r I I y x ≤
        if y a = y b then Q y else 0 := by
    unfold Critical2DKPZ.MomentBounds.freeReplicaKernel
    by_cases hc : IsCollisionConfiguration I y ∧ IsCollisionConfiguration I x
    · have hyab : y a = y b := hc.1.1 a b hrel
      simp [hc, hyab, Q]
    · by_cases hyab : y a = y b
      · simp [hc, hyab, hprod_nonneg y]
      · simp [hc, hyab]
  have hpointwise (y : LatticeConfiguration h) : F y ≤ H y := by
    by_cases hyab : y a = y b
    · have hfree' : Critical2DKPZ.MomentBounds.freeReplicaKernel r I I y x ≤ Q y := by
        simpa [hyab] using hfree y
      calc
        F y ≤ B y * Q y := by
          dsimp [F]
          exact mul_le_mul_of_nonneg_left hfree' (hB_nonneg y)
        _ = H y := by simp [H, hyab]
    · have hfree' : Critical2DKPZ.MomentBounds.freeReplicaKernel r I I y x ≤ 0 := by
        simpa [hyab] using hfree y
      have hfree0 : Critical2DKPZ.MomentBounds.freeReplicaKernel r I I y x = 0 :=
        le_antisymm hfree' (Critical2DKPZ.MomentBounds.freeReplicaKernel_nonneg r I I y x)
      simp [F, H, hyab, hfree0]
  have hQzero (y : LatticeConfiguration h) (hy : y ∉ S) : Q y = 0 :=
    product_srwKernel_zero_of_not_pi r x y (by simpa [S, T] using hy)
  have hFzero (y : LatticeConfiguration h) (hy : y ∉ S) : F y = 0 := by
    have hfree' : Critical2DKPZ.MomentBounds.freeReplicaKernel r I I y x ≤ 0 := by
      simpa [hQzero y hy] using hfree y
    have hfree0 : Critical2DKPZ.MomentBounds.freeReplicaKernel r I I y x = 0 :=
      le_antisymm hfree' (Critical2DKPZ.MomentBounds.freeReplicaKernel_nonneg r I I y x)
    simp [F, hfree0]
  have hHzero (y : LatticeConfiguration h) (hy : y ∉ S) : H y = 0 := by
    by_cases hp : y a = y b
    · simp [H, hp, hQzero y hy]
    · simp [H, hp]
  have hsum_le : (∑' y : LatticeConfiguration h, F y) ≤
      ∑' y : LatticeConfiguration h, H y := by
    calc
      _ = ∑ y ∈ S, F y := tsum_eq_sum hFzero
      _ ≤ ∑ y ∈ S, H y := Finset.sum_le_sum fun y hy => hpointwise y
      _ = _ := (tsum_eq_sum hHzero).symm
  have hsum_filter : (∑ y ∈ S, H y) =
      ∑ y ∈ S.filter (fun y => y a = y b), B y * Q y := by
    dsimp [H]
    rw [← Finset.sum_filter]
  have hGprod (y : LatticeConfiguration h) :
      (∏ i : Fin h,
        ((if i = a then Collision.spatialRenewal σ2 k (y a - z a) else 1) *
          Critical2DKPZ.srwKernel r (x i - y i) *
          (if i ∈ R then Critical2DKPZ.srwKernel k (y i - z i) else 1))) =
        ∏ i : Fin h, G i (y i) := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hia : i = a
    · subst i
      simp [G]
    · simp [G, hia]
  have hGsum :
      (∑ y ∈ S.filter (fun y => y a = y b), B y * Q y) =
        ∏ i : E, ∑ v ∈ T i.1,
          if i = ea then G a v * G b v else G i.1 v := by
    calc
      _ = ∑ y ∈ S.filter (fun y => y a = y b), ∏ i : Fin h, G i (y i) := by
        apply Finset.sum_congr rfl
        intro y hy
        calc
          B y * Q y =
              ∏ i : Fin h,
                ((if i = a then Collision.spatialRenewal σ2 k (y a - z a) else 1) *
                  Critical2DKPZ.srwKernel r (x i - y i) *
                  (if i ∈ R then Critical2DKPZ.srwKernel k (y i - z i) else 1)) := by
                    simpa [B, Q, R] using product_renewalKernelFactors I a σ2 k r z x y
          _ = ∏ i : Fin h, G i (y i) := hGprod y
      _ = _ := by
        simpa [S] using sum_pairFilter_prod a b hab T hTab G
  have hsum_special : (∑ v ∈ T a,
        G a v * G b v) = M := by
    have hterm (v : Site) :
        G a v * G b v =
          Collision.spatialRenewal σ2 k (v - z a) *
            Critical2DKPZ.srwKernel r (x a - v) ^ 2 := by
      calc
        G a v * G b v =
            (Collision.spatialRenewal σ2 k (v - z a) *
              Critical2DKPZ.srwKernel r (x a - v)) *
                Critical2DKPZ.srwKernel r (x b - v) := by
                  simp [G, haR, hbR, hab.symm]
        _ = Collision.spatialRenewal σ2 k (v - z a) *
              Critical2DKPZ.srwKernel r (x a - v) ^ 2 := by
                rw [← hx.1 a b hrel]
                ring
    have hfinite :
        (∑ v ∈ T a, Collision.spatialRenewal σ2 k (v - z a) *
          Critical2DKPZ.srwKernel r (x a - v) ^ 2) = M := by
      dsimp [M, T]
      symm
      apply tsum_eq_sum
      intro v hv
      have hqzero : Critical2DKPZ.srwKernel r (x a - v) = 0 := by
        rw [Critical2DKPZ.Polymer.srwKernel_sub_swap r (x a) v]
        exact Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem r (x a) v hv
      simp [hqzero]
    calc
      _ = ∑ v ∈ T a, Collision.spatialRenewal σ2 k (v - z a) *
            Critical2DKPZ.srwKernel r (x a - v) ^ 2 := by
              apply Finset.sum_congr rfl
              intro v hv
              exact hterm v
      _ = M := hfinite
  have hcoord (i : E) :
      (∑ v ∈ T i.1, if i = ea then G a v * G b v else G i.1 v) =
        if i = ea then M else if i.1 ∈ R then
          Critical2DKPZ.srwKernel (k + r) (x i.1 - z i.1) else 1 := by
    by_cases hie : i = ea
    · subst i
      simpa [ea, haR] using hsum_special
    · have hia : i.1 ≠ a := by
        intro hia
        apply hie
        exact Subtype.ext hia
      by_cases hiR : i.1 ∈ R
      · have hG (v : Site) : G i.1 v =
            Critical2DKPZ.srwKernel r (x i.1 - v) *
              Critical2DKPZ.srwKernel k (v - z i.1) := by
          simp [G, hia, hiR]
        have hconv : (∑ v ∈ T i.1, G i.1 v) =
            Critical2DKPZ.srwKernel (k + r) (x i.1 - z i.1) := by
          calc
            _ = ∑ v ∈ T i.1,
                Critical2DKPZ.srwKernel k (v - z i.1) *
                  Critical2DKPZ.srwKernel r (x i.1 - v) := by
                    apply Finset.sum_congr rfl
                    intro v hv
                    rw [hG]
                    ring
            _ = _ := sum_srwKernel_mul_endpoints_eq_convolution k r
              (z i.1) (x i.1)
        simpa [hie, hiR] using hconv
      · have hG (v : Site) : G i.1 v =
            Critical2DKPZ.srwKernel r (x i.1 - v) := by
          simp [G, hia, hiR]
        have hmass : (∑ v ∈ T i.1, G i.1 v) = 1 := by
          calc
            _ = ∑ v ∈ T i.1, Critical2DKPZ.srwKernel r (x i.1 - v) := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  rw [hG]
            _ = 1 := srwKernel_sum_endpoints_reverse r (x i.1)
        simpa [hie, hiR] using hmass
  have hcoord_prod :
      (∏ i : E, ∑ v ∈ T i.1,
        if i = ea then G a v * G b v else G i.1 v) =
        M * otherBlocksFreeKernel I a (k + r) z x := by
    have hRproduct : (∏ i : E,
        if i.1 ∈ R then Critical2DKPZ.srwKernel (k + r) (x i.1 - z i.1) else 1) =
        otherBlocksFreeKernel I a (k + r) z x := by
      exact (otherBlocksFreeKernel_eq_reducedProduct I a b hrel (k + r) z x).symm
    have hMproduct : (∏ i : E, if i = ea then M else 1) = M := by
      have hrest : (∏ i ∈ Finset.univ.erase ea, if i = ea then M else 1) = 1 := by
        apply Finset.prod_eq_one
        intro i hi
        have hie : i ≠ ea := (Finset.mem_erase.mp hi).1
        simp [hie]
      calc
        _ = (∏ i ∈ Finset.univ.erase ea, if i = ea then M else 1) *
            (if ea = ea then M else 1) := by
              symm
              exact Finset.prod_erase_mul Finset.univ
                (fun i : E => if i = ea then M else 1) (Finset.mem_univ ea)
        _ = M := by rw [hrest]; simp
    have hpoint (i : E) :
        (if i = ea then M else if i.1 ∈ R then
            Critical2DKPZ.srwKernel (k + r) (x i.1 - z i.1) else 1) =
          (if i = ea then M else 1) *
            (if i.1 ∈ R then Critical2DKPZ.srwKernel (k + r) (x i.1 - z i.1) else 1) := by
      by_cases hie : i = ea
      · subst i
        simp [ea, haR]
      · simp [hie]
    calc
      _ = ∏ i : E, if i = ea then M else
          if i.1 ∈ R then Critical2DKPZ.srwKernel (k + r) (x i.1 - z i.1) else 1 := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hcoord i
      _ = ∏ i : E,
          ((if i = ea then M else 1) *
            (if i.1 ∈ R then Critical2DKPZ.srwKernel (k + r) (x i.1 - z i.1) else 1)) := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hpoint i
      _ = (∏ i : E, if i = ea then M else 1) *
          (∏ i : E, if i.1 ∈ R then
            Critical2DKPZ.srwKernel (k + r) (x i.1 - z i.1) else 1) :=
              Finset.prod_mul_distrib
      _ = M * otherBlocksFreeKernel I a (k + r) z x := by rw [hMproduct, hRproduct]
  calc
    _ = ∑' y : LatticeConfiguration h, F y := rfl
    _ ≤ ∑ y ∈ S, H y := hsum_le.trans_eq (tsum_eq_sum hHzero)
    _ = ∑ y ∈ S.filter (fun y => y a = y b), B y * Q y := hsum_filter
    _ = ∏ i : E, ∑ v ∈ T i.1,
          if i = ea then G a v * G b v else G i.1 v := hGsum
    _ = M * otherBlocksFreeKernel I a (k + r) z x := hcoord_prod


private theorem sum_range_spatialRenewal_kernelStep (σ2 : ℝ) (m : ℕ) (d : Site) :
    (∑ n ∈ Finset.range (m + 1),
      ∑' v : Site,
        Collision.spatialRenewal σ2 (m - n) v * σ2 *
          Critical2DKPZ.srwKernel (n + 1) (d - v) ^ 2) =
      Collision.spatialRenewal σ2 (m + 1) d := by
  rw [Collision.spatialRenewal_succ]
  refine Finset.sum_bij (fun n hn => ⟨m - n, by
    have hn' := Finset.mem_range.mp hn
    omega⟩) ?_ ?_ ?_ ?_
  · intro n hn
    simp
  · intro n hn n' hn' heq
    have hnle : n ≤ m := by have := Finset.mem_range.mp hn; omega
    have hn'le : n' ≤ m := by have := Finset.mem_range.mp hn'; omega
    apply (tsub_right_inj hnle hn'le).mp
    exact congrArg Fin.val heq
  · intro j hj
    refine ⟨m - j.val, Finset.mem_range.mpr ?_, ?_⟩
    · have hjle : j.val ≤ m := by omega
      omega
    · apply Fin.ext
      exact Nat.sub_sub_self (by omega : j.val ≤ m)
  · intro n hn
    have hnle : n ≤ m := by have := Finset.mem_range.mp hn; omega
    have htime : m + 1 - (m - n) = n + 1 := by omega
    rw [htime]

private theorem spatialRenewalKernel_shift (σ2 : ℝ) (k r : ℕ) (z x : Site) :
    (∑' v : Site,
      Collision.spatialRenewal σ2 k (v - z) *
        Critical2DKPZ.srwKernel r (x - v) ^ 2) =
      ∑' u : Site,
        Collision.spatialRenewal σ2 k u *
          Critical2DKPZ.srwKernel r ((x - z) - u) ^ 2 := by
  calc
    _ = ∑' u : Site,
        Collision.spatialRenewal σ2 k ((Equiv.addLeft z u) - z) *
          Critical2DKPZ.srwKernel r (x - Equiv.addLeft z u) ^ 2 :=
      (Equiv.addLeft z).tsum_eq (fun v : Site =>
        Collision.spatialRenewal σ2 k (v - z) *
          Critical2DKPZ.srwKernel r (x - v) ^ 2) |>.symm
    _ = _ := by
      apply tsum_congr
      intro u
      have h1 : (Equiv.addLeft z u) - z = u := by
        simp [Equiv.addLeft]
      have h2 : x - Equiv.addLeft z u = (x - z) - u := by
        simp [Equiv.addLeft]
        abel
      rw [h1, h2]

/-- The absolute interacting kernel is bounded by spatial renewal times the spectator-block free kernel. -/
theorem interactingReplicaKernelAbs_le_spatialRenewal {h : ℕ} (β : ℝ)
    (I : ReplicaPartition h)
    (hmom : |replicaPartitionDisorderMoment β I| ≤ Critical2DKPZ.Polymer.sigmaSq β)
    {a b : Fin h} (hab : a ≠ b) (hrel : I.r a b) (m : ℕ)
    (z x : LatticeConfiguration h) :
    interactingReplicaKernelAbs β I m z x ≤
      Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) m (x a - z a) *
        otherBlocksFreeKernel I a m z x := by
  classical
  have hσ : 0 ≤ Critical2DKPZ.Polymer.sigmaSq β :=
    le_trans (abs_nonneg _) hmom
  induction m using Nat.strong_induction_on generalizing z x with
  | h m ih =>
      cases m with
      | zero =>
          by_cases hz : z = x ∧ IsCollisionConfiguration I x
          · rcases hz with ⟨rfl, hx⟩
            simp [interactingReplicaKernelAbs, Collision.spatialRenewal_zero,
              otherBlocksFreeKernel, Critical2DKPZ.srwKernel_zero, hx]
          · have hright :
                0 ≤ Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) 0
                    (x a - z a) * otherBlocksFreeKernel I a 0 z x :=
              mul_nonneg
                (Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ 0 _)
                (otherBlocksFreeKernel_nonneg I a 0 z x)
            simpa [interactingReplicaKernelAbs, hz] using hright
      | succ m =>
          by_cases hx : IsCollisionConfiguration I x
          ·
            let M : ℕ → ℝ := fun n =>
              ∑' v : Site,
                Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m - n)
                    v *
                  Critical2DKPZ.srwKernel (n + 1) ((x a - z a) - v) ^ 2
            let O : ℝ := otherBlocksFreeKernel I a (m + 1) z x
            have hterm_nonneg (n : ℕ) :
                0 ≤ ∑' y : LatticeConfiguration h,
                  interactingReplicaKernelAbs β I (m - n) z y *
                    freeReplicaKernel (n + 1) I I y x := by
              apply tsum_nonneg
              intro y
              exact mul_nonneg
                (interactingReplicaKernelAbs_nonneg β I (m - n) z y)
                (freeReplicaKernel_nonneg (n + 1) I I y x)
            have hinner (n : ℕ) (hn : n ∈ Finset.range (m + 1)) :
                (∑' y : LatticeConfiguration h,
                  interactingReplicaKernelAbs β I (m - n) z y *
                    freeReplicaKernel (n + 1) I I y x) ≤ M n * O := by
              let S : Finset (LatticeConfiguration h) :=
                Fintype.piFinset (fun i : Fin h =>
                  Critical2DKPZ.Polymer.endpoints (x i) (n + 1))
              have hpoint (y : LatticeConfiguration h) :
                  interactingReplicaKernelAbs β I (m - n) z y *
                      freeReplicaKernel (n + 1) I I y x ≤
                    Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                        (m - n) (y a - z a) *
                      otherBlocksFreeKernel I a (m - n) z y *
                        freeReplicaKernel (n + 1) I I y x := by
                exact mul_le_mul_of_nonneg_right
                  (ih (m - n) (by have hn' := Finset.mem_range.mp hn; omega) z y)
                  (freeReplicaKernel_nonneg (n + 1) I I y x)
              have hfree_zero (y : LatticeConfiguration h) (hy : y ∉ S) :
                  freeReplicaKernel (n + 1) I I y x = 0 := by
                have hqzero :
                    (∏ i : Fin h, Critical2DKPZ.srwKernel (n + 1) (x i - y i)) = 0 :=
                  product_srwKernel_zero_of_not_pi (n + 1) x y (by
                    simpa [S] using hy)
                unfold freeReplicaKernel
                simp [hx, hqzero]
              have hleft_zero (y : LatticeConfiguration h) (hy : y ∉ S) :
                  interactingReplicaKernelAbs β I (m - n) z y *
                    freeReplicaKernel (n + 1) I I y x = 0 := by
                rw [hfree_zero y hy]
                ring
              have hright_zero (y : LatticeConfiguration h) (hy : y ∉ S) :
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                      (m - n) (y a - z a) *
                    otherBlocksFreeKernel I a (m - n) z y *
                      freeReplicaKernel (n + 1) I I y x = 0 := by
                rw [hfree_zero y hy]
                ring
              have hsleft : Summable (fun y : LatticeConfiguration h =>
                  interactingReplicaKernelAbs β I (m - n) z y *
                    freeReplicaKernel (n + 1) I I y x) :=
                summable_of_ne_finset_zero (s := S) hleft_zero
              have hsright : Summable (fun y : LatticeConfiguration h =>
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                      (m - n) (y a - z a) *
                    otherBlocksFreeKernel I a (m - n) z y *
                      freeReplicaKernel (n + 1) I I y x) :=
                summable_of_ne_finset_zero (s := S) hright_zero
              have hsumle := hsleft.tsum_le_tsum hpoint hsright
              calc
                _ ≤ ∑' y : LatticeConfiguration h,
                    Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                        (m - n) (y a - z a) *
                      otherBlocksFreeKernel I a (m - n) z y *
                        freeReplicaKernel (n + 1) I I y x := hsumle
                _ ≤ M n * O := by
                    have hstep := spatialRenewal_kernelStep_le I a b hab hrel
                      (Critical2DKPZ.Polymer.sigmaSq β) hσ (m - n) (n + 1) z x hx
                    have htime : (m - n) + (n + 1) = m + 1 := by
                      have hn' := Finset.mem_range.mp hn
                      omega
                    calc
                      _ ≤ (∑' v : Site,
                            Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                                (m - n) (v - z a) *
                              Critical2DKPZ.srwKernel (n + 1) (x a - v) ^ 2) *
                            otherBlocksFreeKernel I a (m - n + (n + 1)) z x := hstep
                      _ = M n * O := by
                          rw [htime]
                          dsimp [M, O]
                          rw [← spatialRenewalKernel_shift
                            (Critical2DKPZ.Polymer.sigmaSq β) (m - n) (n + 1)
                            (z a) (x a)]
            have hA_nonneg :
                0 ≤ ∑ n ∈ Finset.range (m + 1),
                  ∑' y : LatticeConfiguration h,
                    interactingReplicaKernelAbs β I (m - n) z y *
                      freeReplicaKernel (n + 1) I I y x := by
              apply Finset.sum_nonneg
              intro n hn
              exact hterm_nonneg n
            have hsum_bound :
                (∑ n ∈ Finset.range (m + 1),
                  ∑' y : LatticeConfiguration h,
                    interactingReplicaKernelAbs β I (m - n) z y *
                      freeReplicaKernel (n + 1) I I y x) ≤
                ∑ n ∈ Finset.range (m + 1), M n * O := by
              apply Finset.sum_le_sum
              intro n hn
              exact hinner n hn
            have hfactor :
                Critical2DKPZ.Polymer.sigmaSq β *
                    (∑ n ∈ Finset.range (m + 1), M n * O) =
                  (∑ n ∈ Finset.range (m + 1),
                    Critical2DKPZ.Polymer.sigmaSq β * M n) * O := by
              calc
                _ = ∑ n ∈ Finset.range (m + 1),
                      Critical2DKPZ.Polymer.sigmaSq β * (M n * O) := by
                    rw [Finset.mul_sum]
                _ = ∑ n ∈ Finset.range (m + 1),
                      (Critical2DKPZ.Polymer.sigmaSq β * M n) * O := by
                    apply Finset.sum_congr rfl
                    intro n hn
                    ring
                _ = _ := by rw [Finset.sum_mul]
            have hrenewal :
                (∑ n ∈ Finset.range (m + 1),
                  Critical2DKPZ.Polymer.sigmaSq β * M n) =
                Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                  (m + 1) (x a - z a) := by
              unfold M
              calc
                _ = ∑ n ∈ Finset.range (m + 1),
                      ∑' v : Site,
                        Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                            (m - n) v * Critical2DKPZ.Polymer.sigmaSq β *
                          Critical2DKPZ.srwKernel (n + 1) ((x a - z a) - v) ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro n hn
                    rw [← tsum_mul_left]
                    apply tsum_congr
                    intro v
                    ring
                _ = Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                      (m + 1) (x a - z a) :=
                    sum_range_spatialRenewal_kernelStep
                      (Critical2DKPZ.Polymer.sigmaSq β) m (x a - z a)
            calc
              interactingReplicaKernelAbs β I (m + 1) z x =
                  |replicaPartitionDisorderMoment β I| *
                    (∑ n ∈ Finset.range (m + 1),
                      ∑' y : LatticeConfiguration h,
                        interactingReplicaKernelAbs β I (m - n) z y *
                          freeReplicaKernel (n + 1) I I y x) := by
                    simp only [interactingReplicaKernelAbs]
              _ ≤ Critical2DKPZ.Polymer.sigmaSq β *
                    (∑ n ∈ Finset.range (m + 1),
                      ∑' y : LatticeConfiguration h,
                        interactingReplicaKernelAbs β I (m - n) z y *
                          freeReplicaKernel (n + 1) I I y x) :=
                    mul_le_mul_of_nonneg_right hmom hA_nonneg
              _ ≤ Critical2DKPZ.Polymer.sigmaSq β *
                    (∑ n ∈ Finset.range (m + 1), M n * O) :=
                    mul_le_mul_of_nonneg_left hsum_bound hσ
              _ = Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                    (m + 1) (x a - z a) * otherBlocksFreeKernel I a (m + 1) z x := by
                    rw [hfactor, hrenewal]
          · have hright :
                0 ≤ Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
                    (m + 1) (x a - z a) * otherBlocksFreeKernel I a (m + 1) z x :=
              mul_nonneg
                (Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ (m + 1) _)
                (otherBlocksFreeKernel_nonneg I a (m + 1) z x)
            have hfree_zero (n : ℕ) (y : LatticeConfiguration h) :
                freeReplicaKernel (n + 1) I I y x = 0 := by
              simp [freeReplicaKernel, hx]
            have hinner_zero (n : ℕ) :
                (∑' y : LatticeConfiguration h,
                  interactingReplicaKernelAbs β I (m - n) z y *
                    freeReplicaKernel (n + 1) I I y x) = 0 := by
              simp_rw [hfree_zero n]
              simp
            have hzero : interactingReplicaKernelAbs β I (m + 1) z x = 0 := by
              simp only [interactingReplicaKernelAbs, hinner_zero,
                Finset.sum_const_zero, mul_zero]
            rw [hzero]
            exact hright

end

end Critical2DKPZ.MomentBounds

end
