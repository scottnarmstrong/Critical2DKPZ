/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25BlockConfigurationSum
public import Critical2DKPZ.SHF.Moments.PairStratumInteractionBounds
import Mathlib.Tactic

/-! # Exact one-step renewal factorization on a pair stratum -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

attribute [local instance] Classical.propDecidable

private theorem pairPartition_collision_iff {h : ℕ} (α : CollisionPair h)
    (x : LatticeConfiguration h) :
    IsCollisionConfiguration (pairPartition α) x ↔ x α.1.1 = x α.1.2 := by
  constructor
  · intro hx
    exact (isEqualityConfiguration_pair_iff α x).mp hx.1
  · intro hpair
    refine ⟨(isEqualityConfiguration_pair_iff α x).mpr hpair, ?_⟩
    intro i j hi hj hnot
    obtain ⟨i', hi'ne, hi'rel⟩ := hi
    obtain ⟨j', hj'ne, hj'rel⟩ := hj
    have hipair : i = α.1.1 ∨ i = α.1.2 := by
      have hrel := (pairPartition_rel α i i').mp hi'rel
      rcases hrel with hEq | ⟨hleft, _⟩
      · exact (hi'ne hEq.symm).elim
      · exact hleft
    have hjpair : j = α.1.1 ∨ j = α.1.2 := by
      have hrel := (pairPartition_rel α j j').mp hj'rel
      rcases hrel with hEq | ⟨hleft, _⟩
      · exact (hj'ne hEq.symm).elim
      · exact hleft
    have hij : (pairPartition α).r i j := by
      exact (pairPartition_rel α i j).mpr (Or.inr ⟨hipair, hjpair⟩)
    exact (hnot hij).elim

private theorem pairPartition_representatives_erase {h : ℕ}
    (α : CollisionPair h) :
    replicaBlockRepresentatives (pairPartition α) = Finset.univ.erase α.1.2 := by
  classical
  let a := α.1.1
  let b := α.1.2
  have hab : a < b := α.2
  ext i
  simp only [replicaBlockRepresentatives, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro hi
    refine ⟨?_, trivial⟩
    intro hEq
    subst i
    have hrel : (pairPartition α).r b a := by
      rw [pairPartition_rel]
      exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
    have hle := hi a hrel
    exact (not_le_of_gt hab) hle
  · rintro ⟨hne, _⟩ j hrel
    rcases (pairPartition_rel α i j).mp hrel with hEq | ⟨hiPair, hjPair⟩
    · exact hEq ▸ le_rfl
    · have hiA : i = a := by
        rcases hiPair with hiA | hiB
        · exact hiA
        · exact (hne hiB).elim
      subst i
      rcases hjPair with hjA | hjB
      · exact hjA ▸ le_rfl
      · exact hjB ▸ hab.le

private theorem otherBlocksFreeKernel_pairPartition_erase {h : ℕ}
    (α : CollisionPair h) (m : ℕ) (z x : LatticeConfiguration h) :
    otherBlocksFreeKernel (pairPartition α) α.1.1 m z x =
      ∏ i ∈ (Finset.univ.erase α.1.2).erase α.1.1,
        srwKernel m (x i - z i) := by
  classical
  let a := α.1.1
  let b := α.1.2
  let R : Finset (Fin h) := (Finset.univ.erase b).erase a
  have hab : a ≠ b := ne_of_lt α.2
  rw [otherBlocksFreeKernel_pairPartition_eq]
  calc
    (∏ i : Fin h, if i = a ∨ i = b then (1 : ℝ) else srwKernel m (x i - z i)) =
        ∏ i : Fin h, if i ∈ R then srwKernel m (x i - z i) else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hia : i = a
      · simp [R, hia]
      · by_cases hib : i = b
        · simp [R, hib]
        · simp [R, hia, hib]
    _ = ∏ i ∈ R, srwKernel m (x i - z i) := Finset.prod_ite_mem_eq R _
    _ = _ := by rfl

private theorem pairPartition_replicaProduct_eq_erase {h : ℕ}
    (α : CollisionPair h) (f : Fin h → ℝ) :
    (∏ i : {i : Fin h // i ∈ replicaBlockRepresentatives (pairPartition α)},
      f i.1) = ∏ i ∈ Finset.univ.erase α.1.2, f i := by
  classical
  let E := {i : Fin h // i ∈ replicaBlockRepresentatives (pairPartition α)}
  let E' := {i : Fin h // i ∈ Finset.univ.erase α.1.2}
  have hreps := pairPartition_representatives_erase α
  let e : E ≃ E' := {
    toFun := fun i => ⟨i.1, by
      have hi : i.1 ∈ replicaBlockRepresentatives (pairPartition α) := i.2
      simpa only [hreps] using hi⟩
    invFun := fun i => ⟨i.1, by
      simpa only [hreps] using i.2⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl }
  calc
    (∏ i : E, f i.1) = ∏ i : E', f i.1 := by
      rw [Fintype.prod_equiv e (fun i : E => f i.1)
        (fun i : E' => f i.1) (by intro i; rfl)]
    _ = ∏ i ∈ Finset.univ.erase α.1.2, f i := by
      rw [← Finset.prod_subtype (Finset.univ.erase α.1.2) (fun i => by simp)
        (fun i => f i)]

/-- On a single-pair collision stratum, one free interval factors exactly into
the pair renewal convolution and independent spectator convolutions. -/
theorem spatialRenewal_kernelStep_pairPartition_eq {h : ℕ}
    (α : CollisionPair h) (σ2 : ℝ) (k r : ℕ)
    (z x : LatticeConfiguration h) (hx : x α.1.1 = x α.1.2) :
    (∑' y : LatticeConfiguration h,
      Collision.spatialRenewal σ2 k (y α.1.1 - z α.1.1) *
        otherBlocksFreeKernel (pairPartition α) α.1.1 k z y *
        freeReplicaKernel r (pairPartition α) (pairPartition α) y x) =
      (∑' v : Site,
        Collision.spatialRenewal σ2 k (v - z α.1.1) *
          srwKernel r (x α.1.1 - v) ^ 2) *
        otherBlocksFreeKernel (pairPartition α) α.1.1 (k + r) z x := by
  classical
  let a := α.1.1
  let b := α.1.2
  let I := pairPartition α
  let T : Fin h → Finset Site := fun i => endpoints (x i) r
  let S : Finset (LatticeConfiguration h) := Fintype.piFinset T
  let E := {i : Fin h // i ∈ replicaBlockRepresentatives I}
  let F : E → Site → ℝ := fun i v =>
    if i.1 = a then
      Collision.spatialRenewal σ2 k (v - z a) * srwKernel r (x a - v) ^ 2
    else srwKernel k (v - z i.1) * srwKernel r (x i.1 - v)
  have hTa : T a = T b := by
    dsimp [T]
    rw [← hx]
  have hfree (y : LatticeConfiguration h) :
      freeReplicaKernel r I I y x =
        if y a = y b then ∏ i : Fin h, srwKernel r (x i - y i) else 0 := by
    unfold freeReplicaKernel
    rw [pairPartition_collision_iff α y, pairPartition_collision_iff α x, hx]
    simp [a, b]
  have hfreezero (y : LatticeConfiguration h) (hy : y ∉ S) :
      freeReplicaKernel r I I y x = 0 := by
    obtain ⟨i, hi⟩ := not_forall.mp (by
      intro hall
      exact hy (Fintype.mem_piFinset.mpr hall))
    have hq : srwKernel r (x i - y i) = 0 := by
      rw [Polymer.srwKernel_sub_swap]
      exact Polymer.srwKernel_eq_zero_of_not_mem r (x i) (y i) hi
    rw [hfree]
    by_cases hpair : y a = y b
    · have hprod : (∏ j : Fin h, srwKernel r (x j - y j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hq
      simp [hpair, hprod]
    · simp [hpair]
  have hsum_support :
      (∑' y : LatticeConfiguration h,
        Collision.spatialRenewal σ2 k (y a - z a) *
          otherBlocksFreeKernel I a k z y * freeReplicaKernel r I I y x) =
        ∑ y ∈ S,
          Collision.spatialRenewal σ2 k (y a - z a) *
            otherBlocksFreeKernel I a k z y * freeReplicaKernel r I I y x := by
    apply tsum_eq_sum
    intro y hy
    rw [hfreezero y hy]
    ring
  have hsum_filter :
      (∑ y ∈ S,
        Collision.spatialRenewal σ2 k (y a - z a) *
          otherBlocksFreeKernel I a k z y * freeReplicaKernel r I I y x) =
        ∑ y ∈ S.filter (fun y => y a = y b),
          Collision.spatialRenewal σ2 k (y a - z a) *
            otherBlocksFreeKernel I a k z y *
              ∏ i : Fin h, srwKernel r (x i - y i) := by
    calc
      _ = ∑ y ∈ S, if y a = y b then
            Collision.spatialRenewal σ2 k (y a - z a) *
              otherBlocksFreeKernel I a k z y *
                ∏ i : Fin h, srwKernel r (x i - y i) else 0 := by
          apply Finset.sum_congr rfl
          intro y hyS
          rw [hfree]
          split_ifs <;> simp
      _ = _ := by rw [Finset.sum_filter]
  have hterm (y : LatticeConfiguration h) (hy : y a = y b) :
      Collision.spatialRenewal σ2 k (y a - z a) *
          otherBlocksFreeKernel I a k z y *
            ∏ i : Fin h, srwKernel r (x i - y i) =
        ∏ i : E, F i (y i.1) := by
    let R : Finset (Fin h) := (Finset.univ.erase b).erase a
    have hab : a ≠ b := ne_of_lt α.2
    have hRprod :
        otherBlocksFreeKernel I a k z y =
          ∏ i ∈ R, srwKernel k (y i - z i) := by
      simpa [R] using otherBlocksFreeKernel_pairPartition_erase α k z y
    have hqprod :
        (∏ i : Fin h, srwKernel r (x i - y i)) =
          srwKernel r (x a - y a) * srwKernel r (x b - y b) *
            ∏ i ∈ R, srwKernel r (x i - y i) := by
      rw [← Finset.mul_prod_erase Finset.univ
        (fun i : Fin h => srwKernel r (x i - y i)) (Finset.mem_univ b)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase b)
        (fun i : Fin h => srwKernel r (x i - y i))
        (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ a⟩)]
      simp only [R]
      ring
    have hqpair : srwKernel r (x b - y b) = srwKernel r (x a - y a) := by
      rw [hx, hy]
    have hprodRep :
        (∏ i : E, F i (y i.1)) =
          (Collision.spatialRenewal σ2 k (y a - z a) *
            srwKernel r (x a - y a) ^ 2) *
            ∏ i ∈ R,
              (srwKernel k (y i - z i) * srwKernel r (x i - y i)) := by
      let g : Fin h → ℝ := fun i =>
        if i = a then
          Collision.spatialRenewal σ2 k (y a - z a) * srwKernel r (x a - y a) ^ 2
        else srwKernel k (y i - z i) * srwKernel r (x i - y i)
      have hconvert : (∏ i : E, F i (y i.1)) = ∏ i : E, g i.1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hia : i.1 = a <;> simp [F, g, hia]
      have hrepProd : (∏ i : E, g i.1) = ∏ i ∈ Finset.univ.erase b, g i := by
        simpa [I, E] using pairPartition_replicaProduct_eq_erase α g
      have haMem : a ∈ Finset.univ.erase b := by simp [hab]
      have hsplit := Finset.prod_erase_mul (Finset.univ.erase b) g haMem
      have hrest :
          (∏ i ∈ R, g i) =
            ∏ i ∈ R,
              (srwKernel k (y i - z i) * srwKernel r (x i - y i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hia : i ≠ a := (Finset.mem_erase.mp hi).1
        simp [g, hia]
      have hfirst : g a =
          Collision.spatialRenewal σ2 k (y a - z a) *
            srwKernel r (x a - y a) ^ 2 := by simp [g]
      calc
        _ = (∏ i ∈ Finset.univ.erase b, g i) := hconvert.trans hrepProd
        _ = (∏ i ∈ R, g i) * g a := hsplit.symm
        _ = _ := by rw [hrest, hfirst]; ring
    rw [hRprod, hqprod, hqpair]
    calc
      Collision.spatialRenewal σ2 k (y a - z a) *
          (∏ i ∈ R, srwKernel k (y i - z i)) *
            (srwKernel r (x a - y a) * srwKernel r (x a - y a) *
              ∏ i ∈ R, srwKernel r (x i - y i)) =
        (Collision.spatialRenewal σ2 k (y a - z a) *
            srwKernel r (x a - y a) ^ 2) *
          ((∏ i ∈ R, srwKernel k (y i - z i)) *
            ∏ i ∈ R, srwKernel r (x i - y i)) := by ring
      _ = (Collision.spatialRenewal σ2 k (y a - z a) *
            srwKernel r (x a - y a) ^ 2) *
          ∏ i ∈ R,
            (srwKernel k (y i - z i) * srwKernel r (x i - y i)) := by
              rw [← Finset.prod_mul_distrib]
      _ = ∏ i : E, F i (y i.1) := hprodRep.symm
  have hsumFact :
      (∑ y ∈ S.filter (fun y => y a = y b),
        Collision.spatialRenewal σ2 k (y a - z a) *
          otherBlocksFreeKernel I a k z y *
            ∏ i : Fin h, srwKernel r (x i - y i)) =
        ∏ i : E, ∑ v ∈ T i.1, F i v := by
    calc
      _ = ∑ y ∈ S.filter (fun y => y a = y b), ∏ i : E, F i (y i.1) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hterm y (Finset.mem_filter.mp hy).2
      _ = _ := by
        have hfilter :
            S.filter (fun y => y a = y b) =
              S.filter (fun y => IsEqualityConfiguration I y) := by
          ext y
          simp only [Finset.mem_filter]
          rw [isEqualityConfiguration_pair_iff α y]
        rw [hfilter]
        exact sum_equalityConfigurations_prod_blocks I x
          ((isEqualityConfiguration_pair_iff α x).mpr hx) r F
  have hpairCoord :
      (∑ v ∈ T a,
        Collision.spatialRenewal σ2 k (v - z a) * srwKernel r (x a - v) ^ 2) =
        ∑' v : Site,
          Collision.spatialRenewal σ2 k (v - z a) * srwKernel r (x a - v) ^ 2 := by
    symm
    apply tsum_eq_sum
    intro v hv
    have hzero : srwKernel r (x a - v) = 0 := by
      rw [Polymer.srwKernel_sub_swap r (x a) v]
      exact Polymer.srwKernel_eq_zero_of_not_mem r (x a) v hv
    simp [hzero]
  have hcoord (i : E) :
      (∑ v ∈ T i.1, F i v) =
        if i.1 = a then
          ∑' v : Site,
            Collision.spatialRenewal σ2 k (v - z a) * srwKernel r (x a - v) ^ 2
        else srwKernel (k + r) (x i.1 - z i.1) := by
    by_cases hia : i.1 = a
    · rcases i with ⟨i, hi⟩
      simp only at hia
      subst i
      simpa [F] using hpairCoord
    · have hconv :
          (∑ v ∈ T i.1,
            srwKernel k (v - z i.1) * srwKernel r (x i.1 - v)) =
            srwKernel (k + r) (x i.1 - z i.1) := by
        have hsum : (∑ v ∈ T i.1,
            srwKernel k (v - z i.1) * srwKernel r (x i.1 - v)) =
            ∑' v : Site,
              srwKernel k (v - z i.1) * srwKernel r (x i.1 - v) := by
          symm
          apply tsum_eq_sum
          intro v hv
          have hzero : srwKernel r (x i.1 - v) = 0 := by
            rw [Polymer.srwKernel_sub_swap]
            exact Polymer.srwKernel_eq_zero_of_not_mem r (x i.1) v hv
          simp [hzero]
        calc
          _ = ∑' v : Site,
                srwKernel k (v - z i.1) * srwKernel r (x i.1 - v) := hsum
          _ = srwKernel (k + r) (x i.1 - z i.1) := by
                symm
                exact Polymer.srwKernel_convolution k r (z i.1) (x i.1)
      simpa [F, hia] using hconv
  have hcoordProd :
      (∏ i : E, ∑ v ∈ T i.1, F i v) =
        (∑' v : Site,
          Collision.spatialRenewal σ2 k (v - z a) * srwKernel r (x a - v) ^ 2) *
          otherBlocksFreeKernel I a (k + r) z x := by
    calc
      _ = ∏ i : E, if i.1 = a then
            ∑' v : Site,
              Collision.spatialRenewal σ2 k (v - z a) * srwKernel r (x a - v) ^ 2
          else srwKernel (k + r) (x i.1 - z i.1) := by
            apply Finset.prod_congr rfl
            intro i hi
            exact hcoord i
      _ = _ := by
        let R : Finset (Fin h) := (Finset.univ.erase b).erase a
        have hab : a ≠ b := ne_of_lt α.2
        let g : Fin h → ℝ := fun i => if i = a then
          ∑' v : Site,
            Collision.spatialRenewal σ2 k (v - z a) * srwKernel r (x a - v) ^ 2
          else srwKernel (k + r) (x i - z i)
        have hrep :
            (∏ i : E, if i.1 = a then
              ∑' v : Site,
                Collision.spatialRenewal σ2 k (v - z a) * srwKernel r (x a - v) ^ 2
            else srwKernel (k + r) (x i.1 - z i.1)) =
              ∏ i ∈ Finset.univ.erase b, g i := by
          simpa [I, E, g] using pairPartition_replicaProduct_eq_erase α g
        have hrest :
            (∏ i ∈ R, g i) =
              ∏ i ∈ R, srwKernel (k + r) (x i - z i) := by
          apply Finset.prod_congr rfl
          intro i hi
          have hia : i ≠ a := (Finset.mem_erase.mp hi).1
          simp [g, hia]
        have haMem : a ∈ Finset.univ.erase b := by simp [hab]
        have hsplit := Finset.prod_erase_mul (Finset.univ.erase b) g haMem
        have hOther :
            otherBlocksFreeKernel I a (k + r) z x =
              ∏ i ∈ R, srwKernel (k + r) (x i - z i) := by
          simpa [R] using otherBlocksFreeKernel_pairPartition_erase α (k + r) z x
        rw [hrep, hsplit.symm, hrest, hOther]
        simp [g]
        ring
  calc
    _ = ∑ y ∈ S,
        Collision.spatialRenewal σ2 k (y a - z a) *
          otherBlocksFreeKernel I a k z y * freeReplicaKernel r I I y x := hsum_support
    _ = ∑ y ∈ S.filter (fun y => y a = y b),
        Collision.spatialRenewal σ2 k (y a - z a) *
          otherBlocksFreeKernel I a k z y *
            ∏ i : Fin h, srwKernel r (x i - y i) := hsum_filter
    _ = ∏ i : E, ∑ v ∈ T i.1, F i v := hsumFact
    _ = _ := hcoordProd

end Critical2DKPZ.SHF.Moments

end
