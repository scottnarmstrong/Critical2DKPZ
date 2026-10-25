/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25InteractingRenewal
public import Critical2DKPZ.MomentBounds.CCR25BlockConfigurationSum
public import Critical2DKPZ.MomentBounds.CCR25SpatialRenewalBounds
public import Critical2DKPZ.MomentBounds.CCR25RenewalReflection
public import Critical2DKPZ.MomentBounds.CCR25WalkBounds
public import Critical2DKPZ.MomentBounds.CCR25FreeOperatorBound
public import Critical2DKPZ.MomentBounds.AiiKSchur
public import Critical2DKPZ.MomentBounds.PairSelection
import Critical2DKPZ.Blocks.StringSumPropagation
import Mathlib.Tactic

/-! # Weighted operator bound for the CCR25 interacting kernel -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem mem_endpoints_translate (z v : Site) (n : ℕ) :
    v ∈ Critical2DKPZ.Polymer.endpoints 0 n ↔
      z + v ∈ Critical2DKPZ.Polymer.endpoints z n := by
  rw [Critical2DKPZ.Polymer.mem_endpoints_iff,
    Critical2DKPZ.Polymer.mem_endpoints_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    calc
      Critical2DKPZ.walkPosition z s n = z + Critical2DKPZ.walkPosition 0 s n :=
        by simpa using Critical2DKPZ.Polymer.walkPosition_add_start z 0 s n
      _ = z + v := by rw [hs]
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    have hwalk : Critical2DKPZ.walkPosition z s n =
        z + Critical2DKPZ.walkPosition 0 s n := by
      simpa using Critical2DKPZ.Polymer.walkPosition_add_start z 0 s n
    rw [hs] at hwalk
    exact (add_left_cancel_iff.mp hwalk).symm

private theorem endpoints_translate (z : Site) (n : ℕ) :
    Critical2DKPZ.Polymer.endpoints z n =
      (Critical2DKPZ.Polymer.endpoints 0 n).image (fun v => z + v) := by
  ext y
  rw [Finset.mem_image]
  constructor
  · intro hy
    refine ⟨y - z, (mem_endpoints_translate z (y - z) n).mpr ?_, ?_⟩
    · simpa using hy
    · ext i
      simp
  · rintro ⟨v, hv, rfl⟩
    exact (mem_endpoints_translate z v n).mp hv

private theorem sum_endpoints_translate (z : Site) (n : ℕ) (f : Site → ℝ) :
    (∑ y ∈ Critical2DKPZ.Polymer.endpoints z n, f (y - z)) =
      ∑ v ∈ Critical2DKPZ.Polymer.endpoints 0 n, f v := by
  rw [endpoints_translate]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v hv
    simp
  · intro u hu v hv huv
    exact add_left_cancel huv

private theorem sum_endpoints_weighted_spatialRenewal_eq_tsum
    (σ2 t : ℝ) (n : ℕ) (z : Site) :
    (∑ y ∈ Critical2DKPZ.Polymer.endpoints z n,
      Real.exp (t * ‖Critical2DKPZ.siteToPlane (y - z)‖) *
        Collision.spatialRenewal σ2 n (y - z)) =
      ∑' v : Site, Real.exp (t * ‖Critical2DKPZ.siteToPlane v‖) *
        Collision.spatialRenewal σ2 n v := by
  rw [sum_endpoints_translate z n (fun v =>
    Real.exp (t * ‖Critical2DKPZ.siteToPlane v‖) * Collision.spatialRenewal σ2 n v)]
  symm
  apply tsum_eq_sum
  intro v hv
  rw [Critical2DKPZ.Blocks.spatialRenewal_eq_zero_of_not_mem_endpoints hv]
  simp

private theorem sum_endpoints_weighted_srwKernel_eq_tsum
    (t : ℝ) (n : ℕ) (z : Site) :
    (∑ y ∈ Critical2DKPZ.Polymer.endpoints z n,
      Real.exp (t * ‖Critical2DKPZ.siteToPlane (y - z)‖) *
        Critical2DKPZ.srwKernel n (y - z)) =
      ∑' v : Site, Real.exp (t * ‖Critical2DKPZ.siteToPlane v‖) *
        Critical2DKPZ.srwKernel n v := by
  rw [sum_endpoints_translate z n (fun v =>
    Real.exp (t * ‖Critical2DKPZ.siteToPlane v‖) * Critical2DKPZ.srwKernel n v)]
  symm
  apply tsum_eq_sum
  intro v hv
  have hzero := Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem n 0 v hv
  have hzero' : Critical2DKPZ.srwKernel n v = 0 := by
    simpa only [sub_zero] using hzero
  rw [hzero']
  simp

private theorem endpoint_sub_not_mem {n : ℕ} {z y : Site}
    (hy : y ∉ Critical2DKPZ.Polymer.endpoints z n) :
    y - z ∉ Critical2DKPZ.Polymer.endpoints 0 n := by
  intro hv
  apply hy
  have hmem := (mem_endpoints_translate z (y - z) n).mp hv
  simpa using hmem

private theorem mem_endpoints_reverse (n : ℕ) (z y : Site) :
    z ∈ Critical2DKPZ.Polymer.endpoints y n ↔
      y ∈ Critical2DKPZ.Polymer.endpoints z n := by
  have hreverse : ∀ {u v : Site}, v ∈ Critical2DKPZ.Polymer.endpoints u n →
      u ∈ Critical2DKPZ.Polymer.endpoints v n := by
    intro u v huv
    rw [Critical2DKPZ.Polymer.mem_endpoints_iff] at huv ⊢
    obtain ⟨s, hs⟩ := huv
    refine ⟨fun i => Critical2DKPZ.Polymer.oppositeStep (s i), ?_⟩
    have hstart : Critical2DKPZ.walkPosition u s n =
        u + Critical2DKPZ.walkPosition 0 s n := by
      simpa using Critical2DKPZ.Polymer.walkPosition_add_start u 0 s n
    have hdisp : Critical2DKPZ.walkPosition 0 s n = v - u := by
      calc
        _ = u + Critical2DKPZ.walkPosition 0 s n - u := by abel
        _ = v - u := by rw [← hstart, hs]
    calc
      Critical2DKPZ.walkPosition v
          (fun i => Critical2DKPZ.Polymer.oppositeStep (s i)) n =
          v + Critical2DKPZ.walkPosition 0
            (fun i => Critical2DKPZ.Polymer.oppositeStep (s i)) n := by
              simpa using Critical2DKPZ.Polymer.walkPosition_add_start v 0
                (fun i => Critical2DKPZ.Polymer.oppositeStep (s i)) n
      _ = v - Critical2DKPZ.walkPosition 0 s n := by
        rw [Critical2DKPZ.Polymer.walkPosition_opposite]
        abel
      _ = u := by rw [hdisp]; abel
  exact ⟨hreverse, hreverse⟩

private theorem siteToPlane_neg (z : Site) :
    Critical2DKPZ.siteToPlane (-z) = -Critical2DKPZ.siteToPlane z := by
  ext i
  simp [Critical2DKPZ.siteToPlane]

private theorem interactingReplicaKernelAbs_zero_of_not_collision_left {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h) :
    ∀ n z x, ¬ IsCollisionConfiguration I z →
      interactingReplicaKernelAbs β I n z x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro z x hz
      cases n with
      | zero =>
          simp only [interactingReplicaKernelAbs]
          by_cases hEq : z = x
          · subst x
            simp [hz]
          · simp [hEq]
      | succ m =>
          have hsum :
              (∑ r ∈ Finset.range (m + 1),
                ∑' y : LatticeConfiguration h,
                  interactingReplicaKernelAbs β I (m - r) z y *
                    freeReplicaKernel (r + 1) I I y x) = 0 := by
            apply Finset.sum_eq_zero
            intro r hr
            calc
              _ = ∑' y : LatticeConfiguration h, (0 : ℝ) := by
                apply tsum_congr
                intro y
                have hy := ih (m - r) (by omega) z y hz
                rw [hy]
                simp
              _ = 0 := tsum_zero
          rw [interactingReplicaKernelAbs, hsum]
          ring

private theorem interactingReplicaKernelAbs_zero_of_not_collision_right {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h) :
    ∀ n z x, ¬ IsCollisionConfiguration I x →
      interactingReplicaKernelAbs β I n z x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro z x hx
      cases n with
      | zero =>
          simp only [interactingReplicaKernelAbs]
          by_cases hEq : z = x
          · subst x
            simp [hx]
          · simp [hEq]
      | succ m =>
          have hsum :
              (∑ r ∈ Finset.range (m + 1),
                ∑' y : LatticeConfiguration h,
                  interactingReplicaKernelAbs β I (m - r) z y *
                    freeReplicaKernel (r + 1) I I y x) = 0 := by
            apply Finset.sum_eq_zero
            intro r hr
            calc
              _ = ∑' y : LatticeConfiguration h, (0 : ℝ) := by
                apply tsum_congr
                intro y
                have hfree : freeReplicaKernel (r + 1) I I y x = 0 := by
                  simp [freeReplicaKernel, hx]
                rw [hfree]
                simp
              _ = 0 := tsum_zero
          rw [interactingReplicaKernelAbs, hsum]
          ring

private theorem interactingReplicaKernelAbs_zero_of_endpoint_miss {h : ℕ}
    (I : ReplicaPartition h) (hI : I ≠ ⊥) (β : ℝ)
    (hmom : |replicaPartitionDisorderMoment β I| ≤ Critical2DKPZ.Polymer.sigmaSq β)
    (n : ℕ) (z x : LatticeConfiguration h)
    (hz : IsCollisionConfiguration I z) (hx : IsCollisionConfiguration I x)
    (hmiss : ∃ i : Fin h, x i ∉ Critical2DKPZ.Polymer.endpoints (z i) n) :
    interactingReplicaKernelAbs β I n z x = 0 := by
  classical
  obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete I hI
  let a := α.val.1
  let b := α.val.2
  have hab : a ≠ b := ne_of_lt α.property
  obtain ⟨i, hi⟩ := hmiss
  let r := canonicalReplicaBlockRepresentative I i
  have hr : r ∈ replicaBlockRepresentatives I :=
    canonicalReplicaBlockRepresentative_mem I i
  have hri : I.r r i := canonicalReplicaBlockRepresentative_rel I i
  have hnot : x r - z r ∉ Critical2DKPZ.Polymer.endpoints 0 n := by
    have h := endpoint_sub_not_mem hi
    simpa [hx.1 r i hri, hz.1 r i hri] using h
  have hdom := interactingReplicaKernelAbs_le_spatialRenewal β I hmom hab hα
    (a := a) (b := b) n z x
  have hnonneg := interactingReplicaKernelAbs_nonneg β I n z x
  by_cases hra : I.r r a
  ·
    have hnotA : x a - z a ∉ Critical2DKPZ.Polymer.endpoints 0 n := by
      have heq : x r - z r = x a - z a := by
        rw [hx.1 r a hra, hz.1 r a hra]
      rw [← heq]
      exact hnot
    have hR : Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) n
        (x a - z a) = 0 :=
      Critical2DKPZ.Blocks.spatialRenewal_eq_zero_of_not_mem_endpoints hnotA
    rw [hR, zero_mul] at hdom
    exact le_antisymm hdom hnonneg
  · have hmem : r ∈ (replicaBlockRepresentatives I).filter (fun c => ¬ I.r c a) :=
      Finset.mem_filter.mpr ⟨hr, hra⟩
    have hq : Critical2DKPZ.srwKernel n (x r - z r) = 0 := by
      have h := Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem n 0 (x r - z r) hnot
      simpa only [sub_zero] using h
    have hO : otherBlocksFreeKernel I a n z x = 0 := by
      unfold otherBlocksFreeKernel
      exact Finset.prod_eq_zero hmem hq
    rw [hO, mul_zero] at hdom
    exact le_antisymm hdom hnonneg

private theorem selected_replica_block_representation {h : ℕ}
    (I : ReplicaPartition h) (a : Fin h) {r : Fin h}
    (hr : r ∈ replicaBlockRepresentatives I) (hra : I.r r a) :
    r = canonicalReplicaBlockRepresentative I a := by
  calc
    r = canonicalReplicaBlockRepresentative I r :=
      (canonicalReplicaBlockRepresentative_eq_self I hr).symm
    _ = canonicalReplicaBlockRepresentative I a :=
      canonicalReplicaBlockRepresentative_eq_of_rel I hra

private theorem prod_replicaRenewal_otherBlocksFreeKernel {h : ℕ}
    (I : ReplicaPartition h) (a : Fin h) (σ2 : ℝ) (n : ℕ)
    (z x : LatticeConfiguration h)
    (hz : IsEqualityConfiguration I z) (hx : IsEqualityConfiguration I x) :
    (∏ r ∈ replicaBlockRepresentatives I,
      if I.r r a then Collision.spatialRenewal σ2 n (x r - z r)
      else Critical2DKPZ.srwKernel n (x r - z r)) =
      Collision.spatialRenewal σ2 n (x a - z a) * otherBlocksFreeKernel I a n z x := by
  classical
  let reps := replicaBlockRepresentatives I
  let r₀ := canonicalReplicaBlockRepresentative I a
  have hr₀ : r₀ ∈ reps := canonicalReplicaBlockRepresentative_mem I a
  have hrel₀ : I.r r₀ a := canonicalReplicaBlockRepresentative_rel I a
  have hselected : reps.filter (fun r => I.r r a) = {r₀} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hr, hrel⟩
      exact selected_replica_block_representation I a hr hrel
    · intro hr
      subst r
      exact ⟨hr₀, hrel₀⟩
  have hother :
      (∏ r ∈ reps, if I.r r a then 1 else
        Critical2DKPZ.srwKernel n (x r - z r)) =
        ∏ r ∈ reps.filter (fun r => ¬ I.r r a),
          Critical2DKPZ.srwKernel n (x r - z r) := by
    calc
      _ = ∏ r ∈ reps, if ¬ I.r r a then
            Critical2DKPZ.srwKernel n (x r - z r) else 1 := by
          apply Finset.prod_congr rfl
          intro r hr
          by_cases hrel : I.r r a <;> simp [hrel]
      _ = _ := by rw [← Finset.prod_filter]
  have hfactor :
      (∏ r ∈ reps,
        if I.r r a then Collision.spatialRenewal σ2 n (x r - z r)
        else Critical2DKPZ.srwKernel n (x r - z r)) =
        (∏ r ∈ reps.filter (fun r => I.r r a),
          Collision.spatialRenewal σ2 n (x r - z r)) *
        (∏ r ∈ reps.filter (fun r => ¬ I.r r a),
          Critical2DKPZ.srwKernel n (x r - z r)) := by
    calc
      _ = (∏ r ∈ reps, if I.r r a then
              Collision.spatialRenewal σ2 n (x r - z r) else 1) *
            (∏ r ∈ reps, if I.r r a then 1 else
              Critical2DKPZ.srwKernel n (x r - z r)) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro r hr
          by_cases hrel : I.r r a <;> simp [hrel]
      _ = _ := by
        rw [← Finset.prod_filter, hother]
  calc
    _ = (∏ r ∈ reps.filter (fun r => I.r r a),
          Collision.spatialRenewal σ2 n (x r - z r)) *
        (∏ r ∈ reps.filter (fun r => ¬ I.r r a),
          Critical2DKPZ.srwKernel n (x r - z r)) := hfactor
    _ = Collision.spatialRenewal σ2 n (x r₀ - z r₀) *
          otherBlocksFreeKernel I a n z x := by
      rw [hselected]
      simp [otherBlocksFreeKernel, reps]
    _ = Collision.spatialRenewal σ2 n (x a - z a) *
          otherBlocksFreeKernel I a n z x := by
      have hx' := hx r₀ a hrel₀
      have hz' := hz r₀ a hrel₀
      rw [hx', hz']

private theorem replicaDisplacement_sum_le_representatives {h : ℕ}
    (I : ReplicaPartition h) (z x : LatticeConfiguration h)
    (hz : IsEqualityConfiguration I z) (hx : IsEqualityConfiguration I x) :
    (∑ i : Fin h, ‖Critical2DKPZ.siteToPlane (x i - z i)‖) ≤
      (h : ℝ) * ∑ r ∈ replicaBlockRepresentatives I,
        ‖Critical2DKPZ.siteToPlane (x r - z r)‖ := by
  classical
  let reps := replicaBlockRepresentatives I
  let d : Fin h → ℝ := fun i =>
    ‖Critical2DKPZ.siteToPlane (x i - z i)‖
  let S : ℝ := ∑ r ∈ reps, d r
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun r hr => norm_nonneg _
  have hcoord (i : Fin h) : d i ≤ S := by
    let r := canonicalReplicaBlockRepresentative I i
    have hr : r ∈ reps := canonicalReplicaBlockRepresentative_mem I i
    have hrel : I.r r i := canonicalReplicaBlockRepresentative_rel I i
    have heq : d i = d r := by
      dsimp [d]
      rw [hx r i hrel, hz r i hrel]
    rw [heq]
    dsimp [S]
    have hnonneg : ∀ u ∈ reps, 0 ≤ d u := by
      intro u hu
      exact norm_nonneg (Critical2DKPZ.siteToPlane (x u - z u))
    exact Finset.single_le_sum hnonneg hr
  calc
    _ = ∑ i : Fin h, d i := by rfl
    _ ≤ ∑ _i : Fin h, S := Finset.sum_le_sum fun i hi => hcoord i
    _ = (h : ℝ) * S := by simp [S]

private theorem finiteProd_le_pow_mul_of_one {α : Type*} [Fintype α] [DecidableEq α]
    (e : α) {B M : ℝ} (hB : 1 ≤ B)
    (f : α → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfe : f e ≤ B * M) (hfrest : ∀ i, i ≠ e → f i ≤ B) :
    (∏ i : α, f i) ≤ B ^ Fintype.card α * M := by
  classical
  have hsplit :
      (∏ i : α, f i) =
        (∏ i ∈ (Finset.univ.erase e), f i) * f e := by
    symm
    exact Finset.prod_erase_mul Finset.univ f (Finset.mem_univ e)
  have hrest :
      (∏ i ∈ (Finset.univ.erase e), f i) ≤
        ∏ i ∈ (Finset.univ.erase e), B := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact hf i
    · intro i hi
      exact hfrest i (Finset.mem_erase.mp hi).1
  have hrest_nonneg : 0 ≤ ∏ i ∈ (Finset.univ.erase e), f i :=
    Finset.prod_nonneg fun i hi => hf i
  have hrestB_nonneg : 0 ≤ ∏ i ∈ (Finset.univ.erase e), B :=
    Finset.prod_nonneg fun i hi => le_trans (by norm_num) hB
  calc
    _ = (∏ i ∈ (Finset.univ.erase e), f i) * f e := hsplit
    _ ≤ (∏ i ∈ (Finset.univ.erase e), B) * (B * M) :=
      mul_le_mul hrest hfe (hf e) hrestB_nonneg
    _ = B ^ Fintype.card α * M := by
      have hprod : (∏ i ∈ (Finset.univ.erase e), B) =
          B ^ (Finset.univ.erase e).card := by simp
      rw [hprod]
      calc
        B ^ (Finset.univ.erase e).card * (B * M) =
            B ^ ((Finset.univ.erase e).card + 1) * M := by rw [pow_succ]; ring
        _ = B ^ Fintype.card α * M := by
          rw [Finset.card_erase_add_one (Finset.mem_univ e), Finset.card_univ]

private theorem endpointInteractionEnvelope_sum_le {h : ℕ} (hh : 2 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (I : ReplicaPartition h) (a : Fin h)
      (z : LatticeConfiguration h), IsEqualityConfiguration I z →
      ∀ σ2 t : ℝ, 0 ≤ σ2 → 0 ≤ t → ∀ n : ℕ,
      (∑ x ∈ (Fintype.piFinset
          (fun i : Fin h => Critical2DKPZ.Polymer.endpoints (z i) n)).filter
            (fun x => IsEqualityConfiguration I x),
        Real.exp (t * ∑ i : Fin h,
            ‖Critical2DKPZ.siteToPlane (x i - z i)‖) *
          Collision.spatialRenewal σ2 n (x a - z a) *
            otherBlocksFreeKernel I a n z x) ≤
        C * Real.exp (C * t ^ 2 * n) *
          ∑' v : Site, Collision.spatialRenewal σ2 n v := by
  classical
  obtain ⟨cR, hcR, hR⟩ := tsum_exp_mul_norm_spatialRenewal_le
  obtain ⟨cQ, hcQ, hQ⟩ := Critical2DKPZ.MomentBounds.tsum_exp_mul_norm_srwKernel_le
  let c : ℝ := max cR cQ
  have hc : 1 ≤ c := le_max_of_le_left hcR
  have hcR' : cR ≤ c := le_max_left cR cQ
  have hcQ' : cQ ≤ c := le_max_right cR cQ
  let C : ℝ := max 1 (max (c ^ h) (2 * c * (h : ℝ) ^ 3))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCp : c ^ h ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hCt : 2 * c * (h : ℝ) ^ 3 ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC1, ?_⟩
  intro I a z hz σ2 t hσ ht n
  let k : ℝ := (h : ℝ) * t
  have hk : 0 ≤ k := mul_nonneg (by positivity) ht
  let M : ℝ := ∑' v : Site, Collision.spatialRenewal σ2 n v
  have hM : 0 ≤ M := tsum_nonneg fun v =>
    Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ n v
  let B : ℝ := c * Real.exp (2 * c * k ^ 2 * n)
  have hB : 1 ≤ B := by
    dsimp [B]
    have harg : 0 ≤ 2 * c * k ^ 2 * n := by positivity
    have hexp : 1 ≤ Real.exp (2 * c * k ^ 2 * n) := by
      nlinarith [Real.add_one_le_exp (2 * c * k ^ 2 * n)]
    calc
      1 ≤ c := hc
      _ = c * 1 := by ring
      _ ≤ c * Real.exp (2 * c * k ^ 2 * n) :=
        mul_le_mul_of_nonneg_left hexp (le_trans (by norm_num) hc)
  let reps : Finset (Fin h) := replicaBlockRepresentatives I
  let E := {r : Fin h // r ∈ reps}
  let r₀ : E := ⟨canonicalReplicaBlockRepresentative I a,
    canonicalReplicaBlockRepresentative_mem I a⟩
  have hr₀ : I.r r₀.1 a := canonicalReplicaBlockRepresentative_rel I a
  have hselected (r : E) : I.r r.1 a ↔ r = r₀ := by
    constructor
    · intro hrel
      apply Subtype.ext
      exact selected_replica_block_representation I a r.2 hrel
    · intro hr
      subst r
      exact hr₀
  let F : E → Site → ℝ := fun r y =>
    Real.exp (k * ‖Critical2DKPZ.siteToPlane (y - z r.1)‖) *
      (if I.r r.1 a then Collision.spatialRenewal σ2 n (y - z r.1)
        else Critical2DKPZ.srwKernel n (y - z r.1))
  let A : E → ℝ := fun r =>
    ∑ y ∈ Critical2DKPZ.Polymer.endpoints (z r.1) n, F r y
  have hA_nonneg (r : E) : 0 ≤ A r := by
    dsimp [A, F]
    apply Finset.sum_nonneg
    intro y hy
    apply mul_nonneg (Real.exp_nonneg _)
    split_ifs
    · exact Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ n _
    · exact Critical2DKPZ.srwKernel_nonneg n _
  have hRle : cR * Real.exp (2 * cR * k ^ 2 * n) * M ≤ B * M := by
    apply mul_le_mul_of_nonneg_right _ hM
    apply mul_le_mul
    · exact hcR'
    · apply Real.exp_le_exp.mpr
      have hcoef : 2 * cR * k ^ 2 * n ≤ 2 * c * k ^ 2 * n := by
        calc
          2 * cR * k ^ 2 * n = (2 * cR) * (k ^ 2 * n) := by ring
          _ ≤ (2 * c) * (k ^ 2 * n) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcR' (by norm_num))
              (mul_nonneg (sq_nonneg k) (Nat.cast_nonneg n))
          _ = 2 * c * k ^ 2 * n := by ring
      exact hcoef
    · exact (Real.exp_nonneg _)
    · exact le_trans (by norm_num) hc
  have hQle : cQ * Real.exp (2 * cQ * k ^ 2 * n) ≤
      c * Real.exp (2 * c * k ^ 2 * n) := by
    apply mul_le_mul
    · exact hcQ'
    · apply Real.exp_le_exp.mpr
      have hcoef : 2 * cQ * k ^ 2 * n ≤ 2 * c * k ^ 2 * n := by
        calc
          2 * cQ * k ^ 2 * n = (2 * cQ) * (k ^ 2 * n) := by ring
          _ ≤ (2 * c) * (k ^ 2 * n) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcQ' (by norm_num))
              (mul_nonneg (sq_nonneg k) (Nat.cast_nonneg n))
          _ = 2 * c * k ^ 2 * n := by ring
      exact hcoef
    · exact Real.exp_nonneg _
    · exact le_trans (by norm_num) hc
  have hA_bound (r : E) :
      A r ≤ if I.r r.1 a then B * M else B := by
    by_cases hrel : I.r r.1 a
    · have hbound : A r ≤ B * M := by
        dsimp [A, F]
        simp_rw [ite_eq_left hrel]
        rw [sum_endpoints_weighted_spatialRenewal_eq_tsum σ2 k n (z r.1)]
        calc
          _ ≤ cR * Real.exp (2 * cR * k ^ 2 * n) * M := hR σ2 hσ k hk n
          _ ≤ B * M := hRle
      simpa [hrel] using hbound
    · have hbound : A r ≤ B := by
        dsimp [A, F]
        simp_rw [ite_eq_right hrel]
        rw [sum_endpoints_weighted_srwKernel_eq_tsum k n (z r.1)]
        calc
          _ ≤ cQ * Real.exp (2 * cQ * k ^ 2 * n) := (hQ k hk n).1
          _ ≤ B := by dsimp [B]; exact hQle
      simpa [hrel] using hbound
  let T : Fin h → Finset Site := fun i => Critical2DKPZ.Polymer.endpoints (z i) n
  have hsumFact := sum_equalityConfigurations_prod_blocks I z hz n F
  have hcard : Fintype.card E ≤ h := by
    have hinj := Fintype.card_le_of_injective (fun r : E => r.1)
      (fun r s hrs => Subtype.ext hrs)
    simpa [E] using hinj
  have hprodA : (∏ r : E, A r) ≤ B ^ Fintype.card E * M := by
    apply finiteProd_le_pow_mul_of_one r₀ hB A hA_nonneg
    · simpa [hr₀] using hA_bound r₀
    · intro r hr
      have hnot : ¬ I.r r.1 a := by
        intro hrel
        exact hr ((hselected r).mp hrel)
      simpa [hnot] using hA_bound r
  have hprodA' : (∏ r : E, A r) ≤ B ^ h * M := by
    calc
      _ ≤ B ^ Fintype.card E * M := hprodA
      _ ≤ B ^ h * M := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hB hcard) hM
  have hBpow : B ^ h = c ^ h * Real.exp (2 * c * (h : ℝ) ^ 3 * t ^ 2 * n) := by
    dsimp [B, k]
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 1
    ring_nf
  have hfinal : B ^ h * M ≤ C * Real.exp (C * t ^ 2 * n) * M := by
    rw [hBpow]
    apply mul_le_mul_of_nonneg_right _ hM
    apply mul_le_mul
    · exact hCp
    · apply Real.exp_le_exp.mpr
      have hcoef :
          2 * c * (h : ℝ) ^ 3 * t ^ 2 * n ≤ C * t ^ 2 * n := by
        calc
          2 * c * (h : ℝ) ^ 3 * t ^ 2 * n =
              (2 * c * (h : ℝ) ^ 3) * (t ^ 2 * n) := by ring
          _ ≤ C * (t ^ 2 * n) :=
            mul_le_mul_of_nonneg_right hCt
              (mul_nonneg (sq_nonneg t) (Nat.cast_nonneg n))
          _ = C * t ^ 2 * n := by ring
      exact hcoef
    · exact Real.exp_nonneg _
    · exact le_trans (by norm_num) hC1
  calc
    _ ≤ ∑ x ∈ (Fintype.piFinset T).filter (fun x => IsEqualityConfiguration I x),
        ∏ r : E, F r (x r.1) := by
      apply Finset.sum_le_sum
      intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      let R := Collision.spatialRenewal σ2 n (x a - z a)
      let O := otherBlocksFreeKernel I a n z x
      have hkernel := prod_replicaRenewal_otherBlocksFreeKernel I a σ2 n z x hz hx'
      have hdisp := replicaDisplacement_sum_le_representatives I z x hz hx'
      let S : ℝ := ∑ r ∈ reps, ‖Critical2DKPZ.siteToPlane (x r - z r)‖
      have harg : t * (∑ i : Fin h,
          ‖Critical2DKPZ.siteToPlane (x i - z i)‖) ≤ k * S := by
        calc
          _ ≤ t * ((h : ℝ) * S) := by
            apply mul_le_mul_of_nonneg_left hdisp ht
          _ = k * S := by dsimp [k, S]; ring
      have hexp := Real.exp_le_exp.mpr harg
      have hRnonneg : 0 ≤ R := by
        dsimp [R]
        exact Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ n _
      have hOnonneg : 0 ≤ O := otherBlocksFreeKernel_nonneg I a n z x
      have hprodExp :
          (∏ r : E, Real.exp (k *
            ‖Critical2DKPZ.siteToPlane (x r.1 - z r.1)‖)) = Real.exp (k * S) := by
        calc
          _ = Real.exp (∑ r : E, k *
              ‖Critical2DKPZ.siteToPlane (x r.1 - z r.1)‖) := by
                rw [← Real.exp_sum]
          _ = Real.exp (k * S) := by
                congr 1
                rw [Finset.mul_sum]
                exact Finset.sum_coe_sort reps (fun r =>
                  k * ‖Critical2DKPZ.siteToPlane (x r - z r)‖)
      calc
        _ = Real.exp (t * (∑ i : Fin h,
              ‖Critical2DKPZ.siteToPlane (x i - z i)‖)) * (R * O) := by
          dsimp [R, O]
          ring
        _ ≤ Real.exp (k * S) * (R * O) :=
          mul_le_mul_of_nonneg_right hexp (mul_nonneg hRnonneg hOnonneg)
        _ = (∏ r : E, Real.exp (k *
              ‖Critical2DKPZ.siteToPlane (x r.1 - z r.1)‖)) *
            (∏ r : E, if I.r r.1 a then
              Collision.spatialRenewal σ2 n (x r.1 - z r.1)
              else Critical2DKPZ.srwKernel n (x r.1 - z r.1)) := by
          have hkernelSubtype :
              (∏ r : E, if I.r r.1 a then
                Collision.spatialRenewal σ2 n (x r.1 - z r.1)
                else Critical2DKPZ.srwKernel n (x r.1 - z r.1)) = R * O := by
            calc
              _ = ∏ r ∈ reps, if I.r r a then
                    Collision.spatialRenewal σ2 n (x r - z r)
                    else Critical2DKPZ.srwKernel n (x r - z r) :=
                Finset.prod_coe_sort reps (fun r => if I.r r a then
                  Collision.spatialRenewal σ2 n (x r - z r)
                  else Critical2DKPZ.srwKernel n (x r - z r))
              _ = R * O := by simpa [R, O] using hkernel
          rw [hprodExp, hkernelSubtype]
        _ = ∏ r : E, F r (x r.1) := by
          change (∏ r : E, Real.exp (k *
              ‖Critical2DKPZ.siteToPlane (x r.1 - z r.1)‖)) *
            (∏ r : E, if I.r r.1 a then
              Collision.spatialRenewal σ2 n (x r.1 - z r.1)
              else Critical2DKPZ.srwKernel n (x r.1 - z r.1)) =
            ∏ r : E, Real.exp (k *
              ‖Critical2DKPZ.siteToPlane (x r.1 - z r.1)‖) *
              (if I.r r.1 a then Collision.spatialRenewal σ2 n (x r.1 - z r.1)
                else Critical2DKPZ.srwKernel n (x r.1 - z r.1))
          symm
          exact Finset.prod_mul_distrib
    _ = ∏ r : E, A r := by
      simpa [A, T, E, Finset.prod_coe_sort] using hsumFact
    _ ≤ B ^ h * M := hprodA'
    _ ≤ C * Real.exp (C * t ^ 2 * n) * M := hfinal

private theorem weighted_interaction_row_sum_le {h : ℕ} (hh : 2 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (β : ℝ) (I : ReplicaPartition h), I ≠ ⊥ →
      |replicaPartitionDisorderMoment β I| ≤ Critical2DKPZ.Polymer.sigmaSq β →
      ∀ t : ℝ, 0 ≤ t → ∀ (z : LatticeConfiguration h),
      IsEqualityConfiguration I z → ∀ n : ℕ,
      ∀ s : Finset (LatticeConfiguration h),
        (∑ x ∈ s, weightedKernel (replicaExponentialWeight t)
          (fun z x => interactingReplicaKernelAbs β I n z x) z x) ≤
        C * Real.exp (C * t ^ 2 * n) *
          ∑' v : Site, Collision.spatialRenewal
            (Critical2DKPZ.Polymer.sigmaSq β) n v := by
  classical
  obtain ⟨C, hC, hEnv⟩ := endpointInteractionEnvelope_sum_le hh
  refine ⟨C, hC, ?_⟩
  intro β I hI hmom t ht z hz n s
  obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete I hI
  let a := α.val.1
  let b := α.val.2
  have hab : a ≠ b := ne_of_lt α.property
  have hσ : 0 ≤ Critical2DKPZ.Polymer.sigmaSq β := sigmaSq_nonneg β
  let T : Fin h → Finset Site := fun i =>
    Critical2DKPZ.Polymer.endpoints (z i) n
  let E : Finset (LatticeConfiguration h) :=
    (Fintype.piFinset T).filter (fun x => IsEqualityConfiguration I x)
  let K : LatticeConfiguration h → ℝ := fun x =>
    weightedKernel (replicaExponentialWeight t)
      (fun z x => interactingReplicaKernelAbs β I n z x) z x
  have hKnonneg (x : LatticeConfiguration h) : 0 ≤ K x := by
    dsimp [K, weightedKernel]
    exact div_nonneg
      (mul_nonneg (replicaExponentialWeight_pos t z).le
        (interactingReplicaKernelAbs_nonneg β I n z x))
      (replicaExponentialWeight_pos t x).le
  have hzero (x : LatticeConfiguration h) (hx : x ∉ E) : K x = 0 := by
    by_cases hxC : IsCollisionConfiguration I x
    · have hxnotPi : x ∉ Fintype.piFinset T := by
        intro hpi
        exact hx (Finset.mem_filter.mpr ⟨hpi, hxC.1⟩)
      have hnotall : ¬ ∀ i : Fin h, x i ∈ T i := by
        simpa only [Fintype.mem_piFinset] using hxnotPi
      push Not at hnotall
      obtain ⟨i, hi⟩ := hnotall
      by_cases hzC : IsCollisionConfiguration I z
      · have hU := interactingReplicaKernelAbs_zero_of_endpoint_miss I hI β hmom
          n z x hzC hxC ⟨i, hi⟩
        simp [K, weightedKernel, hU]
      · have hU := interactingReplicaKernelAbs_zero_of_not_collision_left β I n z x hzC
        simp [K, weightedKernel, hU]
    · have hU := interactingReplicaKernelAbs_zero_of_not_collision_right β I n z x hxC
      simp [K, weightedKernel, hU]
  have hsumSupport : (∑ x ∈ s, K x) = ∑ x ∈ s ∩ E, K x := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro x hx hxE
    have hx' : x ∉ E := fun he => hxE (Finset.mem_inter.mpr ⟨hx, he⟩)
    rw [hzero x hx']
  have hsumSubset : (∑ x ∈ s ∩ E, K x) ≤ ∑ x ∈ E, K x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
      (fun x hx _ => hKnonneg x)
  have hpoint (x : LatticeConfiguration h) (hx : x ∈ E) :
      K x ≤ Real.exp (t * ∑ i : Fin h,
        ‖Critical2DKPZ.siteToPlane (x i - z i)‖) *
          Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
            n (x a - z a) * otherBlocksFreeKernel I a n z x := by
    have hratio := replica_exponentialWeight_ratio_le ht z x
    have hU := interactingReplicaKernelAbs_le_spatialRenewal β I hmom hab hα n z x
    have hUnonneg := interactingReplicaKernelAbs_nonneg β I n z x
    calc
      K x = (replicaExponentialWeight t z / replicaExponentialWeight t x) *
          interactingReplicaKernelAbs β I n z x := by
            dsimp [K, weightedKernel]
            field_simp [ne_of_gt (replicaExponentialWeight_pos t x)]
      _ ≤ Real.exp (t * ∑ i : Fin h,
            ‖Critical2DKPZ.siteToPlane (x i - z i)‖) *
            interactingReplicaKernelAbs β I n z x :=
        mul_le_mul_of_nonneg_right hratio hUnonneg
      _ ≤ Real.exp (t * ∑ i : Fin h,
            ‖Critical2DKPZ.siteToPlane (x i - z i)‖) *
            (Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
              n (x a - z a) * otherBlocksFreeKernel I a n z x) :=
        mul_le_mul_of_nonneg_left hU (Real.exp_nonneg _)
      _ = Real.exp (t * ∑ i : Fin h,
            ‖Critical2DKPZ.siteToPlane (x i - z i)‖) *
            Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
              n (x a - z a) * otherBlocksFreeKernel I a n z x := by ring
  calc
    _ = ∑ x ∈ s, K x := by rfl
    _ = ∑ x ∈ s ∩ E, K x := hsumSupport
    _ ≤ ∑ x ∈ E, K x := hsumSubset
    _ ≤ ∑ x ∈ E,
          Real.exp (t * ∑ i : Fin h,
            ‖Critical2DKPZ.siteToPlane (x i - z i)‖) *
            Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
              n (x a - z a) * otherBlocksFreeKernel I a n z x := by
        apply Finset.sum_le_sum
        intro x hx
        exact hpoint x hx
    _ ≤ C * Real.exp (C * t ^ 2 * n) *
          ∑' v : Site, Collision.spatialRenewal
            (Critical2DKPZ.Polymer.sigmaSq β) n v := by
        exact hEnv I a z hz (Critical2DKPZ.Polymer.sigmaSq β) t hσ ht n

private theorem weighted_interaction_column_sum_le {h : ℕ} (hh : 2 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (β : ℝ) (I : ReplicaPartition h), I ≠ ⊥ →
      |replicaPartitionDisorderMoment β I| ≤ Critical2DKPZ.Polymer.sigmaSq β →
      ∀ t : ℝ, 0 ≤ t → ∀ (x : LatticeConfiguration h),
      IsEqualityConfiguration I x → ∀ n : ℕ,
      ∀ s : Finset (LatticeConfiguration h),
        (∑ z ∈ s, weightedKernel (replicaExponentialWeight t)
          (fun z x => interactingReplicaKernelAbs β I n z x) z x) ≤
        C * Real.exp (C * t ^ 2 * n) *
          ∑' v : Site, Collision.spatialRenewal
            (Critical2DKPZ.Polymer.sigmaSq β) n v := by
  classical
  obtain ⟨C, hC, hEnv⟩ := endpointInteractionEnvelope_sum_le hh
  refine ⟨C, hC, ?_⟩
  intro β I hI hmom t ht x hx n s
  obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete I hI
  let a := α.val.1
  let b := α.val.2
  have hab : a ≠ b := ne_of_lt α.property
  have hσ : 0 ≤ Critical2DKPZ.Polymer.sigmaSq β := sigmaSq_nonneg β
  let T : Fin h → Finset Site := fun i =>
    Critical2DKPZ.Polymer.endpoints (x i) n
  let E : Finset (LatticeConfiguration h) :=
    (Fintype.piFinset T).filter (fun z => IsEqualityConfiguration I z)
  let K : LatticeConfiguration h → ℝ := fun z =>
    weightedKernel (replicaExponentialWeight t)
      (fun z x => interactingReplicaKernelAbs β I n z x) z x
  have hKnonneg (z : LatticeConfiguration h) : 0 ≤ K z := by
    dsimp [K, weightedKernel]
    exact div_nonneg
      (mul_nonneg (replicaExponentialWeight_pos t z).le
        (interactingReplicaKernelAbs_nonneg β I n z x))
      (replicaExponentialWeight_pos t x).le
  have hzero (z : LatticeConfiguration h) (hz : z ∉ E) : K z = 0 := by
    by_cases hxC : IsCollisionConfiguration I x
    · by_cases hzC : IsCollisionConfiguration I z
      · have hznotPi : z ∉ Fintype.piFinset T := by
          intro hpi
          exact hz (Finset.mem_filter.mpr ⟨hpi, hzC.1⟩)
        have hnotall : ¬ ∀ i : Fin h, z i ∈ T i := by
          simpa only [Fintype.mem_piFinset] using hznotPi
        push Not at hnotall
        obtain ⟨i, hi⟩ := hnotall
        have hmiss : ∃ i : Fin h, x i ∉ Critical2DKPZ.Polymer.endpoints (z i) n :=
          ⟨i, by
            intro hreach
            exact hi ((mem_endpoints_reverse n (x i) (z i)).mp hreach)⟩
        have hU := interactingReplicaKernelAbs_zero_of_endpoint_miss I hI β hmom
          n z x hzC hxC hmiss
        simp [K, weightedKernel, hU]
      · have hU := interactingReplicaKernelAbs_zero_of_not_collision_left β I n z x hzC
        simp [K, weightedKernel, hU]
    · have hU := interactingReplicaKernelAbs_zero_of_not_collision_right β I n z x hxC
      simp [K, weightedKernel, hU]
  have hsumSupport : (∑ z ∈ s, K z) = ∑ z ∈ s ∩ E, K z := by
    symm
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro z hzS hzE
    have hz' : z ∉ E := fun he => hzE (Finset.mem_inter.mpr ⟨hzS, he⟩)
    rw [hzero z hz']
  have hsumSubset : (∑ z ∈ s ∩ E, K z) ≤ ∑ z ∈ E, K z :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.inter_subset_right)
      (fun z hz _ => hKnonneg z)
  have hpoint (z : LatticeConfiguration h) (hz : z ∈ E) :
      K z ≤ Real.exp (t * ∑ i : Fin h,
        ‖Critical2DKPZ.siteToPlane (z i - x i)‖) *
          (Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
            n (z a - x a) * otherBlocksFreeKernel I a n x z) := by
    have hratio := replica_exponentialWeight_ratio_le ht z x
    have hnorm : ∑ i : Fin h, ‖Critical2DKPZ.siteToPlane (x i - z i)‖ =
        ∑ i : Fin h, ‖Critical2DKPZ.siteToPlane (z i - x i)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show x i - z i = -(z i - x i) by abel,
        siteToPlane_neg, norm_neg]
    have hratio' : replicaExponentialWeight t z / replicaExponentialWeight t x ≤
        Real.exp (t * ∑ i : Fin h,
          ‖Critical2DKPZ.siteToPlane (z i - x i)‖) := by
      rw [← hnorm]
      exact hratio
    have hU := interactingReplicaKernelAbs_le_spatialRenewal β I hmom hab hα n z x
    have hR : Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
        n (x a - z a) = Collision.spatialRenewal
          (Critical2DKPZ.Polymer.sigmaSq β) n (z a - x a) := by
      rw [show x a - z a = -(z a - x a) by abel,
        spatialRenewal_neg]
    have hO : otherBlocksFreeKernel I a n z x = otherBlocksFreeKernel I a n x z := by
      unfold otherBlocksFreeKernel
      apply Finset.prod_congr rfl
      intro r hr
      rw [Critical2DKPZ.Polymer.srwKernel_sub_swap]
    rw [hR, hO] at hU
    have hUnonneg := interactingReplicaKernelAbs_nonneg β I n z x
    calc
      K z = (replicaExponentialWeight t z / replicaExponentialWeight t x) *
          interactingReplicaKernelAbs β I n z x := by
            dsimp [K, weightedKernel]
            field_simp [ne_of_gt (replicaExponentialWeight_pos t x)]
      _ ≤ Real.exp (t * ∑ i : Fin h,
            ‖Critical2DKPZ.siteToPlane (z i - x i)‖) *
            interactingReplicaKernelAbs β I n z x :=
        mul_le_mul_of_nonneg_right hratio' hUnonneg
      _ ≤ Real.exp (t * ∑ i : Fin h,
            ‖Critical2DKPZ.siteToPlane (z i - x i)‖) *
            (Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
              n (z a - x a) * otherBlocksFreeKernel I a n x z) :=
        mul_le_mul_of_nonneg_left hU (Real.exp_nonneg _)
  calc
    _ = ∑ z ∈ s, K z := by rfl
    _ = ∑ z ∈ s ∩ E, K z := hsumSupport
    _ ≤ ∑ z ∈ E, K z := hsumSubset
    _ ≤ ∑ z ∈ E,
          Real.exp (t * ∑ i : Fin h,
            ‖Critical2DKPZ.siteToPlane (z i - x i)‖) *
            Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β)
              n (z a - x a) * otherBlocksFreeKernel I a n x z := by
        apply Finset.sum_le_sum
        intro z hz
        simpa [mul_assoc] using hpoint z hz
    _ ≤ C * Real.exp (C * t ^ 2 * n) *
          ∑' v : Site, Collision.spatialRenewal
            (Critical2DKPZ.Polymer.sigmaSq β) n v := by
        exact hEnv I a x hx (Critical2DKPZ.Polymer.sigmaSq β) t hσ ht n

private theorem weighted_hattedInteraction_split {h : ℕ} (L : ℕ) (lam β t : ℝ)
    (I : ReplicaPartition h) (z x : LatticeConfiguration h) :
    weightedKernel (replicaExponentialWeight t)
        (hattedInteractingReplicaKernelAbs L lam β I) z x =
      weightedKernel (replicaExponentialWeight t)
          (fun z x => if z = x ∧ IsCollisionConfiguration I x then 1 else 0) z x +
        ∑ m ∈ Finset.range L,
          Real.exp (-lam * (m + 1 : ℕ)) *
            weightedKernel (replicaExponentialWeight t)
              (fun z x => interactingReplicaKernelAbs β I (m + 1) z x) z x := by
  classical
  unfold weightedKernel hattedInteractingReplicaKernelAbs
  rw [mul_add, Finset.mul_sum, add_div, Finset.sum_div]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro m hm
  ring

private theorem weighted_interaction_diagonal_sum_le {h : ℕ}
    (t : ℝ) (I : ReplicaPartition h) (z : LatticeConfiguration h)
    (s : Finset (LatticeConfiguration h)) :
    (∑ x ∈ s, weightedKernel (replicaExponentialWeight t)
      (fun z x => if z = x ∧ IsCollisionConfiguration I x then 1 else 0) z x) ≤ 1 := by
  classical
  have hterm (x : LatticeConfiguration h) :
      weightedKernel (replicaExponentialWeight t)
        (fun z x => if z = x ∧ IsCollisionConfiguration I x then 1 else 0) z x ≤
        if z = x then 1 else 0 := by
    by_cases hzx : z = x
    · subst x
      by_cases hc : IsCollisionConfiguration I z
      · simp [weightedKernel, hc, ne_of_gt (replicaExponentialWeight_pos t z)]
      · simp [weightedKernel, hc]
    · simp [weightedKernel, hzx]
  calc
    (∑ x ∈ s, weightedKernel (replicaExponentialWeight t)
      (fun z x => if z = x ∧ IsCollisionConfiguration I x then 1 else 0) z x) ≤
        ∑ x ∈ s, if z = x then 1 else 0 := by
      exact Finset.sum_le_sum (fun x hx => hterm x)
    _ = if z ∈ s then 1 else 0 := by simp
    _ ≤ 1 := by split_ifs <;> norm_num

private theorem weighted_interaction_diagonal_column_sum_le {h : ℕ}
    (t : ℝ) (I : ReplicaPartition h) (z : LatticeConfiguration h)
    (s : Finset (LatticeConfiguration h)) :
    (∑ x ∈ s, weightedKernel (replicaExponentialWeight t)
      (fun z x => if z = x ∧ IsCollisionConfiguration I x then 1 else 0) x z) ≤ 1 := by
  classical
  have hterm (x : LatticeConfiguration h) :
      weightedKernel (replicaExponentialWeight t)
        (fun z x => if z = x ∧ IsCollisionConfiguration I x then 1 else 0) x z ≤
        if x = z then 1 else 0 := by
    by_cases hxz : x = z
    · subst x
      by_cases hc : IsCollisionConfiguration I z
      · simp [weightedKernel, hc, ne_of_gt (replicaExponentialWeight_pos t z)]
      · simp [weightedKernel, hc]
    · simp [weightedKernel, hxz]
  calc
    (∑ x ∈ s, weightedKernel (replicaExponentialWeight t)
      (fun z x => if z = x ∧ IsCollisionConfiguration I x then 1 else 0) x z) ≤
        ∑ x ∈ s, if x = z then 1 else 0 := by
      exact Finset.sum_le_sum (fun x hx => hterm x)
    _ = if z ∈ s then 1 else 0 := by simp
    _ ≤ 1 := by split_ifs <;> norm_num

/-- CCR25 Proposition 4.24: the weighted finite-volume interacting kernel is
bounded on every counting `ℓ^q`, uniformly in the volume and in `q>1`. -/
theorem finiteLpNorm_weighted_hattedInteractingReplicaKernelAbs_le
    (h : ℕ) (hh : 2 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ L : ℕ, ∀ lam β : ℝ, 0 ≤ lam →
      (∀ I : ReplicaPartition h, I ≠ ⊥ →
        |replicaPartitionDisorderMoment β I| ≤ Critical2DKPZ.Polymer.sigmaSq β) →
      Critical2DKPZ.Polymer.sigmaSq β * dampedOverlap lam L < 1 →
      ∀ q : ℝ, 1 < q → ∀ (s : Finset (LatticeConfiguration h))
        (I : ReplicaPartition h), I ≠ ⊥ → ∀ f : LatticeConfiguration h → ℝ,
          finiteLpNorm s q (finiteKernelApply s
            (weightedKernel (replicaExponentialWeight t)
              (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤
            (1 + C * Real.exp (C * t ^ 2 * L) *
              (Critical2DKPZ.Polymer.sigmaSq β * dampedOverlap lam L /
                (1 - Critical2DKPZ.Polymer.sigmaSq β * dampedOverlap lam L))) *
              finiteLpNorm s q f := by
  classical
  obtain ⟨Cr, hCr, hrowBound⟩ := weighted_interaction_row_sum_le hh
  obtain ⟨Cc, hCc, hcolBound⟩ := weighted_interaction_column_sum_le hh
  let C : ℝ := max Cr Cc
  have hC : 1 ≤ C := le_trans hCr (le_max_left Cr Cc)
  have hCrC : Cr ≤ C := le_max_left Cr Cc
  have hCcC : Cc ≤ C := le_max_right Cr Cc
  refine ⟨C, hC, ?_⟩
  intro t ht L lam β hlam hMom hsmall q hq s I hI f
  have hσ : 0 ≤ Critical2DKPZ.Polymer.sigmaSq β := sigmaSq_nonneg β
  have hOverlapNonneg : 0 ≤ dampedOverlap lam L := by
    unfold dampedOverlap
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (Real.exp_nonneg _)
      (Critical2DKPZ.srwKernel_nonneg (2 * n) 0)
  have hden : 0 < 1 - Critical2DKPZ.Polymer.sigmaSq β * dampedOverlap lam L :=
    sub_pos.mpr hsmall
  let ρ : ℝ := Critical2DKPZ.Polymer.sigmaSq β * dampedOverlap lam L /
    (1 - Critical2DKPZ.Polymer.sigmaSq β * dampedOverlap lam L)
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact div_nonneg (mul_nonneg hσ hOverlapNonneg) hden.le
  let B : ℝ := C * Real.exp (C * t ^ 2 * L)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let K : LatticeConfiguration h → LatticeConfiguration h → ℝ :=
    weightedKernel (replicaExponentialWeight t)
      (hattedInteractingReplicaKernelAbs L lam β I)
  have hKnonneg (x y : LatticeConfiguration h) : 0 ≤ K x y := by
    dsimp [K, weightedKernel]
    exact div_nonneg
      (mul_nonneg (replicaExponentialWeight_pos t x).le
        (hattedInteractingReplicaKernelAbs_nonneg L lam β I x y))
      (replicaExponentialWeight_pos t y).le
  have hrow (x : LatticeConfiguration h) (hx : x ∈ s) :
      ∑ y ∈ s, K x y ≤ 1 + B * ρ := by
    by_cases hxEq : IsEqualityConfiguration I x
    · let V (y : LatticeConfiguration h) :=
        weightedKernel (replicaExponentialWeight t)
          (fun x y => if x = y ∧ IsCollisionConfiguration I y then 1 else 0) x y
      let U (m : ℕ) (y : LatticeConfiguration h) :=
        weightedKernel (replicaExponentialWeight t)
          (fun x y => interactingReplicaKernelAbs β I (m + 1) x y) x y
      have hsumInner : ∀ m ∈ Finset.range L,
          (∑ y ∈ s, Real.exp (-lam * (m + 1 : ℕ)) * U m y) =
            Real.exp (-lam * (m + 1 : ℕ)) * ∑ y ∈ s, U m y := by
        intro m hm
        rw [Finset.mul_sum]
      have hsumMixed :
          (∑ y ∈ s, ∑ m ∈ Finset.range L,
            Real.exp (-lam * (m + 1 : ℕ)) * U m y) =
          ∑ m ∈ Finset.range L,
            Real.exp (-lam * (m + 1 : ℕ)) * ∑ y ∈ s, U m y := by
        calc
          _ = ∑ m ∈ Finset.range L, ∑ y ∈ s,
                Real.exp (-lam * (m + 1 : ℕ)) * U m y := Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hsumInner m hm
      have hdecomp : (∑ y ∈ s, K x y) =
          (∑ y ∈ s, V y) +
            ∑ m ∈ Finset.range L,
              Real.exp (-lam * (m + 1 : ℕ)) * ∑ y ∈ s, U m y := by
        calc
          _ = ∑ y ∈ s, (V y + ∑ m ∈ Finset.range L,
                Real.exp (-lam * (m + 1 : ℕ)) * U m y) := by
              apply Finset.sum_congr rfl
              intro y hy
              simpa [K, V, U] using
                weighted_hattedInteraction_split L lam β t I x y
          _ = (∑ y ∈ s, V y) +
                ∑ m ∈ Finset.range L,
                  Real.exp (-lam * (m + 1 : ℕ)) * ∑ y ∈ s, U m y := by
              rw [Finset.sum_add_distrib, hsumMixed]
      have hdiag := weighted_interaction_diagonal_sum_le t I x s
      have hseries :
          (∑ m ∈ Finset.range L,
            Real.exp (-lam * (m + 1 : ℕ)) * ∑ y ∈ s, U m y) ≤ B * ρ := by
        have hmass (m : ℕ) :
            0 ≤ ∑' v : Site,
              Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v :=
          tsum_nonneg fun v => Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ (m + 1) v
        have hrate (m : ℕ) (hm : m ∈ Finset.range L) :
            Cr * Real.exp (Cr * t ^ 2 * (m + 1 : ℕ)) ≤
              C * Real.exp (C * t ^ 2 * L) := by
          have hmL : ((m + 1 : ℕ) : ℝ) ≤ L := by
            exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hm))
          have harg : Cr * t ^ 2 * (m + 1 : ℕ) ≤ C * t ^ 2 * L := by
            calc
              Cr * t ^ 2 * (m + 1 : ℕ) = Cr * (t ^ 2 * (m + 1 : ℕ)) := by ring
              _ ≤ C * (t ^ 2 * (m + 1 : ℕ)) :=
                mul_le_mul_of_nonneg_right hCrC (by positivity)
              _ ≤ C * (t ^ 2 * L) := by
                have htime : t ^ 2 * (m + 1 : ℕ) ≤ t ^ 2 * L :=
                  mul_le_mul_of_nonneg_left hmL (sq_nonneg t)
                exact mul_le_mul_of_nonneg_left htime (by positivity)
              _ = C * t ^ 2 * L := by ring
          apply mul_le_mul hCrC (Real.exp_le_exp.mpr harg)
          · exact Real.exp_nonneg _
          · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hC
        have hterm (m : ℕ) (hm : m ∈ Finset.range L) :
            Real.exp (-lam * (m + 1 : ℕ)) * ∑ y ∈ s, U m y ≤
              B * (Real.exp (-lam * (m + 1 : ℕ)) *
                ∑' v : Site,
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v) := by
          have hu := hrowBound β I hI (hMom I hI) t ht x hxEq (m + 1) s
          have hu' : (∑ y ∈ s, U m y) ≤
              Cr * Real.exp (Cr * t ^ 2 * (m + 1 : ℕ)) *
                ∑' v : Site,
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v := by
            simpa [U] using hu
          have hu'' : (∑ y ∈ s, U m y) ≤ B *
              ∑' v : Site,
                Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v :=
            hu'.trans (mul_le_mul_of_nonneg_right (hrate m hm) (hmass m))
          calc
            _ ≤ Real.exp (-lam * (m + 1 : ℕ)) *
                (B * ∑' v : Site,
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v) :=
              mul_le_mul_of_nonneg_left hu'' (Real.exp_nonneg _)
            _ = _ := by ring
        calc
          _ ≤ ∑ m ∈ Finset.range L,
              B * (Real.exp (-lam * (m + 1 : ℕ)) *
                ∑' v : Site,
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v) :=
            Finset.sum_le_sum fun m hm => hterm m hm
          _ = B * ∑ m ∈ Finset.range L,
                Real.exp (-lam * (m + 1 : ℕ)) *
                  ∑' v : Site,
                    Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v := by
              rw [Finset.mul_sum]
          _ ≤ B * ρ := by
            dsimp [B, ρ]
            exact mul_le_mul_of_nonneg_left
              (sum_exp_mul_tsum_spatialRenewal_le hσ hlam L hsmall) hB
      exact hdecomp ▸ add_le_add hdiag hseries
    · have hxNotColl : ¬IsCollisionConfiguration I x := fun hc => hxEq hc.1
      have hUzero (m : ℕ) (y : LatticeConfiguration h) :
          interactingReplicaKernelAbs β I (m + 1) x y = 0 := by
        exact interactingReplicaKernelAbs_zero_of_not_collision_left β I (m + 1) x y hxNotColl
      have hdiagzero (y : LatticeConfiguration h) :
          weightedKernel (replicaExponentialWeight t)
            (fun x y => if x = y ∧ IsCollisionConfiguration I y then 1 else 0) x y = 0 := by
        by_cases hxy : x = y
        · subst y
          simp [weightedKernel, hxNotColl]
        · simp [weightedKernel, hxy]
      have hKzero (y : LatticeConfiguration h) : K x y = 0 := by
        rw [show K x y =
          weightedKernel (replicaExponentialWeight t)
            (hattedInteractingReplicaKernelAbs L lam β I) x y by rfl,
          weighted_hattedInteraction_split L lam β t I x y]
        have hsumzero :
            (∑ m ∈ Finset.range L,
              Real.exp (-lam * (m + 1 : ℕ)) *
                weightedKernel (replicaExponentialWeight t)
                  (fun x y => interactingReplicaKernelAbs β I (m + 1) x y) x y) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          have hterm : weightedKernel (replicaExponentialWeight t)
              (fun x y => interactingReplicaKernelAbs β I (m + 1) x y) x y = 0 := by
            simp [weightedKernel, hUzero m y]
          simp [hterm]
        rw [hdiagzero, hsumzero]
        simp
      simpa [hKzero] using (show 0 ≤ 1 + B * ρ from by positivity)
  have hcol (y : LatticeConfiguration h) (hy : y ∈ s) :
      ∑ x ∈ s, K x y ≤ 1 + B * ρ := by
    by_cases hyEq : IsEqualityConfiguration I y
    · let V (x : LatticeConfiguration h) :=
        weightedKernel (replicaExponentialWeight t)
          (fun x y => if x = y ∧ IsCollisionConfiguration I y then 1 else 0) x y
      let U (m : ℕ) (x : LatticeConfiguration h) :=
        weightedKernel (replicaExponentialWeight t)
          (fun x y => interactingReplicaKernelAbs β I (m + 1) x y) x y
      have hsumInner : ∀ m ∈ Finset.range L,
          (∑ x ∈ s, Real.exp (-lam * (m + 1 : ℕ)) * U m x) =
            Real.exp (-lam * (m + 1 : ℕ)) * ∑ x ∈ s, U m x := by
        intro m hm
        rw [Finset.mul_sum]
      have hsumMixed :
          (∑ x ∈ s, ∑ m ∈ Finset.range L,
            Real.exp (-lam * (m + 1 : ℕ)) * U m x) =
          ∑ m ∈ Finset.range L,
            Real.exp (-lam * (m + 1 : ℕ)) * ∑ x ∈ s, U m x := by
        calc
          _ = ∑ m ∈ Finset.range L, ∑ x ∈ s,
                Real.exp (-lam * (m + 1 : ℕ)) * U m x := Finset.sum_comm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hsumInner m hm
      have hdecomp : (∑ x ∈ s, K x y) =
          (∑ x ∈ s, V x) +
            ∑ m ∈ Finset.range L,
              Real.exp (-lam * (m + 1 : ℕ)) * ∑ x ∈ s, U m x := by
        calc
          _ = ∑ x ∈ s, (V x + ∑ m ∈ Finset.range L,
                Real.exp (-lam * (m + 1 : ℕ)) * U m x) := by
              apply Finset.sum_congr rfl
              intro x hx
              simpa [K, V, U] using
                weighted_hattedInteraction_split L lam β t I x y
          _ = (∑ x ∈ s, V x) +
                ∑ m ∈ Finset.range L,
                  Real.exp (-lam * (m + 1 : ℕ)) * ∑ x ∈ s, U m x := by
              rw [Finset.sum_add_distrib, hsumMixed]
      have hdiag := weighted_interaction_diagonal_column_sum_le t I y s
      have hseries :
          (∑ m ∈ Finset.range L,
            Real.exp (-lam * (m + 1 : ℕ)) * ∑ x ∈ s, U m x) ≤ B * ρ := by
        have hmass (m : ℕ) :
            0 ≤ ∑' v : Site,
              Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v :=
          tsum_nonneg fun v => Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ (m + 1) v
        have hrate (m : ℕ) (hm : m ∈ Finset.range L) :
            Cc * Real.exp (Cc * t ^ 2 * (m + 1 : ℕ)) ≤
              C * Real.exp (C * t ^ 2 * L) := by
          have hmL : ((m + 1 : ℕ) : ℝ) ≤ L := by
            exact_mod_cast (Nat.succ_le_of_lt (Finset.mem_range.mp hm))
          have harg : Cc * t ^ 2 * (m + 1 : ℕ) ≤ C * t ^ 2 * L := by
            calc
              Cc * t ^ 2 * (m + 1 : ℕ) = Cc * (t ^ 2 * (m + 1 : ℕ)) := by ring
              _ ≤ C * (t ^ 2 * (m + 1 : ℕ)) :=
                mul_le_mul_of_nonneg_right hCcC (by positivity)
              _ ≤ C * (t ^ 2 * L) := by
                have htime : t ^ 2 * (m + 1 : ℕ) ≤ t ^ 2 * L :=
                  mul_le_mul_of_nonneg_left hmL (sq_nonneg t)
                exact mul_le_mul_of_nonneg_left htime (by positivity)
              _ = C * t ^ 2 * L := by ring
          apply mul_le_mul hCcC (Real.exp_le_exp.mpr harg)
          · exact Real.exp_nonneg _
          · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) hC
        have hterm (m : ℕ) (hm : m ∈ Finset.range L) :
            Real.exp (-lam * (m + 1 : ℕ)) * ∑ x ∈ s, U m x ≤
              B * (Real.exp (-lam * (m + 1 : ℕ)) *
                ∑' v : Site,
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v) := by
          have hu := hcolBound β I hI (hMom I hI) t ht y hyEq (m + 1) s
          have hu' : (∑ x ∈ s, U m x) ≤
              Cc * Real.exp (Cc * t ^ 2 * (m + 1 : ℕ)) *
                ∑' v : Site,
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v := by
            simpa [U] using hu
          have hu'' : (∑ x ∈ s, U m x) ≤ B *
              ∑' v : Site,
                Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v :=
            hu'.trans (mul_le_mul_of_nonneg_right (hrate m hm) (hmass m))
          calc
            _ ≤ Real.exp (-lam * (m + 1 : ℕ)) *
                (B * ∑' v : Site,
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v) :=
              mul_le_mul_of_nonneg_left hu'' (Real.exp_nonneg _)
            _ = _ := by ring
        calc
          _ ≤ ∑ m ∈ Finset.range L,
              B * (Real.exp (-lam * (m + 1 : ℕ)) *
                ∑' v : Site,
                  Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v) :=
            Finset.sum_le_sum fun m hm => hterm m hm
          _ = B * ∑ m ∈ Finset.range L,
                Real.exp (-lam * (m + 1 : ℕ)) *
                  ∑' v : Site,
                    Collision.spatialRenewal (Critical2DKPZ.Polymer.sigmaSq β) (m + 1) v := by
              rw [Finset.mul_sum]
          _ ≤ B * ρ := by
            dsimp [B, ρ]
            exact mul_le_mul_of_nonneg_left
              (sum_exp_mul_tsum_spatialRenewal_le hσ hlam L hsmall) hB
      exact hdecomp ▸ add_le_add hdiag hseries
    · have hyNotColl : ¬IsCollisionConfiguration I y := fun hc => hyEq hc.1
      have hUzero (m : ℕ) (x : LatticeConfiguration h) :
          interactingReplicaKernelAbs β I (m + 1) x y = 0 := by
        exact interactingReplicaKernelAbs_zero_of_not_collision_right β I (m + 1) x y hyNotColl
      have hdiagzero (x : LatticeConfiguration h) :
          weightedKernel (replicaExponentialWeight t)
            (fun x y => if x = y ∧ IsCollisionConfiguration I y then 1 else 0) x y = 0 := by
        by_cases hxy : x = y
        · subst x
          simp [weightedKernel, hyNotColl]
        · simp [weightedKernel, hxy]
      have hKzero (x : LatticeConfiguration h) : K x y = 0 := by
        rw [show K x y =
          weightedKernel (replicaExponentialWeight t)
            (hattedInteractingReplicaKernelAbs L lam β I) x y by rfl,
          weighted_hattedInteraction_split L lam β t I x y]
        have hsumzero :
            (∑ m ∈ Finset.range L,
              Real.exp (-lam * (m + 1 : ℕ)) *
                weightedKernel (replicaExponentialWeight t)
                  (fun x y => interactingReplicaKernelAbs β I (m + 1) x y) x y) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          have hterm : weightedKernel (replicaExponentialWeight t)
              (fun x y => interactingReplicaKernelAbs β I (m + 1) x y) x y = 0 := by
            simp [weightedKernel, hUzero m x]
          simp [hterm]
        rw [hdiagzero, hsumzero]
        simp
      simpa [hKzero] using (show 0 ≤ 1 + B * ρ from by positivity)
  exact finiteLpNorm_finiteKernelApply_le_of_rowCol s K hKnonneg (le_of_lt hq)
    (a := 1 + B * ρ) hrow hcol f

end

end Critical2DKPZ.MomentBounds

end
