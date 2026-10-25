/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25GapCompositions
public import Critical2DKPZ.MomentBounds.CCR25FiniteSupportComposition
public import Critical2DKPZ.MomentBounds.CCR25ActivePathCompression
import Mathlib.Tactic

/-! # Composition identities for timed CCR25 interaction runs -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- Configurations `x` with each `x i` in `endpoints (z i) d`. -/
def ccr25FreeTargetConfigurations {h : ℕ} (d : ℕ)
    (z : LatticeConfiguration h) : Finset (LatticeConfiguration h) :=
  Fintype.piFinset fun i : Fin h => Critical2DKPZ.Polymer.endpoints (z i) d

private theorem freeReplicaKernel_zero_of_not_timedTarget
    {h : ℕ} (d : ℕ) (I : ReplicaPartition h)
    (z x : LatticeConfiguration h)
    (hx : x ∉ ccr25FreeTargetConfigurations d z) :
    freeReplicaKernel d I I z x = 0 := by
  have hmissing : ∃ i : Fin h,
      x i ∉ Critical2DKPZ.Polymer.endpoints (z i) d := by
    by_contra hnot
    apply hx
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hnot ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmissing
  have hq : Critical2DKPZ.srwKernel d (x i - z i) = 0 :=
    Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem d (z i) (x i) hi
  have hprod : (∏ j : Fin h, Critical2DKPZ.srwKernel d (x j - z j)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hq
  simp [freeReplicaKernel, hprod]

/-- Free target configurations of `z`, iterated over the list of gaps. -/
def ccr25TimedRunTargetConfigurations {h : ℕ} :
    List ℕ → LatticeConfiguration h → Finset (LatticeConfiguration h)
  | [], z => {z}
  | d :: ds, z =>
      (ccr25TimedRunTargetConfigurations ds z).biUnion
        (ccr25FreeTargetConfigurations d)

/-- A timed interaction run has finite endpoint support, contained in the
configurations reachable through its prescribed free gaps. -/
theorem ccr25TimedInteractionRunAbs_zero_of_not_target
    {h : ℕ} (β : ℝ) (I : ReplicaPartition h) :
    ∀ (gaps : List ℕ) (z x : LatticeConfiguration h),
      x ∉ ccr25TimedRunTargetConfigurations gaps z →
        ccr25TimedInteractionRunAbs β I gaps z x = 0 := by
  intro gaps
  induction gaps with
  | nil =>
      intro z x hx
      have hne : z ≠ x := by
        intro heq
        subst x
        exact hx (Finset.mem_singleton_self z)
      simp [ccr25TimedInteractionRunAbs, hne]
  | cons d ds ih =>
      intro z x hx
      have hterm (y : LatticeConfiguration h) :
          ccr25TimedInteractionRunAbs β I ds z y *
              freeReplicaKernel d I I y x = 0 := by
        by_cases hy : y ∈ ccr25TimedRunTargetConfigurations ds z
        · have hxy : x ∉ ccr25FreeTargetConfigurations d y := by
            intro hxy
            exact hx (Finset.mem_biUnion.mpr ⟨y, hy, hxy⟩)
          rw [freeReplicaKernel_zero_of_not_timedTarget d I y x hxy]
          simp
        · rw [ih z y hy]
          simp
      simp [ccr25TimedInteractionRunAbs, hterm]


/-- The zero-gap interaction kernel acts as the identity when tested against a
free kernel, whose source endpoint already lies in the collision stratum. -/
private theorem ccr25TimedInteractionRunAbs_nil_comp_free
    {h : ℕ} (β : ℝ) (I : ReplicaPartition h)
    (z x : LatticeConfiguration h) (d : ℕ) :
    (∑' y : LatticeConfiguration h,
      ccr25TimedInteractionRunAbs β I [] z y * freeReplicaKernel d I I y x) =
        freeReplicaKernel d I I z x := by
  classical
  have hsingle : ∀ y ≠ z,
      ccr25TimedInteractionRunAbs β I [] z y * freeReplicaKernel d I I y x = 0 := by
    intro y hy
    have hzy : z ≠ y := Ne.symm hy
    simp [ccr25TimedInteractionRunAbs, hzy]
  rw [tsum_eq_single z hsingle]
  by_cases hz : IsCollisionConfiguration I z
  · simp [ccr25TimedInteractionRunAbs, hz]
  · simp [ccr25TimedInteractionRunAbs, hz, freeReplicaKernel]

private theorem ccr25TimedInteractionRunAbs_zero_of_not_collision_target
    {h : ℕ} (β : ℝ) (I : ReplicaPartition h) :
    ∀ (gaps : List ℕ) (z x : LatticeConfiguration h),
      ¬ IsCollisionConfiguration I x →
        ccr25TimedInteractionRunAbs β I gaps z x = 0 := by
  intro gaps
  induction gaps with
  | nil => intro z x hx; simp [ccr25TimedInteractionRunAbs, hx]
  | cons d ds ih =>
      intro z x hx
      simp [ccr25TimedInteractionRunAbs, freeReplicaKernel, hx]

/-- The zero-gap interaction kernel is the identity on the collision
stratum, so it composes neutrally on the right of any timed run. -/
private theorem ccr25TimedInteractionRunAbs_nil_comp
    {h : ℕ} (β : ℝ) (I : ReplicaPartition h)
    (gaps : List ℕ) (z x : LatticeConfiguration h) :
    ccr25TimedInteractionRunAbs β I gaps z x =
      ∑' y : LatticeConfiguration h,
        ccr25TimedInteractionRunAbs β I gaps z y *
          ccr25TimedInteractionRunAbs β I [] y x := by
  classical
  have hsingle : ∀ y ≠ x,
      ccr25TimedInteractionRunAbs β I gaps z y *
        ccr25TimedInteractionRunAbs β I [] y x = 0 := by
    intro y hy
    simp [ccr25TimedInteractionRunAbs, hy]
  rw [tsum_eq_single x hsingle]
  by_cases hx : IsCollisionConfiguration I x
  · simp [ccr25TimedInteractionRunAbs, hx]
  · rw [ccr25TimedInteractionRunAbs_zero_of_not_collision_target
      β I gaps z x hx]
    simp [ccr25TimedInteractionRunAbs, hx]

/-- Split a later gap list from an earlier one. The zero-gap interaction
kernel is the identity on the collision stratum, so the convolution law also
holds when the later list is empty. -/
theorem ccr25TimedInteractionRunAbs_append {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h) :
    ∀ (later earlier : List ℕ) (z x : LatticeConfiguration h),
        ccr25TimedInteractionRunAbs β I (later ++ earlier) z x =
          ∑' y : LatticeConfiguration h,
            ccr25TimedInteractionRunAbs β I earlier z y *
              ccr25TimedInteractionRunAbs β I later y x := by
  intro later
  induction later with
  | nil =>
      intro earlier z x
      simpa using ccr25TimedInteractionRunAbs_nil_comp β I earlier z x
  | cons d ds ih =>
      intro earlier z x
      cases ds with
      | nil =>
          change ccr25TimedInteractionRunAbs β I (d :: earlier) z x = _
          rw [ccr25TimedInteractionRunAbs]
          calc
            _ = ∑' y : LatticeConfiguration h,
                  |replicaPartitionDisorderMoment β I| *
                    (ccr25TimedInteractionRunAbs β I earlier z y *
                      freeReplicaKernel d I I y x) := by
                rw [← tsum_mul_left]
            _ = ∑' y : LatticeConfiguration h,
                  ccr25TimedInteractionRunAbs β I earlier z y *
                    ccr25TimedInteractionRunAbs β I [d] y x := by
                apply tsum_congr
                intro y
                rw [ccr25TimedInteractionRunAbs,
                  ccr25TimedInteractionRunAbs_nil_comp_free]
                ring
      | cons e es =>
          rw [show (d :: (e :: es)) ++ earlier =
              d :: ((e :: es) ++ earlier) by rfl,
            ccr25TimedInteractionRunAbs]
          have hIH (v : LatticeConfiguration h) :
              ccr25TimedInteractionRunAbs β I ((e :: es) ++ earlier) z v =
                ∑' y : LatticeConfiguration h,
                  ccr25TimedInteractionRunAbs β I earlier z y *
                    ccr25TimedInteractionRunAbs β I (e :: es) y v :=
            ih earlier z v
          rw [show (∑' v : LatticeConfiguration h,
              ccr25TimedInteractionRunAbs β I ((e :: es) ++ earlier) z v *
                freeReplicaKernel d I I v x) =
              ∑' v : LatticeConfiguration h,
                (∑' y : LatticeConfiguration h,
                  ccr25TimedInteractionRunAbs β I earlier z y *
                    ccr25TimedInteractionRunAbs β I (e :: es) y v) *
                  freeReplicaKernel d I I v x by
                apply tsum_congr
                intro v
                rw [hIH v]]
          let S := ccr25TimedRunTargetConfigurations earlier z
          let T : LatticeConfiguration h → Finset (LatticeConfiguration h) :=
            fun y => ccr25TimedRunTargetConfigurations (e :: es) y
          have hfubini :=
            tsum_mul_tsum_eq_tsum_composed_of_finSupport
              S T
              (fun y => ccr25TimedInteractionRunAbs β I earlier z y)
              (fun y v => ccr25TimedInteractionRunAbs β I (e :: es) y v)
              (fun v => freeReplicaKernel d I I v x)
              (by
                intro y hy
                exact ccr25TimedInteractionRunAbs_zero_of_not_target
                  β I earlier z y hy)
              (by
                intro y hy v hv
                exact ccr25TimedInteractionRunAbs_zero_of_not_target
                  β I (e :: es) y v hv)
          calc
            _ = |replicaPartitionDisorderMoment β I| *
                ∑' y : LatticeConfiguration h,
                  ccr25TimedInteractionRunAbs β I earlier z y *
                    ∑' v : LatticeConfiguration h,
                      ccr25TimedInteractionRunAbs β I (e :: es) y v *
                        freeReplicaKernel d I I v x := by
                  congr 1
                  have hf := hfubini
                  simpa only [S, T] using hf.symm
            _ = ∑' y : LatticeConfiguration h,
                  ccr25TimedInteractionRunAbs β I earlier z y *
                    ccr25TimedInteractionRunAbs β I (d :: e :: es) y x := by
                  rw [← tsum_mul_left]
                  apply tsum_congr
                  intro y
                  rw [ccr25TimedInteractionRunAbs]
                  ring

/-- Pairing the run-kernel convolution identity with a terminal function is
exact. This is the finite-support Fubini step needed when a later equal-label
collision is absorbed into an existing interaction run. -/
theorem ccr25TimedInteractionRunAbs_append_pairing {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h)
    (later earlier : List ℕ) (z : LatticeConfiguration h)
    (f : LatticeConfiguration h → ℝ) :
    (∑' x : LatticeConfiguration h,
      ccr25TimedInteractionRunAbs β I (later ++ earlier) z x * f x) =
      ∑' y : LatticeConfiguration h,
        ccr25TimedInteractionRunAbs β I earlier z y *
          ∑' x : LatticeConfiguration h,
            ccr25TimedInteractionRunAbs β I later y x * f x := by
  classical
  let S := ccr25TimedRunTargetConfigurations earlier z
  let T : LatticeConfiguration h → Finset (LatticeConfiguration h) :=
    fun y => ccr25TimedRunTargetConfigurations later y
  have hfubini :=
    tsum_mul_tsum_eq_tsum_composed_of_finSupport
      S T
      (fun y => ccr25TimedInteractionRunAbs β I earlier z y)
      (fun y x => ccr25TimedInteractionRunAbs β I later y x)
      f
      (by
        intro y hy
        exact ccr25TimedInteractionRunAbs_zero_of_not_target
          β I earlier z y hy)
      (by
        intro y hy x hx
        exact ccr25TimedInteractionRunAbs_zero_of_not_target
          β I later y x hx)
  calc
    _ = ∑' x : LatticeConfiguration h,
        (∑' y : LatticeConfiguration h,
          ccr25TimedInteractionRunAbs β I earlier z y *
            ccr25TimedInteractionRunAbs β I later y x) * f x := by
          apply tsum_congr
          intro x
          rw [ccr25TimedInteractionRunAbs_append β I later earlier z x]
    _ = _ := by
          have hf := hfubini.symm
          simpa only [S, T] using hf


/-- A one-gap interaction run is its collision moment times the free kernel. -/
theorem ccr25TimedInteractionRunAbs_singleton {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h) (d : ℕ)
    (z x : LatticeConfiguration h) :
    ccr25TimedInteractionRunAbs β I [d] z x =
      |replicaPartitionDisorderMoment β I| * freeReplicaKernel d I I z x := by
  change |replicaPartitionDisorderMoment β I| *
      (∑' y : LatticeConfiguration h,
        ccr25TimedInteractionRunAbs β I [] z y * freeReplicaKernel d I I y x) = _
  rw [ccr25TimedInteractionRunAbs_nil_comp_free]


end Critical2DKPZ.MomentBounds

end
