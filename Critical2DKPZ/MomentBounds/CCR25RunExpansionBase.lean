/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25PartitionWords
public import Critical2DKPZ.MomentBounds.CCR25FiniteMomentExpansion
public import Critical2DKPZ.MomentBounds.CCR25PartitionMoments
import Critical2DKPZ.Lattice.Basic
import Mathlib.Tactic

/-! # One-step base and sequence constraints for CCR25 moment runs -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- One transition of independent replicas, with the endpoint restricted to
the collision stratum of `I`. -/
def replicaStepKernel {h : ℕ} (I : ReplicaPartition h)
    (z x : LatticeConfiguration h) : ℝ :=
  freeReplicaKernel 1 ⊥ I z x

/-- Weighted walk paths which hit the prescribed collision strata in order. -/
def replicaPathWeight {h : ℕ} : List (ReplicaPartition h) →
    LatticeConfiguration h → ℝ
  | [], _ => 1
  | I :: Is, z => ∑' x, replicaStepKernel I z x * replicaPathWeight Is x

/-- Finite time-indexed partition sequences in which every replica participates
in a collision at least once. -/
def fullSupportSequences (h L : ℕ) : Finset (Fin L → ReplicaPartition h) := by
  classical
  exact Finset.univ.filter fun I =>
    ∀ a : Fin h, ∃ n : Fin L, InCollisionBlock (I n) a


/-- Sites at sup-distance at most `L` from at least one point of `A`. -/
def siteBox (A : Finset Site) (L : ℕ) : Finset Site :=
  A.biUnion fun z => Fintype.piFinset fun i : Fin 2 => Finset.Icc (z i - L) (z i + L)

/-- Configurations reachable within `L` steps from a product start set. -/
def configBox (h : ℕ) (A : Finset Site) (L : ℕ) :
    Finset (LatticeConfiguration h) :=
  Fintype.piFinset fun _ : Fin h => siteBox A L

/-- Indicator of the CCR collision stratum of `J`. -/
def collisionIndicator {h : ℕ} (J : ReplicaPartition h)
    (x : LatticeConfiguration h) : ℝ := by
  classical
  exact if IsCollisionConfiguration J x then 1 else 0

/-- Configuration after one specified direction is chosen for each replica. -/
def ccr25RunOneStepConfiguration {h : ℕ} (z : LatticeConfiguration h)
    (directions : Fin h → Fin 4) : LatticeConfiguration h :=
  fun i => z i + Critical2DKPZ.srwStep (directions i)

private theorem srwKernel_one_directionSum (z : Site) :
    Critical2DKPZ.srwKernel 1 z =
      (4 : ℝ)⁻¹ * ∑ d : Fin 4,
        if Critical2DKPZ.srwStep d = z then 1 else 0 := by
  rw [show 1 = 0 + 1 by omega, Critical2DKPZ.srwKernel_succ]
  simp only [Critical2DKPZ.srwKernel_zero, sub_eq_zero]
  simp only [eq_comm]
  rw [div_eq_mul_inv]
  ring_nf

private theorem ccr25RunProd_srwKernel_one_eq {h : ℕ}
    (z x : LatticeConfiguration h) :
    ∏ i : Fin h, Critical2DKPZ.srwKernel 1 (x i - z i) =
      (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
        if ccr25RunOneStepConfiguration z directions = x then 1 else 0 := by
  classical
  have hconfig (directions : Fin h → Fin 4) :
      (∀ i : Fin h, Critical2DKPZ.srwStep (directions i) = x i - z i) ↔
        ccr25RunOneStepConfiguration z directions = x := by
    constructor
    · intro hd
      funext i
      ext j
      have hj := congrFun (hd i) j
      change z i j + Critical2DKPZ.srwStep (directions i) j = x i j
      change Critical2DKPZ.srwStep (directions i) j = x i j - z i j at hj
      omega
    · intro hx i
      have hi := congrFun hx i
      ext j
      have hj := congrFun hi j
      change Critical2DKPZ.srwStep (directions i) j = x i j - z i j
      change z i j + Critical2DKPZ.srwStep (directions i) j = x i j at hj
      omega
  calc
    _ = ∏ i : Fin h, ((4 : ℝ)⁻¹ * ∑ d : Fin 4,
        if Critical2DKPZ.srwStep d = x i - z i then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact srwKernel_one_directionSum (x i - z i)
    _ = (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
        ∏ i : Fin h,
          if Critical2DKPZ.srwStep (directions i) = x i - z i then 1 else 0 := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin,
        Fintype.prod_sum]
    _ = (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
        if ccr25RunOneStepConfiguration z directions = x then 1 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro directions hdirections
      by_cases hdir : ∀ i : Fin h,
          Critical2DKPZ.srwStep (directions i) = x i - z i
      · rw [(hconfig directions).mp hdir]
        simp [hdir]
      · have hbad : ∃ i : Fin h,
            ¬ Critical2DKPZ.srwStep (directions i) = x i - z i := not_forall.mp hdir
        obtain ⟨i, hi⟩ := hbad
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])]
        have hx : ccr25RunOneStepConfiguration z directions ≠ x := by
          intro heq
          exact hi ((hconfig directions).mpr heq i)
        simp [hx]

private theorem collisionConfig_bot {h : ℕ} (z : LatticeConfiguration h) :
    IsCollisionConfiguration (⊥ : ReplicaPartition h) z := by
  constructor
  · intro i j hij
    have hij' : i = j := by simpa using hij
    exact congrArg z hij'
  · intro i j hi _ _
    obtain ⟨k, hik, hrel⟩ := hi
    have heq : i = k := by simpa using hrel
    exact (hik heq.symm).elim

/-- The replica step kernel equals `(1/4)^h` times the sum over direction choices of the collision
indicator of the configuration reached from `z`. -/
theorem replicaStepKernel_eq_directionSum {h : ℕ} (I : ReplicaPartition h)
    (z x : LatticeConfiguration h) :
    replicaStepKernel I z x =
      (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
        if ccr25RunOneStepConfiguration z directions = x then collisionIndicator I x else 0 := by
  classical
  by_cases hI : IsCollisionConfiguration I x
  · simp [replicaStepKernel, freeReplicaKernel, collisionConfig_bot, hI,
      ccr25RunProd_srwKernel_one_eq, collisionIndicator]
  · simp [replicaStepKernel, freeReplicaKernel, collisionConfig_bot, hI,
      collisionIndicator]

/-- Integrating one collision-restricted replica step against any function is
the uniform finite average over direction families. -/
theorem tsum_replicaStepKernel_mul_eq_directionSum {h : ℕ}
    (I : ReplicaPartition h) (z : LatticeConfiguration h)
    (f : LatticeConfiguration h → ℝ) :
    (∑' x, replicaStepKernel I z x * f x) =
      (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
        collisionIndicator I (ccr25RunOneStepConfiguration z directions) *
          f (ccr25RunOneStepConfiguration z directions) := by
  classical
  let S : Finset (LatticeConfiguration h) :=
    Finset.univ.image (ccr25RunOneStepConfiguration z)
  have hzero (x : LatticeConfiguration h) (hx : x ∉ S) :
      replicaStepKernel I z x = 0 := by
    rw [replicaStepKernel_eq_directionSum]
    have hne : ∀ directions : Fin h → Fin 4,
        ccr25RunOneStepConfiguration z directions ≠ x := by
      intro directions heq
      exact hx (Finset.mem_image.mpr ⟨directions, Finset.mem_univ _, heq⟩)
    simp [hne]
  have hsingle (directions : Fin h → Fin 4) :
      (∑ x ∈ S, if ccr25RunOneStepConfiguration z directions = x then
        collisionIndicator I x * f x else 0) =
        collisionIndicator I (ccr25RunOneStepConfiguration z directions) *
          f (ccr25RunOneStepConfiguration z directions) := by
    let x₀ := ccr25RunOneStepConfiguration z directions
    have hx₀ : x₀ ∈ S := Finset.mem_image.mpr ⟨directions, Finset.mem_univ _, rfl⟩
    rw [Finset.sum_eq_single x₀]
    · simp [x₀]
    · intro x hx hne
      simp [x₀, hne.symm]
    · intro hnot
      exact (hnot hx₀).elim
  have hpoint (x : LatticeConfiguration h) :
      replicaStepKernel I z x * f x =
        (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
          if ccr25RunOneStepConfiguration z directions = x then
            collisionIndicator I x * f x else 0 := by
    rw [replicaStepKernel_eq_directionSum]
    calc
      ((4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
          if ccr25RunOneStepConfiguration z directions = x then collisionIndicator I x else 0) * f x =
          (4 : ℝ)⁻¹ ^ h *
            ((∑ directions : Fin h → Fin 4,
              if ccr25RunOneStepConfiguration z directions = x then collisionIndicator I x else 0) * f x) := by
            ring
      _ = (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
          (if ccr25RunOneStepConfiguration z directions = x then collisionIndicator I x else 0) * f x := by
            rw [Finset.sum_mul]
      _ = (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
          if ccr25RunOneStepConfiguration z directions = x then
            collisionIndicator I x * f x else 0 := by
            congr 1
            apply Finset.sum_congr rfl
            intro directions hdirections
            by_cases heq : ccr25RunOneStepConfiguration z directions = x <;> simp [heq]
  calc
    _ = ∑ x ∈ S, replicaStepKernel I z x * f x :=
      tsum_eq_sum (s := S) (fun x hx => by simp [hzero x hx])
    _ = ∑ x ∈ S, (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
          if ccr25RunOneStepConfiguration z directions = x then
            collisionIndicator I x * f x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpoint x
    _ = (4 : ℝ)⁻¹ ^ h * ∑ directions : Fin h → Fin 4,
          collisionIndicator I (ccr25RunOneStepConfiguration z directions) *
            f (ccr25RunOneStepConfiguration z directions) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro directions hdirections
      exact hsingle directions

/-- The replica step kernel is nonnegative. -/
theorem replicaStepKernel_nonneg {h : ℕ} (I : ReplicaPartition h)
    (z x : LatticeConfiguration h) : 0 ≤ replicaStepKernel I z x := by
  unfold replicaStepKernel freeReplicaKernel
  split_ifs
  · exact Finset.prod_nonneg fun _ _ => Critical2DKPZ.srwKernel_nonneg _ _
  · exact le_of_eq rfl

/-- The replica path weight of any list of partitions is nonnegative. -/
theorem replicaPathWeight_nonneg {h : ℕ} (Is : List (ReplicaPartition h))
    (z : LatticeConfiguration h) : 0 ≤ replicaPathWeight Is z := by
  induction Is generalizing z with
  | nil => norm_num [replicaPathWeight]
  | cons I Is ih =>
      simp only [replicaPathWeight]
      exact tsum_nonneg fun x => mul_nonneg
        (replicaStepKernel_nonneg I z x) (ih x)

/-- One unconstrained replica transition has total mass one. -/
theorem tsum_replicaStepKernel_bot_eq_one {h : ℕ} (z : LatticeConfiguration h) :
    (∑' x : LatticeConfiguration h, replicaStepKernel ⊥ z x) = 1 := by
  rw [show (∑' x : LatticeConfiguration h, replicaStepKernel ⊥ z x) =
      ∑' x, replicaStepKernel ⊥ z x * (1 : ℝ) by simp]
  rw [tsum_replicaStepKernel_mul_eq_directionSum]
  have hcollision (d : Fin h → Fin 4) :
      collisionIndicator ⊥ (ccr25RunOneStepConfiguration z d) = 1 := by
    rw [collisionIndicator, ite_eq_left (collisionConfig_bot _)]
  calc
    (4 : ℝ)⁻¹ ^ h *
        ∑ d : Fin h → Fin 4,
          collisionIndicator ⊥ (ccr25RunOneStepConfiguration z d) * 1 =
      (4 : ℝ)⁻¹ ^ h * Fintype.card (Fin h → Fin 4) := by
        congr 1
        calc
          _ = ∑ d : Fin h → Fin 4, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [hcollision d]
            ring
          _ = Fintype.card (Fin h → Fin 4) := by simp
    _ = 1 := by simp

/-- A sequence consisting only of unrestricted collision labels has total
path weight one, regardless of its initial configuration. -/
theorem replicaPathWeight_replicate_bot_eq_one {h : ℕ} :
    ∀ k : ℕ, ∀ z : LatticeConfiguration h,
      replicaPathWeight (List.replicate k (⊥ : ReplicaPartition h)) z = 1 := by
  intro k
  induction k with
  | zero =>
      intro z
      simp [replicaPathWeight]
  | succ k ih =>
      intro z
      change (∑' x : LatticeConfiguration h,
        replicaStepKernel ⊥ z x *
          replicaPathWeight (List.replicate k ⊥) x) = 1
      calc
        _ = ∑' x : LatticeConfiguration h, replicaStepKernel ⊥ z x * 1 := by
          apply tsum_congr
          intro x
          rw [ih]
        _ = 1 := by simpa using tsum_replicaStepKernel_bot_eq_one z

private theorem memLp_prod_centeredPointToPlane {h : ℕ}
    (β : ℝ) (a n : ℕ) (w : Fin h → Site) :
    ∀ p : ℝ≥0∞, p ≠ ∞ →
      MemLp (fun ω : Disorder =>
        ∏ i : Fin h,
          (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) p disorderLaw := by
  induction h with
  | zero =>
      intro p hp
      change MemLp (fun _ : Disorder => (1 : ℝ)) p disorderLaw
      exact memLp_const 1
  | succ h ih =>
      intro p hp
      have hp2 : 2 * p ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hp
      have hhead : MemLp
          (fun ω : Disorder => Critical2DKPZ.pointToPlane β a n (w 0) ω - 1)
          (2 * p) disorderLaw :=
        (Critical2DKPZ.Polymer.memLp_pointToPlane β a n (w 0) (2 * p) hp2).sub
          (memLp_const 1)
      have htail : MemLp
          (fun ω : Disorder =>
            ∏ i : Fin h,
              (Critical2DKPZ.pointToPlane β a n (w i.succ) ω - 1))
          (2 * p) disorderLaw := ih (fun i => w i.succ) (2 * p) hp2
      have hprod :
          (fun ω : Disorder =>
            ∏ i : Fin (h + 1),
              (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) =
          fun ω =>
            (Critical2DKPZ.pointToPlane β a n (w 0) ω - 1) *
              (∏ i : Fin h,
                (Critical2DKPZ.pointToPlane β a n (w i.succ) ω - 1)) := by
        funext ω
        rw [Fin.prod_univ_succ]
      rw [hprod]
      exact Critical2DKPZ.Polymer.memLp_mul_double p hhead htail

private theorem integrable_prod_centeredPointToPlane {h : ℕ}
    (β : ℝ) (a n : ℕ) (w : Fin h → Site) :
    Integrable (fun ω : Disorder =>
      ∏ i : Fin h, (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) disorderLaw :=
  memLp_one_iff_integrable.mp
    (memLp_prod_centeredPointToPlane β a n w 1 (by simp))

/-- The product over `i` of `φ (w i)` times the centered point-to-plane partition function at `w i`
is integrable under the disorder law. -/
theorem integrable_prod_scaledCenteredPointToPlane {h : ℕ}
    (β : ℝ) (a n : ℕ) (φ : Site → ℝ) (w : Fin h → Site) :
    Integrable (fun ω : Disorder =>
      ∏ i : Fin h, φ (w i) *
        (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) disorderLaw := by
  have hbase := integrable_prod_centeredPointToPlane β a n w
  have heq :
      (fun ω : Disorder =>
        ∏ i : Fin h, φ (w i) *
          (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) =
        fun ω => (∏ i : Fin h, φ (w i)) *
          (∏ i : Fin h,
            (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) := by
    funext ω
    rw [Finset.prod_mul_distrib]
  rw [heq]
  exact hbase.const_mul _


end

end Critical2DKPZ.MomentBounds

end
