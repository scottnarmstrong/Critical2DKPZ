/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25PartitionWords
public import Critical2DKPZ.MomentBounds.CCR25FiniteMomentExpansion
public import Critical2DKPZ.MomentBounds.CCR25PartitionMoments
public import Critical2DKPZ.MomentBounds.CCR25RunExpansionBase
import Critical2DKPZ.Lattice.Basic
import Mathlib.Tactic

/-! # Finite-start expansion for CCR25 moment runs -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- Coordinate sets for independent replicas that start at different sites. -/
def ccr25RunReplicaChaosCoordinateSets {h n : ℕ} (a : ℕ)
    (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) :
    Fin h → Finset (ℕ × Site) :=
  fun i => ccr25ChaosCoordinates a (w i) (choices i)

private theorem prod_ccr25RunCenteredChaosTerms_eq {h n : ℕ}
    (β : ℝ) (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) (ω : Disorder) :
    (∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω) =
      ((4 : ℝ)⁻¹ ^ n) ^ h *
        ∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β
          (ccr25RunReplicaChaosCoordinateSets a w choices i) ω := by
  calc
    (∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω) =
        ∏ i : Fin h,
          ((4 : ℝ)⁻¹ ^ n) *
            Critical2DKPZ.Polymer.chaosMonomial β
              (ccr25RunReplicaChaosCoordinateSets a w choices i) ω := by
      apply Finset.prod_congr rfl
      intro i hi
      exact ccr25CenteredChaosTerm_eq_chaosMonomial β a (w i) (choices i) ω
    _ = ((4 : ℝ)⁻¹ ^ n) ^ h *
          ∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β
            (ccr25RunReplicaChaosCoordinateSets a w choices i) ω := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]

private theorem integrable_prod_ccr25RunCenteredChaosTerms {h n : ℕ}
    (β : ℝ) (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) :
    Integrable (fun ω : Disorder =>
      ∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω) disorderLaw := by
  rw [show (fun ω : Disorder =>
      ∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω) =
    fun ω => ((4 : ℝ)⁻¹ ^ n) ^ h *
      ∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β
        (ccr25RunReplicaChaosCoordinateSets a w choices i) ω from by
      funext ω
      exact prod_ccr25RunCenteredChaosTerms_eq β a w choices ω]
  exact (integrable_replicaChaosMonomialProduct β
    (ccr25RunReplicaChaosCoordinateSets a w choices)).const_mul _

private theorem integral_prod_ccr25RunCenteredChaosTerms {h n : ℕ}
    (β : ℝ) (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) :
    ∫ ω : Disorder,
        (∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω) ∂disorderLaw =
      ((4 : ℝ)⁻¹ ^ n) ^ h *
        ∏ z ∈ chaosOccurrenceUnion (ccr25RunReplicaChaosCoordinateSets a w choices),
          gaussianDisorderMoment β
            (chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z) := by
  rw [show (fun ω : Disorder =>
      ∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω) =
    fun ω => ((4 : ℝ)⁻¹ ^ n) ^ h *
      ∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β
        (ccr25RunReplicaChaosCoordinateSets a w choices i) ω from by
      funext ω
      exact prod_ccr25RunCenteredChaosTerms_eq β a w choices ω]
  rw [integral_const_mul,
    integral_chaosMonomial_product_eq_gaussianMoments]

/-- Mixed-start finite chaos expansion: integrating a product of centered
point-to-plane terms produces the Gaussian coordinate moments for their union. -/
theorem integral_prod_centeredPointToPlane_eq_chaosExpansion {h : ℕ}
    (β : ℝ) (a n : ℕ) (w : Fin h → Site) :
    ∫ ω : Disorder,
        (∏ i : Fin h,
          (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) ∂disorderLaw =
      ((4 : ℝ)⁻¹ ^ n) ^ h *
        ∑ choices ∈ Fintype.piFinset
          (fun _ : Fin h => ccr25CenteredChaosIndices n),
          ∏ z ∈ chaosOccurrenceUnion
            (ccr25RunReplicaChaosCoordinateSets a w choices),
            gaussianDisorderMoment β
              (chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z) := by
  classical
  have hpoint (ω : Disorder) :
      (∏ i : Fin h,
        (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) =
        ∑ choices ∈ Fintype.piFinset
          (fun _ : Fin h => ccr25CenteredChaosIndices n),
          ∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω := by
    calc
      _ = ∏ i : Fin h, ccr25CenteredChaosExpansion β a n (w i) ω := by
        apply Finset.prod_congr rfl
        intro i hi
        exact pointToPlane_sub_one_eq_ccr25CenteredChaosExpansion β a n (w i) ω
      _ = _ := by
        exact Finset.prod_univ_sum
          (fun _ : Fin h => ccr25CenteredChaosIndices n)
          (fun i choice => ccr25CenteredChaosTerm β a n (w i) choice ω)
  have hfun :
      (fun ω : Disorder =>
        ∏ i : Fin h,
          (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) =
        fun ω => ∑ choices ∈ Fintype.piFinset
          (fun _ : Fin h => ccr25CenteredChaosIndices n),
          ∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω :=
    funext hpoint
  rw [hfun, integral_finsetSum _ (fun choices hchoices =>
    integrable_prod_ccr25RunCenteredChaosTerms β a w choices)]
  calc
    (∑ choices ∈ Fintype.piFinset
        (fun _ : Fin h => ccr25CenteredChaosIndices n),
        ∫ ω : Disorder,
          ∏ i : Fin h, ccr25CenteredChaosTerm β a n (w i) (choices i) ω ∂disorderLaw) =
        ∑ choices ∈ Fintype.piFinset
          (fun _ : Fin h => ccr25CenteredChaosIndices n),
          ((4 : ℝ)⁻¹ ^ n) ^ h *
            ∏ z ∈ chaosOccurrenceUnion
              (ccr25RunReplicaChaosCoordinateSets a w choices),
              gaussianDisorderMoment β
                (chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z) := by
      apply Finset.sum_congr rfl
      intro choices hchoices
      exact integral_prod_ccr25RunCenteredChaosTerms β a w choices
    _ = _ := by rw [Finset.mul_sum]

/-- The partition at one microscopic time induced by the replicas which chose
that time in a finite centered-chaos word. Selected replicas are related
exactly when their paths occupy the same site. -/
@[instance_reducible] def ccr25RunTimePartition {h n : ℕ} (t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) : ReplicaPartition h where
  r i j := i = j ∨
    (t ∈ (choices i).1 ∧ t ∈ (choices j).1 ∧
      Critical2DKPZ.walkPosition (w i) (choices i).2 t =
        Critical2DKPZ.walkPosition (w j) (choices j).2 t)
  iseqv := {
    refl := fun i => Or.inl rfl
    symm := by
      intro i j hij
      rcases hij with rfl | ⟨hit, hjt, hpos⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hjt, hit, hpos.symm⟩
    trans := by
      intro i j k hij hjk
      rcases hij with rfl | ⟨hit, hjt, hijpos⟩
      · exact hjk
      rcases hjk with rfl | ⟨_, hkt, hjkpos⟩
      · exact Or.inr ⟨hit, hjt, hijpos⟩
      · exact Or.inr ⟨hit, hkt, hijpos.trans hjkpos⟩
  }

/-- The time-indexed collision partitions induced by one chaos word and its
replica paths. The index `k` corresponds to physical time `k + 1`. -/
@[instance_reducible] def ccr25RunTimePartitionSequence {h n : ℕ} (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) :
    Fin n → ReplicaPartition h :=
  fun k => ccr25RunTimePartition (k.val + 1) w choices

/-- Reconstruct the per-replica chaos-time subsets from a full-support
partition sequence, retaining the prescribed replica paths. -/
def ccr25RunChoicesOfPartitionSequence {h n : ℕ}
    (I : Fin n → ReplicaPartition h) (paths : Fin h → Fin n → Fin 4) :
    Fin h → Finset ℕ × (Fin n → Fin 4) := by
  classical
  exact fun i =>
    ((Finset.univ.filter fun k : Fin n => InCollisionBlock (I k) i).image
      (fun k => k.val + 1), paths i)

/-- The inverse construction from a full-support collision sequence gives a
valid nonempty chaos-time subset for every replica. -/
theorem ccr25RunChoicesOfPartitionSequence_mem_piFinset {h n : ℕ}
    (I : Fin n → ReplicaPartition h) (paths : Fin h → Fin n → Fin 4)
    (hI : I ∈ fullSupportSequences h n) :
    ccr25RunChoicesOfPartitionSequence I paths ∈ Fintype.piFinset
      (fun _ : Fin h => ccr25CenteredChaosIndices n) := by
  classical
  apply Fintype.mem_piFinset.mpr
  intro i
  have hfull : ∀ i : Fin h, ∃ k : Fin n, InCollisionBlock (I k) i :=
    (Finset.mem_filter.mp hI).2
  let S : Finset ℕ :=
    (Finset.univ.filter fun k : Fin n => InCollisionBlock (I k) i).image
      (fun k => k.val + 1)
  have hSNonempty : S.Nonempty := by
    obtain ⟨k, hk⟩ := hfull i
    exact ⟨k.val + 1, Finset.mem_image.mpr
      ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩⟩
  have hSsubset : S ⊆ Finset.Icc 1 n := by
    intro t ht
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    simp only [Finset.mem_Icc]
    omega
  have hSpowerset : S ∈ Finset.powerset (Finset.Icc 1 n) :=
    Finset.mem_powerset.mpr hSsubset
  have hSchaos : S ∈ ccr25NonemptyChaosSubsets n := by
    apply Finset.mem_erase.mpr
    exact ⟨Finset.nonempty_iff_ne_empty.mp hSNonempty, hSpowerset⟩
  have hpair : (S, paths i) ∈ ccr25NonemptyChaosSubsets n ×ˢ Finset.univ :=
    Finset.mem_product.mpr ⟨hSchaos, Finset.mem_univ _⟩
  simpa [ccr25RunChoicesOfPartitionSequence, ccr25CenteredChaosIndices, S] using hpair

/-- The reconstructed subset contains time `k + 1` exactly when the label is
in a collision block of the prescribed partition at `k`. -/
theorem ccr25RunChoicesOfPartitionSequence_active_iff {h n : ℕ}
    (I : Fin n → ReplicaPartition h) (paths : Fin h → Fin n → Fin 4)
    (i : Fin h) (k : Fin n) :
    k.val + 1 ∈ (ccr25RunChoicesOfPartitionSequence I paths i).1 ↔
      InCollisionBlock (I k) i := by
  classical
  change k.val + 1 ∈
      (Finset.univ.filter fun j : Fin n => InCollisionBlock (I j) i).image
        (fun j => j.val + 1) ↔ _
  constructor
  · intro hk
    obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp hk
    have hjk : j = k := Fin.ext (by omega)
    subst j
    exact (Finset.mem_filter.mp hj).2
  · intro hk
    exact Finset.mem_image.mpr ⟨k,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩, rfl⟩

/-- A collision-compatible path sequence reconstructs exactly its prescribed
partition sequence from the per-replica chaos subsets. -/
theorem ccr25RunTimePartitionSequence_choicesOf_eq {h n : ℕ}
    (w : Fin h → Site) (I : Fin n → ReplicaPartition h)
    (paths : Fin h → Fin n → Fin 4)
    (hcollision : ∀ k : Fin n,
      IsCollisionConfiguration (I k)
        (fun i => Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1))) :
    ccr25RunTimePartitionSequence w
      (ccr25RunChoicesOfPartitionSequence I paths) = I := by
  funext k
  apply Setoid.ext
  intro i j
  change i = j ∨
      (k.val + 1 ∈
          (ccr25RunChoicesOfPartitionSequence I paths i).1 ∧
        k.val + 1 ∈
          (ccr25RunChoicesOfPartitionSequence I paths j).1 ∧
        Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1) =
          Critical2DKPZ.walkPosition (w j) (paths j) (k.val + 1)) ↔
    (I k).r i j
  rw [ccr25RunChoicesOfPartitionSequence_active_iff,
    ccr25RunChoicesOfPartitionSequence_active_iff]
  constructor
  · rintro (rfl | ⟨hi, hj, hpos⟩)
    · exact (I k).refl i
    · by_contra hnot
      have hsep := (hcollision k).2 i j hi hj hnot
      exact hsep hpos
  · intro hij
    by_cases heq : i = j
    · exact Or.inl heq
    · right
      have hi : InCollisionBlock (I k) i := ⟨j, Ne.symm heq, hij⟩
      have hj : InCollisionBlock (I k) j := ⟨i, heq, (I k).symm' hij⟩
      exact ⟨hi, hj, (hcollision k).1 i j hij⟩

/-- The path configuration at time `t` belongs to the collision stratum of
the partition induced by the selected chaos coordinates at that time. -/
theorem ccr25RunTimePartition_path_isCollisionConfiguration {h n : ℕ}
    (t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) :
    IsCollisionConfiguration (ccr25RunTimePartition t w choices)
      (fun i => Critical2DKPZ.walkPosition (w i) (choices i).2 t) := by
  constructor
  · intro i j hij
    rcases hij with rfl | ⟨_, _, hpos⟩
    · rfl
    · exact hpos
  · intro i j hiBlock hjBlock hnot
    apply Classical.byContradiction
    intro hne
    apply hnot
    right
    have hactive (i : Fin h) (hi : InCollisionBlock
        (ccr25RunTimePartition t w choices) i) : t ∈ (choices i).1 := by
      obtain ⟨j, hij, hrel⟩ := hi
      rcases hrel with rfl | ⟨hactive, _, _⟩
      · exact (hij rfl).elim
      · exact hactive
    have hiActive := hactive i hiBlock
    have hjActive := hactive j hjBlock
    exact ⟨hiActive, hjActive, by
      exact Classical.not_not.mp hne⟩

/-- A replica is in a collision block at time `t` precisely when it chose the
time and shares its site with another selected replica. -/
theorem ccr25RunTimePartition_inCollisionBlock_iff {h n : ℕ}
    (t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) (i : Fin h) :
    InCollisionBlock (ccr25RunTimePartition t w choices) i ↔
      t ∈ (choices i).1 ∧ ∃ j, j ≠ i ∧ t ∈ (choices j).1 ∧
        Critical2DKPZ.walkPosition (w i) (choices i).2 t =
          Critical2DKPZ.walkPosition (w j) (choices j).2 t := by
  constructor
  · rintro ⟨j, hji, hrel⟩
    rcases hrel with rfl | ⟨hi, hj, hpos⟩
    · exact (hji rfl).elim
    · exact ⟨hi, j, hji, hj, hpos⟩
  · rintro ⟨hi, j, hji, hj, hpos⟩
    exact ⟨j, hji, Or.inr ⟨hi, hj, hpos⟩⟩

/-- A chaos replica uses the coordinate `(a + t, y)` exactly when it selected
time `t` and its path is at `y` then. -/
theorem ccr25RunChaosCoordinates_mem_iff {h n : ℕ} (a t : ℕ)
    (w : Fin h → Site) (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (i : Fin h) (y : Site) :
    (a + t, y) ∈ ccr25RunReplicaChaosCoordinateSets a w choices i ↔
      t ∈ (choices i).1 ∧
        Critical2DKPZ.walkPosition (w i) (choices i).2 t = y := by
  unfold ccr25RunReplicaChaosCoordinateSets ccr25ChaosCoordinates
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨j, hj, hcoord⟩
    have htime := congrArg Prod.fst hcoord
    have hjt : j = t := Nat.add_left_cancel htime
    subst j
    exact ⟨hj, congrArg Prod.snd hcoord⟩
  · rintro ⟨ht, hy⟩
    exact Finset.mem_image.mpr ⟨t, ht, Prod.ext (by rfl) hy⟩

/-- Under the no-singleton condition, a replica is active at a time exactly
when it belongs to a nontrivial block of the induced partition. -/
theorem ccr25RunTimePartition_active_iff_inCollisionBlock {h n : ℕ}
    (a t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hnoSingleton : ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets a w choices),
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1)
    (i : Fin h) :
    t ∈ (choices i).1 ↔ InCollisionBlock (ccr25RunTimePartition t w choices) i := by
  constructor
  · intro ht
    let z : ℕ × Site := (a + t, Critical2DKPZ.walkPosition (w i) (choices i).2 t)
    have hzmem : z ∈ ccr25RunReplicaChaosCoordinateSets a w choices i := by
      change (a + t, Critical2DKPZ.walkPosition (w i) (choices i).2 t) ∈ _
      exact (ccr25RunChaosCoordinates_mem_iff a t w choices i
        (Critical2DKPZ.walkPosition (w i) (choices i).2 t)).2 ⟨ht, rfl⟩
    have hzunion : z ∈ chaosOccurrenceUnion
        (ccr25RunReplicaChaosCoordinateSets a w choices) :=
      Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hzmem⟩
    have hcountpos : 0 < chaosOccurrenceCount
        (ccr25RunReplicaChaosCoordinateSets a w choices) z := by
      change 0 < (Finset.univ.filter fun j : Fin h =>
        z ∈ ccr25RunReplicaChaosCoordinateSets a w choices j).card
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzmem⟩⟩
    have hcounttwo : 2 ≤ chaosOccurrenceCount
        (ccr25RunReplicaChaosCoordinateSets a w choices) z := by
      have hnotone := hnoSingleton z hzunion
      omega
    let S : Finset (Fin h) := Finset.univ.filter fun j =>
      z ∈ ccr25RunReplicaChaosCoordinateSets a w choices j
    have hScard : S.card = chaosOccurrenceCount
        (ccr25RunReplicaChaosCoordinateSets a w choices) z := rfl
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzmem⟩
    have hexists : ∃ j ∈ S, j ≠ i := by
      by_contra hnone
      have hsubsingleton : ∀ j ∈ S, ∀ k ∈ S, j = k := by
        intro j hj k hk
        have hj' : j = i := by
          by_contra hji
          exact hnone ⟨j, hj, hji⟩
        have hk' : k = i := by
          by_contra hki
          exact hnone ⟨k, hk, hki⟩
        exact hj'.trans hk'.symm
      have hcardle := (Finset.card_le_one).2 hsubsingleton
      omega
    obtain ⟨j, hjS, hji⟩ := hexists
    have hjcoord : z ∈ ccr25RunReplicaChaosCoordinateSets a w choices j :=
      (Finset.mem_filter.mp hjS).2
    have hjdata := (ccr25RunChaosCoordinates_mem_iff a t w choices j
      (Critical2DKPZ.walkPosition (w i) (choices i).2 t)).1 hjcoord
    have hpos := hjdata.2.symm
    exact (ccr25RunTimePartition_inCollisionBlock_iff t w choices i).2
      ⟨ht, j, hji, hjdata.1, hpos⟩
  · intro hiBlock
    exact ((ccr25RunTimePartition_inCollisionBlock_iff t w choices i).1 hiBlock).1

/-- The multiplicity of a disorder coordinate in a mixed-start chaos word is
the number of replicas selected at its time and position. -/
theorem ccr25RunChaosOccurrenceCount_eq_card {h n : ℕ} (a t : ℕ)
    (w : Fin h → Site) (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) (y : Site) :
    chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) (a + t, y) =
      (Finset.univ.filter fun i : Fin h =>
        t ∈ (choices i).1 ∧
          Critical2DKPZ.walkPosition (w i) (choices i).2 t = y).card := by
  rw [chaosOccurrenceCount]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ccr25RunChaosCoordinates_mem_iff a t w choices i y

/-- The inverse chaos word constructed from a collision-compatible partition
path has no singleton disorder coordinates. -/
theorem ccr25RunChoicesOfPartitionSequence_noSingleton {h n : ℕ}
    (a : ℕ) (w : Fin h → Site) (I : Fin n → ReplicaPartition h)
    (paths : Fin h → Fin n → Fin 4)
    (hcollision : ∀ k : Fin n,
      IsCollisionConfiguration (I k)
        (fun i => Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1))) :
    ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets a w
        (ccr25RunChoicesOfPartitionSequence I paths)),
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w
        (ccr25RunChoicesOfPartitionSequence I paths)) z ≠ 1 := by
  classical
  intro z hzunion hcount
  obtain ⟨i, _, hzi⟩ := Finset.mem_biUnion.mp hzunion
  unfold ccr25RunReplicaChaosCoordinateSets ccr25ChaosCoordinates at hzi
  obtain ⟨t, ht, hcoord⟩ := Finset.mem_image.mp hzi
  have hcount' : chaosOccurrenceCount
      (ccr25RunReplicaChaosCoordinateSets a w
        (ccr25RunChoicesOfPartitionSequence I paths))
      (a + t, Critical2DKPZ.walkPosition (w i)
        (ccr25RunChoicesOfPartitionSequence I paths i).2 t) = 1 := by
    rw [hcoord]
    exact hcount
  have hpathsI : (ccr25RunChoicesOfPartitionSequence I paths i).2 = paths i := rfl
  rw [hpathsI] at hcount'
  have htime : ∃ k : Fin n, k.val + 1 = t ∧ InCollisionBlock (I k) i := by
    unfold ccr25RunChoicesOfPartitionSequence at ht
    obtain ⟨k, hk, hval⟩ := Finset.mem_image.mp ht
    exact ⟨k, hval, (Finset.mem_filter.mp hk).2⟩
  obtain ⟨k, hval, hiBlock⟩ := htime
  obtain ⟨j, hji, hij⟩ := hiBlock
  have hjBlock : InCollisionBlock (I k) j := ⟨i, hji.symm, (I k).symm' hij⟩
  have hjActive : t ∈
      (ccr25RunChoicesOfPartitionSequence I paths j).1 := by
    rw [← hval]
    exact (ccr25RunChoicesOfPartitionSequence_active_iff I paths j k).2 hjBlock
  have hpos : Critical2DKPZ.walkPosition (w j) (paths j) t =
      Critical2DKPZ.walkPosition (w i) (paths i) t := by
    rw [← hval]
    exact ((hcollision k).1 i j hij).symm
  have hjcoord : (a + t, Critical2DKPZ.walkPosition (w i)
      (ccr25RunChoicesOfPartitionSequence I paths i).2 t) ∈
      ccr25RunReplicaChaosCoordinateSets a w
        (ccr25RunChoicesOfPartitionSequence I paths) j := by
    rw [hpathsI]
    exact (ccr25RunChaosCoordinates_mem_iff a t w
      (ccr25RunChoicesOfPartitionSequence I paths) j
      (Critical2DKPZ.walkPosition (w i) (paths i) t)).2 ⟨hjActive, hpos⟩
  have hcountEq := ccr25RunChaosOccurrenceCount_eq_card a t w
    (ccr25RunChoicesOfPartitionSequence I paths)
    (Critical2DKPZ.walkPosition (w i) (paths i) t)
  have hcountOne : (Finset.univ.filter fun l : Fin h =>
      t ∈ (ccr25RunChoicesOfPartitionSequence I paths l).1 ∧
        Critical2DKPZ.walkPosition (w l) (paths l) t =
          Critical2DKPZ.walkPosition (w i) (paths i) t).card = 1 := by
    rw [hcountEq] at hcount'
    simpa [ccr25RunChoicesOfPartitionSequence] using hcount'
  have hiMember : i ∈ Finset.univ.filter (fun l : Fin h =>
      t ∈ (ccr25RunChoicesOfPartitionSequence I paths l).1 ∧
        Critical2DKPZ.walkPosition (w l) (paths l) t =
          Critical2DKPZ.walkPosition (w i) (paths i) t) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, rfl⟩
  have hjMember : j ∈ Finset.univ.filter (fun l : Fin h =>
      t ∈ (ccr25RunChoicesOfPartitionSequence I paths l).1 ∧
        Critical2DKPZ.walkPosition (w l) (paths l) t =
          Critical2DKPZ.walkPosition (w i) (paths i) t) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjActive, hpos⟩
  have hcardle := (Finset.card_le_one).mp (by omega :
      (Finset.univ.filter fun l : Fin h =>
        t ∈ (ccr25RunChoicesOfPartitionSequence I paths l).1 ∧
          Critical2DKPZ.walkPosition (w l) (paths l) t =
            Critical2DKPZ.walkPosition (w i) (paths i) t).card ≤ 1)
  have heq := hcardle i hiMember j hjMember
  exact hji (heq.symm)


/-- For an active representative, its block size at one time is exactly the
disorder-coordinate multiplicity at the representative's site. -/
theorem ccr25RunTimePartition_blockSize_eq_occurrenceCount {h n : ℕ}
    (a t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) (r : Fin h)
    (hrActive : t ∈ (choices r).1) :
    replicaBlockSize (ccr25RunTimePartition t w choices) r =
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices)
        (a + t, Critical2DKPZ.walkPosition (w r) (choices r).2 t) := by
  have hrel (j : Fin h) :
      (ccr25RunTimePartition t w choices).r r j ↔
        (a + t, Critical2DKPZ.walkPosition (w r) (choices r).2 t) ∈
          ccr25RunReplicaChaosCoordinateSets a w choices j := by
    rw [ccr25RunChaosCoordinates_mem_iff]
    constructor
    · intro h
      rcases h with rfl | ⟨_, hjActive, hpos⟩
      · exact ⟨hrActive, rfl⟩
      · exact ⟨hjActive, hpos.symm⟩
    · rintro ⟨hjActive, hpos⟩
      by_cases hrj : r = j
      · subst j
        exact Or.inl rfl
      · exact Or.inr ⟨hrActive, hjActive, hpos.symm⟩
  unfold replicaBlockSize chaosOccurrenceCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hrel j

/-- The spatial coordinates of the nonsingleton blocks at one selected time,
indexed through their least-label representatives. -/
def ccr25RunCollisionSites {h n : ℕ} (t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) : Finset Site :=
  (ccr25NontrivialBlockRepresentatives (ccr25RunTimePartition t w choices)).image
    (fun i => Critical2DKPZ.walkPosition (w i) (choices i).2 t)

/-- At a fixed time, the product of coordinate moments over distinct
nonsingleton collision sites is the partition disorder moment. -/
theorem replicaPartitionDisorderMoment_eq_prod_runCollisionSites {h n : ℕ}
    (β : ℝ) (a t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) :
    replicaPartitionDisorderMoment β (ccr25RunTimePartition t w choices) =
      ∏ y ∈ ccr25RunCollisionSites t w choices,
        gaussianDisorderMoment β
          (chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices)
            (a + t, y)) := by
  classical
  let I := ccr25RunTimePartition t w choices
  let R := ccr25NontrivialBlockRepresentatives I
  let pos : Fin h → Site := fun i =>
    Critical2DKPZ.walkPosition (w i) (choices i).2 t
  have hactive (r : Fin h) (hr : r ∈ R) : t ∈ (choices r).1 := by
    have hrep : r ∈ replicaBlockRepresentatives I :=
      (Finset.mem_filter.mp hr).1
    have hsize : 2 ≤ replicaBlockSize I r :=
      (Finset.mem_filter.mp hr).2
    have hrclass : r ∈ Finset.univ.filter (fun j : Fin h => I.r r j) := by
      simp
    have hrclassCard : (Finset.univ.filter (fun j : Fin h => I.r r j)).card =
        replicaBlockSize I r := rfl
    have hother : 0 < ((Finset.univ.filter (fun j : Fin h => I.r r j)).erase r).card := by
      rw [Finset.card_erase_of_mem hrclass, hrclassCard]
      omega
    obtain ⟨j, hj⟩ := Finset.card_pos.mp hother
    have hji : j ≠ r := (Finset.mem_erase.mp hj).1
    have hjrel : I.r r j := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
    have hblock : InCollisionBlock I r := ⟨j, hji, hjrel⟩
    exact ((ccr25RunTimePartition_inCollisionBlock_iff t w choices r).1 hblock).1
  have hinj : Set.InjOn pos R := by
    intro r hr s hs hpos
    have hrActive := hactive r hr
    have hsActive := hactive s hs
    have hrs : I.r r s := by
      change r = s ∨
        (t ∈ (choices r).1 ∧ t ∈ (choices s).1 ∧ pos r = pos s)
      exact Or.inr ⟨hrActive, hsActive, hpos⟩
    have hrrep : r ∈ replicaBlockRepresentatives I :=
      (Finset.mem_filter.mp hr).1
    have hrleast : ∀ j, I.r r j → r ≤ j := by
      exact (Finset.mem_filter.mp hrrep).2
    have hsrep : s ∈ replicaBlockRepresentatives I :=
      (Finset.mem_filter.mp hs).1
    have hsleast : ∀ j, I.r s j → s ≤ j := by
      exact (Finset.mem_filter.mp hsrep).2
    exact le_antisymm (hrleast s hrs) (hsleast r (I.symm' hrs))
  have hmoment : replicaPartitionDisorderMoment β I =
      ∏ r ∈ R, gaussianDisorderMoment β (replicaBlockSize I r) := by
    simp [replicaPartitionDisorderMoment, R, ccr25NontrivialBlockRepresentatives,
      Finset.prod_filter]
  rw [hmoment]
  rw [show ccr25RunCollisionSites t w choices = R.image pos from rfl,
    Finset.prod_image hinj]
  apply Finset.prod_congr rfl
  intro r hr
  rw [ccr25RunTimePartition_blockSize_eq_occurrenceCount a t w choices r
    (hactive r hr)]

/-- Disorder coordinates selected at one time by a finite chaos word. -/
def ccr25RunTimeCoordinates {h n : ℕ} (a t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) : Finset (ℕ × Site) :=
  (Finset.univ.filter fun i : Fin h => t ∈ (choices i).1).image
    (fun i => (a + t, Critical2DKPZ.walkPosition (w i) (choices i).2 t))

/-- Chaos words with no singleton disorder coordinate. -/
def ccr25RunGoodChaosChoices {h : ℕ} (n : ℕ) (a : ℕ) (w : Fin h → Site) :
    Finset (Fin h → Finset ℕ × (Fin n → Fin 4)) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin h => ccr25CenteredChaosIndices n)).filter
    (fun choices => ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets a w choices),
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1)

/-- Every member of a nontrivial partition block has block size at least two,
including when the supplied related label is not the representative. -/
theorem ccr25RunReplicaBlockSize_ge_two {h : ℕ} (I : ReplicaPartition h)
    (r i : Fin h) (hri : I.r r i) (hi : InCollisionBlock I i) :
    2 ≤ replicaBlockSize I r := by
  classical
  obtain ⟨j, hji, hij⟩ := hi
  have hrj : I.r r j := I.trans hri hij
  have hsubset : ({i, j} : Finset (Fin h)) ⊆ ccr25ReplicaBlockLabels I r := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hri⟩
    · simp only [Finset.mem_singleton] at hx
      subst x
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrj⟩
  have hcard := Finset.card_le_card hsubset
  have hpair : ({i, j} : Finset (Fin h)).card = 2 := by
    simp [Ne.symm hji]
  have hblock : 2 ≤ (ccr25ReplicaBlockLabels I r).card := by
    rw [← hpair]
    exact hcard
  simpa [ccr25ReplicaBlockLabels, replicaBlockSize] using hblock

/-- The least representative of a nontrivial block is active at its time. -/
theorem ccr25RunTimePartition_nontrivialRepresentative_active {h n : ℕ}
    (t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) (r : Fin h)
    (hr : r ∈ ccr25NontrivialBlockRepresentatives
      (ccr25RunTimePartition t w choices)) :
    t ∈ (choices r).1 := by
  classical
  let I := ccr25RunTimePartition t w choices
  have hsize : 2 ≤ replicaBlockSize I r := (Finset.mem_filter.mp hr).2
  have hrclass : r ∈ Finset.univ.filter (fun j : Fin h => I.r r j) := by simp
  have hclassCard : (Finset.univ.filter (fun j : Fin h => I.r r j)).card =
      replicaBlockSize I r := rfl
  have hother : 0 < ((Finset.univ.filter (fun j : Fin h => I.r r j)).erase r).card := by
    rw [Finset.card_erase_of_mem hrclass, hclassCard]
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hother
  have hji : j ≠ r := (Finset.mem_erase.mp hj).1
  have hjrel : I.r r j := (Finset.mem_filter.mp (Finset.mem_erase.mp hj).2).2
  have hblock : InCollisionBlock I r := ⟨j, hji, hjrel⟩
  exact ((ccr25RunTimePartition_inCollisionBlock_iff t w choices r).1 hblock).1

/-- The selected time coordinates coincide with the coordinates of the
nonsingleton blocks when singleton disorder coordinates are excluded. -/
theorem ccr25RunTimeCoordinates_eq_collisionCoordinates {h n : ℕ}
    (a t : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hnoSingleton : ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets a w choices),
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1) :
    ccr25RunTimeCoordinates a t w choices =
      (ccr25RunCollisionSites t w choices).image (fun y => (a + t, y)) := by
  classical
  let I := ccr25RunTimePartition t w choices
  let pos : Fin h → Site := fun i =>
    Critical2DKPZ.walkPosition (w i) (choices i).2 t
  ext z
  constructor
  · intro hz
    unfold ccr25RunTimeCoordinates at hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_image.mp hz
    have hactive : t ∈ (choices i).1 := (Finset.mem_filter.mp hi).2
    have hblock := (ccr25RunTimePartition_active_iff_inCollisionBlock
      a t w choices hnoSingleton i).1 hactive
    obtain ⟨r, hr, hri⟩ := exists_replicaBlockRepresentative I i
    have hsize := ccr25RunReplicaBlockSize_ge_two I r i hri hblock
    have hr' : r ∈ ccr25NontrivialBlockRepresentatives I :=
      Finset.mem_filter.mpr ⟨hr, hsize⟩
    have hpos : pos r = pos i := by
      change r = i ∨
        (t ∈ (choices r).1 ∧ t ∈ (choices i).1 ∧ pos r = pos i) at hri
      rcases hri with hEq | ⟨_, _, hEq⟩
      · simp [hEq]
      · exact hEq
    unfold ccr25RunCollisionSites
    apply Finset.mem_image.mpr
    refine ⟨pos r, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨r, hr', rfl⟩
    · have hzi' : (a + t, pos i) = z := by simpa [pos] using hzi
      calc
        (a + t, pos r) = (a + t, pos i) := congrArg (fun y => (a + t, y)) hpos
        _ = z := hzi'
  · intro hz
    unfold ccr25RunCollisionSites at hz
    obtain ⟨y, hy, hzy⟩ := Finset.mem_image.mp hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hy
    have hactive := ccr25RunTimePartition_nontrivialRepresentative_active t w choices r hr
    unfold ccr25RunTimeCoordinates
    apply Finset.mem_image.mpr
    refine ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hactive⟩, ?_⟩
    simp [hzy]

/-- The occurrence union of a valid centered chaos word is the disjoint union
of its selected space-time coordinates, indexed by times `1, …, n`. -/
theorem chaosOccurrenceUnion_eq_biUnion_runTimeCoordinates {h n : ℕ}
    (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hchoices : choices ∈ Fintype.piFinset
      (fun _ : Fin h => ccr25CenteredChaosIndices n)) :
    chaosOccurrenceUnion (ccr25RunReplicaChaosCoordinateSets a w choices) =
      (Finset.Icc 1 n).biUnion (ccr25RunTimeCoordinates a · w choices) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    have hci : choices i ∈ ccr25CenteredChaosIndices n :=
      Fintype.mem_piFinset.mp hchoices i
    have hcpair : choices i ∈ ccr25NonemptyChaosSubsets n ×ˢ Finset.univ := by
      simpa [ccr25CenteredChaosIndices] using hci
    have hsubsetMem : (choices i).1 ∈ ccr25NonemptyChaosSubsets n :=
      (Finset.mem_product.mp hcpair).1
    have hsubsetPow : (choices i).1 ∈ Finset.powerset (Finset.Icc 1 n) :=
      (Finset.mem_erase.mp (by simpa [ccr25NonemptyChaosSubsets] using hsubsetMem)).2
    unfold ccr25RunReplicaChaosCoordinateSets ccr25ChaosCoordinates at hzi
    obtain ⟨t, ht, hcoord⟩ := Finset.mem_image.mp hzi
    have htIcc : t ∈ Finset.Icc 1 n := Finset.mem_powerset.mp hsubsetPow ht
    refine Finset.mem_biUnion.mpr ⟨t, htIcc, ?_⟩
    unfold ccr25RunTimeCoordinates
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩
    exact hcoord
  · intro hz
    obtain ⟨t, ht, hzt⟩ := Finset.mem_biUnion.mp hz
    unfold ccr25RunTimeCoordinates at hzt
    obtain ⟨i, hi, hcoord⟩ := Finset.mem_image.mp hzt
    have hzi : (a + t, Critical2DKPZ.walkPosition (w i) (choices i).2 t) ∈
        ccr25RunReplicaChaosCoordinateSets a w choices i :=
      (ccr25RunChaosCoordinates_mem_iff a t w choices i
        (Critical2DKPZ.walkPosition (w i) (choices i).2 t)).2
          ⟨(Finset.mem_filter.mp hi).2, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    simpa [hcoord] using hzi

/-- A nonzero mixed chaos word factors into the disorder moments of its
time-indexed collision partitions. -/
theorem ccr25RunChaosWordMomentWeight_eq_partitionProduct {h n : ℕ}
    (β : ℝ) (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hchoices : choices ∈ Fintype.piFinset
      (fun _ : Fin h => ccr25CenteredChaosIndices n))
    (hnoSingleton : ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets a w choices),
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1) :
    ∏ z ∈ chaosOccurrenceUnion (ccr25RunReplicaChaosCoordinateSets a w choices),
        gaussianDisorderMoment β
          (chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z) =
      ∏ t ∈ Finset.Icc 1 n,
        replicaPartitionDisorderMoment β (ccr25RunTimePartition t w choices) := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 n))
      (ccr25RunTimeCoordinates a · w choices) := by
    intro t ht u hu htu
    apply Finset.disjoint_left.mpr
    intro z hzt hzu
    unfold ccr25RunTimeCoordinates at hzt hzu
    obtain ⟨i, _, hleft⟩ := Finset.mem_image.mp hzt
    obtain ⟨j, _, hright⟩ := Finset.mem_image.mp hzu
    have htime : a + t = a + u := by
      calc
        a + t = z.1 := congrArg Prod.fst hleft
        _ = a + u := (congrArg Prod.fst hright).symm
    exact htu (Nat.add_left_cancel htime)
  rw [chaosOccurrenceUnion_eq_biUnion_runTimeCoordinates a w choices hchoices,
    Finset.prod_biUnion hdisj]
  apply Finset.prod_congr rfl
  intro t ht
  have hcoordInj : Set.InjOn (fun y : Site => (a + t, y))
      (ccr25RunCollisionSites t w choices) := by
    intro x hx y hy hxy
    exact congrArg Prod.snd hxy
  rw [ccr25RunTimeCoordinates_eq_collisionCoordinates a t w choices hnoSingleton,
    Finset.prod_image hcoordInj]
  exact (replicaPartitionDisorderMoment_eq_prod_runCollisionSites β a t w choices).symm

/-- A singleton disorder coordinate annihilates a mixed-start chaos word. -/
theorem ccr25RunChaosWordMomentWeight_eq_zero_of_singleton {h n : ℕ}
    (β : ℝ) (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (z : ℕ × Site)
    (hz : z ∈ chaosOccurrenceUnion (ccr25RunReplicaChaosCoordinateSets a w choices))
    (hcount : chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z = 1) :
    ∏ z ∈ chaosOccurrenceUnion (ccr25RunReplicaChaosCoordinateSets a w choices),
      gaussianDisorderMoment β
        (chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z) = 0 := by
  exact Finset.prod_eq_zero hz (by
    rw [hcount]
    exact gaussianDisorderMoment_one_eq_zero β)

/-- The mixed-start centered product is the finite sum over the nonzero
collision-partition words. -/
theorem integral_prod_centeredPointToPlane_eq_goodChaosPartitionSum {h n : ℕ}
    (β : ℝ) (a : ℕ) (w : Fin h → Site) :
    ∫ ω : Disorder,
        (∏ i : Fin h,
          (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) ∂disorderLaw =
      ((4 : ℝ)⁻¹ ^ n) ^ h *
        ∑ choices ∈ ccr25RunGoodChaosChoices n a w,
          ∏ t ∈ Finset.Icc 1 n,
            replicaPartitionDisorderMoment β (ccr25RunTimePartition t w choices) := by
  classical
  let base := Fintype.piFinset (fun _ : Fin h => ccr25CenteredChaosIndices n)
  let weight := fun choices : Fin h → Finset ℕ × (Fin n → Fin 4) =>
    ∏ z ∈ chaosOccurrenceUnion (ccr25RunReplicaChaosCoordinateSets a w choices),
      gaussianDisorderMoment β
        (chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z)
  let partitionWeight := fun choices : Fin h → Finset ℕ × (Fin n → Fin 4) =>
    ∏ t ∈ Finset.Icc 1 n,
      replicaPartitionDisorderMoment β (ccr25RunTimePartition t w choices)
  have hsum : (∑ choices ∈ base, weight choices) =
      ∑ choices ∈ ccr25RunGoodChaosChoices n a w, partitionWeight choices := by
    have hzeroOutside : ∀ choices ∈ base,
        (if choices ∈ ccr25RunGoodChaosChoices n a w then weight choices else 0) =
          weight choices := by
      intro choices hchoices
      by_cases hg : choices ∈ ccr25RunGoodChaosChoices n a w
      · simp [hg]
      · have hbad : ¬ ∀ z ∈ chaosOccurrenceUnion
          (ccr25RunReplicaChaosCoordinateSets a w choices),
            chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1 := by
          intro hgood
          exact hg (Finset.mem_filter.mpr ⟨hchoices, hgood⟩)
        push Not at hbad
        obtain ⟨z, hz, hcount⟩ := hbad
        have hzero := ccr25RunChaosWordMomentWeight_eq_zero_of_singleton
          β a w choices z hz hcount
        simp [hg, weight, hzero]
    calc
      _ = ∑ choices ∈ base,
          (if choices ∈ ccr25RunGoodChaosChoices n a w then weight choices else 0) := by
        apply Finset.sum_congr rfl
        intro choices hchoices
        exact (hzeroOutside choices hchoices).symm
      _ = ∑ choices ∈ ccr25RunGoodChaosChoices n a w, weight choices := by
        rw [← Finset.sum_filter]
        have hfilter : base.filter
            (fun choices => choices ∈ ccr25RunGoodChaosChoices n a w) =
            ccr25RunGoodChaosChoices n a w := by
          ext choices
          simp only [Finset.mem_filter]
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨(Finset.mem_filter.mp h).1, h⟩
        rw [hfilter]
      _ = ∑ choices ∈ ccr25RunGoodChaosChoices n a w, partitionWeight choices := by
        apply Finset.sum_congr rfl
        intro choices hchoices
        have hvalid : choices ∈ base := (Finset.mem_filter.mp hchoices).1
        have hgood : ∀ z ∈ chaosOccurrenceUnion
            (ccr25RunReplicaChaosCoordinateSets a w choices),
            chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1 :=
          (Finset.mem_filter.mp hchoices).2
        exact ccr25RunChaosWordMomentWeight_eq_partitionProduct β a w choices
          hvalid hgood
  rw [integral_prod_centeredPointToPlane_eq_chaosExpansion]
  dsimp [base, weight, partitionWeight] at hsum ⊢
  rw [hsum]

/-- If a valid centered chaos word has no singleton disorder coordinate, each
replica is in a nontrivial collision block at one of its selected times. -/
theorem ccr25RunTimePartition_fullSupport_of_noSingleton {h n : ℕ}
    (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hchoices : choices ∈ Fintype.piFinset
      (fun _ : Fin h => ccr25CenteredChaosIndices n))
    (hnoSingleton : ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets a w choices),
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1) :
    ∀ i : Fin h, ∃ t ∈ (choices i).1,
      InCollisionBlock (ccr25RunTimePartition t w choices) i := by
  intro i
  have hchoice : choices i ∈ ccr25CenteredChaosIndices n :=
    Fintype.mem_piFinset.mp hchoices i
  have hprod : choices i ∈ ccr25NonemptyChaosSubsets n ×ˢ Finset.univ := by
    simpa [ccr25CenteredChaosIndices] using hchoice
  have hsubset : (choices i).1 ∈ ccr25NonemptyChaosSubsets n :=
    (Finset.mem_product.mp hprod).1
  have hsubsetNe : (choices i).1 ≠ ∅ := by
    have hmem : (choices i).1 ∈
        (Finset.powerset (Finset.Icc 1 n)).erase ∅ := by
      simpa [ccr25NonemptyChaosSubsets] using hsubset
    exact (Finset.mem_erase.mp hmem).1
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.mpr hsubsetNe
  have hblock := (ccr25RunTimePartition_active_iff_inCollisionBlock
    a t w choices hnoSingleton i).1 ht
  exact ⟨t, ht, hblock⟩

/-- The partition sequence associated to a nonzero chaos word has full
support in the finite-sequence convention of CCR25. -/
theorem ccr25RunTimePartitionSequence_mem_fullSupport {h n : ℕ}
    (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hgood : choices ∈ ccr25RunGoodChaosChoices n a w) :
    ccr25RunTimePartitionSequence w choices ∈ fullSupportSequences h n := by
  classical
  have hchoices : choices ∈ Fintype.piFinset
      (fun _ : Fin h => ccr25CenteredChaosIndices n) :=
    (Finset.mem_filter.mp hgood).1
  have hnoSingleton : ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets a w choices),
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1 :=
    (Finset.mem_filter.mp hgood).2
  have hfull := ccr25RunTimePartition_fullSupport_of_noSingleton
    a w choices hchoices hnoSingleton
  unfold fullSupportSequences
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i
  obtain ⟨t, ht, hblock⟩ := hfull i
  have hchoice : choices i ∈ ccr25CenteredChaosIndices n :=
    Fintype.mem_piFinset.mp hchoices i
  have hprod : choices i ∈ ccr25NonemptyChaosSubsets n ×ˢ Finset.univ := by
    simpa [ccr25CenteredChaosIndices] using hchoice
  have hsubset : (choices i).1 ∈ ccr25NonemptyChaosSubsets n :=
    (Finset.mem_product.mp hprod).1
  have hsubsetPow : (choices i).1 ∈ Finset.powerset (Finset.Icc 1 n) :=
    (Finset.mem_erase.mp (by simpa [ccr25NonemptyChaosSubsets] using hsubset)).2
  have htIcc : t ∈ Finset.Icc 1 n := Finset.mem_powerset.mp hsubsetPow ht
  have htBounds := Finset.mem_Icc.mp htIcc
  let k : Fin n := ⟨t - 1, by omega⟩
  have hk : k.val + 1 = t := by simp [k]; omega
  refine ⟨k, ?_⟩
  simpa [ccr25RunTimePartitionSequence, hk] using hblock

/-- Reconstructing the chaos subsets from the induced full-support partition
sequence returns every good chaos word exactly. -/
theorem ccr25RunChoicesOfPartitionSequence_timePartitionSequence_eq {h n : ℕ}
    (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hgood : choices ∈ ccr25RunGoodChaosChoices n a w) :
    ccr25RunChoicesOfPartitionSequence
      (ccr25RunTimePartitionSequence w choices)
      (fun i => (choices i).2) = choices := by
  classical
  have hchoices : choices ∈ Fintype.piFinset
      (fun _ : Fin h => ccr25CenteredChaosIndices n) :=
    (Finset.mem_filter.mp hgood).1
  have hnoSingleton : ∀ z ∈ chaosOccurrenceUnion
      (ccr25RunReplicaChaosCoordinateSets a w choices),
      chaosOccurrenceCount (ccr25RunReplicaChaosCoordinateSets a w choices) z ≠ 1 :=
    (Finset.mem_filter.mp hgood).2
  funext i
  apply Prod.ext
  · have hsubsetValid : (choices i).1 ∈ Finset.powerset (Finset.Icc 1 n) := by
      have hci : choices i ∈ ccr25CenteredChaosIndices n :=
        Fintype.mem_piFinset.mp hchoices i
      have hcpair : choices i ∈ ccr25NonemptyChaosSubsets n ×ˢ Finset.univ := by
        simpa [ccr25CenteredChaosIndices] using hci
      have hcnonempty : (choices i).1 ∈ ccr25NonemptyChaosSubsets n :=
        (Finset.mem_product.mp hcpair).1
      exact (Finset.mem_erase.mp
        (by simpa [ccr25NonemptyChaosSubsets] using hcnonempty)).2
    ext t
    constructor
    · intro ht
      unfold ccr25RunChoicesOfPartitionSequence at ht
      obtain ⟨k, hk, hval⟩ := Finset.mem_image.mp ht
      have hblock : InCollisionBlock
          (ccr25RunTimePartitionSequence w choices k) i :=
        (Finset.mem_filter.mp hk).2
      have hblock' : InCollisionBlock
          (ccr25RunTimePartition k.val.succ w choices) i := by
        simpa [ccr25RunTimePartitionSequence] using hblock
      have hselected := (ccr25RunTimePartition_active_iff_inCollisionBlock
        a k.val.succ w choices hnoSingleton i).2 hblock'
      rw [← hval]
      exact hselected
    · intro ht
      have htIcc : t ∈ Finset.Icc 1 n := Finset.mem_powerset.mp hsubsetValid ht
      have htBounds := Finset.mem_Icc.mp htIcc
      let k : Fin n := ⟨t - 1, by omega⟩
      have hk : k.val + 1 = t := by simp [k]; omega
      have hblock := (ccr25RunTimePartition_active_iff_inCollisionBlock
        a t w choices hnoSingleton i).1 ht
      unfold ccr25RunChoicesOfPartitionSequence
      simp only [Finset.mem_image]
      refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simpa [ccr25RunTimePartitionSequence, hk] using hblock
      · exact hk
  · rfl

/-- Full direction families whose configurations realize a prescribed
time-indexed collision sequence. -/
def ccr25RunCompatiblePathFamilies {h n : ℕ} (w : Fin h → Site)
    (I : Fin n → ReplicaPartition h) : Finset (Fin h → Fin n → Fin 4) := by
  classical
  exact Finset.univ.filter fun paths => ∀ k : Fin n,
    IsCollisionConfiguration (I k)
      (fun i => Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1))

/-- The zero-one weight of a replica direction family under a prescribed
collision sequence. -/
def ccr25RunPathCollisionWeight {h n : ℕ} (w : Fin h → Site)
    (I : Fin n → ReplicaPartition h) (paths : Fin h → Fin n → Fin 4) : ℝ := by
  classical
  exact ∏ k : Fin n, collisionIndicator (I k)
    (fun i => Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1))

/-- The path collision weight is one exactly on the compatible direction
families and zero on all other families. -/
theorem ccr25RunPathCollisionWeight_eq_ite_mem {h n : ℕ}
    (w : Fin h → Site) (I : Fin n → ReplicaPartition h)
    (paths : Fin h → Fin n → Fin 4) :
    ccr25RunPathCollisionWeight w I paths =
      if paths ∈ ccr25RunCompatiblePathFamilies w I then 1 else 0 := by
  classical
  by_cases hp : ∀ k : Fin n,
      IsCollisionConfiguration (I k)
        (fun i => Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1))
  · simp [ccr25RunPathCollisionWeight, ccr25RunCompatiblePathFamilies,
      collisionIndicator, hp]
  · have hbad : ∃ k : Fin n,
        ¬ IsCollisionConfiguration (I k)
          (fun i => Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1)) :=
      not_forall.mp hp
    obtain ⟨k, hk⟩ := hbad
    have hzero : collisionIndicator (I k)
        (fun i => Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1)) = 0 := by
      simp [collisionIndicator, hk]
    simp only [ccr25RunPathCollisionWeight]
    rw [Finset.prod_eq_zero (Finset.mem_univ k) hzero]
    simp [ccr25RunCompatiblePathFamilies, hp]

/-- Summing a constant over compatible paths equals the weighted sum over all
direction families. -/
theorem ccr25RunCompatiblePaths_sum_const_eq_weightedSum {h n : ℕ}
    (w : Fin h → Site) (I : Fin n → ReplicaPartition h) (c : ℝ) :
    (∑ _paths ∈ ccr25RunCompatiblePathFamilies w I, c) =
      c * ∑ paths : Fin h → Fin n → Fin 4,
        ccr25RunPathCollisionWeight w I paths := by
  classical
  calc
    _ = ∑ paths : Fin h → Fin n → Fin 4,
        if paths ∈ ccr25RunCompatiblePathFamilies w I then c else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ paths : Fin h → Fin n → Fin 4,
        c * ccr25RunPathCollisionWeight w I paths := by
      apply Finset.sum_congr rfl
      intro paths hpaths
      rw [ccr25RunPathCollisionWeight_eq_ite_mem]
      by_cases hp : paths ∈ ccr25RunCompatiblePathFamilies w I <;> simp [hp]
    _ = c * ∑ paths : Fin h → Fin n → Fin 4,
        ccr25RunPathCollisionWeight w I paths := by rw [Finset.mul_sum]

/-- Splitting every replica's direction sequence into its first step and its
remaining steps. -/
def ccr25RunDirectionConsEquiv {h n : ℕ} :
    (Fin h → Fin 4) × (Fin h → Fin n → Fin 4) ≃
      (Fin h → Fin (n + 1) → Fin 4) where
  toFun p := fun i => Fin.cons (p.1 i) (p.2 i)
  invFun paths := (fun i => paths i 0, fun i k => paths i k.succ)
  left_inv := by
    rintro ⟨directions, tails⟩
    apply Prod.ext
    · rfl
    · funext i k
      rfl
  right_inv := by
    intro paths
    funext i k
    cases k using Fin.cases <;> rfl

/-- The path collision weight factors at its first microscopic time. -/
theorem ccr25RunPathCollisionWeight_cons {h n : ℕ}
    (w : Fin h → Site) (I : Fin (n + 1) → ReplicaPartition h)
    (directions : Fin h → Fin 4) (tails : Fin h → Fin n → Fin 4) :
    ccr25RunPathCollisionWeight w I
        (ccr25RunDirectionConsEquiv (directions, tails)) =
      collisionIndicator (I 0)
          (ccr25RunOneStepConfiguration w directions) *
        ccr25RunPathCollisionWeight (ccr25RunOneStepConfiguration w directions)
          (fun k => I k.succ) tails := by
  classical
  have hpaths : ccr25RunDirectionConsEquiv (directions, tails) =
      (fun i => Fin.cons (directions i) (tails i)) := by
    funext i
    rfl
  rw [hpaths]
  simp only [ccr25RunPathCollisionWeight, Fin.prod_univ_succ, Fin.val_zero,
    Nat.zero_add]
  simp only [Critical2DKPZ.Polymer.walkPosition_cons_one]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp only [show k.succ.val + 1 = (k.val + 1) + 1 by simp,
    Critical2DKPZ.Polymer.walkPosition_cons_succ,
    ccr25RunOneStepConfiguration]

/-- The replica path weight is the finite uniform walk average of the
time-ordered collision indicators. -/
theorem replicaPathWeight_listOfFn_eq_directionSum {h n : ℕ}
    (I : Fin n → ReplicaPartition h) (w : LatticeConfiguration h) :
    replicaPathWeight (List.ofFn I) w =
      ((4 : ℝ)⁻¹ ^ h) ^ n *
        ∑ paths : Fin h → Fin n → Fin 4,
          ccr25RunPathCollisionWeight w I paths := by
  classical
  induction n generalizing w with
  | zero =>
      simp [replicaPathWeight, ccr25RunPathCollisionWeight]
  | succ n ih =>
      let Itail : Fin n → ReplicaPartition h := fun k => I k.succ
      let c : ℝ := (4 : ℝ)⁻¹ ^ h
      have hlist : List.ofFn I = I 0 :: List.ofFn Itail := by
        simp [Itail, List.ofFn_succ]
      have hrec : replicaPathWeight (List.ofFn I) w =
          c * ∑ directions : Fin h → Fin 4,
            collisionIndicator (I 0)
                (ccr25RunOneStepConfiguration w directions) *
              replicaPathWeight (List.ofFn Itail)
                (ccr25RunOneStepConfiguration w directions) := by
        rw [hlist, replicaPathWeight, tsum_replicaStepKernel_mul_eq_directionSum]
      calc
        replicaPathWeight (List.ofFn I) w =
            c * ∑ directions : Fin h → Fin 4,
              collisionIndicator (I 0)
                  (ccr25RunOneStepConfiguration w directions) *
                (c ^ n * ∑ tails : Fin h → Fin n → Fin 4,
                  ccr25RunPathCollisionWeight
                    (ccr25RunOneStepConfiguration w directions) Itail tails) := by
          rw [hrec]
          apply congrArg (fun x => c * x)
          apply Finset.sum_congr rfl
          intro directions hdirections
          rw [ih Itail (ccr25RunOneStepConfiguration w directions)]
        _ = c ^ (n + 1) *
              ∑ directions : Fin h → Fin 4,
                ∑ tails : Fin h → Fin n → Fin 4,
                  collisionIndicator (I 0)
                      (ccr25RunOneStepConfiguration w directions) *
                    ccr25RunPathCollisionWeight
                      (ccr25RunOneStepConfiguration w directions) Itail tails := by
          have hsum :
              (∑ directions : Fin h → Fin 4,
                collisionIndicator (I 0)
                    (ccr25RunOneStepConfiguration w directions) *
                  (c ^ n * ∑ tails : Fin h → Fin n → Fin 4,
                    ccr25RunPathCollisionWeight
                      (ccr25RunOneStepConfiguration w directions) Itail tails)) =
                c ^ n *
                  ∑ directions : Fin h → Fin 4,
                    ∑ tails : Fin h → Fin n → Fin 4,
                      collisionIndicator (I 0)
                          (ccr25RunOneStepConfiguration w directions) *
                        ccr25RunPathCollisionWeight
                          (ccr25RunOneStepConfiguration w directions) Itail tails := by
            calc
              _ = ∑ directions : Fin h → Fin 4,
                    c ^ n * ∑ tails : Fin h → Fin n → Fin 4,
                      collisionIndicator (I 0)
                          (ccr25RunOneStepConfiguration w directions) *
                        ccr25RunPathCollisionWeight
                          (ccr25RunOneStepConfiguration w directions) Itail tails := by
                apply Finset.sum_congr rfl
                intro directions hdirections
                calc
                  _ = c ^ n *
                      (collisionIndicator (I 0)
                          (ccr25RunOneStepConfiguration w directions) *
                        ∑ tails : Fin h → Fin n → Fin 4,
                          ccr25RunPathCollisionWeight
                            (ccr25RunOneStepConfiguration w directions) Itail tails) := by
                    ring
                  _ = c ^ n *
                      ∑ tails : Fin h → Fin n → Fin 4,
                        collisionIndicator (I 0)
                            (ccr25RunOneStepConfiguration w directions) *
                          ccr25RunPathCollisionWeight
                            (ccr25RunOneStepConfiguration w directions) Itail tails := by
                    congr 1
                    rw [Finset.mul_sum]
              _ = _ := by rw [Finset.mul_sum]
          rw [hsum, pow_succ]
          ring
        _ = c ^ (n + 1) *
              ∑ paths : Fin h → Fin (n + 1) → Fin 4,
                ccr25RunPathCollisionWeight w I paths := by
          congr 1
          rw [← ccr25RunDirectionConsEquiv.sum_comp, Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro directions hdirections
          apply Finset.sum_congr rfl
          intro tails htails
          simpa [Itail] using
            (ccr25RunPathCollisionWeight_cons w I directions tails).symm

/-- The finite dependent-pair index set for full-support collision partitions
and compatible replica direction families. -/
def ccr25RunGoodPartitionPathPairs {h n : ℕ} (w : Fin h → Site) :=
  (fullSupportSequences h n).sigma (ccr25RunCompatiblePathFamilies w)

/-- A nonzero centered-chaos word determines its collision partitions and its
replica direction family. -/
def ccr25RunChoiceToPartitionPathPair {h n : ℕ} (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) :
    Σ _I : Fin n → ReplicaPartition h, Fin h → Fin n → Fin 4 :=
  ⟨ccr25RunTimePartitionSequence w choices, fun i => (choices i).2⟩

/-- A full-support collision sequence and compatible direction family
reconstruct the unique centered-chaos word. -/
def ccr25RunPartitionPathPairToChoice {h n : ℕ}
    (pair : Σ _I : Fin n → ReplicaPartition h, Fin h → Fin n → Fin 4) :
    Fin h → Finset ℕ × (Fin n → Fin 4) :=
  ccr25RunChoicesOfPartitionSequence pair.1 pair.2

/-- Every nonzero chaos word maps to a full-support compatible partition-path
pair. -/
theorem ccr25RunChoiceToPartitionPathPair_mem {h n : ℕ} (a : ℕ)
    (w : Fin h → Site) (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hgood : choices ∈ ccr25RunGoodChaosChoices n a w) :
    ccr25RunChoiceToPartitionPathPair w choices ∈
      ccr25RunGoodPartitionPathPairs w := by
  classical
  apply Finset.mem_sigma.mpr
  refine ⟨ccr25RunTimePartitionSequence_mem_fullSupport a w choices hgood, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro k
  simpa [ccr25RunTimePartitionSequence, ccr25RunChoiceToPartitionPathPair] using
    ccr25RunTimePartition_path_isCollisionConfiguration (k.val + 1) w choices

/-- Reconstructing a valid partition-path pair produces a nonzero centered
chaos word. -/
theorem ccr25RunPartitionPathPairToChoice_mem {h n : ℕ} (a : ℕ)
    (w : Fin h → Site) (pair : Σ _I : Fin n → ReplicaPartition h, Fin h → Fin n → Fin 4)
    (hpair : pair ∈ ccr25RunGoodPartitionPathPairs w) :
    ccr25RunPartitionPathPairToChoice pair ∈ ccr25RunGoodChaosChoices n a w := by
  classical
  have hp := Finset.mem_sigma.mp hpair
  have hvalid := ccr25RunChoicesOfPartitionSequence_mem_piFinset
    pair.1 pair.2 hp.1
  have hnoSingleton := ccr25RunChoicesOfPartitionSequence_noSingleton
    a w pair.1 pair.2 (Finset.mem_filter.mp hp.2).2
  exact Finset.mem_filter.mpr ⟨hvalid, hnoSingleton⟩

/-- The two reconstructions are inverse on full-support compatible paths. -/
theorem ccr25RunChoiceToPartitionPathPair_partitionPathPairToChoice {h n : ℕ}
    (w : Fin h → Site)
    (pair : Σ _I : Fin n → ReplicaPartition h, Fin h → Fin n → Fin 4)
    (hpair : pair ∈ ccr25RunGoodPartitionPathPairs w) :
    ccr25RunChoiceToPartitionPathPair w
      (ccr25RunPartitionPathPairToChoice pair) = pair := by
  rcases pair with ⟨I, paths⟩
  classical
  have hcollision : ∀ k : Fin n,
      IsCollisionConfiguration (I k)
        (fun i => Critical2DKPZ.walkPosition (w i) (paths i) (k.val + 1)) :=
    (Finset.mem_filter.mp (Finset.mem_sigma.mp hpair).2).2
  apply Sigma.ext
  · exact ccr25RunTimePartitionSequence_choicesOf_eq
      w I paths hcollision
  · rfl

/-- The chaos word reconstruction is also inverse on every good word. -/
theorem ccr25RunPartitionPathPairToChoice_choiceToPartitionPathPair {h n : ℕ}
    (a : ℕ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4))
    (hgood : choices ∈ ccr25RunGoodChaosChoices n a w) :
    ccr25RunPartitionPathPairToChoice
      (ccr25RunChoiceToPartitionPathPair w choices) = choices := by
  exact ccr25RunChoicesOfPartitionSequence_timePartitionSequence_eq
    a w choices hgood

/-- Reindexing the finite nonzero chaos-word sum by its collision partition
sequence and compatible direction family. -/
theorem ccr25RunGoodChaosChoices_sum_bij {h n : ℕ} (a : ℕ)
    (w : Fin h → Site)
    (f : (Fin h → Finset ℕ × (Fin n → Fin 4)) → ℝ)
    (g : (Σ _I : Fin n → ReplicaPartition h, Fin h → Fin n → Fin 4) → ℝ)
    (hfg : ∀ choices ∈ ccr25RunGoodChaosChoices n a w,
      f choices = g (ccr25RunChoiceToPartitionPathPair w choices)) :
    (∑ choices ∈ ccr25RunGoodChaosChoices n a w, f choices) =
      ∑ pair ∈ ccr25RunGoodPartitionPathPairs w, g pair := by
  classical
  apply Finset.sum_bij'
    (fun choices _ => ccr25RunChoiceToPartitionPathPair w choices)
    (fun pair _ => ccr25RunPartitionPathPairToChoice pair)
  · intro choices hchoices
    exact ccr25RunChoiceToPartitionPathPair_mem a w choices hchoices
  · intro pair hpair
    exact ccr25RunPartitionPathPairToChoice_mem a w pair hpair
  · intro choices hchoices
    exact ccr25RunPartitionPathPairToChoice_choiceToPartitionPathPair
      a w choices hchoices
  · intro pair hpair
    exact ccr25RunChoiceToPartitionPathPair_partitionPathPairToChoice
      w pair hpair
  · exact hfg

/-- The microscopic-time collision product is the same product over the
zero-based finite partition sequence. -/
theorem ccr25RunTimePartitionMomentProduct_eq_sequenceProduct {h n : ℕ}
    (β : ℝ) (w : Fin h → Site)
    (choices : Fin h → Finset ℕ × (Fin n → Fin 4)) :
    (∏ t ∈ Finset.Icc 1 n,
      replicaPartitionDisorderMoment β (ccr25RunTimePartition t w choices)) =
      ∏ k : Fin n,
        replicaPartitionDisorderMoment β (ccr25RunTimePartitionSequence w choices k) := by
  classical
  apply Finset.prod_bij (fun t ht => ⟨t - 1, by
    have ht' := Finset.mem_Icc.mp ht
    omega⟩)
  · intro t ht
    exact Finset.mem_univ _
  · intro t ht u hu hEq
    have hval := congrArg Fin.val hEq
    have htlo := (Finset.mem_Icc.mp ht).1
    have hulo := (Finset.mem_Icc.mp hu).1
    have hplus := congrArg (fun r : ℕ => r + 1) hval
    simpa [Nat.sub_add_cancel htlo, Nat.sub_add_cancel hulo] using hplus
  · intro k hk
    refine ⟨k.val + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      exact ⟨by omega, by have := k.isLt; omega⟩
    · apply Fin.ext
      simp
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    have hk : (⟨t - 1, by omega⟩ : Fin n).val + 1 = t := by
      change t - 1 + 1 = t
      exact Nat.sub_add_cancel ht'.1
    simp [ccr25RunTimePartitionSequence, hk]

/-- Summing a constant over compatible direction families and then over
full-support partition sequences is the collision-weighted direction sum. -/
theorem ccr25RunGoodPartitionPathPairs_momentSum_eq_weightedPathSum
    {h n : ℕ} (β : ℝ) (w : LatticeConfiguration h) :
    (∑ pair ∈ ccr25RunGoodPartitionPathPairs w,
      ∏ k : Fin n, replicaPartitionDisorderMoment β (pair.1 k)) =
      ∑ I ∈ fullSupportSequences h n,
        (∏ k : Fin n, replicaPartitionDisorderMoment β (I k)) *
          ∑ paths : Fin h → Fin n → Fin 4,
            ccr25RunPathCollisionWeight w I paths := by
  classical
  rw [ccr25RunGoodPartitionPathPairs, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro I hI
  exact ccr25RunCompatiblePaths_sum_const_eq_weightedSum w I
    (∏ k : Fin n, replicaPartitionDisorderMoment β (I k))

/-- The mixed-start centered product expands over full-support collision
partitions, with the constrained walk average represented by
`replicaPathWeight`. -/
theorem integral_prod_pointToPlane_sub_one_eq_partitionSum {h n : ℕ}
    (β : ℝ) (a : ℕ) (w : LatticeConfiguration h) :
    ∫ ω : Disorder,
        (∏ i : Fin h,
          (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) ∂disorderLaw =
      ∑ I ∈ fullSupportSequences h n,
        (∏ k : Fin n, replicaPartitionDisorderMoment β (I k)) *
          replicaPathWeight (List.ofFn I) w := by
  classical
  have hmomentIndex :
      ((4 : ℝ)⁻¹ ^ n) ^ h = ((4 : ℝ)⁻¹ ^ h) ^ n := by
    calc
      _ = (4 : ℝ)⁻¹ ^ (n * h) := by rw [pow_mul]
      _ = (4 : ℝ)⁻¹ ^ (h * n) := by rw [Nat.mul_comm]
      _ = _ := by rw [← pow_mul]
  have hfg : ∀ choices ∈ ccr25RunGoodChaosChoices n a w,
      (∏ t ∈ Finset.Icc 1 n,
        replicaPartitionDisorderMoment β (ccr25RunTimePartition t w choices)) =
        (∏ k : Fin n,
          replicaPartitionDisorderMoment β
            ((ccr25RunChoiceToPartitionPathPair w choices).1 k)) := by
    intro choices hchoices
    rw [ccr25RunTimePartitionMomentProduct_eq_sequenceProduct]
    rfl
  rw [integral_prod_centeredPointToPlane_eq_goodChaosPartitionSum,
    ccr25RunGoodChaosChoices_sum_bij a w
      (fun choices => ∏ t ∈ Finset.Icc 1 n,
        replicaPartitionDisorderMoment β (ccr25RunTimePartition t w choices))
      (fun pair => ∏ k : Fin n,
        replicaPartitionDisorderMoment β (pair.1 k)) hfg,
    ccr25RunGoodPartitionPathPairs_momentSum_eq_weightedPathSum]
  rw [hmomentIndex, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [replicaPathWeight_listOfFn_eq_directionSum]
  ring

/-- The absolute mixed-start integral is bounded by the sum of absolute
partition moments. The integrand is integrable by `Polymer.integrable_pow_pointToPlane`
(expand the product). -/
theorem abs_integral_prod_pointToPlane_sub_one_le_abs_partitionSum {h n : ℕ}
    (β : ℝ) (a : ℕ) (w : LatticeConfiguration h) :
    |∫ ω : Disorder,
        (∏ i : Fin h,
          (Critical2DKPZ.pointToPlane β a n (w i) ω - 1)) ∂disorderLaw| ≤
      ∑ I ∈ fullSupportSequences h n,
        (∏ k : Fin n, |replicaPartitionDisorderMoment β (I k)|) *
          replicaPathWeight (List.ofFn I) w := by
  rw [integral_prod_pointToPlane_sub_one_eq_partitionSum]
  calc
    |∑ I ∈ fullSupportSequences h n,
        (∏ k : Fin n, replicaPartitionDisorderMoment β (I k)) *
          replicaPathWeight (List.ofFn I) w| ≤
      ∑ I ∈ fullSupportSequences h n,
        |(∏ k : Fin n, replicaPartitionDisorderMoment β (I k)) *
          replicaPathWeight (List.ofFn I) w| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ I ∈ fullSupportSequences h n,
        (∏ k : Fin n, |replicaPartitionDisorderMoment β (I k)|) *
          replicaPathWeight (List.ofFn I) w := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [abs_mul, abs_of_nonneg (replicaPathWeight_nonneg _ _), Finset.abs_prod]


/-- Centering a finitely supported start profile expands its `h`-th moment
into a finite sum over independently selected starting sites. -/
theorem centeredMoment_profileP2Fun_eq_sum_starts {h : ℕ}
    (β : ℝ) (L : ℕ) (φ : Site → ℝ) (A : Finset Site)
    (hA : ∀ z ∉ A, φ z = 0) :
    ∫ ω, (Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h
        ∂disorderLaw =
      ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, φ (w i)) *
          ∫ ω, ∏ i : Fin h,
            (Critical2DKPZ.pointToPlane β 0 L (w i) ω - 1) ∂disorderLaw := by
  classical
  let P : Site → Disorder → ℝ := fun z ω =>
    Critical2DKPZ.pointToPlane β 0 L z ω
  have hprofile (ω : Disorder) :
      Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω =
        ∑ z ∈ A, φ z * P z ω := by
    simpa [P, Nat.sub_zero, mul_one, Critical2DKPZ.Polymer.tsum_pointToPoint] using
      Critical2DKPZ.Polymer.profileP2Fun_eq_sum β 0 L φ (fun _ => 1) A hA ω
  have hmean :
      (∫ ω, Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω ∂disorderLaw) =
        ∑ z ∈ A, φ z := by
    rw [Critical2DKPZ.Polymer.integral_profileP2Fun_finset β 0 L φ
      (fun _ => 1) A hA]
    apply Finset.sum_congr rfl
    intro z hz
    simp [mul_one, Critical2DKPZ.Polymer.tsum_srwKernel]
  have hcenter (ω : Disorder) :
      Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw =
        ∑ z ∈ A, φ z * (P z ω - 1) := by
    rw [hprofile ω, hmean]
    calc
      (∑ z ∈ A, φ z * P z ω) - ∑ z ∈ A, φ z =
          ∑ z ∈ A, (φ z * P z ω - φ z) := by rw [Finset.sum_sub_distrib]
      _ = ∑ z ∈ A, φ z * (P z ω - 1) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
  have hpow (ω : Disorder) :
      (Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h =
        ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          ∏ i : Fin h, φ (w i) * (P (w i) ω - 1) := by
    rw [hcenter]
    exact Finset.sum_pow' A (fun z => φ z * (P z ω - 1)) h
  have hfun :
      (fun ω : Disorder =>
        (Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω -
          ∫ ω', Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ h) =
        fun ω => ∑ w ∈ Fintype.piFinset (fun _ : Fin h => A),
          ∏ i : Fin h, φ (w i) *
            (Critical2DKPZ.pointToPlane β 0 L (w i) ω - 1) := by
    funext ω
    simpa [P] using hpow ω
  rw [hfun, integral_finsetSum _ (fun w hw =>
    integrable_prod_scaledCenteredPointToPlane β 0 L φ w)]
  apply Finset.sum_congr rfl
  intro w hw
  have heq :
      (fun ω : Disorder =>
        ∏ i : Fin h, φ (w i) *
          (Critical2DKPZ.pointToPlane β 0 L (w i) ω - 1)) =
      fun ω => (∏ i : Fin h, φ (w i)) *
        (∏ i : Fin h,
          (Critical2DKPZ.pointToPlane β 0 L (w i) ω - 1)) := by
    funext ω
    rw [Finset.prod_mul_distrib]
  rw [heq, integral_const_mul]

end

end Critical2DKPZ.MomentBounds

end
