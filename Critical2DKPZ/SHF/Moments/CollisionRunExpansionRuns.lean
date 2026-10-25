/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionRunExpansion
public import Critical2DKPZ.Collision.SpatialRenewalComposition
import Critical2DKPZ.SHF.Moments.PairBlockLocalLimit
import Critical2DKPZ.MomentBounds.CCR25BlockConfigurationSum
import Mathlib.Tactic

/-! # Markov factorization for maximal collision runs -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose
attribute [local instance] Classical.propDecidable

private theorem pairPartition_representatives_eq {h : ℕ} (α : CollisionPair h) :
    MomentBounds.replicaBlockRepresentatives (MomentBounds.pairPartition α) =
      Finset.univ.erase α.1.2 := by
  classical
  ext i
  simp only [MomentBounds.replicaBlockRepresentatives, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · intro hi
    have hne : i ≠ α.1.2 := by
      intro hEq
      subst i
      have hrel : (MomentBounds.pairPartition α).r α.1.2 α.1.1 := by
        rw [MomentBounds.pairPartition_rel]
        exact Or.inr ⟨Or.inr rfl, Or.inl rfl⟩
      have hle := hi α.1.1 hrel
      exact (not_le_of_gt α.2) hle
    exact ⟨hne, trivial⟩
  · rintro ⟨hne, _⟩
    intro j hrel
    rcases (MomentBounds.pairPartition_rel α i j).mp hrel with hij | ⟨hiPair, hjPair⟩
    · exact hij ▸ le_rfl
    · rcases hiPair with hia | hib
      · subst i
        rcases hjPair with hja | hjb
        · exact hja ▸ le_rfl
        · exact hjb ▸ α.2.le
      · exact (hne hib).elim

private theorem run_pairConfigSum_factor {h : ℕ} (α : CollisionPair h)
    (m d : ℕ) (u v : Fin h → Site) (hu : u α.1.1 = u α.1.2)
    (hv : v α.1.1 = v α.1.2) (U : Site → ℝ)
    (hU : ∀ z, z ∉ Polymer.endpoints 0 m → U z = 0) :
    (∑' z : Fin h → Site,
      (if z α.1.1 = z α.1.2 then (1 : ℝ) else 0) *
        U (z α.1.1 - u α.1.1) *
        (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
          srwKernel m (z i - u i)) *
        ∏ i, srwKernel d (v i - z i)) =
      (∑' w : Site, U (w - u α.1.1) * srwKernel d (v α.1.1 - w) ^ 2) *
        ∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
          srwKernel (m + d) (v i - u i) := by
  classical
  let a := α.1.1
  let b := α.1.2
  let I := MomentBounds.pairPartition α
  let T : Fin h → Finset Site := fun i => Polymer.endpoints (u i) m
  let R : Finset (Fin h → Site) := Fintype.piFinset T
  let E := {i : Fin h // i ∈ MomentBounds.replicaBlockRepresentatives I}
  let f : E → Site → ℝ := fun i w =>
    if i.1 = a then
      U (w - u a) * srwKernel d (v a - w) * srwKernel d (v b - w)
    else srwKernel m (w - u i.1) * srwKernel d (v i.1 - w)
  have hTa : T a = T b := by
    change Polymer.endpoints (u a) m = Polymer.endpoints (u b) m
    rw [hu]
  have hrel_not (w : Site) (hw : w ∉ T a) : w - u a ∉ Polymer.endpoints 0 m := by
    intro hmem
    change w - u a ∈ Finset.univ.image
      (fun p : Fin m → Fin 4 => walkPosition 0 p m) at hmem
    obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hmem
    apply hw
    change w ∈ Finset.univ.image
      (fun p : Fin m → Fin 4 => walkPosition (u a) p m)
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_univ _, ?_⟩
    rw [Polymer.walkPosition_eq_start_add, hp]
    abel
  have hzero (z : Fin h → Site) (hz : z ∉ R) :
      (if z a = z b then (1 : ℝ) else 0) * U (z a - u a) *
        (∏ i, if i = a ∨ i = b then (1 : ℝ) else srwKernel m (z i - u i)) *
        ∏ i, srwKernel d (v i - z i) = 0 := by
    have hmiss : ∃ i, z i ∉ T i := by
      by_contra hn
      apply hz
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hmiss
    by_cases hpair : z a = z b
    · by_cases hipair : i = a ∨ i = b
      · have hza : z a ∉ T a := by
          rcases hipair with rfl | rfl
          · exact hi
          · rw [← hTa] at hi
            simpa [hpair] using hi
        have hUz := hU (z a - u a) (hrel_not (z a) hza)
        simp [hUz]
      · have hkernel : srwKernel m (z i - u i) = 0 := by
          exact Polymer.srwKernel_eq_zero_of_not_mem m (u i) (z i) hi
        have hfactor : (∏ j, if j = a ∨ j = b then (1 : ℝ) else
            srwKernel m (z j - u j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hipair, hkernel])
        simp [hpair, hfactor]
    · simp [hpair]
  have hterm (z : Fin h → Site) (hzb : z a = z b) :
      U (z a - u a) *
          (∏ i, if i = a ∨ i = b then (1 : ℝ) else srwKernel m (z i - u i)) *
          ∏ i, srwKernel d (v i - z i) =
        ∏ i : E, f i (z i.1) := by
    let rest : Finset (Fin h) := (Finset.univ.erase b).erase a
    let qm : Fin h → ℝ := fun i => srwKernel m (z i - u i)
    let qd : Fin h → ℝ := fun i => srwKernel d (v i - z i)
    have hab : a ≠ b := ne_of_lt α.2
    have hrest : (Finset.univ.erase b).erase a = rest := rfl
    have hqm : (∏ i, if i = a ∨ i = b then (1 : ℝ) else qm i) =
        ∏ i ∈ rest, qm i := by
      calc
        _ = ∏ i, if i ∈ rest then qm i else 1 := by
          apply Finset.prod_congr rfl
          intro i _
          by_cases hia : i = a
          · simp [rest, hia]
          · by_cases hib : i = b
            · simp [rest, hib]
            · simp [rest, hia, hib]
        _ = _ := Finset.prod_ite_mem_eq rest qm
    have hqd : (∏ i, qd i) = qd a * qd b * ∏ i ∈ rest, qd i := by
      change (Finset.univ.prod qd) = _
      rw [← Finset.mul_prod_erase Finset.univ qd (by simp : a ∈ Finset.univ)]
      rw [← Finset.mul_prod_erase (Finset.univ.erase a) qd
        (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩)]
      rw [show (Finset.univ.erase a).erase b = rest by
        ext i
        simp [rest, and_comm]]
      ring
    have hqpair : qd b = qd a := by
      change srwKernel d (v b - z b) = srwKernel d (v a - z a)
      rw [show v b = v a from hv.symm, show z b = z a from hzb.symm]
    have hreps := pairPartition_representatives_eq α
    let e : E ≃ {i : Fin h // i ∈ Finset.univ.erase b} := {
      toFun := fun i => ⟨i.1, by
        have hi : i.1 ∈ MomentBounds.replicaBlockRepresentatives
            (MomentBounds.pairPartition α) := by
          change i.1 ∈ MomentBounds.replicaBlockRepresentatives I
          exact i.2
        have hi' : i.1 ∈ Finset.univ.erase b := by
          have heq := congrArg (fun s : Finset (Fin h) => i.1 ∈ s) hreps
          exact heq.mp hi
        simpa [b] using hi'⟩
      invFun := fun i => ⟨i.1, by
        have hi : i.1 ∈ MomentBounds.replicaBlockRepresentatives
            (MomentBounds.pairPartition α) := by
          have heq := congrArg (fun s : Finset (Fin h) => i.1 ∈ s) hreps
          exact heq.mpr i.2
        simpa [I] using hi⟩
      left_inv := by intro i; apply Subtype.ext; rfl
      right_inv := by intro i; apply Subtype.ext; rfl }
    have hconvert :
        (∏ i : E, f i (z i.1)) =
          ∏ i ∈ Finset.univ.erase b,
            (if i = a then U (z a - u a) * qd a * qd b else qm i * qd i) := by
      rw [Fintype.prod_equiv e (fun i : E => f i (z i.1))
        (fun i => if i.1 = a then U (z a - u a) * qd a * qd b else qm i.1 * qd i.1)
        (by intro i
            have he : (e i).1 = i.1 := rfl
            rw [he]
            dsimp only [f, qm, qd]
            split_ifs with hi
            · rw [hi, hzb.symm]
            · rfl)]
      rw [← Finset.prod_subtype (Finset.univ.erase b)
        (fun i => by simp) (fun i => if i = a then
          U (z a - u a) * qd a * qd b else qm i * qd i)]
    rw [hqm, hqd, hqpair]
    rw [hconvert]
    rw [← Finset.mul_prod_erase (Finset.univ.erase b)
      (fun i => if i = a then U (z a - u a) * qd a * qd b else qm i * qd i)
      (Finset.mem_erase.mpr ⟨hab, Finset.mem_univ _⟩)]
    have hrestprod :
        (∏ i ∈ rest,
          if i = a then U (z a - u a) * qd a * qd b else qm i * qd i) =
          ∏ i ∈ rest, qm i * qd i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hia : i ≠ a := (Finset.mem_erase.mp hi).1
      simp [hia]
    have hrestprod' :
        (∏ i ∈ rest, qm i * qd i) = (∏ i ∈ rest, qm i) * ∏ i ∈ rest, qd i := by
      rw [Finset.prod_mul_distrib]
    rw [hrestprod, hrestprod']
    simp only [ite_true]
    rw [show rest = (Finset.univ.erase b).erase a by rfl]
    simp [hqpair]
    ring
  calc
    _ = ∑ z ∈ R,
        (if z a = z b then (1 : ℝ) else 0) * U (z a - u a) *
          (∏ i, if i = a ∨ i = b then (1 : ℝ) else srwKernel m (z i - u i)) *
          ∏ i, srwKernel d (v i - z i) := by
            apply tsum_eq_sum
            intro z hz
            exact hzero z hz
    _ = ∑ z ∈ R.filter (fun z => z a = z b),
        U (z a - u a) *
          (∏ i, if i = a ∨ i = b then (1 : ℝ) else srwKernel m (z i - u i)) *
          ∏ i, srwKernel d (v i - z i) := by
            calc
              _ = ∑ z ∈ R, if z a = z b then
                    U (z a - u a) *
                      (∏ i, if i = a ∨ i = b then (1 : ℝ) else srwKernel m (z i - u i)) *
                      ∏ i, srwKernel d (v i - z i) else 0 := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    by_cases hzab : z a = z b <;> simp [hzab]
              _ = _ := by
                    rw [Finset.sum_filter]
    _ = ∑ z ∈ R.filter (fun z =>
          MomentBounds.IsEqualityConfiguration I z),
        U (z a - u a) *
          (∏ i, if i = a ∨ i = b then (1 : ℝ) else srwKernel m (z i - u i)) *
          ∏ i, srwKernel d (v i - z i) := by
            congr 1
            ext z
            simp [MomentBounds.isEqualityConfiguration_pair_iff, I, a, b]
    _ = ∏ i : E, ∑ w ∈ T i.1, f i w := by
          rw [show R = Fintype.piFinset T by rfl]
          calc
            _ = ∑ z ∈ R.filter (fun z =>
                MomentBounds.IsEqualityConfiguration I z),
                ∏ i : E, f i (z i.1) := by
                  apply Finset.sum_congr rfl
                  intro z hz
                  have hEq := (MomentBounds.isEqualityConfiguration_pair_iff α z).mp
                    (Finset.mem_filter.mp hz).2
                  exact hterm z hEq
            _ = _ := MomentBounds.sum_equalityConfigurations_prod_blocks I u
              ((MomentBounds.isEqualityConfiguration_pair_iff α u).mpr hu) m f
    _ = _ := by
          have hPairSum :
              (∑ w ∈ T a, U (w - u a) * srwKernel d (v a - w) ^ 2) =
                ∑' w : Site, U (w - u a) * srwKernel d (v a - w) ^ 2 := by
            symm
            apply tsum_eq_sum
            intro w hw
            have hw' : w - u a ∉ Polymer.endpoints 0 m := hrel_not w hw
            rw [hU (w - u a) hw', zero_mul]
          have hSpectator (i : Fin h) (hi : i ≠ a) (hib : i ≠ b) :
              (∑ w ∈ T i, srwKernel m (w - u i) * srwKernel d (v i - w)) =
                srwKernel (m + d) (v i - u i) := by
            simpa [T, Polymer.srwKernel_sub_swap] using
              Polymer.kernel_convolution_finset m d (u i) (v i)
          let rest : Finset (Fin h) := (Finset.univ.erase b).erase a
          have hreps := pairPartition_representatives_eq α
          let e : E ≃ {i : Fin h // i ∈ Finset.univ.erase b} := {
            toFun := fun i => ⟨i.1, by
              have hi : i.1 ∈ MomentBounds.replicaBlockRepresentatives
                  (MomentBounds.pairPartition α) := by
                change i.1 ∈ MomentBounds.replicaBlockRepresentatives I
                exact i.2
              have hi' : i.1 ∈ Finset.univ.erase b := by
                have heq := congrArg (fun s : Finset (Fin h) => i.1 ∈ s) hreps
                exact heq.mp hi
              simpa [b] using hi'⟩
            invFun := fun i => ⟨i.1, by
              have hi : i.1 ∈ MomentBounds.replicaBlockRepresentatives
                  (MomentBounds.pairPartition α) := by
                have heq := congrArg (fun s : Finset (Fin h) => i.1 ∈ s) hreps
                exact heq.mpr i.2
              simpa [I] using hi⟩
            left_inv := by intro i; apply Subtype.ext; rfl
            right_inv := by intro i; apply Subtype.ext; rfl }
          rw [Fintype.prod_equiv e (fun i : E => ∑ w ∈ T i.1, f i w)
            (fun i => ∑ w ∈ T i.1,
              if i.1 = a then U (w - u a) * srwKernel d (v a - w) *
                srwKernel d (v b - w) else
                srwKernel m (w - u i.1) * srwKernel d (v i.1 - w))
            (by intro i; simp [f, e])]
          rw [← Finset.prod_subtype (Finset.univ.erase b)
            (fun i => by simp) (fun i => ∑ w ∈ T i,
              if i = a then U (w - u a) * srwKernel d (v a - w) *
                srwKernel d (v b - w) else
                srwKernel m (w - u i) * srwKernel d (v i - w))]
          rw [← Finset.mul_prod_erase (Finset.univ.erase b)
            (fun i => ∑ w ∈ T i,
              if i = a then U (w - u a) * srwKernel d (v a - w) *
                srwKernel d (v b - w) else
                srwKernel m (w - u i) * srwKernel d (v i - w))
            (Finset.mem_erase.mpr ⟨(ne_of_lt α.2), Finset.mem_univ _⟩)]
          have hrest :
              (∏ i ∈ rest,
                  ∑ w ∈ T i, if i = a then U (w - u a) * srwKernel d (v a - w) *
                    srwKernel d (v b - w) else
                    srwKernel m (w - u i) * srwKernel d (v i - w)) =
                ∏ i ∈ rest, srwKernel (m + d) (v i - u i) := by
            apply Finset.prod_congr rfl
            intro i hi
            have hia : i ≠ a := (Finset.mem_erase.mp hi).1
            have hib : i ≠ b := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
            simpa [hia] using hSpectator i hia hib
          rw [hrest, ← hPairSum]
          have hqfinal :
              (∏ i ∈ rest, srwKernel (m + d) (v i - u i)) =
                ∏ i, if i = a ∨ i = b then (1 : ℝ) else
                  srwKernel (m + d) (v i - u i) := by
            symm
            calc
              _ = ∏ i, if i ∈ rest then srwKernel (m + d) (v i - u i) else 1 := by
                apply Finset.prod_congr rfl
                intro i _
                by_cases hia : i = a
                · subst i
                  simp [rest]
                · by_cases hib : i = b
                  · subst i
                    simp [rest]
                  · simp [rest, hia, hib]
              _ = _ := Finset.prod_ite_mem_eq rest _
          rw [hqfinal]
          simp only [a, b, ite_true]
          rw [← hv]
          simp only [pow_two]
          ac_rfl

/-- A nonempty run-time set is obtained by adjoining its terminal time to an
arbitrary subset of the preceding interval. -/
theorem runTimeSets_succ (r : ℕ) :
    runTimeSets (r + 1) =
      (Finset.Icc 1 r).powerset.image (fun S => insert (r + 1) S) := by
  classical
  ext S
  constructor
  · intro hS
    rcases Finset.mem_filter.mp hS with ⟨hPow, hEnd⟩
    have hsubset : S ⊆ Finset.Icc 1 (r + 1) := Finset.mem_powerset.mp hPow
    have hend : r + 1 ∈ S := by
      simpa using hEnd.resolve_left (by omega)
    refine Finset.mem_image.mpr ?_
    refine ⟨S.erase (r + 1), ?_, ?_⟩
    · apply Finset.mem_powerset.mpr
      intro t ht
      have htS : t ∈ S := Finset.mem_of_mem_erase ht
      have htIcc := hsubset htS
      have htne : t ≠ r + 1 := (Finset.mem_erase.mp ht).1
      simp only [Finset.mem_Icc] at htIcc ⊢
      omega
    · exact Finset.insert_erase hend
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨T, hT, hEq⟩
    rw [← hEq]
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro t ht
      rcases Finset.mem_insert.mp ht with ht | ht
      · subst t
        simp
      · have htIcc := Finset.mem_powerset.mp hT ht
        simp only [Finset.mem_Icc] at htIcc ⊢
        omega
    · right
      simp

/-- Summing over a terminal run time and all earlier terminal times enumerates
each subset of the interval exactly once. -/
theorem sum_runTimeSets_range (r : ℕ) (F : Finset ℕ → ℝ) :
    ∑ m ∈ Finset.range (r + 1), ∑ S ∈ runTimeSets m, F S =
      ∑ S ∈ (Finset.Icc 1 r).powerset, F S := by
  induction r with
  | zero => simp [runTimeSets]
  | succ r ih =>
    have hIcc : Finset.Icc 1 (r + 1) = insert (r + 1) (Finset.Icc 1 r) := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : r + 1 ∉ Finset.Icc 1 r := by
      simp only [Finset.mem_Icc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 r).powerset
        ((Finset.Icc 1 r).powerset.image (insert (r + 1))) := by
      rw [Finset.disjoint_left]
      intro S hS hImage
      obtain ⟨T, hT, hEq⟩ := Finset.mem_image.mp hImage
      have hEnd : r + 1 ∈ S := by rw [← hEq]; simp
      exact hnot (Finset.mem_powerset.mp hS hEnd)
    rw [Finset.sum_range_succ, ih]
    rw [runTimeSets_succ]
    rw [hIcc, Finset.powerset_insert, Finset.sum_union hdisj]

private def runTimeSetCoefficient {h : ℕ} (σ2 : ℝ) (α : CollisionPair h)
    (r : ℕ) (u v : Fin h → Site) : ℝ :=
  ∑ S ∈ runTimeSets r, σ2 ^ S.card *
    collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v

/-- Peel off the terminal selected collision, then split at the preceding
selected time. -/
private theorem runTimeSetCoefficient_succ_markov {h : ℕ} (σ2 : ℝ)
    (α : CollisionPair h) (r : ℕ) (u v : Fin h → Site) :
    runTimeSetCoefficient σ2 α (r + 1) u v =
      σ2 * ∑ m ∈ Finset.range (r + 1), ∑ S ∈ runTimeSets m,
        σ2 ^ S.card *
          (∑' z : Fin h → Site,
            collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z *
              collisionSubsetCoefficient (r + 1 - m) h
                {(r + 1 - m, α)} z v) := by
  classical
  have hnot (T : Finset ℕ) (hT : T ∈ (Finset.Icc 1 r).powerset) :
      r + 1 ∉ T := by
    apply Finset.notMem_of_mem_powerset_of_notMem hT
    simp only [Finset.mem_Icc]
    omega
  have hinj : Set.InjOn (insert (r + 1))
      ((Finset.Icc 1 r).powerset : Set (Finset ℕ)) := by
    intro T hT T' hT' heq
    have hTend := hnot T hT
    have hT'end := hnot T' hT'
    have herase := congrArg (fun A : Finset ℕ => A.erase (r + 1)) heq
    simpa [hTend, hT'end] using herase
  have hsumImage (G : Finset ℕ → ℝ) :
      (∑ S ∈ (Finset.Icc 1 r).powerset.image (insert (r + 1)), G S) =
        ∑ T ∈ (Finset.Icc 1 r).powerset, G (insert (r + 1) T) := by
    rw [Finset.sum_image hinj]
  rw [runTimeSetCoefficient, runTimeSets_succ]
  rw [hsumImage]
  rw [← sum_runTimeSets_range r
    (fun T => σ2 ^ (insert (r + 1) T).card *
      collisionSubsetCoefficient (r + 1) h
        ((insert (r + 1) T).image fun t => (t, α)) u v)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  let d := r + 1 - m
  have hm_le : m ≤ r := by
    have hm' := Finset.mem_range.mp hm
    omega
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hSsub : S ⊆ Finset.Icc 1 m :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hEndNot : r + 1 ∉ S := by
    intro ht
    have htime' := hSsub ht
    simp only [Finset.mem_Icc] at htime'
    omega
  have hA1 : S.image (fun t => (t, α)) ⊆ collisionEdges m h := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1 ht,
      Finset.mem_univ _⟩
  have hA2 : ({(d, α)} : Finset (ℕ × CollisionPair h)) ⊆ collisionEdges d h := by
    intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hd, le_rfl⟩, Finset.mem_univ _⟩
  have htime : m + d = r + 1 := by dsimp [d]; omega
  have hshift : shiftEdges m {(d, α)} = {(r + 1, α)} := by
    ext e
    simp [shiftEdges, htime, Nat.add_comm]
  have hset :
      (insert (r + 1) S).image (fun t => (t, α)) =
        S.image (fun t => (t, α)) ∪ shiftEdges m {(d, α)} := by
    rw [Finset.image_insert, hshift]
    ext e
    simp [Finset.mem_insert]
  have hcoeff :
      collisionSubsetCoefficient (r + 1) h
          ((insert (r + 1) S).image fun t => (t, α)) u v =
        ∑' z : Fin h → Site,
          collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z *
            collisionSubsetCoefficient d h {(d, α)} z v := by
    calc
      collisionSubsetCoefficient (r + 1) h
          ((insert (r + 1) S).image fun t => (t, α)) u v =
        collisionSubsetCoefficient (m + d) h
          ((insert (r + 1) S).image fun t => (t, α)) u v := by
            exact congrArg (fun k => collisionSubsetCoefficient k h
              ((insert (r + 1) S).image fun t => (t, α)) u v) htime.symm
      _ = collisionSubsetCoefficient (m + d) h
          (S.image (fun t => (t, α)) ∪ shiftEdges m {(d, α)}) u v := by rw [hset]
      _ = _ := collisionSubsetCoefficient_union_shiftEdges m d hA1 hA2 u v
  rw [hcoeff]
  have hcard : (insert (r + 1) S).card = S.card + 1 :=
    Finset.card_insert_of_notMem hEndNot
  have hdeq : d = r + 1 - m := rfl
  rw [hcard, pow_succ]
  rw [← hdeq]
  ring_nf

/-- A collision-subset coefficient vanishes when an endpoint coordinate is
outside the finite set of sites reachable by that replica's walk. -/
theorem collisionSubsetCoefficient_zero_of_endpoint_not_mem {n h : ℕ}
    (A : Finset (ℕ × CollisionPair h)) (x y : Fin h → Site) (i : Fin h)
    (hi : y i ∉ Polymer.endpoints (x i) n) :
    collisionSubsetCoefficient n h A x y = 0 := by
  classical
  rw [collisionSubsetCoefficient]
  apply Finset.sum_eq_zero
  intro p hp
  have hnot : walkPosition (x i) (p i) n ≠ y i := by
    intro heq
    apply hi
    exact (Polymer.mem_endpoints_iff (x i) (y i) n).mpr ⟨p i, heq⟩
  have hzero : (∏ j, if walkPosition (x j) (p j) n = y j then (1 : ℝ) else 0) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hnot])
  simp [hzero]

/-- Interchange a finite sum with a `tsum` when the second variable has a
common finite support. -/
theorem sum_tsum_eq_tsum_sum_of_support {α β : Type*} [Countable β]
    (s : Finset α) (R : Finset β) (f : α → β → ℝ)
    (hz : ∀ a ∈ s, ∀ b ∉ R, f a b = 0) :
    (∑ a ∈ s, ∑' b, f a b) = ∑' b, ∑ a ∈ s, f a b := by
  classical
  calc
    (∑ a ∈ s, ∑' b, f a b) = ∑ a ∈ s, ∑ b ∈ R, f a b := by
      apply Finset.sum_congr rfl
      intro a ha
      apply tsum_eq_sum
      intro b hb
      exact hz a ha b hb
    _ = ∑ b ∈ R, ∑ a ∈ s, f a b := Finset.sum_comm
    _ = ∑' b, ∑ a ∈ s, f a b := by
      symm
      apply tsum_eq_sum
      intro b hb
      apply Finset.sum_eq_zero
      intro a ha
      exact hz a ha b hb

/-- Resumming all selected times of one fixed pair gives the spatial renewal,
while every other replica makes one free transition. -/
theorem sum_runTimeSets_coefficient_eq {h : ℕ} (σ2 : ℝ) (α : CollisionPair h)
    (r : ℕ) (u v : Fin h → Site) (hu : u α.1.1 = u α.1.2) :
    (∑ S ∈ runTimeSets r, σ2 ^ S.card *
      collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v) =
      (if v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
        Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) *
        ∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
          srwKernel r (v i - u i) := by
  classical
  revert v
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro v
      cases r with
      | zero =>
          simp [runTimeSets, collisionSubsetCoefficient_empty_eq_prod_srwKernel,
            Collision.spatialRenewal_zero, sub_eq_zero, hu]
          let a := α.1.1
          let b := α.1.2
          let e : Fin h → ℝ := fun i => if v i = u i then 1 else 0
          let rest : Finset (Fin h) := (Finset.univ.erase b).erase a
          have hab : a ≠ b := ne_of_lt α.2
          have hprod : (∏ i, e i) = e a * e b * ∏ i ∈ rest, e i := by
            change (Finset.univ.prod e) = _
            rw [← Finset.mul_prod_erase Finset.univ e (by simp : a ∈ Finset.univ)]
            rw [← Finset.mul_prod_erase (Finset.univ.erase a) e
              (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩)]
            rw [show (Finset.univ.erase a).erase b = rest by
              ext i
              simp [rest, and_comm]]
            ring
          have hmask : (∏ i ∈ rest, e i) =
              ∏ i, if i = a ∨ i = b then (1 : ℝ) else e i := by
            calc
              _ = ∏ i, if i ∈ rest then e i else 1 := by
                symm
                exact Finset.prod_ite_mem_eq rest e
              _ = _ := by
                apply Finset.prod_congr rfl
                intro i hi
                by_cases hia : i = a
                · simp [rest, hia]
                · by_cases hib : i = b
                  · simp [rest, hib]
                  · simp [rest, hia, hib]
          by_cases hav : v a = u a
          · by_cases hvab : v a = v b
            · have hvb : v b = u b := by
                calc
                  v b = v a := hvab.symm
                  _ = u a := hav
                  _ = u b := hu
              have hva_b : v a = u b := hav.trans hu
              have hvaAlpha : v α.1.1 = u α.1.2 := by simpa only [a, b] using hva_b
              have hvbAlpha : v α.1.2 = u α.1.2 := by simpa only [b] using hvb
              rw [hprod]
              rw [hmask]
              simp only [e, hav, hvb, ite_true, one_mul]
              simp only [hvaAlpha, hvbAlpha.symm, ite_true]
              simp only [a, b]
            · have hvb : v b ≠ u b := by
                intro hvb
                apply hvab
                calc
                  v a = u a := hav
                  _ = u b := hu
                  _ = v b := hvb.symm
              have hzero : ∏ i, e i = 0 :=
                Finset.prod_eq_zero (Finset.mem_univ b) (by simp [e, hvb])
              rw [hzero]
              have hvaAlpha : v α.1.1 = u α.1.2 := by
                simpa only [a, b] using hav.trans hu
              have hvbAlpha : v α.1.2 ≠ u α.1.2 := by simpa only [b] using hvb
              have hneq : u α.1.2 ≠ v α.1.2 := fun h => hvbAlpha h.symm
              simp only [hvaAlpha, hneq, ite_true, ite_false]
          · have hva' : v a ≠ u b := by
              intro hvau
              apply hav
              calc
                v a = u b := hvau
                _ = u a := hu.symm
            have hzero : ∏ i, e i = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ a) (by simp [e, hav])
            rw [hzero]
            have hvaAlpha : ¬ v α.1.1 = u α.1.2 := by simpa only [a, b] using hva'
            simp only [hvaAlpha, ite_false]
      | succ r =>
          change runTimeSetCoefficient σ2 α (r + 1) u v = _
          rw [runTimeSetCoefficient_succ_markov]
          let a := α.1.1
          let b := α.1.2
          let d (m : ℕ) := r + 1 - m
          have hvac : u a = u b := by exact hu
          have hsumStep (m : ℕ) (hm : m ∈ Finset.range (r + 1)) :
              (∑ S ∈ runTimeSets m, σ2 ^ S.card *
                (∑' z : Fin h → Site,
                  collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z *
                    collisionSubsetCoefficient (d m) h {(d m, α)} z v)) =
                (if v a = v b then (1 : ℝ) else 0) *
                  (∑' w : Site, Collision.spatialRenewal σ2 m (w - u a) *
                    srwKernel (d m) (v a - w) ^ 2) *
                  ∏ i, if i = a ∨ i = b then (1 : ℝ) else
                    srwKernel (r + 1) (v i - u i) := by
            have hmle : m ≤ r := by
              have := Finset.mem_range.mp hm
              omega
            have hmlt : m < r + 1 := by omega
            have hdm : m + d m = r + 1 := by dsimp [d]; omega
            have hdpos : 1 ≤ d m := by dsimp [d]; omega
            let Rm : Finset (Fin h → Site) := Fintype.piFinset
              (fun i => Polymer.endpoints (u i) m)
            have hsupport (S : Finset ℕ) (hS : S ∈ runTimeSets m)
                (z : Fin h → Site) (hz : z ∉ Rm) :
                σ2 ^ S.card *
                  collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z *
                    collisionSubsetCoefficient (d m) h {(d m, α)} z v = 0 := by
              have hmiss : ∃ i, z i ∉ Polymer.endpoints (u i) m := by
                by_contra hn
                apply hz
                apply Fintype.mem_piFinset.mpr
                intro i
                by_contra hi
                exact hn ⟨i, hi⟩
              obtain ⟨i, hi⟩ := hmiss
              rw [collisionSubsetCoefficient_zero_of_endpoint_not_mem _ _ _ i hi]
              ring
            calc
              _ = ∑ S ∈ runTimeSets m, ∑' z : Fin h → Site,
                    (σ2 ^ S.card *
                      collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z) *
                      collisionSubsetCoefficient (d m) h {(d m, α)} z v := by
                    apply Finset.sum_congr rfl
                    intro S hS
                    rw [← tsum_mul_left]
                    apply tsum_congr
                    intro z
                    ring
              _ = ∑' z : Fin h → Site, ∑ S ∈ runTimeSets m,
                    (σ2 ^ S.card *
                      collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z) *
                      collisionSubsetCoefficient (d m) h {(d m, α)} z v := by
                    exact sum_tsum_eq_tsum_sum_of_support (runTimeSets m) Rm
                      (fun S z => (σ2 ^ S.card *
                        collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z) *
                        collisionSubsetCoefficient (d m) h {(d m, α)} z v)
                      hsupport
              _ = ∑' z : Fin h → Site,
                    (∑ S ∈ runTimeSets m, σ2 ^ S.card *
                      collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z) *
                      collisionSubsetCoefficient (d m) h {(d m, α)} z v := by
                    apply tsum_congr
                    intro z
                    rw [Finset.sum_mul]
              _ = ∑' z : Fin h → Site,
                    (if z a = z b then (1 : ℝ) else 0) *
                      Collision.spatialRenewal σ2 m (z a - u a) *
                      (∏ i, if i = a ∨ i = b then (1 : ℝ) else
                        srwKernel m (z i - u i)) *
                      collisionSubsetCoefficient (d m) h {(d m, α)} z v := by
                    apply tsum_congr
                    intro z
                    rw [ih m hmlt z]
              _ = _ := by
                    by_cases hv : v a = v b
                    · simp_rw [collisionSubsetCoefficient_singleton_end hdpos α]
                      have hvAlpha : v α.1.1 = v α.1.2 := by simpa only [a, b] using hv
                      simp only [hvAlpha, ite_true, one_mul]
                      rw [run_pairConfigSum_factor α m (d m) u v hu hv
                        (fun x => Collision.spatialRenewal σ2 m x)
                        (by intro x hx
                            exact spatialRenewal_eq_zero_of_not_mem_endpoints σ2 m x hx)]
                      rw [hv, hdm]
                      simp only [a, b, eq_self, ite_true, one_mul]
                    · simp_rw [collisionSubsetCoefficient_singleton_end hdpos α]
                      have hvAlpha : ¬ v α.1.1 = v α.1.2 := by simpa only [a, b] using hv
                      simp only [hvAlpha, hv, ite_false, zero_mul, mul_zero]
                      rw [tsum_zero]
          have hrunSum :
              (∑ m ∈ Finset.range (r + 1), ∑ S ∈ runTimeSets m,
                σ2 ^ S.card *
                  (∑' z : Fin h → Site,
                    collisionSubsetCoefficient m h (S.image fun t => (t, α)) u z *
                      collisionSubsetCoefficient (r + 1 - m) h {(r + 1 - m, α)} z v)) =
                ∑ m ∈ Finset.range (r + 1),
                  (if v a = v b then (1 : ℝ) else 0) *
                    (∑' w : Site, Collision.spatialRenewal σ2 m (w - u a) *
                      srwKernel (r + 1 - m) (v a - w) ^ 2) *
                    ∏ i, if i = a ∨ i = b then (1 : ℝ) else
                      srwKernel (r + 1) (v i - u i) := by
            apply Finset.sum_congr rfl
            intro m hm
            exact hsumStep m hm
          rw [hrunSum]
          have hshift (m : ℕ) :
              (∑' w : Site, Collision.spatialRenewal σ2 m (w - u a) *
                srwKernel (r + 1 - m) (v a - w) ^ 2) =
                ∑' z : Site, Collision.spatialRenewal σ2 m z *
                  srwKernel (r + 1 - m) ((v a - u a) - z) ^ 2 := by
            calc
              _ = ∑' z : Site,
                    Collision.spatialRenewal σ2 m
                      (Equiv.addLeft (u a) z - u a) *
                      srwKernel (r + 1 - m) (v a - Equiv.addLeft (u a) z) ^ 2 :=
                    (Equiv.addLeft (u a)).tsum_eq _ |>.symm
              _ = _ := by
                    apply tsum_congr
                    intro z
                    have hz : Equiv.addLeft (u a) z - u a = z := by
                      simp [Equiv.addLeft]
                    have hk : v a - Equiv.addLeft (u a) z = (v a - u a) - z := by
                      simp [Equiv.addLeft]
                      abel
                    rw [hz, hk]
          have hrenewal :
              σ2 * (∑ m ∈ Finset.range (r + 1),
                ∑' w : Site, Collision.spatialRenewal σ2 m (w - u a) *
                  srwKernel (r + 1 - m) (v a - w) ^ 2) =
                Collision.spatialRenewal σ2 (r + 1) (v a - u a) := by
            rw [← Fin.sum_univ_eq_sum_range]
            rw [Finset.mul_sum]
            rw [Collision.spatialRenewal_succ]
            apply Finset.sum_congr rfl
            intro m hm
            rw [hshift m.val]
            rw [mul_comm σ2]
            rw [← tsum_mul_right]
            apply tsum_congr
            intro z
            ring
          have hfactor :
              σ2 * (∑ m ∈ Finset.range (r + 1),
                (if v a = v b then (1 : ℝ) else 0) *
                  (∑' w : Site, Collision.spatialRenewal σ2 m (w - u a) *
                    srwKernel (r + 1 - m) (v a - w) ^ 2) *
                  ∏ i, if i = a ∨ i = b then (1 : ℝ) else
                    srwKernel (r + 1) (v i - u i)) =
              (if v a = v b then (1 : ℝ) else 0) *
                (σ2 * (∑ m ∈ Finset.range (r + 1),
                  ∑' w : Site, Collision.spatialRenewal σ2 m (w - u a) *
                    srwKernel (r + 1 - m) (v a - w) ^ 2)) *
                ∏ i, if i = a ∨ i = b then (1 : ℝ) else
                  srwKernel (r + 1) (v i - u i) := by
            let I : ℝ := if v a = v b then 1 else 0
            let Q : ℝ := ∏ i, if i = a ∨ i = b then (1 : ℝ) else
              srwKernel (r + 1) (v i - u i)
            let G (m : ℕ) : ℝ := ∑' w : Site,
              Collision.spatialRenewal σ2 m (w - u a) *
                srwKernel (r + 1 - m) (v a - w) ^ 2
            change σ2 * (∑ m ∈ Finset.range (r + 1), I * G m * Q) =
              I * (σ2 * (∑ m ∈ Finset.range (r + 1), G m)) * Q
            rw [Finset.mul_sum]
            calc
              _ = ∑ m ∈ Finset.range (r + 1),
                    (I * Q) * (σ2 * G m) := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  ring
              _ = (I * Q) * (σ2 * (∑ m ∈ Finset.range (r + 1), G m)) := by
                  rw [Finset.mul_sum, Finset.mul_sum]
              _ = I * (σ2 * (∑ m ∈ Finset.range (r + 1), G m)) * Q := by ring
          rw [hfactor, hrenewal]

/-- The coefficient of a first run followed by a shifted rest factors at the run's two ends. -/
theorem collisionSubsetCoefficient_runEdges_union {h : ℕ} (α : CollisionPair h) {s r m : ℕ}
    (_hs : 1 ≤ s) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 r)
    {A' : Finset (ℕ × CollisionPair h)} (hA' : A' ⊆ collisionEdges m h)
    (x y : Fin h → Site) :
    collisionSubsetCoefficient (s + r + m) h (runEdges α s S ∪ shiftEdges (s + r) A') x y =
      ∑' u : Fin h → Site, ∑' v : Fin h → Site,
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          (∏ i, srwKernel s (u i - x i)) *
          collisionSubsetCoefficient r h (S.image fun t => (t, α)) u v *
            collisionSubsetCoefficient m h A' v y := by
  classical
  let B : Finset (ℕ × CollisionPair h) := S.image fun t => (t, α)
  have hB : B ⊆ collisionEdges r h := by
    intro e he
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ?_, Finset.mem_univ _⟩
    exact Finset.mem_Icc.mp (hS ht)
  have hshiftA : shiftEdges r A' ⊆ collisionEdges (r + m) h := by
    intro e he
    obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    have heTime := Finset.mem_product.mp (hA' he')
    have htime := Finset.mem_Icc.mp heTime.1
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_Icc.mpr ?_, Finset.mem_univ _⟩
    omega
  have hrest : B ∪ shiftEdges r A' ⊆ collisionEdges (r + m) h := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · have htime := Finset.mem_Icc.mp (Finset.mem_product.mp (hB he)).1
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Icc.mpr (by omega), Finset.mem_univ _⟩
    · exact hshiftA he
  have hfirst : ({(s, α)} : Finset (ℕ × CollisionPair h)) ⊆ collisionEdges s h := by
    intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, Finset.mem_univ _⟩
  have hset :
      runEdges α s S ∪ shiftEdges (s + r) A' =
        {(s, α)} ∪ shiftEdges s (B ∪ shiftEdges r A') := by
    have hrun : runEdges α s S = insert (s, α) (shiftEdges s B) := by
      ext e
      simp [runEdges, shiftEdges, B, Nat.add_comm]
    have hshift : shiftEdges (s + r) A' = shiftEdges s (shiftEdges r A') := by
      simp [shiftEdges, Finset.image_image, Function.comp_def,
        Nat.add_assoc, Nat.add_comm r s]
    rw [hrun, hshift, Finset.singleton_union]
    unfold shiftEdges
    rw [Finset.image_union]
    exact Finset.insert_union (s, α) _ _
  rw [show s + r + m = s + (r + m) by omega, hset,
    collisionSubsetCoefficient_union_shiftEdges s (r + m) hfirst hrest]
  have hinner (u : Fin h → Site) :
      collisionSubsetCoefficient (r + m) h (B ∪ shiftEdges r A') u y =
        ∑' v : Fin h → Site,
          collisionSubsetCoefficient r h B u v *
            collisionSubsetCoefficient m h A' v y :=
    collisionSubsetCoefficient_union_shiftEdges (t := r) (m := m)
      (A₁ := B) (A₂ := A') hB hA' u y
  simp_rw [hinner]
  have hsingle (u : Fin h → Site) :
      collisionSubsetCoefficient s h {(s, α)} x u =
        (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
          ∏ i, srwKernel s (u i - x i) :=
    collisionSubsetCoefficient_singleton_end _hs α x u
  simp_rw [B, hsingle]
  apply tsum_congr
  intro u
  rw [← tsum_mul_left]
  apply tsum_congr
  intro v
  ring_nf

end Critical2DKPZ.SHF.Moments

end
