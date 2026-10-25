/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationBlockWordSupport
public import Critical2DKPZ.SHF.Moments.WordDominationRunDampingProduct
public import Critical2DKPZ.SHF.Moments.WordDominationPairStratumFree
import Mathlib.Tactic

/-! # Finite-support recursion after a free terminal extension -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

/-- The product free-walk kernel vanishes outside the coordinatewise endpoint
set, giving finite support for its lattice sums. -/
theorem collisionWord_freeProduct_zero_of_not_endpoints {h : ℕ}
    (n : ℕ) (x y : LatticeConfiguration h)
    (hy : y ∉ collisionWordConfigurationEndpointSet n x) :
    (∏ i, srwKernel n (y i - x i)) = 0 := by
  have hmiss : ∃ i, y i ∉ endpoints (x i) n := by
    by_contra hn
    apply hy
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmiss
  have hkernel : srwKernel n (y i - x i) = 0 := by
    exact srwKernel_eq_zero_of_not_mem n (x i) (y i) hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) hkernel

/-- A collision-run factor vanishes outside the run endpoint set. -/
theorem collisionWord_runFactor_zero_of_not_endpoints {h : ℕ}
    (β : ℝ) (α : CollisionPair h) (r : ℕ)
    (u v : LatticeConfiguration h)
    (hv : v ∉ collisionWordConfigurationEndpointSet r u) :
    collisionWordUndampedPairRunFactor β α r u v = 0 := by
  by_contra hrun
  have hcollision : u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 := by
    by_contra hnot
    apply hrun
    simp [collisionWordUndampedPairRunFactor, hnot]
  have hrenew : Collision.spatialRenewal (sigmaSq β) r
      (v α.1.1 - u α.1.1) ≠ 0 := by
    intro hz
    apply hrun
    have hind : (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2
        then (1 : ℝ) else 0) = 1 := by
      simp [hcollision]
    unfold collisionWordUndampedPairRunFactor
    rw [hind, hz]
    simp
  apply hv
  apply Fintype.mem_piFinset.mpr
  intro i
  by_cases hia : i = α.1.1
  · subst i
    exact spatialRenewal_nonzero_endpoint hrenew
  · by_cases hib : i = α.1.2
    · subst i
      simpa [hcollision.1, hcollision.2] using
        (spatialRenewal_nonzero_endpoint hrenew)
    · have hkernel : srwKernel r (v i - u i) ≠ 0 := by
        intro hz
        have hprod :
            (∏ j : Fin h, if j = α.1.1 ∨ j = α.1.2 then (1 : ℝ)
              else srwKernel r (v j - u j)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hia, hib, hz])
        apply hrun
        simp [collisionWordUndampedPairRunFactor, hcollision, hprod]
      by_contra hnot
      exact hkernel (srwKernel_eq_zero_of_not_mem r (u i) (v i) hnot)

/-- The terminal free-walk product has finite support in its terminal endpoint
configuration. -/
theorem collisionWord_terminalWalkProduct_zero_of_not_endpoints {h : ℕ}
    (k : ℕ) (y z : LatticeConfiguration h)
    (hz : z ∉ collisionWordConfigurationEndpointSet k y) :
    (∏ i, srwKernel k (y i - z i)) = 0 := by
  have hmiss : ∃ i, z i ∉ endpoints (y i) k := by
    by_contra hn
    apply hz
    apply Fintype.mem_piFinset.mpr
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  obtain ⟨i, hi⟩ := hmiss
  have hyz : y i ∉ endpoints (z i) k := by
    intro hmem
    exact hi (Critical2DKPZ.SHF.Flow.mem_endpoints_reverse hmem)
  have hkernel : srwKernel k (y i - z i) = 0 :=
    srwKernel_eq_zero_of_not_mem k (z i) (y i) hyz
  exact Finset.prod_eq_zero (Finset.mem_univ i) hkernel

/-- Exact recursion for a block word paired with a positive terminal free
walk. Every lattice sum is finite-support: the terminal walk, incoming free
walk and run kernel provide the three endpoint cutoffs. -/
theorem blockWordKernel_cons_terminalExtension_eq
    {h n k : ℕ} (β : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (x y : LatticeConfiguration h) :
    (∑' z : LatticeConfiguration h,
      blockWordKernel (sigmaSq β) (α :: w) n x z *
        ∏ i, srwKernel k (y i - z i)) =
      (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
        ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          ((∏ i, srwKernel s (u i - x i)) *
            collisionWordUndampedPairRunFactor β α r u v) *
            (∑' z : LatticeConfiguration h,
              blockWordKernel (sigmaSq β) w (n - s - r) v z *
                ∏ i, srwKernel k (y i - z i))) := by
  classical
  let Z : Finset (LatticeConfiguration h) := collisionWordConfigurationEndpointSet k y
  let U : ℕ → Finset (LatticeConfiguration h) :=
    fun s => collisionWordConfigurationEndpointSet s x
  let V : ℕ → LatticeConfiguration h → Finset (LatticeConfiguration h) :=
    fun r u => collisionWordConfigurationEndpointSet r u
  let A : ℕ → LatticeConfiguration h → ℝ := fun s u =>
    ∏ i, srwKernel s (u i - x i)
  let R : ℕ → LatticeConfiguration h → LatticeConfiguration h → ℝ :=
    fun r u v => collisionWordUndampedPairRunFactor β α r u v
  let B : ℕ → LatticeConfiguration h → LatticeConfiguration h → ℝ :=
    fun m v z => blockWordKernel (sigmaSq β) w m v z
  let P : LatticeConfiguration h → ℝ := fun z =>
    ∏ i, srwKernel k (y i - z i)
  have hleft :
      (∑' z : LatticeConfiguration h,
        blockWordKernel (sigmaSq β) (α :: w) n x z *
          ∏ i, srwKernel k (y i - z i)) =
        ∑ z ∈ Z,
          blockWordKernel (sigmaSq β) (α :: w) n x z *
            ∏ i, srwKernel k (y i - z i) := by
    apply tsum_eq_sum
    intro z hz
    have hPzero : (∏ i, srwKernel k (y i - z i)) = 0 :=
      collisionWord_terminalWalkProduct_zero_of_not_endpoints k y z (by simpa [Z] using hz)
    rw [hPzero]
    simp
  rw [hleft]
  have hterm (s : ℕ) (hs : s ∈ Finset.Icc 1 n)
      (r : ℕ) (hr : r ∈ Finset.range (n - s + 1)) :
      (∑ z ∈ Z,
        (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          A s u * R r u v * B (n - s - r) v z) * P z) =
      ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
        (A s u * R r u v) *
          (∑' z : LatticeConfiguration h, B (n - s - r) v z * P z) := by
    have hUzero (u : LatticeConfiguration h) (hu : u ∉ U s) : A s u = 0 := by
      exact collisionWord_freeProduct_zero_of_not_endpoints s x u (by simpa [U] using hu)
    have hRzero (u v : LatticeConfiguration h) (hv : v ∉ V r u) : R r u v = 0 := by
      exact collisionWord_runFactor_zero_of_not_endpoints β α r u v (by simpa [V] using hv)
    have hVsum (u z : LatticeConfiguration h) :
        (∑' v : LatticeConfiguration h,
          A s u * R r u v * B (n - s - r) v z) =
        ∑ v ∈ V r u, A s u * R r u v * B (n - s - r) v z := by
      apply tsum_eq_sum
      intro v hv
      rw [hRzero u v hv]
      simp
    have hUsum (z : LatticeConfiguration h) :
        (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          A s u * R r u v * B (n - s - r) v z) =
        ∑ u ∈ U s, ∑ v ∈ V r u,
          A s u * R r u v * B (n - s - r) v z := by
      rw [tsum_eq_sum (s := U s)]
      · apply Finset.sum_congr rfl
        intro u hu
        exact hVsum u z
      · intro u hu
        rw [hUzero u hu]
        simp
    have hZsum (u v : LatticeConfiguration h) :
        (∑ z ∈ Z, B (n - s - r) v z * P z) =
          ∑' z : LatticeConfiguration h, B (n - s - r) v z * P z := by
      symm
      apply tsum_eq_sum
      intro z hz
      have hPzero : (∏ i, srwKernel k (y i - z i)) = 0 :=
        collisionWord_terminalWalkProduct_zero_of_not_endpoints k y z (by simpa [Z] using hz)
      have hPzero' : P z = 0 := by
        change (∏ i, srwKernel k (y i - z i)) = 0
        exact hPzero
      rw [hPzero']
      simp
    have hVback (u : LatticeConfiguration h) :
        (∑ v ∈ V r u,
          (A s u * R r u v) *
            (∑' z : LatticeConfiguration h, B (n - s - r) v z * P z)) =
        ∑' v : LatticeConfiguration h,
          (A s u * R r u v) *
            (∑' z : LatticeConfiguration h, B (n - s - r) v z * P z) := by
      symm
      apply tsum_eq_sum
      intro v hv
      rw [hRzero u v hv]
      simp
    have hUback :
        (∑ u ∈ U s, ∑' v : LatticeConfiguration h,
          (A s u * R r u v) *
            (∑' z : LatticeConfiguration h, B (n - s - r) v z * P z)) =
        ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
          (A s u * R r u v) *
            (∑' z : LatticeConfiguration h, B (n - s - r) v z * P z) := by
      symm
      apply tsum_eq_sum (s := U s)
      intro u hu
      rw [hUzero u hu]
      simp
    calc
      _ = ∑ z ∈ Z, ∑ u ∈ U s, ∑ v ∈ V r u,
            A s u * R r u v * (B (n - s - r) v z * P z) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [hUsum z]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = ∑ u ∈ U s, ∑ z ∈ Z, ∑ v ∈ V r u,
            A s u * R r u v * (B (n - s - r) v z * P z) := by
        rw [Finset.sum_comm]
      _ = ∑ u ∈ U s, ∑ v ∈ V r u, ∑ z ∈ Z,
            A s u * R r u v * (B (n - s - r) v z * P z) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact Finset.sum_comm
      _ = ∑ u ∈ U s, ∑ v ∈ V r u,
            (A s u * R r u v) *
              (∑ z ∈ Z, B (n - s - r) v z * P z) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        rw [← Finset.mul_sum]
      _ = ∑ u ∈ U s, ∑ v ∈ V r u,
            (A s u * R r u v) *
              (∑' z : LatticeConfiguration h,
                B (n - s - r) v z * P z) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        rw [hZsum u v]
      _ = ∑ u ∈ U s, ∑' v : LatticeConfiguration h,
            (A s u * R r u v) *
              (∑' z : LatticeConfiguration h,
                B (n - s - r) v z * P z) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hVback u
      _ = ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            (A s u * R r u v) *
              (∑' z : LatticeConfiguration h,
                B (n - s - r) v z * P z) := hUback
  calc
    _ = ∑ z ∈ Z,
          (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
            ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
              (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
                (∏ i, srwKernel s (u i - x i)) *
                  sigmaSq β * Collision.spatialRenewal (sigmaSq β) r
                    (v α.1.1 - u α.1.1) *
                  (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ)
                    else srwKernel r (v i - u i)) *
                  blockWordKernel (sigmaSq β) w (n - s - r) v z) *
            ∏ i, srwKernel k (y i - z i) := by
      simp only [blockWordKernel]
    _ = ∑ z ∈ Z, ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            A s u * R r u v * B (n - s - r) v z) * P z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      have hcoeff :
          (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            (if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0) *
              (∏ i, srwKernel s (u i - x i)) *
                sigmaSq β * Collision.spatialRenewal (sigmaSq β) r
                  (v α.1.1 - u α.1.1) *
                (∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ)
                  else srwKernel r (v i - u i)) *
                blockWordKernel (sigmaSq β) w (n - s - r) v z) =
            ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
              A s u * R r u v * B (n - s - r) v z := by
        apply tsum_congr
        intro u
        apply tsum_congr
        intro v
        dsimp [A, R, B, collisionWordUndampedPairRunFactor]
        ring
      rw [hcoeff]
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑ z ∈ Z,
            (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
              A s u * R r u v * B (n - s - r) v z) * P z := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm
    _ = ∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
          ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
            ((∏ i, srwKernel s (u i - x i)) *
              collisionWordUndampedPairRunFactor β α r u v) *
              (∑' z : LatticeConfiguration h,
                blockWordKernel (sigmaSq β) w (n - s - r) v z *
                  ∏ i, srwKernel k (y i - z i)) := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro r hr
      have hterm' := hterm s hs r hr
      simpa only [A, R, B, P] using hterm'

end Critical2DKPZ.SHF.Moments

end
