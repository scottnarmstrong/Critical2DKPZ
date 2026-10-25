/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25BoundaryVectorBound
import Mathlib.Tactic

/-! # Time-summed CCR25 boundary-vector estimate -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- The weighted replica boundary vector satisfies the finite Lᵖ estimate. -/
theorem finiteLpNorm_hattedReplicaBoundaryVector_le (h : ℕ) (hh : 2 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ L : ℕ, ∀ p : ℝ, 1 < p →
      ∀ (A : Finset Site) (f : Site → ℝ), (∀ y, 0 ≤ f y) →
      ∀ (s : Finset (LatticeConfiguration h)) (I : ReplicaPartition h), I ≠ ⊥ →
        finiteLpNorm s p
          (fun x => hattedReplicaBoundaryVector L I A f x /
            replicaExponentialWeight t x) ≤
          C * Real.exp (C * t ^ 2 * L) * (p / (p - 1)) *
            (∑ y ∈ A, f y * Real.exp (t * ‖siteToPlane y‖)) *
            finiteLpNorm A p (fun y => f y * Real.exp (t * ‖siteToPlane y‖)) ^ (h - 1) := by
  obtain ⟨c, hc, hconvBounds⟩ := finiteLpNorm_boundaryConvolution_mul_exp_le
  let C : ℝ := max (3 * c ^ h) (2 * c * (h : ℝ))
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hpowC : 1 ≤ c ^ h := by
    have hle : (1 : ℝ) ^ h ≤ c ^ h := pow_le_pow_left₀ (by norm_num) hc h
    simpa using hle
  have hC : 1 ≤ C := by
    dsimp [C]
    have hsmall : 1 ≤ 3 * c ^ h := by nlinarith [hpowC]
    exact le_trans hsmall (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro t ht L p hp A f hf s I hI
  classical
  let F : Site → ℝ := fun y => f y * Real.exp (t * ‖siteToPlane y‖)
  let P : ℝ := finiteLpNorm A p F
  let B : ℝ := ∑ y ∈ A, F y
  let H : ℝ := c * Real.exp (2 * c * t ^ 2 * L)
  have hFnonneg : ∀ y ∈ A, 0 ≤ F y := by
    intro y hy
    dsimp [F]
    exact mul_nonneg (hf y) (Real.exp_nonneg _)
  have hP : 0 ≤ P := finiteLpNorm_nonneg A p F
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun y hy => hFnonneg y hy
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hdelta : 0 < 1 - 1 / p := by
    have hInv : 1 / p < 1 := by rw [div_lt_one hp0]; exact hp
    linarith
  have hdelta_le : 1 - 1 / p ≤ 1 := by
    have : 0 ≤ 1 / p := (one_div_pos.mpr hp0).le
    linarith
  have hq : 0 < p / (p - 1) := div_pos hp0 (sub_pos.mpr hp)
  have hH : 1 ≤ H := by
    dsimp [H]
    have harg : 0 ≤ 2 * c * t ^ 2 * L := by positivity
    have hexp : 1 ≤ Real.exp (2 * c * t ^ 2 * L) := by
      nlinarith [Real.add_one_le_exp (2 * c * t ^ 2 * L)]
    calc
      1 ≤ c := hc
      _ = c * 1 := by ring
      _ ≤ c * Real.exp (2 * c * t ^ 2 * L) :=
        mul_le_mul_of_nonneg_left hexp hc0
  have hHnonneg : 0 ≤ H := le_trans (by norm_num) hH
  by_cases hPzero : P = 0
  · have hFzero : ∀ y ∈ A, F y = 0 := by
      intro y hy
      exact finiteLpNorm_eq_zero_forces_zero A F hPzero y hy
    have hfzero : ∀ y ∈ A, f y = 0 := by
      intro y hy
      have hz := hFzero y hy
      dsimp [F] at hz
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt (Real.exp_pos _))
    have hconvzero : ∀ n : ℕ, ∀ x : Site, finiteBoundaryConvolution n A f x = 0 := by
      intro n x
      unfold finiteBoundaryConvolution
      apply Finset.sum_eq_zero
      intro y hy
      simp [hfzero y hy]
    have hrepzero : ∀ n : ℕ, ∀ x : LatticeConfiguration h,
        replicaBoundaryVector n I A f x = 0 := by
      intro n x
      by_cases hcoll : IsCollisionConfiguration I x
      · rw [replicaBoundaryVector, ite_eq_left hcoll]
        have hz :
            (∏ i : Fin h, finiteBoundaryConvolution n A f (x i)) = 0 := by
          let i0 : Fin h := ⟨0, by omega⟩
          exact Finset.prod_eq_zero (Finset.mem_univ i0) (hconvzero n (x i0))
        exact hz
      · rw [replicaBoundaryVector, ite_eq_right hcoll]
    have hhatzero : ∀ x : LatticeConfiguration h,
        hattedReplicaBoundaryVector L I A f x = 0 := by
      intro x
      unfold hattedReplicaBoundaryVector
      apply Finset.sum_eq_zero
      intro n hn
      exact hrepzero (n + 1) x
    have hleftzero : finiteLpNorm s p
        (fun x => hattedReplicaBoundaryVector L I A f x /
          replicaExponentialWeight t x) = 0 := by
      unfold finiteLpNorm
      have hinvpos : 0 < 1 / p := one_div_pos.mpr hp0
      have hinvNe : p⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hp0)
      simp [hhatzero, Real.zero_rpow hp0.ne']
      exact Real.zero_rpow hinvNe
    rw [hleftzero]
    positivity
  · have hPpos : 0 < P := lt_of_le_of_ne hP (Ne.symm hPzero)
    have hPleB : P ≤ B := by
      dsimp [P, B, F]
      exact finiteLpNorm_nonneg_le_sum A hp.le
        (fun y => f y * Real.exp (t * ‖siteToPlane y‖))
        (fun y hy => mul_nonneg (hf y) (Real.exp_nonneg _))
    have hBpos : 0 < B := lt_of_lt_of_le hPpos hPleB
    let q : ℝ := p / (p - 1)
    let δ : ℝ := 1 - 1 / p
    let r : ℝ := B / P
    let R : ℝ := r ^ q
    let N : ℕ := Nat.floor R + 1
    have hqδ : q * δ = 1 := by
      dsimp [q, δ]
      field_simp [ne_of_gt hp0, ne_of_gt (sub_pos.mpr hp)]
    have hrpos : 0 < r := by dsimp [r]; exact div_pos hBpos hPpos
    have hrone : 1 ≤ r := by
      dsimp [r]
      rw [le_div_iff₀ hPpos]
      simpa using hPleB
    have hqpos : 0 < q := by dsimp [q]; exact div_pos hp0 (sub_pos.mpr hp)
    have hRnonneg : 0 ≤ R := by dsimp [R]; positivity
    have hRone : 1 ≤ R := by
      dsimp [R]
      calc
        (1 : ℝ) = 1 ^ q := by rw [Real.one_rpow]
        _ ≤ r ^ q := Real.rpow_le_rpow (by norm_num) hrone hqpos.le
    have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hRone
    have hfloor : (Nat.floor R : ℝ) ≤ R := Nat.floor_le hRnonneg
    have hRN : R < (N : ℝ) := by
      simp only [N, Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one R
    have hNpos : 1 ≤ N := by dsimp [N]; omega
    have hNlower : R ≤ (N : ℝ) := hRN.le
    have hNupper : (N : ℝ) ≤ 2 * R := by
      dsimp [N]
      norm_num at hfloor ⊢
      nlinarith [hfloor, hRone]
    have hRδ : R ^ δ = r := by
      dsimp [R]
      rw [← Real.rpow_mul hrpos.le, hqδ, Real.rpow_one]
    have hNδ : (N : ℝ) ^ δ ≤ 2 * r := by
      calc
        (N : ℝ) ^ δ ≤ (2 * R) ^ δ :=
          Real.rpow_le_rpow (by positivity) hNupper hdelta.le
        _ = 2 ^ δ * R ^ δ := Real.mul_rpow (by norm_num) hRnonneg
        _ ≤ 2 * r := by
          rw [hRδ]
          have h2δ : (2 : ℝ) ^ δ ≤ 2 := by
            calc
              (2 : ℝ) ^ δ ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hdelta_le
              _ = 2 := by rw [Real.rpow_one]
          exact mul_le_mul_of_nonneg_right h2δ hrpos.le
    have hNnegδ : (N : ℝ) ^ (-δ) ≤ 1 / r := by
      calc
        (N : ℝ) ^ (-δ) ≤ R ^ (-δ) :=
          Real.rpow_le_rpow_of_nonpos hRpos hNlower (by linarith)
        _ = r ^ (-1 : ℝ) := by
          dsimp [R]
          rw [← Real.rpow_mul hrpos.le]
          have hexp : q * (-δ) = (-1 : ℝ) := by
            rw [mul_neg]
            nlinarith [hqδ]
          rw [hexp]
        _ = 1 / r := by
          rw [Real.rpow_neg hrpos.le, Real.rpow_one]
          simp [one_div]
    have hbalanceShort : P ^ h * r = B * P ^ (h - 1) := by
      dsimp [r]
      have hhpow : h = (h - 1) + 1 := by omega
      conv_lhs => rw [hhpow]
      rw [pow_succ]
      field_simp [ne_of_gt hPpos]
    have hbalanceTail : B ^ 2 * P ^ (h - 2) * (1 / r) =
        B * P ^ (h - 1) := by
      dsimp [r]
      have hhpow : h - 1 = (h - 2) + 1 := by omega
      conv_rhs => rw [hhpow]
      rw [pow_succ]
      field_simp [ne_of_gt hBpos, ne_of_gt hPpos]
      ring
    let Rshort : Finset ℕ := (Finset.range L).filter (fun k => k < N)
    let Rtail : Finset ℕ := (Finset.range L).filter (fun k => N ≤ k)
    have hpartition : Finset.range L = Rshort ∪ Rtail := by
      ext k
      simp [Rshort, Rtail]
      omega
    have hdis : Disjoint Rshort Rtail := by
      apply Finset.disjoint_left.mpr
      intro k hkS hkT
      have hkN := (Finset.mem_filter.mp hkS).2
      have hkN' := (Finset.mem_filter.mp hkT).2
      omega
    let shortWeight : ℕ → ℝ := fun k =>
      H ^ h * ((k + 1 : ℕ) : ℝ) ^ (-1 / p) * P ^ h
    let tailWeight : ℕ → ℝ := fun k =>
      H ^ h * ((k + 1 : ℕ) : ℝ) ^ (-(2 - 1 / p)) *
        B ^ 2 * P ^ (h - 2)
    have hshortSum : (∑ k ∈ Finset.range N, shortWeight k) ≤
        H ^ h * P ^ h * q * (N : ℝ) ^ δ := by
      calc
        (∑ k ∈ Finset.range N, shortWeight k) =
            ∑ k ∈ Finset.range N,
              (H ^ h * P ^ h) * ((k + 1 : ℕ) : ℝ) ^ (-1 / p) := by
          dsimp [shortWeight]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = H ^ h * P ^ h *
              ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ (-1 / p) := by
          rw [← Finset.mul_sum]
        _ ≤ H ^ h * P ^ h * (p / (p - 1)) * (N : ℝ) ^ δ := by
          have hsum := sum_shift_rpow_inv_le hp N
          have hsum' :
              (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ (-1 / p)) ≤
                p / (p - 1) * (N : ℝ) ^ (1 - 1 / p) := by
            simpa only [Nat.cast_add, Nat.cast_one] using hsum
          have hcoef : 0 ≤ H ^ h * P ^ h :=
            mul_nonneg (pow_nonneg hHnonneg _) (pow_nonneg hP _)
          calc
            H ^ h * P ^ h * ∑ k ∈ Finset.range N,
                ((k + 1 : ℕ) : ℝ) ^ (-1 / p) ≤
              H ^ h * P ^ h * (p / (p - 1) * (N : ℝ) ^ (1 - 1 / p)) :=
                mul_le_mul_of_nonneg_left hsum' hcoef
            _ = H ^ h * P ^ h * (p / (p - 1)) * (N : ℝ) ^ δ := by
              dsimp [δ]
              ring
        _ = H ^ h * P ^ h * q * (N : ℝ) ^ δ := by rfl
    have hshortSubset : (∑ k ∈ Rshort, shortWeight k) ≤
        H ^ h * P ^ h * q * (N : ℝ) ^ δ := by
      apply le_trans
        (Finset.sum_le_sum_of_subset_of_nonneg
          (show Rshort ⊆ Finset.range N by
            intro k hk
            exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2)
          (fun k hkN hkS => by
            dsimp [shortWeight]
            positivity))
        hshortSum
    have htailSum : (∑ k ∈ Finset.Ico N L, tailWeight k) ≤
        H ^ h * B ^ 2 * P ^ (h - 2) * q * (N : ℝ) ^ (-δ) := by
      calc
        (∑ k ∈ Finset.Ico N L, tailWeight k) =
            ∑ k ∈ Finset.Ico N L,
              (H ^ h * B ^ 2 * P ^ (h - 2)) *
                ((k + 1 : ℕ) : ℝ) ^ (-(2 - 1 / p)) := by
          dsimp [tailWeight]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = H ^ h * B ^ 2 * P ^ (h - 2) *
              ∑ k ∈ Finset.Ico N L,
                ((k + 1 : ℕ) : ℝ) ^ (-(2 - 1 / p)) := by
          rw [← Finset.mul_sum]
        _ ≤ H ^ h * B ^ 2 * P ^ (h - 2) *
              (p / (p - 1)) * (N : ℝ) ^ (-(1 - 1 / p)) := by
          by_cases hNL : N ≤ L
          · have hsum := sum_shift_rpow_tail_le hp N L hNpos hNL
            have hsum' :
                (∑ k ∈ Finset.Ico N L, ((k + 1 : ℕ) : ℝ) ^ (-(2 - 1 / p))) ≤
                  p / (p - 1) * (N : ℝ) ^ (-(1 - 1 / p)) := by
              simpa only [Nat.cast_add, Nat.cast_one] using hsum
            have hcoef : 0 ≤ H ^ h * B ^ 2 * P ^ (h - 2) :=
              mul_nonneg (mul_nonneg (pow_nonneg hHnonneg _) (sq_nonneg B))
                (pow_nonneg hP _)
            calc
              _ ≤ H ^ h * B ^ 2 * P ^ (h - 2) *
                    (p / (p - 1) * (N : ℝ) ^ (-(1 - 1 / p))) :=
                mul_le_mul_of_nonneg_left hsum' hcoef
              _ = _ := by ring
          · have hIco : Finset.Ico N L = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro k hk
              simp only [Finset.mem_Ico] at hk
              omega
            rw [hIco]
            simp only [Finset.sum_empty, mul_zero]
            positivity
        _ = H ^ h * B ^ 2 * P ^ (h - 2) * q * (N : ℝ) ^ (-δ) := by
          dsimp [q, δ]
    have hsumNorm :
        (∑ k ∈ Finset.range L,
          finiteLpNorm s p
            (fun x => replicaBoundaryVector (k + 1) I A f x /
              replicaExponentialWeight t x)) ≤
          H ^ h * P ^ h * q * (N : ℝ) ^ δ +
            H ^ h * B ^ 2 * P ^ (h - 2) * q * (N : ℝ) ^ (-δ) := by
      have hpoint : ∀ k ∈ Finset.range L,
          finiteLpNorm s p
              (fun x => replicaBoundaryVector (k + 1) I A f x /
                replicaExponentialWeight t x) ≤
            if k < N then shortWeight k else tailWeight k := by
        intro k hk
        have htime := finiteLpNorm_replicaBoundaryVector_time_two_bounds hh I hI
          A f hf s t ht (k + 1) (by omega) hp c hc hconvBounds
        have hklt : k < L := Finset.mem_range.mp hk
        have hkle : k + 1 ≤ L := by omega
        have harg : 2 * c * t ^ 2 * (k + 1 : ℕ) ≤ 2 * c * t ^ 2 * L := by
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hkle)
            (by positivity)
        have hKle : c * Real.exp (2 * c * t ^ 2 * (k + 1 : ℕ)) ≤ H := by
          dsimp [H]
          exact mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr harg) hc0
        have hKpow :
            (c * Real.exp (2 * c * t ^ 2 * (k + 1 : ℕ))) ^ h ≤ H ^ h :=
          pow_le_pow_left₀ (by positivity) hKle h
        by_cases hkN : k < N
        · rw [ite_eq_left hkN]
          calc
            _ ≤ (c * Real.exp (2 * c * t ^ 2 * (k + 1 : ℕ))) ^ h *
                ((k + 1 : ℕ) : ℝ) ^ (-1 / p) * P ^ h := htime.1
            _ ≤ shortWeight k := by
              calc
                _ = (c * Real.exp (2 * c * t ^ 2 * (k + 1 : ℕ))) ^ h *
                    (((k + 1 : ℕ) : ℝ) ^ (-1 / p) * P ^ h) := by ring
                _ ≤ H ^ h *
                    (((k + 1 : ℕ) : ℝ) ^ (-1 / p) * P ^ h) :=
                  mul_le_mul_of_nonneg_right hKpow
                    (mul_nonneg (Real.rpow_nonneg (by positivity) _)
                      (pow_nonneg hP _))
                _ = shortWeight k := by dsimp [shortWeight]; ring
        · rw [ite_eq_right hkN]
          calc
            _ ≤ (c * Real.exp (2 * c * t ^ 2 * (k + 1 : ℕ))) ^ h *
                ((k + 1 : ℕ) : ℝ) ^ (-(2 - 1 / p)) *
                B ^ 2 * P ^ (h - 2) := htime.2
            _ ≤ tailWeight k := by
              calc
                _ = (c * Real.exp (2 * c * t ^ 2 * (k + 1 : ℕ))) ^ h *
                    ((((k + 1 : ℕ) : ℝ) ^ (-(2 - 1 / p)) * B ^ 2) *
                      P ^ (h - 2)) := by ring
                _ ≤ H ^ h *
                    ((((k + 1 : ℕ) : ℝ) ^ (-(2 - 1 / p)) * B ^ 2) *
                      P ^ (h - 2)) :=
                  mul_le_mul_of_nonneg_right hKpow
                    (mul_nonneg
                      (mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg B))
                      (pow_nonneg hP _))
                _ = tailWeight k := by dsimp [tailWeight]; ring
      have hshortFilter :
          (∑ k ∈ Rshort, (if k < N then shortWeight k else tailWeight k)) =
            ∑ k ∈ Rshort, shortWeight k := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [((Finset.mem_filter.mp hk).2)]
      have htailFilter :
          (∑ k ∈ Rtail, (if k < N then shortWeight k else tailWeight k)) =
            ∑ k ∈ Rtail, tailWeight k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkN : ¬ k < N := not_lt_of_ge (Finset.mem_filter.mp hk).2
        simp [hkN]
      have htailOnRtail : (∑ k ∈ Rtail, tailWeight k) ≤
          H ^ h * B ^ 2 * P ^ (h - 2) * q * (N : ℝ) ^ (-δ) := by
        by_cases hNL : N ≤ L
        · have htailEq : Rtail = Finset.Ico N L := by
            ext k
            simp [Rtail]
            omega
          rw [htailEq]
          exact htailSum
        · have htailEmpty : Rtail = ∅ := by
            ext k
            constructor
            · intro hk
              have hk' := Finset.mem_filter.mp hk
              have hklt : k < L := Finset.mem_range.mp hk'.1
              omega
            · simp
          rw [htailEmpty]
          simp
          positivity
      have hshortNorm :
          (∑ k ∈ Rshort,
            finiteLpNorm s p (fun x => replicaBoundaryVector (k + 1) I A f x /
              replicaExponentialWeight t x)) ≤
          H ^ h * P ^ h * q * (N : ℝ) ^ δ := by
        calc
          _ ≤ ∑ k ∈ Rshort, if k < N then shortWeight k else tailWeight k := by
            apply Finset.sum_le_sum
            intro k hk
            exact hpoint k (Finset.mem_filter.mp hk).1
          _ = ∑ k ∈ Rshort, shortWeight k := hshortFilter
          _ ≤ _ := hshortSubset
      have htailNorm :
          (∑ k ∈ Rtail,
            finiteLpNorm s p (fun x => replicaBoundaryVector (k + 1) I A f x /
              replicaExponentialWeight t x)) ≤
          H ^ h * B ^ 2 * P ^ (h - 2) * q * (N : ℝ) ^ (-δ) := by
        calc
          _ ≤ ∑ k ∈ Rtail, if k < N then shortWeight k else tailWeight k := by
            apply Finset.sum_le_sum
            intro k hk
            exact hpoint k (Finset.mem_filter.mp hk).1
          _ = ∑ k ∈ Rtail, tailWeight k := htailFilter
          _ ≤ _ := htailOnRtail
      calc
        _ = (∑ k ∈ Rshort,
              finiteLpNorm s p (fun x => replicaBoundaryVector (k + 1) I A f x /
                replicaExponentialWeight t x)) +
            ∑ k ∈ Rtail,
              finiteLpNorm s p (fun x => replicaBoundaryVector (k + 1) I A f x /
                replicaExponentialWeight t x) := by
          rw [← Finset.sum_union hdis, ← hpartition]
        _ ≤ _ := add_le_add hshortNorm htailNorm
    have hsumdiv (x : LatticeConfiguration h) :
        hattedReplicaBoundaryVector L I A f x /
            replicaExponentialWeight t x =
          ∑ k ∈ Finset.range L,
            replicaBoundaryVector (k + 1) I A f x /
              replicaExponentialWeight t x := by
      unfold hattedReplicaBoundaryVector
      calc
        (∑ k ∈ Finset.range L, replicaBoundaryVector (k + 1) I A f x) /
            replicaExponentialWeight t x =
          (∑ k ∈ Finset.range L, replicaBoundaryVector (k + 1) I A f x) *
            (replicaExponentialWeight t x)⁻¹ := by rw [div_eq_mul_inv]
        _ = ∑ k ∈ Finset.range L,
            replicaBoundaryVector (k + 1) I A f x *
              (replicaExponentialWeight t x)⁻¹ := by rw [Finset.sum_mul]
        _ = ∑ k ∈ Finset.range L,
            replicaBoundaryVector (k + 1) I A f x /
              replicaExponentialWeight t x := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [div_eq_mul_inv]
    have htriangle := finiteLpNorm_sum_le (Finset.range L) s hp.le
      (fun k x => replicaBoundaryVector (k + 1) I A f x /
        replicaExponentialWeight t x)
    have hleft : finiteLpNorm s p
        (fun x => hattedReplicaBoundaryVector L I A f x /
          replicaExponentialWeight t x) ≤
          ∑ k ∈ Finset.range L,
            finiteLpNorm s p
              (fun x => replicaBoundaryVector (k + 1) I A f x /
                replicaExponentialWeight t x) := by
      calc
        _ = finiteLpNorm s p (fun x =>
            ∑ k ∈ Finset.range L,
              replicaBoundaryVector (k + 1) I A f x /
                replicaExponentialWeight t x) := by
          apply finiteLpNorm_abs_congr
          intro x hx
          exact congrArg abs (hsumdiv x)
        _ ≤ _ := htriangle
    have hNbalance :
        H ^ h * P ^ h * q * (N : ℝ) ^ δ +
          H ^ h * B ^ 2 * P ^ (h - 2) * q * (N : ℝ) ^ (-δ) ≤
        3 * H ^ h * q * B * P ^ (h - 1) := by
      have hshortBound : H ^ h * P ^ h * q * (N : ℝ) ^ δ ≤
          2 * H ^ h * q * B * P ^ (h - 1) := by
        calc
          _ ≤ H ^ h * P ^ h * q * (2 * r) := by
            exact mul_le_mul_of_nonneg_left hNδ
              (mul_nonneg (mul_nonneg (pow_nonneg hHnonneg _) (pow_nonneg hP _)) hq.le)
          _ = 2 * H ^ h * q * B * P ^ (h - 1) := by
            calc
              _ = 2 * H ^ h * q * (P ^ h * r) := by ring
              _ = 2 * H ^ h * q * (B * P ^ (h - 1)) := by rw [hbalanceShort]
              _ = _ := by ring
      have htailBound : H ^ h * B ^ 2 * P ^ (h - 2) * q * (N : ℝ) ^ (-δ) ≤
          H ^ h * q * B * P ^ (h - 1) := by
        calc
          _ ≤ H ^ h * B ^ 2 * P ^ (h - 2) * q * (1 / r) := by
            exact mul_le_mul_of_nonneg_left hNnegδ
              (mul_nonneg
                (mul_nonneg (mul_nonneg (pow_nonneg hHnonneg _) (sq_nonneg B))
                  (pow_nonneg hP _)) hq.le)
          _ = H ^ h * q * B * P ^ (h - 1) := by
            calc
              _ = H ^ h * q * (B ^ 2 * P ^ (h - 2) * (1 / r)) := by ring
              _ = H ^ h * q * (B * P ^ (h - 1)) := by rw [hbalanceTail]
              _ = _ := by ring
      exact add_le_add hshortBound htailBound |>.trans_eq (by ring)
    calc
      finiteLpNorm s p
          (fun x => hattedReplicaBoundaryVector L I A f x /
            replicaExponentialWeight t x) ≤
        ∑ k ∈ Finset.range L,
          finiteLpNorm s p
            (fun x => replicaBoundaryVector (k + 1) I A f x /
              replicaExponentialWeight t x) := hleft
      _ ≤ 3 * H ^ h * q * B * P ^ (h - 1) := hsumNorm.trans hNbalance
      _ ≤ C * Real.exp (C * t ^ 2 * L) * (p / (p - 1)) *
            (∑ y ∈ A, f y * Real.exp (t * ‖siteToPlane y‖)) *
            finiteLpNorm A p (fun y => f y * Real.exp (t * ‖siteToPlane y‖)) ^ (h - 1) := by
        have htimeCoeff : 3 * H ^ h ≤ C * Real.exp (C * t ^ 2 * L) := by
          have hcoeff : 3 * c ^ h ≤ C := le_max_left _ _
          have htime : 2 * c * (h : ℝ) ≤ C := le_max_right _ _
          have hexpPow (x : ℝ) (m : ℕ) : Real.exp x ^ m = Real.exp ((m : ℝ) * x) := by
            induction m with
            | zero => simp
            | succ m ih =>
              rw [pow_succ, ih, ← Real.exp_add]
              congr 1
              push_cast
              ring
          calc
            3 * H ^ h = 3 * c ^ h * Real.exp (2 * c * (h : ℝ) * t ^ 2 * L) := by
              dsimp [H]
              rw [mul_pow, hexpPow]
              have hExpArg :
                  (h : ℝ) * (2 * c * t ^ 2 * (L : ℝ)) =
                    2 * c * (h : ℝ) * t ^ 2 * (L : ℝ) := by ring
              rw [hExpArg]
              ring
            _ ≤ C * Real.exp (2 * c * (h : ℝ) * t ^ 2 * L) :=
              mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
            _ ≤ C * Real.exp (C * t ^ 2 * L) := by
              apply mul_le_mul_of_nonneg_left _ (by nlinarith [hC])
              apply Real.exp_le_exp.mpr
              have hTL : 0 ≤ t ^ 2 * (L : ℝ) := by positivity
              have htimeArg := mul_le_mul_of_nonneg_right htime hTL
              calc
                2 * c * (h : ℝ) * t ^ 2 * L =
                    (2 * c * (h : ℝ)) * (t ^ 2 * (L : ℝ)) := by ring
                _ ≤ C * (t ^ 2 * (L : ℝ)) := htimeArg
                _ = C * t ^ 2 * L := by ring
        calc
          _ = (3 * H ^ h) * (q * B * P ^ (h - 1)) := by ring
          _ ≤ (C * Real.exp (C * t ^ 2 * L)) *
                (q * B * P ^ (h - 1)) :=
            mul_le_mul_of_nonneg_right htimeCoeff
              (mul_nonneg (mul_nonneg hq.le hB) (pow_nonneg hP _))
          _ = C * Real.exp (C * t ^ 2 * L) *
                (p / (p - 1)) *
                (∑ y ∈ A, f y * Real.exp (t * ‖siteToPlane y‖)) *
                finiteLpNorm A p (fun y => f y * Real.exp (t * ‖siteToPlane y‖)) ^ (h - 1) := by
              dsimp [q, B, P, F]
              ring

end Critical2DKPZ.MomentBounds

end
