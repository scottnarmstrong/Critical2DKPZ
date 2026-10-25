/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25RunExpansion
public import Critical2DKPZ.MomentBounds.LatticePowerSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exponential weights on a replica collision stratum -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem exp_neg_le_rational_tail (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 256 / (1 + u ^ 2) ^ 2 := by
  have hlin : 1 + u / 4 ≤ Real.exp (u / 4) := by
    have h := Real.add_one_le_exp (u / 4)
    linarith
  have hexpPoly : (1 + u / 4) ^ 4 ≤ Real.exp u := by
    calc
      (1 + u / 4) ^ 4 ≤ Real.exp (u / 4) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hlin 4
      _ = Real.exp u := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hbase₁ : 1 + u ^ 2 ≤ (1 + u) ^ 2 := by nlinarith
  have hbase₂ : 1 + u ≤ 4 * (1 + u / 4) := by nlinarith
  have hpoly : (1 + u ^ 2) ^ 2 ≤ 256 * (1 + u / 4) ^ 4 := by
    calc
      (1 + u ^ 2) ^ 2 ≤ ((1 + u) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hbase₁ 2
      _ = (1 + u) ^ 4 := by ring
      _ ≤ (4 * (1 + u / 4)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase₂ 4
      _ = 256 * (1 + u / 4) ^ 4 := by norm_num [mul_pow]
  have hrecip : (Real.exp u)⁻¹ ≤ ((1 + u / 4) ^ 4)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos u) (pow_pos (by positivity) 4)).2 hexpPoly
  have hrecipPoly : ((1 + u / 4) ^ 4)⁻¹ ≤ 256 / (1 + u ^ 2) ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < (1 + u ^ 2) ^ 2)).2
    calc
      ((1 + u / 4) ^ 4)⁻¹ * (1 + u ^ 2) ^ 2 ≤
          ((1 + u / 4) ^ 4)⁻¹ * (256 * (1 + u / 4) ^ 4) :=
        mul_le_mul_of_nonneg_left hpoly (inv_nonneg.mpr (pow_pos (by positivity) 4).le)
      _ = 256 := by field_simp
  rw [Real.exp_neg]
  exact hrecip.trans hrecipPoly

private theorem tsum_exp_neg_norm_site_le (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    Summable (fun z : Site => Real.exp (-t * ‖siteToPlane z‖)) ∧
      (∑' z : Site, Real.exp (-t * ‖siteToPlane z‖)) ≤ 2304 / t ^ 2 := by
  let L : ℝ := (t ^ 2)⁻¹
  have hL : 1 ≤ L := by
    dsimp [L]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith
    simpa using (inv_le_inv₀ (by norm_num : 0 < (1 : ℝ)) (sq_pos_of_pos ht)).2 ht2
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨hkernel, hkernelBound⟩ :=
    lattice_rpow_sum_bound hL (by norm_num : (2 : ℝ) ≤ 2)
  let K : Site → ℝ := fun z => (L + ‖siteToPlane z‖ ^ 2) ^ (-2 : ℝ)
  let c : ℝ := 256 * ((t ^ 2)⁻¹) ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint (z : Site) : Real.exp (-t * ‖siteToPlane z‖) ≤ c * K z := by
    let x : ℝ := ‖siteToPlane z‖
    have hx : 0 ≤ x := norm_nonneg _
    have hden : 1 + (t * x) ^ 2 = t ^ 2 * (L + x ^ 2) := by
      dsimp [L]
      field_simp [ne_of_gt ht]
    have hK : (L + x ^ 2) ^ (-2 : ℝ) = ((L + x ^ 2) ^ 2)⁻¹ := by
      calc
        (L + x ^ 2) ^ (-2 : ℝ) = ((L + x ^ 2) ^ (2 : ℝ))⁻¹ :=
          Real.rpow_neg (by positivity : 0 ≤ L + x ^ 2) 2
        _ = ((L + x ^ 2) ^ (2 : ℕ))⁻¹ :=
          congrArg (fun y : ℝ => y⁻¹) (Real.rpow_natCast (L + x ^ 2) 2)
    have hfactor :
        1 / (1 + (t * x) ^ 2) ^ 2 = ((t ^ 2)⁻¹) ^ 2 * (L + x ^ 2) ^ (-2 : ℝ) := by
      rw [hden, hK]
      field_simp [ne_of_gt (sq_pos_of_pos ht),
        ne_of_gt (add_pos_of_pos_of_nonneg hLpos (sq_nonneg x))]
    have hpoly := exp_neg_le_rational_tail (t * x) (mul_nonneg ht.le hx)
    have hpoly' : Real.exp (-t * x) ≤ 256 / (1 + (t * x) ^ 2) ^ 2 := by
      simpa only [neg_mul] using hpoly
    calc
      Real.exp (-t * x) ≤ 256 / (1 + (t * x) ^ 2) ^ 2 := hpoly'
      _ = c * K z := by
        calc
          256 / (1 + (t * x) ^ 2) ^ 2 =
              256 * (1 / (1 + (t * x) ^ 2) ^ 2) := by ring
          _ = 256 * (((t ^ 2)⁻¹) ^ 2 * (L + x ^ 2) ^ (-2 : ℝ)) := by rw [hfactor]
          _ = c * K z := by
            dsimp [c, K, x]
            ring
  have hkernel' : Summable K := by simpa [K] using hkernel
  have hsumc : Summable (fun z : Site => c * K z) := hkernel'.mul_left c
  have hsum : Summable (fun z : Site => Real.exp (-t * ‖siteToPlane z‖)) :=
    hsumc.of_nonneg_of_le (fun z => (Real.exp_pos _).le) hpoint
  have hsumBound := hsum.tsum_le_tsum hpoint hsumc
  have hkernelBound' : (∑' z : Site, K z) ≤ 9 * L ^ (1 - (2 : ℝ)) := by
    simpa [K] using hkernelBound
  have htotal :
      (∑' z : Site, Real.exp (-t * ‖siteToPlane z‖)) ≤ c * (9 * L ^ (1 - (2 : ℝ))) := by
    calc
      _ ≤ ∑' z : Site, c * K z := hsumBound
      _ = c * ∑' z : Site, K z := tsum_mul_left
      _ ≤ c * (9 * L ^ (1 - (2 : ℝ))) := mul_le_mul_of_nonneg_left hkernelBound' hc
  refine ⟨hsum, ?_⟩
  dsimp [c, L] at htotal ⊢
  have hexp : (1 : ℝ) - 2 = -1 := by norm_num
  rw [hexp, Real.rpow_neg_one] at htotal
  field_simp at htotal ⊢
  nlinarith

private theorem replicaExponentialWeight_rpow_eq {h : ℕ} (t q : ℝ)
    (x : LatticeConfiguration h) :
    replicaExponentialWeight t x ^ q =
      ∏ i : Fin h, Real.exp (-(q * t * ‖siteToPlane (x i)‖)) := by
  have hweight : replicaExponentialWeight t x =
      Real.exp (∑ i : Fin h, -t * ‖siteToPlane (x i)‖) := by
    simp [replicaExponentialWeight, ← Real.exp_sum]
  have harg : (∑ i : Fin h, -t * ‖siteToPlane (x i)‖) * q =
      ∑ i : Fin h, -(q * t * ‖siteToPlane (x i)‖) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    replicaExponentialWeight t x ^ q =
        (Real.exp (∑ i : Fin h, -t * ‖siteToPlane (x i)‖)) ^ q := by rw [hweight]
    _ = Real.exp ((∑ i : Fin h, -t * ‖siteToPlane (x i)‖) * q) := by
      rw [← Real.exp_mul]
    _ = Real.exp (∑ i : Fin h, -(q * t * ‖siteToPlane (x i)‖)) := by rw [harg]
    _ = ∏ i : Fin h, Real.exp (-(q * t * ‖siteToPlane (x i)‖)) := by
      rw [← Real.exp_sum]

private theorem finite_sum_exp_q_le_site_sum (B : Finset Site) (t q : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hq : 1 ≤ q) :
    ∑ z ∈ B, Real.exp (-(q * t * ‖siteToPlane z‖)) ≤ 2304 / t ^ 2 := by
  obtain ⟨hsum, hbound⟩ := tsum_exp_neg_norm_site_le t ht ht1
  calc
    ∑ z ∈ B, Real.exp (-(q * t * ‖siteToPlane z‖)) ≤
        ∑ z ∈ B, Real.exp (-t * ‖siteToPlane z‖) := by
      apply Finset.sum_le_sum
      intro z hz
      apply Real.exp_le_exp.mpr
      have hnorm : 0 ≤ ‖siteToPlane z‖ := norm_nonneg _
      have hmul : 0 ≤ t * ‖siteToPlane z‖ := mul_nonneg ht.le hnorm
      have hqmul : t * ‖siteToPlane z‖ ≤ q * (t * ‖siteToPlane z‖) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hq) hmul]
      nlinarith
    _ ≤ ∑' z : Site, Real.exp (-t * ‖siteToPlane z‖) :=
      hsum.sum_le_tsum B (fun z _ => (Real.exp_pos (-t * ‖siteToPlane z‖)).le)
    _ ≤ 2304 / t ^ 2 := hbound

private theorem collision_weight_power_sum_le {h : ℕ} (t q : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hq : 1 ≤ q)
    (s : Finset (LatticeConfiguration h)) (J : ReplicaPartition h) (hJ : J ≠ ⊥) :
    ∑ x ∈ s,
      |replicaExponentialWeight t x * collisionIndicator J x| ^ q ≤
        (2304 / t ^ 2) ^ (h - 1 : ℕ) := by
  classical
  obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete J hJ
  let a : Fin h := α.val.1
  let b : Fin h := α.val.2
  have hab : a ≠ b := (ne_of_lt α.property)
  have hJab : J.r a b := hα
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let E : Finset (LatticeConfiguration h) := s.filter fun x => IsCollisionConfiguration J x
  have hsumFilter :
      (∑ x ∈ s,
        |replicaExponentialWeight t x * collisionIndicator J x| ^ q) =
      ∑ x ∈ E, replicaExponentialWeight t x ^ q := by
    unfold E
    calc
      _ = ∑ x ∈ s,
          if IsCollisionConfiguration J x then replicaExponentialWeight t x ^ q else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hcollision : IsCollisionConfiguration J x
        · simp [collisionIndicator, hcollision,
            abs_of_nonneg (replicaExponentialWeight_pos t x).le]
        · simp [collisionIndicator, hcollision, Real.zero_rpow hqpos.ne']
      _ = ∑ x ∈ s.filter (fun x => IsCollisionConfiguration J x),
          replicaExponentialWeight t x ^ q := by rw [← Finset.sum_filter]
  let B : Finset Site := s.biUnion fun x => Finset.univ.image x
  have hB (x : LatticeConfiguration h) (hx : x ∈ s) (i : Fin h) : x i ∈ B := by
    exact Finset.mem_biUnion.mpr
      ⟨x, hx, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let u : LatticeConfiguration h → LatticeConfiguration h := fun x => Function.update x b 0
  let T : Fin h → Finset Site := fun i => if i = b then {0} else B
  let G : LatticeConfiguration h → ℝ := fun y =>
    ∏ i : Fin h, if i = b then 1 else Real.exp (-(q * t * ‖siteToPlane (y i)‖))
  have hcollisionPair (x : LatticeConfiguration h) (hx : x ∈ E) : x a = x b :=
    (Finset.mem_filter.mp hx).2.1 a b hJab
  have hu_inj : Set.InjOn u E := by
    intro x hx y hy hxy
    funext i
    by_cases hib : i = b
    · subst i
      have hxyA : x a = y a := by
        have h := congrFun hxy a
        simpa [u, hab] using h
      exact (hcollisionPair x hx).symm.trans (hxyA.trans (hcollisionPair y hy))
    · have h := congrFun hxy i
      simpa [u, hib] using h
  have himage_sum :
      (∑ x ∈ E, G (u x)) = ∑ y ∈ E.image u, G y := by
    apply Finset.sum_bij (fun x _ => u x)
    · intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · intro x hx y hy heq
      exact hu_inj hx hy heq
    · intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · intro x hx
      rfl
  have hu_mem_pi (x : LatticeConfiguration h) (hx : x ∈ E) :
      u x ∈ Fintype.piFinset T := by
    apply Fintype.mem_piFinset.mpr
    intro i
    by_cases hib : i = b
    · subst i
      simp [u, T]
    · simp [u, T, hib]
      exact hB x (Finset.mem_filter.mp hx).1 i
  have himage_subset : E.image u ⊆ Fintype.piFinset T := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    exact hu_mem_pi x hx
  have hG_nonneg (y : LatticeConfiguration h) : 0 ≤ G y := by
    apply Finset.prod_nonneg
    intro i hi
    by_cases hib : i = b
    · simp [hib]
    · simp [hib]
      positivity
  have hcoord : ∑ z ∈ B, Real.exp (-(q * t * ‖siteToPlane z‖)) ≤ 2304 / t ^ 2 :=
    finite_sum_exp_q_le_site_sum B t q ht ht1 hq
  have hG_sum :
      (∑ y ∈ Fintype.piFinset T, G y) =
        ∏ i : Fin h, ∑ z ∈ T i,
          if i = b then 1 else Real.exp (-(q * t * ‖siteToPlane z‖)) := by
    dsimp [G]
    exact (Finset.prod_univ_sum T fun i z =>
      if i = b then 1 else Real.exp (-(q * t * ‖siteToPlane z‖))).symm
  have hcoordT (i : Fin h) :
      (∑ z ∈ T i,
        if i = b then 1 else Real.exp (-(q * t * ‖siteToPlane z‖))) ≤
          if i = b then 1 else 2304 / t ^ 2 := by
    by_cases hib : i = b
    · subst i
      simp [T]
    · simp [T, hib]
      exact hcoord
  have hcoordT_nonneg (i : Fin h) :
      0 ≤ ∑ z ∈ T i,
        if i = b then 1 else Real.exp (-(q * t * ‖siteToPlane z‖)) := by
    apply Finset.sum_nonneg
    intro z hz
    by_cases hib : i = b
    · simp [hib]
    · simp [hib]
      positivity
  have hprod_coord :
      (∏ i : Fin h, ∑ z ∈ T i,
        if i = b then 1 else Real.exp (-(q * t * ‖siteToPlane z‖))) ≤
        ∏ i : Fin h, if i = b then 1 else 2304 / t ^ 2 := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact hcoordT_nonneg i
    · intro i hi
      exact hcoordT i
  have hbmem : b ∈ (Finset.univ : Finset (Fin h)) := Finset.mem_univ b
  have hprod_const :
      (∏ i : Fin h, if i = b then 1 else 2304 / t ^ 2) =
        (2304 / t ^ 2) ^ (h - 1 : ℕ) := by
    calc
      _ = ∏ i : Fin h, if i ∈ Finset.univ.erase b then 2304 / t ^ 2 else 1 := by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hib : i = b <;> simp [hib]
      _ = ∏ i ∈ Finset.univ.erase b, (2304 / t ^ 2) := Finset.prod_ite_mem_eq _ _
      _ = (2304 / t ^ 2) ^ (h - 1 : ℕ) := by
        simp [Finset.card_erase_of_mem hbmem, div_pow]
  have hweight_le_G (x : LatticeConfiguration h) (hx : x ∈ E) :
      replicaExponentialWeight t x ^ q ≤ G (u x) := by
    have hdrop : Real.exp (-(q * t * ‖siteToPlane (x b)‖)) ≤ 1 := by
      have hqtn : 0 ≤ q * t * ‖siteToPlane (x b)‖ := by positivity
      calc
        _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by nlinarith)
        _ = 1 := by simp
    have hrest_nonneg :
        0 ≤ ∏ i ∈ Finset.univ.erase b,
          Real.exp (-(q * t * ‖siteToPlane (x i)‖)) :=
      Finset.prod_nonneg fun i hi => (Real.exp_pos _).le
    have hweight_split :
        replicaExponentialWeight t x ^ q =
          Real.exp (-(q * t * ‖siteToPlane (x b)‖)) *
            ∏ i ∈ Finset.univ.erase b,
              Real.exp (-(q * t * ‖siteToPlane (x i)‖)) := by
      rw [replicaExponentialWeight_rpow_eq]
      exact (Finset.mul_prod_erase Finset.univ
        (fun i => Real.exp (-(q * t * ‖siteToPlane (x i)‖))) hbmem).symm
    have hG_split : G (u x) =
        ∏ i ∈ Finset.univ.erase b,
          Real.exp (-(q * t * ‖siteToPlane (x i)‖)) := by
      calc
        G (u x) = ∏ i : Fin h,
            if i ∈ Finset.univ.erase b then
              Real.exp (-(q * t * ‖siteToPlane (x i)‖)) else 1 := by
          unfold G
          apply Finset.prod_congr rfl
          intro i hi
          by_cases hib : i = b
          · subst i
            simp
          · simp [u, hib]
        _ = ∏ i ∈ Finset.univ.erase b,
            Real.exp (-(q * t * ‖siteToPlane (x i)‖)) := Finset.prod_ite_mem_eq _ _
    calc
      replicaExponentialWeight t x ^ q ≤
          1 * ∏ i ∈ Finset.univ.erase b,
            Real.exp (-(q * t * ‖siteToPlane (x i)‖)) := by
        rw [hweight_split]
        exact mul_le_mul_of_nonneg_right hdrop hrest_nonneg
      _ = G (u x) := by rw [hG_split]; simp
  have hcollision_sum :
      (∑ x ∈ E, replicaExponentialWeight t x ^ q) ≤
        (2304 / t ^ 2) ^ (h - 1 : ℕ) := by
    calc
      _ ≤ ∑ x ∈ E, G (u x) :=
        Finset.sum_le_sum fun x hx => hweight_le_G x hx
      _ = ∑ y ∈ E.image u, G y := himage_sum
      _ ≤ ∑ y ∈ Fintype.piFinset T, G y :=
        Finset.sum_le_sum_of_subset_of_nonneg himage_subset fun y hy _ => hG_nonneg y
      _ = ∏ i : Fin h, ∑ z ∈ T i,
          if i = b then 1 else Real.exp (-(q * t * ‖siteToPlane z‖)) := hG_sum
      _ ≤ ∏ i : Fin h, if i = b then 1 else 2304 / t ^ 2 := hprod_coord
      _ = (2304 / t ^ 2) ^ (h - 1 : ℕ) := hprod_const
  calc
    _ = ∑ x ∈ E, replicaExponentialWeight t x ^ q := hsumFilter
    _ ≤ (2304 / t ^ 2) ^ (h - 1 : ℕ) := hcollision_sum

/-- Multiplication by a weighted collision indicator satisfies the finite Lᵖ bound. -/
theorem finiteLpNorm_weight_mul_collisionIndicator_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h : ℕ, ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ q : ℝ, 1 ≤ q →
      ∀ (s : Finset (LatticeConfiguration h)) (J : ReplicaPartition h), J ≠ ⊥ →
        finiteLpNorm s q (fun x => replicaExponentialWeight t x * collisionIndicator J x) ≤
          (C / t ^ 2) ^ (((h : ℝ) - 1) / q) := by
  refine ⟨2304, by norm_num, ?_⟩
  intro h t ht ht1 q hq s J hJ
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hSpos : 0 < 2304 / t ^ 2 := div_pos (by norm_num) (sq_pos_of_pos ht)
  have hsum := collision_weight_power_sum_le t q ht ht1 hq s J hJ
  have hcastSub : ((h - 1 : ℕ) : ℝ) = (h : ℝ) - 1 := by
    rw [Nat.cast_sub (by
      obtain ⟨α, hα⟩ := exists_collisionPair_of_ne_discrete J hJ
      have hab := α.property
      omega)]
    norm_num
  have hsum' :
      (∑ x ∈ s,
        |replicaExponentialWeight t x * collisionIndicator J x| ^ q) ≤
        (2304 / t ^ 2) ^ ((h : ℝ) - 1) := by
    calc
      _ ≤ (2304 / t ^ 2) ^ (h - 1 : ℕ) := hsum
      _ = (2304 / t ^ 2) ^ ((h : ℝ) - 1) := by
        rw [← Real.rpow_natCast, hcastSub]
  have hroot := Real.rpow_le_rpow
    (Finset.sum_nonneg fun x hx => Real.rpow_nonneg (abs_nonneg _) _)
    hsum' (by positivity : 0 ≤ 1 / q)
  calc
    finiteLpNorm s q (fun x => replicaExponentialWeight t x * collisionIndicator J x) =
        (∑ x ∈ s,
          |replicaExponentialWeight t x * collisionIndicator J x| ^ q) ^ (1 / q) := rfl
    _ ≤ ((2304 / t ^ 2) ^ ((h : ℝ) - 1)) ^ (1 / q) := hroot
    _ = (2304 / t ^ 2) ^ (((h : ℝ) - 1) / q) := by
      rw [← Real.rpow_mul hSpos.le]
      congr 1
      field_simp [ne_of_gt hqpos]

end Critical2DKPZ.MomentBounds

end
