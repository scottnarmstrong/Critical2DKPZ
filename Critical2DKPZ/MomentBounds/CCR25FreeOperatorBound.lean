/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25GreenDecay
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Critical2DKPZ.MomentBounds.LZ21Finite
public import Critical2DKPZ.MomentBounds.LZ21Absolute
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # Exponentially weighted finite free-replica operators -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem siteToPlane_sub (x y : Site) :
    Critical2DKPZ.siteToPlane (y - x) =
      Critical2DKPZ.siteToPlane y - Critical2DKPZ.siteToPlane x := by
  ext i
  simp [Critical2DKPZ.siteToPlane]

private theorem replica_displacement_sum_norm_le_sqrt_energy {h : ℕ}
    (x y : LatticeConfiguration h) :
    (∑ i : Fin h, ‖Critical2DKPZ.siteToPlane (y i - x i)‖) ≤
      (h : ℝ) * Real.sqrt (replicaDistanceEnergy x y) := by
  have hE : 0 ≤ replicaDistanceEnergy x y := replicaDistanceEnergy_nonneg x y
  have hcoord (i : Fin h) :
      ‖Critical2DKPZ.siteToPlane (y i - x i)‖ ≤
        Real.sqrt (replicaDistanceEnergy x y) := by
    have henergy :
        replicaCoordinateEnergy x y i ≤ replicaDistanceEnergy x y := by
      unfold replicaDistanceEnergy
      exact Finset.single_le_sum
        (fun j hj => sq_nonneg (‖Critical2DKPZ.siteToPlane (y j - x j)‖))
        (Finset.mem_univ i)
    have hsqrt := Real.sqrt_le_sqrt henergy
    simpa [replicaCoordinateEnergy, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using hsqrt
  calc
    _ ≤ ∑ i : Fin h, Real.sqrt (replicaDistanceEnergy x y) :=
      Finset.sum_le_sum fun i hi => hcoord i
    _ = (h : ℝ) * Real.sqrt (replicaDistanceEnergy x y) := by simp

private theorem replica_exponentialWeight_eq_exp_sum {h : ℕ} (t : ℝ)
    (x : LatticeConfiguration h) :
    replicaExponentialWeight t x =
      Real.exp (∑ i : Fin h, -t * ‖Critical2DKPZ.siteToPlane (x i)‖) := by
  simp [replicaExponentialWeight, ← Real.exp_sum]

/-- The ratio of replica exponential weights is controlled by the displacement weight. -/
theorem replica_exponentialWeight_ratio_le {h : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (x y : LatticeConfiguration h) :
    replicaExponentialWeight t x / replicaExponentialWeight t y ≤
      Real.exp (t * ∑ i : Fin h,
        ‖Critical2DKPZ.siteToPlane (y i - x i)‖) := by
  have hnorm (i : Fin h) :
      ‖Critical2DKPZ.siteToPlane (y i)‖ -
          ‖Critical2DKPZ.siteToPlane (x i)‖ ≤
        ‖Critical2DKPZ.siteToPlane (y i - x i)‖ := by
    rw [siteToPlane_sub]
    exact norm_sub_norm_le _ _
  have harg :
      (∑ i : Fin h, -t * ‖Critical2DKPZ.siteToPlane (x i)‖) -
          ∑ i : Fin h, -t * ‖Critical2DKPZ.siteToPlane (y i)‖ =
        t * ∑ i : Fin h,
          (‖Critical2DKPZ.siteToPlane (y i)‖ -
            ‖Critical2DKPZ.siteToPlane (x i)‖) := by
    calc
      (∑ i : Fin h, -t * ‖Critical2DKPZ.siteToPlane (x i)‖) -
          ∑ i : Fin h, -t * ‖Critical2DKPZ.siteToPlane (y i)‖ =
          ∑ i : Fin h,
            (-t * ‖Critical2DKPZ.siteToPlane (x i)‖ -
              -t * ‖Critical2DKPZ.siteToPlane (y i)‖) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin h, t *
          (‖Critical2DKPZ.siteToPlane (y i)‖ -
            ‖Critical2DKPZ.siteToPlane (x i)‖) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = t * ∑ i : Fin h,
          (‖Critical2DKPZ.siteToPlane (y i)‖ -
            ‖Critical2DKPZ.siteToPlane (x i)‖) := by
        rw [Finset.mul_sum]
  have hsum :
      t * ∑ i : Fin h,
          (‖Critical2DKPZ.siteToPlane (y i)‖ -
            ‖Critical2DKPZ.siteToPlane (x i)‖) ≤
        t * ∑ i : Fin h,
          ‖Critical2DKPZ.siteToPlane (y i - x i)‖ :=
    mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i hi => hnorm i) ht
  rw [replica_exponentialWeight_eq_exp_sum, replica_exponentialWeight_eq_exp_sum,
    ← Real.exp_sub, harg]
  exact Real.exp_le_exp.mpr hsum

private theorem gaussian_exponent_absorbs_weight {h : ℕ} {t c L E : ℝ}
    (hc : 0 < c) (hL : 0 < L) (hE : 0 ≤ E) :
    t * (h : ℝ) * Real.sqrt E - c * E / (2 * L) ≤
      t ^ 2 * (h : ℝ) ^ 2 * L / c := by
  let u : ℝ := Real.sqrt (c * E / (4 * L))
  let v : ℝ := t * (h : ℝ) * Real.sqrt (L / c)
  have hu2 : u ^ 2 = c * E / (4 * L) := by
    dsimp [u]
    exact Real.sq_sqrt (div_nonneg (mul_nonneg hc.le hE) (by positivity))
  have hv2 : v ^ 2 = t ^ 2 * (h : ℝ) ^ 2 * (L / c) := by
    dsimp [v]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  have hroot :
      Real.sqrt (c * E / (4 * L)) * Real.sqrt (L / c) = Real.sqrt E / 2 := by
    rw [← Real.sqrt_mul (div_nonneg (mul_nonneg hc.le hE) (by positivity))]
    field_simp [ne_of_gt hc, ne_of_gt hL]
    norm_num
  have huv : 2 * (u * v) = t * (h : ℝ) * Real.sqrt E := by
    dsimp [u, v]
    calc
      2 * (Real.sqrt (c * E / (4 * L)) *
          (t * (h : ℝ) * Real.sqrt (L / c))) =
          2 * (t * (h : ℝ)) *
            (Real.sqrt (c * E / (4 * L)) * Real.sqrt (L / c)) := by ring
      _ = t * (h : ℝ) * Real.sqrt E := by rw [hroot]; ring
  have hYoung : 2 * (u * v) ≤ u ^ 2 + v ^ 2 := by
    nlinarith only [sq_nonneg (u - v)]
  rw [hu2, hv2, huv] at hYoung
  have hv2' : t ^ 2 * (h : ℝ) ^ 2 * (L / c) =
      t ^ 2 * (h : ℝ) ^ 2 * L / c := by ring
  rw [hv2'] at hYoung
  have hEterm : 0 ≤ c * E / (4 * L) :=
    div_nonneg (mul_nonneg hc.le hE) (by positivity)
  have hhalf : c * E / (2 * L) = 2 * (c * E / (4 * L)) := by
    field_simp [ne_of_gt hL]
    ring
  rw [hhalf]
  linarith


/-- Uniform version of the weighted Green bound, with the cutoff dependence
absorbed into `exp(C t² L)` as required by CCR25 Proposition 4.23. -/
theorem weightedKernel_hattedFreeReplicaKernel_le_greenKernel {h : ℕ} (hh : 2 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ L : ℕ,
      ∀ (I J : ReplicaPartition h) (z x : LatticeConfiguration h),
        weightedKernel (replicaExponentialWeight t) (hattedFreeReplicaKernel L I J) z x ≤
          C * Real.exp (C * t ^ 2 * L) * replicaGreenKernel z x := by
  obtain ⟨Cwalk, cwalk, hCwalk, hcwalk, hgauss⟩ :=
    hattedFreeReplicaKernel_gaussian_green_bound (h := h) hh
  let D : ℝ := 2 * Cwalk ^ h * (1 + 2 * (h : ℝ) / cwalk) ^ (h - 1)
  let α : ℝ := (h : ℝ) ^ 2 / cwalk
  let C : ℝ := max 1 (max D α)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDC : D ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hαC : α ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, ?_, ?_⟩
  · dsimp [C]
    exact le_max_left _ _
  · intro t ht L I J z x
    by_cases hL : L = 0
    · subst L
      have hCpos : 0 ≤ C := by
        dsimp [C]
        exact le_trans (by norm_num) (le_max_left _ _)
      have hbase : 0 ≤ C * replicaGreenKernel z x :=
        mul_nonneg hCpos (replicaGreenKernel_pos z x).le
      simpa [weightedKernel, hattedFreeReplicaKernel] using hbase
    · have hLpos : 0 < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_ne_zero hL)
      let E : ℝ := replicaDistanceEnergy z x
      have hE : 0 ≤ E := by dsimp [E]; exact replicaDistanceEnergy_nonneg z x
      have hkernel := hgauss L I J z x
      have hratio := replica_exponentialWeight_ratio_le ht z x
      have hsumNorm := replica_displacement_sum_norm_le_sqrt_energy z x
      have hratioBound :
          replicaExponentialWeight t z / replicaExponentialWeight t x *
              Real.exp (-cwalk * E / (2 * (L : ℝ))) ≤
            Real.exp (α * (t ^ 2 * (L : ℝ))) := by
        have hweight :
            t * ∑ i : Fin h, ‖Critical2DKPZ.siteToPlane (x i - z i)‖ ≤
              t * (h : ℝ) * Real.sqrt E := by
          dsimp [E]
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hsumNorm ht
        have hYoung := gaussian_exponent_absorbs_weight (h := h) (t := t)
          (c := cwalk) (L := (L : ℝ)) (E := E) hcwalk hLpos hE
        have harg :
            t * (h : ℝ) * Real.sqrt E - cwalk * E / (2 * (L : ℝ)) ≤
              α * (t ^ 2 * (L : ℝ)) := by
          dsimp [α]
          calc
            _ ≤ t ^ 2 * (h : ℝ) ^ 2 * (L : ℝ) / cwalk := hYoung
            _ = (h : ℝ) ^ 2 / cwalk * (t ^ 2 * (L : ℝ)) := by ring
        calc
          _ ≤ Real.exp (t * (h : ℝ) * Real.sqrt E) *
                Real.exp (-cwalk * E / (2 * (L : ℝ))) := by
            calc
              _ ≤ Real.exp (t * ∑ i : Fin h,
                    ‖Critical2DKPZ.siteToPlane (x i - z i)‖) *
                    Real.exp (-cwalk * E / (2 * (L : ℝ))) :=
                mul_le_mul_of_nonneg_right hratio (Real.exp_nonneg _)
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (Real.exp_le_exp.mpr hweight) (Real.exp_nonneg _)
          _ = Real.exp (t * (h : ℝ) * Real.sqrt E - cwalk * E / (2 * (L : ℝ))) := by
            rw [← Real.exp_add]
            congr 1
            ring
          _ ≤ Real.exp (α * (t ^ 2 * (L : ℝ))) := Real.exp_le_exp.mpr harg
      have hgreen : 0 ≤ replicaGreenKernel z x := (replicaGreenKernel_pos z x).le
      have hratioPos : 0 < replicaExponentialWeight t z / replicaExponentialWeight t x :=
        div_pos (replicaExponentialWeight_pos t z) (replicaExponentialWeight_pos t x)
      have hkernel' :
          hattedFreeReplicaKernel L I J z x ≤
            D * Real.exp (-cwalk * E / (2 * (L : ℝ))) * replicaGreenKernel z x := by
        simpa [D, E, mul_assoc] using hkernel
      have hweighted :
          replicaExponentialWeight t z / replicaExponentialWeight t x *
              hattedFreeReplicaKernel L I J z x ≤
            D * Real.exp (α * (t ^ 2 * (L : ℝ))) * replicaGreenKernel z x := by
        calc
          _ ≤ (replicaExponentialWeight t z / replicaExponentialWeight t x) *
                (D * Real.exp (-cwalk * E / (2 * (L : ℝ))) * replicaGreenKernel z x) :=
            mul_le_mul_of_nonneg_left hkernel' hratioPos.le
          _ = D * (replicaExponentialWeight t z / replicaExponentialWeight t x *
                Real.exp (-cwalk * E / (2 * (L : ℝ)))) * replicaGreenKernel z x := by ring
          _ ≤ _ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hratioBound hD) hgreen
      have hu : 0 ≤ t ^ 2 * (L : ℝ) := mul_nonneg (sq_nonneg t) (Nat.cast_nonneg L)
      have hexp : Real.exp (α * (t ^ 2 * (L : ℝ))) ≤
          Real.exp (C * t ^ 2 * L) := by
        apply Real.exp_le_exp.mpr
        calc
          α * (t ^ 2 * (L : ℝ)) ≤ C * (t ^ 2 * (L : ℝ)) :=
            mul_le_mul_of_nonneg_right hαC hu
          _ = C * t ^ 2 * L := by ring
      have hcoeff : D * Real.exp (α * (t ^ 2 * (L : ℝ))) ≤
          C * Real.exp (C * t ^ 2 * L) := by
        calc
          _ ≤ C * Real.exp (α * (t ^ 2 * (L : ℝ))) :=
            mul_le_mul_of_nonneg_right hDC (Real.exp_nonneg _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by dsimp [C]; positivity)
      have hkernelWeight :
          weightedKernel (replicaExponentialWeight t)
              (hattedFreeReplicaKernel L I J) z x =
            replicaExponentialWeight t z / replicaExponentialWeight t x *
              hattedFreeReplicaKernel L I J z x := by
        simp only [weightedKernel]
        field_simp [ne_of_gt (replicaExponentialWeight_pos t x)]
      rw [hkernelWeight]
      exact hweighted.trans (mul_le_mul_of_nonneg_right hcoeff hgreen)

/-! The LZ21 bilinear estimate is the finite-support operator form needed by
CCR25: the Gaussian weight conjugation contributes only the explicit
cutoff-uniform factor proved above. -/



/-- A finite operator norm follows from its absolute bilinear estimate by
duality of counting `ℓᵖ` norms. -/
private theorem finiteLpNorm_kernelApply_le_of_bilinearBound {α : Type*} [DecidableEq α]
    (s u : Finset α) (K : α → α → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    {p q : ℝ} (hpq : p.HolderConjugate q) (B : ℝ) (hB : 0 ≤ B)
    (hbilinear : ∀ g f : α → ℝ,
      (∑ x ∈ s, ∑ y ∈ u, |g x| * K x y * |f y|) ≤
        B * finiteLpNorm s p g * finiteLpNorm u q f)
    (f : α → ℝ) :
    finiteLpNorm s q (fun x => ∑ y ∈ u, K x y * f y) ≤
      B * finiteLpNorm u q f := by
  classical
  let F : α → ℝ := fun x => ∑ y ∈ u, K x y * |f y|
  have hFnonneg (x : α) : 0 ≤ F x := by
    dsimp [F]
    exact Finset.sum_nonneg fun y hy => mul_nonneg (hK x y) (abs_nonneg _)
  have hsumAbs (x : α) :
      |∑ y ∈ u, K x y * f y| ≤ F x := by
    calc
      |∑ y ∈ u, K x y * f y| ≤ ∑ y ∈ u, |K x y * f y| := Finset.abs_sum_le_sum_abs _ _
      _ = F x := by
        dsimp [F]
        apply Finset.sum_congr rfl
        intro y hy
        rw [abs_mul, abs_of_nonneg (hK x y)]
  have hsumPow :
      (∑ x ∈ s, |∑ y ∈ u, K x y * f y| ^ q) ≤ ∑ x ∈ s, F x ^ q := by
    apply Finset.sum_le_sum
    intro x hx
    exact Real.rpow_le_rpow (abs_nonneg _) (hsumAbs x) hpq.symm.pos.le
  have hsumPow' :
      (∑ x ∈ s, |∑ y ∈ u, K x y * f y| ^ q) ≤ ∑ x ∈ s, |F x| ^ q := by
    apply le_trans hsumPow
    apply Finset.sum_le_sum
    intro x hx
    rw [abs_of_nonneg (hFnonneg x)]
  have hnormAbs :
      finiteLpNorm s q (fun x => ∑ y ∈ u, K x y * f y) ≤ finiteLpNorm s q F := by
    unfold finiteLpNorm
    apply Real.rpow_le_rpow
    · exact Finset.sum_nonneg fun x hx => Real.rpow_nonneg (abs_nonneg _) _
    · exact hsumPow'
    · exact (one_div_pos.mpr hpq.symm.pos).le
  let Fnn : α → NNReal := fun x => ⟨F x, hFnonneg x⟩
  obtain ⟨v, hv, hpair⟩ := (NNReal.isGreatest_Lp s Fnn hpq.symm).1
  have hvNormNN : (∑ x ∈ s, v x ^ p) ^ (1 / p) ≤ 1 :=
    NNReal.rpow_le_one hv (le_of_lt (one_div_pos.mpr hpq.pos))
  have hvNorm : finiteLpNorm s p (fun x => (v x : ℝ)) ≤ 1 := by
    unfold finiteLpNorm
    have hsum : (∑ x ∈ s, |(v x : ℝ)| ^ p) = ((∑ x ∈ s, v x ^ p : NNReal) : ℝ) := by simp
    rw [hsum]
    exact_mod_cast hvNormNN
  have hpairReal :
      (∑ x ∈ s, F x * (v x : ℝ)) = (∑ x ∈ s, F x ^ q) ^ (1 / q) := by
    have hpairCast := congrArg (fun r : NNReal => (r : ℝ)) hpair
    simp only [NNReal.coe_sum, NNReal.coe_rpow, Fnn] at hpairCast
    exact hpairCast
  have hpairSum :
      (∑ x ∈ s, ∑ y ∈ u, |(v x : ℝ)| * K x y * |f y|) =
        ∑ x ∈ s, F x * (v x : ℝ) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [abs_of_nonneg (NNReal.coe_nonneg (v x))]
    dsimp [F]
    calc
      (∑ y ∈ u, (v x : ℝ) * K x y * |f y|) =
          ∑ y ∈ u, (v x : ℝ) * (K x y * |f y|) := by
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (v x : ℝ) * ∑ y ∈ u, K x y * |f y| := by rw [Finset.mul_sum]
      _ = (∑ y ∈ u, K x y * |f y|) * (v x : ℝ) := by ring
  have hbilinearV := hbilinear (fun x => (v x : ℝ)) f
  have hnormF : finiteLpNorm s q F ≤ B * finiteLpNorm u q f := by
    calc
      finiteLpNorm s q F = ∑ x ∈ s, F x * (v x : ℝ) := by
        unfold finiteLpNorm
        simp_rw [abs_of_nonneg (hFnonneg _)]
        exact hpairReal.symm
      _ = ∑ x ∈ s, ∑ y ∈ u, |(v x : ℝ)| * K x y * |f y| := hpairSum.symm
      _ ≤ B * finiteLpNorm s p (fun x => (v x : ℝ)) * finiteLpNorm u q f := hbilinearV
      _ ≤ B * 1 * finiteLpNorm u q f := by
        calc
          _ = (B * finiteLpNorm s p (fun x => (v x : ℝ))) * finiteLpNorm u q f := by ring
          _ ≤ (B * 1) * finiteLpNorm u q f :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvNorm hB)
              (finiteLpNorm_nonneg u q f)
          _ = _ := by ring
      _ = B * finiteLpNorm u q f := by ring
  exact hnormAbs.trans hnormF

/-- CCR25 Proposition 4.23's weighted free-operator bound. The walk kernel
estimate supplies the exponential cutoff factor; the finite LZ21 inequality
supplies the `q · q/(q−1)` factor. -/
theorem finiteLpNorm_weighted_hattedFreeReplicaKernel_le (h : ℕ) (hh : 3 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, 0 ≤ t → ∀ L : ℕ, ∀ q : ℝ, 1 < q →
      ∀ (s : Finset (LatticeConfiguration h)) (I J : ReplicaPartition h),
        I ≠ ⊥ → J ≠ ⊥ → I ≠ J → ∀ f : LatticeConfiguration h → ℝ,
          finiteLpNorm s q (finiteKernelApply s
              (weightedKernel (replicaExponentialWeight t) (hattedFreeReplicaKernel L I J)) f) ≤
            C * Real.exp (C * t ^ 2 * L) * q * (q / (q - 1)) * finiteLpNorm s q f := by
  obtain ⟨Cwalk, hCwalk, hkernelBound⟩ :=
    weightedKernel_hattedFreeReplicaKernel_le_greenKernel (h := h) (by omega)
  let B0 : ℝ := 4 ^ ((h : ℝ) - 1) * 4 * (9 : ℝ) ^ (h - 3) * 1188
  let C : ℝ := max 1 (max (Cwalk * B0) Cwalk)
  have hB0 : 0 < B0 := by
    dsimp [B0]
    positivity
  have hC1 : 1 ≤ C := by dsimp [C]; exact le_max_left _ _
  have hCwalkC : Cwalk ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hprodC : Cwalk * B0 ≤ C := by
    dsimp [C]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨C, hC1, ?_⟩
  intro t ht L q hq s I J hI hJ hIJ f
  classical
  let p : ℝ := q / (q - 1)
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hqone : 1 ≤ q := le_of_lt hq
  have hqden : 0 < q - 1 := by linarith
  have hpq : p.HolderConjugate q := by
    have hconj : q.HolderConjugate (q / (q - 1)) :=
      Real.HolderConjugate.conjExponent hq
    simpa [p] using hconj.symm
  have hcommon : ∀ α : DeltaBose.CollisionPair h,
      ¬(I = pairPartition α ∧ J = pairPartition α) := by
    intro α hpairs
    exact hIJ (hpairs.1.trans hpairs.2.symm)
  let sI := s.filter fun x => IsEqualityConfiguration I x
  let sJ := s.filter fun x => IsEqualityConfiguration J x
  let K : LatticeConfiguration h → LatticeConfiguration h → ℝ :=
    weightedKernel (replicaExponentialWeight t) (hattedFreeReplicaKernel L I J)
  let u : ℝ := t ^ 2 * (L : ℝ)
  let A : ℝ := Cwalk * Real.exp (Cwalk * u)
  let B : ℝ := C * Real.exp (C * u) * q * p
  have hApos : 0 < A := by dsimp [A]; positivity
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hKnonneg (x y : LatticeConfiguration h) : 0 ≤ K x y := by
    dsimp [K, weightedKernel]
    exact div_nonneg
      (mul_nonneg (replicaExponentialWeight_pos t x).le
        (hattedFreeReplicaKernel_nonneg L I J x y))
      (replicaExponentialWeight_pos t y).le
  have hKbound (x y : LatticeConfiguration h) :
      K x y ≤ A * replicaGreenKernel x y := by
    simpa [K, A, u, mul_assoc] using hkernelBound t ht L I J x y
  have hzeroLeft (x y : LatticeConfiguration h)
      (hx : ¬IsEqualityConfiguration I x) : K x y = 0 := by
    have hnot : ¬IsCollisionConfiguration I x := fun hx' => hx hx'.1
    simp [K, weightedKernel, hattedFreeReplicaKernel, freeReplicaKernel, hnot]
  have hzeroRight (x y : LatticeConfiguration h)
      (hy : ¬IsEqualityConfiguration J y) : K x y = 0 := by
    have hnot : ¬IsCollisionConfiguration J y := fun hy' => hy hy'.1
    simp [K, weightedKernel, hattedFreeReplicaKernel, freeReplicaKernel, hnot]
  have hBscale : A * B0 ≤ C * Real.exp (C * u) := by
    dsimp [A]
    calc
      Cwalk * Real.exp (Cwalk * u) * B0 =
          (Cwalk * B0) * Real.exp (Cwalk * u) := by ring
      _ ≤ C * Real.exp (Cwalk * u) :=
        mul_le_mul_of_nonneg_right hprodC (Real.exp_nonneg _)
      _ ≤ C * Real.exp (C * u) := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [C]; positivity)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right hCwalkC (mul_nonneg (sq_nonneg t) (Nat.cast_nonneg L))
  have hRestNonneg (g f' : LatticeConfiguration h → ℝ) :
      0 ≤ (p * q) * finiteLpNorm sI p g * finiteLpNorm sJ q f' := by
    have hpqnonneg : 0 ≤ p * q := mul_nonneg hpq.pos.le hqpos.le
    have hleft : 0 ≤ p * q * finiteLpNorm sI p g :=
      mul_nonneg hpqnonneg (finiteLpNorm_nonneg sI p g)
    exact mul_nonneg hleft (finiteLpNorm_nonneg sJ q f')
  have hbilinear : ∀ g f' : LatticeConfiguration h → ℝ,
      (∑ x ∈ sI, ∑ y ∈ sJ, |g x| * K x y * |f' y|) ≤
        B * finiteLpNorm sI p g * finiteLpNorm sJ q f' := by
    intro g f'
    have hgreenSum :
        (∑ x ∈ sI, ∑ y ∈ sJ, |g x| * K x y * |f' y|) ≤
          A * ∑ x ∈ sI, ∑ y ∈ sJ, |g x| * replicaGreenKernel x y * |f' y| := by
      calc
        _ ≤ ∑ x ∈ sI, ∑ y ∈ sJ,
              A * (|g x| * replicaGreenKernel x y * |f' y|) := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          calc
            |g x| * K x y * |f' y| ≤
                |g x| * (A * replicaGreenKernel x y) * |f' y| := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hKbound x y) (abs_nonneg _)) (abs_nonneg _)
            _ = A * (|g x| * replicaGreenKernel x y * |f' y|) := by ring
        _ = _ := by simp_rw [← Finset.mul_sum]
    have hLZ := finite_equalityStratum_bilinear_le I J hI hJ hcommon hpq sI sJ
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun y hy => (Finset.mem_filter.mp hy).2) g f'
    have hLZ' :
        (∑ x ∈ sI, ∑ y ∈ sJ, |g x| * replicaGreenKernel x y * |f' y|) ≤
          B0 * (p * q) * finiteLpNorm sI p g * finiteLpNorm sJ q f' := by
      simpa [B0, lz21BilinearConstant, finiteLpNorm] using hLZ
    calc
      _ ≤ A * (B0 * (p * q) * finiteLpNorm sI p g * finiteLpNorm sJ q f') :=
        hgreenSum.trans (mul_le_mul_of_nonneg_left hLZ' hApos.le)
      _ = (A * B0) * (p * q) * finiteLpNorm sI p g * finiteLpNorm sJ q f' := by ring
      _ ≤ (C * Real.exp (C * u)) * (p * q) *
            finiteLpNorm sI p g * finiteLpNorm sJ q f' := by
        calc
          _ = (A * B0) * ((p * q) * finiteLpNorm sI p g * finiteLpNorm sJ q f') := by ring
          _ ≤ (C * Real.exp (C * u)) *
                ((p * q) * finiteLpNorm sI p g * finiteLpNorm sJ q f') :=
            mul_le_mul_of_nonneg_right hBscale (hRestNonneg g f')
          _ = (C * Real.exp (C * u)) * (p * q) *
                finiteLpNorm sI p g * finiteLpNorm sJ q f' := by ring
      _ = B * finiteLpNorm sI p g * finiteLpNorm sJ q f' := by
        dsimp [B]
        ring
  have hkernelApply_bound := finiteLpNorm_kernelApply_le_of_bilinearBound
    sI sJ K hKnonneg hpq B hBnonneg hbilinear f
  let F : LatticeConfiguration h → ℝ := fun x =>
    ∑ y ∈ s, K x y * f y
  have hsumRestrict (x : LatticeConfiguration h) :
      F x = ∑ y ∈ sJ, K x y * f y := by
    dsimp [F]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y hyS hyJ
    have hyNot : ¬IsEqualityConfiguration J y := by
      intro hyEq
      exact hyJ (Finset.mem_filter.mpr ⟨hyS, hyEq⟩)
    rw [hzeroRight x y hyNot]
    simp
  have hFzero (x : LatticeConfiguration h) (hx : ¬IsEqualityConfiguration I x) : F x = 0 := by
    dsimp [F]
    apply Finset.sum_eq_zero
    intro y hy
    rw [hzeroLeft x y hx]
    simp
  have hnormRestrict : finiteLpNorm s q F = finiteLpNorm sI q F := by
    unfold finiteLpNorm
    congr 1
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hxS hxI
    have hxNot : ¬IsEqualityConfiguration I x := by
      intro hxEq
      exact hxI (Finset.mem_filter.mpr ⟨hxS, hxEq⟩)
    rw [hFzero x hxNot]
    simp [Real.zero_rpow (ne_of_gt hqpos)]
  have hinputMono : finiteLpNorm sJ q f ≤ finiteLpNorm s q f := by
    unfold finiteLpNorm
    apply Real.rpow_le_rpow
    · exact Finset.sum_nonneg fun x hx => Real.rpow_nonneg (abs_nonneg _) _
    · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x hxS hxJ => Real.rpow_nonneg (abs_nonneg _) _)
    · exact (one_div_pos.mpr hqpos).le
  have htarget : B ≤ C * Real.exp (C * t ^ 2 * L) * q * (q / (q - 1)) := by
    have harg : C * u = C * t ^ 2 * L := by dsimp [u]; ring
    dsimp [B, p]
    rw [harg]
  calc
    finiteLpNorm s q (finiteKernelApply s K f) = finiteLpNorm s q F := by rfl
    _ = finiteLpNorm sI q F := hnormRestrict
    _ = finiteLpNorm sI q (fun x => ∑ y ∈ sJ, K x y * f y) := by
      congr 1
      funext x
      exact hsumRestrict x
    _ ≤ B * finiteLpNorm sJ q f := hkernelApply_bound
    _ ≤ B * finiteLpNorm s q f :=
      mul_le_mul_of_nonneg_left hinputMono hBnonneg
    _ ≤ C * Real.exp (C * t ^ 2 * L) * q * (q / (q - 1)) * finiteLpNorm s q f :=
      mul_le_mul_of_nonneg_right htarget (finiteLpNorm_nonneg s q f)

end Critical2DKPZ.MomentBounds

end
