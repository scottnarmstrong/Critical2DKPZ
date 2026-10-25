/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.AiiKNormMGF
public import Critical2DKPZ.MomentBounds.AiiKSchur
public import Critical2DKPZ.MomentBounds.CCR25Operators
public import Critical2DKPZ.Collision.SpatialGaussian
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # Weighted finite boundary convolution bounds -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private noncomputable def walkExponentialWeight (t : ℝ) (x : Site) : ℝ :=
  Real.exp (t * ‖siteToPlane x‖)

private noncomputable def radialWalkWeight (n : ℕ) (t : ℝ) (z : Site) : ℝ :=
  Real.exp (t * ‖siteToPlane z‖) * srwKernel n z

private theorem summable_radialWalkWeight (n : ℕ) (t : ℝ) :
    Summable (radialWalkWeight n t) := by
  apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 n)
  intro z hz
  have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 z hz
  have hq : srwKernel n z = 0 := by simpa only [sub_zero] using h
  simp [radialWalkWeight, hq]

private theorem sum_subLeft_radialWalkWeight_le (n : ℕ) (t B : ℝ)
    (hB : ∑' z : Site, radialWalkWeight n t z ≤ B) (s : Finset Site) (x : Site) :
    ∑ y ∈ s, radialWalkWeight n t (x - y) ≤ B := by
  have hsum : Summable (fun y : Site => radialWalkWeight n t (x - y)) :=
    (summable_radialWalkWeight n t).comp_injective (Equiv.subLeft x).injective
  calc
    ∑ y ∈ s, radialWalkWeight n t (x - y) ≤
        ∑' y : Site, radialWalkWeight n t (x - y) :=
      hsum.sum_le_tsum s (fun y _ => mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _))
    _ = ∑' z : Site, radialWalkWeight n t z := Equiv.tsum_eq (Equiv.subLeft x) _
    _ ≤ B := hB

private theorem sum_subRight_radialWalkWeight_le (n : ℕ) (t B : ℝ)
    (hB : ∑' z : Site, radialWalkWeight n t z ≤ B) (s : Finset Site) (y : Site) :
    ∑ x ∈ s, radialWalkWeight n t (x - y) ≤ B := by
  have hsum : Summable (fun x : Site => radialWalkWeight n t (x - y)) :=
    (summable_radialWalkWeight n t).comp_injective (Equiv.subRight y).injective
  calc
    ∑ x ∈ s, radialWalkWeight n t (x - y) ≤
        ∑' x : Site, radialWalkWeight n t (x - y) :=
      hsum.sum_le_tsum s (fun x _ => mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _))
    _ = ∑' z : Site, radialWalkWeight n t z := Equiv.tsum_eq (Equiv.subRight y) _
    _ ≤ B := hB

private theorem expWeight_sub_le {t : ℝ} (ht : 0 ≤ t) (x y : Site) :
    walkExponentialWeight t x ≤
      Real.exp (t * ‖siteToPlane (x - y)‖) * walkExponentialWeight t y := by
  have htri : ‖siteToPlane x‖ ≤ ‖siteToPlane (x - y)‖ + ‖siteToPlane y‖ := by
    have hxy : siteToPlane x = siteToPlane (x - y) + siteToPlane y := by
      rw [Collision.siteToPlane_sub y x]
      abel
    rw [hxy]
    exact norm_add_le _ _
  have harg : t * ‖siteToPlane x‖ ≤
      t * ‖siteToPlane (x - y)‖ + t * ‖siteToPlane y‖ := by
    nlinarith [mul_nonneg ht (sub_nonneg.mpr htri)]
  calc
    walkExponentialWeight t x ≤
        Real.exp (t * ‖siteToPlane (x - y)‖ + t * ‖siteToPlane y‖) := by
      exact Real.exp_le_exp.mpr (by simpa [walkExponentialWeight] using harg)
    _ = Real.exp (t * ‖siteToPlane (x - y)‖) * walkExponentialWeight t y := by
      rw [Real.exp_add]
      rfl

private theorem expWeight_conjugatedKernel_le_radial
    (t : ℝ) (ht : 0 ≤ t) (n : ℕ) (x y : Site) :
    walkExponentialWeight t x * srwKernel n (x - y) /
        walkExponentialWeight t y ≤ radialWalkWeight n t (x - y) := by
  have hnorm : ‖siteToPlane x‖ - ‖siteToPlane y‖ ≤ ‖siteToPlane (x - y)‖ := by
    calc
      ‖siteToPlane x‖ - ‖siteToPlane y‖ ≤
          |‖siteToPlane x‖ - ‖siteToPlane y‖| := le_abs_self _
      _ ≤ ‖siteToPlane x - siteToPlane y‖ := abs_norm_sub_norm_le _ _
      _ = ‖siteToPlane (x - y)‖ := by rw [Collision.siteToPlane_sub y x]
  have hExp : walkExponentialWeight t x / walkExponentialWeight t y ≤
      Real.exp (t * ‖siteToPlane (x - y)‖) := by
    unfold walkExponentialWeight
    rw [← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hnorm)]
  have hq : 0 ≤ srwKernel n (x - y) := srwKernel_nonneg _ _
  calc
    _ = srwKernel n (x - y) *
        (walkExponentialWeight t x / walkExponentialWeight t y) := by ring
    _ ≤ srwKernel n (x - y) * Real.exp (t * ‖siteToPlane (x - y)‖) :=
      mul_le_mul_of_nonneg_left hExp hq
    _ = radialWalkWeight n t (x - y) := by
      simp [radialWalkWeight, mul_comm]

private theorem finiteLpNorm_mono {α : Type*} (s u : Finset α) (hsu : s ⊆ u)
    {p : ℝ} (hp : 0 < p) (f : α → ℝ) :
    finiteLpNorm s p f ≤ finiteLpNorm u p f := by
  unfold finiteLpNorm
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun x hx => Real.rpow_nonneg (abs_nonneg _) _
  · exact Finset.sum_le_sum_of_subset_of_nonneg hsu
      (fun x hxU hxS => Real.rpow_nonneg (abs_nonneg _) _)
  · exact one_div_nonneg.mpr hp.le

private theorem finiteLpNorm_zeroExtend_eq {α : Type*} [DecidableEq α]
    (a u : Finset α) (hau : a ⊆ u)
    {p : ℝ} (hp : 0 < p) (f : α → ℝ) :
    finiteLpNorm u p (fun x => if x ∈ a then f x else 0) = finiteLpNorm a p f := by
  classical
  unfold finiteLpNorm
  congr 1
  have hsum :
      (∑ x ∈ u, |(if x ∈ a then f x else 0 : ℝ)| ^ p) =
        ∑ x ∈ a, |f x| ^ p := by
    calc
      (∑ x ∈ u, |(if x ∈ a then f x else 0 : ℝ)| ^ p) =
          ∑ x ∈ u, if x ∈ a then |f x| ^ p else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxa : x ∈ a <;> simp [hxa, Real.zero_rpow (ne_of_gt hp)]
      _ = ∑ x ∈ a, if x ∈ a then |f x| ^ p else 0 :=
        (Finset.sum_subset hau (by intro x hxU hxa; simp [hxa])).symm
      _ = ∑ x ∈ a, |f x| ^ p := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [hx]
  exact hsum

private theorem weightedBoundaryConvolution_pointwise
    (c : ℝ) (hc : 1 ≤ c) (n : ℕ) (hn : 1 ≤ n) {t p : ℝ}
    (ht : 0 ≤ t) (hp : 1 ≤ p)
    (hRad : ∑' z : Site, radialWalkWeight n t z ≤ c * Real.exp (2 * c * t ^ 2 * n))
    (hRadPoint : 1 ≤ n → ∀ z : Site,
      radialWalkWeight n t z ≤ c * Real.exp (2 * c * t ^ 2 * n) / n)
    (A : Finset Site) (f : Site → ℝ) (x : Site) :
    |finiteBoundaryConvolution n A f x| * walkExponentialWeight t x ≤
      c * Real.exp (2 * c * t ^ 2 * n) / n ^ (1 / p) *
        finiteLpNorm A p (fun y => f y * walkExponentialWeight t y) := by
  let M := c * Real.exp (2 * c * t ^ 2 * n)
  let w : Site → ℝ := fun y => radialWalkWeight n t (x - y)
  let g : Site → ℝ := fun y => |f y| * walkExponentialWeight t y
  have hM : 0 < M := by positivity
  have hMnonneg : 0 ≤ M := hM.le
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hwsum : ∑ y ∈ A, w y ≤ M := by
    simpa [w, M] using sum_subLeft_radialWalkWeight_le n t M hRad A x
  have hwsum_nonneg : 0 ≤ ∑ y ∈ A, w y :=
    Finset.sum_nonneg fun y hy => mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _)
  have hwpoint (y : Site) : w y ≤ M / n := by
    simpa [w, M, radialWalkWeight] using hRadPoint hn (x - y)
  have hw (y : Site) : 0 ≤ w y := by
    exact mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _)
  have hg (y : Site) : 0 ≤ g y := mul_nonneg (abs_nonneg _) (Real.exp_nonneg _)
  have hHolder := Real.inner_le_weight_mul_Lp_of_nonneg A hp w g hw hg
  have hmoment :
      ∑ y ∈ A, w y * g y ^ p ≤ (M / n) * ∑ y ∈ A, g y ^ p := by
    calc
      ∑ y ∈ A, w y * g y ^ p ≤
          ∑ y ∈ A, (M / n) * g y ^ p := by
            apply Finset.sum_le_sum
            intro y hy
            exact mul_le_mul_of_nonneg_right (hwpoint y)
              (Real.rpow_nonneg (hg y) _)
      _ = (M / n) * ∑ y ∈ A, g y ^ p := by rw [Finset.mul_sum]
  have hmoment_nonneg : 0 ≤ ∑ y ∈ A, w y * g y ^ p :=
    Finset.sum_nonneg fun y hy => mul_nonneg (hw y) (Real.rpow_nonneg (hg y) _)
  have hG : 0 ≤ ∑ y ∈ A, g y ^ p :=
    Finset.sum_nonneg fun y hy => Real.rpow_nonneg (hg y) _
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hα : 0 ≤ 1 - p⁻¹ := by
    have hpInv : p⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hp0]
      exact hp
    linarith
  have hβ : 0 ≤ p⁻¹ := inv_nonneg.mpr hp0.le
  have hwsum_rpow : (∑ y ∈ A, w y) ^ (1 - p⁻¹) ≤ M ^ (1 - p⁻¹) :=
    Real.rpow_le_rpow hwsum_nonneg hwsum hα
  have hmoment_rpow :
      (∑ y ∈ A, w y * g y ^ p) ^ p⁻¹ ≤ ((M / n) * ∑ y ∈ A, g y ^ p) ^ p⁻¹ :=
    Real.rpow_le_rpow hmoment_nonneg hmoment hβ
  have hHolderBound :
      ∑ y ∈ A, w y * g y ≤
        M ^ (1 - p⁻¹) * ((M / n) * ∑ y ∈ A, g y ^ p) ^ p⁻¹ := by
    calc
      ∑ y ∈ A, w y * g y ≤
          (∑ y ∈ A, w y) ^ (1 - p⁻¹) *
            (∑ y ∈ A, w y * g y ^ p) ^ p⁻¹ := hHolder
      _ ≤ M ^ (1 - p⁻¹) * ((M / n) * ∑ y ∈ A, g y ^ p) ^ p⁻¹ := by
        exact mul_le_mul hwsum_rpow hmoment_rpow
          (Real.rpow_nonneg hmoment_nonneg _) (Real.rpow_nonneg hMnonneg _)
  have hGnorm :
      (∑ y ∈ A, g y ^ p) ^ (1 / p) =
        finiteLpNorm A p (fun y => f y * walkExponentialWeight t y) := by
    unfold finiteLpNorm
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    dsimp [g]
    rw [abs_mul, abs_of_nonneg (show 0 ≤ walkExponentialWeight t y from Real.exp_nonneg _)]
  have hnormalize :
      M ^ (1 - p⁻¹) * ((M / n) * (∑ y ∈ A, g y ^ p)) ^ p⁻¹ =
        M * (∑ y ∈ A, g y ^ p) ^ (1 / p) / n ^ (1 / p) := by
    have hpowers : (1 - p⁻¹) + p⁻¹ = 1 := by ring
    calc
      M ^ (1 - p⁻¹) * ((M / n) * (∑ y ∈ A, g y ^ p)) ^ p⁻¹ =
          (M ^ (1 - p⁻¹) * M ^ p⁻¹ * (∑ y ∈ A, g y ^ p) ^ p⁻¹) / n ^ p⁻¹ := by
            rw [Real.mul_rpow (div_nonneg hMnonneg hnR.le) hG,
              Real.div_rpow hMnonneg hnR.le]
            ring
      _ = M * (∑ y ∈ A, g y ^ p) ^ p⁻¹ / n ^ p⁻¹ := by
        rw [← Real.rpow_add hM, hpowers, Real.rpow_one]
      _ = M * (∑ y ∈ A, g y ^ p) ^ (1 / p) / n ^ (1 / p) := by
        simp only [one_div]
  have hweighted :
      |finiteBoundaryConvolution n A f x| * walkExponentialWeight t x ≤
        ∑ y ∈ A, w y * g y := by
    rw [finiteBoundaryConvolution]
    calc
      |∑ y ∈ A, srwKernel n (x - y) * f y| * walkExponentialWeight t x ≤
          (∑ y ∈ A, |srwKernel n (x - y) * f y|) * walkExponentialWeight t x :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Real.exp_nonneg _)
      _ = ∑ y ∈ A, |srwKernel n (x - y) * f y| * walkExponentialWeight t x := by
        rw [Finset.sum_mul]
      _ ≤ ∑ y ∈ A,
          (srwKernel n (x - y) * |f y|) * walkExponentialWeight t x := by
        apply Finset.sum_le_sum
        intro y hy
        rw [abs_mul, abs_of_nonneg (srwKernel_nonneg _ _)]
      _ ≤ ∑ y ∈ A, w y * g y := by
        apply Finset.sum_le_sum
        intro y hy
        have hweight := expWeight_sub_le ht x y
        have hqf : 0 ≤ srwKernel n (x - y) * |f y| :=
          mul_nonneg (srwKernel_nonneg _ _) (abs_nonneg _)
        calc
          (srwKernel n (x - y) * |f y|) * walkExponentialWeight t x ≤
              (srwKernel n (x - y) * |f y|) *
                (Real.exp (t * ‖siteToPlane (x - y)‖) * walkExponentialWeight t y) :=
            mul_le_mul_of_nonneg_left hweight hqf
          _ = w y * g y := by dsimp [w, g, radialWalkWeight]; ring
  calc
    |finiteBoundaryConvolution n A f x| * walkExponentialWeight t x ≤
        ∑ y ∈ A, w y * g y := hweighted
    _ ≤ M ^ (1 - p⁻¹) * ((M / n) * ∑ y ∈ A, g y ^ p) ^ p⁻¹ := hHolderBound
    _ = M * (∑ y ∈ A, g y ^ p) ^ (1 / p) / n ^ (1 / p) := hnormalize
    _ = M / n ^ (1 / p) * finiteLpNorm A p
          (fun y => f y * walkExponentialWeight t y) := by rw [hGnorm]; ring
    _ = c * Real.exp (2 * c * t ^ 2 * n) / n ^ (1 / p) *
          finiteLpNorm A p (fun y => f y * walkExponentialWeight t y) := by
      simp [M, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Weighted Young and pointwise boundary-convolution estimates for the planar walk. -/
theorem finiteLpNorm_boundaryConvolution_mul_exp_le :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, ∀ p : ℝ, 1 ≤ p →
      ∀ (A S : Finset Site) (f : Site → ℝ),
      finiteLpNorm S p
        (fun x => finiteBoundaryConvolution n A f x * Real.exp (t * ‖siteToPlane x‖)) ≤
        c * Real.exp (2 * c * t ^ 2 * n) *
          finiteLpNorm A p (fun y => f y * Real.exp (t * ‖siteToPlane y‖)) ∧
      (1 ≤ n → ∀ x : Site,
        |finiteBoundaryConvolution n A f x| * Real.exp (t * ‖siteToPlane x‖) ≤
          c * Real.exp (2 * c * t ^ 2 * n) / (n : ℝ) ^ (1 / p) *
            finiteLpNorm A p (fun y => f y * Real.exp (t * ‖siteToPlane y‖))) := by
  classical
  obtain ⟨c, hc, hmgf⟩ := tsum_exp_mul_norm_srwKernel_le
  refine ⟨c, hc, fun t ht n p hp A S f => ?_⟩
  obtain ⟨hRad, hRadPoint⟩ := hmgf t ht n
  have hRad' : ∑' z : Site, radialWalkWeight n t z ≤
      c * Real.exp (2 * c * t ^ 2 * n) := by simpa [radialWalkWeight] using hRad
  let M := c * Real.exp (2 * c * t ^ 2 * n)
  let U := A ∪ S
  let W := walkExponentialWeight t
  let K : Site → Site → ℝ := fun x y => W x * srwKernel n (x - y) / W y
  let g : Site → ℝ := fun y => if y ∈ A then f y * W y else 0
  have hAU : A ⊆ U := Finset.subset_union_left
  have hSU : S ⊆ U := Finset.subset_union_right
  have hM : 0 ≤ M := by positivity
  have hK : ∀ x y, 0 ≤ K x y := by
    intro x y
    dsimp [K]
    exact div_nonneg (mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _))
      (Real.exp_nonneg _)
  have hrow : ∀ x ∈ U, ∑ y ∈ U, K x y ≤ M := by
    intro x hx
    calc
      ∑ y ∈ U, K x y ≤ ∑ y ∈ U, radialWalkWeight n t (x - y) := by
        apply Finset.sum_le_sum
        intro y hy
        exact expWeight_conjugatedKernel_le_radial t ht n x y
      _ ≤ M := by simpa [M] using sum_subLeft_radialWalkWeight_le n t M hRad' U x
  have hcol : ∀ y ∈ U, ∑ x ∈ U, K x y ≤ M := by
    intro y hy
    calc
      ∑ x ∈ U, K x y ≤ ∑ x ∈ U, radialWalkWeight n t (x - y) := by
        apply Finset.sum_le_sum
        intro x hx
        exact expWeight_conjugatedKernel_le_radial t ht n x y
      _ ≤ M := by simpa [M] using sum_subRight_radialWalkWeight_le n t M hRad' U y
  have hSchur := finiteLpNorm_finiteKernelApply_le_of_rowCol U K hK hp hrow hcol g
  have hconv (x : Site) :
      finiteKernelApply U K g x = W x * finiteBoundaryConvolution n A f x := by
    rw [finiteKernelApply, finiteBoundaryConvolution]
    calc
      ∑ y ∈ U, K x y * g y =
          ∑ y ∈ U, if y ∈ A then W x * (srwKernel n (x - y) * f y) else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hya : y ∈ A
        · simp [K, g, hya]
          have hWy : 0 < W y := Real.exp_pos _
          field_simp [ne_of_gt hWy]
        · simp [g, hya]
      _ = ∑ y ∈ A, W x * (srwKernel n (x - y) * f y) := by
        calc
          (∑ y ∈ U, (if y ∈ A then W x * (srwKernel n (x - y) * f y) else 0)) =
              (∑ y ∈ A, (if y ∈ A then W x * (srwKernel n (x - y) * f y) else 0)) :=
            (Finset.sum_subset hAU (by intro y hyU hya; simp [hya])).symm
          _ = ∑ y ∈ A, W x * (srwKernel n (x - y) * f y) := by
            apply Finset.sum_congr rfl
            intro y hy
            simp [hy]
      _ = W x * ∑ y ∈ A, srwKernel n (x - y) * f y := by rw [Finset.mul_sum]
  have hgnorm : finiteLpNorm U p g =
      finiteLpNorm A p (fun y => f y * W y) := by
    simpa [g] using finiteLpNorm_zeroExtend_eq A U hAU (by linarith : 0 < p)
      (fun y => f y * W y)
  have hfirst : finiteLpNorm S p
      (fun x => finiteBoundaryConvolution n A f x * W x) ≤
      M * finiteLpNorm A p (fun y => f y * W y) := by
    have heq : finiteLpNorm S p
        (fun x => finiteBoundaryConvolution n A f x * W x) =
          finiteLpNorm S p (fun x => finiteKernelApply U K g x) := by
      congr 1
      funext x
      rw [hconv x]
      ring
    calc
      finiteLpNorm S p (fun x => finiteBoundaryConvolution n A f x * W x) =
          finiteLpNorm S p (fun x => finiteKernelApply U K g x) := heq
      _ ≤ finiteLpNorm U p (fun x => finiteKernelApply U K g x) :=
        finiteLpNorm_mono S U hSU (by linarith : 0 < p) _
      _ ≤ M * finiteLpNorm U p g := hSchur
      _ = M * finiteLpNorm A p (fun y => f y * W y) := by rw [hgnorm]
  constructor
  · simpa [M, W, walkExponentialWeight] using hfirst
  · intro hn x
    have hpoint := weightedBoundaryConvolution_pointwise c hc n hn ht hp hRad'
      hRadPoint A f x
    simpa [M, W, walkExponentialWeight, radialWalkWeight] using hpoint

end Critical2DKPZ.MomentBounds

end
