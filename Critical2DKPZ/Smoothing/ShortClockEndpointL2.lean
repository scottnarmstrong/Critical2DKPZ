/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ShortClockEndpoint
public import Critical2DKPZ.Smoothing.ShortClockProfile
import Mathlib.Tactic

/-! # Coordinate L² control of short-clock endpoint laws -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

private theorem integrable_sq_pathWeight_sub_one (β : ℝ) (d : ℕ) (y : Site)
    {ℓ : ℕ} (s : Fin ℓ → Fin 4) :
    Integrable (fun ω => (Polymer.pathWeight β d y s ω - 1) ^ 2) disorderLaw := by
  have hmem : MemLp (fun ω => Polymer.pathWeight β d y s ω - 1) 2 disorderLaw :=
    (Polymer.memLp_pathWeight β d y s 2 (by norm_num)).sub (memLp_const 1)
  have h := hmem.integrable_norm_pow'
  simpa only [Real.norm_eq_abs, sq_abs] using h

private theorem integral_sq_pathWeight_sub_one (β : ℝ) (d : ℕ) (y : Site)
    {ℓ : ℕ} (s : Fin ℓ → Fin 4) :
    (∫ ω, (Polymer.pathWeight β d y s ω - 1) ^ 2 ∂disorderLaw) =
      Real.exp ((ℓ : ℝ) * β ^ 2) - 1 := by
  have hW2 := MomentBounds.integral_pathWeight_pow β d y s 2
  have hW := Polymer.integral_pathWeight β d y s
  have hWmem : MemLp (fun ω => Polymer.pathWeight β d y s ω) 2 disorderLaw :=
    Polymer.memLp_pathWeight β d y s 2 (by norm_num)
  have hW2Int : Integrable (fun ω => Polymer.pathWeight β d y s ω ^ 2) disorderLaw := by
    have h := hWmem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hWInt : Integrable (fun ω => Polymer.pathWeight β d y s ω) disorderLaw :=
    Polymer.integrable_pathWeight β d y s
  calc
    _ = ∫ ω, (Polymer.pathWeight β d y s ω ^ 2 -
          2 * Polymer.pathWeight β d y s ω + 1) ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
    _ = (∫ ω, Polymer.pathWeight β d y s ω ^ 2 ∂disorderLaw) -
          2 * (∫ ω, Polymer.pathWeight β d y s ω ∂disorderLaw) + 1 := by
        calc
          _ = (∫ ω, Polymer.pathWeight β d y s ω ^ 2 -
                2 * Polymer.pathWeight β d y s ω ∂disorderLaw) +
                ∫ ω, (1 : ℝ) ∂disorderLaw :=
              integral_add (hW2Int.sub (hWInt.const_mul 2)) (integrable_const 1)
          _ = _ := by
            rw [integral_sub hW2Int (hWInt.const_mul 2), integral_const_mul]
            simp [hW]
    _ = Real.exp ((ℓ : ℝ) * β ^ 2) - 1 := by
        rw [hW2, hW]
        ring_nf

/-- The squared coordinate distance between the short-clock random endpoint distribution and
the free endpoint law is controlled by the maximum free endpoint mass and the short-clock mass
fluctuation. The integral includes its integrability companion. -/
theorem integral_shortClockEndpoint_coordinate_sq_le (β : ℝ) {d k : ℕ}
    (hdk : d ≤ k) (x : Site) (Q R : ℝ) (hR : 0 ≤ R)
    (hZvarInt : Integrable
      (fun ω => (smoothedP2Plane β d k x ω - 1) ^ 2) disorderLaw)
    (hZvar : (∫ ω, (smoothedP2Plane β d k x ω - 1) ^ 2 ∂disorderLaw) ≤ Q)
    (hkernel : ∀ z, srwKernel k (z - x) ≤ R) :
    Integrable (fun ω => ∑ z ∈ Polymer.endpoints x k,
      (smoothedEndpointDist β d k x ω z - srwKernel k (z - x)) ^ 2) disorderLaw ∧
    (∫ ω, ∑ z ∈ Polymer.endpoints x k,
      (smoothedEndpointDist β d k x ω z - srwKernel k (z - x)) ^ 2 ∂disorderLaw) ≤
      8 * (R * (Real.exp (((k - d : ℕ) : ℝ) * β ^ 2) - 1)) +
        8 * R * Q + 8 * Q := by
  classical
  let ℓ := k - d
  let A := Polymer.endpoints x d
  let B := Polymer.endpoints x k
  let c (y : Site) (s : Fin ℓ → Fin 4) :=
    srwKernel d (y - x) * (4 : ℝ)⁻¹ ^ ℓ
  let W (y : Site) (s : Fin ℓ → Fin 4) (ω : Disorder) :=
    Polymer.pathWeight β d y s ω
  let U (z : Site) (ω : Disorder) :=
    ∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω
  let p (z : Site) := srwKernel k (z - x)
  let S (ω : Disorder) := ∑ z ∈ B,
    (smoothedEndpointDist β d k x ω z - p z) ^ 2
  let V (ω : Disorder) := ∑ z ∈ B, (U z ω - p z) ^ 2
  have hcoeff : ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s = 1 := by
    dsimp [c, A]
    calc
      _ = (∑ y ∈ Polymer.endpoints x d, srwKernel d (y - x)) *
          (∑ s : Fin ℓ → Fin 4, (4 : ℝ)⁻¹ ^ ℓ) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y hy
            rw [← Finset.mul_sum]
      _ = 1 := by
            rw [Polymer.sum_srwKernel_endpoints, Polymer.sum_walkProbability]
            norm_num
  have hc (y : Site) (s : Fin ℓ → Fin 4) : 0 ≤ c y s := by
    dsimp [c]
    exact mul_nonneg (Polymer.kernel_nonneg d (y - x)) (by positivity)
  have hUpath (z : Site) (ω : Disorder) :
      U z ω = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
        c y s * W y s ω * (if walkPosition y s ℓ = z then 1 else 0) := by
    dsimp [U, c, W, A]
    calc
      _ = ∑ y ∈ Polymer.endpoints x d,
          srwKernel d (y - x) * pointToPoint β d ℓ y z ω := by
            apply tsum_eq_sum
            intro y hy
            rw [Polymer.srwKernel_eq_zero_of_not_mem d x y
              (by simpa [A] using hy)]
            simp
      _ = _ := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Polymer.pointToPoint_eq_sum]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            ring
  have hfree (z : Site) :
      p z = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
        c y s * (if walkPosition y s ℓ = z then 1 else 0) := by
    have htime : d + ℓ = k := Nat.add_sub_of_le hdk
    change srwKernel k (z - x) =
      ∑ y ∈ Polymer.endpoints x d, ∑ s : Fin ℓ → Fin 4,
        c y s * (if walkPosition y s ℓ = z then 1 else 0)
    rw [← htime, Polymer.srwKernel_convolution]
    calc
      _ = ∑ y ∈ Polymer.endpoints x d,
          srwKernel d (y - x) * srwKernel ℓ (z - y) := by
            apply tsum_eq_sum
            intro y hy
            rw [Polymer.srwKernel_eq_zero_of_not_mem d x y (by simpa [A] using hy)]
            simp
      _ = _ := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Polymer.srwKernel_eq_sum ℓ y z]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            dsimp [c]
            ring
  have hnum (z : Site) (ω : Disorder) :
      U z ω - p z = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
        c y s * (W y s ω - 1) * (if walkPosition y s ℓ = z then 1 else 0) := by
    rw [hUpath z ω, hfree z]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hend : walkPosition y s ℓ = z
    · simp [W, hend]
      ring
    · simp [W, hend]
  have hprob (ω : Disorder) := smoothedEndpointDist_probability β hdk x ω
  have hsupport (ω : Disorder) (z : Site) (hz : z ∉ B) :
      smoothedEndpointDist β d k x ω z = 0 := (hprob ω).1 z (by
        intro hz'
        apply hz
        rcases Finset.mem_biUnion.mp hz' with ⟨y, hy, hzy⟩
        have hadd := shortClock_endpoints_add hy hzy
        simpa [B, Nat.add_sub_of_le hdk] using hadd)
  have hprobMass (ω : Disorder) :
      ∑ z ∈ B, smoothedEndpointDist β d k x ω z = 1 := by
    have hCB : (Polymer.endpoints x d).biUnion
        (fun y => Polymer.endpoints y (k - d)) ⊆ B := by
      intro z hz
      rcases Finset.mem_biUnion.mp hz with ⟨y, hy, hzy⟩
      have hadd := shortClock_endpoints_add hy hzy
      simpa [B, Nat.add_sub_of_le hdk] using hadd
    calc
      _ = ∑ z ∈ (Polymer.endpoints x d).biUnion
          (fun y => Polymer.endpoints y (k - d)), smoothedEndpointDist β d k x ω z := by
            symm
            apply Finset.sum_subset hCB
            intro z hz hznot
            exact (hprob ω).1 z hznot
      _ = 1 := (hprob ω).2.2
  have hfreeMass : ∑ z ∈ B, p z = 1 := by
    dsimp [p, B]
    exact Polymer.sum_srwKernel_endpoints k x
  have hpnonneg (z : Site) : 0 ≤ p z := Polymer.kernel_nonneg k (z - x)
  have hηnonneg (ω : Disorder) (z : Site) :
      0 ≤ smoothedEndpointDist β d k x ω z := (hprob ω).2.1 z
  have hηleOne (ω : Disorder) (z : Site) (hz : z ∈ B) :
      smoothedEndpointDist β d k x ω z ≤ 1 := by
    calc
      _ ≤ ∑ v ∈ B, smoothedEndpointDist β d k x ω v :=
        Finset.single_le_sum (fun v hv => hηnonneg ω v) hz
      _ = 1 := hprobMass ω
  have hpleOne (z : Site) (hz : z ∈ B) : p z ≤ 1 := by
    calc
      _ ≤ ∑ v ∈ B, p v := Finset.single_le_sum (fun v hv => hpnonneg v) hz
      _ = 1 := hfreeMass
  have hSnonneg (ω : Disorder) : 0 ≤ S ω := by
    dsimp [S]
    positivity
  have hVnonneg (ω : Disorder) : 0 ≤ V ω := by
    dsimp [V]
    positivity
  have hSbound (ω : Disorder) : S ω ≤ 2 := by
    dsimp [S]
    calc
      _ ≤ ∑ z ∈ B, (smoothedEndpointDist β d k x ω z + p z) := by
            apply Finset.sum_le_sum
            intro z hz
            have hη0 := hηnonneg ω z
            have hp0 := hpnonneg z
            have hη1 := hηleOne ω z hz
            have hp1 := hpleOne z hz
            nlinarith [sq_nonneg (smoothedEndpointDist β d k x ω z - p z)]
      _ = 2 := by rw [Finset.sum_add_distrib, hprobMass, hfreeMass]; norm_num
  have hZpos (ω : Disorder) : 0 < smoothedP2Plane β d k x ω :=
    Polymer.smoothedP2Plane_pos β d k x ω
  have hpointGood (ω : Disorder) (hgood : 1 / 2 ≤ smoothedP2Plane β d k x ω) :
      S ω ≤ 8 * V ω + 8 * R * (smoothedP2Plane β d k x ω - 1) ^ 2 := by
    have hηratio (z : Site) : smoothedEndpointDist β d k x ω z =
        U z ω / smoothedP2Plane β d k x ω := by
      change (∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) / _ = _
      rfl
    have hdecomp (z : Site) : smoothedEndpointDist β d k x ω z - p z =
        ((U z ω - p z) - p z * (smoothedP2Plane β d k x ω - 1)) /
          smoothedP2Plane β d k x ω := by
      rw [hηratio z]
      field_simp [ne_of_gt (hZpos ω)]
      ring
    have hratio : (smoothedP2Plane β d k x ω)⁻¹ ^ 2 ≤ 4 := by
      have hinv : (smoothedP2Plane β d k x ω)⁻¹ ≤ 2 := by
        have hinv' : 1 / smoothedP2Plane β d k x ω ≤ 2 := by
          calc
            _ ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le
              (by norm_num : (0 : ℝ) < 1 / 2) hgood
            _ = 2 := by norm_num
        simpa only [one_div] using hinv'
      have hnonneg : 0 ≤ (smoothedP2Plane β d k x ω)⁻¹ :=
        inv_nonneg.mpr (hZpos ω).le
      calc
        _ ≤ 2 ^ 2 := (sq_le_sq₀ hnonneg (by norm_num : (0 : ℝ) ≤ 2)).2 hinv
        _ = 4 := by norm_num
    have hpointwise (z : Site) (hz : z ∈ B) :
        (smoothedEndpointDist β d k x ω z - p z) ^ 2 ≤
          8 * (U z ω - p z) ^ 2 +
            8 * p z ^ 2 * (smoothedP2Plane β d k x ω - 1) ^ 2 := by
      rw [hdecomp z, div_pow]
      have hsq : ((U z ω - p z) - p z * (smoothedP2Plane β d k x ω - 1)) ^ 2 ≤
        2 * (U z ω - p z) ^ 2 + 2 * (p z * (smoothedP2Plane β d k x ω - 1)) ^ 2 := by
        nlinarith [sq_nonneg ((U z ω - p z) + p z *
          (smoothedP2Plane β d k x ω - 1))]
      have hsqDen := mul_le_mul hsq hratio (by positivity) (by positivity)
      have hprod : p z ^ 2 * (smoothedP2Plane β d k x ω - 1) ^ 2 ≤
          R * (smoothedP2Plane β d k x ω - 1) ^ 2 :=
        mul_le_mul_of_nonneg_right (by
          have hpR : p z ≤ R := by simpa [p] using hkernel z
          calc
            p z ^ 2 ≤ R * p z := by
              nlinarith [mul_nonneg (hpnonneg z) (sub_nonneg.mpr hpR)]
            _ ≤ R := by
              have hmul := mul_le_mul_of_nonneg_left (hpleOne z hz) hR
              simpa using hmul) (sq_nonneg _)
      calc
        _ = (((U z ω - p z) - p z * (smoothedP2Plane β d k x ω - 1)) ^ 2) *
            (smoothedP2Plane β d k x ω)⁻¹ ^ 2 := by ring
        _ ≤ (2 * (U z ω - p z) ^ 2 +
              2 * (p z * (smoothedP2Plane β d k x ω - 1)) ^ 2) * 4 := hsqDen
        _ ≤ _ := by nlinarith [hprod]
    have hpsqsum : ∑ z ∈ B, p z ^ 2 ≤ R := by
      calc
        _ ≤ ∑ z ∈ B, R * p z := by
              apply Finset.sum_le_sum
              intro z hz
              have hpR : p z ≤ R := by simpa [p] using hkernel z
              have hsq : p z ^ 2 ≤ R * p z := by
                nlinarith [mul_nonneg (hpnonneg z) (sub_nonneg.mpr hpR)]
              exact hsq
        _ = R := by rw [← Finset.mul_sum, hfreeMass]; ring
    calc
      _ ≤ ∑ z ∈ B, (8 * (U z ω - p z) ^ 2 +
            8 * p z ^ 2 * (smoothedP2Plane β d k x ω - 1) ^ 2) := by
          apply Finset.sum_le_sum
          intro z hz
          exact hpointwise z hz
      _ = 8 * V ω + 8 * (∑ z ∈ B, p z ^ 2) *
            (smoothedP2Plane β d k x ω - 1) ^ 2 := by
          simp only [V]
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
          · calc
              _ = ∑ z ∈ B, p z ^ 2 *
                  (8 * (smoothedP2Plane β d k x ω - 1) ^ 2) := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    ring
              _ = _ := by rw [← Finset.sum_mul]; ring
      _ ≤ _ := by
          have hvar : 0 ≤ (smoothedP2Plane β d k x ω - 1) ^ 2 := sq_nonneg _
          have hmul := mul_le_mul_of_nonneg_right hpsqsum hvar
          nlinarith [hmul]
  have hpointBad (ω : Disorder) (hbad : smoothedP2Plane β d k x ω < 1 / 2) :
      S ω ≤ 8 * (smoothedP2Plane β d k x ω - 1) ^ 2 := by
    have hvar : 1 / 4 ≤ (smoothedP2Plane β d k x ω - 1) ^ 2 := by nlinarith
    nlinarith [hSbound ω]
  have hpoint (ω : Disorder) :
      S ω ≤ 8 * V ω + 8 * R * (smoothedP2Plane β d k x ω - 1) ^ 2 +
        8 * (smoothedP2Plane β d k x ω - 1) ^ 2 := by
    by_cases hgood : 1 / 2 ≤ smoothedP2Plane β d k x ω
    · have h := hpointGood ω hgood
      have hv := sq_nonneg (smoothedP2Plane β d k x ω - 1)
      linarith [hVnonneg ω, hv]
    · have hbad : smoothedP2Plane β d k x ω < 1 / 2 := lt_of_not_ge hgood
      have h := hpointBad ω hbad
      exact h.trans (by nlinarith [hVnonneg ω, hR])
  have hSmeas : Measurable S := by
    dsimp [S]
    apply Finset.measurable_sum
    intro z hz
    exact ((Polymer.measurable_smoothedEndpointDist β d k x z).sub measurable_const).pow_const 2
  have hSint : Integrable S disorderLaw := by
    have hSnorm : AEStronglyMeasurable S disorderLaw := hSmeas.aestronglyMeasurable
    refine Integrable.of_bound hSnorm 2 ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hSnonneg ω)]
      exact hSbound ω
  have hpathSum : Integrable V disorderLaw := by
    dsimp [V]
    apply integrable_finsetSum
    intro z hz
    have hnumMem : MemLp (fun ω => U z ω - p z) 2 disorderLaw := by
      have heq : (fun ω => U z ω - p z) = fun ω =>
          ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
            c y s * (W y s ω - 1) * (if walkPosition y s ℓ = z then 1 else 0) := by
        funext ω
        exact hnum z ω
      rw [heq]
      apply memLp_finsetSum
      intro y hy
      apply memLp_finsetSum
      intro s hs
      by_cases hpath : walkPosition y s ℓ = z
      · have hmem := (Polymer.memLp_pathWeight β d y s 2 (by norm_num)).sub
          (memLp_const 1)
        simpa [W, hpath, mul_assoc] using hmem.const_mul (c y s)
      · simp [hpath]
    have hsq := hnumMem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using hsq
  have hVbound :
      (∫ ω, V ω ∂disorderLaw) ≤ R * (Real.exp ((ℓ : ℝ) * β ^ 2) - 1) := by
    dsimp [V]
    have hpointwise (z : Site) (hz : z ∈ B) (ω : Disorder) :
        (U z ω - p z) ^ 2 ≤ p z *
          ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
            c y s * (W y s ω - 1) ^ 2 *
              (if walkPosition y s ℓ = z then 1 else 0) := by
      let r (q : Site × (Fin ℓ → Fin 4)) :=
        c q.1 q.2 * (W q.1 q.2 ω - 1) *
          (if walkPosition q.1 q.2 ℓ = z then 1 else 0)
      let f (q : Site × (Fin ℓ → Fin 4)) :=
        c q.1 q.2 * (if walkPosition q.1 q.2 ℓ = z then 1 else 0)
      let g (q : Site × (Fin ℓ → Fin 4)) :=
        c q.1 q.2 * (W q.1 q.2 ω - 1) ^ 2 *
          (if walkPosition q.1 q.2 ℓ = z then 1 else 0)
      have hcs (q : Site × (Fin ℓ → Fin 4)) (hq : q ∈ A ×ˢ Finset.univ) :
          0 ≤ f q := by
        dsimp [f]
        by_cases hz : walkPosition q.1 q.2 ℓ = z
        · simpa [hz] using hc q.1 q.2
        · simp [hz]
      have hcg (q : Site × (Fin ℓ → Fin 4)) (hq : q ∈ A ×ˢ Finset.univ) :
          0 ≤ g q := by
        dsimp [g]
        by_cases hz : walkPosition q.1 q.2 ℓ = z
        · simpa [hz] using mul_nonneg (hc q.1 q.2) (sq_nonneg _)
        · simp [hz]
      have heq (q : Site × (Fin ℓ → Fin 4)) (hq : q ∈ A ×ˢ Finset.univ) :
          r q ^ 2 = f q * g q := by
        dsimp [r, f, g]
        split_ifs <;> ring
      have hcsum : (∑ q ∈ A ×ˢ Finset.univ, f q) = p z := by
        dsimp [f]
        rw [Finset.sum_product]
        simpa [c] using (hfree z).symm
      have hgsum : (∑ q ∈ A ×ˢ Finset.univ, g q) =
          ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
            c y s * (W y s ω - 1) ^ 2 *
              (if walkPosition y s ℓ = z then 1 else 0) := by
        dsimp [g]
        rw [Finset.sum_product]
      have hcsq := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (A ×ˢ Finset.univ)
        (fun q hq => hcs q hq)
        (fun q hq => hcg q hq)
        (fun q hq => le_of_eq (heq q hq))
      have hsumr :
          (∑ q ∈ A ×ˢ Finset.univ, r q) = U z ω - p z := by
        dsimp [r]
        rw [Finset.sum_product]
        simp only [hnum z ω]
      rw [hsumr, hcsum, hgsum] at hcsq
      exact hcsq
    have hsumBound (ω : Disorder) :
        ∑ z ∈ B, (U z ω - p z) ^ 2 ≤ R *
          ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
            c y s * (W y s ω - 1) ^ 2 := by
      calc
        _ ≤ ∑ z ∈ B, p z *
            ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
              c y s * (W y s ω - 1) ^ 2 *
                (if walkPosition y s ℓ = z then 1 else 0) := by
              apply Finset.sum_le_sum
              intro z hz
              exact hpointwise z hz ω
        _ ≤ ∑ z ∈ B, R *
            ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
              c y s * (W y s ω - 1) ^ 2 *
                (if walkPosition y s ℓ = z then 1 else 0) := by
              apply Finset.sum_le_sum
              intro z hz
              have hinner : 0 ≤ ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
                  c y s * (W y s ω - 1) ^ 2 *
                    (if walkPosition y s ℓ = z then 1 else 0) := by
                apply Finset.sum_nonneg
                intro y hy
                apply Finset.sum_nonneg
                intro s hs
                by_cases hend : walkPosition y s ℓ = z
                · simpa [hend] using mul_nonneg (hc y s) (sq_nonneg (W y s ω - 1))
                · simp [hend]
              exact mul_le_mul_of_nonneg_right (by simpa [p] using hkernel z) hinner
        _ = R * ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
              c y s * (W y s ω - 1) ^ 2 := by
              rw [← Finset.mul_sum]
              congr 1
              calc
                _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, ∑ z ∈ B,
                    c y s * (W y s ω - 1) ^ 2 *
                      (if walkPosition y s ℓ = z then 1 else 0) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl
                  intro y hy
                  rw [Finset.sum_comm]
                _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
                    c y s * (W y s ω - 1) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  apply Finset.sum_congr rfl
                  intro s hs
                  have hyend : y ∈ Polymer.endpoints x d := by simpa [A] using hy
                  have hend := shortClock_endpoints_add hyend
                    ((Polymer.mem_endpoints_iff y (walkPosition y s ℓ) ℓ).2 ⟨s, rfl⟩)
                  have hend' : walkPosition y s ℓ ∈ B := by
                    simpa [B, ℓ, Nat.add_sub_of_le hdk] using hend
                  calc
                    _ = c y s * (W y s ω - 1) ^ 2 *
                        ∑ z ∈ B, (if walkPosition y s ℓ = z then 1 else 0) := by
                          rw [← Finset.mul_sum]
                    _ = c y s * (W y s ω - 1) ^ 2 := by simp [hend']
    have hbaseInt : Integrable (fun ω =>
        ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * (W y s ω - 1) ^ 2) disorderLaw := by
      apply integrable_finsetSum
      intro y hy
      apply integrable_finsetSum
      intro s hs
      simpa [c, W] using
        (integrable_sq_pathWeight_sub_one β d y s).const_mul (c y s)
    have hmajorInt : Integrable (fun ω => R *
        ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * (W y s ω - 1) ^ 2) disorderLaw := by
      simpa [mul_assoc] using hbaseInt.const_mul R
    have hI := integral_mono hpathSum hmajorInt (fun ω => hsumBound ω)
    calc
      _ ≤ R * ∫ ω, ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * (W y s ω - 1) ^ 2 ∂disorderLaw := by
            simpa only [integral_const_mul] using hI
      _ = R * (Real.exp ((ℓ : ℝ) * β ^ 2) - 1) := by
            congr 1
            rw [integral_finsetSum _ (fun y hy =>
              integrable_finsetSum _ (fun s hs =>
                (integrable_sq_pathWeight_sub_one β d y s).const_mul (c y s)))]
            calc
              _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
                    c y s * (Real.exp ((ℓ : ℝ) * β ^ 2) - 1) := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [integral_finsetSum _ (fun s hs =>
                  (integrable_sq_pathWeight_sub_one β d y s).const_mul (c y s))]
                apply Finset.sum_congr rfl
                intro s hs
                rw [integral_const_mul, integral_sq_pathWeight_sub_one]
              _ = Real.exp ((ℓ : ℝ) * β ^ 2) - 1 := by
                calc
                  _ = ∑ y ∈ A, (∑ s : Fin ℓ → Fin 4, c y s) *
                        (Real.exp ((ℓ : ℝ) * β ^ 2) - 1) := by
                      apply Finset.sum_congr rfl
                      intro y hy
                      rw [← Finset.sum_mul]
                  _ = (∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s) *
                        (Real.exp ((ℓ : ℝ) * β ^ 2) - 1) := by rw [Finset.sum_mul]
                  _ = _ := by rw [hcoeff]; ring
  have hVbound' : (∫ ω, V ω ∂disorderLaw) ≤
      R * (Real.exp ((((k - d : ℕ) : ℝ)) * β ^ 2) - 1) := by
    simpa only [ℓ] using hVbound
  have hpointSq : ∀ ω, S ω ≤
      8 * V ω + 8 * R * (smoothedP2Plane β d k x ω - 1) ^ 2 +
        8 * (smoothedP2Plane β d k x ω - 1) ^ 2 := hpoint
  have hrightInt : Integrable (fun ω => 8 * V ω +
      8 * R * (smoothedP2Plane β d k x ω - 1) ^ 2 +
        8 * (smoothedP2Plane β d k x ω - 1) ^ 2) disorderLaw := by
    exact ((hpathSum.const_mul 8).add (hZvarInt.const_mul (8 * R))).add
      (hZvarInt.const_mul 8)
  have hfirstInt : Integrable (fun ω => 8 * V ω +
      8 * R * (smoothedP2Plane β d k x ω - 1) ^ 2) disorderLaw :=
    (hpathSum.const_mul 8).add (hZvarInt.const_mul (8 * R))
  refine ⟨hSint, ?_⟩
  calc
    _ ≤ ∫ ω, 8 * V ω +
        8 * R * (smoothedP2Plane β d k x ω - 1) ^ 2 +
          8 * (smoothedP2Plane β d k x ω - 1) ^ 2 ∂disorderLaw :=
      integral_mono hSint hrightInt hpointSq
    _ = 8 * (∫ ω, V ω ∂disorderLaw) +
        8 * R * (∫ ω, (smoothedP2Plane β d k x ω - 1) ^ 2 ∂disorderLaw) +
          8 * (∫ ω, (smoothedP2Plane β d k x ω - 1) ^ 2 ∂disorderLaw) := by
      calc
        _ = (∫ ω, 8 * V ω +
              8 * R * (smoothedP2Plane β d k x ω - 1) ^ 2 ∂disorderLaw) +
              ∫ ω, 8 * (smoothedP2Plane β d k x ω - 1) ^ 2 ∂disorderLaw :=
            integral_add hfirstInt (hZvarInt.const_mul 8)
        _ = _ := by
            rw [integral_add (hpathSum.const_mul 8) (hZvarInt.const_mul (8 * R)),
              integral_const_mul, integral_const_mul, integral_const_mul]
    _ ≤ 8 * (R * (Real.exp ((((k - d : ℕ) : ℝ)) * β ^ 2) - 1)) +
        8 * R * Q + 8 * Q := by
      have hV := mul_le_mul_of_nonneg_left hVbound' (by norm_num : (0 : ℝ) ≤ 8)
      have hZ1 := mul_le_mul_of_nonneg_left hZvar (by positivity : (0 : ℝ) ≤ 8 * R)
      have hZ2 := mul_le_mul_of_nonneg_left hZvar (by norm_num : (0 : ℝ) ≤ 8)
      exact add_le_add (add_le_add hV hZ1) hZ2

end Critical2DKPZ.Smoothing

end
