/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Polymer.WalkKernel
public import Critical2DKPZ.Renewal.CriticalWindow
public import Critical2DKPZ.RandomWalk.GaussianBridge
public import Critical2DKPZ.RandomWalk.KernelBridge
public import Critical2DKPZ.SHF.Moments.CollisionEntrance
public import Critical2DKPZ.SHF.Moments.EntranceScaling
public import Critical2DKPZ.SHF.Moments.FirstMoment
public import Critical2DKPZ.SHF.Moments.WalkBounds
import Mathlib.Tactic

/-! # Exact second moments of the walk used at the collision entrance -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

private theorem sum_step_norm_sq (x : Site) :
    ∑ a : Fin 4, ‖siteToPlane (x + srwStep a)‖ ^ 2 =
      4 * ‖siteToPlane x‖ ^ 2 + 4 := by
  rw [Fin.sum_univ_four]
  simp [srwStep, norm_siteToPlane_sq]
  simp only [Matrix.vecHead, Matrix.vecTail]
  simp only [Function.comp_apply, Fin.succ_zero_eq_one']
  ring

private noncomputable def pathSecondMoment (n : ℕ) : ℝ :=
  ∑ s : Fin n → Fin 4, ‖siteToPlane (walkPosition 0 s n)‖ ^ 2

private theorem pathSecondMoment_succ (n : ℕ) :
    pathSecondMoment (n + 1) =
      4 * pathSecondMoment n + 4 * (Fintype.card (Fin n → Fin 4) : ℝ) := by
  let e : ((Fin n → Fin 4) × Fin 4) ≃ (Fin (n + 1) → Fin 4) :=
    { toFun := fun p => Fin.snoc p.1 p.2
      invFun := fun s => (fun i => s i.castSucc, s (Fin.last n))
      left_inv := by intro p; simp
      right_inv := by intro s; exact Fin.snoc_init_self s }
  calc
    _ = ∑ s : Fin n → Fin 4, ∑ a : Fin 4,
        ‖siteToPlane (walkPosition 0 (Fin.snoc s a) (n + 1))‖ ^ 2 := by
      simp only [pathSecondMoment]
      rw [← e.sum_comp, Fintype.sum_prod_type]
      rfl
    _ = ∑ s : Fin n → Fin 4,
        (4 * ‖siteToPlane (walkPosition 0 s n)‖ ^ 2 + 4) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hrewrite : (fun a : Fin 4 =>
          ‖siteToPlane (walkPosition 0 (Fin.snoc s a) (n + 1))‖ ^ 2) =
          (fun a => ‖siteToPlane
            (walkPosition 0 s n + srwStep a)‖ ^ 2) := by
        funext a
        rw [Critical2DKPZ.walkPosition_snoc (n := n) s a]
      rw [hrewrite]
      exact sum_step_norm_sq (walkPosition 0 s n)
    _ = 4 * pathSecondMoment n + 4 * (Fintype.card (Fin n → Fin 4) : ℝ) := by
      simp only [pathSecondMoment, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun,
        Fintype.card_fin]
      ring

/-- The exact second spatial moment of the simple-walk endpoint law is its time. -/
theorem sum_srwKernel_norm_sq (n : ℕ) :
    ∑ z ∈ Polymer.endpoints 0 n,
      srwKernel n z * ‖siteToPlane z‖ ^ 2 = n := by
  have hpath : pathSecondMoment n = (n : ℝ) * 4 ^ n := by
    induction n with
    | zero => simp [pathSecondMoment, Polymer.walkPosition_zero, norm_siteToPlane_sq]
    | succ n ih =>
        rw [pathSecondMoment_succ, ih]
        simp only [Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring
  have hrepr (z : Site) : srwKernel n z =
      ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
        if walkPosition 0 s n = z then 1 else 0 := by
    simpa only [sub_zero] using Polymer.srwKernel_eq_sum n 0 z
  calc
    _ = ∑ z ∈ Polymer.endpoints 0 n, ∑ s : Fin n → Fin 4,
        (4 : ℝ)⁻¹ ^ n * (if walkPosition 0 s n = z then 1 else 0) *
          ‖siteToPlane z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hrepr z]
      rw [Finset.sum_mul]
    _ = ∑ s : Fin n → Fin 4, ∑ z ∈ Polymer.endpoints 0 n,
        (4 : ℝ)⁻¹ ^ n * (if walkPosition 0 s n = z then 1 else 0) *
          ‖siteToPlane z‖ ^ 2 := by
      rw [Finset.sum_comm]
    _ = (4 : ℝ)⁻¹ ^ n * pathSecondMoment n := by
      calc
        _ = ∑ s : Fin n → Fin 4,
            (4 : ℝ)⁻¹ ^ n * ‖siteToPlane (walkPosition 0 s n)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro s hs
          let z := walkPosition 0 s n
          have hz : z ∈ Polymer.endpoints 0 n :=
            Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
          have hsum : ∑ z' ∈ Polymer.endpoints 0 n,
              (4 : ℝ)⁻¹ ^ n * (if z = z' then 1 else 0) *
                ‖siteToPlane z'‖ ^ 2 =
              (4 : ℝ)⁻¹ ^ n * ‖siteToPlane z‖ ^ 2 := by
            rw [Finset.sum_eq_single z]
            · simp
            · intro z' hz' hne
              simp [Ne.symm hne]
            · intro hnot
              exact (hnot hz).elim
          simpa only [z] using hsum
        _ = (4 : ℝ)⁻¹ ^ n * pathSecondMoment n := by
          simp only [pathSecondMoment, Finset.mul_sum]
    _ = n := by
      rw [hpath]
      rw [inv_pow]
      field_simp [pow_ne_zero n (by norm_num : (4 : ℝ) ≠ 0)]

/-- The squared-kernel mass is the return probability at twice the time. -/
theorem sum_srwKernel_sq (n : ℕ) :
    ∑ z ∈ Polymer.endpoints 0 n, srwKernel n z ^ 2 = Renewal.returnWeight n := by
  let E := Polymer.endpoints (0 : Site) n
  have hfinite : ∑ z ∈ E, srwKernel n z ^ 2 =
      ∑' z : Site, srwKernel n z ^ 2 := by
    symm
    apply tsum_eq_sum
    intro z hz
    have hz' : z ∉ Polymer.endpoints 0 n := by simpa only [E] using hz
    have hqzero : srwKernel n z = 0 := by
      simpa only [sub_zero] using
        Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem n 0 z hz'
    rw [hqzero]
    simp
  calc
    _ = ∑' z : Site, srwKernel n z ^ 2 := by simpa only [E] using hfinite
    _ = srwKernel (2 * n) 0 := by
      simpa only [sub_zero, pow_two] using
        Critical2DKPZ.Polymer.srwKernel_collision n 0 0
    _ = Renewal.returnWeight n := rfl

private theorem sum_endpoints_start_sub (n : ℕ) (a : Site) (f : Site → ℝ) :
    ∑ z ∈ Polymer.endpoints a n, f (z - a) =
      ∑ y ∈ Polymer.endpoints 0 n, f y := by
  classical
  refine Finset.sum_bij (fun z hz => z - a) ?_ ?_ ?_ ?_
  · intro z hz
    obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff a z n).mp hz
    apply (Polymer.mem_endpoints_iff 0 (z - a) n).mpr
    refine ⟨s, ?_⟩
    rw [Polymer.walkPosition_eq_start_add] at hs
    rw [← hs]
    simp
  · intro z₁ hz₁ z₂ hz₂ heq
    ext i
    have hi := congrFun heq i
    simp only [Pi.sub_apply] at hi
    omega
  · intro y hy
    obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff 0 y n).mp hy
    refine ⟨a + y, ?_, ?_⟩
    · apply (Polymer.mem_endpoints_iff a (a + y) n).mpr
      refine ⟨s, ?_⟩
      rw [Polymer.walkPosition_eq_start_add, hs]
    · simp
  · intro z hz
    rfl

/-- Squared-kernel mass at a translated walk start is the same return mass. -/
theorem sum_srwKernel_sq_start (n : ℕ) (a : Site) :
    ∑ z ∈ Polymer.endpoints a n, srwKernel n (z - a) ^ 2 =
      Renewal.returnWeight n := by
  calc
    _ = ∑ y ∈ Polymer.endpoints 0 n, srwKernel n y ^ 2 :=
      sum_endpoints_start_sub n a (fun y => srwKernel n y ^ 2)
    _ = Renewal.returnWeight n := sum_srwKernel_sq n

/-- The first spatial moment of the squared walk kernel has the Gaussian scale. -/
theorem exists_sum_sq_srwKernel_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∑ z ∈ Polymer.endpoints 0 n,
        srwKernel n z ^ 2 * ‖siteToPlane z‖ ≤ C / Real.sqrt ((n : ℝ) + 1) := by
  obtain ⟨C, c, hC, hc, hgauss⟩ := srwKernel_gaussianBound_all_times
  refine ⟨C, hC, fun n => ?_⟩
  let E := Polymer.endpoints (0 : Site) n
  have hqBound (z : Site) : srwKernel n z ≤ C / ((n : ℝ) + 1) := by
    have hexp : Real.exp (-c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      apply div_nonpos_of_nonpos_of_nonneg
      · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)
      · positivity
    calc
      _ ≤ C / ((n : ℝ) + 1) *
          Real.exp (-c * ‖siteToPlane z‖ ^ 2 / ((n : ℝ) + 1)) := hgauss n z
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp (by positivity)
  have hmass :
      ∑ z ∈ E, srwKernel n z ^ 2 = Renewal.returnWeight n := by
    simpa only [E] using sum_srwKernel_sq n
  have hreturn : Renewal.returnWeight n ≤ C / ((n : ℝ) + 1) := by
    have hlarge : Renewal.returnWeight n ≤ C / ((2 * n : ℕ) + 1) := by
      have h := hgauss (2 * n) (0 : Site)
      have hzero : siteToPlane (0 : Site) = 0 := by
        ext i
        simp [siteToPlane]
      simpa [Renewal.returnWeight, hzero] using h
    have hden : ((n : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) + 1 := by
      push_cast
      nlinarith
    calc
      Renewal.returnWeight n ≤ C / ((2 * n : ℕ) + 1) := hlarge
      _ ≤ C / ((n : ℝ) + 1) := div_le_div_of_nonneg_left hC.le (by positivity) hden
  have hsecond :
      ∑ z ∈ E, srwKernel n z ^ 2 * ‖siteToPlane z‖ ^ 2 ≤ C := by
    calc
      _ ≤ ∑ z ∈ E, (C / ((n : ℝ) + 1)) *
          (srwKernel n z * ‖siteToPlane z‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro z hz
        have hq0 : 0 ≤ srwKernel n z := Critical2DKPZ.Polymer.kernel_nonneg n z
        have hqmul := mul_le_mul_of_nonneg_right (hqBound z) hq0
        calc
          srwKernel n z ^ 2 * ‖siteToPlane z‖ ^ 2 ≤
              (C / ((n : ℝ) + 1) * srwKernel n z) * ‖siteToPlane z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by nlinarith [hqmul]) (sq_nonneg _)
          _ = (C / ((n : ℝ) + 1)) *
              (srwKernel n z * ‖siteToPlane z‖ ^ 2) := by ring
      _ = (C / ((n : ℝ) + 1)) * n := by
        rw [← Finset.mul_sum]
        rw [show (∑ z ∈ E,
          srwKernel n z * ‖siteToPlane z‖ ^ 2) = n by
            simpa only [E] using sum_srwKernel_norm_sq n]
      _ ≤ C := by
        have hnratio : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
          apply (div_le_one (show (0 : ℝ) < (n : ℝ) + 1 by positivity)).2
          exact le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)
        calc
          C / ((n : ℝ) + 1) * n = C * ((n : ℝ) / ((n : ℝ) + 1)) := by ring
          _ ≤ C * 1 := mul_le_mul_of_nonneg_left hnratio hC.le
          _ = C := by ring
  have hreturnId : (∑ z ∈ E, srwKernel n z ^ 2) = Renewal.returnWeight n := hmass
  have hCauchy :
      ∑ z ∈ E, srwKernel n z ^ 2 * ‖siteToPlane z‖ ≤
        Real.sqrt (∑ z ∈ E, srwKernel n z ^ 2) *
          Real.sqrt (∑ z ∈ E, (srwKernel n z * ‖siteToPlane z‖) ^ 2) := by
    calc
      _ = ∑ z ∈ E, srwKernel n z * (srwKernel n z * ‖siteToPlane z‖) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt E _ _
  have hsecond' :
      ∑ z ∈ E, (srwKernel n z * ‖siteToPlane z‖) ^ 2 ≤ C := by
    calc
      _ = ∑ z ∈ E, srwKernel n z ^ 2 * ‖siteToPlane z‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ ≤ C := hsecond
  have hmain :
      ∑ z ∈ E, srwKernel n z ^ 2 * ‖siteToPlane z‖ ≤
        Real.sqrt (C / ((n : ℝ) + 1)) * Real.sqrt C := by
    calc
      _ ≤ Real.sqrt (∑ z ∈ E, srwKernel n z ^ 2) *
          Real.sqrt (∑ z ∈ E, (srwKernel n z * ‖siteToPlane z‖) ^ 2) := hCauchy
      _ ≤ _ := by
        apply mul_le_mul
        · rw [hreturnId]
          exact Real.sqrt_le_sqrt hreturn
        · exact Real.sqrt_le_sqrt hsecond'
        · exact Real.sqrt_nonneg _
        · positivity
  calc
    _ ≤ Real.sqrt (C / ((n : ℝ) + 1)) * Real.sqrt C := hmain
    _ = C / Real.sqrt ((n : ℝ) + 1) := by
      rw [Real.sqrt_div hC.le]
      calc
        _ = (Real.sqrt C * Real.sqrt C) / Real.sqrt ((n : ℝ) + 1) := by ring
        _ = _ := by
          have hsqrt : Real.sqrt C * Real.sqrt C = C := by
            nlinarith [Real.sq_sqrt hC.le]
          rw [hsqrt]

/-- The first spatial moment of the squared endpoint kernel obeys the same bound
at every translated start. -/
theorem exists_sum_sq_srwKernel_norm_start_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ a : Site,
      ∑ z ∈ Polymer.endpoints a n,
        srwKernel n (z - a) ^ 2 * ‖siteToPlane (z - a)‖ ≤
          C / Real.sqrt ((n : ℝ) + 1) := by
  obtain ⟨C, hC, hmoment⟩ := exists_sum_sq_srwKernel_norm_le
  refine ⟨C, hC, fun n a => ?_⟩
  calc
    _ = ∑ y ∈ Polymer.endpoints 0 n,
        srwKernel n y ^ 2 * ‖siteToPlane y‖ :=
      sum_endpoints_start_sub n a (fun y => srwKernel n y ^ 2 * ‖siteToPlane y‖)
    _ ≤ C / Real.sqrt ((n : ℝ) + 1) := hmoment n


/-- A linearly vanishing test centered near a coincident moving start has a
per-time slice bound with an explicit center-displacement term. -/
theorem exists_collisionSlice_abs_le_linear_center :
    ∃ C : ℝ, 0 < C ∧ ∀ (N r : ℕ) (a : Site) (c : Plane) (L : ℝ),
      0 ≤ L → ∀ (F : ℝ × Plane → ℝ),
      (∀ u x, 0 ≤ u → |F (u, x)| ≤ L * (u + ‖x - c‖)) →
      |collisionSlice r a a (fun z => F
        ((r : ℝ) / N, latticeRepresentative N z))| ≤
        L * ((((r : ℝ) / N) +
          ‖latticeRepresentative N a - c‖) * Renewal.returnWeight r +
            (Real.sqrt ((N : ℝ) / 2))⁻¹ * (C / Real.sqrt ((r : ℝ) + 1))) := by
  obtain ⟨C, hC, hmoment⟩ := exists_sum_sq_srwKernel_norm_start_le
  refine ⟨C, hC, fun N r a c L hL F hF => ?_⟩
  let E := Polymer.endpoints a r
  let u : ℝ := (r : ℝ) / N
  let scale : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
  let d : ℝ := ‖latticeRepresentative N a - c‖
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hnormRep (z : Site) :
      ‖latticeRepresentative N (z - a)‖ = scale * ‖siteToPlane (z - a)‖ := by
    simp only [scale, latticeRepresentative, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hdecomp (z : Site) : latticeRepresentative N z - c =
      latticeRepresentative N (z - a) + (latticeRepresentative N a - c) := by
    rw [latticeRepresentative_sub]
    abel
  have hdist (z : Site) :
      ‖latticeRepresentative N z - c‖ ≤
        scale * ‖siteToPlane (z - a)‖ + d := by
    rw [hdecomp z]
    calc
      ‖latticeRepresentative N (z - a) +
          (latticeRepresentative N a - c)‖ ≤
        ‖latticeRepresentative N (z - a)‖ +
          ‖latticeRepresentative N a - c‖ := norm_add_le _ _
      _ = scale * ‖siteToPlane (z - a)‖ + d := by rw [hnormRep z]
  have hmass : ∑ z ∈ E, srwKernel r (z - a) ^ 2 = Renewal.returnWeight r := by
    simpa only [E] using sum_srwKernel_sq_start r a
  have hspace : ∑ z ∈ E, srwKernel r (z - a) ^ 2 *
      ‖siteToPlane (z - a)‖ ≤ C / Real.sqrt ((r : ℝ) + 1) := by
    simpa only [E] using hmoment r a
  have hsumEq :
      ∑ z ∈ E, srwKernel r (z - a) ^ 2 *
        (L * (u + d + scale * ‖siteToPlane (z - a)‖)) =
      L * ((u + d) * Renewal.returnWeight r +
        scale * ∑ z ∈ E, srwKernel r (z - a) ^ 2 *
          ‖siteToPlane (z - a)‖) := by
    calc
      _ = ∑ z ∈ E,
          ((L * (u + d)) * srwKernel r (z - a) ^ 2 +
            (L * scale) * (srwKernel r (z - a) ^ 2 *
              ‖siteToPlane (z - a)‖)) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _ = (L * (u + d)) *
          (∑ z ∈ E, srwKernel r (z - a) ^ 2) +
          (L * scale) *
            (∑ z ∈ E, srwKernel r (z - a) ^ 2 *
              ‖siteToPlane (z - a)‖) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by rw [hmass]; ring
  have hrewrite : collisionSlice r a a (fun z => F (u, latticeRepresentative N z)) =
      ∑ z ∈ E, srwKernel r (z - a) ^ 2 * F (u, latticeRepresentative N z) := by
    simp [collisionSlice, E, pow_two]
  rw [show (fun z => F ((r : ℝ) / N, latticeRepresentative N z)) =
      (fun z => F (u, latticeRepresentative N z)) by rfl, hrewrite]
  calc
    _ ≤ ∑ z ∈ E,
        |srwKernel r (z - a) ^ 2 * F (u, latticeRepresentative N z)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z ∈ E,
        srwKernel r (z - a) ^ 2 * |F (u, latticeRepresentative N z)| := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    _ ≤ ∑ z ∈ E, srwKernel r (z - a) ^ 2 *
        (L * (u + d + scale * ‖siteToPlane (z - a)‖)) := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left
      · calc
          |F (u, latticeRepresentative N z)| ≤
              L * (u + ‖latticeRepresentative N z - c‖) := hF u _ hu
          _ ≤ L * (u + (scale * ‖siteToPlane (z - a)‖ + d)) := by
            apply mul_le_mul_of_nonneg_left _ hL
            nlinarith [hdist z]
          _ = L * (u + d + scale * ‖siteToPlane (z - a)‖) := by ring
      · exact sq_nonneg _
    _ = L * ((u + d) * Renewal.returnWeight r +
        scale * ∑ z ∈ E, srwKernel r (z - a) ^ 2 *
          ‖siteToPlane (z - a)‖) := hsumEq
    _ ≤ L * ((u + d) * Renewal.returnWeight r +
        scale * (C / Real.sqrt ((r : ℝ) + 1))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hspace hscale)) hL
    _ = _ := by dsimp [u, scale, d]

/-- The return weights have a uniform reciprocal-time upper bound. -/
theorem exists_returnWeight_le_inv :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      Renewal.returnWeight n ≤ C / ((n : ℝ) + 1) := by
  obtain ⟨C, c, hC, hc, hgauss⟩ := srwKernel_gaussianBound_all_times
  refine ⟨C, hC, fun n => ?_⟩
  have hlarge : Renewal.returnWeight n ≤ C / ((2 * n : ℕ) + 1) := by
    have h := hgauss (2 * n) (0 : Site)
    have hzero : siteToPlane (0 : Site) = 0 := by
      ext i
      simp [siteToPlane]
    simpa [Renewal.returnWeight, hzero] using h
  have hden : ((n : ℝ) + 1) ≤ ((2 * n : ℕ) : ℝ) + 1 := by
    push_cast
    nlinarith
  calc
    Renewal.returnWeight n ≤ C / ((2 * n : ℕ) + 1) := hlarge
    _ ≤ C / ((n : ℝ) + 1) := div_le_div_of_nonneg_left hC.le (by positivity) hden

private theorem inv_sqrt_add_one_le_sqrt_diff (n : ℕ) :
    1 / Real.sqrt ((n : ℝ) + 1) ≤
      2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
  let x : ℝ := n
  let a := Real.sqrt (x + 1)
  let b := Real.sqrt x
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hba : b ≤ a := by
    dsimp [a, b]
    exact Real.sqrt_le_sqrt (by linarith)
  have hden : 0 < a + b := by positivity
  have hratio : 1 / a ≤ 2 / (a + b) := by
    apply (div_le_div_iff₀ ha hden).2
    nlinarith
  have ha2 : a ^ 2 = x + 1 := by
    dsimp [a]
    exact Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = x := by
    dsimp [b]
    exact Real.sq_sqrt hx
  have hdiff : a - b = (a + b)⁻¹ := by
    field_simp [hden.ne']
    nlinarith
  have hratio' : 1 / Real.sqrt ((n : ℝ) + 1) ≤
      2 / (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) := by
    simpa [a, b, x] using hratio
  have hdiff' : Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ) =
      (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ))⁻¹ := by
    simpa [a, b, x] using hdiff
  calc
    1 / Real.sqrt ((n : ℝ) + 1) ≤
        2 / (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) := hratio'
    _ = 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
      rw [hdiff']
      ring

private theorem sum_inv_sqrt_add_one_le (K : ℕ) :
    ∑ r ∈ Finset.Icc 0 K, 1 / Real.sqrt ((r : ℝ) + 1) ≤
      2 * Real.sqrt ((K : ℝ) + 1) := by
  have htel : ∀ K : ℕ,
      ∑ r ∈ Finset.Icc 0 K,
        (Real.sqrt ((r : ℝ) + 1) - Real.sqrt (r : ℝ)) =
        Real.sqrt ((K : ℝ) + 1) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 0 ≤ K + 1), ih]
        push_cast
        ring
  calc
    _ ≤ ∑ r ∈ Finset.Icc 0 K,
        2 * (Real.sqrt ((r : ℝ) + 1) - Real.sqrt (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact inv_sqrt_add_one_le_sqrt_diff r
    _ = 2 * ∑ r ∈ Finset.Icc 0 K,
        (Real.sqrt ((r : ℝ) + 1) - Real.sqrt (r : ℝ)) := by
      rw [← Finset.mul_sum]
    _ = 2 * Real.sqrt ((K : ℝ) + 1) := by rw [htel K]

/-- A coincident moving start has the diagonal short-strip estimate, with the
scaled distance from the test's zero retained as a return-mass term. -/
theorem exists_collisionEntrance_abs_le_linear_center :
    ∃ Creturn Cmoment : ℝ, 0 < Creturn ∧ 0 < Cmoment ∧
      ∀ (N K : ℕ), 0 < N → ∀ (a : Site) (c : Plane) (L : ℝ), 0 ≤ L →
      ∀ (F : ℝ × Plane → ℝ),
      (∀ u x, 0 ≤ u → |F (u, x)| ≤ L * (u + ‖x - c‖)) →
      |collisionEntrance N 0 K a a F| ≤
        L * (Creturn * (((K : ℝ) + 1) / N) +
          ‖latticeRepresentative N a - c‖ *
            ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r +
          2 * Cmoment * (Real.sqrt ((N : ℝ) / 2))⁻¹ *
            Real.sqrt ((K : ℝ) + 1)) := by
  obtain ⟨Creturn, hCreturn, hreturn⟩ := exists_returnWeight_le_inv
  obtain ⟨Cmoment, hCmoment, hSlice⟩ :=
    exists_collisionSlice_abs_le_linear_center
  refine ⟨Creturn, Cmoment, hCreturn, hCmoment, ?_⟩
  intro N K hN a c L hL F hF
  let scale : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
  let d : ℝ := ‖latticeRepresentative N a - c‖
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hcard : ((Finset.Icc 0 K).card : ℝ) = (K : ℝ) + 1 := by simp
  have hrow : ∀ r ∈ Finset.Icc 0 K,
      |collisionSlice r a a (fun z => F
        ((r : ℝ) / N, latticeRepresentative N z))| ≤
        L * (Creturn / N + d * Renewal.returnWeight r +
          scale * Cmoment / Real.sqrt ((r : ℝ) + 1)) := by
    intro r hr
    have hu : 0 ≤ (r : ℝ) / N := by positivity
    have hbase := hSlice N r a c L hL F hF
    have hreturnr := hreturn r
    have hratio : (r : ℝ) / ((r : ℝ) + 1) ≤ 1 := by
      apply (div_le_one (by positivity)).2
      linarith
    have htime : ((r : ℝ) / N) * Renewal.returnWeight r ≤ Creturn / N := by
      calc
        ((r : ℝ) / N) * Renewal.returnWeight r ≤
            ((r : ℝ) / N) * (Creturn / ((r : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hreturnr hu
        _ = (Creturn / N) * ((r : ℝ) / ((r : ℝ) + 1)) := by
          field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
        _ ≤ Creturn / N := by
          calc
            (Creturn / N) * ((r : ℝ) / ((r : ℝ) + 1)) ≤
                (Creturn / N) * 1 :=
              mul_le_mul_of_nonneg_left hratio (by positivity)
            _ = Creturn / N := by ring
    have hscale' : (Real.sqrt ((N : ℝ) / 2))⁻¹ = scale := rfl
    have hd' : ‖latticeRepresentative N a - c‖ = d := rfl
    calc
      _ ≤ L * ((((r : ℝ) / N) +
          ‖latticeRepresentative N a - c‖) * Renewal.returnWeight r +
            (Real.sqrt ((N : ℝ) / 2))⁻¹ *
              (Cmoment / Real.sqrt ((r : ℝ) + 1))) := hbase
      _ ≤ L * (Creturn / N + d * Renewal.returnWeight r +
          scale * Cmoment / Real.sqrt ((r : ℝ) + 1)) := by
        rw [hscale', hd']
        apply mul_le_mul_of_nonneg_left _ hL
        calc
          (((r : ℝ) / N) + d) * Renewal.returnWeight r +
              scale * (Cmoment / Real.sqrt ((r : ℝ) + 1)) =
            ((r : ℝ) / N) * Renewal.returnWeight r +
              d * Renewal.returnWeight r +
              scale * Cmoment / Real.sqrt ((r : ℝ) + 1) := by ring
          _ ≤ Creturn / N + d * Renewal.returnWeight r +
              scale * Cmoment / Real.sqrt ((r : ℝ) + 1) := by
            linarith [htime]
  have hsum :
      |∑ r ∈ Finset.Icc 0 K,
        collisionSlice r a a (fun z => F
          ((r : ℝ) / N, latticeRepresentative N z))| ≤
        L * (Creturn * (((K : ℝ) + 1) / N) +
          d * ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r +
          2 * Cmoment * scale * Real.sqrt ((K : ℝ) + 1)) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc 0 K,
          |collisionSlice r a a (fun z => F
            ((r : ℝ) / N, latticeRepresentative N z))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.Icc 0 K,
          L * (Creturn / N + d * Renewal.returnWeight r +
            scale * Cmoment / Real.sqrt ((r : ℝ) + 1)) :=
        Finset.sum_le_sum fun r hr => hrow r hr
      _ = ((Finset.Icc 0 K).card : ℝ) * (L * (Creturn / N)) +
          (L * d) * ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r +
          (L * scale * Cmoment) *
            ∑ r ∈ Finset.Icc 0 K, 1 / Real.sqrt ((r : ℝ) + 1) := by
        calc
          _ = ∑ r ∈ Finset.Icc 0 K,
              (L * (Creturn / N) + L * (d * Renewal.returnWeight r) +
                (L * scale * Cmoment) *
                  (1 / Real.sqrt ((r : ℝ) + 1))) := by
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ = (∑ r ∈ Finset.Icc 0 K, L * (Creturn / N)) +
              (∑ r ∈ Finset.Icc 0 K, L * (d * Renewal.returnWeight r)) +
              (∑ r ∈ Finset.Icc 0 K,
                (L * scale * Cmoment) *
                  (1 / Real.sqrt ((r : ℝ) + 1))) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          _ = ((Finset.Icc 0 K).card : ℝ) * (L * (Creturn / N)) +
              (L * d) * ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r +
              (L * scale * Cmoment) *
                ∑ r ∈ Finset.Icc 0 K, 1 / Real.sqrt ((r : ℝ) + 1) := by
            have hA : (∑ r ∈ Finset.Icc 0 K, L * (Creturn / N)) =
                ((Finset.Icc 0 K).card : ℝ) * (L * (Creturn / N)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
            have hB : (∑ r ∈ Finset.Icc 0 K,
                L * (d * Renewal.returnWeight r)) =
                (L * d) * ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r := by
              calc
                _ = ∑ r ∈ Finset.Icc 0 K,
                    (L * d) * Renewal.returnWeight r := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  ring
                _ = _ := by rw [← Finset.mul_sum]
            have hC : (∑ r ∈ Finset.Icc 0 K,
                (L * scale * Cmoment) * (1 / Real.sqrt ((r : ℝ) + 1))) =
                (L * scale * Cmoment) *
                  ∑ r ∈ Finset.Icc 0 K, 1 / Real.sqrt ((r : ℝ) + 1) := by
              rw [← Finset.mul_sum]
            rw [hA, hB, hC]
      _ = ((K : ℝ) + 1) * (L * (Creturn / N)) +
          (L * d) * ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r +
          (L * scale * Cmoment) *
            ∑ r ∈ Finset.Icc 0 K, 1 / Real.sqrt ((r : ℝ) + 1) := by
        rw [hcard]
      _ ≤ ((K : ℝ) + 1) * (L * (Creturn / N)) +
          (L * d) * ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r +
          (L * scale * Cmoment) * (2 * Real.sqrt ((K : ℝ) + 1)) := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left (sum_inv_sqrt_add_one_le K)
        positivity
      _ = L * (Creturn * (((K : ℝ) + 1) / N) +
          d * ∑ r ∈ Finset.Icc 0 K, Renewal.returnWeight r +
          2 * Cmoment * scale * Real.sqrt ((K : ℝ) + 1)) := by ring
  have hreduce : collisionEntrance N 0 K a a F =
      ∑ r ∈ Finset.Icc 0 K,
        collisionSlice r a a (fun z => F
          ((r : ℝ) / N, latticeRepresentative N z)) := by
    simp [collisionEntrance]
  rw [hreduce]
  simpa [scale, d] using hsum


end Critical2DKPZ.SHF.Moments

end
