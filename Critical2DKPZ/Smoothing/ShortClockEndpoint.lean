/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.ShortDurationMoments
public import Critical2DKPZ.Smoothing.EndpointDistribution
public import Critical2DKPZ.Smoothing.KernelVariation
public import Critical2DKPZ.Polymer.BlockMeasurability
public import Critical2DKPZ.Polymer.WalkKernel
import Mathlib.Tactic

/-! # Short-clock endpoint perturbations -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Smoothing

/-- Concatenating two reachable walk segments gives a reachable endpoint at the summed time. -/
theorem shortClock_endpoints_add {m n : ℕ} {x y z : Site}
    (hy : y ∈ Polymer.endpoints x m) (hz : z ∈ Polymer.endpoints y n) :
    z ∈ Polymer.endpoints x (m + n) := by
  apply (Polymer.mem_endpoints_iff x z (m + n)).2
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff x y m).1 hy
  obtain ⟨t, ht⟩ := (Polymer.mem_endpoints_iff y z n).1 hz
  exact ⟨Fin.append s t, by rw [Polymer.walkPosition_append_end, hs, ht]⟩

/-- The average absolute deviation of the path weights in a short segment started from a
diffuse walk kernel. -/
noncomputable def shortClockPathDeviation (β : ℝ) (d ℓ : ℕ) (x : Site) (ω : Disorder) : ℝ :=
  ∑ y ∈ Polymer.endpoints x d, ∑ s : Fin ℓ → Fin 4,
    (srwKernel d (y - x) * (4 : ℝ)⁻¹ ^ ℓ) *
      |Polymer.pathWeight β d y s ω - 1|

/-- The `ℓ¹` distance between the random endpoint law of the short polymer segment and the
unweighted walk endpoint law. -/
noncomputable def shortClockEndpointTV (β : ℝ) (d k : ℕ) (x : Site) (ω : Disorder) : ℝ :=
  ∑ z ∈ Polymer.endpoints x k,
    |smoothedEndpointDist β d k x ω z - srwKernel k (z - x)|

/-- Normalizing the short polymer path weights costs only the inverse short mass; before
normalization, the endpoint total variation is bounded by the average path-weight deviation. -/
theorem shortClockEndpointTV_le_pathDeviation (β : ℝ) {d k : ℕ} (hdk : d ≤ k)
    (x : Site) (ω : Disorder) :
    shortClockEndpointTV β d k x ω ≤
      2 * shortClockPathDeviation β d (k - d) x ω /
        smoothedP2Plane β d k x ω := by
  classical
  let ℓ := k - d
  let A := Polymer.endpoints x d
  let B := Polymer.endpoints x k
  let c (y : Site) (s : Fin ℓ → Fin 4) :=
    srwKernel d (y - x) * (4 : ℝ)⁻¹ ^ ℓ
  let W (y : Site) (s : Fin ℓ → Fin 4) := Polymer.pathWeight β d y s ω
  have hc (y : Site) (s : Fin ℓ → Fin 4) : 0 ≤ c y s := by
    dsimp [c]
    exact mul_nonneg (Polymer.kernel_nonneg d (y - x)) (by positivity)
  have hZpos : 0 < smoothedP2Plane β d k x ω :=
    Polymer.smoothedP2Plane_pos β d k x ω
  have hmass : ∑ y ∈ A, srwKernel d (y - x) = 1 :=
    Polymer.sum_srwKernel_endpoints d x
  have hwalk : ∑ s : Fin ℓ → Fin 4, (4 : ℝ)⁻¹ ^ ℓ = 1 :=
    Polymer.sum_walkProbability ℓ
  have hcoeff : ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s = 1 := by
    calc
      _ = ∑ y ∈ A, srwKernel d (y - x) *
          (∑ s : Fin ℓ → Fin 4, (4 : ℝ)⁻¹ ^ ℓ) := by
            apply Finset.sum_congr rfl
            intro y hy
            simp only [c]
            rw [← Finset.mul_sum]
      _ = (∑ y ∈ A, srwKernel d (y - x)) *
          (∑ s : Fin ℓ → Fin 4, (4 : ℝ)⁻¹ ^ ℓ) := by
            rw [Finset.sum_mul]
      _ = 1 := by rw [hmass, hwalk]; norm_num
  have hZexp : smoothedP2Plane β d k x ω =
      ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s * W y s := by
    rw [Polymer.smoothedP2Plane_eq_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [Polymer.pointToPlane_eq_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [c, W]
    ring
  have hnum (z : Site) :
      (∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) =
        ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * W y s * (if walkPosition y s ℓ = z then 1 else 0) := by
    calc
      _ = ∑ y ∈ A, srwKernel d (y - x) * pointToPoint β d ℓ y z ω := by
        apply tsum_eq_sum
        intro y hy
        rw [Polymer.srwKernel_eq_zero_of_not_mem d x y (by simpa [A] using hy)]
        simp
      _ = ∑ y ∈ A, srwKernel d (y - x) *
          (∑ s : Fin ℓ → Fin 4, (4 : ℝ)⁻¹ ^ ℓ *
            Polymer.pathWeight β d y s ω *
              (if walkPosition y s ℓ = z then 1 else 0)) := by
        simp_rw [Polymer.pointToPoint_eq_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        dsimp [c, W]
        ring
  have hfree (z : Site) :
      srwKernel k (z - x) =
        ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * (if walkPosition y s ℓ = z then 1 else 0) := by
    have htime : d + ℓ = k := Nat.add_sub_of_le hdk
    rw [← htime, Polymer.srwKernel_convolution]
    calc
      _ = ∑ y ∈ A, srwKernel d (y - x) * srwKernel ℓ (z - y) := by
        apply tsum_eq_sum
        intro y hy
        rw [Polymer.srwKernel_eq_zero_of_not_mem d x y (by simpa [A] using hy)]
        simp
      _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * (if walkPosition y s ℓ = z then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Polymer.srwKernel_eq_sum ℓ y z]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        dsimp [c]
        ring
  have hnumSub (z : Site) :
      (∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
          srwKernel k (z - x) =
        ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * (W y s - 1) * (if walkPosition y s ℓ = z then 1 else 0) := by
    rw [hnum z, hfree z]
    calc
      _ = ∑ y ∈ A,
          ((∑ s : Fin ℓ → Fin 4, c y s * W y s *
              (if walkPosition y s ℓ = z then 1 else 0)) -
            ∑ s : Fin ℓ → Fin 4, c y s *
              (if walkPosition y s ℓ = z then 1 else 0)) := by
                rw [Finset.sum_sub_distrib]
      _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          (c y s * W y s * (if walkPosition y s ℓ = z then 1 else 0) -
            c y s * (if walkPosition y s ℓ = z then 1 else 0)) := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [Finset.sum_sub_distrib]
      _ = _ := by
                apply Finset.sum_congr rfl
                intro y hy
                apply Finset.sum_congr rfl
                intro s hs
                by_cases hpath : walkPosition y s ℓ = z
                · simp [hpath, W]
                  ring
                · simp [hpath, W]
  have hsumBase : ∑ z ∈ B, srwKernel k (z - x) = 1 :=
    Polymer.sum_srwKernel_endpoints k x
  have hsumTVnumerator :
      (∑ z ∈ B,
        |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
          srwKernel k (z - x)|) ≤ shortClockPathDeviation β d ℓ x ω := by
    rw [shortClockPathDeviation]
    calc
      _ ≤ ∑ z ∈ B, ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          |c y s * (W y s - 1) * (if walkPosition y s ℓ = z then 1 else 0)| := by
            apply Finset.sum_le_sum
            intro z hz
            rw [hnumSub z]
            calc
              _ ≤ ∑ y ∈ A, abs (∑ s : Fin ℓ → Fin 4,
                    c y s * (W y s - 1) *
                      (if walkPosition y s ℓ = z then 1 else 0)) :=
                    Finset.abs_sum_le_sum_abs _ _
              _ ≤ _ := by
                    apply Finset.sum_le_sum
                    intro y hy
                    exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * |W y s - 1| := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro s hs
            have hyend : y ∈ Polymer.endpoints x d := hy
            have hsend : walkPosition y s ℓ ∈ Polymer.endpoints y ℓ :=
              (Polymer.mem_endpoints_iff y (walkPosition y s ℓ) ℓ).2 ⟨s, rfl⟩
            have hend : walkPosition y s ℓ ∈ B := by
              have hadd := shortClock_endpoints_add hyend hsend
              simpa [B, show d + ℓ = k from Nat.add_sub_of_le hdk] using hadd
            have hindicator :
                (∑ z ∈ B,
                  |c y s * (W y s - 1) *
                    (if walkPosition y s ℓ = z then 1 else 0)|) =
                  c y s * |W y s - 1| := by
              calc
                _ = ∑ z ∈ B,
                    c y s * |W y s - 1| *
                      (if walkPosition y s ℓ = z then 1 else 0) := by
                        apply Finset.sum_congr rfl
                        intro z hz
                        by_cases hpath : walkPosition y s ℓ = z <;>
                          simp [hpath, abs_mul, abs_of_nonneg (hc y s)]
                _ = c y s * |W y s - 1| := by
                      rw [← Finset.mul_sum]
                      simp [hend]
            simpa only [abs_mul, abs_of_nonneg (hc y s)] using hindicator
      _ = shortClockPathDeviation β d ℓ x ω := rfl
  have hZsub : |smoothedP2Plane β d k x ω - 1| ≤
      shortClockPathDeviation β d ℓ x ω := by
    rw [hZexp]
    have hrewrite :
        (∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s * W y s) - 1 =
          ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s * (W y s - 1) := by
      calc
        _ = (∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s * W y s) -
            (∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s) := by rw [hcoeff]
        _ = ∑ y ∈ A,
            ((∑ s : Fin ℓ → Fin 4, c y s * W y s) -
              (∑ s : Fin ℓ → Fin 4, c y s)) := by
                rw [← Finset.sum_sub_distrib]
        _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
            (c y s * W y s - c y s) := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [← Finset.sum_sub_distrib]
        _ = _ := by
                apply Finset.sum_congr rfl
                intro y hy
                apply Finset.sum_congr rfl
                intro s hs
                ring
    rw [hrewrite, shortClockPathDeviation]
    calc
      |∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s * (W y s - 1)| ≤
          ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, |c y s * (W y s - 1)| := by
            calc
              _ ≤ ∑ y ∈ A, |∑ s : Fin ℓ → Fin 4,
                  c y s * (W y s - 1)| := Finset.abs_sum_le_sum_abs _ _
              _ ≤ _ := by
                    apply Finset.sum_le_sum
                    intro y hy
                    exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s * |W y s - 1| := by
            apply Finset.sum_congr rfl
            intro y hy
            apply Finset.sum_congr rfl
            intro s hs
            rw [abs_mul, abs_of_nonneg (by exact hc y s)]
      _ = _ := rfl
  have hdist (z : Site) :
      smoothedEndpointDist β d k x ω z =
        (∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) /
          smoothedP2Plane β d k x ω := by
    rfl
  have hpoint (z : Site) :
      |smoothedEndpointDist β d k x ω z - srwKernel k (z - x)| =
        |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
          smoothedP2Plane β d k x ω * srwKernel k (z - x)| /
          smoothedP2Plane β d k x ω := by
    have hfrac :
        (∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) /
            smoothedP2Plane β d k x ω - srwKernel k (z - x) =
          ((∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
            smoothedP2Plane β d k x ω * srwKernel k (z - x)) /
            smoothedP2Plane β d k x ω := by
      field_simp [ne_of_gt hZpos]
    rw [hdist z, hfrac]
    rw [abs_div, abs_of_pos hZpos]
  have hTVbound :
      (∑ z ∈ B, |smoothedEndpointDist β d k x ω z - srwKernel k (z - x)|) ≤
        ((∑ z ∈ B,
          |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
            srwKernel k (z - x)|) +
          |smoothedP2Plane β d k x ω - 1|) / smoothedP2Plane β d k x ω := by
    calc
      _ = (∑ z ∈ B,
          |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
            smoothedP2Plane β d k x ω * srwKernel k (z - x)|) /
          smoothedP2Plane β d k x ω := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro z hz
            exact hpoint z
      _ ≤ _ := by
          rw [div_le_div_iff_of_pos_right hZpos]
          have htri (z : Site) :
              |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
                  smoothedP2Plane β d k x ω * srwKernel k (z - x)| ≤
                |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
                    srwKernel k (z - x)| +
                  |smoothedP2Plane β d k x ω - 1| * srwKernel k (z - x) := by
              calc
                _ = |((∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
                      srwKernel k (z - x)) -
                    (smoothedP2Plane β d k x ω - 1) * srwKernel k (z - x)| := by
                      congr 1
                      simp only [sub_eq_add_neg, add_comm]
                      ring
                _ ≤ _ := by
                  calc
                    _ ≤ |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
                          srwKernel k (z - x)| +
                        |(smoothedP2Plane β d k x ω - 1) * srwKernel k (z - x)| :=
                          abs_sub _ _
                    _ = _ := by rw [abs_mul, abs_of_nonneg
                      (Polymer.kernel_nonneg k (z - x))]
          calc
            _ ≤ (∑ z ∈ B,
                  (|(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
                    srwKernel k (z - x)| +
                    |smoothedP2Plane β d k x ω - 1| * srwKernel k (z - x))) :=
                  Finset.sum_le_sum fun z hz => htri z
            _ = _ := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hsumBase]
                  ring
  have hnumle :
      (∑ z ∈ B,
        |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
          srwKernel k (z - x)|) + |smoothedP2Plane β d k x ω - 1| ≤
        2 * shortClockPathDeviation β d ℓ x ω := by
    calc
      _ ≤ shortClockPathDeviation β d ℓ x ω +
          shortClockPathDeviation β d ℓ x ω :=
            add_le_add hsumTVnumerator hZsub
      _ = _ := by ring
  rw [shortClockEndpointTV]
  calc
    _ ≤ ((∑ z ∈ B,
          |(∑' y, srwKernel d (y - x) * pointToPoint β d ℓ y z ω) -
            srwKernel k (z - x)|) +
          |smoothedP2Plane β d k x ω - 1|) /
        smoothedP2Plane β d k x ω := hTVbound
    _ ≤ (2 * shortClockPathDeviation β d ℓ x ω) /
        smoothedP2Plane β d k x ω := by
          exact div_le_div_of_nonneg_right hnumle (le_of_lt hZpos)

private theorem integral_pathWeight_sub_one_sq (β : ℝ) (d : ℕ) (y : Site)
    {ℓ : ℕ} (s : Fin ℓ → Fin 4) :
    Integrable (fun ω => |Polymer.pathWeight β d y s ω - 1| ^ 2) disorderLaw ∧
    (∫ ω, |Polymer.pathWeight β d y s ω - 1| ^ 2 ∂disorderLaw) =
      Real.exp ((ℓ : ℝ) * β ^ 2) - 1 := by
  let W : Disorder → ℝ := Polymer.pathWeight β d y s
  have hWmem : MemLp W 2 disorderLaw := Polymer.memLp_pathWeight β d y s 2 (by norm_num)
  have hWint : Integrable W disorderLaw := hWmem.integrable (by norm_num)
  have hW2int : Integrable (fun ω => W ω ^ 2) disorderLaw := by
    have h := hWmem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hDint : Integrable (fun ω => |W ω - 1| ^ 2) disorderLaw := by
    have h := (hWmem.sub (memLp_const (1 : ℝ))).integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using h
  have hDint' : Integrable (fun ω => (W ω - 1) ^ 2) disorderLaw := by
    apply hDint.congr
    filter_upwards [] with ω
    exact sq_abs (W ω - 1)
  have hpolyInt : Integrable (fun ω => W ω ^ 2 - 2 * W ω + 1) disorderLaw :=
    (hW2int.sub (hWint.const_mul 2)).add (integrable_const 1)
  have hpolyEq :
      (∫ ω, (W ω - 1) ^ 2 ∂disorderLaw) =
        (∫ ω, W ω ^ 2 ∂disorderLaw) - 2 * (∫ ω, W ω ∂disorderLaw) + 1 := by
    calc
      _ = ∫ ω, W ω ^ 2 - 2 * W ω + 1 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = (∫ ω, W ω ^ 2 - 2 * W ω ∂disorderLaw) +
            ∫ _ω : Disorder, (1 : ℝ) ∂disorderLaw :=
        integral_add (hW2int.sub (hWint.const_mul 2)) (integrable_const 1)
      _ = _ := by
        rw [integral_sub hW2int (hWint.const_mul 2), integral_const_mul]
        simp only [MeasureTheory.integral_const, probReal_univ]
        ring
  have hWmean : ∫ ω, W ω ∂disorderLaw = 1 := by
    simpa only [W] using Polymer.integral_pathWeight β d y s
  have hWsecond : ∫ ω, W ω ^ 2 ∂disorderLaw = Real.exp ((ℓ : ℝ) * β ^ 2) := by
    have h := Critical2DKPZ.MomentBounds.integral_pathWeight_pow β d y s 2
    convert h using 1
    congr 1
    ring
  refine ⟨hDint, ?_⟩
  have hEq : (fun ω => |W ω - 1| ^ 2) = fun ω => (W ω - 1) ^ 2 := by
    funext ω
    exact sq_abs (W ω - 1)
  have hIntegralEq :
      (∫ ω, |W ω - 1| ^ 2 ∂disorderLaw) =
        ∫ ω, (W ω - 1) ^ 2 ∂disorderLaw := by
    rw [hEq]
  rw [hIntegralEq, hpolyEq, hWsecond, hWmean]
  ring

/-- The squared short-clock path deviation has the single-path second-moment scale. -/
theorem integral_shortClockPathDeviation_sq_le (β : ℝ) (d ℓ : ℕ) (x : Site) :
    Integrable (fun ω => shortClockPathDeviation β d ℓ x ω ^ 2) disorderLaw ∧
    (∫ ω, shortClockPathDeviation β d ℓ x ω ^ 2 ∂disorderLaw) ≤
      Real.exp ((ℓ : ℝ) * β ^ 2) - 1 := by
  classical
  let A := Polymer.endpoints x d
  let c (y : Site) (s : Fin ℓ → Fin 4) :=
    srwKernel d (y - x) * (4 : ℝ)⁻¹ ^ ℓ
  let W (y : Site) (s : Fin ℓ → Fin 4) := Polymer.pathWeight β d y s
  let D : Disorder → ℝ := fun ω =>
    ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s * |W y s ω - 1| ^ 2
  have hc (y : Site) (s : Fin ℓ → Fin 4) : 0 ≤ c y s := by
    dsimp [c]
    exact mul_nonneg (Polymer.kernel_nonneg d (y - x)) (by positivity)
  have hcoeff : ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s = 1 := by
    calc
      _ = (∑ y ∈ A, srwKernel d (y - x)) *
          (∑ s : Fin ℓ → Fin 4, (4 : ℝ)⁻¹ ^ ℓ) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y hy
            dsimp [c]
            rw [← Finset.mul_sum]
      _ = 1 := by
        rw [Polymer.sum_srwKernel_endpoints, Polymer.sum_walkProbability]
        norm_num
  have hDint : Integrable D disorderLaw := by
    dsimp [D]
    apply integrable_finsetSum
    intro y hy
    apply integrable_finsetSum
    intro s hs
    exact (integral_pathWeight_sub_one_sq β d y s).1.const_mul _
  have hDmean : (∫ ω, D ω ∂disorderLaw) =
      Real.exp ((ℓ : ℝ) * β ^ 2) - 1 := by
    dsimp [D]
    calc
      _ = ∑ y ∈ A, ∫ ω, ∑ s : Fin ℓ → Fin 4,
          c y s * |W y s ω - 1| ^ 2 ∂disorderLaw := by
            rw [integral_finsetSum _ (fun y hy =>
              integrable_finsetSum _ (fun s hs =>
                (integral_pathWeight_sub_one_sq β d y s).1.const_mul (c y s)))]
      _ = ∑ y ∈ A, ∑ s : Fin ℓ → Fin 4,
          c y s * (Real.exp ((ℓ : ℝ) * β ^ 2) - 1) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [integral_finsetSum _ (fun s hs =>
              (integral_pathWeight_sub_one_sq β d y s).1.const_mul (c y s))]
            apply Finset.sum_congr rfl
            intro s hs
            rw [integral_const_mul, (integral_pathWeight_sub_one_sq β d y s).2]
      _ = _ := by
        calc
          _ = (∑ y ∈ A, ∑ s : Fin ℓ → Fin 4, c y s) *
              (Real.exp ((ℓ : ℝ) * β ^ 2) - 1) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro y hy
                rw [Finset.sum_mul]
          _ = _ := by rw [hcoeff]; ring
  have hdevNonneg (ω : Disorder) : 0 ≤ shortClockPathDeviation β d ℓ x ω := by
    dsimp [shortClockPathDeviation]
    apply Finset.sum_nonneg
    intro y hy
    apply Finset.sum_nonneg
    intro s hs
    exact mul_nonneg (hc y s) (abs_nonneg _)
  have hdevMem : MemLp (fun ω => shortClockPathDeviation β d ℓ x ω) 2 disorderLaw := by
    unfold shortClockPathDeviation
    apply memLp_finsetSum
    intro y hy
    apply memLp_finsetSum
    intro s hs
    have hpw : MemLp (fun ω => Polymer.pathWeight β d y s ω - 1)
        (2 : ℝ≥0∞) disorderLaw :=
      (Polymer.memLp_pathWeight β d y s 2 (by norm_num)).sub (memLp_const 1)
    have habs : MemLp (fun ω => |Polymer.pathWeight β d y s ω - 1|)
        (2 : ℝ≥0∞) disorderLaw := by
      simpa only [Real.norm_eq_abs] using hpw.norm
    exact habs.const_mul (c y s)
  have hdevInt : Integrable
      (fun ω => shortClockPathDeviation β d ℓ x ω ^ 2) disorderLaw := by
    have h := hdevMem.integrable_norm_pow'
    have heq : (fun ω => ‖shortClockPathDeviation β d ℓ x ω‖ ^ 2) =
        fun ω => shortClockPathDeviation β d ℓ x ω ^ 2 := by
      funext ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hdevNonneg ω)]
    rw [heq] at h
    exact h
  have hdevSq (ω : Disorder) : shortClockPathDeviation β d ℓ x ω ^ 2 ≤ D ω := by
    let P := A ×ˢ (Finset.univ : Finset (Fin ℓ → Fin 4))
    let coeff (p : Site × (Fin ℓ → Fin 4)) := c p.1 p.2
    let err (p : Site × (Fin ℓ → Fin 4)) := |W p.1 p.2 ω - 1|
    have hcoeffP : ∑ p ∈ P, coeff p = 1 := by
      dsimp [P, coeff]
      rw [Finset.sum_product]
      exact hcoeff
    have hdevRep : ∑ p ∈ P, coeff p * err p =
        shortClockPathDeviation β d ℓ x ω := by
      dsimp [P, coeff, err, shortClockPathDeviation, c, W]
      rw [Finset.sum_product]
    have hDrep : ∑ p ∈ P, coeff p * err p ^ 2 = D ω := by
      dsimp [P, coeff, err, D]
      rw [Finset.sum_product]
    have hcs : (∑ p ∈ P, coeff p * err p) ^ 2 ≤
        (∑ p ∈ P, coeff p) * ∑ p ∈ P, coeff p * err p ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul P
        (fun p hp => hc p.1 p.2)
        (fun p hp => mul_nonneg (hc p.1 p.2) (sq_nonneg _))
        (fun p hp => le_of_eq (by ring))
    rw [hdevRep, hcoeffP, one_mul, hDrep] at hcs
    exact hcs
  refine ⟨hdevInt, ?_⟩
  calc
    _ ≤ ∫ ω, D ω ∂disorderLaw := integral_mono hdevInt hDint hdevSq
    _ = Real.exp ((ℓ : ℝ) * β ^ 2) - 1 := hDmean


/-- The squared endpoint total variation is bounded by the short path deviation and the
short-clock mass fluctuation. The displayed integral estimate includes its integrability clause. -/
theorem integral_shortClockEndpointTV_sq_le (β : ℝ) {d k : ℕ}
    (hdk : d ≤ k) (x : Site) (Q : ℝ)
    (hZvarInt : Integrable (fun ω => (smoothedP2Plane β d k x ω - 1) ^ 2) disorderLaw)
    (hZvar : (∫ ω, (smoothedP2Plane β d k x ω - 1) ^ 2 ∂disorderLaw) ≤ Q) :
    Integrable (fun ω => shortClockEndpointTV β d k x ω ^ 2) disorderLaw ∧
    (∫ ω, shortClockEndpointTV β d k x ω ^ 2 ∂disorderLaw) ≤
      16 * (Real.exp (((k - d : ℕ) : ℝ) * β ^ 2) - 1) + 16 * Q := by
  classical
  let B := Polymer.endpoints x k
  let Z : Disorder → ℝ := smoothedP2Plane β d k x
  let S : Disorder → ℝ := fun ω => shortClockEndpointTV β d k x ω ^ 2
  have hprob (ω : Disorder) := smoothedEndpointDist_probability β hdk x ω
  have hCB : (Polymer.endpoints x d).biUnion
      (fun y => Polymer.endpoints y (k - d)) ⊆ B := by
    intro z hz
    rcases Finset.mem_biUnion.mp hz with ⟨y, hy, hzy⟩
    have hadd := shortClock_endpoints_add hy hzy
    simpa [B, Nat.add_sub_of_le hdk] using hadd
  have hprobMass (ω : Disorder) :
      ∑ z ∈ B, smoothedEndpointDist β d k x ω z = 1 := by
    calc
      _ = ∑ z ∈ (Polymer.endpoints x d).biUnion
          (fun y => Polymer.endpoints y (k - d)), smoothedEndpointDist β d k x ω z := by
            symm
            apply Finset.sum_subset hCB
            intro z hz hznot
            exact (hprob ω).1 z hznot
      _ = 1 := (hprob ω).2.2
  have hfreeMass : ∑ z ∈ B, srwKernel k (z - x) = 1 :=
    Polymer.sum_srwKernel_endpoints k x
  have hTVnonneg (ω : Disorder) : 0 ≤ shortClockEndpointTV β d k x ω := by
    dsimp [shortClockEndpointTV]
    apply Finset.sum_nonneg
    intro z hz
    exact abs_nonneg _
  have hTVleTwo (ω : Disorder) : shortClockEndpointTV β d k x ω ≤ 2 := by
    dsimp [shortClockEndpointTV]
    calc
      _ ≤ ∑ z ∈ B,
          (smoothedEndpointDist β d k x ω z + srwKernel k (z - x)) := by
            apply Finset.sum_le_sum
            intro z hz
            have hη0 := (hprob ω).2.1 z
            have hν0 := Polymer.kernel_nonneg k (z - x)
            calc
              |smoothedEndpointDist β d k x ω z - srwKernel k (z - x)| ≤
                  |smoothedEndpointDist β d k x ω z| + |srwKernel k (z - x)| := by
                    simpa only [sub_zero, zero_sub, abs_neg] using
                      (abs_sub_le (smoothedEndpointDist β d k x ω z) 0
                        (srwKernel k (z - x)))
              _ = smoothedEndpointDist β d k x ω z + srwKernel k (z - x) := by
                    rw [abs_of_nonneg hη0, abs_of_nonneg hν0]
      _ = 2 := by rw [Finset.sum_add_distrib, hprobMass ω, hfreeMass]; norm_num
  have hTVmeas : Measurable (fun ω => shortClockEndpointTV β d k x ω) := by
    unfold shortClockEndpointTV
    apply Finset.measurable_sum
    intro z hz
    exact ((Polymer.measurable_smoothedEndpointDist β d k x z).sub measurable_const).abs
  have hSint : Integrable S disorderLaw := by
    apply Integrable.of_bound (by
      dsimp [S]
      exact hTVmeas.pow_const 2 |>.aestronglyMeasurable) 4
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    dsimp [S]
    nlinarith [hTVnonneg ω, hTVleTwo ω]
  have hdev := integral_shortClockPathDeviation_sq_le β d (k - d) x
  have hpoint (ω : Disorder) : S ω ≤
      16 * shortClockPathDeviation β d (k - d) x ω ^ 2 + 16 * (Z ω - 1) ^ 2 := by
    by_cases hgood : (1 / 2 : ℝ) ≤ Z ω
    · have hdevnonneg : 0 ≤ shortClockPathDeviation β d (k - d) x ω := by
        unfold shortClockPathDeviation
        apply Finset.sum_nonneg
        intro y hy
        apply Finset.sum_nonneg
        intro s hs
        exact mul_nonneg
          (mul_nonneg (Polymer.kernel_nonneg d (y - x)) (by positivity)) (abs_nonneg _)
      have hTVbound : shortClockEndpointTV β d k x ω ≤
          4 * shortClockPathDeviation β d (k - d) x ω := by
        have hTV := shortClockEndpointTV_le_pathDeviation β hdk x ω
        have hratio :
            2 * shortClockPathDeviation β d (k - d) x ω / Z ω ≤
              4 * shortClockPathDeviation β d (k - d) x ω := by
          apply (div_le_iff₀ (Polymer.smoothedP2Plane_pos β d k x ω)).2
          have hmul := mul_le_mul_of_nonneg_left hgood
            (show 0 ≤ 4 * shortClockPathDeviation β d (k - d) x ω by positivity)
          nlinarith
        exact hTV.trans hratio
      have hsq : shortClockEndpointTV β d k x ω ^ 2 ≤
          (4 * shortClockPathDeviation β d (k - d) x ω) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hTVbound)
          (add_nonneg (hTVnonneg ω)
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hdevnonneg))]
      change shortClockEndpointTV β d k x ω ^ 2 ≤ _
      calc
        _ ≤ (4 * shortClockPathDeviation β d (k - d) x ω) ^ 2 := hsq
        _ = 16 * shortClockPathDeviation β d (k - d) x ω ^ 2 := by ring
        _ ≤ 16 * shortClockPathDeviation β d (k - d) x ω ^ 2 +
              16 * (Z ω - 1) ^ 2 := le_add_of_nonneg_right (by positivity)
    · have hZlt : Z ω < 1 / 2 := lt_of_not_ge hgood
      have hbad : (1 / 4 : ℝ) ≤ (Z ω - 1) ^ 2 := by nlinarith
      have hTVsq : shortClockEndpointTV β d k x ω ^ 2 ≤ 4 := by
        nlinarith [hTVnonneg ω, hTVleTwo ω]
      dsimp [S, Z]
      nlinarith [hTVsq, hbad, sq_nonneg (shortClockEndpointTV β d k x ω)]
  have hmajorInt : Integrable
      (fun ω => 16 * shortClockPathDeviation β d (k - d) x ω ^ 2 +
        16 * (Z ω - 1) ^ 2) disorderLaw := by
    exact (hdev.1.const_mul 16).add (hZvarInt.const_mul 16)
  have hfinal := integral_mono hSint hmajorInt hpoint
  refine ⟨hSint, ?_⟩
  calc
    _ ≤ 16 * (∫ ω, shortClockPathDeviation β d (k - d) x ω ^ 2 ∂disorderLaw) +
        16 * (∫ ω, (Z ω - 1) ^ 2 ∂disorderLaw) := by
          simpa only [integral_add (hdev.1.const_mul 16) (hZvarInt.const_mul 16),
            integral_const_mul, Z] using hfinal
    _ ≤ 16 * (Real.exp (((k - d : ℕ) : ℝ) * β ^ 2) - 1) + 16 * Q := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hdev.2 (by norm_num))
            (mul_le_mul_of_nonneg_left hZvar (by norm_num))
