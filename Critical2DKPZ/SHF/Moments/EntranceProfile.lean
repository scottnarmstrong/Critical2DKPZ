/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionEntrance
public import Critical2DKPZ.SHF.Moments.GapOverlap
public import Critical2DKPZ.SHF.Moments.TimeRounding
public import Critical2DKPZ.PolymerCalculus.OverlapRescaling
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Critical2DKPZ.Renewal.ReturnSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Continuous time-only tests of the collision entrance -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- A right-endpoint Riemann sum with mesh `1/N` and a possibly moving endpoint `M/N`. -/
def collisionEntranceScaledPrefixSum (f : ℝ → ℝ) (N M : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ Finset.range M, f (((k + 1 : ℕ) : ℝ) / N)

private theorem sum_Icc_interval_as_sub (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ r ∈ Finset.Icc (m + 1) n, f r) =
      (∑ r ∈ Finset.Icc 1 n, f r) - ∑ r ∈ Finset.Icc 1 m, f r := by
  induction n with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      simp
  | succ n ih =>
      by_cases heq : m = n + 1
      · subst m
        simp
      · have hm : m ≤ n := by omega
        rw [Finset.sum_Icc_succ_top (by omega : m + 1 ≤ n + 1),
          Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
        rw [ih hm]
        ring

private theorem collisionEntranceScaledPrefixSum_eq_Icc (f : ℝ → ℝ) (N M : ℕ) :
    collisionEntranceScaledPrefixSum f N M = (N : ℝ)⁻¹ *
      ∑ r ∈ Finset.Icc 1 M, f ((r : ℝ) / N) := by
  dsimp [collisionEntranceScaledPrefixSum]
  congr 1
  symm
  exact Renewal.sum_Icc_one_eq_sum_range (fun r : ℕ => f ((r : ℝ) / N)) M

/-- On each grid interval the right-endpoint sum differs from the interval integral
by at most the modulus of continuity times the interval length. -/
private theorem norm_collisionEntranceScaledPrefixSum_sub_variableIntegral (f : ℝ → ℝ) (hf : Continuous f)
    {N M : ℕ} {R ε : ℝ} (hN : 0 < N) (_hR : 0 ≤ R)
    (hMN : (M : ℝ) / N ≤ R) (_hε : 0 ≤ ε)
    (hmod : ∀ x ∈ Icc (0 : ℝ) R, ∀ y ∈ Icc (0 : ℝ) R,
      |x - y| ≤ (N : ℝ)⁻¹ → |f x - f y| ≤ ε) :
    ‖collisionEntranceScaledPrefixSum f N M - ∫ x in (0 : ℝ)..((M : ℝ) / N), f x‖ ≤
      ε * ((M : ℝ) / N) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let q : ℕ → ℝ := fun k => (k : ℝ) / N
  have hq (k : ℕ) (hk : k ≤ M) : q k ∈ Icc (0 : ℝ) R := by
    constructor
    · exact div_nonneg (Nat.cast_nonneg k) hNr.le
    · exact (div_le_div_of_nonneg_right (by exact_mod_cast hk) hNr.le).trans hMN
  have hstep (k : ℕ) : q (k + 1) - q k = (N : ℝ)⁻¹ := by
    dsimp only [q]
    push_cast
    field_simp [hNr.ne']
    ring
  have htel : (∑ k ∈ Finset.range M,
      ∫ x in q k..q (k + 1), f x) = ∫ x in (0 : ℝ)..((M : ℝ) / N), f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (n := M) (f := f) (μ := volume) (a := q)
      (fun k (_hk : k < M) => hf.intervalIntegrable _ _)
    simpa only [q, Nat.cast_zero, zero_div] using h
  have hid : collisionEntranceScaledPrefixSum f N M - ∫ x in (0 : ℝ)..((M : ℝ) / N), f x =
      ∑ k ∈ Finset.range M,
        ∫ x in q k..q (k + 1), f (q (k + 1)) - f x := by
    rw [collisionEntranceScaledPrefixSum, Finset.mul_sum, ← htel, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),
      intervalIntegral.integral_const, hstep, smul_eq_mul]
  have hcell (k : ℕ) (hk : k ∈ Finset.range M) :
      ‖∫ x in q k..q (k + 1), f (q (k + 1)) - f x‖ ≤ ε * (N : ℝ)⁻¹ := by
    have hkM : k + 1 ≤ M := by have := Finset.mem_range.mp hk; omega
    have hright := hq (k + 1) hkM
    have hleft := hq k (by omega)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := q k) (b := q (k + 1)) (C := ε)
      (f := fun x => f (q (k + 1)) - f x) (fun x hx => ?_)
    · rw [hstep, abs_of_pos (inv_pos.mpr hNr)] at h
      exact h
    · rw [uIoc_of_le (div_le_div_of_nonneg_right (by exact_mod_cast (Nat.le_succ k)) hNr.le)] at hx
      have hxy : |q (k + 1) - x| ≤ (N : ℝ)⁻¹ := by
        rw [abs_of_nonneg (sub_nonneg.mpr hx.2)]
        calc
          q (k + 1) - x ≤ q (k + 1) - q k := by linarith [hx.1]
          _ = (N : ℝ)⁻¹ := hstep k
      have := hmod (q (k + 1)) hright x ⟨hleft.1.trans hx.1.le, hx.2.trans hright.2⟩ hxy
      have hnorm : ‖f (q (k + 1)) - f x‖ ≤ ε := by
        simpa only [Real.norm_eq_abs] using this
      exact hnorm
  rw [hid]
  calc
    _ ≤ ∑ k ∈ Finset.range M,
        ‖∫ x in q k..q (k + 1), f (q (k + 1)) - f x‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range M, ε * (N : ℝ)⁻¹ := Finset.sum_le_sum hcell
    _ = ε * ((M : ℝ) / N) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hNr.ne']

/-- Moving-endpoint mesh sums of a continuous function converge to the integral
from zero to the limiting endpoint. -/
theorem tendsto_collisionEntranceScaledPrefixSum (f : ℝ → ℝ) (hf : Continuous f)
    {M : ℕ → ℕ} {T : ℝ} (hT : 0 < T)
    (hM : Tendsto (fun N : ℕ => (M N : ℝ) / N) atTop (𝓝 T)) :
    Tendsto (fun N : ℕ => collisionEntranceScaledPrefixSum f N (M N)) atTop
      (𝓝 (∫ x in (0 : ℝ)..T, f x)) := by
  let prim : ℝ → ℝ := fun x => ∫ u in (0 : ℝ)..x, f u
  have hprim : Continuous prim :=
    intervalIntegral.continuous_primitive (fun a b => hf.intervalIntegrable a b) 0
  have hprimLimit : Tendsto (fun N : ℕ => prim ((M N : ℝ) / N)) atTop
      (𝓝 (∫ x in (0 : ℝ)..T, f x)) := by
    convert hprim.continuousAt.tendsto.comp hM using 1
    rfl
  have hmesh : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let R : ℝ := T + 1
  let η : ℝ := ε / (4 * R)
  have hR : 0 < R := by dsimp [R]; linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hUC : UniformContinuousOn f (Icc (0 : ℝ) R) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC (η / 2)
    (half_pos hη)
  have hmeshEvent : ∀ᶠ N : ℕ in atTop, (N : ℝ)⁻¹ < δ := hmesh.eventually_lt_const hδ
  have hratioEvent : ∀ᶠ N : ℕ in atTop, (M N : ℝ) / N < R :=
    hM.eventually (eventually_lt_nhds (by dsimp [R]; linarith))
  have hposEvent : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hmeshEvent.and hratioEvent).and hposEvent)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp
    (hprimLimit.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
  refine ⟨max N₀ N₁, fun N hN => ?_⟩
  have hgood := hN₀ N (by omega)
  have hmeshN : (N : ℝ)⁻¹ < δ := hgood.1.1
  have hratioN : (M N : ℝ) / N < R := hgood.1.2
  have hNpos : 0 < N := hgood.2
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hratioNonneg : 0 ≤ (M N : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNr.le
  have hmod' : ∀ x ∈ Icc (0 : ℝ) R, ∀ y ∈ Icc (0 : ℝ) R,
      |x - y| ≤ (N : ℝ)⁻¹ → |f x - f y| ≤ η := by
    intro x hx y hy hxy
    have hdist : dist x y < δ := by
      simpa only [Real.dist_eq] using hxy.trans_lt hmeshN
    have hcont := hmod x hx y hy hdist
    have habs : |f x - f y| < η / 2 := by simpa only [Real.dist_eq] using hcont
    have hnorm : ‖f x - f y‖ < η / 2 := by simpa only [Real.norm_eq_abs] using habs
    linarith
  have happrox := norm_collisionEntranceScaledPrefixSum_sub_variableIntegral f hf hNpos hR.le
    hratioN.le (by positivity) hmod'
  have happrox' : dist (collisionEntranceScaledPrefixSum f N (M N)) (prim ((M N : ℝ) / N)) ≤ ε / 4 := by
    rw [dist_eq_norm]
    change ‖collisionEntranceScaledPrefixSum f N (M N) -
      ∫ x in (0 : ℝ)..((M N : ℝ) / N), f x‖ ≤ ε / 4
    calc
      _ ≤ η * ((M N : ℝ) / N) := happrox
      _ ≤ η * R := mul_le_mul_of_nonneg_left hratioN.le hη.le
      _ = ε / 4 := by dsimp [η, R]; field_simp
  have hendpoint := hN₁ N (le_trans (le_max_right _ _) hN)
  have hendpoint' : dist (prim ((M N : ℝ) / N)) (∫ x in (0 : ℝ)..T, f x) < ε / 2 := by
    simpa only [Metric.mem_ball, dist_comm] using hendpoint
  calc
    dist (collisionEntranceScaledPrefixSum f N (M N)) (∫ x in (0 : ℝ)..T, f x) ≤
        dist (collisionEntranceScaledPrefixSum f N (M N)) (prim ((M N : ℝ) / N)) +
          dist (prim ((M N : ℝ) / N)) (∫ x in (0 : ℝ)..T, f x) := dist_triangle _ _ _
    _ ≤ ε / 4 + dist (prim ((M N : ℝ) / N)) (∫ x in (0 : ℝ)..T, f x) :=
      add_le_add_left happrox' _
    _ < ε := by linarith

/-- A moving right-endpoint sum over a positive-time interval converges when
both rounded endpoints converge after division by the mesh scale. -/
theorem tendsto_collisionEntranceScaledIntervalSum (f : ℝ → ℝ) (hf : Continuous f)
    {M₀ M₁ : ℕ → ℕ} {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (hMmono : ∀ N, M₀ N ≤ M₁ N)
    (hM₀ : Tendsto (fun N : ℕ => (M₀ N : ℝ) / N) atTop (𝓝 s))
    (hM₁ : Tendsto (fun N : ℕ => (M₁ N : ℝ) / N) atTop (𝓝 t)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N), f ((r : ℝ) / N)) atTop
      (𝓝 (∫ u in s..t, f u)) := by
  have hprefix₀ := tendsto_collisionEntranceScaledPrefixSum f hf hs hM₀
  have hprefix₁ := tendsto_collisionEntranceScaledPrefixSum f hf (lt_trans hs hst) hM₁
  have hinterval : ∀ N : ℕ,
      (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N), f ((r : ℝ) / N) =
        collisionEntranceScaledPrefixSum f N (M₁ N) -
          collisionEntranceScaledPrefixSum f N (M₀ N) := by
    intro N
    rw [collisionEntranceScaledPrefixSum_eq_Icc, collisionEntranceScaledPrefixSum_eq_Icc]
    rw [sum_Icc_interval_as_sub _ (hMmono N)]
    ring
  have hseg : (∫ u in (0 : ℝ)..t, f u) - ∫ u in (0 : ℝ)..s, f u =
      ∫ u in s..t, f u :=
    intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hlimit := hprefix₁.sub hprefix₀
  have hlimit' : Tendsto (fun N : ℕ =>
      collisionEntranceScaledPrefixSum f N (M₁ N) -
        collisionEntranceScaledPrefixSum f N (M₀ N)) atTop
      (𝓝 (∫ u in s..t, f u)) := by
    simpa only [hseg] using hlimit
  apply hlimit'.congr'
  filter_upwards with N
  exact (hinterval N).symm


end Critical2DKPZ.SHF.Moments

end
