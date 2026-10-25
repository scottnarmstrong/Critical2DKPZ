/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.SHF.Moments.WalkScaling
public import Critical2DKPZ.SHF.Moments.TimeRounding
import Critical2DKPZ.SHF.Moments.EntranceScaling
import Critical2DKPZ.JointConvergence.HeatKernelTranslation
import Critical2DKPZ.Collision.SpatialRenewal
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Heat-kernel approximation of lattice cell masses -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.JointConvergence

/-- The piecewise constant density associated with the walk kernel on the lattice cells. -/
def scaledWalkCellDensity (N n : ℕ) (x : Plane) : ℝ :=
  (N : ℝ) / 4 * srwKernel n (latticePoint N x)

/-- At every fixed point, the scaled density of the even-ceiling walk kernel converges to the
continuum heat kernel. The scaled local CLT is applied at the sampled lattice point, and the
nearest-cell representative converges to the original point. -/
theorem tendsto_heatKernel_cellDensity {δ : ℝ} (hδ : 0 < δ) (x : Plane) :
    Tendsto (fun N : ℕ => (N : ℝ) / 4 *
      srwKernel (evenCeil ((N : ℝ) * δ)) (latticePoint N x)) atTop (𝓝 (heatKernel δ x)) := by
  let n : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * δ)
  obtain ⟨C, hC, hclt⟩ := SHF.Moments.srwKernel_scaled_localCLT
  have htime : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 δ) := by
    simpa only [n] using SHF.Moments.tendsto_evenCeil_div δ hδ.le
  have hspace : Tendsto (fun N : ℕ => cellSample N x) atTop (𝓝 x) :=
    tendsto_cellSample x
  have hpair : Tendsto (fun N : ℕ => ((n N : ℝ) / N, cellSample N x)) atTop
      (𝓝 (δ, x)) := by
    simpa only [nhds_prod_eq] using htime.prodMk hspace
  have hcont : ContinuousAt (fun p : ℝ × Plane => heatKernel p.1 p.2) (δ, x) := by
    unfold heatKernel
    fun_prop (disch := positivity)
  have hheat : Tendsto (fun N : ℕ => heatKernel ((n N : ℝ) / N) (cellSample N x))
      atTop (𝓝 (heatKernel δ x)) := hcont.tendsto.comp hpair
  have herrorBound : Tendsto (fun N : ℕ => C * (N : ℝ) / (n N : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hsmall : Tendsto (fun N : ℕ => (C / δ ^ 2) / (N : ℝ)) atTop (𝓝 0) :=
      SHF.Moments.tendsto_const_div_nat (C / δ ^ 2)
    apply squeeze_zero' ?_ ?_ hsmall
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hn : 0 < (n N : ℝ) := by
        have hceil : (N : ℝ) * δ ≤ (n N : ℝ) := by
          dsimp [n]
          exact Critical2DKPZ.le_evenCeil _
        exact lt_of_lt_of_le (mul_pos hNr hδ) hceil
      positivity
    · filter_upwards [eventually_gt_atTop 0] with N hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hn : (N : ℝ) * δ ≤ (n N : ℝ) := by
        dsimp [n]
        exact Critical2DKPZ.le_evenCeil _
      have hbase : C * (N : ℝ) / (n N : ℝ) ^ 2 ≤
          C * (N : ℝ) / ((N : ℝ) * δ) ^ 2 := by
        apply div_le_div_of_nonneg_left (mul_nonneg hC.le hNr.le)
          (sq_pos_of_pos (mul_pos hNr hδ))
        exact pow_le_pow_left₀ (mul_nonneg hNr.le hδ.le) hn 2
      have heq : C * (N : ℝ) / ((N : ℝ) * δ) ^ 2 =
          (C / δ ^ 2) / (N : ℝ) := by
        field_simp [hNr.ne', hδ.ne']
      exact hbase.trans_eq heq
  have herror : Tendsto (fun N : ℕ =>
      (N : ℝ) / 4 * srwKernel (n N) (latticePoint N x) -
        heatKernel ((n N : ℝ) / N) (cellSample N x)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [herrorBound.eventually (gt_mem_nhds hε), eventually_gt_atTop 0,
      eventually_ge_atTop (Nat.ceil (1 / δ))] with N herr hN hNlarge
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hn1 : 1 ≤ n N := by
      have hthreshold : 1 / δ ≤ (N : ℝ) := by
        calc
          1 / δ ≤ (Nat.ceil (1 / δ) : ℝ) := Nat.le_ceil _
          _ ≤ (N : ℝ) := by exact_mod_cast hNlarge
      have hnδ : 1 ≤ (n N : ℝ) := by
        have hn := Critical2DKPZ.le_evenCeil ((N : ℝ) * δ)
        have hNδ : 1 ≤ (N : ℝ) * δ := (div_le_iff₀ hδ).mp hthreshold
        dsimp [n] at hn ⊢
        exact hNδ.trans hn
      exact_mod_cast hnδ
    have hnEvenNat : Even (n N) := by
      dsimp [n]
      exact SHF.Moments.even_evenCeil ((N : ℝ) * δ)
    have hnEven : Even ((n N : ℤ)) := (Int.even_coe_nat (n N)).2 hnEvenNat
    have hzEven : Even ((latticePoint N x) 0 + (latticePoint N x) 1) :=
      latticePoint_mem_evenLattice N x
    have hphase : Even ((latticePoint N x) 0 + (latticePoint N x) 1 + (n N : ℤ)) :=
      Even.add hzEven hnEven
    have hcltN := hclt N (n N) hN hn1 (latticePoint N x) hphase
    have hpoint : |(N : ℝ) / 4 * srwKernel (n N) (latticePoint N x) -
        heatKernel ((n N : ℝ) / N) (latticeRepresentative N (latticePoint N x))| ≤
        C * (N : ℝ) / (n N : ℝ) ^ 2 := hcltN
    have hrep : latticeRepresentative N (latticePoint N x) = cellSample N x := rfl
    rw [hrep] at hpoint
    have herrAbs : |(N : ℝ) / 4 * srwKernel (n N) (latticePoint N x) -
        heatKernel ((n N : ℝ) / N) (cellSample N x)| < ε := hpoint.trans_lt herr
    simpa only [Real.dist_eq, sub_zero] using herrAbs
  have hsum := herror.add hheat
  have heq (N : ℕ) :
      (N : ℝ) / 4 * srwKernel (n N) (latticePoint N x) =
        ((N : ℝ) / 4 * srwKernel (n N) (latticePoint N x) -
          heatKernel ((n N : ℝ) / N) (cellSample N x)) +
        heatKernel ((n N : ℝ) / N) (cellSample N x) := by ring
  have hfun : (fun N : ℕ => (N : ℝ) / 4 * srwKernel (n N) (latticePoint N x)) =
      fun N : ℕ => ((N : ℝ) / 4 * srwKernel (n N) (latticePoint N x) -
        heatKernel ((n N : ℝ) / N) (cellSample N x)) +
          heatKernel ((n N : ℝ) / N) (cellSample N x) := by
    funext N
    exact heq N
  rw [hfun]
  simpa only [zero_add] using hsum

/-- The scaled walk density has an integrable Gaussian majorant for all sufficiently large
lattice scales. The Gaussian walk bound is expressed in lattice coordinates; the cell sampling
estimate transfers it to continuum coordinates. -/
private theorem eventually_scaledWalkCellDensity_le_heatKernel
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ u B : ℝ, 0 < u ∧ 0 ≤ B ∧ ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
      0 ≤ scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x ∧
        scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x ≤
          B * heatKernel u x := by
  obtain ⟨A, c, hc, hwalk⟩ := Critical2DKPZ.srwKernel_gaussianBound
  have hA : 0 ≤ A := by
    by_contra hA
    have hA' : A < 0 := lt_of_not_ge hA
    have hker := Critical2DKPZ.srwKernel_nonneg 1 (0 : Site)
    have hbound := hwalk 1 (by omega) (0 : Site)
    have hexp : 0 < Real.exp (-c * ‖siteToPlane (0 : Site)‖ ^ 2 / 1) := Real.exp_pos _
    have hneg : A / 1 * Real.exp (-c * ‖siteToPlane (0 : Site)‖ ^ 2 / 1) < 0 :=
      mul_neg_of_neg_of_pos (by simpa using hA') hexp
    linarith
  let a₀ : ℝ := c / (2 * (δ + 1))
  let u : ℝ := a₀⁻¹
  let K : ℝ := A / (4 * δ) * Real.exp (4 * a₀)
  let B : ℝ := K * (2 * Real.pi * u)
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨u, B, hu, hB, ?_⟩
  let N₀ : ℕ := Nat.ceil (max (2 / δ) 2)
  filter_upwards [eventually_ge_atTop N₀] with N hNN₀
  have hNbound : max (2 / δ) 2 ≤ (N : ℝ) := by
    calc
      _ ≤ (N₀ : ℝ) := Nat.le_ceil _
      _ ≤ (N : ℝ) := by exact_mod_cast hNN₀
  have hNδ : 2 ≤ (N : ℝ) * δ := by
    have h := le_max_left (2 / δ) 2
    exact (div_le_iff₀ hδ).mp (h.trans hNbound)
  have hNtwo : 2 ≤ (N : ℝ) := (le_max_right (2 / δ) 2).trans hNbound
  have hNpos : 0 < N := by
    have hNposR : (0 : ℝ) < N := lt_of_lt_of_le (by norm_num) hNtwo
    exact_mod_cast hNposR
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hnLower : (N : ℝ) * δ ≤ (evenCeil ((N : ℝ) * δ) : ℝ) :=
    Critical2DKPZ.le_evenCeil _
  have hnUpper : (evenCeil ((N : ℝ) * δ) : ℝ) ≤ (N : ℝ) * δ + 2 :=
    (Critical2DKPZ.evenCeil_lt_add_two (mul_nonneg hNr.le hδ.le)).le
  have hnPos : 0 < (evenCeil ((N : ℝ) * δ) : ℝ) :=
    lt_of_lt_of_le (mul_pos hNr hδ) hnLower
  have hratioLo : δ ≤ (evenCeil ((N : ℝ) * δ) : ℝ) / N := by
    rw [le_div_iff₀ hNr]
    nlinarith [hnLower]
  have hratioHi : (evenCeil ((N : ℝ) * δ) : ℝ) / N ≤ δ + 1 := by
    rw [div_le_iff₀ hNr]
    have h2div : (2 : ℝ) / N ≤ 1 := (div_le_iff₀ hNr).2 (by nlinarith [hNtwo])
    nlinarith [hnUpper]
  have hsampleDist (x : Plane) :
      ‖x - cellSample N x‖ ≤ 2 := by
    have h := dist_cellSample_le_two hNpos x
    simpa only [dist_comm, dist_eq_norm] using h
  intro x
  let n : ℕ := evenCeil ((N : ℝ) * δ)
  let r : ℝ := (n : ℝ) / N
  let y : Site := latticePoint N x
  have hn1 : 1 ≤ n := by
    have hnc : 1 ≤ (n : ℝ) := by dsimp [n]; linarith [hNδ, hnLower]
    exact_mod_cast hnc
  have hrlo : δ ≤ r := by dsimp [r, n]; exact hratioLo
  have hrhi : r ≤ δ + 1 := by dsimp [r, n]; exact hratioHi
  have hrpos : 0 < r := lt_of_lt_of_le hδ hrlo
  have hwalkx := hwalk n hn1 y
  have hscale : ‖siteToPlane y‖ ^ 2 = (N : ℝ) / 2 * ‖cellSample N x‖ ^ 2 := by
    have hrep : ‖cellSample N x‖ ^ 2 = (2 / (N : ℝ)) * ‖siteToPlane y‖ ^ 2 := by
      simpa only [y, cellSample] using SHF.Moments.norm_latticeRepresentative_sq N
        (latticePoint N x)
    rw [hrep]
    field_simp [hNr.ne']
  have hexpEq : -c * ‖siteToPlane y‖ ^ 2 / (n : ℝ) =
      -(c / (2 * r)) * ‖cellSample N x‖ ^ 2 := by
    rw [hscale]
    dsimp [r, n]
    field_simp [hNr.ne', hnPos.ne']
  have hcoef : a₀ ≤ c / (2 * r) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) (by linarith [hrhi]))
      (mul_pos (by norm_num) hrpos)).2
    change c * (2 * r) ≤ c * (2 * (δ + 1))
    nlinarith [hrhi, hc]
  have hnormx : ‖x‖ ≤ ‖cellSample N x‖ + 2 := by
    calc
      ‖x‖ ≤ ‖x - cellSample N x‖ + ‖cellSample N x‖ := norm_le_norm_sub_add _ _
      _ ≤ ‖cellSample N x‖ + 2 := by linarith [hsampleDist x]
  have hnormSq : ‖x‖ ^ 2 ≤ 2 * ‖cellSample N x‖ ^ 2 + 8 := by
    nlinarith [sq_nonneg (‖cellSample N x‖ - 2), norm_nonneg x,
      norm_nonneg (cellSample N x)]
  have harg : -(c / (2 * r)) * ‖cellSample N x‖ ^ 2 ≤
      4 * a₀ - a₀ / 2 * ‖x‖ ^ 2 := by
    have hcoef' := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖cellSample N x‖)
    nlinarith [hnormSq, ha₀]
  have hexpBound : Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (n : ℝ)) ≤
      Real.exp (4 * a₀) * Real.exp (-a₀ / 2 * ‖x‖ ^ 2) := by
    rw [hexpEq]
    calc
      _ ≤ Real.exp (4 * a₀ - a₀ / 2 * ‖x‖ ^ 2) := Real.exp_le_exp.mpr harg
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hcoeff : (N : ℝ) / 4 * (A / (n : ℝ)) ≤ A / (4 * δ) := by
    have hnr : 0 < (n : ℝ) := hnPos
    have heq : (N : ℝ) / 4 * (A / (n : ℝ)) = A / (4 * r) := by
      dsimp [r]
      field_simp [hNr.ne', hnr.ne']
    rw [heq]
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hrpos)
      (mul_pos (by norm_num) hδ)).2
    change A * (4 * δ) ≤ A * (4 * r)
    have hmul := mul_le_mul_of_nonneg_left hrlo (mul_nonneg hA (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith [hmul]
  have hraw : scaledWalkCellDensity N n x ≤
      K * Real.exp (-a₀ / 2 * ‖x‖ ^ 2) := by
    have hwalk' : srwKernel n y ≤ A / (n : ℝ) *
        Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (n : ℝ)) := hwalkx
    have hnonneg : 0 ≤ (N : ℝ) / 4 := by positivity
    calc
      scaledWalkCellDensity N n x ≤ (N : ℝ) / 4 *
          (A / (n : ℝ) * Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (n : ℝ))) := by
        dsimp [scaledWalkCellDensity, y]
        exact mul_le_mul_of_nonneg_left hwalk' hnonneg
      _ = ((N : ℝ) / 4 * (A / (n : ℝ))) *
          Real.exp (-c * ‖siteToPlane y‖ ^ 2 / (n : ℝ)) := by ring
      _ ≤ (A / (4 * δ)) *
          (Real.exp (4 * a₀) * Real.exp (-a₀ / 2 * ‖x‖ ^ 2)) :=
        mul_le_mul hcoeff hexpBound (Real.exp_nonneg _) (by positivity)
      _ = (A / (4 * δ)) * Real.exp (4 * a₀) *
          Real.exp (-a₀ / 2 * ‖x‖ ^ 2) := by ring
      _ = K * Real.exp (-a₀ / 2 * ‖x‖ ^ 2) := by rfl
  have hkernelId (z : Plane) :
      (2 * Real.pi * u) * heatKernel u z = Real.exp (-a₀ / 2 * ‖z‖ ^ 2) := by
    rw [heatKernel]
    have hcoefPos : 0 < 2 * Real.pi * u := by positivity
    calc
      _ = ((2 * Real.pi * u) * (2 * Real.pi * u)⁻¹) *
          Real.exp (-‖z‖ ^ 2 / (2 * u)) := by ring
      _ = Real.exp (-‖z‖ ^ 2 / (2 * u)) := by
        rw [mul_inv_cancel₀ (ne_of_gt hcoefPos), one_mul]
      _ = Real.exp (-a₀ / 2 * ‖z‖ ^ 2) := by
        congr 1
        dsimp [u]
        field_simp [ha₀.ne']
  have hbound : scaledWalkCellDensity N n x ≤ B * heatKernel u x := by
    calc
      _ ≤ K * Real.exp (-a₀ / 2 * ‖x‖ ^ 2) := hraw
      _ = K * ((2 * Real.pi * u) * heatKernel u x) := by rw [← hkernelId x]
      _ = B * heatKernel u x := by dsimp [B]; ring
  have hnonneg : 0 ≤ scaledWalkCellDensity N n x := by
    dsimp [scaledWalkCellDensity, y, n]
    exact mul_nonneg (by positivity) (Critical2DKPZ.srwKernel_nonneg _ _)
  exact ⟨hnonneg, hbound⟩

/-- The centered scaled walk density converges to the heat kernel in `L¹`. The preceding uniform
Gaussian majorant supplies the domination needed to pass from pointwise local-CLT convergence to
integral convergence. -/
theorem tendsto_integral_abs_scaledWalkCellDensity {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => ∫ x : Plane,
      |scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x - heatKernel δ x|)
      atTop (𝓝 0) ∧ ∀ᶠ N : ℕ in atTop, Integrable (fun x : Plane =>
        |scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x - heatKernel δ x|) := by
  obtain ⟨u, B, hu, hB, hdom⟩ := eventually_scaledWalkCellDensity_le_heatKernel hδ
  let G : Plane → ℝ := fun x => B * heatKernel u x + heatKernel δ x
  have hG : Integrable G := by
    dsimp [G]
    exact ((Critical2DKPZ.integrable_heatKernel hu).const_mul B).add
      (Critical2DKPZ.integrable_heatKernel hδ)
  have hmeas (N : ℕ) : Measurable (fun x : Plane =>
      |scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x - heatKernel δ x|) := by
    apply Measurable.abs
    apply Measurable.sub
    ·
      exact measurable_const.mul
        ((measurable_of_countable fun y : Site =>
          srwKernel (evenCeil ((N : ℝ) * δ)) y).comp (measurable_latticePoint N))
    · exact (Critical2DKPZ.continuous_heatKernel δ).measurable
  have hpoint (x : Plane) : Tendsto (fun N : ℕ =>
      |scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x - heatKernel δ x|)
      atTop (𝓝 0) := by
    have h := tendsto_heatKernel_cellDensity hδ x
    have hsub : Tendsto (fun N : ℕ =>
        scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x - heatKernel δ x)
        atTop (𝓝 0) := by
      simpa only [scaledWalkCellDensity, sub_self] using h.sub_const (heatKernel δ x)
    simpa only [abs_zero] using hsub.abs
  have hboundAbs (N : ℕ) (hN : ∀ x : Plane,
      0 ≤ scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x ∧
        scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x ≤ B * heatKernel u x)
      (x : Plane) :
      |scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x - heatKernel δ x| ≤ G x := by
    have hf := hN x
    have hfNonneg : 0 ≤ scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x := hf.1
    have hgNonneg : 0 ≤ heatKernel δ x := Critical2DKPZ.heatKernel_nonneg hδ.le x
    have hfLe : scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x ≤ B * heatKernel u x := hf.2
    rw [abs_le]
    constructor <;> dsimp [G] <;> linarith
  have hint : ∀ᶠ N : ℕ in atTop, Integrable (fun x : Plane =>
      |scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x - heatKernel δ x|) := by
    filter_upwards [hdom] with N hN
    apply hG.mono' (hmeas N).aestronglyMeasurable
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_abs] using hboundAbs N hN x
  have hDCT : Tendsto (fun N : ℕ => ∫ x : Plane,
      |scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) x - heatKernel δ x|)
      atTop (𝓝 (∫ x : Plane, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence G
    · exact Filter.Eventually.of_forall fun N => (hmeas N).aestronglyMeasurable
    · filter_upwards [hdom] with N hN
      exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_abs] using hboundAbs N hN x
    · exact hG
    · exact Filter.Eventually.of_forall hpoint
  exact ⟨by simpa using hDCT, hint⟩

/-- Nearest-even rounding commutes with translations by the even lattice. -/
private theorem nearestEven_sub_siteToPlane_of_even {v : Site} (hv : v ∈ evenLattice)
    (u : Plane) :
    nearestEven (u - siteToPlane v) = nearestEven u - v := by
  obtain ⟨c, hc⟩ := hv
  let d : ℤ := v 0 - c
  have hv0 : v 0 = c + d := by dsimp [d]; omega
  have hv1 : v 1 = c - d := by dsimp [d]; omega
  let a : ℤ := round ((u 0 + u 1) / 2) - c
  let b : ℤ := round ((u 0 - u 1) / 2) - d
  have hdiag0 :
      ((u - siteToPlane v) 0 + (u - siteToPlane v) 1) / 2 =
        (u 0 + u 1) / 2 - (c : ℝ) := by
    simp [siteToPlane, hv0, hv1]
    ring
  have hdiag1 :
      ((u - siteToPlane v) 0 - (u - siteToPlane v) 1) / 2 =
        (u 0 - u 1) / 2 - (d : ℝ) := by
    simp [siteToPlane, hv0, hv1]
    ring
  have hrounded : nearestEven (u - siteToPlane v) = ![a + b, a - b] := by
    apply (nearestEven_eq_iff (u - siteToPlane v) a b).2
    constructor
    · rw [hdiag0, round_sub_intCast]
    · rw [hdiag1, round_sub_intCast]
  have htranslated : nearestEven u - v = ![a + b, a - b] := by
    ext i
    fin_cases i <;> simp [nearestEven, a, b, hv0, hv1] <;> ring
  exact hrounded.trans htranslated.symm

/-- Sampling commutes with translating the continuum point by a sampled even-lattice site. -/
private theorem latticePoint_sub_cellSample {N : ℕ} (hN : 0 < N) (x z : Plane) :
    latticePoint N (z - cellSample N x) = latticePoint N z - latticePoint N x := by
  have hsqrt : 0 < Real.sqrt ((N : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hscale : Real.sqrt ((N : ℝ) / 2) • cellSample N x =
      siteToPlane (latticePoint N x) := by
    rw [cellSample, latticeRepresentative, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hsqrt), one_smul]
  change nearestEven (Real.sqrt ((N : ℝ) / 2) • (z - cellSample N x)) =
    nearestEven (Real.sqrt ((N : ℝ) / 2) • z) - latticePoint N x
  rw [smul_sub, hscale]
  exact nearestEven_sub_siteToPlane_of_even (latticePoint_mem_evenLattice N x) _

/-- Comparing the mass of every lattice cell with the corresponding heat-kernel mass is bounded
by the continuum `L¹` error of their piecewise-constant densities. -/
private theorem tsum_abs_walkCellMass_sub_heatCellMass_le
    {δ : ℝ} {N n : ℕ} (hN : 0 < N) (hn : Even n) (x : Plane)
    (hwalk : Integrable (fun z : Plane =>
      scaledWalkCellDensity N n (z - cellSample N x)))
    (hheat : Integrable (fun z : Plane => heatKernel δ (z - x)))
    (herror : Integrable (fun z : Plane =>
      |scaledWalkCellDensity N n (z - cellSample N x) - heatKernel δ (z - x)|)) :
    ∑' y : Site, |srwKernel n (y - latticePoint N x) -
        ∫ z in cell N y, heatKernel δ (z - x)| ≤
      ∫ z : Plane,
        |scaledWalkCellDensity N n (z - cellSample N x) - heatKernel δ (z - x)| := by
  let f : Plane → ℝ := fun z => scaledWalkCellDensity N n (z - cellSample N x)
  let g : Plane → ℝ := fun z => heatKernel δ (z - x)
  let F : Plane → ℝ := fun z => |f z - g z|
  have hcover : (⋃ y : Site, cell N y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact Set.mem_iUnion.mpr ⟨latticePoint N z, mem_cell_latticePoint N z⟩
  have hsum : HasSum (fun y : Site => ∫ z in cell N y, F z) (∫ z : Plane, F z) := by
    have hi := hasSum_integral_iUnion (fun y => measurableSet_cell N y)
      (pairwise_disjoint_cell N) herror.integrableOn
    simpa only [hcover, setIntegral_univ] using hi
  have hkernelCell (y : Site) : ∫ z in cell N y, f z = srwKernel n (y - latticePoint N x) := by
    by_cases hy : y ∈ evenLattice
    · have hconst (z : Plane) (hz : z ∈ cell N y) :
          f z = (N : ℝ) / 4 * srwKernel n (y - latticePoint N x) := by
        dsimp [f, scaledWalkCellDensity]
        rw [latticePoint_sub_cellSample hN x z, (mem_cell_iff N y z).mp hz]
      rw [setIntegral_congr_fun (measurableSet_cell N y) hconst, setIntegral_const,
        measureReal_def, volume_cell_toReal hN hy]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      rw [smul_eq_mul]
      field_simp [hNr.ne']
    · have hyodd : ¬ Even (y 0 + y 1) := hy
      have hxEven : Even ((latticePoint N x) 0 + (latticePoint N x) 1) :=
        latticePoint_mem_evenLattice N x
      have hnEven : Even ((n : ℤ)) := (Int.even_coe_nat n).2 hn
      have hphase : ¬ Even ((n : ℤ) + (y - latticePoint N x) 0 +
          (y - latticePoint N x) 1) := by
        intro hphase
        apply hyodd
        have hphaseMod := Int.even_iff.mp hphase
        have hnMod := Int.even_iff.mp hnEven
        have hxMod := Int.even_iff.mp hxEven
        have hyNotMod : (y 0 + y 1) % 2 ≠ 0 := by
          intro hmod
          exact hyodd (Int.even_iff.mpr hmod)
        simp only [Pi.sub_apply] at hphaseMod
        omega
      simp [cell_eq_empty_of_not_even hy,
        Collision.srwKernel_eq_zero_of_not_hatGaussianParity hphase]
  have hcell (y : Site) :
      |srwKernel n (y - latticePoint N x) - ∫ z in cell N y, g z| ≤
        ∫ z in cell N y, F z := by
    have hwalkSet : Integrable (fun z : Plane => f z) (volume.restrict (cell N y)) :=
      hwalk.restrict
    have hheatSet : Integrable (fun z : Plane => g z) (volume.restrict (cell N y)) :=
      hheat.restrict
    have hdiff : ∫ z in cell N y, (f z - g z) =
        (∫ z in cell N y, f z) - ∫ z in cell N y, g z := by
      exact integral_sub hwalkSet hheatSet
    rw [← hkernelCell y, ← hdiff]
    exact abs_integral_le_integral_abs
  have hcellNonneg (y : Site) : 0 ≤ ∫ z in cell N y, F z :=
    setIntegral_nonneg (measurableSet_cell N y) (fun z _ => abs_nonneg _)
  have hsumErr : Summable (fun y : Site =>
      |srwKernel n (y - latticePoint N x) - ∫ z in cell N y, g z|) :=
    hsum.summable.of_nonneg_of_le (fun y => abs_nonneg _) hcell
  calc
    _ ≤ ∑' y : Site, ∫ z in cell N y, F z :=
      hsumErr.tsum_le_tsum hcell hsum.summable
    _ = ∫ z : Plane, F z := hsum.tsum_eq

/-- The walk kernel is `ℓ¹`-close to the heat-kernel masses of the lattice cells, uniformly in the
center. The centered density limit, translation continuity of the heat kernel, and exact cell
partition reduce the assertion to the `L¹` convergence above. -/
theorem srwKernel_sub_cellHeat_l1_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
      ∑' y : Site, |srwKernel (evenCeil ((N : ℝ) * δ)) (y - latticePoint N x) -
        ∫ z in cell N y, heatKernel δ (z - x)| ≤ ε := by
  obtain ⟨hcentral, hcentralInt⟩ := tendsto_integral_abs_scaledWalkCellDensity hδ
  obtain ⟨u, B, hu, hB, hmajor⟩ := eventually_scaledWalkCellDensity_le_heatKernel hδ
  let H : Plane → ℝ := fun z => B * heatKernel u z
  have hH : Integrable H := by
    dsimp [H]
    exact (Critical2DKPZ.integrable_heatKernel hu).const_mul B
  have hmeasDensity (N : ℕ) : Measurable (fun z : Plane =>
      scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) z) := by
    exact measurable_const.mul ((measurable_of_countable fun y : Site =>
      srwKernel (evenCeil ((N : ℝ) * δ)) y).comp (measurable_latticePoint N))
  have hdensityInt : ∀ᶠ N : ℕ in atTop, Integrable (fun z : Plane =>
      scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) z) := by
    filter_upwards [hmajor] with N hN
    apply hH.mono' (hmeasDensity N).aestronglyMeasurable
    filter_upwards with z
    have hz := hN z
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz.1, H] using hz.2
  obtain ⟨C, htrans⟩ := integral_abs_heatKernel_sub_le
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  let η : ℕ → ℝ := fun N => |C| * (Real.sqrt ((N : ℝ) / 2))⁻¹ / Real.sqrt δ
  have hη : Tendsto η atTop (𝓝 0) := by
    have hmesh := tendsto_lattice_mesh
    have hscaled : Tendsto (fun N : ℕ => |C| * (Real.sqrt ((N : ℝ) / 2))⁻¹)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds (x := |C|)).mul hmesh
    have hscaled' : Tendsto
        (fun N : ℕ => |C| * (Real.sqrt ((N : ℝ) / 2))⁻¹ / Real.sqrt δ)
        atTop (𝓝 0) := by
      simpa using hscaled.div_const (Real.sqrt δ)
    simpa only [η] using hscaled'
  have htotal : Tendsto (fun N : ℕ =>
      (∫ z : Plane, |scaledWalkCellDensity N (evenCeil ((N : ℝ) * δ)) z -
          heatKernel δ z|) + η N) atTop (𝓝 0) := by
    simpa only [zero_add] using hcentral.add hη
  intro ε hε
  filter_upwards [htotal.eventually (gt_mem_nhds hε), hcentralInt, hdensityInt,
    eventually_gt_atTop 0] with N htotalN hcentralN hdensityN hN
  intro x
  have hNpos : 0 < N := hN
  let n : ℕ := evenCeil ((N : ℝ) * δ)
  let x₀ : Plane := cellSample N x
  have hnEven : Even n := by
    dsimp [n]
    exact SHF.Moments.even_evenCeil ((N : ℝ) * δ)
  have hwalk : Integrable (fun z : Plane =>
      scaledWalkCellDensity N n (z - x₀)) := by
    simpa only [n, x₀] using hdensityN.comp_sub_right x₀
  have hheat : Integrable (fun z : Plane => heatKernel δ (z - x)) :=
    (Critical2DKPZ.integrable_heatKernel hδ).comp_sub_right x
  have herror : Integrable (fun z : Plane =>
      |scaledWalkCellDensity N n (z - x₀) - heatKernel δ (z - x)|) :=
    (hwalk.sub hheat).abs
  have hcellSum := tsum_abs_walkCellMass_sub_heatCellMass_le hNpos hnEven x hwalk hheat herror
  let f₁ : Plane → ℝ := fun z =>
    |scaledWalkCellDensity N n (z - x₀) - heatKernel δ (z - x₀)|
  let f₂ : Plane → ℝ := fun z => |heatKernel δ (z - x₀) - heatKernel δ (z - x)|
  have hf₁ : Integrable f₁ := by
    simpa only [f₁, n, x₀] using hcentralN.comp_sub_right x₀
  have hf₂ : Integrable f₂ := integrable_abs_heatKernel_sub hδ x₀ x
  have htranslation : ∫ z : Plane, f₁ z =
      ∫ z : Plane, |scaledWalkCellDensity N n z - heatKernel δ z| := by
    simpa only [f₁, n, x₀, sub_eq_add_neg] using
      (integral_add_right_eq_self
        (fun z : Plane =>
          |scaledWalkCellDensity N n z - heatKernel δ z|) (-x₀))
  have htriangle (z : Plane) :
      |scaledWalkCellDensity N n (z - x₀) - heatKernel δ (z - x)| ≤ f₁ z + f₂ z := by
    calc
      _ = |(scaledWalkCellDensity N n (z - x₀) - heatKernel δ (z - x₀)) +
          (heatKernel δ (z - x₀) - heatKernel δ (z - x))| := by congr 1; ring
      _ ≤ f₁ z + f₂ z := abs_add_le _ _
  have hintegralTriangle :
      (∫ z : Plane,
        |scaledWalkCellDensity N n (z - x₀) - heatKernel δ (z - x)|) ≤
          (∫ z : Plane, f₁ z) + ∫ z : Plane, f₂ z := by
    calc
      _ ≤ ∫ z : Plane, f₁ z + f₂ z :=
        integral_mono herror (hf₁.add hf₂) htriangle
      _ = _ := integral_add hf₁ hf₂
  have hmesh : ‖x₀ - x‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
    have h := dist_cellSample_le hNpos x
    simpa only [x₀, dist_eq_norm] using h
  have htransBound := htrans δ hδ x₀ x
  have hCmul : C * ‖x₀ - x‖ ≤ |C| * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
    by_cases hC : 0 ≤ C
    · rw [abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_left hmesh hC
    · have hCneg : C < 0 := lt_of_not_ge hC
      have hmeshNonneg : 0 ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ := by positivity
      have hcnonneg : 0 ≤ |C| * (Real.sqrt ((N : ℝ) / 2))⁻¹ :=
        mul_nonneg (abs_nonneg C) hmeshNonneg
      have hleftneg : C * ‖x₀ - x‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hCneg.le (norm_nonneg _)
      linarith
  have htransBound' : ∫ z : Plane, f₂ z ≤ η N := by
    calc
      _ ≤ C * ‖x₀ - x‖ / Real.sqrt δ := htransBound
      _ ≤ |C| * (Real.sqrt ((N : ℝ) / 2))⁻¹ / Real.sqrt δ := by
        exact div_le_div_of_nonneg_right hCmul hsqrt.le
      _ = η N := rfl
  calc
    _ ≤ ∫ z : Plane,
        |scaledWalkCellDensity N n (z - x₀) - heatKernel δ (z - x)| := hcellSum
    _ ≤ (∫ z : Plane, f₁ z) + ∫ z : Plane, f₂ z := hintegralTriangle
    _ ≤ (∫ z : Plane, |scaledWalkCellDensity N n z - heatKernel δ z|) + η N := by
      rw [htranslation]
      linarith [htransBound']
    _ ≤ ε := htotalN.le

end Critical2DKPZ.JointConvergence

end
