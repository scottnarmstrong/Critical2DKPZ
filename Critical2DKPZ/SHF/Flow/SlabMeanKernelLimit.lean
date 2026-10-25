/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.SlabMean
public import Critical2DKPZ.SHF.Moments.KernelLimit
public import Critical2DKPZ.SHF.Moments.FirstMoment
public import Critical2DKPZ.Analysis.Lattice.Sampling
import Critical2DKPZ.SHF.DeltaBose.KernelBlocks

/-! The annealed slab connector converges to the heat kernel. -/

@[expose] public section

open Filter
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Moments
open scoped Topology

namespace Critical2DKPZ.SHF.Flow


/-- The annealed slab connector converges uniformly to the heat kernel on compact endpoint sets. -/
theorem tendsto_slabMeanKernel_uniformOn_compact (ϑ : ℝ) {t : ℝ} (ht : 0 ≤ t)
    {v : ℝ} (hv : 0 < v) (K : Set (Plane × Plane)) (hK : IsCompact K) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      ∀ x y, (x, y) ∈ K →
        |slabMeanKernel ϑ N t (t + v) x y - heatKernel v (y - x)| < ε := by
  intro ε hε
  let Kx : Set Plane := Prod.fst '' K
  let Ky : Set Plane := Prod.snd '' K
  have hKx : IsCompact Kx := hK.image continuous_fst
  have hKy : IsCompact Ky := hK.image continuous_snd
  obtain ⟨Rx₀, hRx₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hKx.isBounded
  obtain ⟨Ry₀, hRy₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hKy.isBounded
  let Rx := max Rx₀ 0
  let Ry := max Ry₀ 0
  let R := Rx + Ry + 4
  have hRx : 0 ≤ Rx := le_max_right _ _
  have hRy : 0 ≤ Ry := le_max_right _ _
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hKxnorm {x : Plane} (hx : x ∈ Kx) : ‖x‖ ≤ Rx := by
    have hxball := hRx₀ hx
    have hxnorm : ‖x‖ ≤ Rx₀ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hxball
    exact hxnorm.trans (le_max_left _ _)
  have hKynorm {y : Plane} (hy : y ∈ Ky) : ‖y‖ ≤ Ry := by
    have hyball := hRy₀ hy
    have hynorm : ‖y‖ ≤ Ry₀ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hyball
    exact hynorm.trans (le_max_left _ _)
  let Kheat : Set (ℝ × Plane) := Set.Icc (v / 2) (2 * v) ×ˢ Metric.closedBall 0 R
  have hKheat : IsCompact Kheat := isCompact_Icc.prod (isCompact_closedBall 0 R)
  have hheatContinuous : ContinuousOn
      (fun p : ℝ × Plane => heatKernel p.1 p.2) Kheat := by
    exact Critical2DKPZ.DeltaBose.continuousOn_heatKernel.mono (by
      intro p hp
      exact lt_of_lt_of_le (by positivity) hp.1.1)
  have hheatUniform : UniformContinuousOn
      (fun p : ℝ × Plane => heatKernel p.1 p.2) Kheat :=
    hKheat.uniformContinuousOn_of_continuous hheatContinuous
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hheatUniform (ε / 2) (half_pos hε)
  let n : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * (t + v)) - evenCeil ((N : ℝ) * t)
  have htime : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (nhds v) := by
    simpa only [n, add_sub_cancel_left] using
      tendsto_evenCeil_gap_div (s := t) (t := t + v) ht (by linarith)
  obtain ⟨C, hC, hclt⟩ := srwKernel_scaled_localCLT
  have herror : ∀ᶠ N : ℕ in atTop, 4 * C / (v ^ 2 * (N : ℝ)) < ε / 2 := by
    have hlim := tendsto_const_div_nat (4 * C / v ^ 2)
    filter_upwards [hlim.eventually (Iio_mem_nhds (half_pos hε))] with N hN
    have hEq : (4 * C / v ^ 2) / (N : ℝ) = 4 * C / (v ^ 2 * (N : ℝ)) := by ring
    rw [hEq] at hN
    exact hN
  have htimeWindow : ∀ᶠ N : ℕ in atTop,
      (n N : ℝ) / N ∈ Set.Ioo (v / 2) (2 * v) := by
    filter_upwards [htime.eventually (Ioo_mem_nhds
      (by linarith : v / 2 < v) (by linarith : v < 2 * v))] with N hN
    exact hN
  have htimeClose : ∀ᶠ N : ℕ in atTop,
      dist ((n N : ℝ) / N) v < δ / 2 := by
    filter_upwards [htime.eventually (Metric.ball_mem_nhds v (half_pos hδ))] with N hN
    simpa only [Metric.mem_ball] using hN
  have hmesh : ∀ᶠ N : ℕ in atTop, (Real.sqrt ((N : ℝ) / 2))⁻¹ < δ / 4 := by
    filter_upwards [tendsto_lattice_mesh.eventually (Iio_mem_nhds (by positivity : 0 < δ / 4))]
      with N hN
    exact hN
  have hNlarge : ∀ᶠ N : ℕ in atTop, (2 / v : ℝ) < N :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
      (eventually_gt_atTop (2 / v))
  filter_upwards [eventually_gt_atTop 0, herror, htimeWindow, htimeClose, hmesh, hNlarge]
      with N hN hNerr hNtime hNclose hNmesh hNlarge
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlargeProduct : 1 < (v / 2) * (N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hNlarge (by positivity : 0 < v / 2)
    have hcancel : (2 / v) * (v / 2) = 1 := by field_simp [hv.ne']
    rw [hcancel] at hmul
    nlinarith
  have hnreal : (v / 2) * (N : ℝ) < (n N : ℝ) := by
    have hmul := mul_lt_mul_of_pos_right hNtime.1 hNpos
    simpa only [div_mul_cancel₀ _ hNpos.ne'] using hmul
  have hnpos : 1 ≤ n N := by
    exact_mod_cast (show (1 : ℝ) ≤ (n N : ℝ) by linarith)
  have hnlower : (v / 2) * (N : ℝ) ≤ (n N : ℝ) := hnreal.le
  have hcltError (x y : Plane) :
      |((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
          heatKernel ((n N : ℝ) / N)
            (latticeRepresentative N (latticePoint N y - latticePoint N x))| < ε / 2 := by
    have hzEven : Even ((latticePoint N y - latticePoint N x) 0 +
        (latticePoint N y - latticePoint N x) 1 + (n N : ℤ)) := by
      exact latticePoint_gap_phase N (n N) (even_evenCeil_sub ((N : ℝ) * t)
        ((N : ℝ) * (t + v))) x y
    have hraw := hclt N (n N) hN hnpos (latticePoint N y - latticePoint N x) hzEven
    have hden : ((v / 2) * (N : ℝ)) ^ 2 ≤ (n N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hnlower 2
    have hcmp : C * (N : ℝ) / (n N : ℝ) ^ 2 ≤
        4 * C / (v ^ 2 * (N : ℝ)) := by
      have hdiv := div_le_div_of_nonneg_left (by positivity : 0 ≤ C * (N : ℝ))
        (by positivity : 0 < ((v / 2) * (N : ℝ)) ^ 2) hden
      calc
        C * (N : ℝ) / (n N : ℝ) ^ 2 ≤
            C * (N : ℝ) / ((v / 2) * (N : ℝ)) ^ 2 := hdiv
        _ = 4 * C / (v ^ 2 * (N : ℝ)) := by field_simp [hNpos.ne']; ring
    calc
      |((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
          heatKernel ((n N : ℝ) / N)
            (latticeRepresentative N (latticePoint N y - latticePoint N x))|
        ≤ C * (N : ℝ) / (n N : ℝ) ^ 2 := hraw
      _ ≤ 4 * C / (v ^ 2 * (N : ℝ)) := hcmp
      _ < ε / 2 := hNerr
  have hspatial (x y : Plane) :
      dist (cellSample N y - cellSample N x) (y - x) < δ := by
    have hxsample := Critical2DKPZ.dist_cellSample_le hN x
    have hysample := Critical2DKPZ.dist_cellSample_le hN y
    have hdecomp : cellSample N y - cellSample N x - (y - x) =
        (cellSample N y - y) - (cellSample N x - x) := by abel
    rw [dist_eq_norm, hdecomp]
    calc
      ‖(cellSample N y - y) - (cellSample N x - x)‖ ≤
          ‖cellSample N y - y‖ + ‖cellSample N x - x‖ := norm_sub_le _ _
      _ = dist (cellSample N y) y + dist (cellSample N x) x := by rw [dist_eq_norm, dist_eq_norm]
      _ ≤ 2 * (Real.sqrt ((N : ℝ) / 2))⁻¹ := by linarith [hysample, hxsample]
      _ < δ := by nlinarith [hNmesh]
  intro x y hxy
  have hxK : x ∈ Kx := ⟨(x, y), hxy, rfl⟩
  have hyK : y ∈ Ky := ⟨(x, y), hxy, rfl⟩
  have hxnorm := hKxnorm hxK
  have hynorm := hKynorm hyK
  have hsamplex : ‖cellSample N x‖ ≤ Rx + 2 :=
    Critical2DKPZ.norm_cellSample_le hRx hxnorm N
  have hsampley : ‖cellSample N y‖ ≤ Ry + 2 :=
    Critical2DKPZ.norm_cellSample_le hRy hynorm N
  have hdisp (p q : Plane) (hp : ‖p‖ ≤ Rx) (hq : ‖q‖ ≤ Ry) : ‖q - p‖ ≤ Rx + Ry := by
    calc
      ‖q - p‖ ≤ ‖q‖ + ‖p‖ := norm_sub_le _ _
      _ ≤ Ry + Rx := add_le_add hq hp
      _ = Rx + Ry := by ring
  have hdispSample : ‖cellSample N y - cellSample N x‖ ≤ Rx + Ry + 4 := by
    calc
      ‖cellSample N y - cellSample N x‖ ≤ ‖cellSample N y‖ + ‖cellSample N x‖ :=
        norm_sub_le _ _
      _ ≤ (Ry + 2) + (Rx + 2) := add_le_add hsampley hsamplex
      _ = Rx + Ry + 4 := by ring
  have hdispLimit : ‖y - x‖ ≤ Rx + Ry := hdisp x y hxnorm hynorm
  have hp : ((n N : ℝ) / N, cellSample N y - cellSample N x) ∈ Kheat := by
    change ((n N : ℝ) / N ∈ Set.Icc (v / 2) (2 * v)) ∧
      (cellSample N y - cellSample N x ∈ Metric.closedBall 0 R)
    constructor
    · exact ⟨hNtime.1.le, hNtime.2.le⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right, R] using hdispSample
  have hq : (v, y - x) ∈ Kheat := by
    change (v ∈ Set.Icc (v / 2) (2 * v)) ∧ (y - x ∈ Metric.closedBall 0 R)
    constructor
    · exact ⟨by linarith, by linarith⟩
    · apply Metric.mem_closedBall.mpr
      rw [dist_zero_right]
      dsimp [R]
      linarith
  have hpairclose : dist ((n N : ℝ) / N, cellSample N y - cellSample N x)
      (v, y - x) < δ := by
    rw [Prod.dist_eq]
    exact max_lt_iff.mpr ⟨hNclose.trans (by linarith), hspatial x y⟩
  have hheat := hmod _ hp _ hq hpairclose
  have hrep : latticeRepresentative N (latticePoint N y - latticePoint N x) =
      cellSample N y - cellSample N x := by
    simp only [latticeRepresentative, cellSample]
    rw [← smul_sub]
    congr 1
    ext i
    simp [siteToPlane]
  have hcltError' := hcltError x y
  rw [hrep] at hcltError'
  have hslab : slabMeanKernel ϑ N t (t + v) x y =
      ((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) := by
    rw [slabMeanKernel_eq_srwKernel]
  rw [hslab]
  calc
    |((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
        heatKernel v (y - x)| =
      |(((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
        heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x)) +
        (heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x) - heatKernel v (y - x))| := by
          congr 1
          ring
    _ ≤ |((N : ℝ) / 4) * srwKernel (n N) (latticePoint N y - latticePoint N x) -
        heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x)| +
        |heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x) - heatKernel v (y - x)| :=
          abs_add_le _ _
    _ < ε := by
      have hheat' : |heatKernel ((n N : ℝ) / N) (cellSample N y - cellSample N x) -
          heatKernel v (y - x)| < ε / 2 := by
        simpa only [Real.dist_eq, Prod.fst, Prod.snd] using hheat
      have hhalves : ε / 2 + ε / 2 = ε := by ring
      rw [← hhalves]
      exact add_lt_add hcltError' hheat'

end Critical2DKPZ.SHF.Flow

end
