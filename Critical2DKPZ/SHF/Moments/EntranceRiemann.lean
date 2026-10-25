/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Normed.Group.Bounded
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
public import Critical2DKPZ.SHF.Moments.EntranceProfile
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Tactic

/-! # Shifted cell sampling for collision entrance Riemann sums

The odd spatial parity class is a unit translate of the even lattice, and sampling a compact test and a continuous profile on these translated cells preserves the continuum limit. -/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped CompactlySupported Topology Uniformity

namespace Critical2DKPZ.SHF.Moments

/-- A fixed microscopic spatial shift vanishes under diffusive rescaling. -/
theorem tendsto_latticeRepresentative_fixed_site (z : Site) :
    Tendsto (fun N : ℕ => latticeRepresentative N z) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun N : ℕ => ‖latticeRepresentative N z‖) atTop
      (𝓝 (0 * ‖siteToPlane z‖)) := by
    have h := tendsto_lattice_mesh.mul_const ‖siteToPlane z‖
    apply h.congr'
    filter_upwards with N
    rw [latticeRepresentative, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hnorm' : Tendsto (fun N : ℕ => ‖latticeRepresentative N z‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using hnorm
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hnorm'.eventually (Iio_mem_nhds hε)] with N hN
  simpa only [dist_zero_right] using hN

/-- A fixed shifted compact profile is integrable after even-lattice cell sampling at every positive scale. -/
theorem integrable_cellSample_shifted_compact_product
    (N : ℕ) (hN : 0 < N) (δ : Plane) (φ : C_c(Plane, ℝ))
    (G : Plane → ℝ) (hG : Continuous G) :
    Integrable (fun x : Plane =>
      φ (cellSample N x + δ) * G (cellSample N x + δ)) := by
  obtain ⟨R₀, hR₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp φ.hasCompactSupport.isBounded
  let R := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  obtain ⟨Cφ₀, hCφ₀⟩ := (isCompact_closedBall (0 : Plane) R).exists_bound_of_continuousOn
    φ.continuous.continuousOn
  obtain ⟨CG₀, hCG₀⟩ := (isCompact_closedBall (0 : Plane) R).exists_bound_of_continuousOn
    hG.continuousOn
  let Cφ := max Cφ₀ 0
  let CG := max CG₀ 0
  have hCφ : 0 ≤ Cφ := le_max_right _ _
  have hCG : 0 ≤ CG := le_max_right _ _
  let M := Cφ * CG
  have hM : 0 ≤ M := mul_nonneg hCφ hCG
  let K : Set Plane := Metric.closedBall 0 (R + 2 + ‖δ‖)
  let majorant : Plane → ℝ := K.indicator (fun _ => M)
  have hmajorant : Integrable majorant := by
    dsimp [majorant, K]
    exact (integrableOn_const
      (isCompact_closedBall (0 : Plane) (R + 2 + ‖δ‖)).measure_ne_top).integrable_indicator
        (isCompact_closedBall (0 : Plane) (R + 2 + ‖δ‖)).measurableSet
  have hsample (x : Plane) : dist (cellSample N x) x ≤ 2 :=
    dist_cellSample_le_two hN x
  apply hmajorant.mono'
  · have hsampled : Measurable (fun x : Plane => cellSample N x + δ) :=
      (measurable_cellSample N).add measurable_const
    exact ((φ.continuous.measurable.comp hsampled).mul
      (hG.measurable.comp hsampled)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    let y := cellSample N x + δ
    by_cases hφzero : φ y = 0
    · by_cases hx : x ∈ K
      · rw [Real.norm_eq_abs, hφzero, zero_mul, abs_zero]
        simp [majorant, hx, hM]
      · rw [Real.norm_eq_abs, hφzero, zero_mul, abs_zero]
        simp [majorant, hx]
    · have hyts : y ∈ tsupport φ := subset_tsupport φ hφzero
      have hyball₀ : y ∈ Metric.closedBall (0 : Plane) R₀ := hR₀ hyts
      have hyball : y ∈ Metric.closedBall (0 : Plane) R := by
        rw [Metric.mem_closedBall, dist_zero_right] at hyball₀ ⊢
        exact hyball₀.trans (le_max_left _ _)
      have hφbound : |φ y| ≤ Cφ := (hCφ₀ y hyball).trans (le_max_left _ _)
      have hGbound : |G y| ≤ CG := (hCG₀ y hyball).trans (le_max_left _ _)
      have hxy : dist x y ≤ 2 + ‖δ‖ := by
        dsimp [y]
        calc
          dist x (cellSample N x + δ) ≤
              dist x (cellSample N x) + dist (cellSample N x) (cellSample N x + δ) :=
            dist_triangle _ _ _
          _ ≤ 2 + ‖δ‖ := by
            apply add_le_add (by simpa [dist_comm] using hsample x)
            rw [dist_eq_norm]
            have hsub : cellSample N x - (cellSample N x + δ) = -δ := by abel
            rw [hsub, norm_neg]
      have hxnorm : ‖x‖ ≤ dist x y + ‖y‖ := by
        rw [dist_eq_norm]
        exact norm_le_norm_sub_add x y
      have hxball : x ∈ K := by
        change x ∈ Metric.closedBall (0 : Plane) (R + 2 + ‖δ‖)
        rw [Metric.mem_closedBall, dist_zero_right]
        have hyNorm : ‖y‖ ≤ R := by
          have hy := Metric.mem_closedBall.mp hyball
          simpa only [dist_zero_right] using hy
        calc
          ‖x‖ ≤ dist x y + ‖y‖ := hxnorm
          _ ≤ (2 + ‖δ‖) + R := add_le_add hxy hyNorm
          _ = R + 2 + ‖δ‖ := by ring
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |φ y| * |G y| ≤ Cφ * CG :=
          mul_le_mul hφbound hGbound (abs_nonneg _) hCφ
        _ = majorant x := by simp [majorant, hxball, M]


/-- The sampled compact product equals its cell sum, with zero contributions from odd sites whose even-lattice cells are empty. -/
theorem integral_cellSample_shifted_compact_product_eq_tsum
    (N : ℕ) (hN : 0 < N) (δ : Plane) (φ : C_c(Plane, ℝ))
    (G : Plane → ℝ) (hG : Continuous G) :
    (∫ x : Plane, φ (cellSample N x + δ) * G (cellSample N x + δ)) =
      ∑' z : Site, (volume (cell N z)).toReal *
        (φ (latticeRepresentative N z + δ) * G (latticeRepresentative N z + δ)) := by
  let f : Plane → ℝ := fun x => φ (cellSample N x + δ) * G (cellSample N x + δ)
  have hf : Integrable f := integrable_cellSample_shifted_compact_product N hN δ φ G hG
  have hcover : (⋃ z : Site, cell N z) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨latticePoint N x, mem_cell_latticePoint N x⟩
  have hdecomp := integral_iUnion (measurableSet_cell N) (pairwise_disjoint_cell N)
    hf.integrableOn
  rw [hcover, setIntegral_univ] at hdecomp
  rw [hdecomp]
  apply tsum_congr
  intro z
  have hz : ∀ x ∈ cell N z,
      f x = φ (latticeRepresentative N z + δ) * G (latticeRepresentative N z + δ) := by
    intro x hx
    dsimp [f]
    rw [cellSample_eq_of_mem_cell hx]
  rw [setIntegral_congr_fun (measurableSet_cell N z) hz, setIntegral_const]
  simp only [smul_eq_mul, Measure.real_def]



/-- The heat-kernel product cell sum remains convergent when its two starting
centres move with the lattice scale. -/
theorem tendsto_heatKernel_pair_cellSum_moving_time_profile_along
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (uN : ℕ → ℝ) {u : ℝ} (hu : 0 < u)
    (huN : Tendsto uN atTop (𝓝 u))
    (aN bN : ℕ → Plane) (a b : Plane)
    (ha : Tendsto aN atTop (𝓝 a)) (hb : Tendsto bN atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ t x, |F (t, x)| ≤ C)
    (hFsupport : ∀ t x, F (t, x) ≠ 0 → ‖x‖ ≤ R)
    (hFcont : Continuous F) (δ : ℕ → Plane) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑' z : Site, (volume (cell (M N) z)).toReal *
      (F (uN N, latticeRepresentative (M N) z + δ N) *
        (heatKernel (uN N) (latticeRepresentative (M N) z + δ N - aN N) *
          heatKernel (uN N) (latticeRepresentative (M N) z + δ N - bN N)))) atTop
      (𝓝 (∫ x : Plane, F (u, x) *
        (heatKernel u (x - a) * heatKernel u (x - b)))) := by
  let K := (2 * Real.pi * (u / 2))⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have htimeEventually : ∀ᶠ N : ℕ in atTop, u / 2 < uN N :=
    huN.eventually (Ioi_mem_nhds (by linarith))
  have hKbound (N : ℕ) (hN : u / 2 < uN N) (x : Plane) :
      0 ≤ heatKernel (uN N) x ∧ heatKernel (uN N) x ≤ K := by
    have huNpos : 0 < uN N := by linarith
    have hden₀ : 0 < 2 * Real.pi * (u / 2) := by positivity
    have hden : 0 < 2 * Real.pi * uN N := by positivity
    have hdenle : 2 * Real.pi * (u / 2) ≤ 2 * Real.pi * uN N := by
      gcongr
    have hkernelBound : (2 * Real.pi * uN N)⁻¹ ≤ K := by
      exact (inv_le_inv₀ hden hden₀).2 hdenle
    exact ⟨heatKernel_nonneg huNpos.le x,
      (heatKernel_le_at_zero huNpos.le x).trans hkernelBound⟩
  let B := C * K ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let S : Set Plane := Metric.closedBall 0 (R + 3)
  let majorant : Plane → ℝ := S.indicator (fun _ => B)
  have hmajorant : Integrable majorant := by
    dsimp [majorant, S]
    exact (integrableOn_const
      (isCompact_closedBall (0 : Plane) (R + 3)).measure_ne_top).integrable_indicator
        (isCompact_closedBall (0 : Plane) (R + 3)).measurableSet
  have hδnorm : Tendsto (fun N : ℕ => ‖δ N‖) atTop (𝓝 0) := by
    simpa using hδ.norm
  have hδsmall : ∀ᶠ N : ℕ in atTop, ‖δ N‖ < 1 :=
    hδnorm.eventually (Iio_mem_nhds (by norm_num))
  have hMpos : ∀ᶠ N : ℕ in atTop, 0 < M N :=
    hM.eventually (eventually_gt_atTop 0)
  have hint : Tendsto (fun N : ℕ => ∫ x : Plane,
      F (uN N, cellSample (M N) x + δ N) *
        (heatKernel (uN N) (cellSample (M N) x + δ N - aN N) *
          heatKernel (uN N) (cellSample (M N) x + δ N - bN N))) atTop
      (𝓝 (∫ x : Plane, F (u, x) *
        (heatKernel u (x - a) * heatKernel u (x - b)))) := by
    apply tendsto_integral_filter_of_dominated_convergence majorant
    · exact Filter.Eventually.of_forall fun N => by
        have hsample : Measurable (fun x : Plane => cellSample (M N) x + δ N) :=
          (measurable_cellSample (M N)).add measurable_const
        have hpair : Measurable (fun x : Plane => (uN N, cellSample (M N) x + δ N)) :=
          measurable_const.prodMk hsample
        exact ((hFcont.measurable.comp hpair).mul
          (((measurable_heatKernel (uN N)).comp (hsample.sub measurable_const)).mul
            ((measurable_heatKernel (uN N)).comp (hsample.sub measurable_const)))).aestronglyMeasurable
    · filter_upwards [hMpos, hδsmall, htimeEventually] with N hN hδN huNpos
      apply Filter.Eventually.of_forall
      intro x
      let y := cellSample (M N) x + δ N
      change ‖F (uN N, y) *
        (heatKernel (uN N) (y - aN N) * heatKernel (uN N) (y - bN N))‖ ≤ majorant x
      by_cases hFzero : F (uN N, y) = 0
      · by_cases hx : x ∈ S
        · rw [Real.norm_eq_abs, hFzero, zero_mul, abs_zero]
          simp [majorant, hx, hB]
        · rw [Real.norm_eq_abs, hFzero, zero_mul, abs_zero]
          simp [majorant, hx]
      · have hyNorm : ‖y‖ ≤ R := hFsupport (uN N) y hFzero
        have hyball : y ∈ Metric.closedBall (0 : Plane) R := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hyNorm
        have hFbound' : |F (uN N, y)| ≤ C := hFbound (uN N) y
        have haKernel := hKbound N huNpos (y - aN N)
        have hbKernel := hKbound N huNpos (y - bN N)
        have hsample : dist (cellSample (M N) x) x ≤ 2 :=
          dist_cellSample_le_two hN x
        have hxy : dist x y ≤ 2 + ‖δ N‖ := by
          dsimp [y]
          calc
            dist x (cellSample (M N) x + δ N) ≤
                dist x (cellSample (M N) x) + dist (cellSample (M N) x) (cellSample (M N) x + δ N) :=
              dist_triangle _ _ _
            _ ≤ 2 + ‖δ N‖ := by
              apply add_le_add (by simpa [dist_comm] using hsample)
              rw [dist_eq_norm]
              have hsub : cellSample (M N) x - (cellSample (M N) x + δ N) = -δ N := by abel
              rw [hsub, norm_neg]
        have hxball : x ∈ S := by
          change x ∈ Metric.closedBall (0 : Plane) (R + 3)
          rw [Metric.mem_closedBall, dist_zero_right]
          have hyNorm : ‖y‖ ≤ R := by
            have hy := Metric.mem_closedBall.mp hyball
            simpa only [dist_zero_right] using hy
          have hxnorm : ‖x‖ ≤ dist x y + ‖y‖ := by
            rw [dist_eq_norm]
            exact norm_le_norm_sub_add x y
          calc
            ‖x‖ ≤ dist x y + ‖y‖ := hxnorm
            _ ≤ (2 + ‖δ N‖) + R := add_le_add hxy hyNorm
            _ ≤ R + 3 := by linarith
        rw [Real.norm_eq_abs, abs_mul]
        have hprod :
            |heatKernel (uN N) (y - aN N) * heatKernel (uN N) (y - bN N)| ≤ K ^ 2 := by
          rw [abs_of_nonneg (mul_nonneg haKernel.1 hbKernel.1)]
          calc
            heatKernel (uN N) (y - aN N) * heatKernel (uN N) (y - bN N) ≤ K * K :=
              mul_le_mul haKernel.2 hbKernel.2 hbKernel.1 hK.le
            _ = K ^ 2 := by rw [pow_two]
        calc
          |F (uN N, y)| *
              |heatKernel (uN N) (y - aN N) * heatKernel (uN N) (y - bN N)| ≤ C * K ^ 2 :=
            mul_le_mul hFbound' hprod (abs_nonneg _) hC
          _ = majorant x := by simp [majorant, hxball, B]
    · exact hmajorant
    · exact Filter.Eventually.of_forall fun x => by
        have hsample : Tendsto (fun N : ℕ => cellSample (M N) x) atTop (𝓝 x) :=
          (tendsto_cellSample x).comp hM
        have hshift : Tendsto (fun N : ℕ => cellSample (M N) x + δ N) atTop (𝓝 x) := by
          simpa using hsample.add hδ
        have hargA : Tendsto (fun N : ℕ => cellSample (M N) x + δ N - aN N) atTop (𝓝 (x - a)) :=
          hshift.sub ha
        have hargB : Tendsto (fun N : ℕ => cellSample (M N) x + δ N - bN N) atTop (𝓝 (x - b)) :=
          hshift.sub hb
        have hpair0 : Tendsto (fun N : ℕ => (uN N, cellSample (M N) x + δ N))
            atTop (𝓝 (u, x)) := huN.prodMk_nhds hshift
        have hpairA : Tendsto (fun N : ℕ => (uN N, cellSample (M N) x + δ N - aN N))
            atTop (𝓝 (u, x - a)) := huN.prodMk_nhds hargA
        have hpairB : Tendsto (fun N : ℕ => (uN N, cellSample (M N) x + δ N - bN N))
            atTop (𝓝 (u, x - b)) := huN.prodMk_nhds hargB
        have hposOpen : IsOpen {p : ℝ × Plane | 0 < p.1} :=
          isOpen_lt continuous_const continuous_fst
        have hjoint : ContinuousOn (fun p : ℝ × Plane => heatKernel p.1 p.2)
            {p | 0 < p.1} := Critical2DKPZ.DeltaBose.continuousOn_heatKernel
        have hheatA : ContinuousAt (fun p : ℝ × Plane => heatKernel p.1 p.2)
            (u, x - a) :=
          hjoint.continuousAt (hposOpen.mem_nhds hu)
        have hheatB : ContinuousAt (fun p : ℝ × Plane => heatKernel p.1 p.2)
            (u, x - b) :=
          hjoint.continuousAt (hposOpen.mem_nhds hu)
        exact Tendsto.mul
          (hFcont.continuousAt.tendsto.comp hpair0)
          (Tendsto.mul (hheatA.tendsto.comp hpairA) (hheatB.tendsto.comp hpairB))
  have hlim := hint
  apply hlim.congr'
  filter_upwards [hMpos] with N hN
  let φN : C_c(Plane, ℝ) :=
    ⟨⟨fun x => F (uN N, x), hFcont.comp (continuous_const.prodMk continuous_id)⟩,
      HasCompactSupport.intro (isCompact_closedBall (0 : Plane) R) fun x hx => by
        have hxnorm : ¬ ‖x‖ ≤ R := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hx
        by_contra hxzero
        exact hxnorm (hFsupport (uN N) x hxzero)⟩
  exact integral_cellSample_shifted_compact_product_eq_tsum (M N) hN (δ N) φN
    (fun x => heatKernel (uN N) (x - aN N) * heatKernel (uN N) (x - bN N))
    ((continuous_heatKernel (uN N)).comp (continuous_id.sub continuous_const) |>.mul
      ((continuous_heatKernel (uN N)).comp (continuous_id.sub continuous_const)))




/-- The spatial heat-kernel cell sum at scale N and macroscopic time u. -/
@[expose] noncomputable def heatKernelPairCellSum (N : ℕ) (u : ℝ) (aN bN : ℕ → Plane)
    (δ : ℕ → Plane) (F : ℝ × Plane → ℝ) : ℝ :=
  ∑' z : Site, (volume (cell N z)).toReal *
    (F (u, latticeRepresentative N z + δ N) *
      (heatKernel u (latticeRepresentative N z + δ N - aN N) *
        heatKernel u (latticeRepresentative N z + δ N - bN N)))

/-- The continuum spatial collision profile at positive time. -/
@[expose] noncomputable def heatKernelPairProfileIntegral (u : ℝ) (a b : Plane)
    (F : ℝ × Plane → ℝ) : ℝ :=
  ∫ x : Plane, F (u, x) * (heatKernel u (x - a) * heatKernel u (x - b))

/-- The continuum spatial profile is continuous in positive heat time under a
uniform spatial support and bound. -/
theorem continuousOn_heatKernelPairProfileIntegral
    (a b : Plane) (F : ℝ × Plane → ℝ) (R C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ u x, |F (u, x)| ≤ C)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R)
    (hFcont : Continuous F) :
    ContinuousOn (fun u => heatKernelPairProfileIntegral u a b F) {u : ℝ | 0 < u} := by
  intro u hu
  have hu0 : 0 < u := hu
  have hcont (x : Plane) : ContinuousAt (fun p : ℝ × Plane => heatKernel p.1 p.2)
      (u, x) := by
    have hposOpen : IsOpen {p : ℝ × Plane | 0 < p.1} :=
      isOpen_lt continuous_const continuous_fst
    have hjoint : ContinuousOn (fun p : ℝ × Plane => heatKernel p.1 p.2)
        {p | 0 < p.1} := Critical2DKPZ.DeltaBose.continuousOn_heatKernel
    exact hjoint.continuousAt (hposOpen.mem_nhds hu)
  have hpointwise : ∀ v : ℕ → ℝ, Tendsto v atTop (𝓝 u) →
      Tendsto (fun N => heatKernelPairProfileIntegral (v N) a b F) atTop
        (𝓝 (heatKernelPairProfileIntegral u a b F)) := by
    intro v hv
    let K := (2 * Real.pi * (u / 2))⁻¹
    have hK : 0 < K := by dsimp [K]; positivity
    have htimeEventually : ∀ᶠ N : ℕ in atTop, u / 2 < v N :=
      hv.eventually (Ioi_mem_nhds (by linarith [hu0]))
    let majorant : Plane → ℝ := (Metric.closedBall (0 : Plane) R).indicator
      (fun _ => C * K ^ 2)
    have hB : 0 ≤ C * K ^ 2 := mul_nonneg hC (sq_nonneg K)
    have hmajorant : Integrable majorant := by
      dsimp [majorant]
      exact (integrableOn_const
        (isCompact_closedBall (0 : Plane) R).measure_ne_top).integrable_indicator
          (isCompact_closedBall (0 : Plane) R).measurableSet
    apply tendsto_integral_filter_of_dominated_convergence majorant
    · exact Filter.Eventually.of_forall fun N => by
        have hFmeas : Measurable (fun x : Plane => F (v N, x)) :=
          hFcont.measurable.comp (measurable_const.prodMk measurable_id)
        have hka : Measurable (fun x : Plane => heatKernel (v N) (x - a)) :=
          (measurable_heatKernel (v N)).comp (measurable_id.sub measurable_const)
        have hkb : Measurable (fun x : Plane => heatKernel (v N) (x - b)) :=
          (measurable_heatKernel (v N)).comp (measurable_id.sub measurable_const)
        exact (hFmeas.mul (hka.mul hkb)).aestronglyMeasurable
    · filter_upwards [htimeEventually] with N hvN
      apply Filter.Eventually.of_forall
      intro x
      by_cases hzero : F (v N, x) = 0
      · by_cases hx : x ∈ Metric.closedBall (0 : Plane) R
        · rw [Real.norm_eq_abs, hzero, zero_mul, abs_zero]
          simp [majorant, hx, hB]
        · rw [Real.norm_eq_abs, hzero, zero_mul, abs_zero]
          simp [majorant, hx]
      · have hxnorm : ‖x‖ ≤ R := hFsupport (v N) x hzero
        have hxball : x ∈ Metric.closedBall (0 : Plane) R := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact hxnorm
        have hkernel (z : Plane) :
            0 ≤ heatKernel (v N) z ∧ heatKernel (v N) z ≤ K := by
          have hvNpos : 0 < v N := by linarith [hu0]
          have hden₀ : 0 < 2 * Real.pi * (u / 2) := by positivity
          have hden : 0 < 2 * Real.pi * v N := by positivity
          have hdenle : 2 * Real.pi * (u / 2) ≤ 2 * Real.pi * v N := by
            exact mul_le_mul_of_nonneg_left (by linarith [hvN]) (by positivity)
          have hK' : (2 * Real.pi * v N)⁻¹ ≤ K :=
            (inv_le_inv₀ hden hden₀).2 hdenle
          exact ⟨heatKernel_nonneg hvNpos.le z,
            (heatKernel_le_at_zero hvNpos.le z).trans hK'⟩
        have hka := hkernel (x - a)
        have hkb := hkernel (x - b)
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |F (v N, x)| *
              |heatKernel (v N) (x - a) * heatKernel (v N) (x - b)| ≤ C * K ^ 2 := by
            have hprod :
                |heatKernel (v N) (x - a) * heatKernel (v N) (x - b)| ≤ K ^ 2 := by
              rw [abs_of_nonneg (mul_nonneg hka.1 hkb.1)]
              calc
                heatKernel (v N) (x - a) * heatKernel (v N) (x - b) ≤ K * K :=
                  mul_le_mul hka.2 hkb.2 hkb.1 hK.le
                _ = K ^ 2 := by rw [pow_two]
            exact mul_le_mul (hFbound (v N) x) hprod (abs_nonneg _) hC
          _ = majorant x := by simp [majorant, hxball]
    · exact hmajorant
    · exact Filter.Eventually.of_forall fun x => by
        have hp : Tendsto (fun N => (v N, x - a)) atTop (𝓝 (u, x - a)) :=
          hv.prodMk_nhds tendsto_const_nhds
        have hpa : Tendsto (fun N => (v N, x - b)) atTop (𝓝 (u, x - b)) :=
          hv.prodMk_nhds tendsto_const_nhds
        have hFconv : Tendsto (fun N => F (v N, x)) atTop (𝓝 (F (u, x))) :=
          hFcont.continuousAt.tendsto.comp (hv.prodMk_nhds tendsto_const_nhds)
        exact Tendsto.mul hFconv
          (Tendsto.mul ((hcont (x - a)).tendsto.comp hp)
            ((hcont (x - b)).tendsto.comp hpa))
  have hcontI : ContinuousAt (fun v => heatKernelPairProfileIntegral v a b F) u := by
    change Tendsto (fun v => heatKernelPairProfileIntegral v a b F) (𝓝 u)
      (𝓝 (heatKernelPairProfileIntegral u a b F))
    rw [tendsto_iff_seq_tendsto]
    intro v hv
    exact hpointwise v hv
  exact hcontI.continuousWithinAt

/-- The moving-time spatial cell sums converge locally uniformly on positive
times. The sequential cell limit along arbitrary lattice subsequences supplies
the uniformity needed before the microscopic-time Riemann sum. -/
theorem tendstoLocallyUniformlyOn_heatKernelPairCellSum
    (aN bN : ℕ → Plane) (a b : Plane)
    (ha : Tendsto aN atTop (𝓝 a)) (hb : Tendsto bN atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ u x, |F (u, x)| ≤ C)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R)
    (hFcont : Continuous F) (δ : ℕ → Plane) (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn
      (fun N u => heatKernelPairCellSum N u aN bN δ F)
      (fun u => heatKernelPairProfileIntegral u a b F) atTop {u : ℝ | 0 < u} := by
  have hopen : IsOpen {u : ℝ | 0 < u} := isOpen_lt continuous_const continuous_id
  apply hopen.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro u hu
  rw [tendsto_iff_seq_tendsto]
  intro p hp
  rcases (tendsto_prod_iff'.mp hp) with ⟨hM, huN⟩
  let M : ℕ → ℕ := fun k => (p k).1
  let uSeq : ℕ → ℝ := fun k => (p k).2
  have hM' : Tendsto M atTop atTop := by simpa [M] using hM
  have huSeq : Tendsto uSeq atTop (𝓝 u) := by simpa [uSeq] using huN
  have hA : Tendsto (fun k => aN (M k)) atTop (𝓝 a) := ha.comp hM'
  have hB : Tendsto (fun k => bN (M k)) atTop (𝓝 b) := hb.comp hM'
  have hδ' : Tendsto (fun k => δ (M k)) atTop (𝓝 0) := hδ.comp hM'
  have hS : Tendsto (fun k => heatKernelPairCellSum (M k) (uSeq k) aN bN δ F)
      atTop (𝓝 (heatKernelPairProfileIntegral u a b F)) := by
    have h := tendsto_heatKernel_pair_cellSum_moving_time_profile_along
      M hM' uSeq hu huSeq (fun k => aN (M k)) (fun k => bN (M k)) a b hA hB
      F R C hC hFbound hFsupport hFcont (fun k => δ (M k)) hδ'
    simpa [heatKernelPairCellSum, heatKernelPairProfileIntegral] using h
  have hIcont := continuousOn_heatKernelPairProfileIntegral
    a b F R C hC hFbound hFsupport hFcont
  have hI : Tendsto (fun k => heatKernelPairProfileIntegral (uSeq k) a b F)
      atTop (𝓝 (heatKernelPairProfileIntegral u a b F)) := by
    exact (hIcont.continuousAt (hopen.mem_nhds hu)).tendsto.comp huSeq
  have hdist : Tendsto (fun k =>
      dist (heatKernelPairProfileIntegral (uSeq k) a b F)
        (heatKernelPairCellSum (M k) (uSeq k) aN bN δ F)) atTop (𝓝 0) := by
    simpa only [dist_self] using Filter.Tendsto.dist hI hS
  have hpair : Tendsto (fun k =>
      (heatKernelPairProfileIntegral (uSeq k) a b F,
        heatKernelPairCellSum (M k) (uSeq k) aN bN δ F)) atTop (𝓤 ℝ) := by
    rw [Metric.uniformity_basis_dist.tendsto_right_iff]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp hdist) ε hε] with k hk
    have hnonneg : 0 ≤ dist (heatKernelPairProfileIntegral (uSeq k) a b F)
        (heatKernelPairCellSum (M k) (uSeq k) aN bN δ F) := dist_nonneg
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hk
  simpa [Function.comp_def, M, uSeq, heatKernelPairCellSum, heatKernelPairProfileIntegral]
    using hpair

/-- On every compact positive-time interval, the spatial cell sums converge
uniformly in the macroscopic time. -/
theorem tendstoUniformlyOn_heatKernelPairCellSum_Icc {s t : ℝ} (hs : 0 < s)
    (aN bN : ℕ → Plane) (a b : Plane)
    (ha : Tendsto aN atTop (𝓝 a)) (hb : Tendsto bN atTop (𝓝 b))
    (F : ℝ × Plane → ℝ) (R C : ℝ) (hC : 0 ≤ C)
    (hFbound : ∀ u x, |F (u, x)| ≤ C)
    (hFsupport : ∀ u x, F (u, x) ≠ 0 → ‖x‖ ≤ R)
    (hFcont : Continuous F) (δ : ℕ → Plane) (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoUniformlyOn
      (fun N u => heatKernelPairCellSum N u aN bN δ F)
      (fun u => heatKernelPairProfileIntegral u a b F) atTop (Set.Icc s t) := by
  have hlocal := tendstoLocallyUniformlyOn_heatKernelPairCellSum
    aN bN a b ha hb F R C hC hFbound hFsupport hFcont δ hδ
  have hsubset : Set.Icc s t ⊆ {u : ℝ | 0 < u} := by
    intro u hu
    exact lt_of_lt_of_le hs hu.1
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    (isCompact_Icc : IsCompact (Set.Icc s t))).mp (hlocal.mono hsubset)

/-- Uniformly convergent summands have the same moving-endpoint time Riemann
limit as their continuous profile on a positive slab. -/
theorem tendsto_scaledIntervalSum_uniformlyConverging {s t : ℝ} (hs : 0 < s)
    (hst : s < t) {M₀ M₁ : ℕ → ℕ} (hMmono : ∀ N, M₀ N ≤ M₁ N)
    (hM₀ratio : Tendsto (fun N : ℕ => (M₀ N : ℝ) / N) atTop (𝓝 s))
    (hM₁ratio : Tendsto (fun N : ℕ => (M₁ N : ℝ) / N) atTop (𝓝 t))
    (f : ℝ → ℝ) (fN : ℕ → ℝ → ℝ) (hf : Continuous f)
    (huniform : TendstoUniformlyOn fN f atTop (Set.Icc s (t + 1)))
    (hM₀lower : ∀ᶠ N : ℕ in atTop, s ≤ (M₀ N : ℝ) / N)
    (hM₁upper : ∀ᶠ N : ℕ in atTop, (M₁ N : ℝ) / N ≤ t + 1) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N), fN N ((r : ℝ) / N)) atTop
      (𝓝 (∫ u in s..t, f u)) := by
  have hbase := tendsto_collisionEntranceScaledIntervalSum f hf hs hst hMmono
    hM₀ratio hM₁ratio
  have herr : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
        (fN N ((r : ℝ) / N) - f ((r : ℝ) / N))) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    let η : ℝ := ε / (2 * (t + 2))
    have ht2 : 0 < t + 2 := by linarith [lt_trans hs hst]
    have hη : 0 < η := by dsimp [η]; exact div_pos hε (mul_pos (by norm_num) ht2)
    have hrel : {p : ℝ × ℝ | dist p.1 p.2 < η} ∈ 𝓤 ℝ :=
      Metric.uniformity_basis_dist.mem_iff.mpr ⟨η, hη, subset_rfl⟩
    obtain ⟨Nclose, hNclose⟩ := eventually_atTop.mp (huniform _ hrel)
    obtain ⟨Nlower, hNlower⟩ := eventually_atTop.mp hM₀lower
    obtain ⟨Nupper, hNupper⟩ := eventually_atTop.mp hM₁upper
    obtain ⟨Npos, hNpos⟩ := eventually_atTop.mp (eventually_gt_atTop 0)
    refine ⟨max (max Nclose Nlower) (max Nupper Npos), fun N hN => ?_⟩
    have hleft : max Nclose Nlower ≤ N :=
      (le_max_left _ _).trans hN
    have hright : max Nupper Npos ≤ N :=
      (le_max_right _ _).trans hN
    have hNclose_le : Nclose ≤ N := (le_max_left _ _).trans hleft
    have hNlower_le : Nlower ≤ N := (le_max_right _ _).trans hleft
    have hNupper_le : Nupper ≤ N := (le_max_left _ _).trans hright
    have hNpos_le : Npos ≤ N := (le_max_right _ _).trans hright
    have hNreal : (0 : ℝ) < N := by
      exact_mod_cast (hNpos N hNpos_le)
    have hNone : (1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (hNpos N hNpos_le)
    have hlow : s ≤ (M₀ N : ℝ) / N := hNlower N hNlower_le
    have hupp : (M₁ N : ℝ) / N ≤ t + 1 := hNupper N hNupper_le
    have hcloseN := hNclose N hNclose_le
    have hgrid : ∀ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
        (r : ℝ) / N ∈ Set.Icc s (t + 1) := by
      intro r hr
      have hrlo : M₀ N ≤ r := le_trans (Nat.le_succ _) (Finset.mem_Icc.mp hr).1
      have hrhi : r ≤ M₁ N := (Finset.mem_Icc.mp hr).2
      constructor
      · calc
          s ≤ (M₀ N : ℝ) / N := hlow
          _ ≤ (r : ℝ) / N := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hNreal)
            exact_mod_cast hrlo
      · exact (div_le_div_of_nonneg_right (by exact_mod_cast hrhi)
          (le_of_lt hNreal)).trans hupp
    have hpoint : ∀ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
        |fN N ((r : ℝ) / N) - f ((r : ℝ) / N)| ≤ η := by
      intro r hr
      have h := hcloseN ((r : ℝ) / N) (hgrid r hr)
      have hdist : dist (f ((r : ℝ) / N) ) (fN N ((r : ℝ) / N)) < η := by
        exact h
      have hdist' : |f ((r : ℝ) / N) - fN N ((r : ℝ) / N)| < η := by
        simpa only [Real.dist_eq] using hdist
      have hswap : |fN N ((r : ℝ) / N) - f ((r : ℝ) / N)| < η := by
        simpa only [abs_sub_comm] using hdist'
      exact hswap.le
    have hsubset : Finset.Icc (M₀ N + 1) (M₁ N) ⊆ Finset.range (M₁ N + 1) := by
      intro r hr
      simp only [Finset.mem_Icc] at hr
      simp only [Finset.mem_range]
      omega
    have hcardNat : (Finset.Icc (M₀ N + 1) (M₁ N)).card ≤ M₁ N + 1 := by
      calc
        _ ≤ (Finset.range (M₁ N + 1)).card := Finset.card_le_card hsubset
        _ = M₁ N + 1 := by simp
    have hcard : ((Finset.Icc (M₀ N + 1) (M₁ N)).card : ℝ) ≤ (M₁ N : ℝ) + 1 := by
      exact_mod_cast hcardNat
    have hsmall : (1 : ℝ) / N ≤ 1 := by
      rw [div_le_iff₀ hNreal]
      simpa only [one_mul] using hNone
    have hcount : ((Finset.Icc (M₀ N + 1) (M₁ N)).card : ℝ) / N ≤ t + 2 := by
      calc
        _ ≤ ((M₁ N : ℝ) + 1) / N :=
          div_le_div_of_nonneg_right hcard (le_of_lt hNreal)
        _ = (M₁ N : ℝ) / N + 1 / N := by rw [add_div]
        _ ≤ (t + 1) + 1 := add_le_add hupp hsmall
        _ = t + 2 := by ring
    have hsumBound : |∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
        (fN N ((r : ℝ) / N) - f ((r : ℝ) / N))| ≤
          ((Finset.Icc (M₀ N + 1) (M₁ N)).card : ℝ) * η := by
      calc
        _ ≤ ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
          |fN N ((r : ℝ) / N) - f ((r : ℝ) / N)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _r ∈ Finset.Icc (M₀ N + 1) (M₁ N), η :=
          Finset.sum_le_sum fun r hr => hpoint r hr
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    have hcoef : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
    have hbound : |(N : ℝ)⁻¹ *
        ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
          (fN N ((r : ℝ) / N) - f ((r : ℝ) / N))| < ε := by
      calc
        |(N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
            (fN N ((r : ℝ) / N) - f ((r : ℝ) / N))| =
          (N : ℝ)⁻¹ * |∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
            (fN N ((r : ℝ) / N) - f ((r : ℝ) / N))| := by
              rw [abs_mul, abs_of_nonneg hcoef]
        _ ≤ (N : ℝ)⁻¹ * (((Finset.Icc (M₀ N + 1) (M₁ N)).card : ℝ) * η) :=
          mul_le_mul_of_nonneg_left hsumBound hcoef
        _ = (((Finset.Icc (M₀ N + 1) (M₁ N)).card : ℝ) / N) * η := by ring
        _ ≤ (t + 2) * η := mul_le_mul_of_nonneg_right hcount hη.le
        _ = ε / 2 := by dsimp [η]; field_simp [ne_of_gt ht2]
        _ < ε := by linarith
    simpa only [Real.dist_eq, sub_zero] using hbound
  have hsum := hbase.add herr
  have hcongr (N : ℕ) :
      (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N), fN N ((r : ℝ) / N) =
        ((N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N), f ((r : ℝ) / N)) +
          ((N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
            (fN N ((r : ℝ) / N) - f ((r : ℝ) / N))) := by
    calc
      _ = (N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
          (f ((r : ℝ) / N) +
            (fN N ((r : ℝ) / N) - f ((r : ℝ) / N))) := by
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          ring
      _ = (N : ℝ)⁻¹ *
          (∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N), f ((r : ℝ) / N) +
            ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
              (fN N ((r : ℝ) / N) - f ((r : ℝ) / N))) := by
          rw [Finset.sum_add_distrib]
      _ = _ := by rw [mul_add]
  have hsum' : Tendsto (fun N : ℕ =>
      ((N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N), f ((r : ℝ) / N)) +
        ((N : ℝ)⁻¹ * ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
          (fN N ((r : ℝ) / N) - f ((r : ℝ) / N)))) atTop
      (𝓝 (∫ u in s..t, f u)) := by simpa only [add_zero] using hsum
  apply hsum'.congr'
  filter_upwards with N
  exact (hcongr N).symm
/-- The heat-cell profile with its spatial parity shift selected by the
microscopic time index under the macroscopic time argument. -/
@[expose] noncomputable def parityHeatKernelPairCellSum (N : ℕ) (u : ℝ)
    (aN bN : ℕ → Plane) (δeven δodd : ℕ → Plane) (F : ℝ × Plane → ℝ) : ℝ :=
  if ⌊(N : ℝ) * u⌋₊ % 2 = 0 then
    heatKernelPairCellSum N u aN bN δeven F
  else
    heatKernelPairCellSum N u aN bN δodd F

end Critical2DKPZ.SHF.Moments

end
