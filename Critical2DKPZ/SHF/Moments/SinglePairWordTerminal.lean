/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordUniform
import Mathlib.Tactic

/-! # Terminal walk profiles for the two-particle future limit -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- The terminal factor can be summed over the walk's endpoint set. Cell tests
outside their finite support and kernels outside the endpoint set vanish. -/
theorem pairTwoFutureTerminalCellFactor_eq_endpointSum (N k : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site)
    (w : Site) (i : Fin 2) :
    pairTwoFutureTerminalCellFactor N k φ x w i =
      ∑ y ∈ endpoints w k, cellTestWeight N (φ i) (x i) y * srwKernel k (y - w) := by
  classical
  let Y := ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
    Prod.snd)
  let E := endpoints w k
  let f : Site → ℝ := fun y => cellTestWeight N (φ i) (x i) y * srwKernel k (y - w)
  have hweight (y : Site) (hy : y ∉ Y) : cellTestWeight N (φ i) (x i) y = 0 := by
    have hzero : (∫ p in cell N (x i) ×ˢ cell N y, φ i p) = 0 := by
      by_contra hne
      apply hy
      exact Finset.mem_image.mpr ⟨(x i, y),
        (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).mem_toFinset.mpr hne,
        rfl⟩
    simp [cellTestWeight, hzero]
  have hkernel (y : Site) :
      (if w ∈ endpoints y k then f y else 0) = f y := by
    by_cases hy : w ∈ endpoints y k
    · simp [hy]
    · have hz : srwKernel k (y - w) = 0 := by
        rw [Polymer.srwKernel_sub_swap]
        exact Polymer.srwKernel_eq_zero_of_not_mem k y w hy
      simp [f, hy, hz]
  have hleft : (∑ y ∈ Y, f y) = ∑ y ∈ Y ∪ E, f y := by
    apply Finset.sum_subset Finset.subset_union_left
    intro y hy hyY
    simp [f, hweight y hyY]
  have hright : (∑ y ∈ E, f y) = ∑ y ∈ Y ∪ E, f y := by
    apply Finset.sum_subset Finset.subset_union_right
    intro y hy hyE
    simp [f, Polymer.srwKernel_eq_zero_of_not_mem k w y hyE]
  calc
    pairTwoFutureTerminalCellFactor N k φ x w i = ∑ y ∈ Y, f y := by
      unfold pairTwoFutureTerminalCellFactor
      apply Finset.sum_congr rfl
      intro y hy
      exact hkernel y
    _ = ∑ y ∈ E, f y := hleft.trans hright.symm

/-- Accessible terminal sites lie in the even lattice when the terminal time and collision site have matching parity. -/
private theorem terminal_endpoint_even {k : ℕ} {w y : Site}
    (hphase : Even (w 0 + w 1 + (k : ℤ))) (hy : y ∈ endpoints w k) :
    y ∈ evenLattice := by
  have hp := endpoints_accessible_phase k w y hy
  change Even (y 0 + y 1)
  rw [Int.even_iff] at hphase hp ⊢
  simp only [Pi.sub_apply] at hp
  omega

/-- Replacing terminal cell tests by sampled tests has a vanishing error after
multiplication by `N`, uniformly over the terminal clock and collision site. -/
theorem pairTwoFutureTerminalCellFactor_sample_error
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (i : Fin 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ∀ x : Fin 2 → Site, x i ∈ evenLattice →
      ∀ w : Site, Even (w 0 + w 1 + (k : ℤ)) →
      |(N : ℝ) * pairTwoFutureTerminalCellFactor N k φ x w i -
        4 * ∑ y ∈ endpoints w k,
          φ i (latticeRepresentative N (x i), latticeRepresentative N y) *
            srwKernel k (y - w)| ≤ 4 * ε := by
  have happ := eventually_cellTestWeight_close_to_frozen_sample (φ i) hε
  filter_upwards [happ, eventually_gt_atTop 0] with N happN hN
  intro k x hx w hphase
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hmass : (∑ y ∈ endpoints w k, srwKernel k (y - w)) = 1 :=
    Polymer.sum_srwKernel_endpoints k w
  have hpoint (y : Site) (hy : y ∈ endpoints w k) :
      |(N : ℝ) * (cellTestWeight N (φ i) (x i) y -
        (4 / (N : ℝ)) * φ i (latticeRepresentative N (x i), latticeRepresentative N y)) *
          srwKernel k (y - w)| ≤ 4 * ε * srwKernel k (y - w) := by
    have he := happN (x i) y hx (terminal_endpoint_even hphase hy)
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg N),
      abs_of_nonneg (srwKernel_nonneg _ _)]
    calc
      (N : ℝ) * |cellTestWeight N (φ i) (x i) y -
          (4 / (N : ℝ)) * φ i (latticeRepresentative N (x i), latticeRepresentative N y)| *
          srwKernel k (y - w) ≤
        ((N : ℝ) * ((4 / (N : ℝ)) * ε)) * srwKernel k (y - w) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)) (srwKernel_nonneg _ _)
      _ = 4 * ε * srwKernel k (y - w) := by field_simp
  rw [pairTwoFutureTerminalCellFactor_eq_endpointSum]
  have hsum : (N : ℝ) * (∑ y ∈ endpoints w k,
        cellTestWeight N (φ i) (x i) y * srwKernel k (y - w)) -
      4 * (∑ y ∈ endpoints w k,
        φ i (latticeRepresentative N (x i), latticeRepresentative N y) * srwKernel k (y - w)) =
      ∑ y ∈ endpoints w k,
        (N : ℝ) * (cellTestWeight N (φ i) (x i) y -
          (4 / (N : ℝ)) * φ i (latticeRepresentative N (x i), latticeRepresentative N y)) *
            srwKernel k (y - w) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    field_simp
  rw [hsum]
  calc
    _ ≤ ∑ y ∈ endpoints w k,
        |(N : ℝ) * (cellTestWeight N (φ i) (x i) y -
          (4 / (N : ℝ)) * φ i (latticeRepresentative N (x i), latticeRepresentative N y)) *
            srwKernel k (y - w)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ endpoints w k, 4 * ε * srwKernel k (y - w) :=
      Finset.sum_le_sum hpoint
    _ = 4 * ε := by rw [← Finset.mul_sum, hmass, mul_one]

private theorem terminal_cell_displacement_phase {k : ℕ} {w y : Site}
    (hphase : Even (w 0 + w 1 + (k : ℤ))) (hy : y ∈ evenLattice) :
    Even ((y - w) 0 + (y - w) 1 + (k : ℤ)) := by
  change Even (y 0 + y 1) at hy
  rw [Int.even_iff] at hphase hy ⊢
  simp only [Pi.sub_apply]
  omega

/-- A compact terminal section at a fixed incoming point. -/
def terminalSectionTest (φ : C_c(Plane × Plane, ℝ)) (a : Plane) :
    C_c(Plane, ℝ) where
  toFun y := φ (a, y)
  continuous_toFun := φ.continuous.comp (continuous_const.prodMk continuous_id)
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      (φ.hasCompactSupport.image continuous_snd)
    intro y hy
    exact ⟨(a, y), subset_closure (Function.mem_support.mpr hy), rfl⟩

/-- Evaluation of a compact terminal section. -/
@[simp] theorem terminalSectionTest_apply (φ : C_c(Plane × Plane, ℝ)) (a y : Plane) :
    terminalSectionTest φ a y = φ (a, y) := rfl

private theorem eventually_terminalWalkCellDensity_bound_along
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {q : ℝ} (hq : 0 < q) (kN : ℕ → ℕ)
    (hk : Tendsto (fun N : ℕ => (kN N : ℝ) / M N) atTop (𝓝 q))
    (wN : ℕ → Site)
    (hphase : ∀ᶠ N : ℕ in atTop, Even (wN N 0 + wN N 1 + (kN N : ℤ))) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ y : Plane,
      0 ≤ (M N / 4 : ℝ) * srwKernel (kN N) (latticePoint (M N) y - wN N) ∧
      (M N / 4 : ℝ) * srwKernel (kN N) (latticePoint (M N) y - wN N) ≤ K := by
  obtain ⟨C, hC, hlocal⟩ := srwKernel_scaled_localCLT_away_zero (half_pos hq)
  let K₀ : ℝ := (2 * Real.pi * (q / 2))⁻¹
  have hK₀ : 0 < K₀ := by dsimp [K₀]; positivity
  refine ⟨K₀ + C, by positivity, ?_⟩
  filter_upwards [hM.eventually (eventually_gt_atTop 0), hphase,
    hk.eventually (Ioi_mem_nhds (half_lt_self hq))] with N hN hp htime
  intro y
  have hNr : (0 : ℝ) < M N := by exact_mod_cast hN
  have hgap : (q / 2) * M N ≤ (kN N : ℝ) :=
    ((lt_div_iff₀ hNr).mp htime).le
  have hkpos : 1 ≤ kN N := by
    have : (0 : ℝ) < kN N := (mul_pos (half_pos hq) hNr).trans_le hgap
    exact_mod_cast this
  have hpar := terminal_cell_displacement_phase hp (latticePoint_mem_evenLattice (M N) y)
  have he := hlocal (M N) (kN N) hN hkpos hgap (latticePoint (M N) y - wN N) hpar
  have htpos : 0 < (kN N : ℝ) / M N := div_pos (by exact_mod_cast hkpos) hNr
  have hheat : heatKernel ((kN N : ℝ) / M N)
      (latticeRepresentative (M N) (latticePoint (M N) y - wN N)) ≤ K₀ := by
    apply (heatKernel_le_at_zero htpos.le _).trans
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    exact mul_le_mul_of_nonneg_left htime.le (by positivity)
  have hCN : C / (M N : ℝ) ≤ C := by
    apply (div_le_iff₀ hNr).2
    exact le_mul_of_one_le_right hC.le (by exact_mod_cast hN)
  refine ⟨mul_nonneg (by positivity) (srwKernel_nonneg _ _), ?_⟩
  have he' := (abs_le.mp he).2
  linarith

/-- A compact terminal test against the walk converges along moving positive
clocks and moving collision sites, on the matching parity class. -/
theorem tendsto_terminalWalkTest_moving_along
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {q : ℝ} (hq : 0 < q) (kN : ℕ → ℕ)
    (hk : Tendsto (fun N : ℕ => (kN N : ℝ) / M N) atTop (𝓝 q))
    (wN : ℕ → Site) (w : Plane)
    (hw : Tendsto (fun N : ℕ => latticeRepresentative (M N) (wN N)) atTop (𝓝 w))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (wN N 0 + wN N 1 + (kN N : ℤ)))
    (ψ : C_c(Plane, ℝ)) :
    Tendsto (fun N : ℕ => ∑ y ∈ endpoints (wN N) (kN N),
      ψ (latticeRepresentative (M N) y) * srwKernel (kN N) (y - wN N)) atTop
      (𝓝 (∫ y : Plane, ψ y * heatKernel q (y - w))) := by
  obtain ⟨K, hK, hbound⟩ := eventually_terminalWalkCellDensity_bound_along M hM hq kN hk wN hphase
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp
    ψ.hasCompactSupport.isBounded
  let P : ℝ := ‖ψ.toBoundedContinuousFunction‖
  let S : Set Plane := Metric.closedBall 0 (R + 2)
  let B : Plane → ℝ := S.indicator (fun _ => P * K)
  let f : ℕ → Plane → ℝ := fun N y => ψ (cellSample (M N) y) *
    ((M N / 4 : ℝ) * srwKernel (kN N) (latticePoint (M N) y - wN N))
  have hP : 0 ≤ P := norm_nonneg _
  have hB : Integrable B := by
    exact (integrableOn_const (C := P * K)
      (isCompact_closedBall (0 : Plane) (R + 2)).measure_ne_top).integrable_indicator (isCompact_closedBall (0 : Plane) (R + 2)).measurableSet
  have hmeas (N : ℕ) : AEStronglyMeasurable (f N) := by
    exact ((ψ.continuous.measurable.comp (measurable_cellSample (M N))).mul
      (measurable_const.mul ((measurable_of_countable fun z : Site =>
        srwKernel (kN N) (z - wN N)).comp (measurable_latticePoint (M N))))).aestronglyMeasurable
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ y : Plane, ‖f N y‖ ≤ B y := by
    filter_upwards [hbound, hM.eventually (eventually_gt_atTop 0)] with N hboundN hN
    intro y
    by_cases hz : ψ (cellSample (M N) y) = 0
    · by_cases hy : y ∈ S <;> simp [f, hz, B, hy, mul_nonneg hP hK.le]
    · have hsample : ‖cellSample (M N) y‖ ≤ R := by
        have hp := hR (subset_closure (Function.mem_support.mpr hz))
        simpa only [Metric.mem_closedBall, dist_zero_right] using hp
      have hy : y ∈ S := by
        rw [Metric.mem_closedBall, dist_zero_right]
        calc
          ‖y‖ ≤ dist y (cellSample (M N) y) + ‖cellSample (M N) y‖ :=
            norm_le_norm_sub_add y (cellSample (M N) y)
          _ ≤ 2 + R := add_le_add (by simpa only [dist_comm] using dist_cellSample_le_two hN y) hsample
          _ = R + 2 := by ring
      have hψ : |ψ (cellSample (M N) y)| ≤ P := by
        exact ψ.toBoundedContinuousFunction.norm_coe_le_norm _
      dsimp [f]
      rw [abs_mul, abs_of_nonneg (hboundN y).1]
      exact (mul_le_mul hψ (hboundN y).2 (hboundN y).1 hP).trans_eq
        (by simp [B, hy])
  have hpoint (y : Plane) : Tendsto (fun N => f N y) atTop
      (𝓝 (ψ y * heatKernel q (y - w))) := by
    have hz : Tendsto (fun N : ℕ => latticeRepresentative (M N) (latticePoint (M N) y - wN N))
        atTop (𝓝 (y - w)) := by
      simp only [latticeRepresentative_sub]
      exact ((tendsto_cellSample y).comp hM).sub hw
    have hp : ∀ᶠ N : ℕ in atTop,
        Even ((latticePoint (M N) y - wN N) 0 + (latticePoint (M N) y - wN N) 1 + (kN N : ℤ)) := by
      filter_upwards [hphase] with N hpN
      exact terminal_cell_displacement_phase hpN (latticePoint_mem_evenLattice (M N) y)
    exact (ψ.continuous.continuousAt.tendsto.comp ((tendsto_cellSample y).comp hM)).mul
      (tendsto_scaled_srwKernel_along M hM hq hk hz hp)
  have hlim : Tendsto (fun N => ∫ y : Plane, f N y) atTop
      (𝓝 (∫ y : Plane, ψ y * heatKernel q (y - w))) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · exact Eventually.of_forall hmeas
    · exact hdom.mono fun N hN => Eventually.of_forall hN
    · exact hB
    · exact Eventually.of_forall hpoint
  have hint : ∀ᶠ N : ℕ in atTop, Integrable (f N) := by
    filter_upwards [hdom] with N hN
    exact hB.mono' (hmeas N) (Eventually.of_forall hN)
  apply hlim.congr'
  filter_upwards [hint, hphase, hM.eventually (eventually_gt_atTop 0)] with N hintN hpN hN
  have hcover : (⋃ y : Site, cell (M N) y) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact Set.mem_iUnion.mpr ⟨latticePoint (M N) y, mem_cell_latticePoint (M N) y⟩
  have hdecomp := integral_iUnion (measurableSet_cell (M N)) (pairwise_disjoint_cell (M N)) hintN.integrableOn
  rw [hcover, setIntegral_univ] at hdecomp
  have hcell (y : Site) : (∫ p in cell (M N) y, f N p) =
      ψ (latticeRepresentative (M N) y) * srwKernel (kN N) (y - wN N) := by
    have heq (p : Plane) (hp : p ∈ cell (M N) y) : f N p =
        ψ (latticeRepresentative (M N) y) * ((M N / 4 : ℝ) * srwKernel (kN N) (y - wN N)) := by
      simp only [f, cellSample_eq_of_mem_cell hp, (mem_cell_iff (M N) y p).mp hp]
    rw [setIntegral_congr_fun (measurableSet_cell (M N) y) heq, setIntegral_const,
      measureReal_def, smul_eq_mul]
    by_cases hy : y ∈ endpoints (wN N) (kN N)
    · rw [volume_cell_toReal hN (terminal_endpoint_even hpN hy)]
      have hNr : (M N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp
    · simp [Polymer.srwKernel_eq_zero_of_not_mem (kN N) (wN N) y hy]
  symm
  calc
    (∑ y ∈ endpoints (wN N) (kN N),
        ψ (latticeRepresentative (M N) y) * srwKernel (kN N) (y - wN N)) =
        ∑' y : Site, ψ (latticeRepresentative (M N) y) * srwKernel (kN N) (y - wN N) := by
          symm
          apply tsum_eq_sum
          intro y hy
          simp [Polymer.srwKernel_eq_zero_of_not_mem (kN N) (wN N) y hy]
    _ = ∫ y : Plane, f N y := by rw [hdecomp]; exact tsum_congr fun y => (hcell y).symm

private theorem tendsto_terminalWalkTest_moving_incoming_along
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {q : ℝ} (hq : 0 < q) (kN : ℕ → ℕ)
    (hk : Tendsto (fun N : ℕ => (kN N : ℝ) / M N) atTop (𝓝 q))
    (wN : ℕ → Site) (w : Plane)
    (hw : Tendsto (fun N : ℕ => latticeRepresentative (M N) (wN N)) atTop (𝓝 w))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (wN N 0 + wN N 1 + (kN N : ℤ)))
    (φ : C_c(Plane × Plane, ℝ)) (aN : ℕ → Plane) (a : Plane)
    (ha : Tendsto aN atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => ∑ y ∈ endpoints (wN N) (kN N),
      φ (aN N, latticeRepresentative (M N) y) * srwKernel (kN N) (y - wN N)) atTop
      (𝓝 (∫ y : Plane, φ (a, y) * heatKernel q (y - w))) := by
  let ψ := terminalSectionTest φ a
  let S : ℕ → ℝ := fun N => ∑ y ∈ endpoints (wN N) (kN N),
    φ (aN N, latticeRepresentative (M N) y) * srwKernel (kN N) (y - wN N)
  let T : ℕ → ℝ := fun N => ∑ y ∈ endpoints (wN N) (kN N),
    ψ (latticeRepresentative (M N) y) * srwKernel (kN N) (y - wN N)
  have herr : Tendsto (fun N => S N - T N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactlySupportedContinuousMapClass.uniformContinuous φ) (ε / 2) (by positivity)
    filter_upwards [ha.eventually (Metric.ball_mem_nhds a hδ)] with N hN
    have hpoint (y : Site) :
        |(φ (aN N, latticeRepresentative (M N) y) - φ (a, latticeRepresentative (M N) y)) *
            srwKernel (kN N) (y - wN N)| ≤ (ε / 2) * srwKernel (kN N) (y - wN N) := by
      have hd : dist (aN N, latticeRepresentative (M N) y) (a, latticeRepresentative (M N) y) < δ := by
        simpa only [dist_prod_same_right] using hN
      have he : |φ (aN N, latticeRepresentative (M N) y) - φ (a, latticeRepresentative (M N) y)| ≤ ε / 2 := by
        simpa only [Real.dist_eq] using (hmod hd).le
      rw [abs_mul, abs_of_nonneg (srwKernel_nonneg _ _)]
      exact mul_le_mul_of_nonneg_right he (srwKernel_nonneg _ _)
    have hsum : S N - T N = ∑ y ∈ endpoints (wN N) (kN N),
        (φ (aN N, latticeRepresentative (M N) y) - φ (a, latticeRepresentative (M N) y)) *
          srwKernel (kN N) (y - wN N) := by
      dsimp [S, T, ψ, terminalSectionTest]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    rw [Real.dist_eq, sub_zero, hsum]
    calc
      _ ≤ ∑ y ∈ endpoints (wN N) (kN N),
          |(φ (aN N, latticeRepresentative (M N) y) - φ (a, latticeRepresentative (M N) y)) *
            srwKernel (kN N) (y - wN N)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ endpoints (wN N) (kN N), (ε / 2) * srwKernel (kN N) (y - wN N) :=
        Finset.sum_le_sum fun y _ => hpoint y
      _ = ε / 2 := by rw [← Finset.mul_sum, Polymer.sum_srwKernel_endpoints, mul_one]
      _ < ε := by linarith
  have hwalk := tendsto_terminalWalkTest_moving_along M hM hq kN hk wN w hw hphase ψ
  have hwalk' : Tendsto T atTop (𝓝 (∫ y : Plane, φ (a, y) * heatKernel q (y - w))) := hwalk
  have h := herr.add hwalk'
  simpa only [sub_add_cancel, zero_add] using h

/-- The terminal cell factor converges to the continuum terminal convolution with the even-cell area factor four. -/
theorem tendsto_pairTwoFutureTerminalCellFactor_moving_along
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {q : ℝ} (hq : 0 < q) (kN : ℕ → ℕ)
    (hk : Tendsto (fun N : ℕ => (kN N : ℝ) / M N) atTop (𝓝 q))
    (wN : ℕ → Site) (w : Plane)
    (hw : Tendsto (fun N : ℕ => latticeRepresentative (M N) (wN N)) atTop (𝓝 w))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (wN N 0 + wN N 1 + (kN N : ℤ)))
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (xN : ℕ → Fin 2 → Site) (i : Fin 2)
    (hx : ∀ᶠ N : ℕ in atTop, xN N i ∈ evenLattice) (a : Plane)
    (ha : Tendsto (fun N : ℕ => latticeRepresentative (M N) (xN N i)) atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => (M N : ℝ) *
      pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) (wN N) i) atTop
      (𝓝 (4 * ∫ y : Plane, φ i (a, y) * heatKernel q (y - w))) := by
  let S : ℕ → ℝ := fun N => ∑ y ∈ endpoints (wN N) (kN N),
    φ i (latticeRepresentative (M N) (xN N i), latticeRepresentative (M N) y) *
      srwKernel (kN N) (y - wN N)
  have herr : Tendsto (fun N : ℕ => (M N : ℝ) *
      pairTwoFutureTerminalCellFactor (M N) (kN N) φ (xN N) (wN N) i - 4 * S N) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have he := pairTwoFutureTerminalCellFactor_sample_error φ i (show 0 < ε / 8 by positivity)
    filter_upwards [hM.eventually he, hx, hphase] with N heN hxN hpN
    rw [Real.dist_eq, sub_zero]
    exact (heN (kN N) (xN N) hxN (wN N) hpN).trans_lt (by linarith)
  have hwalk := (tendsto_terminalWalkTest_moving_incoming_along M hM hq kN hk wN w hw hphase
    (φ i) (fun N => latticeRepresentative (M N) (xN N i)) a ha).const_mul 4
  have hwalk' : Tendsto (fun N => 4 * S N) atTop
      (𝓝 (4 * ∫ y : Plane, φ i (a, y) * heatKernel q (y - w))) := hwalk
  have h := herr.add hwalk'
  simpa only [sub_add_cancel, zero_add] using h

/-- The terminal walk test limit at the full sequence of lattice scales. -/
theorem tendsto_terminalWalkTest_moving
    {q : ℝ} (hq : 0 < q) (kN : ℕ → ℕ)
    (hk : Tendsto (fun N : ℕ => (kN N : ℝ) / N) atTop (𝓝 q))
    (wN : ℕ → Site) (w : Plane)
    (hw : Tendsto (fun N : ℕ => latticeRepresentative N (wN N)) atTop (𝓝 w))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (wN N 0 + wN N 1 + (kN N : ℤ)))
    (ψ : C_c(Plane, ℝ)) :
    Tendsto (fun N : ℕ => ∑ y ∈ endpoints (wN N) (kN N),
      ψ (latticeRepresentative N y) * srwKernel (kN N) (y - wN N)) atTop
      (𝓝 (∫ y : Plane, ψ y * heatKernel q (y - w))) := by
  exact tendsto_terminalWalkTest_moving_along id tendsto_id hq kN hk wN w hw hphase ψ


end Critical2DKPZ.SHF.Moments

end
