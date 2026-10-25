/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.PathAssociation
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Critical2DKPZ.SHF.Positivity.FinitePathEhrhard
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.ShfPairing
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Critical2DKPZ.SHF.Positivity.PolymerHeatEhrhard
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Positive association of lattice and flow heat-started masses -/

@[expose] public section

open MeasureTheory ProbabilityTheory Function Filter
open scoped Topology
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

/-- A nonnegative finite path mass is increasing in every disorder coordinate,
including the case of an empty or zero-weight path family. -/
theorem monotone_finitePathMass {ι : Type*} [Fintype ι] {β : ℝ} (hβ : 0 ≤ β)
    (a n : ℕ) (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ p, 0 ≤ c p) : Monotone (PolymerCalculus.finitePathMass β a n w c) := by
  intro ω ω' hω
  unfold PolymerCalculus.finitePathMass
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (PolymerCalculus.monotone_pathEnergy hβ a (w p.1) p.2 hω)) (hc p)

/-- Bounded monotone continuous tests of two finite path masses satisfy Harris's
inequality. Both masses use the same Gaussian disorder, with possibly different
finite path families and time intervals. -/
theorem finitePathMass_harris {ι κ : Type*} [Fintype ι] [Fintype κ]
    {β γ : ℝ} (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (a n b m : ℕ)
    (w : ι → Site) (v : κ → Site)
    {c : ι × (Fin n → Fin 4) → ℝ} {d : κ × (Fin m → Fin 4) → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hd : ∀ p, 0 ≤ d p)
    (φ ψ : ℝ →ᵇ ℝ) (hφ : Monotone φ) (hψ : Monotone ψ) :
    (∫ ω, φ (PolymerCalculus.finitePathMass β a n w c ω) ∂disorderLaw) *
      (∫ ω, ψ (PolymerCalculus.finitePathMass γ b m v d ω) ∂disorderLaw) ≤
      ∫ ω, φ (PolymerCalculus.finitePathMass β a n w c ω) *
        ψ (PolymerCalculus.finitePathMass γ b m v d ω) ∂disorderLaw := by
  let f : Disorder → ℝ := fun ω => φ (PolymerCalculus.finitePathMass β a n w c ω)
  let g : Disorder → ℝ := fun ω => ψ (PolymerCalculus.finitePathMass γ b m v d ω)
  let S := PolymerCalculus.finitePathCoordinates a n w ∪ PolymerCalculus.finitePathCoordinates b m v
  have hfm : Measurable f := φ.continuous.measurable.comp (PolymerCalculus.measurable_finitePathMass β a n w c)
  have hgm : Measurable g := ψ.continuous.measurable.comp (PolymerCalculus.measurable_finitePathMass γ b m v d)
  have hfi : Integrable f disorderLaw :=
    (integrable_const ‖φ‖).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => φ.norm_coe_le_norm _)
  have hgi : Integrable g disorderLaw :=
    (integrable_const ‖ψ‖).mono' hgm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ψ.norm_coe_le_norm _)
  have hfgi : Integrable (fun ω => f ω * g ω) disorderLaw := by
    apply (integrable_const (‖φ‖ * ‖ψ‖)).mono' (hfm.mul hgm).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖f ω * g ω‖ ≤ ‖φ‖ * ‖ψ‖
    rw [norm_mul]
    exact mul_le_mul (φ.norm_coe_le_norm _) (ψ.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  apply PolymerCalculus.disorder_harris_dependsOn S
    (hφ.comp (monotone_finitePathMass hβ a n w hc))
    (hψ.comp (monotone_finitePathMass hγ b m v hd)) hfm hgm ?_ ?_ hfi hgi hfgi
  · intro ω ω' hω
    apply congrArg φ
    apply PolymerCalculus.dependsOn_finitePathMass β a n w c
    intro i hi
    exact hω i (Finset.mem_union_left _ hi)
  · intro ω ω' hω
    apply congrArg ψ
    apply PolymerCalculus.dependsOn_finitePathMass γ b m v d
    intro i hi
    exact hω i (Finset.mem_union_right _ hi)

/-- Spatially truncated lattice heat masses satisfy Harris's inequality for
bounded monotone continuous tests. Their finite path coefficients are checked
nonnegative explicitly; no finite-dependence assertion is assumed. -/
theorem truncatedHeatPairing_harris (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t δ : ℝ) (hδ : 0 < δ) (x y : Plane) (K : ℝ)
    (φ ψ : ℝ →ᵇ ℝ) (hφ : Monotone φ) (hψ : Monotone ψ) :
    (∫ ω, φ (SHF.Positivity.truncatedHeatPairing ϑ N s t δ x 0 K ω) ∂disorderLaw) *
      (∫ ω, ψ (SHF.Positivity.truncatedHeatPairing ϑ N s t δ y 0 K ω) ∂disorderLaw) ≤
      ∫ ω, φ (SHF.Positivity.truncatedHeatPairing ϑ N s t δ x 0 K ω) *
        ψ (SHF.Positivity.truncatedHeatPairing ϑ N s t δ y 0 K ω) ∂disorderLaw := by
  classical
  let A := SHF.Positivity.truncatedHeatStartSites N K
  let a := evenCeil (N * s)
  let n := evenCeil (N * t) - a
  let β := criticalBeta ϑ N
  let Starts := {w : Site // w ∈ A}
  let w : Starts → Site := fun z => z.1
  let ν : Plane → Site → ℝ := fun z q => ∫ r in cell N q,
    heatKernel δ (r - z) * Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) r
  let f : Site → ℝ := cellAverage N (fun z => Real.exp ((0 : Plane →ᵇ ℝ) z))
  let c : Plane → Starts × (Fin n → Fin 4) → ℝ := fun z p =>
    ν z p.1.1 * f (walkPosition p.1.1 p.2 n) * ((4 : ℝ)⁻¹ ^ n)
  have hν : ∀ z q, 0 ≤ ν z q := by
    intro z q
    apply setIntegral_nonneg (measurableSet_cell N q)
    intro r _
    by_cases hr : r ∈ Metric.closedBall (0 : Plane) K
    · simpa only [Set.indicator_of_mem hr, mul_one] using heatKernel_nonneg hδ.le (r - z)
    · simp only [Set.indicator_of_notMem hr, mul_zero, le_refl]
  have hf : ∀ z, 0 ≤ f z := by
    intro z
    by_cases hz : z ∈ evenLattice
    · exact (Smoothing.cellAverage_exp_bounds_of_even N hN (0 : Plane →ᵇ ℝ) hz).1.le
    · dsimp only [f, cellAverage]
      rw [cell_eq_empty_of_not_even hz]
      simp only [setIntegral_empty, mul_zero, le_refl]
  have hc : ∀ z p, 0 ≤ c z p := by
    intro z p
    exact mul_nonneg (mul_nonneg (hν z p.1.1) (hf _)) (by positivity)
  have hβ : 0 ≤ β := Real.sqrt_nonneg _
  have heq (z : Plane) (ω : Disorder) :
      SHF.Positivity.truncatedHeatPairing ϑ N s t δ z 0 K ω =
        PolymerCalculus.finitePathMass β a n w (c z) ω := by
    simpa only [A, a, n, β, Starts, w, c, ν, f] using
      SHF.Positivity.truncatedHeatPairing_eq_finitePathMass ϑ hN hδ z (0 : Plane →ᵇ ℝ) K ω
  simp_rw [heq]
  exact finitePathMass_harris hβ hβ a n a n w w (hc x) (hc y) φ ψ hφ hψ

/-- The lattice Harris inequality survives removal of the spatial cutoff.
All tests are bounded, so dominated convergence applies to their products. -/
theorem polymerHeatPairing_harris (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x y : Plane)
    (φ ψ : ℝ →ᵇ ℝ) (hφ : Monotone φ) (hψ : Monotone ψ) :
    (∫ ω, φ (∫ p, heatKernel δ (p.1 - x) ∂(SHF.Limit.polymerMeasure ϑ N s t ω)) ∂disorderLaw) *
      (∫ ω, ψ (∫ p, heatKernel δ (p.1 - y) ∂(SHF.Limit.polymerMeasure ϑ N s t ω)) ∂disorderLaw) ≤
      ∫ ω, φ (∫ p, heatKernel δ (p.1 - x) ∂(SHF.Limit.polymerMeasure ϑ N s t ω)) *
        ψ (∫ p, heatKernel δ (p.1 - y) ∂(SHF.Limit.polymerMeasure ϑ N s t ω)) ∂disorderLaw := by
  let U : Plane → ℕ → Disorder → ℝ := fun z k ω =>
    SHF.Positivity.truncatedHeatPairing ϑ N s t δ z 0 ((k : ℝ) + 1) ω
  let M : Plane → Disorder → ℝ := fun z ω =>
    ∫ p, heatKernel δ (p.1 - z) ∂(SHF.Limit.polymerMeasure ϑ N s t ω)
  have hN0 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hUm (z : Plane) (k : ℕ) : Measurable (U z k) :=
    SHF.Positivity.measurable_truncatedHeatPairing ϑ N hN0 s t δ z 0 ((k : ℝ) + 1) hδ
  have hU (z : Plane) : ∀ᵐ ω ∂disorderLaw,
      Tendsto (fun k => U z k ω) atTop (𝓝 (M z ω)) := by
    filter_upwards [SHF.Positivity.ae_integrable_polymer_heat_pairing_integrand
      ϑ hN hs hst hδ z (0 : Plane →ᵇ ℝ)] with ω hω
    have hh := SHF.Positivity.tendsto_truncatedHeatPairing_of_integrable ϑ N hδ z 0 ω hω
    simpa only [U, M, BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero, mul_one] using hh
  have hE (z : Plane) (f : ℝ →ᵇ ℝ) :
      Tendsto (fun k => ∫ ω, f (U z k ω) ∂disorderLaw) atTop (𝓝 (∫ ω, f (M z ω) ∂disorderLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Disorder => ‖f‖)
    · intro k
      exact (f.continuous.measurable.comp (hUm z k)).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      exact Eventually.of_forall (fun ω => f.norm_coe_le_norm _)
    · filter_upwards [hU z] with ω hω
      exact (f.continuous.tendsto _).comp hω
  have hprod : Tendsto (fun k => ∫ ω, φ (U x k ω) * ψ (U y k ω) ∂disorderLaw) atTop
      (𝓝 (∫ ω, φ (M x ω) * ψ (M y ω) ∂disorderLaw)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Disorder => ‖φ‖ * ‖ψ‖)
    · intro k
      exact ((φ.continuous.measurable.comp (hUm x k)).mul
        (ψ.continuous.measurable.comp (hUm y k))).aestronglyMeasurable
    · exact integrable_const _
    · intro k
      filter_upwards [] with ω
      change ‖φ (U x k ω) * ψ (U y k ω)‖ ≤ ‖φ‖ * ‖ψ‖
      rw [norm_mul]
      exact mul_le_mul (φ.norm_coe_le_norm _) (ψ.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
    · filter_upwards [hU x, hU y] with ω hx hy
      exact ((φ.continuous.tendsto _).comp hx).mul ((ψ.continuous.tendsto _).comp hy)
  exact le_of_tendsto_of_tendsto ((hE x φ).mul (hE y ψ)) hprod
    (Eventually.of_forall fun k => truncatedHeatPairing_harris ϑ hN s t δ hδ x y ((k : ℝ) + 1) φ ψ hφ hψ)

/-- Joint convergence in law transfers lattice association to the flow pair. -/
theorem heatPairings_harris (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x y : Plane)
    (φ ψ : ℝ →ᵇ ℝ) (hφ : Monotone φ) (hψ : Monotone ψ) :
    (∫ ω, φ (shfPairing Z s t (fun z => heatKernel δ (z - x)) (fun _ => 1) ω) ∂P) *
      (∫ ω, ψ (shfPairing Z s t (fun z => heatKernel δ (z - y)) (fun _ => 1) ω) ∂P) ≤
      ∫ ω, φ (shfPairing Z s t (fun z => heatKernel δ (z - x)) (fun _ => 1) ω) *
        ψ (shfPairing Z s t (fun z => heatKernel δ (z - y)) (fun _ => 1) ω) ∂P := by
  let q : Fin 2 → Plane := fun i => if i = 0 then x else y
  let U : ℕ → Disorder → Fin 2 → ℝ := fun N ω i =>
    ∫ p, heatKernel δ (p.1 - q i) ∂(SHF.Limit.polymerMeasure ϑ N s t ω)
  let M : Ω → Fin 2 → ℝ := fun ω i =>
    shfPairing Z s t (fun z => heatKernel δ (z - q i)) (fun _ => 1) ω
  have hd : TendstoInDistribution U atTop M (fun _ => disorderLaw) P := by
    have hh := SHF.Positivity.isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ 2
      (fun _ => s) (fun _ => t) (fun _ => δ) q (fun _ => (1 : Plane →ᵇ ℝ))
      (fun _ => ⟨hs, hst, hδ⟩)
    have hg : ((1 : Plane →ᵇ ℝ) : Plane → ℝ) = (fun _ => 1) := by
      funext z
      simp only [BoundedContinuousFunction.coe_one, Pi.one_apply]
    simpa only [U, M, hg, mul_one] using hh
  let F : (Fin 2 → ℝ) →ᵇ ℝ := φ.compContinuous ⟨fun z => z 0, continuous_apply 0⟩
  let G : (Fin 2 → ℝ) →ᵇ ℝ := ψ.compContinuous ⟨fun z => z 1, continuous_apply 1⟩
  have ht := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hd.forall_aemeasurable hd.aemeasurable_limit).mp hd
  have hh := le_of_tendsto_of_tendsto ((ht F).mul (ht G)) (ht (F * G))
    (show ∀ᶠ N : ℕ in atTop, (∫ ω, F (U N ω) ∂disorderLaw) *
      (∫ ω, G (U N ω) ∂disorderLaw) ≤ ∫ ω, (F * G) (U N ω) ∂disorderLaw from by
        filter_upwards [eventually_ge_atTop 1] with N hN
        simpa [F, G, U, q] using polymerHeatPairing_harris ϑ hN hs hst hδ x y φ ψ hφ hψ)
  simpa [F, G, M, q] using hh

/-- Continuous increasing approximations to the indicator of a strict upper ray. -/
def upperRayRamp (u : ℝ) (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => min 1 (max 0 (((n : ℝ) + 1) * (z - u))), by fun_prop⟩ 1 (by
      intro x y
      rw [Real.dist_eq, abs_le]
      have hx : 0 ≤ min 1 (max 0 (((n : ℝ) + 1) * (x - u))) := le_min zero_le_one (le_max_left _ _)
      have hy : 0 ≤ min 1 (max 0 (((n : ℝ) + 1) * (y - u))) := le_min zero_le_one (le_max_left _ _)
      have hx' := min_le_left 1 (max 0 (((n : ℝ) + 1) * (x - u)))
      have hy' := min_le_left 1 (max 0 (((n : ℝ) + 1) * (y - u)))
      constructor <;> dsimp at * <;> linarith)

theorem upperRayRamp_bounds (u z : ℝ) (n : ℕ) :
    0 ≤ upperRayRamp u n z ∧ upperRayRamp u n z ≤ 1 := by
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

theorem monotone_upperRayRamp (u : ℝ) (n : ℕ) : Monotone (upperRayRamp u n) := by
  intro x y hxy
  exact min_le_min_left 1 (max_le_max_left 0
    (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy u) (by positivity)))

theorem tendsto_upperRayRamp (u z : ℝ) :
    Tendsto (fun n => upperRayRamp u n z) atTop
      (𝓝 (Set.indicator {z | u < z} (fun _ => (1 : ℝ)) z)) := by
  by_cases hz : u < z
  · have hzu : 0 < z - u := sub_pos.mpr hz
    obtain ⟨N, hN⟩ := exists_nat_ge ((z - u)⁻¹)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (z - u)⁻¹ ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
    have hm : 1 ≤ ((n : ℝ) + 1) * (z - u) := by
      have hh := mul_le_mul_of_nonneg_right hn' hzu.le
      rw [inv_mul_cancel₀ hzu.ne'] at hh
      nlinarith
    simp only [upperRayRamp, BoundedContinuousFunction.mkOfBound_coe,
      ContinuousMap.coe_mk]
    rw [Set.indicator_of_mem (show z ∈ {z | u < z} from hz)]
    rw [max_eq_right (by linarith), min_eq_left hm]
  · have hm (n : ℕ) : ((n : ℝ) + 1) * (z - u) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr (le_of_not_gt hz))
    have he (n : ℕ) : upperRayRamp u n z = 0 := by
      change min 1 (max 0 (((n : ℝ) + 1) * (z - u))) = 0
      rw [max_eq_left (hm n), min_eq_right zero_le_one]
    simpa only [he, Set.indicator_of_notMem (show z ∉ {z | u < z} from hz)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

/-- Bounded continuous Harris tests imply positive quadrant dependence, without
any assumption that the laws have no atoms. -/
theorem real_posQuadrant_of_harris {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hH : ∀ (φ ψ : ℝ →ᵇ ℝ), Monotone φ → Monotone ψ →
      (∫ ω, φ (X ω) ∂P) * (∫ ω, ψ (Y ω) ∂P) ≤ ∫ ω, φ (X ω) * ψ (Y ω) ∂P)
    (u v : ℝ) :
    P.real {ω | u < X ω} * P.real {ω | v < Y ω} ≤
      P.real {ω | u < X ω ∧ v < Y ω} := by
  let I : ℝ → ℝ → ℝ := fun a z => Set.indicator {z | a < z} (fun _ => 1) z
  have hi (a : ℝ) {W : Ω → ℝ} (hW : AEMeasurable W P) :
      (∫ ω, I a (W ω) ∂P) = P.real {ω | a < W ω} := by
    change (∫ ω, Set.indicator {ω | a < W ω} (fun _ => (1 : ℝ)) ω ∂P) = _
    have hs : NullMeasurableSet {ω | a < W ω} P :=
      hW.nullMeasurableSet_preimage (measurableSet_Ioi (a := a))
    rw [integral_indicator₀ hs,
      setIntegral_const, smul_eq_mul, mul_one]
  have ht (a : ℝ) {W : Ω → ℝ} (hW : AEMeasurable W P) :
      Tendsto (fun n => ∫ ω, upperRayRamp a n (W ω) ∂P) atTop
        (𝓝 (P.real {ω | a < W ω})) := by
    rw [← hi a hW]
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    · intro n
      exact ((upperRayRamp a n).continuous.measurable.comp_aemeasurable hW).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (upperRayRamp_bounds a (W ω) n).1]
      exact (upperRayRamp_bounds a (W ω) n).2
    · exact Eventually.of_forall fun ω => tendsto_upperRayRamp a (W ω)
  have hp : Tendsto (fun n => ∫ ω, upperRayRamp u n (X ω) * upperRayRamp v n (Y ω) ∂P) atTop
      (𝓝 (∫ ω, I u (X ω) * I v (Y ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    · intro n
      exact (((upperRayRamp u n).continuous.measurable.comp_aemeasurable hX).mul
        ((upperRayRamp v n).continuous.measurable.comp_aemeasurable hY)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      filter_upwards [] with ω
      change ‖upperRayRamp u n (X ω) * upperRayRamp v n (Y ω)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (upperRayRamp_bounds u (X ω) n).1 (upperRayRamp_bounds v (Y ω) n).1)]
      exact (mul_le_mul (upperRayRamp_bounds u (X ω) n).2
        (upperRayRamp_bounds v (Y ω) n).2 (upperRayRamp_bounds v (Y ω) n).1 zero_le_one).trans (by norm_num)
    · exact Eventually.of_forall fun ω => (tendsto_upperRayRamp u (X ω)).mul (tendsto_upperRayRamp v (Y ω))
  have hh := le_of_tendsto_of_tendsto ((ht u hX).mul (ht v hY)) hp
    (Eventually.of_forall fun n => hH _ _ (monotone_upperRayRamp u n) (monotone_upperRayRamp v n))
  have he : (fun ω => I u (X ω) * I v (Y ω)) =
      Set.indicator {ω | u < X ω ∧ v < Y ω} (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases hx : u < X ω <;> by_cases hy : v < Y ω <;> simp [I, hx, hy]
  have hs : NullMeasurableSet {ω | u < X ω ∧ v < Y ω} P :=
    (hX.nullMeasurableSet_preimage (measurableSet_Ioi (a := u))).inter
      (hY.nullMeasurableSet_preimage (measurableSet_Ioi (a := v)))
  rw [he, integral_indicator₀ hs, setIntegral_const, smul_eq_mul, mul_one] at hh
  exact hh

/-- Heat-started flow masses are positively quadrant dependent. The proof
uses the joint lattice limit, rather than marginal representations of their laws. -/
theorem heatMasses_posQuadrantDependent (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a n : ℝ} (ha : 0 < a) (han : a < n) (x y : Plane) (u v : ℝ) :
    P.real {ω | u < shfPairing Z a n (fun z => heatKernel a (z - x)) (fun _ => 1) ω} *
      P.real {ω | v < shfPairing Z a n (fun z => heatKernel a (z - y)) (fun _ => 1) ω} ≤
      P.real {ω | u < shfPairing Z a n (fun z => heatKernel a (z - x)) (fun _ => 1) ω ∧
        v < shfPairing Z a n (fun z => heatKernel a (z - y)) (fun _ => 1) ω} := by
  have hg : ((1 : Plane →ᵇ ℝ) : Plane → ℝ) = (fun _ => 1) := by
    funext z
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply]
  have hm (z : Plane) : AEMeasurable
      (shfPairing Z a n (fun w => heatKernel a (w - z)) (fun _ => 1)) P := by
    have hh := (SHF.Positivity.isCriticalSHF_heat_bounded_pairing ϑ P Z hZ
      ha.le han ha z (1 : Plane →ᵇ ℝ)).2.1.aestronglyMeasurable.aemeasurable
    simpa only [hg] using hh
  exact real_posQuadrant_of_harris P (hm x) (hm y)
    (fun φ ψ hφ hψ => heatPairings_harris ϑ P Z hZ ha.le han ha x y φ ψ hφ hψ) u v

end Critical2DKPZ.Extensions.GffTangent
