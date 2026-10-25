/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Provider.EhrhardTypeCharacterization
public import Critical2DKPZ.PolymerCalculus.PathAssociation
public import Critical2DKPZ.PolymerCalculus.BoundarySliceDisorder
public import Critical2DKPZ.SHF.Limit.LocalFinite
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.JointConvergence.HeatStartProfileApprox
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Smoothing.ParityHelpers
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Ehrhard type for a finite polymer path mass -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open Critical2DKPZ.SHF.Limit
open scoped BigOperators ENNReal
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Positivity

/-- The finite set of lattice cells intersecting the truncated starting ball. -/
noncomputable def truncatedHeatStartSites (N : ℕ) (K : ℝ) : Finset Site :=
  (finite_latticePoint_image_of_bounded (N := N)
    (Metric.isBounded_closedBall (x := (0 : Plane)) (r := K))).toFinset

/-- Every lattice cell meeting the cutoff ball belongs to the finite start set. -/
theorem latticePoint_mem_truncatedHeatStartSites (N : ℕ) (K : ℝ) {y : Plane}
    (hy : y ∈ Metric.closedBall (0 : Plane) K) :
    latticePoint N y ∈ truncatedHeatStartSites N K := by
  apply (finite_latticePoint_image_of_bounded (N := N)
    (Metric.isBounded_closedBall (x := (0 : Plane)) (r := K))).mem_toFinset.mpr
  exact ⟨y, hy, rfl⟩

/-- The cell mass of the cutoff heat start vanishes outside its finite lattice support. -/
theorem truncatedHeatStartMass_eq_zero_of_not_mem (N : ℕ) (δ : ℝ) (x : Plane)
    (K : ℝ) {w : Site} (hw : w ∉ truncatedHeatStartSites N K) :
    (∫ y in cell N w, heatKernel δ (y - x) *
      Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) y) = 0 := by
  calc
    _ = ∫ y in cell N w, (0 : ℝ) := by
      apply setIntegral_congr_fun (measurableSet_cell N w)
      intro y hy
      by_cases hball : y ∈ Metric.closedBall (0 : Plane) K
      · have hcell : latticePoint N y = w := (mem_cell_iff N w y).mp hy
        exact False.elim (hw (hcell ▸ latticePoint_mem_truncatedHeatStartSites N K hball))
      · simp [hball]
    _ = 0 := by simp

/-- The heat-start pairing with its starting test truncated to a closed ball. -/
def truncatedHeatPairing (ϑ : ℝ) (N : ℕ) (s t δ : ℝ) (x : Plane)
    (h₀ : Plane →ᵇ ℝ) (K : ℝ) (ω : Disorder) : ℝ :=
  ∫ p, heatKernel δ (p.1 - x) *
    Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) p.1 *
    Real.exp (h₀ p.2) ∂(SHF.Limit.polymerMeasure ϑ N s t ω)

/-- The truncated heat-start integrand is integrable for every disorder configuration, by local finiteness of the first marginal and boundedness of the terminal test. -/
theorem integrable_truncatedHeatPairing_integrand (ϑ : ℝ) (N : ℕ)
    (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ) (K : ℝ) (ω : Disorder)
    (hδ : 0 < δ) :
    Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) *
      Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) p.1 *
      Real.exp (h₀ p.2)) (SHF.Limit.polymerMeasure ϑ N s t ω) := by
  let μ := SHF.Limit.polymerMeasure ϑ N s t ω
  let B : Set Plane := Metric.closedBall (0 : Plane) K
  let H : Plane → ℝ := fun y => heatKernel δ (y - x) *
    Set.indicator B (fun _ => (1 : ℝ)) y
  let G : Plane → ℝ := fun y => Real.exp (h₀ y)
  have hMarginalLocal : IsLocallyFiniteMeasure (μ.map Prod.fst) := by
    dsimp [μ]
    exact SHF.Limit.isLocallyFiniteMeasure_polymerMarginal ϑ N s t ω
  have hMarginalFiniteCompacts : IsFiniteMeasureOnCompacts (μ.map Prod.fst) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hBfinite : (μ.map Prod.fst) B < ∞ := by
    exact hMarginalFiniteCompacts.lt_top_of_isCompact
      (isCompact_closedBall (0 : Plane) K)
  have hkernel : AEStronglyMeasurable (fun y : Plane => heatKernel δ (y - x))
      ((μ.map Prod.fst).restrict B) := by
    exact ((Critical2DKPZ.continuous_heatKernel δ).comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable.mono_measure
        (Measure.restrict_le_self)
  have hkernelBound : ∀ᵐ y ∂(μ.map Prod.fst).restrict B,
      ‖heatKernel δ (y - x)‖ ≤ (2 * Real.pi * δ)⁻¹ := by
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (Critical2DKPZ.heatKernel_nonneg hδ.le _)]
    exact Critical2DKPZ.heatKernel_le_at_zero hδ.le _
  have hKernelOn : IntegrableOn (fun y : Plane => heatKernel δ (y - x)) B
      (μ.map Prod.fst) :=
    IntegrableOn.of_bound hBfinite hkernel ((2 * Real.pi * δ)⁻¹) hkernelBound
  have hHintegrable : Integrable H (μ.map Prod.fst) := by
    have hH : H = B.indicator (fun y : Plane => heatKernel δ (y - x)) := by
      funext y
      by_cases hy : y ∈ B <;> simp [H, B, hy]
    rw [hH]
    exact hKernelOn.integrable_indicator Metric.isClosed_closedBall.measurableSet
  have hHjoint : Integrable (fun p : Plane × Plane => H p.1) μ := by
    exact hHintegrable.comp_measurable measurable_fst
  have hGjoint : AEStronglyMeasurable (fun p : Plane × Plane => G p.2) μ := by
    exact (Real.continuous_exp.comp (h₀.continuous.comp continuous_snd)).aestronglyMeasurable
  have hGbound : ∀ᵐ p ∂μ, ‖G p.2‖ ≤ Real.exp ‖h₀‖ := by
    filter_upwards [] with p
    change ‖Real.exp (h₀ p.2)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) (by
      simpa only [Real.norm_eq_abs] using h₀.norm_coe_le_norm p.2))
  have hprod : Integrable (fun p : Plane × Plane => H p.1 * G p.2) μ :=
    hHjoint.mul_bdd hGjoint hGbound
  simpa [μ, H, G, B, mul_assoc] using hprod

/-- Cell decomposition of the truncated pairing. This is the heat-start profile formula with
the initial cell masses cut off on the prescribed ball. -/
theorem truncatedHeatPairing_eq_profile (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {s t δ : ℝ} (x : Plane) (h₀ : Plane →ᵇ ℝ) (K : ℝ) (ω : Disorder)
    (hInt : Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - x) *
        Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) p.1 *
        Real.exp (h₀ p.2)) (SHF.Limit.polymerMeasure ϑ N s t ω)) :
    truncatedHeatPairing ϑ N s t δ x h₀ K ω =
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
        (fun w => ∫ y in cell N w, heatKernel δ (y - x) *
          Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) y)
        (fun z => cellAverage N (fun y => Real.exp (h₀ y)) z) ω := by
  classical
  let β : ℝ := criticalBeta ϑ N
  let a : ℕ := evenCeil (N * s)
  let b : ℕ := evenCeil (N * t)
  let H : Plane → ℝ := fun y => heatKernel δ (y - x) *
    Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) y
  let G : Plane → ℝ := fun y => Real.exp (h₀ y)
  let ν : Site → ℝ := fun w => ∫ y in cell N w, H y
  let f : Site → ℝ := cellAverage N G
  let C : Site × Site → Set (Plane × Plane) := fun q => cell N q.1 ×ˢ cell N q.2
  have hden : Measurable (fun p : Plane × Plane =>
      ENNReal.ofReal (rescaledP2P ϑ N s t p ω)) := by
    exact ENNReal.measurable_ofReal.comp
      (SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s t |>.of_uncurry_right)
  have hdenFinite : ∀ᵐ p ∂(volume : Measure (Plane × Plane)),
      ENNReal.ofReal (rescaledP2P ϑ N s t p ω) < ⊤ := by
    filter_upwards [] with p
    exact ENNReal.ofReal_lt_top
  have hvolInt : Integrable (fun p : Plane × Plane =>
      (H p.1 * G p.2) * rescaledP2P ϑ N s t p ω)
      (volume : Measure (Plane × Plane)) := by
    change Integrable (fun p : Plane × Plane => H p.1 * G p.2)
      ((volume : Measure (Plane × Plane)).withDensity
        (fun p => ENNReal.ofReal (rescaledP2P ϑ N s t p ω))) at hInt
    have h := (integrable_withDensity_iff hden hdenFinite).mp hInt
    simpa only [ENNReal.toReal_ofReal
      (SHF.Moments.rescaledP2P_nonneg ϑ N s t _ ω)] using h
  have hcover : ⋃ q : Site × Site, C q = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact Set.mem_iUnion.mpr ⟨(latticePoint N p.1, latticePoint N p.2),
      ⟨mem_cell_latticePoint N p.1, mem_cell_latticePoint N p.2⟩⟩
  have hCmeas : ∀ q : Site × Site, MeasurableSet (C q) := by
    intro q
    exact (measurableSet_cell N q.1).prod (measurableSet_cell N q.2)
  have hCdisj : Pairwise (fun q r => Disjoint (C q) (C r)) := by
    intro q r hqr
    apply Set.disjoint_left.mpr
    rintro p ⟨hp₁, hp₂⟩ ⟨hr₁, hr₂⟩
    by_cases hfirst : q.1 = r.1
    · have hsecond : q.2 ≠ r.2 := by
        intro h
        exact hqr (Prod.ext hfirst h)
      exact (pairwise_disjoint_cell N hsecond).le_bot ⟨hp₂, hr₂⟩
    · exact (pairwise_disjoint_cell N hfirst).le_bot ⟨hp₁, hr₁⟩
  have hcellHasSum : HasSum
      (fun q : Site × Site => ∫ p in C q,
        (H p.1 * G p.2) * rescaledP2P ϑ N s t p ω
          ∂(volume : Measure (Plane × Plane)))
      (∫ p, (H p.1 * G p.2) * rescaledP2P ϑ N s t p ω
        ∂(volume : Measure (Plane × Plane))) := by
    have h := hasSum_integral_iUnion hCmeas hCdisj hvolInt.integrableOn
    simpa only [hcover, setIntegral_univ] using h
  have hdecomp := integral_iUnion hCmeas hCdisj hvolInt.integrableOn
  rw [hcover, setIntegral_univ] at hdecomp
  have hcell (w z : Site) :
      (∫ p in C (w, z), (H p.1 * G p.2) * rescaledP2P ϑ N s t p ω
        ∂(volume : Measure (Plane × Plane))) =
      ν w * f z * pointToPoint β a (b - a) w z ω := by
    have hconst (p : Plane × Plane) (hp : p ∈ C (w, z)) :
      rescaledP2P ϑ N s t p ω = (N : ℝ) / 4 *
          pointToPoint β a (b - a) w z ω := by
      have hp' : p.1 ∈ cell N w ∧ p.2 ∈ cell N z := hp
      have hfirst : latticePoint N p.1 = w := (mem_cell_iff N w p.1).mp hp'.1
      have hsecond : latticePoint N p.2 = z := (mem_cell_iff N z p.2).mp hp'.2
      rw [rescaledP2P, hfirst, hsecond]
    rw [Measure.volume_eq_prod]
    rw [setIntegral_congr_fun (hCmeas (w, z)) (fun p hp => by rw [hconst p hp])]
    rw [show (fun p : Plane × Plane =>
        H p.1 * G p.2 * ((N : ℝ) / 4 *
          pointToPoint β a (b - a) w z ω)) =
        fun p => (H p.1 * G p.2) * ((N : ℝ) / 4 *
          pointToPoint β a (b - a) w z ω) by funext p; ring]
    rw [integral_mul_const, setIntegral_prod_mul]
    have hfcell : (N : ℝ) / 4 * (∫ y in cell N z, G y) = f z := by
      by_cases hz : z ∈ evenLattice
      · have hv := volume_cell_toReal hN hz
        dsimp [f, cellAverage]
        rw [hv]
        field_simp
      · have hcellEmpty : cell N z = ∅ := cell_eq_empty_of_not_even hz
        simp [f, cellAverage, hcellEmpty]
    dsimp [ν]
    rw [← hfcell]
    ring
  have hpairSummable : Summable (fun q : Site × Site =>
      ν q.1 * (pointToPoint β a (b - a) q.1 q.2 ω * f q.2)) := by
    apply hcellHasSum.summable.congr
    intro q
    rcases q with ⟨w, z⟩
    rw [hcell]
    ring
  have hinnerSummable (w : Site) : Summable (fun z : Site =>
      ν w * (pointToPoint β a (b - a) w z ω * f z)) := by
    apply Summable.mul_left
    apply summable_of_ne_finset_zero (s := Polymer.endpoints w (b - a))
    intro z hz
    rw [Polymer.pointToPoint_eq_zero_of_not_mem β a (b - a) w z ω hz]
    simp
  have hprofileSum : profileP2Fun β a b ν f ω =
      ∑' q : Site × Site, ν q.1 *
        (pointToPoint β a (b - a) q.1 q.2 ω * f q.2) := by
    unfold profileP2Fun
    calc
      (∑' w : Site, ν w * ∑' z : Site,
          pointToPoint β a (b - a) w z ω * f z) =
        ∑' w : Site, ∑' z : Site,
          ν w * (pointToPoint β a (b - a) w z ω * f z) := by
            congr 1
            funext w
            rw [← tsum_mul_left]
      _ = ∑' q : Site × Site, ν q.1 *
          (pointToPoint β a (b - a) q.1 q.2 ω * f q.2) :=
            (hpairSummable.tsum_prod' hinnerSummable).symm
  calc
    truncatedHeatPairing ϑ N s t δ x h₀ K ω =
        ∫ p, (H p.1 * G p.2) * rescaledP2P ϑ N s t p ω := by
          rw [truncatedHeatPairing, SHF.Limit.integral_polymerMeasure]
    _ = ∑' q : Site × Site,
        ∫ p in C q, (H p.1 * G p.2) * rescaledP2P ϑ N s t p ω
          ∂(volume : Measure (Plane × Plane)) := hdecomp
    _ = ∑' q : Site × Site,
        ν q.1 * (pointToPoint β a (b - a) q.1 q.2 ω * f q.2) := by
          apply tsum_congr
          rintro ⟨w, z⟩
          rw [hcell]
          ring
    _ = profileP2Fun β a b ν f ω := hprofileSum.symm

/-- A finite-start profile with an arbitrary terminal weight is a finite path mass, with the
terminal value absorbed into each path coefficient. -/
theorem profileP2Fun_eq_finitePathMass_terminal (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0) (ω : Disorder) :
    profileP2Fun β a b ν f ω =
      PolymerCalculus.finitePathMass β a (b - a)
        (fun y : {w // w ∈ A} => y.1)
        (fun p : {w // w ∈ A} × (Fin (b - a) → Fin 4) =>
          ν p.1.1 * f (walkPosition p.1.1 p.2 (b - a)) * ((4 : ℝ)⁻¹ ^ (b - a))) ω := by
  classical
  let Starts := {w // w ∈ A}
  let w : Starts → Site := fun y => y.1
  let c : Starts × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * f (walkPosition p.1.1 p.2 (b - a)) * ((4 : ℝ)⁻¹ ^ (b - a))
  have hStart : (Finset.univ : Finset Starts) = A.attach := by
    ext y
    simp [Starts]
  rw [Polymer.profileP2Fun_eq_sum β a b ν f A hνA ω]
  calc
    (∑ y ∈ A, ν y * ∑' z, pointToPoint β a (b - a) y z ω * f z) =
        ∑ y ∈ A.attach, ν y.1 * ∑' z,
          pointToPoint β a (b - a) y.1 z ω * f z := by
            exact (Finset.sum_attach A
              (fun y => ν y * ∑' z, pointToPoint β a (b - a) y z ω * f z)).symm
    _ = ∑ y : Starts, ν y.1 * ∑' z,
          pointToPoint β a (b - a) y.1 z ω * f z := by rw [← hStart]
    _ = ∑ y : Starts, ν y.1 * ∑ s : Fin (b - a) → Fin 4,
          (4 : ℝ)⁻¹ ^ (b - a) * Polymer.pathWeight β a y.1 s ω *
            f (walkPosition y.1 s (b - a)) := by
              apply Finset.sum_congr rfl
              intro y hy
              rw [Polymer.tsum_pointToPoint_mul]
    _ = ∑ y : Starts, ∑ s : Fin (b - a) → Fin 4,
          c (y, s) * Real.exp (PolymerCalculus.pathEnergy β a y.1 s ω) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s hs
            dsimp [c]
            simp only [Polymer.pathWeight, PolymerCalculus.pathEnergy]
            ring
    _ = ∑ p : Starts × (Fin (b - a) → Fin 4),
          c p * Real.exp (PolymerCalculus.pathEnergy β a (w p.1) p.2 ω) := by
            rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = PolymerCalculus.finitePathMass β a (b - a) w c ω := rfl

/-- The truncated pairing is exactly a finite path mass; the finite start set is obtained from
the lattice cells meeting the cutoff ball. -/
theorem truncatedHeatPairing_eq_finitePathMass (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (hδ : 0 < δ) (x : Plane)
    (h₀ : Plane →ᵇ ℝ) (K : ℝ) (ω : Disorder) :
    truncatedHeatPairing ϑ N s t δ x h₀ K ω =
      PolymerCalculus.finitePathMass (criticalBeta ϑ N) (evenCeil (N * s))
        (evenCeil (N * t) - evenCeil (N * s))
        (fun y : {w // w ∈ truncatedHeatStartSites N K} => y.1)
        (fun p : {w // w ∈ truncatedHeatStartSites N K} ×
            (Fin (evenCeil (N * t) - evenCeil (N * s)) → Fin 4) =>
          (∫ y in cell N p.1.1, heatKernel δ (y - x) *
            Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) y) *
          cellAverage N (fun y => Real.exp (h₀ y))
            (walkPosition p.1.1 p.2 (evenCeil (N * t) - evenCeil (N * s))) *
          ((4 : ℝ)⁻¹ ^ (evenCeil (N * t) - evenCeil (N * s)))) ω := by
  classical
  let A := truncatedHeatStartSites N K
  let a := evenCeil (N * s)
  let b := evenCeil (N * t)
  let ν : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x) *
    Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) y
  let f : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
  have hInt := integrable_truncatedHeatPairing_integrand ϑ N s t δ x h₀ K ω hδ
  have hprofile := truncatedHeatPairing_eq_profile ϑ hN (s := s) (t := t) (δ := δ)
    x h₀ K ω hInt
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    exact truncatedHeatStartMass_eq_zero_of_not_mem N δ x K hw
  have hEq := profileP2Fun_eq_finitePathMass_terminal
    (criticalBeta ϑ N) a b ν f A hνA ω
  simpa only [A, a, b, ν, f] using hprofile.trans hEq

/-- A positive-radius truncated heat start has positive mass in at least one of its finitely
many lattice cells. -/
theorem exists_pos_truncatedHeatStartMass (N : ℕ) (δ : ℝ) (x : Plane) (K : ℝ)
    (hδ : 0 < δ) (hK : 0 < K) :
    ∃ w ∈ truncatedHeatStartSites N K,
      0 < ∫ y in cell N w, heatKernel δ (y - x) *
        Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) y := by
  classical
  let B : Set Plane := Metric.closedBall (0 : Plane) K
  let H : Plane → ℝ := fun y => heatKernel δ (y - x) *
    Set.indicator B (fun _ => (1 : ℝ)) y
  let A := truncatedHeatStartSites N K
  let ν : Site → ℝ := fun w => ∫ y in cell N w, H y
  have hH : H = B.indicator (fun y : Plane => heatKernel δ (y - x)) := by
    funext y
    by_cases hy : y ∈ B <;> simp [H, B, hy]
  have hHint : Integrable H := by
    rw [hH]
    exact ((Critical2DKPZ.integrable_heatKernel hδ).comp_sub_right x).indicator
      Metric.isClosed_closedBall.measurableSet
  have hHnonneg : ∀ y, 0 ≤ H y := by
    intro y
    by_cases hy : y ∈ B <;> simp [H, B, hy, Critical2DKPZ.heatKernel_nonneg hδ.le]
  have hsupport : Metric.ball (0 : Plane) K ⊆ Function.support H := by
    intro y hy
    rw [Function.mem_support]
    have hclosed : y ∈ B := Metric.ball_subset_closedBall hy
    rw [hH, Set.indicator_of_mem hclosed]
    exact (Critical2DKPZ.heatKernel_pos hδ (y - x)).ne'
  have hballpos : 0 < (volume : Measure Plane) (Metric.ball (0 : Plane) K) :=
    Metric.measure_ball_pos volume 0 hK
  have hsupportpos : 0 < (volume : Measure Plane) (Function.support H) :=
    lt_of_lt_of_le hballpos (measure_mono hsupport)
  have htotalpos : 0 < ∫ y, H y :=
    (integral_pos_iff_support_of_nonneg hHnonneg hHint).2 hsupportpos
  have hcover : ⋃ w : Site, cell N w = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact Set.mem_iUnion.mpr ⟨latticePoint N y, mem_cell_latticePoint N y⟩
  have hcellMeas : ∀ w : Site, MeasurableSet (cell N w) :=
    fun w => measurableSet_cell N w
  have hcellDisjoint : Pairwise (fun w z : Site => Disjoint (cell N w) (cell N z)) :=
    pairwise_disjoint_cell N
  have hhasSum : HasSum ν (∫ y, H y) := by
    have h := hasSum_integral_iUnion hcellMeas hcellDisjoint hHint.integrableOn
    simpa only [hcover, setIntegral_univ, ν] using h
  have hνA : ∀ w ∉ A, ν w = 0 := by
    intro w hw
    dsimp [ν, H, B]
    exact truncatedHeatStartMass_eq_zero_of_not_mem N δ x K hw
  have hsum : ∑ w ∈ A, ν w = ∫ y, H y := by
    calc
      ∑ w ∈ A, ν w = ∑' w, ν w := (tsum_eq_sum hνA).symm
      _ = ∫ y, H y := hhasSum.tsum_eq
  have hνnonneg : ∀ w, 0 ≤ ν w := by
    intro w
    dsimp [ν]
    exact setIntegral_nonneg (measurableSet_cell N w) (fun y hy => hHnonneg y)
  have hsumpos : 0 < ∑ w ∈ A, ν w := by rw [hsum]; exact htotalpos
  obtain ⟨w, hwA, hwpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun w hw => hνnonneg w)).mp hsumpos
  exact ⟨w, hwA, hwpos⟩

private def finiteMassCoordinateSet {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) : Finset (ℕ × Site) :=
  PolymerCalculus.finitePathCoordinates a n w

private def finiteMassCoordinateMap {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) : Fin (finiteMassCoordinateSet a n w).card → ℕ × Site :=
  fun i => ((finiteMassCoordinateSet a n w).equivFin.symm i).val

private def finiteMassCoordinateVector {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) (ω : Disorder) :
    EuclideanSpace ℝ (Fin (finiteMassCoordinateSet a n w).card) :=
  PolymerCalculus.disorderSliceCoordinates (finiteMassCoordinateMap a n w) ω

private def finiteMassCoordinateExtension {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) :
    EuclideanSpace ℝ (Fin (finiteMassCoordinateSet a n w).card) →ₗ[ℝ] Disorder where
  toFun x := fun p => if hp : p ∈ finiteMassCoordinateSet a n w then
    x ((finiteMassCoordinateSet a n w).equivFin ⟨p, hp⟩) else 0
  map_add' x y := by
    funext p
    by_cases hp : p ∈ finiteMassCoordinateSet a n w <;>
      simp [hp, Pi.add_apply]
  map_smul' c x := by
    funext p
    by_cases hp : p ∈ finiteMassCoordinateSet a n w <;>
      simp [hp, smul_eq_mul]

private theorem finiteMassCoordinateExtension_vector_eq {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) (ω : Disorder) (p : ℕ × Site)
    (hp : p ∈ finiteMassCoordinateSet a n w) :
    finiteMassCoordinateExtension a n w (finiteMassCoordinateVector a n w ω) p = ω p := by
  change (if h : p ∈ finiteMassCoordinateSet a n w then
    finiteMassCoordinateVector a n w ω ((finiteMassCoordinateSet a n w).equivFin ⟨p, h⟩)
      else 0) = ω p
  simp [hp, finiteMassCoordinateVector, PolymerCalculus.disorderSliceCoordinates,
    finiteMassCoordinateMap]

/-- A positive finite path mass has Ehrhard-type logarithmic law. The proof restricts the
disorder to the finite set of coordinates visited by its paths and applies the convex Gaussian image property. -/
theorem isEhrhardType_log_finitePathMass {ι : Type*} [Fintype ι]
    (β : ℝ) (a n : ℕ) (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hpos : ∃ p, 0 < c p) :
    IsEhrhardType (disorderLaw.map fun ω =>
      Real.log (PolymerCalculus.finitePathMass β a n w c ω)) := by
  classical
  let π := finiteMassCoordinateVector a n w
  let L := finiteMassCoordinateExtension a n w
  let F : Disorder → ℝ := fun ω =>
    Real.log (PolymerCalculus.finitePathMass β a n w c ω)
  let G : EuclideanSpace ℝ (Fin (finiteMassCoordinateSet a n w).card) → ℝ := fun x => F (L x)
  have hπlaw : HasLaw π
      (stdGaussian (EuclideanSpace ℝ (Fin (finiteMassCoordinateSet a n w).card))) disorderLaw := by
    have he : Function.Injective (finiteMassCoordinateMap a n w) := by
      intro i j hij
      have hsub : (finiteMassCoordinateSet a n w).equivFin.symm i =
          (finiteMassCoordinateSet a n w).equivFin.symm j := Subtype.ext hij
      exact (finiteMassCoordinateSet a n w).equivFin.symm.injective hsub
    change HasLaw (finiteMassCoordinateVector a n w)
      (stdGaussian (EuclideanSpace ℝ (Fin (finiteMassCoordinateSet a n w).card))) disorderLaw
    exact PolymerCalculus.hasLaw_disorderSliceCoordinates
      (finiteMassCoordinateMap a n w) he
  have hπmeas : Measurable π := by
    change Measurable (fun ω : Disorder =>
      WithLp.toLp 2 (fun i => ω (finiteMassCoordinateMap a n w i)))
    have hraw : Measurable (fun ω : Disorder =>
        fun i : Fin (finiteMassCoordinateSet a n w).card =>
          ω (finiteMassCoordinateMap a n w i)) :=
      measurable_pi_iff.mpr (fun i => Gaussian.measurable_disorder_eval
        (finiteMassCoordinateMap a n w i))
    have hto : Measurable (fun x : (Fin (finiteMassCoordinateSet a n w).card → ℝ) =>
        WithLp.toLp 2 x) := by fun_prop
    exact hto.comp hraw
  have hcoordEq (ω : Disorder) (p : ℕ × Site)
      (hp : p ∈ finiteMassCoordinateSet a n w) : L (π ω) p = ω p := by
    simpa only [L, π] using
      finiteMassCoordinateExtension_vector_eq a n w ω p hp
  have hdep : DependsOn
      (PolymerCalculus.finitePathMass β a n w c)
      (finiteMassCoordinateSet a n w : Set (ℕ × Site)) :=
    PolymerCalculus.dependsOn_finitePathMass β a n w c
  have hmassEq (ω : Disorder) :
      PolymerCalculus.finitePathMass β a n w c (L (π ω)) =
        PolymerCalculus.finitePathMass β a n w c ω :=
    hdep (fun p hp => hcoordEq ω p hp)
  have hFcomp : F = fun ω => G (π ω) := by
    funext ω
    dsimp [F, G]
    exact congrArg Real.log (hmassEq ω).symm
  have hconvDisorder : ConvexOn ℝ univ F := by
    simpa only [F] using
      PolymerCalculus.convexOn_log_finitePathMass β a n w hc hpos
  have hconvG : ConvexOn ℝ univ G := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ u v hu hv huv
    change F (L (u • x + v • y)) ≤ u * F (L x) + v * F (L y)
    have hlin : L (u • x + v • y) = u • L x + v • L y := by simp
    rw [hlin]
    exact hconvDisorder.2 (mem_univ _) (mem_univ _) hu hv huv
  have hLmeas : Measurable L := by
    apply measurable_pi_iff.mpr
    intro p
    dsimp [L, finiteMassCoordinateExtension]
    split_ifs <;> fun_prop
  have hGmeas : Measurable G := by
    exact (PolymerCalculus.measurable_log_finitePathMass β a n w c).comp hLmeas
  have hFmeas : Measurable F := by
    simpa only [F] using PolymerCalculus.measurable_log_finitePathMass β a n w c
  have hmeasure : disorderLaw.map F =
      (stdGaussian (EuclideanSpace ℝ (Fin (finiteMassCoordinateSet a n w).card))).map G := by
    rw [hFcomp]
    calc
      disorderLaw.map (fun ω => G (π ω)) = disorderLaw.map (G ∘ π) := rfl
      _ = (disorderLaw.map π).map G := (Measure.map_map hGmeas hπmeas).symm
      _ = (stdGaussian (EuclideanSpace ℝ (Fin (finiteMassCoordinateSet a n w).card))).map G := by
        rw [hπlaw.map_eq]
  rw [hmeasure]
  exact Provider.ehrhardType_convexGaussianImage _ G hconvG

/-- For all sufficiently large lattice scales, the logarithm of each positive-radius truncated heat-start polymer pairing has an Ehrhard-type law. -/
theorem isEhrhardType_log_truncatedHeatPairing (ϑ : ℝ) {s t δ : ℝ}
    (_hs : 0 ≤ s) (_hst : s < t) (hδ : 0 < δ) (x : Plane)
    (h₀ : Plane →ᵇ ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ K : ℝ, 0 < K →
      (∀ ω, 0 < truncatedHeatPairing ϑ N s t δ x h₀ K ω) ∧
      IsEhrhardType (disorderLaw.map fun ω =>
        Real.log (truncatedHeatPairing ϑ N s t δ x h₀ K ω)) := by
  filter_upwards [eventually_ge_atTop 1] with N hN K hK
  classical
  let A := truncatedHeatStartSites N K
  let a := evenCeil (N * s)
  let b := evenCeil (N * t)
  let n := b - a
  let β := criticalBeta ϑ N
  let ν : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x) *
    Set.indicator (Metric.closedBall (0 : Plane) K) (fun _ => (1 : ℝ)) y
  let f : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
  let Starts := {w // w ∈ A}
  let wfun : Starts → Site := fun y => y.1
  let c : Starts × (Fin n → Fin 4) → ℝ := fun p =>
    ν p.1.1 * f (walkPosition p.1.1 p.2 n) * ((4 : ℝ)⁻¹ ^ n)
  have hnEven : Even n := by
    obtain ⟨u, hu⟩ := evenCeil_even (N * s)
    obtain ⟨v, hv⟩ := evenCeil_even (N * t)
    have ha : a = u + u := by simpa [a] using hu
    have hb : b = v + v := by simpa [b] using hv
    refine ⟨v - u, ?_⟩
    dsimp [n]
    omega
  have hνnonneg : ∀ z, 0 ≤ ν z := by
    intro z
    dsimp [ν]
    apply setIntegral_nonneg (measurableSet_cell N z)
    intro y hy
    by_cases hball : y ∈ Metric.closedBall (0 : Plane) K
    · simp [hball, Critical2DKPZ.heatKernel_nonneg hδ.le]
    · simp [hball]
  have hνpos := exists_pos_truncatedHeatStartMass N δ x K hδ hK
  have hfnonneg : ∀ z, 0 ≤ f z := by
    intro z
    by_cases hz : z ∈ evenLattice
    · exact (Smoothing.cellAverage_exp_bounds_of_even N hN h₀ hz).1.le
    · dsimp [f, cellAverage]
      rw [cell_eq_empty_of_not_even hz]
      simp
  have hc : ∀ p, 0 ≤ c p := by
    intro p
    dsimp [c]
    exact mul_nonneg (mul_nonneg (hνnonneg _) (hfnonneg _)) (by positivity)
  have hpos : ∃ p, 0 < c p := by
    obtain ⟨z, hzA, hzpos⟩ := hνpos
    have hzEven : z ∈ evenLattice := by
      by_contra hzNot
      have hzero : ν z = 0 := by
        dsimp [ν]
        rw [cell_eq_empty_of_not_even hzNot]
        simp
      linarith
    have hzEven' : Even (z 0 + z 1) := hzEven
    let path : Fin n → Fin 4 := fun _ => 0
    let endSite := walkPosition z path n
    have hendEven : endSite ∈ evenLattice := by
      change Even (endSite 0 + endSite 1)
      have hnZ : Even (n : ℤ) := by exact_mod_cast hnEven
      have hsumEven : Even (z 0 + z 1 + (n : ℤ)) := by
        simp [Int.even_add, hzEven', hnZ]
      have hsumMod : Int.ModEq 2 (z 0 + z 1 + (n : ℤ)) 0 := by
        change (z 0 + z 1 + (n : ℤ)) % 2 = 0
        exact Int.even_iff.mp hsumEven
      have hmod := (Polymer.walkPosition_parity z path).trans hsumMod
      have hmodEq : (endSite 0 + endSite 1) % 2 = 0 := hmod
      exact Int.even_iff.mpr hmodEq
    have hfpos : 0 < f endSite := by
      exact (Smoothing.cellAverage_exp_bounds_of_even N hN h₀ hendEven).1
    refine ⟨(⟨z, hzA⟩, path), ?_⟩
    dsimp [c, path, endSite]
    exact mul_pos (mul_pos hzpos hfpos) (by positivity)
  have hmass (ω : Disorder) := truncatedHeatPairing_eq_finitePathMass ϑ hN
    (s := s) (t := t) (δ := δ) hδ x h₀ K ω
  have hfinitePos : ∀ ω, 0 < PolymerCalculus.finitePathMass β a n wfun c ω := by
    intro ω
    exact PolymerCalculus.finitePathMass_pos β a n wfun hc hpos ω
  have hEq (ω : Disorder) : truncatedHeatPairing ϑ N s t δ x h₀ K ω =
      PolymerCalculus.finitePathMass β a n wfun c ω := by
    simpa only [A, a, b, n, β, Starts, wfun, c, ν, f] using hmass ω
  have hposPair : ∀ ω, 0 < truncatedHeatPairing ϑ N s t δ x h₀ K ω := by
    intro ω
    rw [hEq]
    exact hfinitePos ω
  have htype := isEhrhardType_log_finitePathMass β a n wfun hc hpos
  have hlogEq : (fun ω => Real.log (truncatedHeatPairing ϑ N s t δ x h₀ K ω)) =
      (fun ω => Real.log (PolymerCalculus.finitePathMass β a n wfun c ω)) := by
    funext ω
    rw [hEq]
  rw [hlogEq]
  exact ⟨hposPair, htype⟩

end Critical2DKPZ.SHF.Positivity

end
