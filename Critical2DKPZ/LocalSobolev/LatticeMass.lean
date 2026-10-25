/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.TimeReversalMass
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Definitions.KpzLattice
public import Critical2DKPZ.Definitions.RescaledP2P
public import Critical2DKPZ.Polymer.ProfileCovariance
public import Critical2DKPZ.Smoothing.EndpointDistribution
public import Critical2DKPZ.PolymerCalculus.PathAssociation
import Mathlib.Tactic

/-! # Spatial integrals of flat lattice polymer masses -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.LocalSobolev

/-- The site `x - walkPosition 0 s n`: the start of the `n`-step path `s` that ends at `x`. -/
def flatMassPathStart {n : ℕ} (x : Site) (s : Fin n → Fin 4) : Site :=
  x - walkPosition 0 s n

/-- The coefficient of a pair of step sequences: `(1/4)^n` if they coincide, and `0` otherwise. -/
def flatMassPathCoeff {n : ℕ} (p : (Fin n → Fin 4) × (Fin n → Fin 4)) : ℝ :=
  if p.1 = p.2 then (4 : ℝ)⁻¹ ^ n else 0

/-- Integrating a flat rescaled point-to-point density over its starting coordinate gives the
discrete flat mass at the fixed terminal site. -/
theorem integral_rescaledP2P_flat_eq_tsum (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (t : ℝ) (x : Plane) (ω : Disorder)
    (htime : Even (evenCeil ((N : ℝ) * t))) :
    (∫ y : Plane, rescaledP2P ϑ N 0 t (y, x) ω) =
      ∑' z : Site, pointToPoint (criticalBeta ϑ N) 0
        (evenCeil ((N : ℝ) * t)) z (latticePoint N x) ω := by
  let n : ℕ := evenCeil ((N : ℝ) * t)
  let β : ℝ := criticalBeta ϑ N
  let x₀ : Site := latticePoint N x
  let start (s : Fin n → Fin 4) : Site := x₀ - walkPosition 0 s n
  have hn : Even n := by simpa [n] using htime
  have hx₀ : x₀ ∈ evenLattice := by
    dsimp [x₀]
    exact latticePoint_mem_evenLattice N x
  have hstart (s : Fin n → Fin 4) : walkPosition (start s) s n = x₀ := by
    rw [Polymer.walkPosition_eq_start_add]
    dsimp [start]
    simp
  have hstartEven (s : Fin n → Fin 4) : start s ∈ evenLattice := by
    have hend : Even (start s 0 + start s 1 + (n : ℤ)) :=
      (walkPosition_parity (start s) s).mpr (by rw [hstart s]; exact hx₀)
    have hnInt : Even (n : ℤ) := by exact_mod_cast hn
    rw [Int.even_add] at hend
    exact hend.mpr hnInt
  have hcond (s : Fin n → Fin 4) (y : Plane) :
      walkPosition (latticePoint N y) s n = x₀ ↔ y ∈ cell N (start s) := by
    rw [Polymer.walkPosition_eq_start_add, mem_cell_iff]
    dsimp [start]
    constructor
    · intro h
      apply eq_sub_iff_add_eq.mpr
      exact h
    · intro h
      exact (eq_sub_iff_add_eq.mp h)
  have hpath :
      (∑' z : Site, pointToPoint β 0 n z x₀ ω) =
        ∑ s : Fin n → Fin 4,
          (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (start s) s ω := by
    classical
    let A : Finset Site := Finset.univ.image start
    have hstartMem (s : Fin n → Fin 4) : start s ∈ A :=
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    have hzero (z : Site) (hz : z ∉ A) : pointToPoint β 0 n z x₀ ω = 0 := by
      rw [Polymer.pointToPoint_eq_sum]
      apply Finset.sum_eq_zero
      intro s hs
      have hne : walkPosition z s n ≠ x₀ := by
        intro heq
        have hzEq : z = start s := by
          rw [Polymer.walkPosition_eq_start_add] at heq
          exact (eq_sub_iff_add_eq).2 heq
        exact hz (hzEq ▸ hstartMem s)
      simp [hne]
    rw [tsum_eq_sum hzero]
    simp_rw [Polymer.pointToPoint_eq_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_eq_single (start s)]
    · simp [hstart s]
    · intro z hz hzne
      have hne : walkPosition z s n ≠ x₀ := by
        intro heq
        have hzEq : z = start s := by
          rw [Polymer.walkPosition_eq_start_add] at heq
          exact (eq_sub_iff_add_eq).2 heq
        exact hzne hzEq
      simp [hne]
    · intro hnot
      exact (hnot (hstartMem s)).elim
  have hfun (y : Plane) :
      ((N : ℝ) / 4) * pointToPoint β 0 n (latticePoint N y) x₀ ω =
        ∑ s : Fin n → Fin 4,
          (cell N (start s)).indicator
            (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
              Polymer.pathWeight β 0 (start s) s ω) y := by
    rw [Polymer.pointToPoint_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hc := hcond s y
    by_cases h : walkPosition (latticePoint N y) s n = x₀
    · have hy : y ∈ cell N (start s) := hc.mp h
      have hpos : latticePoint N y = start s := (mem_cell_iff N (start s) y).mp hy
      rw [hpos]
      simp [Set.indicator, hy, hstart s]
      ring
    · have hy : y ∉ cell N (start s) := fun hy => h (hc.mpr hy)
      simp [Set.indicator, h, hy]
  have hInt (s : Fin n → Fin 4) : Integrable
      (fun y : Plane => (cell N (start s)).indicator
        (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
          Polymer.pathWeight β 0 (start s) s ω) y) volume := by
    exact (integrableOn_const
      (volume_cell_lt_top hN (hstartEven s)).ne).integrable_indicator
        (measurableSet_cell N (start s))
  have hint : Integrable
      (fun y : Plane => ∑ s : Fin n → Fin 4,
        (cell N (start s)).indicator
          (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
            Polymer.pathWeight β 0 (start s) s ω) y) volume :=
    integrable_finsetSum _ (fun s hs => hInt s)
  have hIntegral :
      (∫ y : Plane, ((N : ℝ) / 4) * pointToPoint β 0 n
        (latticePoint N y) x₀ ω) =
        ∑ s : Fin n → Fin 4,
          (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (start s) s ω := by
    calc
      _ = ∫ y : Plane, ∑ s : Fin n → Fin 4,
          (cell N (start s)).indicator
            (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
              Polymer.pathWeight β 0 (start s) s ω) y := by
                apply integral_congr_ae
                filter_upwards [] with y
                exact hfun y
      _ = ∑ s : Fin n → Fin 4,
          ∫ y : Plane, (cell N (start s)).indicator
            (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
              Polymer.pathWeight β 0 (start s) s ω) y :=
            integral_finsetSum _ (fun s hs => hInt s)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [integral_indicator_const _ (measurableSet_cell N (start s)), measureReal_def,
          volume_cell_toReal hN (hstartEven s), smul_eq_mul]
        field_simp [ne_of_gt (Nat.cast_pos.mpr hN)]
  calc
    (∫ y : Plane, rescaledP2P ϑ N 0 t (y, x) ω) =
        ∫ y : Plane, ((N : ℝ) / 4) * pointToPoint β 0 n
          (latticePoint N y) x₀ ω := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [rescaledP2P]
            rw [show evenCeil ((N : ℝ) * 0) = 0 by simp [evenCeil], Nat.sub_zero]
    _ = ∑ s : Fin n → Fin 4,
          (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (start s) s ω := hIntegral
    _ = ∑' z : Site, pointToPoint β 0 n z x₀ ω := hpath.symm

/-- The spatially integrated flat lattice kernel is a finite positive path mass.  The first
path index records the starting site determined by reversing the second path. -/
theorem integral_rescaledP2P_flat_eq_finitePathMass (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (t : ℝ) (x : Plane) (ω : Disorder)
    (htime : Even (evenCeil ((N : ℝ) * t))) :
    (∫ y : Plane, rescaledP2P ϑ N 0 t (y, x) ω) =
      PolymerCalculus.finitePathMass (criticalBeta ϑ N) 0
        (evenCeil ((N : ℝ) * t))
        (flatMassPathStart (latticePoint N x)) flatMassPathCoeff ω := by
  classical
  let n : ℕ := evenCeil ((N : ℝ) * t)
  let β : ℝ := criticalBeta ϑ N
  let x₀ : Site := latticePoint N x
  let start (s : Fin n → Fin 4) : Site := x₀ - walkPosition 0 s n
  have hstart (s : Fin n → Fin 4) : walkPosition (start s) s n = x₀ := by
    rw [Polymer.walkPosition_eq_start_add]
    dsimp [start]
    simp
  have hmass := integral_rescaledP2P_flat_eq_tsum ϑ hN t x ω htime
  have hpath :
      (∑' z : Site, pointToPoint β 0 n z x₀ ω) =
        ∑ s : Fin n → Fin 4,
          (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (start s) s ω := by
    let A : Finset Site := Finset.univ.image start
    have hstartMem (s : Fin n → Fin 4) : start s ∈ A :=
      Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩
    have hzero (z : Site) (hz : z ∉ A) : pointToPoint β 0 n z x₀ ω = 0 := by
      rw [Polymer.pointToPoint_eq_sum]
      apply Finset.sum_eq_zero
      intro s hs
      have hne : walkPosition z s n ≠ x₀ := by
        intro heq
        have hzEq : z = start s := by
          rw [Polymer.walkPosition_eq_start_add] at heq
          exact (eq_sub_iff_add_eq).2 heq
        exact hz (hzEq ▸ hstartMem s)
      simp [hne]
    rw [tsum_eq_sum hzero]
    simp_rw [Polymer.pointToPoint_eq_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_eq_single (start s)]
    · simp only [hstart, ite_true, mul_one]
    · intro z hz hzne
      have hne : walkPosition z s n ≠ x₀ := by
        intro heq
        have hzEq : z = start s := by
          rw [Polymer.walkPosition_eq_start_add] at heq
          exact (eq_sub_iff_add_eq).2 heq
        exact hzne hzEq
      simp [hne]
    · intro hnot
      exact (hnot (hstartMem s)).elim
  have hpathMass :
      (∑ s : Fin n → Fin 4,
          (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (start s) s ω) =
        PolymerCalculus.finitePathMass β 0 n (flatMassPathStart x₀) flatMassPathCoeff ω := by
    unfold PolymerCalculus.finitePathMass flatMassPathCoeff
    rw [Fintype.sum_prod_type]
    simp only [flatMassPathStart]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_eq_single s]
    · simp only [ite_true]
      simp [PolymerCalculus.pathEnergy, Polymer.pathWeight, start]
    · intro t ht hne
      have hst : s ≠ t := fun h => hne h.symm
      simp [hst]
    · intro hnot
      exact (hnot (Finset.mem_univ s)).elim
  calc
    _ = ∑' z : Site, pointToPoint β 0 n z x₀ ω := hmass
    _ = ∑ s : Fin n → Fin 4,
          (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (start s) s ω := hpath
    _ = PolymerCalculus.finitePathMass β 0 n (flatMassPathStart x₀)
          flatMassPathCoeff ω := hpathMass

/-- The flat lattice logarithm is an odd-horizon point-to-plane logarithm under time reversal,
plus the independent terminal Gaussian factor. -/
theorem kpzLattice_flat_log_eq_timeReversedPlane (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (t : ℝ) (x : Plane) (ω : Disorder) (hn : 1 ≤ evenCeil ((N : ℝ) * t)) :
    kpzLattice ϑ N t 0 x ω =
      Real.log (pointToPlane (criticalBeta ϑ N) 0
        (evenCeil ((N : ℝ) * t) - 1) (latticePoint N x)
        (PolymerCalculus.reversedDisorder (evenCeil ((N : ℝ) * t)) ω)) +
        (criticalBeta ϑ N) * ω (evenCeil ((N : ℝ) * t), latticePoint N x) -
          (criticalBeta ϑ N) ^ 2 / 2 - kpzLatticeCentring ϑ N t := by
  let n : ℕ := evenCeil ((N : ℝ) * t)
  have hnEven : Even n := by
    refine ⟨⌈((N : ℝ) * t) / 2⌉₊, ?_⟩
    simp [n, evenCeil, two_mul]
  have hmass := integral_rescaledP2P_flat_eq_tsum ϑ hN t x ω hnEven
  have hrev := tsum_pointToPoint_start_time_reversal (criticalBeta ϑ N) hn
    (latticePoint N x) ω
  unfold kpzLattice
  have hzero (y : Plane) :
      Real.exp ((0 : BoundedContinuousFunction Plane ℝ) y) = 1 := by simp
  simp_rw [hzero, one_mul]
  rw [hmass, hrev]
  have hplane : 0 < pointToPlane (criticalBeta ϑ N) 0 (n - 1)
      (latticePoint N x) (PolymerCalculus.reversedDisorder n ω) :=
    Polymer.pointToPlane_pos _ _ _ _ _
  rw [Real.log_mul (Real.exp_pos _).ne' hplane.ne', Real.log_exp]
  dsimp [n]
  ring

/-- Adding one disorder layer to a point-to-plane mass multiplies it by the one-step polymer
profile averaged against its random endpoint distribution. -/
theorem pointToPlane_succ_eq_mul_endpointProfile (β : ℝ) (n : ℕ) (x : Site)
    (ω : Disorder) :
    pointToPlane β 0 (n + 1) x ω =
      pointToPlane β 0 n x ω *
        profileP2Fun β n (n + 1) (endpointDist β n x ω) (fun _ => 1) ω := by
  classical
  let A : Finset Site := Polymer.endpoints x n
  let M : ℝ := pointToPlane β 0 n x ω
  have hM : 0 < M := Polymer.pointToPlane_pos β 0 n x ω
  have hsupp : ∀ z ∉ A, endpointDist β n x ω z = 0 := by
    intro z hz
    exact (Smoothing.endpointDist_probability β n x ω).1 z (by simpa [A] using hz)
  have hprofile := Polymer.profileP2Fun_flat_eq_sum β n 1
    (endpointDist β n x ω) A hsupp ω
  have hCK := Polymer.pointToPlane_chapmanKolmogorov β 0 n 1 x ω
  have hsum : M * profileP2Fun β n (n + 1) (endpointDist β n x ω)
      (fun _ => 1) ω = pointToPlane β 0 (n + 1) x ω := by
    rw [hprofile, Finset.mul_sum]
    calc
      _ = ∑ z ∈ A, (M * endpointDist β n x ω z) *
          pointToPlane β n 1 z ω := by
            apply Finset.sum_congr rfl
            intro z hz
            ring
      _ = ∑ z ∈ A, pointToPoint β 0 n x z ω * pointToPlane β n 1 z ω := by
            apply Finset.sum_congr rfl
            intro z hz
            have hzM : M * endpointDist β n x ω z =
                pointToPoint β 0 n x z ω := by
              dsimp only [M, endpointDist]
              field_simp [ne_of_gt (Polymer.pointToPlane_pos β 0 n x ω)]
            rw [hzM]
      _ = ∑' z, pointToPoint β 0 n x z ω * pointToPlane β n 1 z ω := by
            symm
            apply tsum_eq_sum
            intro z hz
            rw [Polymer.pointToPoint_eq_zero_of_not_mem β 0 n x z ω
              (by simpa [A] using hz)]
            simp
      _ = pointToPlane β 0 (n + 1) x ω := by simpa only [Nat.zero_add] using hCK.symm
  simpa only [M] using hsum.symm

end Critical2DKPZ.LocalSobolev

end
