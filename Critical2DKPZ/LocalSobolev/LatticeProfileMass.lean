/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeMass
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Definitions.CellAverage
import Mathlib.Tactic

/-! # Weighted lattice masses and cell averages -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

/-- Integrating a weighted lattice kernel gives a sum over cell averages, supported on the finite endpoint set of its finite-time walks. -/
theorem integral_rescaledP2P_profile_eq_tsum (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (t : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ) (ω : Disorder)
    (htime : Even (evenCeil ((N : ℝ) * t))) :
    (∫ y : Plane, Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω) =
      ∑' z : Site, cellAverage N (fun y => Real.exp (h₀ y)) z *
        pointToPoint (criticalBeta ϑ N) 0 (evenCeil ((N : ℝ) * t)) z
          (latticePoint N x) ω := by
  classical
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
      exact eq_sub_iff_add_eq.mp h
  have hpathFun (y : Plane) :
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
  have hExpMeas : Measurable (fun y : Plane => Real.exp (h₀ y)) :=
    Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hExpBound (y : Plane) :
      ‖Real.exp (h₀ y)‖ ≤ Real.exp ‖h₀‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (le_trans (le_abs_self (h₀ y)) (h₀.norm_coe_le_norm y))
  have hExpInt (z : Site) (hz : z ∈ evenLattice) :
      IntegrableOn (fun y : Plane => Real.exp (h₀ y)) (cell N z) volume := by
    apply Measure.integrableOn_of_bounded (μ := volume) (s := cell N z)
    · exact (volume_cell_lt_top hN hz).ne
    · exact hExpMeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_cell N z)] with y hy
      exact hExpBound y
  have htermInt (s : Fin n → Fin 4) : Integrable
      (fun y : Plane => Real.exp (h₀ y) * (cell N (start s)).indicator
        (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
          Polymer.pathWeight β 0 (start s) s ω) y) volume := by
    have hcell := (hExpInt (start s) (hstartEven s)).const_mul
      (((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) * Polymer.pathWeight β 0 (start s) s ω)
    have hEq : (fun y : Plane => Real.exp (h₀ y) * (cell N (start s)).indicator
        (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
          Polymer.pathWeight β 0 (start s) s ω) y) =
        (cell N (start s)).indicator (fun y =>
          (((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
            Polymer.pathWeight β 0 (start s) s ω) * Real.exp (h₀ y)) := by
      funext y
      by_cases hy : y ∈ cell N (start s)
      · simp [Set.indicator, hy]
        ring
      · simp [Set.indicator, hy]
    rw [hEq]
    exact IntegrableOn.integrable_indicator hcell (measurableSet_cell N (start s))
  have hsumInt : Integrable (fun y : Plane => ∑ s : Fin n → Fin 4,
      Real.exp (h₀ y) * (cell N (start s)).indicator
        (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
          Polymer.pathWeight β 0 (start s) s ω) y) volume :=
    integrable_finsetSum _ fun s hs => htermInt s
  have hsumIntEq :
      (∫ y : Plane, ∑ s : Fin n → Fin 4, Real.exp (h₀ y) *
        (cell N (start s)).indicator
          (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
            Polymer.pathWeight β 0 (start s) s ω) y) =
        ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (start s) s ω *
          cellAverage N (fun y => Real.exp (h₀ y)) (start s) := by
    rw [integral_finsetSum _ (fun s hs => htermInt s)]
    apply Finset.sum_congr rfl
    intro s hs
    have hEq : (fun y : Plane => Real.exp (h₀ y) * (cell N (start s)).indicator
        (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
          Polymer.pathWeight β 0 (start s) s ω) y) =
        (cell N (start s)).indicator (fun y =>
          (((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
            Polymer.pathWeight β 0 (start s) s ω) * Real.exp (h₀ y)) := by
      funext y
      by_cases hy : y ∈ cell N (start s)
      · simp [Set.indicator, hy]
        ring
      · simp [Set.indicator, hy]
    rw [hEq, integral_indicator (measurableSet_cell N (start s))]
    rw [integral_const_mul]
    dsimp [cellAverage]
    rw [volume_cell_toReal hN (hstartEven s)]
    have hNreal : (N : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hN)
    field_simp [hNreal]
  have hpointwise (y : Plane) :
      Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω =
        ∑ s : Fin n → Fin 4, Real.exp (h₀ y) * (cell N (start s)).indicator
          (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
            Polymer.pathWeight β 0 (start s) s ω) y := by
    rw [rescaledP2P]
    simp only [show evenCeil (N * 0) = 0 by simp [evenCeil], Nat.sub_zero]
    calc
      _ = Real.exp (h₀ y) * (((N : ℝ) / 4) * pointToPoint β 0 n
          (latticePoint N y) x₀ ω) := by rfl
      _ = Real.exp (h₀ y) *
          (∑ s : Fin n → Fin 4, (cell N (start s)).indicator
            (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
              Polymer.pathWeight β 0 (start s) s ω) y) := by
            congr 1
            simpa only [n, β, x₀] using hpathFun y
      _ = _ := by rw [Finset.mul_sum]
  have hleftInt : Integrable
      (fun y : Plane => Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω) volume := by
    rw [show (fun y : Plane => Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω) =
        fun y => ∑ s : Fin n → Fin 4, Real.exp (h₀ y) * (cell N (start s)).indicator
          (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
            Polymer.pathWeight β 0 (start s) s ω) y by
      funext y
      exact hpointwise y]
    exact hsumInt
  have hleftEq :
      (∫ y : Plane, Real.exp (h₀ y) * rescaledP2P ϑ N 0 t (y, x) ω) =
        ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β 0 (start s) s ω *
          cellAverage N (fun y => Real.exp (h₀ y)) (start s) := by
    calc
      _ = ∫ y : Plane, ∑ s : Fin n → Fin 4, Real.exp (h₀ y) *
          (cell N (start s)).indicator
            (fun _ : Plane => ((N : ℝ) / 4) * ((4 : ℝ)⁻¹ ^ n) *
              Polymer.pathWeight β 0 (start s) s ω) y := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall hpointwise
      _ = _ := hsumIntEq
  let A : Finset Site := Finset.univ.image start
  have hzero (z : Site) (hz : z ∉ A) :
      pointToPoint β 0 n z x₀ ω = 0 := by
    rw [Polymer.pointToPoint_eq_sum]
    apply Finset.sum_eq_zero
    intro s hs
    have hne : walkPosition z s n ≠ x₀ := by
      intro heq
      have hzEq : z = start s := by
        rw [Polymer.walkPosition_eq_start_add] at heq
        exact (eq_sub_iff_add_eq).2 heq
      exact hz (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hzEq.symm⟩)
    simp [hne]
  have hpathTsum :
      (∑' z : Site, cellAverage N (fun y => Real.exp (h₀ y)) z *
        pointToPoint β 0 n z x₀ ω) =
        ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
          Polymer.pathWeight β 0 (start s) s ω *
            cellAverage N (fun y => Real.exp (h₀ y)) (start s) := by
    rw [tsum_eq_sum (fun z hz => by rw [hzero z hz, mul_zero])]
    simp_rw [Polymer.pointToPoint_eq_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.sum_eq_single (start s)]
    · simp only [hstart, ite_true]
      ring
    · intro z hz hzne
      have hne : walkPosition z s n ≠ x₀ := by
        intro heq
        have hzEq : z = start s := by
          rw [Polymer.walkPosition_eq_start_add] at heq
          exact (eq_sub_iff_add_eq).2 heq
        exact hzne hzEq
      simp [hne]
    · intro hnot
      exact (hnot (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩)).elim
  calc
    _ = ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n *
        Polymer.pathWeight β 0 (start s) s ω *
          cellAverage N (fun y => Real.exp (h₀ y)) (start s) := hleftEq
    _ = ∑' z : Site, cellAverage N (fun y => Real.exp (h₀ y)) z *
        pointToPoint β 0 n z x₀ ω := hpathTsum.symm

end Critical2DKPZ.LocalSobolev

end

