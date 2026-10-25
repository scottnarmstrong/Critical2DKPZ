/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Analysis.Lattice.Volume
import Mathlib.Tactic

/-! # Parity and cell-average bounds for lattice smoothing -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

open Critical2DKPZ.Polymer

private theorem no_modEq_of_even_odd {x n y : ℤ} (hx : Even x) (hn : Even n)
    (hy : ¬ Even y) : ¬ Int.ModEq 2 y (x + n) := by
  intro h
  change y % 2 = (x + n) % 2 at h
  have he : Even (x + n) := by simp [Int.even_add, hx, hn]
  apply hy
  apply Int.even_iff.mpr
  rw [h]
  exact Int.even_iff.mp he

private theorem even_walkPosition {n : ℕ} (w : Site) (hw : Even (w 0 + w 1))
    (hn : Even n) (s : Fin n → Fin 4) :
    Even (walkPosition w s n 0 + walkPosition w s n 1) := by
  have hmod := Polymer.walkPosition_parity w s
  change (walkPosition w s n 0 + walkPosition w s n 1) % 2 =
    (w 0 + w 1 + n) % 2 at hmod
  have hrhs : Even (w 0 + w 1 + n) := by
    simp [Int.even_add, hw, Int.even_coe_nat, hn]
  apply Int.even_iff.mpr
  rw [hmod]
  exact Int.even_iff.mp hrhs

/-- Endpoints of an even-length walk from the even lattice remain on the even lattice. -/
theorem even_endpoint_of_mem {m : ℕ} {z w : Site} (hz : Even (z 0 + z 1))
    (hm : Even m) (hw : w ∈ Polymer.endpoints z m) : Even (w 0 + w 1) := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff z w m).mp hw
  rw [← hs]
  exact even_walkPosition z hz hm s

private theorem pointToPoint_eq_zero_of_even_start_odd_end (β : ℝ) (a n : ℕ)
    (z w : Site) (ω : Disorder) (hz : Even (z 0 + z 1)) (hn : Even n)
    (hw : ¬ Even (w 0 + w 1)) : pointToPoint β a n z w ω = 0 := by
  apply Polymer.pointToPoint_eq_zero_of_parity
  exact no_modEq_of_even_odd hz (by exact_mod_cast hn) hw

/-- A profile on the even lattice, after an even number of steps, only sees the weight on the even lattice. -/
theorem profileP2Fun_congr_of_even (β : ℝ) {a b : ℕ} (hab : a ≤ b) (hev : Even (b - a))
    (ν f g : Site → ℝ) (hν : ∀ w, ν w ≠ 0 → Even (w 0 + w 1))
    (hfg : ∀ z, Even (z 0 + z 1) → f z = g z) (ω : Disorder) :
    profileP2Fun β a b ν f ω = profileP2Fun β a b ν g ω := by
  have _ : a ≤ b := hab
  have hinner (w : Site) (hw : ν w ≠ 0) :
      (∑' z, pointToPoint β a (b - a) w z ω * f z) =
        ∑' z, pointToPoint β a (b - a) w z ω * g z := by
    rw [Polymer.tsum_pointToPoint_mul, Polymer.tsum_pointToPoint_mul]
    apply Finset.sum_congr rfl
    intro s hs
    have hz := even_walkPosition w (hν w hw) hev s
    rw [hfg _ hz]
  unfold profileP2Fun
  apply tsum_congr
  intro w
  by_cases hw : ν w = 0
  · simp [hw]
  · rw [hinner w hw]

/-- An even-time endpoint law from an even site vanishes at odd sites. -/
theorem endpointDist_eq_zero_of_odd (β : ℝ) {n : ℕ} (hn : Even n) {z : Site}
    (hz : Even (z 0 + z 1)) (ω : Disorder) {w : Site}
    (hw : ¬ Even (w 0 + w 1)) : endpointDist β n z ω w = 0 := by
  simp [endpointDist,
    pointToPoint_eq_zero_of_even_start_odd_end β 0 n z w ω hz hn hw]

/-- The smoothed endpoint law from an even site at even clocks vanishes at odd sites. -/
theorem smoothedEndpointDist_eq_zero_of_odd (β : ℝ) {m n : ℕ} (hm : Even m)
    (hn : Even n) (hmn : m ≤ n) {z : Site} (hz : Even (z 0 + z 1)) (ω : Disorder)
    {w : Site} (hw : ¬ Even (w 0 + w 1)) :
    smoothedEndpointDist β m n z ω w = 0 := by
  have hnum : (∑' y : Site, srwKernel m (y - z) * pointToPoint β m (n - m) y w ω) = 0 := by
    have hterm : ∀ y : Site,
        srwKernel m (y - z) * pointToPoint β m (n - m) y w ω = 0 := by
      intro y
      by_cases hq : srwKernel m (y - z) = 0
      · simp [hq]
      · have hy : y ∈ Polymer.endpoints z m := by
          by_contra hy
          exact hq (Polymer.srwKernel_eq_zero_of_not_mem m z y hy)
        have hyEven := even_endpoint_of_mem hz hm hy
        have hnm : Even (n - m) := by
          exact (Nat.even_sub hmn).2 ⟨fun _ => hm, fun _ => hn⟩
        simp [pointToPoint_eq_zero_of_even_start_odd_end β m (n - m) y w ω hyEven hnm hw]
    simp_rw [hterm]
    simp
  simp [smoothedEndpointDist, hnum]

/-- On the even lattice the cell average of `e^{h₀}` lies in `[e^{−‖h₀‖}, e^{‖h₀‖}]`. -/
theorem cellAverage_exp_bounds_of_even (N : ℕ) (hN : 1 ≤ N) (h₀ : Plane →ᵇ ℝ) {z : Site}
    (hz : Even (z 0 + z 1)) :
    0 < cellAverage N (fun y => Real.exp (h₀ y)) z ∧
      |Real.log (cellAverage N (fun y => Real.exp (h₀ y)) z)| ≤ ‖h₀‖ := by
  let C : Set Plane := cell N z
  have hNpos : 0 < N := by omega
  have hzmem : z ∈ evenLattice := hz
  have hvol := volume_cell_toReal hNpos hzmem
  have hvolTop := volume_cell_lt_top hNpos hzmem
  have hvolpos : 0 < (volume C).toReal := by rw [volume_cell_toReal hNpos hzmem]; positivity
  have hmeas : Measurable (fun y : Plane => Real.exp (h₀ y)) :=
    Real.continuous_exp.measurable.comp h₀.continuous.measurable
  have hmajor : IntegrableOn (fun _ : Plane => Real.exp ‖h₀‖) C :=
    integrableOn_const hvolTop.ne
  have hint : IntegrableOn (fun y : Plane => Real.exp (h₀ y)) C := by
    refine hmajor.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (le_trans (abs_le.mp (h₀.norm_coe_le_norm y)).2 le_rfl)
  have hlow : Real.exp (-‖h₀‖) * (volume C).toReal ≤
      ∫ y in C, Real.exp (h₀ y) := by
    calc
      Real.exp (-‖h₀‖) * (volume C).toReal = ∫ y in C, Real.exp (-‖h₀‖) := by
        rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
      _ ≤ ∫ y in C, Real.exp (h₀ y) := by
        apply setIntegral_mono_on
          (integrableOn_const (C := Real.exp (-‖h₀‖)) hvolTop.ne) hint
          (measurableSet_cell N z)
        intro y hy
        exact Real.exp_le_exp.mpr ((abs_le.mp (h₀.norm_coe_le_norm y)).1)
  have hupp : ∫ y in C, Real.exp (h₀ y) ≤ Real.exp ‖h₀‖ * (volume C).toReal := by
    calc
      ∫ y in C, Real.exp (h₀ y) ≤ ∫ y in C, Real.exp ‖h₀‖ := by
        apply setIntegral_mono_on hint
          (integrableOn_const (C := Real.exp ‖h₀‖) hvolTop.ne)
          (measurableSet_cell N z)
        intro y hy
        exact Real.exp_le_exp.mpr ((abs_le.mp (h₀.norm_coe_le_norm y)).2)
      _ = Real.exp ‖h₀‖ * (volume C).toReal := by
        rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm]
  have havglo : Real.exp (-‖h₀‖) ≤ cellAverage N (fun y => Real.exp (h₀ y)) z := by
    rw [cellAverage, hvol]
    have hlow' : Real.exp (-‖h₀‖) * (4 / (N : ℝ)) ≤
        ∫ y in C, Real.exp (h₀ y) := by simpa only [C, hvol] using hlow
    calc
      Real.exp (-‖h₀‖) = (4 / (N : ℝ))⁻¹ *
          (Real.exp (-‖h₀‖) * (4 / (N : ℝ))) := by
            field_simp [ne_of_gt (by positivity : (0 : ℝ) < 4 / (N : ℝ))]
      _ ≤ (4 / (N : ℝ))⁻¹ * ∫ y in C, Real.exp (h₀ y) := by
        exact mul_le_mul_of_nonneg_left hlow'
          (inv_nonneg.mpr (by positivity))
  have havgup : cellAverage N (fun y => Real.exp (h₀ y)) z ≤ Real.exp ‖h₀‖ := by
    rw [cellAverage, hvol]
    have hupp' : ∫ y in C, Real.exp (h₀ y) ≤
        Real.exp ‖h₀‖ * (4 / (N : ℝ)) := by simpa only [C, hvol] using hupp
    calc
      (4 / (N : ℝ))⁻¹ * ∫ y in C, Real.exp (h₀ y) ≤
          (4 / (N : ℝ))⁻¹ * (Real.exp ‖h₀‖ * (4 / (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hupp'
          (inv_nonneg.mpr (by positivity))
      _ = Real.exp ‖h₀‖ := by
        field_simp [ne_of_gt (by positivity : (0 : ℝ) < 4 / (N : ℝ))]
  refine ⟨lt_of_lt_of_le (Real.exp_pos _) havglo, ?_⟩
  rw [abs_le]
  constructor
  · calc
      -‖h₀‖ = Real.log (Real.exp (-‖h₀‖)) := (Real.log_exp _).symm
      _ ≤ Real.log (cellAverage N (fun y => Real.exp (h₀ y)) z) :=
        Real.log_le_log (Real.exp_pos _) havglo
  · calc
      Real.log (cellAverage N (fun y => Real.exp (h₀ y)) z) ≤ Real.log (Real.exp ‖h₀‖) :=
        Real.log_le_log (lt_of_lt_of_le (Real.exp_pos _) havglo) havgup
      _ = ‖h₀‖ := Real.log_exp _

end Critical2DKPZ.Smoothing

end
