/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.LaplaceUniqueness
public import Critical2DKPZ.Definitions.Plane
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Tactic

/-! # Uniqueness of the two-dimensional Laplace transform -/

@[expose] public section

open MeasureTheory Set
open scoped ProbabilityTheory ENNReal

namespace Critical2DKPZ.Analysis

/-- The open planar quadrant with both coordinates positive. -/
public def positiveQuadrant : Set Plane := {x | 0 < x 0 ∧ 0 < x 1}

/-- Finite measures on the plane are determined by their two-coordinate moment generating functions on a rectangle around the origin. -/
theorem measure_eq_of_bivariate_mgf_eq_on_Ioo {μ ν : Measure Plane}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {ε : ℝ} (hε : 0 < ε)
    (hμ : ∀ r s : ℝ, r ∈ Ioo (-ε) ε → s ∈ Ioo (-ε) ε →
      Integrable (fun x : Plane => Real.exp (r * x 0 + s * x 1)) μ)
    (hν : ∀ r s : ℝ, r ∈ Ioo (-ε) ε → s ∈ Ioo (-ε) ε →
      Integrable (fun x : Plane => Real.exp (r * x 0 + s * x 1)) ν)
    (hLap : ∀ r s : ℝ, r ∈ Ioo (-ε) ε → s ∈ Ioo (-ε) ε →
      (∫ x : Plane, Real.exp (r * x 0 + s * x 1) ∂μ) =
        ∫ x : Plane, Real.exp (r * x 0 + s * x 1) ∂ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  let p : Plane := (InnerProductSpace.toDual ℝ Plane).symm L
  let M : ℝ := |p 0| + |p 1| + 1
  let δ : ℝ := ε / M
  have hM : 0 < M := by dsimp [M]; positivity
  have hδ : 0 < δ := div_pos hε hM
  have hp0 : |p 0| < M := by dsimp [M]; linarith [abs_nonneg (p 1)]
  have hp1 : |p 1| < M := by dsimp [M]; linarith [abs_nonneg (p 0)]
  let X : Plane → ℝ := L
  have hXm : Measurable X := L.continuous.measurable
  have hXform (x : Plane) : X x = p 0 * x 0 + p 1 * x 1 := by
    change L x = p 0 * x 0 + p 1 * x 1
    rw [← InnerProductSpace.toDual_symm_apply (x := x) (y := L)]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply,
      starRingEnd_apply, star_trivial]
    ring
  have hcoord (t : ℝ) (ht : t ∈ Ioo (-δ) δ) (i : Fin 2) :
      t * p i ∈ Ioo (-ε) ε := by
    have htAbs : |t| < δ := abs_lt.mpr ⟨by linarith [ht.1], ht.2⟩
    have hpi : |p i| < M := by
      fin_cases i
      · exact hp0
      · exact hp1
    have hprod : |t * p i| < ε := by
      rw [abs_mul]
      have hle : |t| * |p i| ≤ |t| * M := mul_le_mul_of_nonneg_left hpi.le (abs_nonneg t)
      have hlt : |t| * M < δ * M := mul_lt_mul_of_pos_right htAbs hM
      have hδM : δ * M = ε := by dsimp [δ]; field_simp
      rw [hδM] at hlt
      exact lt_of_le_of_lt hle hlt
    exact abs_lt.mp hprod
  have hIntμ (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      Integrable (fun x : Plane => Real.exp (t * X x)) μ := by
    have h0 := hμ (t * p 0) (t * p 1) (hcoord t ht 0) (hcoord t ht 1)
    have heq : (fun x : Plane => Real.exp (t * X x)) =
        fun x => Real.exp ((t * p 0) * x 0 + (t * p 1) * x 1) := by
      funext x
      rw [hXform x]
      congr 1
      ring
    rw [heq]
    exact h0
  have hIntν (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      Integrable (fun x : Plane => Real.exp (t * X x)) ν := by
    have h0 := hν (t * p 0) (t * p 1) (hcoord t ht 0) (hcoord t ht 1)
    have heq : (fun x : Plane => Real.exp (t * X x)) =
        fun x => Real.exp ((t * p 0) * x 0 + (t * p 1) * x 1) := by
      funext x
      rw [hXform x]
      congr 1
      ring
    rw [heq]
    exact h0
  have hExpμ : Ioo (-δ) δ ⊆ ProbabilityTheory.integrableExpSet id (Measure.map X μ) := by
    intro t ht
    change Integrable (fun y : ℝ => Real.exp (t * y)) (Measure.map X μ)
    exact (integrable_map_measure (by fun_prop) hXm.aemeasurable).2 (hIntμ t ht)
  have hExpν : Ioo (-δ) δ ⊆ ProbabilityTheory.integrableExpSet id (Measure.map X ν) := by
    intro t ht
    change Integrable (fun y : ℝ => Real.exp (t * y)) (Measure.map X ν)
    exact (integrable_map_measure (by fun_prop) hXm.aemeasurable).2 (hIntν t ht)
  have hIntSetμ : Ioo (-δ) δ ⊆ interior
      (ProbabilityTheory.integrableExpSet id (Measure.map X μ)) :=
    interior_maximal hExpμ isOpen_Ioo
  have hIntSetν : Ioo (-δ) δ ⊆ interior
      (ProbabilityTheory.integrableExpSet id (Measure.map X ν)) :=
    interior_maximal hExpν isOpen_Ioo
  have hmgf (t : ℝ) (ht : t ∈ Ioo (-δ) δ) :
      ProbabilityTheory.mgf id (Measure.map X μ) t =
        ProbabilityTheory.mgf id (Measure.map X ν) t := by
    simp only [ProbabilityTheory.mgf, id_eq]
    rw [integral_map hXm.aemeasurable (by fun_prop), integral_map hXm.aemeasurable (by fun_prop)]
    have heqμ : (fun x : Plane => Real.exp (t * X x)) =
        fun x => Real.exp ((t * p 0) * x 0 + (t * p 1) * x 1) := by
      funext x
      rw [hXform x]
      congr 1
      ring
    rw [heqμ]
    exact hLap (t * p 0) (t * p 1) (hcoord t ht 0) (hcoord t ht 1)
  have hproj : Measure.map X μ = Measure.map X ν :=
    measure_eq_of_mgf_eq_on_Ioo hδ hIntSetμ hIntSetν hmgf
  rw [charFunDual_eq_charFun_map_one (μ := μ) (L := L),
    charFunDual_eq_charFun_map_one (μ := ν) (L := L)]
  exact congrArg (fun ρ : Measure ℝ => MeasureTheory.charFun ρ 1) hproj


end Critical2DKPZ.Analysis

end
