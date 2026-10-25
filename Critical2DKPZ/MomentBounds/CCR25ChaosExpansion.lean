/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Gaussian.DisorderLaws
public import Critical2DKPZ.MomentBounds.CCR25Operators
import Mathlib.Tactic

/-! # Finite chaos products and replica-coordinate moments -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The union of all space-time coordinates used by a finite family of chaos
monomials. -/
def chaosOccurrenceUnion {h : ℕ} (A : Fin h → Finset (ℕ × Site)) :
    Finset (ℕ × Site) := Finset.univ.biUnion A

/-- Number of replicas whose selected chaos monomial contains one fixed
space-time coordinate. -/
def chaosOccurrenceCount {h : ℕ} (A : Fin h → Finset (ℕ × Site))
    (z : ℕ × Site) : ℕ :=
  (Finset.univ.filter (fun i : Fin h => z ∈ A i)).card

/-- The product of the disorder factor at one coordinate over all replicas. -/
def chaosCoordinateFactor {h : ℕ} (β : ℝ) (A : Fin h → Finset (ℕ × Site))
    (z : ℕ × Site) (x : ℝ) : ℝ :=
  ∏ i : Fin h, if z ∈ A i then Real.exp (β * x - β ^ 2 / 2) - 1 else 1

/-- The `k`th moment of the centered disorder at one space-time coordinate. -/
def replicaCoordinateDisorderMoment (β : ℝ) (z : ℕ × Site) (k : ℕ) : ℝ :=
  ∫ ω : Disorder, Critical2DKPZ.Polymer.xi β z ω ^ k ∂disorderLaw

/-- Regrouping a finite product of square-free chaos monomials by disorder
coordinate. -/
theorem chaosMonomial_product_eq_coordinate_factors {h : ℕ} (β : ℝ)
    (A : Fin h → Finset (ℕ × Site)) (ω : Disorder) :
    (∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) =
      ∏ z ∈ chaosOccurrenceUnion A, chaosCoordinateFactor β A z (ω z) := by
  classical
  let U := chaosOccurrenceUnion A
  have hfilter (i : Fin h) : U.filter (fun z => z ∈ A i) = A i := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · exact fun hz => hz.2
    · intro hz
      refine ⟨?_, hz⟩
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩
  have hrow (i : Fin h) :
      Critical2DKPZ.Polymer.chaosMonomial β (A i) ω =
        ∏ z ∈ U, if z ∈ A i then Real.exp (β * ω z - β ^ 2 / 2) - 1 else 1 := by
    calc
      Critical2DKPZ.Polymer.chaosMonomial β (A i) ω =
          ∏ z ∈ A i, (Real.exp (β * ω z - β ^ 2 / 2) - 1) := by
        simp [Critical2DKPZ.Polymer.chaosMonomial, Critical2DKPZ.Polymer.xi]
      _ = ∏ z ∈ U, if z ∈ A i then Real.exp (β * ω z - β ^ 2 / 2) - 1 else 1 := by
        rw [← hfilter i, Finset.prod_filter]
        apply Finset.prod_congr rfl
        intro z hz
        simp only [Finset.mem_filter, hz, true_and]
  calc
    (∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) =
        ∏ i : Fin h, ∏ z ∈ U,
          if z ∈ A i then Real.exp (β * ω z - β ^ 2 / 2) - 1 else 1 := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hrow i
    _ = ∏ z ∈ U, ∏ i : Fin h,
          if z ∈ A i then Real.exp (β * ω z - β ^ 2 / 2) - 1 else 1 :=
      Finset.prod_comm
    _ = ∏ z ∈ chaosOccurrenceUnion A, chaosCoordinateFactor β A z (ω z) := by
      apply Finset.prod_congr rfl
      intro z hz
      simp [chaosCoordinateFactor]

/-- A chaos coordinate factor is a power of its disorder coordinate. -/
theorem chaosCoordinateFactor_eq_rpow {h : ℕ} (β : ℝ)
    (A : Fin h → Finset (ℕ × Site)) (z : ℕ × Site) (x : ℝ) :
    chaosCoordinateFactor β A z x =
      (Real.exp (β * x - β ^ 2 / 2) - 1) ^ chaosOccurrenceCount A z := by
  classical
  let S := Finset.univ.filter (fun i : Fin h => z ∈ A i)
  have hmem (i : Fin h) : z ∈ A i ↔ i ∈ S := by
    simp [S]
  calc
    chaosCoordinateFactor β A z x =
        ∏ i : Fin h, if i ∈ S then Real.exp (β * x - β ^ 2 / 2) - 1 else 1 := by
      unfold chaosCoordinateFactor
      simp_rw [hmem]
    _ = ∏ i ∈ S, (Real.exp (β * x - β ^ 2 / 2) - 1) := by
      exact Finset.prod_ite_mem_eq S (fun _ => Real.exp (β * x - β ^ 2 / 2) - 1)
    _ = (Real.exp (β * x - β ^ 2 / 2) - 1) ^ S.card := by
      rw [Finset.prod_const]
    _ = _ := by rfl

/-- Exact factorization of a finite product of chaos monomials into the
single-coordinate moments dictated by replica multiplicities. -/
theorem integral_chaosMonomial_product {h : ℕ} (β : ℝ)
    (A : Fin h → Finset (ℕ × Site)) :
    ∫ ω : Disorder,
        (∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) ∂disorderLaw =
      ∏ z ∈ chaosOccurrenceUnion A,
        replicaCoordinateDisorderMoment β z (chaosOccurrenceCount A z) := by
  classical
  have hpoint (ω : Disorder) :
      (∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) =
        ∏ z ∈ chaosOccurrenceUnion A,
          (Real.exp (β * ω z - β ^ 2 / 2) - 1) ^ chaosOccurrenceCount A z := by
    rw [chaosMonomial_product_eq_coordinate_factors]
    apply Finset.prod_congr rfl
    intro z hz
    exact chaosCoordinateFactor_eq_rpow β A z (ω z)
  have hmeas (z : ℕ × Site) :
      Measurable (fun x : ℝ =>
        (Real.exp (β * x - β ^ 2 / 2) - 1) ^ chaosOccurrenceCount A z) := by
    fun_prop
  have hfun :
      (fun ω : Disorder =>
        ∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) =
      fun ω =>
        ∏ z ∈ chaosOccurrenceUnion A,
          (Real.exp (β * ω z - β ^ 2 / 2) - 1) ^ chaosOccurrenceCount A z :=
    funext hpoint
  rw [hfun]
  rw [Critical2DKPZ.Polymer.integral_coordinateProduct
    (chaosOccurrenceUnion A)
    (fun z x => (Real.exp (β * x - β ^ 2 / 2) - 1) ^ chaosOccurrenceCount A z)
    hmeas]
  apply Finset.prod_congr rfl
  intro z hz
  simp [replicaCoordinateDisorderMoment, Critical2DKPZ.Polymer.xi]

/-- Replica coordinate moments agree with the corresponding Gaussian disorder moments. -/
theorem replicaCoordinateDisorderMoment_eq_gaussianDisorderMoment
    (β : ℝ) (z : ℕ × Site) (k : ℕ) :
    replicaCoordinateDisorderMoment β z k =
      Critical2DKPZ.MomentBounds.gaussianDisorderMoment β k := by
  let f : ℝ → ℝ := fun x => (Real.exp (β * x - β ^ 2 / 2) - 1) ^ k
  have hz := (Critical2DKPZ.Gaussian.hasLaw_disorder_eval z).integral_comp
    (f := f) (by fun_prop)
  have h0 :=
    (Critical2DKPZ.Gaussian.hasLaw_disorder_eval (0, (0 : Site))).integral_comp
      (f := f) (by fun_prop)
  calc
    replicaCoordinateDisorderMoment β z k = ∫ ω, f (ω z) ∂disorderLaw := by
      simp [replicaCoordinateDisorderMoment, f, Critical2DKPZ.Polymer.xi]
    _ = ∫ x, f x ∂ProbabilityTheory.gaussianReal 0 1 := by
      simpa [Function.comp_apply] using hz
    _ = ∫ ω, f (ω (0, (0 : Site))) ∂disorderLaw := by
      simpa [Function.comp_apply] using h0.symm
    _ = Critical2DKPZ.MomentBounds.gaussianDisorderMoment β k := by
      simp [Critical2DKPZ.MomentBounds.gaussianDisorderMoment, f,
        Critical2DKPZ.Polymer.xi]

/-- The expectation of a product of chaos monomials factors into Gaussian coordinate moments. -/
theorem integral_chaosMonomial_product_eq_gaussianMoments {h : ℕ} (β : ℝ)
    (A : Fin h → Finset (ℕ × Site)) :
    ∫ ω : Disorder,
        (∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) ∂disorderLaw =
      ∏ z ∈ chaosOccurrenceUnion A,
        Critical2DKPZ.MomentBounds.gaussianDisorderMoment β (chaosOccurrenceCount A z) := by
  rw [integral_chaosMonomial_product]
  apply Finset.prod_congr rfl
  intro z hz
  exact replicaCoordinateDisorderMoment_eq_gaussianDisorderMoment β z _

/-- A replica coordinate appearing once has zero disorder expectation. -/
theorem replicaCoordinateDisorderMoment_one_eq_zero (β : ℝ) (z : ℕ × Site) :
    replicaCoordinateDisorderMoment β z 1 = 0 := by
  change (∫ ω, Critical2DKPZ.Polymer.xi β z ω ^ 1 ∂disorderLaw) = 0
  simp only [pow_one]
  exact Critical2DKPZ.Polymer.integral_xi β z

/-- A finite replica chaos product has zero expectation if any space-time
coordinate occurs in exactly one replica. -/
theorem integral_chaosMonomial_product_eq_zero_of_singleton {h : ℕ} (β : ℝ)
    (A : Fin h → Finset (ℕ × Site)) (z : ℕ × Site)
    (hz : z ∈ chaosOccurrenceUnion A)
    (hcount : chaosOccurrenceCount A z = 1) :
    ∫ ω : Disorder,
        (∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) ∂disorderLaw = 0 := by
  rw [integral_chaosMonomial_product]
  exact Finset.prod_eq_zero hz (by
    rw [hcount]
    exact replicaCoordinateDisorderMoment_one_eq_zero β z)

end

end Critical2DKPZ.MomentBounds
