/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.JetCauchy
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

/-! # Uniqueness of response jets

Rational values determine a continuous zeroth component. The exact derivative
identities then determine both remaining jet components.
-/

public section
noncomputable section
open MeasureTheory Filter
namespace Critical2DKPZ.Extensions.Response

/-- Continuous jets with equal zeroth components and exact derivative links are equal. -/
theorem continuous_jet_eq_of_zero_eq (F G : C(ℝ, Fin 3 → ℝ))
    (h0 : (fun q => F q 0) = fun q => G q 0)
    (hF : ∀ q, HasDerivAt (fun u => F u 0) (F q 1) q ∧
      HasDerivAt (fun u => F u 1) (F q 2) q)
    (hG : ∀ q, HasDerivAt (fun u => G u 0) (G q 1) q ∧
      HasDerivAt (fun u => G u 1) (G q 2) q) : F = G := by
  have h1 (q : ℝ) : F q 1 = G q 1 := by
    have hh := (hF q).1
    rw [h0] at hh
    exact hh.unique (hG q).1
  have h1fun : (fun q => F q 1) = fun q => G q 1 := funext h1
  have h2 (q : ℝ) : F q 2 = G q 2 := by
    have hh := (hF q).2
    rw [h1fun] at hh
    exact hh.unique (hG q).2
  ext q j
  fin_cases j
  · exact congrFun h0 q
  · exact h1 q
  · exact h2 q

/-- Identification at every fixed parameter and the derivative links determine an
almost-everywhere class of continuous jets uniquely. -/
theorem response_unique {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (g : ℝ → Ω → ℝ) (R R' : Ω →ₘ[P] C(ℝ, Fin 3 → ℝ))
    (hR : (∀ q, (fun ω => R ω q 0) =ᵐ[P] g q) ∧
      ∀ᵐ ω ∂P, ∀ q, HasDerivAt (fun u => R ω u 0) (R ω q 1) q ∧
        HasDerivAt (fun u => R ω u 1) (R ω q 2) q)
    (hR' : (∀ q, (fun ω => R' ω q 0) =ᵐ[P] g q) ∧
      ∀ᵐ ω ∂P, ∀ q, HasDerivAt (fun u => R' ω u 0) (R' ω q 1) q ∧
        HasDerivAt (fun u => R' ω u 1) (R' ω q 2) q) : R = R' := by
  have hRat : ∀ᵐ ω ∂P, ∀ q : ℚ, R ω q 0 = R' ω q 0 :=
    ae_all_iff.mpr (fun q => (hR.1 q).trans (hR'.1 q).symm)
  apply AEEqFun.ext
  filter_upwards [hRat, hR.2, hR'.2] with ω hω hlinks hlinks'
  apply continuous_jet_eq_of_zero_eq (R ω) (R' ω) _ hlinks hlinks'
  exact Rat.denseRange_cast.equalizer
    ((continuous_apply 0).comp (R ω).continuous)
    ((continuous_apply 0).comp (R' ω).continuous) (funext hω)

end Critical2DKPZ.Extensions.Response
