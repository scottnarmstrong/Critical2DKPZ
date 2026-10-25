/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.KernelReversal
public import Critical2DKPZ.Polymer.Endpoints
public import Mathlib.Tactic
public import Critical2DKPZ.Polymer.Endpoints
import Mathlib.Tactic

/-! # Weighted lattice mass under exact time reversal -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.LocalSobolev

/-- Exact reversal for a weighted point-to-point mass; the finite-time kernels have finite endpoint support by `Polymer.pointToPoint_eq_zero_iff`, and the endpoint Gaussian factors remain explicit. -/
theorem tsum_weightedPointToPoint_time_reversal (β : ℝ) {L m : ℕ} (hmL : m ≤ L)
    (x : Site) (f : Site → ℝ) (ω : Disorder) :
    (∑' z : Site, f z * pointToPoint β 0 m z x ω) =
      Real.exp (β * ω (m, x)) *
        ∑' z : Site, pointToPoint β (L - m) m x z
          (PolymerCalculus.reversedDisorder L ω) *
          (f z * Real.exp (-β * ω (0, z))) := by
  classical
  let A : Finset Site := Polymer.endpoints x m
  have hzero (z : Site) (hz : z ∉ A) :
      f z * pointToPoint β 0 m z x ω = 0 := by
    have hp : pointToPoint β 0 m z x ω = 0 := by
      apply (Polymer.pointToPoint_eq_zero_iff β 0 m z x ω).2
      rintro ⟨s, hs⟩
      exact hz ((Polymer.mem_endpoints_iff x z m).2
        ⟨PolymerCalculus.reverseSteps s,
          (PolymerCalculus.walkPosition_reverse_endpoint_iff z x s).2 hs⟩)
    rw [hp]
    simp
  have hleft : (∑' z : Site, f z * pointToPoint β 0 m z x ω) =
      ∑ z ∈ A, f z * pointToPoint β 0 m z x ω := by
    apply tsum_eq_sum
    exact hzero
  have hright : (∑' z : Site, pointToPoint β (L - m) m x z
      (PolymerCalculus.reversedDisorder L ω) *
      (f z * Real.exp (-β * ω (0, z)))) =
      ∑ z ∈ A, pointToPoint β (L - m) m x z
        (PolymerCalculus.reversedDisorder L ω) *
        (f z * Real.exp (-β * ω (0, z))) := by
    rw [Polymer.tsum_pointToPoint_mul_eq_sum β (L - m) m x
      (fun z => f z * Real.exp (-β * ω (0, z)))
      (PolymerCalculus.reversedDisorder L ω)]
  have hterm (z : Site) : f z * pointToPoint β 0 m z x ω =
      Real.exp (β * ω (m, x)) *
        (pointToPoint β (L - m) m x z (PolymerCalculus.reversedDisorder L ω) *
          (f z * Real.exp (-β * ω (0, z)))) := by
    have hrev := PolymerCalculus.pointToPoint_time_reversal β L 0 m (by omega) z x ω
    have hcancel : Real.exp (-β * ω (0, z)) * Real.exp (β * ω (0, z)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hfac : Real.exp (-β * ω (0, z)) *
        (Real.exp (β * ω (0, z)) * pointToPoint β 0 m z x ω) =
          pointToPoint β 0 m z x ω := by
      rw [← mul_assoc, hcancel, one_mul]
    calc
      _ = f z * (Real.exp (-β * ω (0, z)) *
          (Real.exp (β * ω (0, z)) * pointToPoint β 0 m z x ω)) :=
            congrArg (fun q : ℝ => f z * q) hfac.symm
      _ = _ := by
        rw [hrev]
        ring_nf
  rw [hleft, hright]
  calc
    (∑ z ∈ A, f z * pointToPoint β 0 m z x ω) =
        ∑ z ∈ A, Real.exp (β * ω (m, x)) *
          (pointToPoint β (L - m) m x z (PolymerCalculus.reversedDisorder L ω) *
            (f z * Real.exp (-β * ω (0, z)))) := by
              apply Finset.sum_congr rfl
              intro z hz
              exact hterm z
    _ = Real.exp (β * ω (m, x)) *
        ∑ z ∈ A, pointToPoint β (L - m) m x z
          (PolymerCalculus.reversedDisorder L ω) *
          (f z * Real.exp (-β * ω (0, z))) := by
            rw [Finset.mul_sum]
    _ = _ := by rw [← hright]

end Critical2DKPZ.LocalSobolev

end
