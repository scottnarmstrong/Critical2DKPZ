/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeReversalProfileIdentity
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
public import Critical2DKPZ.PolymerCalculus.TimeReversal
import Mathlib.Tactic

/-! # Terminal profile error under exact lattice reversal -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Critical2DKPZ.LocalSobolev

/-- The exact-clock terminal profile ratio retains the one-slice L¹ estimate after the shifted
time-reversed disorder is substituted. The odd-duration hypothesis is what lets the terminal
profile use weights supported on the even lattice only. -/
theorem integral_abs_exactReverse_terminal_profile_ratio_le (β : ℝ) {L m : ℕ}
    (hm : 1 ≤ m) (hmEven : Even m) (x : Site)
    (hx : Even (x 0 + x 1)) (f : Site → ℝ)
    (hf : ∀ z, Even (z 0 + z 1) → 0 < f z) :
    Integrable (fun ω => |Real.log (profileP2Fun β (m - 1) m
        (endpointDist β (m - 1) x
          (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)))
        f (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω))) -
      Real.log (profileP2Fun 0 (m - 1) m
        (endpointDist β (m - 1) x
          (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)))
        f (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)))|)
        disorderLaw ∧
    (∫ ω, |Real.log (profileP2Fun β (m - 1) m
        (endpointDist β (m - 1) x
          (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)))
        f (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω))) -
      Real.log (profileP2Fun 0 (m - 1) m
        (endpointDist β (m - 1) x
          (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)))
        f (Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)))|
      ∂disorderLaw) ≤ Real.sqrt (β ^ 2 + β ^ 4 / 4) := by
  have hodd : ¬ Even (m - 1) := by
    intro hnEven
    have hmInt : Even (m : ℤ) := by exact_mod_cast hmEven
    have hnInt : Even ((m - 1 : ℕ) : ℤ) := by exact_mod_cast hnEven
    have hmEq : (m : ℤ) = ((m - 1 : ℕ) : ℤ) + 1 := by omega
    rw [hmEq, Int.even_add_one] at hmInt
    exact hmInt hnInt
  let ρ : Disorder → Disorder := fun ω =>
    Smoothing.shiftEnvironment (L - m) (PolymerCalculus.reversedDisorder L ω)
  let R : Disorder → ℝ := fun η =>
    |Real.log (profileP2Fun β (m - 1) m (endpointDist β (m - 1) x η) f η) -
      Real.log (profileP2Fun 0 (m - 1) m (endpointDist β (m - 1) x η) f η)|
  have hbase := integral_abs_log_endpointDist_terminal_ratio_le_of_oddDuration
    β (m - 1) x hx hodd f hf
  have hbaseInt : Integrable R disorderLaw := by
    simpa [R, Nat.sub_add_cancel hm] using hbase.1
  have hbaseBound : (∫ η, R η ∂disorderLaw) ≤ Real.sqrt (β ^ 2 + β ^ 4 / 4) := by
    simpa [R, Nat.sub_add_cancel hm] using hbase.2
  have hρ : MeasurePreserving ρ disorderLaw disorderLaw := by
    dsimp [ρ]
    exact (Smoothing.measurePreserving_shiftEnvironment (L - m)).comp
      (PolymerCalculus.measurePreserving_reversedDisorder L)
  have hcompInt : Integrable (fun ω => R (ρ ω)) disorderLaw :=
    hρ.integrable_comp_of_integrable hbaseInt
  have hRmeasMap : AEStronglyMeasurable R (Measure.map ρ disorderLaw) := by
    rw [hρ.map_eq]
    exact hbaseInt.aestronglyMeasurable
  have hcompEq0 := integral_map hρ.measurable.aemeasurable hRmeasMap
  have hcompEq : (∫ ω, R (ρ ω) ∂disorderLaw) = ∫ η, R η ∂disorderLaw := by
    rw [hρ.map_eq] at hcompEq0
    exact hcompEq0.symm
  refine ⟨?_, ?_⟩
  · change Integrable (fun ω => R (ρ ω)) disorderLaw
    exact hcompInt
  · change (∫ ω, R (ρ ω) ∂disorderLaw) ≤ Real.sqrt (β ^ 2 + β ^ 4 / 4)
    rw [hcompEq]
    exact hbaseBound

end Critical2DKPZ.LocalSobolev

end
