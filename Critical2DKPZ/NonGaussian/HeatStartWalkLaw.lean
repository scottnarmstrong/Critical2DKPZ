/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.ParityHelpers
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
public import Critical2DKPZ.FutureProfiles.EndpointTranslation
public import Critical2DKPZ.MomentBounds.AiiKSmoothedShift
import Mathlib.Probability.IdentDistrib
import Mathlib.Tactic

/-! # The law of the flat heat-start walk profile -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.NonGaussian

/-- Unit cell averages agree with the flat terminal on all reachable sites
of the even heat-start walk profile. -/
theorem heatStartWalkProfile_cellAverage_one_eq (β : ℝ) {N : ℕ} (hN : 0 < N)
    {a b m : ℕ} (hab : a ≤ b) (hm : Even m) (hd : Even (b - a))
    (x : Plane) (ω : Disorder) :
    profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x))
        (cellAverage N fun _ : Plane => 1) ω =
      profileP2Fun β a b (fun w => srwKernel m (w - latticePoint N x)) (fun _ => 1) ω := by
  apply Smoothing.profileP2Fun_congr_of_even β hab hd
  · intro w hw
    have hmem : w ∈ Polymer.endpoints (latticePoint N x) m := by
      by_contra hn
      exact hw (Polymer.srwKernel_eq_zero_of_not_mem m _ w hn)
    exact Smoothing.even_endpoint_of_mem (latticePoint_mem_evenLattice N x) hm hmem
  · intro z hz
    exact cellAverage_const hN hz 1

/-- Time and space translation identify the law of the flat walk profile with that of
a smoothed mass with smoothing time `m` and terminal time `m + (b-a)`. -/
theorem identDistrib_heatStartWalkProfile_smoothed (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (m : ℕ) (x : Site) :
    IdentDistrib (profileP2Fun β a b (fun w => srwKernel m (w - x)) (fun _ => 1))
      (smoothedP2Plane β m (m + (b - a)) 0) disorderLaw disorderLaw := by
  let F : Disorder → ℝ := profileP2Fun β 0 (b - a) (fun w => srwKernel m w) (fun _ => 1)
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x)
  have hF : Measurable F := Polymer.measurable_profileP2Fun _ _ _ _ _
  have hτ : MeasurePreserving τ disorderLaw disorderLaw := FutureProfiles.measurePreserving_disorderShift x
  have hcomp := hτ.comp (Smoothing.measurePreserving_shiftEnvironment a)
  have hStart (ω : Disorder) :
      profileP2Fun β a b (fun w => srwKernel m (w - x)) (fun _ => 1) ω =
        F (τ (Smoothing.shiftEnvironment a ω)) := by
    rw [Smoothing.profileP2Fun_timeShift_sub β le_rfl hab]
    simp only [Nat.sub_self]
    exact FutureProfiles.profileP2Fun_translate β 0 (b - a) x (fun w => srwKernel m w)
      (fun _ => 1) (Smoothing.shiftEnvironment a ω)
  have hEnd (ω : Disorder) : smoothedP2Plane β m (m + (b - a)) 0 ω =
      F (Smoothing.shiftEnvironment m ω) := by
    simpa only [F, Nat.add_sub_cancel_left] using
      MomentBounds.smoothedP2Plane_eq_profileP2Fun_shift β (Nat.le_add_right m (b - a)) ω
  have hStartMap : disorderLaw.map
      (profileP2Fun β a b (fun w => srwKernel m (w - x)) (fun _ => 1)) = disorderLaw.map F := by
    calc
      _ = disorderLaw.map (F ∘ (τ ∘ Smoothing.shiftEnvironment a)) := by
        apply Measure.map_congr
        exact Filter.Eventually.of_forall hStart
      _ = (disorderLaw.map (τ ∘ Smoothing.shiftEnvironment a)).map F :=
        (Measure.map_map hF hcomp.measurable).symm
      _ = _ := by rw [hcomp.map_eq]
  have hEndMap : disorderLaw.map (smoothedP2Plane β m (m + (b - a)) 0) = disorderLaw.map F := by
    calc
      _ = disorderLaw.map (F ∘ Smoothing.shiftEnvironment m) := by
        apply Measure.map_congr
        exact Filter.Eventually.of_forall hEnd
      _ = (disorderLaw.map (Smoothing.shiftEnvironment m)).map F :=
        (Measure.map_map hF (Smoothing.measurable_shiftEnvironment m)).symm
      _ = _ := by rw [(Smoothing.measurePreserving_shiftEnvironment m).map_eq]
  exact ⟨(Polymer.measurable_profileP2Fun _ _ _ _ _).aemeasurable,
    (Polymer.measurable_smoothedP2Plane _ _ _ _).aemeasurable, hStartMap.trans hEndMap.symm⟩

end Critical2DKPZ.NonGaussian

end
