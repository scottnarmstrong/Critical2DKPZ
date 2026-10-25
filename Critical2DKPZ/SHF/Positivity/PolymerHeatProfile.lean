/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.HeatStartProfileApprox
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.SHF.Positivity.HeatStartMean
import Mathlib.Tactic

/-! # Lattice profile representation of polymer heat-start pairings -/

@[expose] public section

noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.SHF.Positivity

/-- When the heat-start pairing is integrable, its lattice cell decomposition is the profile
pairing with cell masses of the heat kernel. -/
theorem integral_heatKernel_polymerMeasure_eq_of_integrable (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (_hs : 0 ≤ s) (hst : s < t) (_hδ : 0 < δ) (x : Plane) (ω : Disorder)
    (hInt : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x))
      (polymerMeasure ϑ N s t ω)) :
    ∫ p, heatKernel δ (p.1 - x) ∂polymerMeasure ϑ N s t ω =
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
        (fun w => ∫ y in cell N w, heatKernel δ (y - x)) (fun _ => 1) ω := by
  let H : Plane → ℝ := fun y => heatKernel δ (y - x)
  let ν : Site → ℝ := fun w => ∫ y in cell N w, H y
  let f : Site → ℝ := cellAverage N (fun _ : Plane => (1 : ℝ))
  have hInt' : Integrable (fun p : Plane × Plane =>
      heatKernel δ (p.1 - x) * Real.exp ((0 : Plane →ᵇ ℝ) p.2))
      (polymerMeasure ϑ N s t ω) := by
    apply hInt.congr
    filter_upwards [] with p
    simp
  have hprofile := JointConvergence.profile_cellHeat_eq_polymerMeasure_pairing
    ϑ N s t δ x (0 : Plane →ᵇ ℝ) ω (by omega) hInt'
  have hν : ∀ w, ν w = ∫ y in cell N w, heatKernel δ (y - x) := by
    intro w
    rfl
  have hflat : profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
      ν f ω = profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
        ν (fun _ => 1) ω := by
    classical
    let a := evenCeil (N * s)
    let b := evenCeil (N * t)
    have hab : a ≤ b := evenCeil_mono (mul_le_mul_of_nonneg_left hst.le
      (Nat.cast_nonneg N))
    have hnEven : Even (b - a) := by
      obtain ⟨u, hu⟩ := evenCeil_even (N * s)
      obtain ⟨v, hv⟩ := evenCeil_even (N * t)
      have hua : a = u + u := by simpa [a] using hu
      have hvb : b = v + v := by simpa [b] using hv
      have huv : u ≤ v := by omega
      refine ⟨v - u, ?_⟩
      omega
    have hνodd (w : Site) (hw : w ∉ evenLattice) : ν w = 0 := by
      dsimp [ν]
      rw [cell_eq_empty_of_not_even hw]
      simp
    have hfEven (z : Site) (hz : z ∈ evenLattice) : f z = 1 := by
      dsimp [f]
      simpa using cellAverage_const (by omega) hz 1
    have hpoint (w z : Site) (hw : w ∈ evenLattice) (hz : z ∈ evenLattice) :
        pointToPoint (criticalBeta ϑ N) a (b - a) w z ω * f z =
          pointToPoint (criticalBeta ϑ N) a (b - a) w z ω := by
      rw [hfEven z hz, mul_one]
    have hinner (w : Site) :
        ν w * ∑' z, pointToPoint (criticalBeta ϑ N) a (b - a) w z ω * f z =
          ν w * ∑' z, pointToPoint (criticalBeta ϑ N) a (b - a) w z ω := by
      by_cases hw : w ∈ evenLattice
      · congr 1
        apply tsum_congr
        intro z
        by_cases hz : z ∈ evenLattice
        · by_cases hzero : pointToPoint (criticalBeta ϑ N) a (b - a) w z ω = 0
          · simp [hzero]
          · exact hpoint w z hw hz
        · have hparity : ¬ Int.ModEq 2 (z 0 + z 1) (w 0 + w 1 + (b - a : ℕ)) := by
            intro hmod
            have hzEven : Even (z 0 + z 1) := by
              obtain ⟨m, hm⟩ := hw
              obtain ⟨n, hn⟩ := hnEven
              have hn' : ((b - a : ℕ) : ℤ) = (n : ℤ) + n := by
                exact_mod_cast hn
              obtain ⟨k, hk⟩ := hmod.dvd
              refine ⟨m + n - k, ?_⟩
              omega
            exact hz hzEven
          have hz0 := Polymer.pointToPoint_eq_zero_of_parity
            (criticalBeta ϑ N) a (b - a) w z ω hparity
          simp [hz0]
      · rw [hνodd w hw]
        simp
    simpa only [profileP2Fun, a, b, mul_one] using tsum_congr hinner
  have hprofile' : profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
      (fun w => ∫ y in cell N w, heatKernel δ (y - x)) f ω =
      profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
        (fun w => ∫ y in cell N w, heatKernel δ (y - x)) (fun _ => 1) ω := by
    simpa only [hν] using hflat
  have hprofile'' : profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s))
      (evenCeil (N * t)) (fun w => ∫ y in cell N w, heatKernel δ (y - x))
      f ω = ∫ p, heatKernel δ (p.1 - x) ∂polymerMeasure ϑ N s t ω := by
    simpa [Real.exp_zero, H, f] using hprofile
  calc
    ∫ p, heatKernel δ (p.1 - x) ∂polymerMeasure ϑ N s t ω =
        profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
          (fun w => ∫ y in cell N w, heatKernel δ (y - x)) f ω := hprofile''.symm
    _ = profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
          (fun w => ∫ y in cell N w, heatKernel δ (y - x)) (fun _ => 1) ω := hprofile'

/-- The lattice profile identity holds almost surely in disorder, since the heat-start pairing is
almost surely integrable. -/
theorem ae_integral_heatKernel_polymerMeasure_eq (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    ∀ᵐ ω ∂disorderLaw,
      ∫ p, heatKernel δ (p.1 - x) ∂polymerMeasure ϑ N s t ω =
        profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
          (fun w => ∫ y in cell N w, heatKernel δ (y - x)) (fun _ => 1) ω := by
  filter_upwards [ae_integrable_polymer_heat_start ϑ hN s t δ hδ x] with ω hω
  exact integral_heatKernel_polymerMeasure_eq_of_integrable ϑ hN hs hst hδ x ω hω

end Critical2DKPZ.SHF.Positivity

end
