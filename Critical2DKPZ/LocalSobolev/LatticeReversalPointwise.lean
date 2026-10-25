/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeReversalExactClock
public import Critical2DKPZ.SHF.Symmetries.LatticeReversalDiscrete
import Mathlib.Tactic

/-! # Pointwise comparison at the exact reflected lattice clock -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.LocalSobolev

/-- At the exact reflected clock, the forward log field differs from the reversed field by the
initial Gaussian slice, the terminal profile ratio, and a deterministic centering discrepancy.
The mean-log term is integrable by `integral_log_exactReverse_flatProfile_eq_pointToPlane`. -/
theorem kpzLattice_sub_exactReverseField_eq (ϑ : ℝ) {N m L : ℕ}
    (hN : 0 < N) (hm : 1 ≤ m) (hmEven : Even m) (hLEven : Even L) (hmL : m ≤ L)
    (h₀ : Plane →ᵇ ℝ) (x : Plane) (ω : Disorder) :
    let q : ℕ := L - m
    let β : ℝ := criticalBeta ϑ N
    let x₀ : Site := latticePoint N x
    let f : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
    let ω' : Disorder := Smoothing.shiftEnvironment q (PolymerCalculus.reversedDisorder L ω)
    let η : Site → ℝ := endpointDist β (m - 1) x₀ ω'
    kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω -
      kpzLatticeReversed ϑ N ((q : ℝ) / N) ((L : ℝ) / N) h₀ x
        (PolymerCalculus.reversedDisorder L ω) =
      β * ω (m, x₀) - β ^ 2 / 2 +
        (Real.log (profileP2Fun 0 (m - 1) m η f ω') -
          Real.log (profileP2Fun β (m - 1) m η f ω')) +
        ((∫ ζ, Real.log (pointToPlane β 0 m 0 ζ) ∂disorderLaw) -
          kpzLatticeCentring ϑ N ((m : ℝ) / N)) := by
  dsimp only
  let q : ℕ := L - m
  let β : ℝ := criticalBeta ϑ N
  let x₀ : Site := latticePoint N x
  let f : Site → ℝ := cellAverage N (fun y => Real.exp (h₀ y))
  let ω' : Disorder := Smoothing.shiftEnvironment q (PolymerCalculus.reversedDisorder L ω)
  let η : Site → ℝ := endpointDist β (m - 1) x₀ ω'
  have hmClock : evenCeil ((N : ℝ) * ((m : ℝ) / N)) = m :=
    Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hN hmEven
  have hLClock : evenCeil ((N : ℝ) * ((L : ℝ) / N)) = L :=
    Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hN hLEven
  have hqEven : Even q := by
    rcases hLEven with ⟨l, hl⟩
    rcases hmEven with ⟨r, hr⟩
    refine ⟨l - r, ?_⟩
    dsimp [q]
    omega
  have hqClock : evenCeil ((N : ℝ) * ((q : ℝ) / N)) = q :=
    Critical2DKPZ.SHF.Symmetries.evenCeil_scaled_nat_div hN hqEven
  have htL : (m : ℝ) / N ≤ (L : ℝ) / N := by
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hmL) (by positivity)
  have hforward := kpzLattice_exactReverseProfile_log_identity
    ϑ hN ((m : ℝ) / N) ((L : ℝ) / N) htL h₀ x ω (by rw [hmClock]; exact hm)
  have hforward' :
      kpzLattice ϑ N ((m : ℝ) / N) h₀ x ω =
        Real.log (profileP2Fun β q L (fun z => if z = x₀ then 1 else 0) f
          (PolymerCalculus.reversedDisorder L ω)) +
          (β * ω (m, x₀) - β ^ 2 / 2 +
            (Real.log (profileP2Fun 0 (m - 1) m η f ω') -
              Real.log (profileP2Fun β (m - 1) m η f ω'))) -
          kpzLatticeCentring ϑ N ((m : ℝ) / N) := by
    simpa [q, β, x₀, f, ω', η, hmClock, hLClock] using hforward
  have hflat := integral_log_exactReverse_flatProfile_eq_pointToPlane β hmL x₀
  have hreverse :
      kpzLatticeReversed ϑ N ((q : ℝ) / N) ((L : ℝ) / N) h₀ x
          (PolymerCalculus.reversedDisorder L ω) =
        Real.log (profileP2Fun β q L (fun z => if z = x₀ then 1 else 0) f
          (PolymerCalculus.reversedDisorder L ω)) -
          (∫ ζ, Real.log (pointToPlane β 0 m 0 ζ) ∂disorderLaw) := by
    unfold kpzLatticeReversed
    rw [hqClock, hLClock, hflat.2]
  rw [hforward', hreverse]
  ring

end Critical2DKPZ.LocalSobolev

end
