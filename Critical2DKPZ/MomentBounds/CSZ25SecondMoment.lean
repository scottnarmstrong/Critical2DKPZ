/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25Profiles
public import Critical2DKPZ.Polymer.ProbabilityProfiles
public import Critical2DKPZ.Polymer.Profiles
import Mathlib.Tactic

/-! # The order-two case of the CSZ25 centered-moment comparison -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.MomentBounds


/-- For every normalized nonnegative profile, the order-two centered moment is
exactly its variance. Thus the h=2 endpoint of CSZ25's comparison has constant
one and needs no operator estimate. -/
theorem profileP2Fun_abs_sq_eq_variance (β : ℝ) (L : ℕ)
    (φ : Site → ℝ) (hφ0 : ∀ z, 0 ≤ φ z) (hφsum : HasSum φ 1) :
    (∫ ω : Disorder,
      |Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw| ^ 2
        ∂disorderLaw) =
      Var[fun ω : Disorder => Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω;
        disorderLaw] := by
  have hm : (∑' z, φ z) = 1 := hφsum.tsum_eq
  have hmean : (∫ ω : Disorder,
      Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1) ω ∂disorderLaw) = 1 :=
    Polymer.integral_profile_flat_probability β 0 L φ hφ0 hm
  have hmem : MemLp (Critical2DKPZ.profileP2Fun β 0 L φ (fun _ => 1)) 2 disorderLaw := by
    exact Polymer.memLp_profile_probability β 0 L φ (fun _ => 1) hφ0 hm
      1 (by norm_num) (by intro z; norm_num) 2 (by norm_num)
  rw [ProbabilityTheory.variance_eq_integral hmem.aemeasurable]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [hmean]
  simp

end Critical2DKPZ.MomentBounds

end
