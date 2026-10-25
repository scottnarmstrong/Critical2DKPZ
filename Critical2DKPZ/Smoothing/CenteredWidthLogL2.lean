/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.CenteredLogL2
public import Critical2DKPZ.Smoothing.ProfileLogIntegrability
public import Critical2DKPZ.Smoothing.WidthLogL2
import Mathlib.Tactic

/-! # Centered logarithmic continuity under kernel-width changes -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.Smoothing

/-- A width change of the weighted logarithm, centered by the corresponding flat-profile width
change, is bounded in `L²` by the two uncentered width differences. -/
theorem eLpNorm_centered_log_walkKernel_profile_difference_le (β : ℝ) (a T p q : ℕ)
    (x : Site) (f : Site → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) :
    eLpNorm (fun ω =>
      (Real.log (profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * q) (w - x)) f ω) -
       Real.log (profileP2Fun β a (a + T)
        (fun w => srwKernel (2 * p) (w - x)) f ω)) -
        (∫ ω', (Real.log (profileP2Fun β a (a + T)
          (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω') -
          Real.log (profileP2Fun β a (a + T)
            (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω'))
          ∂disorderLaw)) 2 disorderLaw ≤
      eLpNorm (fun ω =>
        Real.log (profileP2Fun β a (a + T)
          (fun w => srwKernel (2 * q) (w - x)) f ω) -
        Real.log (profileP2Fun β a (a + T)
          (fun w => srwKernel (2 * p) (w - x)) f ω)) 2 disorderLaw +
      eLpNorm (fun ω =>
        Real.log (profileP2Fun β a (a + T)
          (fun w => srwKernel (2 * q) (w - x)) (fun _ => 1) ω) -
        Real.log (profileP2Fun β a (a + T)
          (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω)) 2 disorderLaw := by
  classical
  let νq : Site → ℝ := fun w => srwKernel (2 * q) (w - x)
  let νp : Site → ℝ := fun w => srwKernel (2 * p) (w - x)
  let A : Finset Site := Polymer.endpoints x (2 * p) ∪ Polymer.endpoints x (2 * q)
  have hνqA : ∀ w ∉ A, νq w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w (by
      intro hwq
      exact hw (Finset.mem_union_right _ hwq))
  have hνpA : ∀ w ∉ A, νp w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w (by
      intro hwp
      exact hw (Finset.mem_union_left _ hwp))
  have hνq0 : ∀ w, 0 ≤ νq w := fun w => Polymer.kernel_nonneg (2 * q) (w - x)
  have hνp0 : ∀ w, 0 ≤ νp w := fun w => Polymer.kernel_nonneg (2 * p) (w - x)
  have hνq1 : ∑ w ∈ A, νq w = 1 := by
    dsimp [νq, A]
    calc
      _ = ∑ w ∈ Polymer.endpoints x (2 * q), srwKernel (2 * q) (w - x) := by
        symm
        apply Finset.sum_subset Finset.subset_union_right
        intro w hw hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * q) x w hnot
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * q) x
  have hνp1 : ∑ w ∈ A, νp w = 1 := by
    dsimp [νp, A]
    calc
      _ = ∑ w ∈ Polymer.endpoints x (2 * p), srwKernel (2 * p) (w - x) := by
        symm
        apply Finset.sum_subset Finset.subset_union_left
        intro w hw hnot
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w hnot
      _ = 1 := Polymer.sum_srwKernel_endpoints (2 * p) x
  have hfFlat : ∀ z : Site, 0 < (1 : ℝ) ∧ |Real.log (1 : ℝ)| ≤ 0 := by
    intro z
    norm_num
  have hqf := memLp_log_profileP2Fun_of_bounded_terminal β a (a + T)
    νq A hνqA hνq0 hνq1 f H hH hf
  have hpf := memLp_log_profileP2Fun_of_bounded_terminal β a (a + T)
    νp A hνpA hνp0 hνp1 f H hH hf
  have hq0 := memLp_log_profileP2Fun_of_bounded_terminal β a (a + T)
    νq A hνqA hνq0 hνq1 (fun _ => 1) 0 (by norm_num) hfFlat
  have hp0 := memLp_log_profileP2Fun_of_bounded_terminal β a (a + T)
    νp A hνpA hνp0 hνp1 (fun _ => 1) 0 (by norm_num) hfFlat
  let Df : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β a (a + T) νq f ω) -
      Real.log (profileP2Fun β a (a + T) νp f ω)
  let D0 : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β a (a + T) νq (fun _ => 1) ω) -
      Real.log (profileP2Fun β a (a + T) νp (fun _ => 1) ω)
  have hDf : MemLp Df 2 disorderLaw := by
    dsimp [Df]
    exact hqf.sub hpf
  have hD0 : MemLp D0 2 disorderLaw := by
    dsimp [D0]
    exact hq0.sub hp0
  have hbound := eLpNorm_sub_integral_le disorderLaw Df D0 hD0
  change eLpNorm (fun ω => Df ω - (∫ ω', D0 ω' ∂disorderLaw)) 2 disorderLaw ≤
    eLpNorm Df 2 disorderLaw + eLpNorm D0 2 disorderLaw
  exact hbound

end Critical2DKPZ.Smoothing

end
