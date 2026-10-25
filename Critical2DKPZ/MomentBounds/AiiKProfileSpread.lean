/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25Profiles
public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.SHF.Moments.EntranceWalkMoments
import Mathlib.Tactic

/-! # The mean and spread of the simple walk profile -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem profileMean_srwKernel_eq_zero (n : ℕ) :
    profileMean (fun z => srwKernel n z) = 0 := by
  let E := Polymer.endpoints (0 : Site) n
  have hsupport : ∀ z ∉ E, srwKernel n z = 0 := by
    intro z hz
    have h := Polymer.srwKernel_eq_zero_of_not_mem n 0 z hz
    simpa only [sub_zero] using h
  have hnegmem : ∀ z ∈ E, -z ∈ E := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨path, -, hpath⟩
    apply Finset.mem_image.mpr
    refine ⟨fun i => Polymer.oppositeStep (path i), Finset.mem_univ _, ?_⟩
    rw [Polymer.walkPosition_opposite]
    simp [← hpath]
  have hE : Finset.map (Equiv.neg Site).toEmbedding E = E := by
    ext z
    simp only [Finset.mem_map, Equiv.toEmbedding_apply, E]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hnegmem y hy
    · intro hz
      refine ⟨-z, hnegmem z hz, ?_⟩
      simp
  have hcoord (i : Fin 2) :
      ∑ z ∈ E, srwKernel n z * (z i : ℝ) = 0 := by
    let f : Site → ℝ := fun z => srwKernel n z * (z i : ℝ)
    have hfodd : f.Odd := by
      intro z
      simp [f, Polymer.srwKernel_neg]
    exact hfodd.finsetSum_eq_zero hE
  have hmean := profileMean_eq_sum_of_support (fun z => srwKernel n z) E hsupport
  calc
    profileMean (fun z => srwKernel n z) =
        ∑ z ∈ E, srwKernel n z • siteToPlane z := hmean
    _ = 0 := by
      ext i
      simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, siteToPlane,
        WithLp.ofLp_toLp, WithLp.ofLp_zero, Pi.zero_apply, Pi.smul_apply,
        Finset.sum_apply, smul_eq_mul] using hcoord i

/-- The mean-squared displacement of the simple-walk kernel equals its time. -/
theorem profileSpread_srwKernel (s : ℕ) :
    profileSpread (fun y => srwKernel s y) = s := by
  unfold profileSpread
  rw [profileMean_srwKernel_eq_zero]
  simp only [sub_zero]
  have hfinite :
      (∑' z : Site, ‖siteToPlane z‖ ^ 2 * srwKernel s z) =
        ∑ z ∈ Polymer.endpoints 0 s, ‖siteToPlane z‖ ^ 2 * srwKernel s z := by
    apply tsum_eq_sum
    intro z hz
    have h := Polymer.srwKernel_eq_zero_of_not_mem s 0 z hz
    have hq : srwKernel s z = 0 := by simpa only [sub_zero] using h
    simp [hq]
  rw [hfinite]
  simpa only [mul_comm] using SHF.Moments.sum_srwKernel_norm_sq s

end Critical2DKPZ.MomentBounds
