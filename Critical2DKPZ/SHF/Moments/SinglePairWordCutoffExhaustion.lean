/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordContinuumCutoffs
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Tactic

/-! # Compact space-time cutoff exhaustions for the two-particle entrance -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- Compact cutoffs supported in the open entrance slab, equal to one on an
expanding spatial ball and an expanding closed time slab. -/
theorem exists_pairTwo_entrance_cutoff_exhaustion (T : ℝ) (hT : 0 < T) :
    ∃ η : ℕ → C_c(ℝ × Plane, ℝ),
      (∀ n p, η n p ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n, ∀ p ∈ tsupport (η n), 0 < p.1 ∧ p.1 < T) ∧
      (∀ (n : ℕ) (p : ℝ × Plane), T / ((n : ℝ) + 3) ≤ p.1 →
        p.1 ≤ T - T / ((n : ℝ) + 3) → ‖p.2‖ ≤ n → η n p = 1) ∧
      (∀ p : ℝ × Plane, 0 < p.1 → p.1 < T →
        ∀ᶠ n : ℕ in atTop, η n p = 1) := by
  classical
  let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 3)
  let K : ℕ → Set (ℝ × Plane) := fun n =>
    Set.Icc (δ n) (T - δ n) ×ˢ Metric.closedBall (0 : Plane) n
  have hδ (n : ℕ) : 0 < δ n := div_pos hT (by positivity)
  have hcompact (n : ℕ) : IsCompact (K n) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : Plane) n)
  have hsub (n : ℕ) : K n ⊆ Set.Ioo 0 T ×ˢ Set.univ := by
    intro p hp
    exact ⟨⟨lt_of_lt_of_le (hδ n) hp.1.1,
      lt_of_le_of_lt hp.1.2 (sub_lt_self T (hδ n))⟩, Set.mem_univ _⟩
  choose f hone hsupport hsubsupport hrange using fun n =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hcompact n)
      (isOpen_Ioo.prod isOpen_univ) (hsub n)
  let η : ℕ → C_c(ℝ × Plane, ℝ) := fun n => ⟨f n, hsupport n⟩
  refine ⟨η, hrange, ?_, ?_, ?_⟩
  · intro n p hp
    exact (hsubsupport n hp).1
  · intro n p hleft hright hnorm
    exact hone n ⟨⟨hleft, hright⟩, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm⟩
  · intro p hp0 hpT
    have hlim : Tendsto δ atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat T).comp (tendsto_add_atTop_nat 3)
      change Tendsto (fun n : ℕ => T / ((n + 3 : ℕ) : ℝ)) atTop (𝓝 0) at h
      simpa only [δ, Nat.cast_add, Nat.cast_ofNat] using h
    have hleft := hlim.eventually (Iio_mem_nhds hp0)
    have hright := hlim.eventually (Iio_mem_nhds (sub_pos.mpr hpT))
    have hnorm : ∀ᶠ n : ℕ in atTop, ‖p.2‖ ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop ‖p.2‖)
    filter_upwards [hleft, hright, hnorm] with n hnleft hnright hnnorm
    exact hone n ⟨⟨hnleft.le, by linarith only [hnright]⟩,
      by simpa only [Metric.mem_closedBall, dist_zero_right] using hnnorm⟩

end Critical2DKPZ.SHF.Moments
