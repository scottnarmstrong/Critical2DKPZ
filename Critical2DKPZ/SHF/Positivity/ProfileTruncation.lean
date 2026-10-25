/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25AssemblyLemmas
public import Critical2DKPZ.Polymer.Series
import Mathlib.Tactic

/-! # Finite-box approximation of a summable polymer profile -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.SHF.Positivity

/-- Finite-box start profiles increase to a summable nonnegative profile almost surely; their
masses converge to the full mass. -/
theorem profileP2Fun_box_truncation (β : ℝ) (a b : ℕ) (ν : Site → ℝ)
    (hν0 : ∀ w, 0 ≤ ν w) (hνsum : Summable ν) :
    Tendsto (fun n : ℕ => ∑ w ∈ MomentBounds.boxSites n, ν w) atTop (𝓝 (∑' w, ν w)) ∧
    (∀ᵐ ω ∂disorderLaw,
      Tendsto (fun n : ℕ => profileP2Fun β a b
        ((↑(MomentBounds.boxSites n) : Set Site).indicator ν) (fun _ => 1) ω)
        atTop (𝓝 (profileP2Fun β a b ν (fun _ => 1) ω))) ∧
    ∀ n, ∀ᵐ ω ∂disorderLaw,
      profileP2Fun β a b ((↑(MomentBounds.boxSites n) : Set Site).indicator ν)
        (fun _ => 1) ω ≤ profileP2Fun β a b ν (fun _ => 1) ω := by
  classical
  let F : Disorder → ℝ := profileP2Fun β a b ν (fun _ => 1)
  let φn (n : ℕ) : Site → ℝ :=
    (↑(MomentBounds.boxSites n) : Set Site).indicator ν
  let Fn (n : ℕ) : Disorder → ℝ := profileP2Fun β a b (φn n) (fun _ => 1)
  let massn (n : ℕ) : ℝ := ∑ z ∈ MomentBounds.boxSites n, ν z
  have hνabs : Summable (fun z => |ν z|) := by
    simpa only [abs_of_nonneg (hν0 _)] using hνsum
  have hbox := MomentBounds.tendsto_boxSites_atTop
  have hmass : Tendsto massn atTop (𝓝 (∑' z, ν z)) := by
    have ht : Tendsto (fun A : Finset Site => ∑ z ∈ A, ν z) atTop (𝓝 (∑' z, ν z)) :=
      hνsum.hasSum
    change Tendsto (fun n : ℕ => ∑ z ∈ MomentBounds.boxSites n, ν z) atTop _
    have hseq : (fun n : ℕ => ∑ z ∈ MomentBounds.boxSites n, ν z) =
        (fun A : Finset Site => ∑ z ∈ A, ν z) ∘ MomentBounds.boxSites := by
      funext n
      rfl
    rw [hseq]
    exact ht.comp hbox
  have hFn_sum (n : ℕ) (ω : Disorder) :
      Fn n ω = ∑ z ∈ MomentBounds.boxSites n, ν z * pointToPlane β a (b - a) z ω := by
    have hsupp : ∀ z ∉ MomentBounds.boxSites n, φn n z = 0 := by
      intro z hz
      simp [φn, hz]
    rw [show Fn n = profileP2Fun β a b (φn n) (fun _ => 1) by rfl,
      Polymer.profileP2Fun_eq_sum β a b (φn n) (fun _ => 1)
        (MomentBounds.boxSites n) hsupp ω]
    simp only [mul_one, Polymer.tsum_pointToPoint]
    apply Finset.sum_congr rfl
    intro z hz
    rw [show φn n z = ν z by
      dsimp [φn]
      exact Set.indicator_of_mem (Finset.mem_coe.mpr hz) ν]
  have hF_series (ω : Disorder) :
      F ω = ∑' z, ν z * pointToPlane β a (b - a) z ω := by
    simp only [F, profileP2Fun]
    simp_rw [mul_one, Polymer.tsum_pointToPoint]
  have htermnorm :
      (∑' z : Site, eLpNorm (fun ω => ν z * pointToPlane β a (b - a) z ω)
        (1 : ℝ≥0∞) disorderLaw) ≠ ⊤ := by
    simpa only [mul_one, Polymer.tsum_pointToPoint] using
      Polymer.profile_term_norms_ne_top β a b ν (fun _ => 1) hνabs 1 (by norm_num)
        (by intro z; norm_num) 1 (by simp)
  have hterms_ae : ∀ᵐ ω ∂disorderLaw,
      Summable (fun z => ‖ν z * pointToPlane β a (b - a) z ω‖) :=
    MeasureTheory.summable_norm_of_tsum_eLpNorm_ne_top (p := 1) (by norm_num) htermnorm
  have hpointwise : ∀ᵐ ω ∂disorderLaw,
      Tendsto (fun n => Fn n ω) atTop (𝓝 (F ω)) := by
    filter_upwards [hterms_ae] with ω hω
    have hs := hω.of_norm.hasSum
    change Tendsto (fun A : Finset Site =>
        ∑ z ∈ A, ν z * pointToPlane β a (b - a) z ω) atTop
        (𝓝 (∑' z, ν z * pointToPlane β a (b - a) z ω)) at hs
    have htc := hs.comp hbox
    have hseq : (fun n : ℕ => Fn n ω) =
        (fun A : Finset Site => ∑ z ∈ A, ν z * pointToPlane β a (b - a) z ω) ∘
          MomentBounds.boxSites := by
      funext n
      rw [hFn_sum]
      rfl
    rw [hseq, hF_series]
    exact htc
  have hFn_le_F : ∀ n, ∀ᵐ ω ∂disorderLaw, Fn n ω ≤ F ω := by
    intro n
    filter_upwards [hterms_ae] with ω hω
    rw [hFn_sum, hF_series]
    exact hω.of_norm.sum_le_tsum (MomentBounds.boxSites n)
      (fun z _ => mul_nonneg (hν0 z) (Polymer.pointToPlane_pos β a (b - a) z ω).le)
  refine ⟨?_, ?_, ?_⟩
  · simpa only [massn] using hmass
  · simpa only [F, Fn, φn] using hpointwise
  · intro n
    simpa only [F, Fn, φn] using hFn_le_F n

end Critical2DKPZ.SHF.Positivity

end
