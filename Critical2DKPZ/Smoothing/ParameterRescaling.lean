/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.CriticalBeta
public import Critical2DKPZ.PolymerCalculus.ClockTuningAlong
import Mathlib.Tactic

/-! # Exact critical-parameter rescaling over comparable integer horizons -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Critical2DKPZ.Smoothing

/-- Solve the variance equation at the new integer horizon. -/
def rescaledCriticalParameter (ϑ : ℝ) (N M : ℕ) : ℝ :=
  Real.log M * (criticalSigmaSq ϑ N * replicaOverlap M - 1)

/-- The re-solved parameter preserves the exact disorder variance. -/
theorem criticalSigmaSq_rescaledParameter (ϑ : ℝ) (N : ℕ) {M : ℕ} (hM : 2 ≤ M) :
    criticalSigmaSq (rescaledCriticalParameter ϑ N M) M = criticalSigmaSq ϑ N := by
  have hlog : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < M by omega))).ne'
  have hR : replicaOverlap M ≠ 0 := (replicaOverlap_pos (by omega)).ne'
  change (1 + rescaledCriticalParameter ϑ N M / Real.log M) / replicaOverlap M = _
  unfold rescaledCriticalParameter
  field_simp
  ring

/-- The re-solved parameter stays in a fixed compact interval, uniformly over all
integer horizons in a fixed comparable window. -/
theorem exists_rescaledCriticalParameter_bound (A a b : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Icc (-A) A, ∀ M : ℕ,
      a * N ≤ M → (M : ℝ) ≤ b * N → |rescaledCriticalParameter ϑ N M| ≤ C := by
  classical
  let B := max b a
  let L := max |Real.log a| |Real.log B|
  let C := |A| + L + 1
  refine ⟨C, ?_⟩
  by_contra hnot
  have hfreq : ∃ᶠ N : ℕ in atTop, ¬ ∀ ϑ ∈ Icc (-A) A, ∀ M : ℕ,
      a * N ≤ M → (M : ℝ) ≤ b * N → |rescaledCriticalParameter ϑ N M| ≤ C := by
    simpa only [Filter.Frequently, not_not] using hnot
  have hbad : ∃ᶠ N : ℕ in atTop, ∃ ϑ ∈ Icc (-A) A, ∃ M : ℕ,
      a * N ≤ M ∧ (M : ℝ) ≤ b * N ∧ C < |rescaledCriticalParameter ϑ N M| := by
    apply hfreq.mono
    intro N hN
    push Not at hN
    exact hN
  obtain ⟨Ns, hNs, hbadNs⟩ := frequently_iff_seq_forall.mp
    (hbad.and_eventually (eventually_ge_atTop 1))
  choose θ hθ M hlo hhi hval using fun n => (hbadNs n).1
  have hNpos (n : ℕ) : (0 : ℝ) < Ns n := by exact_mod_cast (show 0 < Ns n by have := (hbadNs n).2; omega)
  let p : ℕ → ℝ × ℝ := fun n => ((M n : ℝ) / Ns n, θ n)
  have hp (n : ℕ) : p n ∈ Icc a B ×ˢ Icc (-|A|) |A| := by
    refine ⟨⟨(le_div_iff₀ (hNpos n)).mpr (hlo n), ?_⟩, ⟨?_, ?_⟩⟩
    · exact ((div_le_iff₀ (hNpos n)).mpr (hhi n)).trans (le_max_left _ _)
    · exact (neg_le_neg (le_abs_self A)).trans (hθ n).1
    · exact (hθ n).2.trans (le_abs_self A)
  obtain ⟨q, hq, φ, hφ, hφlim⟩ := (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hp
  have hD : 0 < q.1 := ha.trans_le hq.1.1
  have hratio : Tendsto (fun n => (M (φ n) : ℝ) / Ns (φ n)) atTop (𝓝 q.1) :=
    (continuous_fst.tendsto q).comp hφlim
  have hθlim : Tendsto (fun n => θ (φ n)) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hφlim
  have htune := PolymerCalculus.tendsto_critical_clock_tuning_along hD
    (hNs.comp hφ.tendsto_atTop) hratio hθlim
  have hretune : Tendsto (fun n => rescaledCriticalParameter (θ (φ n)) (Ns (φ n)) (M (φ n)))
      atTop (𝓝 (q.2 + Real.log q.1)) := by
    have h := htune.add (hθlim.add_const (Real.log q.1))
    simp only [zero_add] at h
    convert h using 1
    funext n
    dsimp only [rescaledCriticalParameter, Function.comp_apply]
    ring
  have hlimbad : C ≤ |q.2 + Real.log q.1| := ge_of_tendsto' hretune.abs (fun n => (hval (φ n)).le)
  have hθabs : |q.2| ≤ |A| := abs_le.mpr hq.2
  have hloglo : Real.log a ≤ Real.log q.1 := Real.log_le_log ha hq.1.1
  have hloghi : Real.log q.1 ≤ Real.log B := Real.log_le_log hD hq.1.2
  have hlogabs : |Real.log q.1| ≤ L := by
    apply abs_le.mpr
    constructor
    · have hl := neg_abs_le (Real.log a)
      have hm : |Real.log a| ≤ L := le_max_left _ _
      linarith only [hl, hm, hloglo]
    · have hl := le_abs_self (Real.log B)
      have hm : |Real.log B| ≤ L := le_max_right _ _
      linarith only [hl, hm, hloghi]
  have hu : |q.2 + Real.log q.1| ≤ |A| + L :=
    (abs_add_le _ _).trans (add_le_add hθabs hlogabs)
  dsimp only [C] at hlimbad
  linarith only [hlimbad, hu]

/-- Exact inverse retuning is uniform over comparable integer horizons. -/
theorem criticalBeta_rescale (A a b : ℝ) (ha : 0 < a) :
    ∃ A' : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ M : ℕ, a * N ≤ M → (M : ℝ) ≤ b * N →
      ∃ ϑ' ∈ Set.Icc (-A') A', criticalBeta ϑ N = criticalBeta ϑ' M := by
  obtain ⟨C, hC⟩ := exists_rescaledCriticalParameter_bound A a b ha
  have hlarge : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ a * N :=
    ((tendsto_natCast_atTop_atTop.const_mul_atTop ha).eventually (eventually_ge_atTop 2))
  refine ⟨C, ?_⟩
  filter_upwards [hC, hlarge] with N hbound hNlarge
  intro ϑ hϑ M hlo hhi
  have hM : 2 ≤ M := by exact_mod_cast hNlarge.trans hlo
  refine ⟨rescaledCriticalParameter ϑ N M, abs_le.mp (hbound ϑ hϑ M hlo hhi), ?_⟩
  unfold criticalBeta
  rw [criticalSigmaSq_rescaledParameter ϑ N hM]

end Critical2DKPZ.Smoothing

end
