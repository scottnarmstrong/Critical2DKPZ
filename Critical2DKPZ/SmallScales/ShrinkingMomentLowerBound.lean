/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.ThmToyJointConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-! # Lower semicontinuity of the normalized second moment under the KPZ scaling CLT -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.SmallScales

private theorem one_le_eLpNorm_id_standardGaussian :
    1 ≤ eLpNorm (id : ℝ → ℝ) 2 (gaussianReal 0 1) := by
  let γ : Measure ℝ := gaussianReal 0 1
  have hmem : MemLp (id : ℝ → ℝ) 2 γ :=
    ProbabilityTheory.memLp_id_gaussianReal 2
  have hvar : 1 = ∫ x : ℝ, x ^ 2 ∂γ := by
    calc
      1 = Var[id; γ] := (variance_id_gaussianReal (μ := 0) (v := 1)).symm
      _ = ∫ x : ℝ, (x - γ[id]) ^ 2 ∂γ :=
        variance_eq_integral (measurable_id'.aemeasurable)
      _ = ∫ x : ℝ, x ^ 2 ∂γ := by simp [γ, integral_id_gaussianReal]
  have hnorm : eLpNorm (id : ℝ → ℝ) 2 γ = 1 := by
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have hsq : ∫ x : ℝ, ‖id x‖ ^ (2 : ℝ) ∂γ = 1 := by
      calc
        ∫ x : ℝ, ‖id x‖ ^ (2 : ℝ) ∂γ = ∫ x : ℝ, x ^ 2 ∂γ := by
          apply integral_congr_ae
          filter_upwards [] with x
          simp [sq_abs]
        _ = 1 := hvar.symm
    have hsq' : ∫ x : ℝ, ‖id x‖ ^ ENNReal.toReal (2 : ENNReal) ∂γ = 1 := by
      have htoreal : ENNReal.toReal (2 : ENNReal) = 2 := by norm_num
      simpa only [htoreal] using hsq
    rw [hsq']
    norm_num
  simpa only [γ, hnorm] using (le_rfl : (1 : ENNReal) ≤ 1)

/-- A standard Gaussian limit forces the normalized L² norm to have lower limit at least one. -/
theorem eventually_eLpNorm_ge_of_tendstoInDistribution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (a : ℝ → ℝ)
    (hD : TendstoInDistribution (fun ε ω => Y ε ω / a ε)
      (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (gaussianReal 0 1))
    {b : ℝ} (hb₁ : b < 1) :
    ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0), ENNReal.ofReal b ≤
      eLpNorm (fun ω => Y ε ω / a ε) 2 P := by
  by_contra hnot
  have hfreq : ∃ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      eLpNorm (fun ω => Y ε ω / a ε) 2 P < ENNReal.ofReal b := by
    simpa only [Filter.Frequently, not_lt] using hnot
  let bad : Set ℝ := {ε | eLpNorm (fun ω => Y ε ω / a ε) 2 P < ENNReal.ofReal b}
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0) ⊓ 𝓟 bad
  have hne : NeBot l := by
    have hmem : ∃ᶠ ε in nhdsWithin 0 (Set.Ioi 0), ε ∈ bad := by
      simpa only [bad, Set.mem_ofPred_eq] using hfreq
    exact Filter.frequently_mem_iff_neBot.mp hmem
  obtain ⟨εseq, hseq⟩ := Filter.exists_seq_tendsto l
  have hseqWithin : Tendsto εseq atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    hseq.mono_right inf_le_left
  have hseqBad : ∀ᶠ n : ℕ in atTop, εseq n ∈ bad :=
    Filter.tendsto_principal.1 (hseq.mono_right inf_le_right)
  have hDseq : TendstoInDistribution (fun n ω => Y (εseq n) ω / a (εseq n)) atTop
      id (fun _ => P) (gaussianReal 0 1) := by
    refine ⟨fun n => hD.forall_aemeasurable (εseq n), hD.aemeasurable_limit, ?_⟩
    exact hD.tendsto.comp hseqWithin
  have hlim := Critical2DKPZ.JointConvergence.eLpNorm_two_le_liminf_of_tendstoInDistribution hDseq
  have hlim_le : atTop.liminf
      (fun n => eLpNorm (fun ω => Y (εseq n) ω / a (εseq n)) 2 P) ≤ ENNReal.ofReal b := by
    refine Filter.liminf_le_of_le (by isBoundedDefault) fun c hc => ?_
    obtain ⟨n, hcn, hnb⟩ := (hc.and hseqBad).exists
    change eLpNorm (fun ω => Y (εseq n) ω / a (εseq n)) 2 P < ENNReal.ofReal b at hnb
    exact hcn.trans (le_of_lt hnb)
  have hgauss := one_le_eLpNorm_id_standardGaussian
  have hcontr : (1 : ENNReal) ≤ ENNReal.ofReal b := hgauss.trans (hlim.trans hlim_le)
  have hbcast : ENNReal.ofReal b < 1 := by
    exact ENNReal.ofReal_lt_one.mpr hb₁
  exact (not_le_of_gt hbcast) hcontr

end Critical2DKPZ.SmallScales

end
