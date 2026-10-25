/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Chaos
public import Critical2DKPZ.Definitions.ReplicaOverlap
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! # Exponential sums at the critical overlap scale

In the proof of CSZ25 Lemma 5.4, the exponential sum uses the same replica overlap as the critical reparametrization. -/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata.CSZ25

private theorem exp_le_reciprocal {x : ℝ} (hx : x < 1) :
    Real.exp x ≤ 1 / (1 - x) := by
  have hp : 0 < 1 - x := sub_pos.mpr hx
  apply (Real.le_log_iff_exp_le (one_div_pos.mpr hp)).mp
  rw [Real.log_div one_ne_zero hp.ne', Real.log_one, zero_sub]
  have hl := Real.log_le_sub_one_of_pos hp
  linarith only [hl]

/-- The critical overlap reparametrization gives the exponential-sum lower bound used in CSZ25 Lemma 5.4. -/
theorem csz25_30_corrected_exponential_sum (L K : ℕ) (β θ : ℝ)
    (hθ : 0 ≤ θ) (hθR : θ < replicaOverlap L)
    (hpara : Polymer.sigmaSq β * replicaOverlap L =
      1 / (1 - θ / replicaOverlap L)) :
    (1 / 2 : ℝ) * (∑ k ∈ Finset.Icc 1 K,
      Real.exp (θ / replicaOverlap L * (k : ℝ))) ≤
      (1 / 2 : ℝ) * (∑ k ∈ Finset.Icc 1 K,
        (Polymer.sigmaSq β * replicaOverlap L) ^ k) := by
  have hR : 0 < replicaOverlap L := hθ.trans_lt hθR
  have hx : θ / replicaOverlap L < 1 := (div_lt_one hR).mpr hθR
  have hb : Real.exp (θ / replicaOverlap L) ≤ Polymer.sigmaSq β * replicaOverlap L := by
    rw [hpara]
    exact exp_le_reciprocal hx
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro k _hk
  rw [mul_comm (θ / replicaOverlap L), Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hb k

end Critical2DKPZ.Errata.CSZ25
