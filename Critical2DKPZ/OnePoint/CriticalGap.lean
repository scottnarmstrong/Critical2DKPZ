/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.RenewalGap
public import Critical2DKPZ.Renewal.CriticalWindow
public import Critical2DKPZ.Lattice.Basic
import Mathlib.Tactic

/-! # The critical renewal gap is logarithmic uniformly on compact parameters -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Critical2DKPZ.OnePoint

/-- The critical variance is positive above the logarithmic cutoff. -/
theorem criticalSigmaSq_pos_of_abs_lt_log {ϑ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hlog : |ϑ| < Real.log (N : ℝ)) : 0 < Critical2DKPZ.criticalSigmaSq ϑ N := by
  have hLpos : 0 < Real.log (N : ℝ) := lt_of_le_of_lt (abs_nonneg ϑ) hlog
  have hθlower : -Real.log (N : ℝ) < ϑ :=
    lt_of_lt_of_le (neg_lt_neg hlog) (neg_abs_le ϑ)
  have hnum : 0 < 1 + ϑ / Real.log (N : ℝ) := by
    have hdiv : -1 < ϑ / Real.log (N : ℝ) :=
      (lt_div_iff₀ hLpos).2 (by nlinarith only [hθlower])
    linarith
  unfold Critical2DKPZ.criticalSigmaSq
  exact div_pos hnum (Critical2DKPZ.replicaOverlap_pos hN)

/-- Pointwise form of the critical coupling identity above the logarithmic cutoff. -/
theorem criticalBeta_spec_of_abs_lt_log {ϑ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hlog : |ϑ| < Real.log (N : ℝ)) :
    Real.exp (criticalBeta ϑ N ^ 2) - 1 = Critical2DKPZ.criticalSigmaSq ϑ N := by
  have hσ := criticalSigmaSq_pos_of_abs_lt_log hN hlog
  have harg : 0 < 1 + Critical2DKPZ.criticalSigmaSq ϑ N := by linarith
  unfold criticalBeta
  rw [Real.sq_sqrt (Real.log_nonneg (by linarith [hσ]))]
  rw [Real.exp_log harg]
  ring

/-- Uniform critical-window asymptotics for the one-point renewal gap. -/
theorem renewalGap_criticalBeta_sub_log_bounded (A : ℝ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ t : ℕ, t ≤ N →
      |renewalGap (criticalBeta ϑ N) t -
        Real.log ((N : ℝ) / ((max t 1 : ℕ) : ℝ))| ≤ C := by
  obtain ⟨K, hK⟩ := Critical2DKPZ.replicaOverlap_log_bound
  obtain ⟨D, hD⟩ := replicaOverlap_sub_log_bounded
  have hKnonneg : 0 ≤ K := le_trans (abs_nonneg _) (hK 1 (by omega))
  refine ⟨2 * A * (1 + Real.pi * K) + D, ?_⟩
  have hlogEvent : ∀ᶠ N : ℕ in atTop,
      2 * |A| + 2 < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop _
  filter_upwards [eventually_ge_atTop 2, hlogEvent] with N hN hlog
  intro ϑ hϑ t htN
  have hN1 : 1 ≤ N := by omega
  have hA0 : 0 ≤ A := by linarith only [hϑ.1, hϑ.2]
  have hθabs : |ϑ| ≤ A := abs_le.mpr ⟨hϑ.1, hϑ.2⟩
  have hLpos : 0 < Real.log (N : ℝ) := by
    have hbase : 0 < 2 * |A| + 2 := by positivity
    exact lt_trans hbase hlog
  have hLone : 1 ≤ Real.log (N : ℝ) := by
    have h := hlog
    have hAabs : 0 ≤ |A| := abs_nonneg A
    linarith
  have hθL : -Real.log (N : ℝ) < ϑ := by
    have hθle : -A ≤ ϑ := hϑ.1
    have hlogA : A < Real.log (N : ℝ) := by
      have hAabs : A = |A| := (abs_of_nonneg hA0).symm
      rw [hAabs]
      linarith
    linarith
  have hnum : 0 < 1 + ϑ / Real.log (N : ℝ) := by
    have hdiv : -1 < ϑ / Real.log (N : ℝ) :=
      (lt_div_iff₀ hLpos).2 (by nlinarith only [hθL])
    linarith
  have hsigpos : 0 < Critical2DKPZ.criticalSigmaSq ϑ N := by
    unfold Critical2DKPZ.criticalSigmaSq
    exact div_pos hnum (Critical2DKPZ.replicaOverlap_pos hN1)
  have hθupper : ϑ < Real.log (N : ℝ) := by
    have hlogA : A < Real.log (N : ℝ) := by
      have hAabs : A = |A| := (abs_of_nonneg hA0).symm
      rw [hAabs]
      linarith
    exact lt_of_le_of_lt hϑ.2 hlogA
  have hθAbsLog : |ϑ| < Real.log (N : ℝ) := abs_lt.mpr ⟨hθL, hθupper⟩
  have hspec := criticalBeta_spec_of_abs_lt_log hN1 hθAbsLog
  have hsigma : Polymer.sigmaSq (criticalBeta ϑ N) =
      Critical2DKPZ.criticalSigmaSq ϑ N := by
    exact hspec
  have hdenpos : 0 < 1 + ϑ / Real.log (N : ℝ) := hnum
  have hdenhalf : (1 / 2 : ℝ) < 1 + ϑ / Real.log (N : ℝ) := by
    have hθabsL : |ϑ| < Real.log (N : ℝ) / 2 := by
      have hAabs : A = |A| := (abs_of_nonneg hA0).symm
      have hlog' := hlog
      rw [← hAabs] at hlog'
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith only [hθabs, hlog']
    have hθlower : -|ϑ| / Real.log (N : ℝ) ≤ ϑ / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right (neg_abs_le ϑ) hLpos.le
    have hθlower' : -( |ϑ| / Real.log (N : ℝ)) ≤ ϑ / Real.log (N : ℝ) := by
      simpa only [neg_div] using hθlower
    have hratio : |ϑ| / Real.log (N : ℝ) < 1 / 2 :=
      (div_lt_iff₀ hLpos).2 (by nlinarith only [hθabsL])
    linarith only [hθlower', hratio]
  have hRpos : 0 < replicaOverlap N := Critical2DKPZ.replicaOverlap_pos hN1
  have hsigEq : Polymer.sigmaSq (criticalBeta ϑ N) =
      (1 + ϑ / Real.log (N : ℝ)) / replicaOverlap N := by
    rw [hsigma]
    rfl
  have hratio : Real.pi / Polymer.sigmaSq (criticalBeta ϑ N) =
      (Real.pi * replicaOverlap N) / (1 + ϑ / Real.log (N : ℝ)) := by
    rw [hsigEq]
    field_simp [ne_of_gt hRpos, ne_of_gt hdenpos]
  have hRerror : |Real.pi * replicaOverlap N - Real.log (N : ℝ)| ≤ Real.pi * K := by
    have h := hK N hN1
    have heq : Real.pi * replicaOverlap N - Real.log (N : ℝ) =
        Real.pi * (replicaOverlap N - (1 / Real.pi) * Real.log N) := by
      rw [mul_sub]
      field_simp
    rw [heq, abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left h Real.pi_pos.le
  have hpiK : 0 ≤ Real.pi * K := mul_nonneg Real.pi_pos.le hKnonneg
  have hUabs : |Real.pi * replicaOverlap N| ≤
      Real.log (N : ℝ) + Real.pi * K := by
    have heq : Real.pi * replicaOverlap N =
        (Real.pi * replicaOverlap N - Real.log (N : ℝ)) + Real.log (N : ℝ) := by ring
    rw [heq]
    calc
      |(Real.pi * replicaOverlap N - Real.log (N : ℝ)) + Real.log (N : ℝ)|
          ≤ |Real.pi * replicaOverlap N - Real.log (N : ℝ)| +
              |Real.log (N : ℝ)| := abs_add_le _ _
      _ ≤ Real.pi * K + Real.log (N : ℝ) := by
        rw [abs_of_pos hLpos]
        exact add_le_add hRerror le_rfl
      _ = _ := by ring
  have hUdiv : |Real.pi * replicaOverlap N| / Real.log (N : ℝ) ≤ 1 + Real.pi * K := by
    apply (div_le_iff₀ hLpos).2
    calc
      |Real.pi * replicaOverlap N| ≤ Real.log (N : ℝ) + Real.pi * K := hUabs
      _ ≤ (1 + Real.pi * K) * Real.log (N : ℝ) := by
        have hprod : Real.pi * K ≤ Real.pi * K * Real.log (N : ℝ) :=
          by simpa only [mul_one] using mul_le_mul_of_nonneg_left hLone hpiK
        calc
          _ = Real.log (N : ℝ) + Real.pi * K := by ring
          _ ≤ Real.log (N : ℝ) + Real.pi * K * Real.log (N : ℝ) :=
            add_le_add le_rfl hprod
          _ = (1 + Real.pi * K) * Real.log (N : ℝ) := by ring
  have hAupper : 0 ≤ A := hA0
  have hBnonneg : 0 ≤ 1 + Real.pi * K := by linarith
  have hsumpos : 0 < Real.log (N : ℝ) + ϑ := by
    have heq : Real.log (N : ℝ) + ϑ =
        Real.log (N : ℝ) * (1 + ϑ / Real.log (N : ℝ)) := by
      field_simp [ne_of_gt hLpos]
    rw [heq]
    exact mul_pos hLpos hdenpos
  have hgapFirst :
      |Real.pi / Polymer.sigmaSq (criticalBeta ϑ N) -
        Real.pi * replicaOverlap N| ≤ 2 * A * (1 + Real.pi * K) := by
    have heq : Real.pi / Polymer.sigmaSq (criticalBeta ϑ N) -
        Real.pi * replicaOverlap N =
        -(Real.pi * replicaOverlap N * (ϑ / Real.log (N : ℝ))) /
          (1 + ϑ / Real.log (N : ℝ)) := by
      rw [hratio]
      have hdenform : 1 + ϑ / Real.log (N : ℝ) =
          (Real.log (N : ℝ) + ϑ) / Real.log (N : ℝ) := by
        field_simp [ne_of_gt hLpos]
      rw [hdenform]
      field_simp [ne_of_gt hLpos, ne_of_gt hsumpos]
      ring
    rw [heq, abs_div, abs_neg, abs_mul, abs_div,
      abs_of_pos hLpos, abs_of_pos hdenpos]
    have htop :
        |Real.pi * replicaOverlap N| * (|ϑ| / Real.log (N : ℝ)) ≤
          (1 + Real.pi * K) * A := by
      have hmul := mul_le_mul hUdiv hθabs (abs_nonneg ϑ) hBnonneg
      rw [div_mul_eq_mul_div] at hmul
      calc
        |Real.pi * replicaOverlap N| * (|ϑ| / Real.log (N : ℝ)) =
            (|Real.pi * replicaOverlap N| * |ϑ|) / Real.log (N : ℝ) := by
              rw [← mul_div_assoc]
        _ ≤ (1 + Real.pi * K) * A := hmul
    have hdenmul :
        (1 + Real.pi * K) * A ≤
          (2 * A * (1 + Real.pi * K)) * (1 + ϑ / Real.log (N : ℝ)) := by
      calc
        _ = (2 * A * (1 + Real.pi * K)) * (1 / 2) := by ring
        _ ≤ (2 * A * (1 + Real.pi * K)) *
            (1 + ϑ / Real.log (N : ℝ)) :=
          mul_le_mul_of_nonneg_left hdenhalf.le
            (mul_nonneg (mul_nonneg (by norm_num) hAupper) hBnonneg)
    apply (div_le_iff₀ hdenpos).2
    calc
      |Real.pi * replicaOverlap N| * (|ϑ| / Real.log (N : ℝ))
          ≤ (1 + Real.pi * K) * A := htop
      _ ≤ (2 * A * (1 + Real.pi * K)) * (1 + ϑ / Real.log (N : ℝ)) := hdenmul
  have hdiff := hD t N htN
  have hmaxN : max N 1 = N := max_eq_left (by omega)
  have hdiff' :
      |Real.pi * (replicaOverlap N - replicaOverlap t) -
        Real.log ((N : ℝ) / ((max t 1 : ℕ) : ℝ))| ≤ D := by
    simpa only [hmaxN] using hdiff
  have hsplit :
      renewalGap (criticalBeta ϑ N) t -
        Real.log ((N : ℝ) / ((max t 1 : ℕ) : ℝ)) =
      (Real.pi / Polymer.sigmaSq (criticalBeta ϑ N) -
          Real.pi * replicaOverlap N) +
        (Real.pi * (replicaOverlap N - replicaOverlap t) -
          Real.log ((N : ℝ) / ((max t 1 : ℕ) : ℝ))) := by
    unfold renewalGap
    ring
  rw [hsplit]
  calc
    |(Real.pi / Polymer.sigmaSq (criticalBeta ϑ N) -
        Real.pi * replicaOverlap N) +
        (Real.pi * (replicaOverlap N - replicaOverlap t) -
          Real.log ((N : ℝ) / ((max t 1 : ℕ) : ℝ)))|
      ≤ |Real.pi / Polymer.sigmaSq (criticalBeta ϑ N) -
          Real.pi * replicaOverlap N| +
        |Real.pi * (replicaOverlap N - replicaOverlap t) -
          Real.log ((N : ℝ) / ((max t 1 : ℕ) : ℝ))| := abs_add_le _ _
    _ ≤ 2 * A * (1 + Real.pi * K) + D := add_le_add hgapFirst hdiff'

end Critical2DKPZ.OnePoint
