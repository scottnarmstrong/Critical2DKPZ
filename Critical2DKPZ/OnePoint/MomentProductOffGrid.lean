/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.SecondMoment
import Mathlib.Tactic

/-! # Off-grid second-moment comparison -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology BigOperators

namespace Critical2DKPZ.OnePoint

/-- The smoothed second-moment difference over a short change of the starting time. Both second
moments are finite by `integrable_smoothedP2Plane_sq`. -/
theorem smoothedP2Plane_secondMoment_sub_le (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ s s' n : ℕ, s ≤ s' → s' ≤ n →
      0 < renewalGap (Critical2DKPZ.criticalBeta ϑ N) n →
        0 ≤ (∫ ω, smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N) s n 0 ω ^ 2 ∂disorderLaw) -
            ∫ ω, smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N) s' n 0 ω ^ 2 ∂disorderLaw ∧
        (∫ ω, smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N) s n 0 ω ^ 2 ∂disorderLaw) -
            ∫ ω, smoothedP2Plane (Critical2DKPZ.criticalBeta ϑ N) s' n 0 ω ^ 2 ∂disorderLaw ≤
          Real.pi * (replicaOverlap s' - replicaOverlap s) /
            renewalGap (Critical2DKPZ.criticalBeta ϑ N) n := by
  have hlog : ∀ᶠ N : ℕ in atTop, A < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop A
  filter_upwards [eventually_ge_atTop 1, hlog] with N hN hlog
  intro ϑ hϑ s s' n hss' hs'n hgap
  have hθabs : |ϑ| ≤ A := abs_le.mpr ⟨(Set.mem_Icc.mp hϑ).1, (Set.mem_Icc.mp hϑ).2⟩
  have hθlog : |ϑ| < Real.log (N : ℝ) := lt_of_le_of_lt hθabs hlog
  have hσpos : 0 < Critical2DKPZ.criticalSigmaSq ϑ N :=
    criticalSigmaSq_pos_of_abs_lt_log hN hθlog
  have hβpos : 0 < Critical2DKPZ.criticalBeta ϑ N := by
    unfold Critical2DKPZ.criticalBeta
    apply Real.sqrt_pos.2
    apply Real.log_pos
    linarith
  obtain ⟨_, hgapBounds⟩ := renewalGap_secondMoment_bounds
  let β := Critical2DKPZ.criticalBeta ϑ N
  let M := fun j : ℕ =>
    ∫ ω, smoothedP2Plane β j n 0 ω ^ 2 ∂disorderLaw
  have hformula (j : ℕ) (hjn : j ≤ n) :
      M j - 1 =
        ∑ k ∈ Finset.Icc (j + 1) n,
          Renewal.returnWeight k * (Polymer.sigmaSq β *
            ∫ ω, pointToPlane β 0 (n - k) 0 ω ^ 2 ∂disorderLaw) := by
    have h := Polymer.local_replica_formula β j n hjn (0 : Site) 0
    simp only [← pow_two] at h
    simpa [M, Renewal.returnWeight, mul_assoc] using h
  have hsplit : Finset.Icc (s + 1) n =
      Finset.Icc (s + 1) s' ∪ Finset.Icc (s' + 1) n := by
    ext k
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc (s + 1) s') (Finset.Icc (s' + 1) n) := by
    apply Finset.disjoint_left.mpr
    intro k hk₁ hk₂
    simp only [Finset.mem_Icc] at hk₁ hk₂
    omega
  have hsum :
      (∑ k ∈ Finset.Icc (s + 1) n,
        Renewal.returnWeight k * (Polymer.sigmaSq β *
          ∫ ω, pointToPlane β 0 (n - k) 0 ω ^ 2 ∂disorderLaw)) =
      (∑ k ∈ Finset.Icc (s + 1) s',
        Renewal.returnWeight k * (Polymer.sigmaSq β *
          ∫ ω, pointToPlane β 0 (n - k) 0 ω ^ 2 ∂disorderLaw)) +
      ∑ k ∈ Finset.Icc (s' + 1) n,
        Renewal.returnWeight k * (Polymer.sigmaSq β *
          ∫ ω, pointToPlane β 0 (n - k) 0 ω ^ 2 ∂disorderLaw) := by
    rw [hsplit, Finset.sum_union hdisj]
  have hdiff :
      M s - M s' =
        ∑ k ∈ Finset.Icc (s + 1) s',
          Renewal.returnWeight k * (Polymer.sigmaSq β *
            ∫ ω, pointToPlane β 0 (n - k) 0 ω ^ 2 ∂disorderLaw) := by
    have hFs := hformula s (le_trans hss' hs'n)
    have hFs' := hformula s' hs'n
    calc
      M s - M s' = (M s - 1) - (M s' - 1) := by ring
      _ = _ := by rw [hFs, hFs']
      _ = _ := by rw [hsum]; ring
  have hterm_nonneg (k : ℕ) (hk : k ∈ Finset.Icc (s + 1) s') :
      0 ≤ Renewal.returnWeight k * (Polymer.sigmaSq β *
        ∫ ω, pointToPlane β 0 (n - k) 0 ω ^ 2 ∂disorderLaw) := by
    have hq : 0 ≤ Renewal.returnWeight k := by
      exact Critical2DKPZ.srwKernel_nonneg (2 * k) 0
    have hσ : 0 ≤ Polymer.sigmaSq β := by
      unfold Polymer.sigmaSq
      exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
    exact mul_nonneg hq (mul_nonneg hσ (integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun ω => sq_nonneg (pointToPlane β 0 (n - k) 0 ω))))
  have hnonneg : 0 ≤ M s - M s' := by
    rw [hdiff]
    exact Finset.sum_nonneg fun k hk => hterm_nonneg k hk
  have hupper : M s - M s' ≤
      Real.pi * (replicaOverlap s' - replicaOverlap s) / renewalGap β n := by
    have hsumOverlap : replicaOverlap s' - replicaOverlap s =
        ∑ k ∈ Finset.Icc (s + 1) s', Renewal.returnWeight k :=
      replicaOverlap_sub_eq_sum s s' hss'
    rw [hdiff, hsumOverlap]
    have hsum_le :
        (∑ k ∈ Finset.Icc (s + 1) s',
          Renewal.returnWeight k * (Polymer.sigmaSq β *
            ∫ ω, pointToPlane β 0 (n - k) 0 ω ^ 2 ∂disorderLaw)) ≤
        ∑ k ∈ Finset.Icc (s + 1) s',
          Renewal.returnWeight k * (Real.pi / renewalGap β n) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_Icc.mp hk
      have hkn : k ≤ n := le_trans hk'.2 hs'n
      have hm : n - k ≤ n := Nat.sub_le _ _
      have hRdiff : 0 ≤ replicaOverlap n - replicaOverlap (n - k) := by
        rw [replicaOverlap_sub_eq_sum (n - k) n hm]
        exact Finset.sum_nonneg fun j hj => Critical2DKPZ.srwKernel_nonneg (2 * j) 0
      have hRm : replicaOverlap (n - k) ≤ replicaOverlap n :=
        sub_nonneg.mp hRdiff
      have hgapm : 0 < renewalGap β (n - k) := by
        have heq : renewalGap β (n - k) = renewalGap β n +
            Real.pi * (replicaOverlap n - replicaOverlap (n - k)) := by
          unfold renewalGap
          ring
        rw [heq]
        exact lt_of_lt_of_le hgap (le_add_of_nonneg_right
          (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hRm)))
      have hK := (hgapBounds β hβpos (n - k) hgapm).1
      have hpoint : Polymer.sigmaSq β *
          ∫ ω, pointToPlane β 0 (n - k) 0 ω ^ 2 ∂disorderLaw ≤
          Real.pi / renewalGap β (n - k) := by
        linarith
      have hden : renewalGap β n ≤ renewalGap β (n - k) := by
        have heq : renewalGap β (n - k) = renewalGap β n +
            Real.pi * (replicaOverlap n - replicaOverlap (n - k)) := by
          unfold renewalGap
          ring
        rw [heq]
        exact le_add_of_nonneg_right (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hRm))
      have hquot : Real.pi / renewalGap β (n - k) ≤ Real.pi / renewalGap β n :=
        div_le_div_of_nonneg_left Real.pi_pos.le hgap hden
      exact mul_le_mul_of_nonneg_left (hpoint.trans hquot)
        (Critical2DKPZ.srwKernel_nonneg (2 * k) 0)
    calc
      _ ≤ ∑ k ∈ Finset.Icc (s + 1) s',
          Renewal.returnWeight k * (Real.pi / renewalGap β n) := hsum_le
      _ = Real.pi / renewalGap β n *
          (∑ k ∈ Finset.Icc (s + 1) s', Renewal.returnWeight k) := by
            rw [← Finset.sum_mul]
            ring
      _ = _ := by ring
  exact ⟨by simpa [M] using hnonneg, by simpa [M, β] using hupper⟩

end Critical2DKPZ.OnePoint

end
