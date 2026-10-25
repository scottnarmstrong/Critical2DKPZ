/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.HelperGeometry
public import Critical2DKPZ.FutureProfiles.Basic
public import Critical2DKPZ.MomentBounds.BlockClockBounds
public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.OnePoint.RenewalGap
import Mathlib.Tactic

/-! # Future-energy estimates along the geometric block clock -/

@[expose] public section

open Filter Set MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks

/-- The future energy of the walk kernel at a geometric block time grows at most linearly in the
remaining number of blocks. -/
theorem futureEnergy_srwKernel_blockTime_le (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ s : ℕ, 1 ≤ s → s ≤ blockCount N ρ →
        futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
            (fun y => srwKernel (blockTime N ρ s) y) ≤
          C * ((blockCount N ρ : ℝ) + 1 - s) := by
  obtain ⟨Csec, hsec⟩ := OnePoint.smoothedP2Plane_secondMoment_le_uniform A 1
  obtain ⟨Coverlap, hoverlap⟩ := OnePoint.replicaOverlap_sub_log_bounded
  have hCoverlap : 0 ≤ Coverlap := by
    have h := hoverlap 1 1 (by omega)
    exact le_trans (abs_nonneg _) h
  obtain ⟨Cclock, hclock⟩ := log_div_blockTime_le ρ₀ ρ₁ hρ
  let Csec' := max Csec 0
  let Cclock' := max Cclock 0
  let Dcoef := (Cclock' + Coverlap) / Real.pi
  let C := 1 + Csec' * Dcoef / Real.log 2
  have hCsec' : 0 ≤ Csec' := le_max_right _ _
  have hCclock' : 0 ≤ Cclock' := le_max_right _ _
  have hDcoef : 0 ≤ Dcoef := by
    dsimp [Dcoef]
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C, ?_⟩
  intro ρ hρmem
  have hρ' : 1 < ρ := lt_of_lt_of_le hρ hρmem.1
  filter_upwards [hsec, hclock ρ hρmem, blockTime_monotone hρ', eventually_ge_atTop 2]
    with N hsecN hclockN hmonN hN
  intro ϑ hϑ s hs hsK
  let K := blockCount N ρ
  let T := blockTime N ρ s
  have hK : 1 ≤ K := by dsimp [K, blockCount]; omega
  have hgap : 1 ≤ (K : ℝ) + 1 - (s : ℝ) := by
    have hsK' : (s : ℝ) ≤ (K : ℝ) := by exact_mod_cast hsK
    linarith
  have hTle : T ≤ N := by
    have hle := hmonN hsK
    have hterminal : blockTime N ρ K = N := by
      simp [blockTime, K, Nat.ne_of_gt (by omega : 0 < blockCount N ρ)]
    rw [hterminal] at hle
    exact hle
  have hTpos : 1 ≤ T := by
    by_cases hsInterior : s < blockCount N ρ
    · have hscale := MomentBounds.blockTime_lower_geometric_scale hρ' hs hsInterior
      have hpos : 0 < (blockTime N ρ s : ℝ) :=
        lt_of_lt_of_le (Real.rpow_pos_of_pos (by linarith : 0 < ρ) _) hscale
      have : 0 < blockTime N ρ s := by exact_mod_cast hpos
      omega
    · have hT : T = N := by
        dsimp [T]
        have hs0 : s ≠ 0 := by omega
        simp [blockTime, hs0, hsInterior]
      rw [hT]
      omega
  have hDnonneg : 0 ≤ replicaOverlap N - replicaOverlap T := by
    rw [OnePoint.replicaOverlap_sub_eq_sum T N hTle]
    apply Finset.sum_nonneg
    intro r _
    dsimp [Renewal.returnWeight]
    exact srwKernel_nonneg _ _
  have hlogratio :
      Real.log ((N : ℝ) / (T : ℝ)) ≤ Cclock' * ((K : ℝ) + 1 - (s : ℝ)) := by
    have hbase := hclockN s hs hsK
    have hle : Cclock ≤ Cclock' := le_max_left _ _
    calc
      Real.log ((N : ℝ) / (T : ℝ)) ≤ Cclock * ((K : ℝ) + 1 - (s : ℝ)) := by
        simpa [K, T] using hbase
      _ ≤ Cclock' * ((K : ℝ) + 1 - (s : ℝ)) :=
        mul_le_mul_of_nonneg_right hle (by linarith)
  have hOverlapLog := hoverlap T N hTle
  have hOverlapLog' :
      |Real.pi * (replicaOverlap N - replicaOverlap T) -
          Real.log ((N : ℝ) / (T : ℝ))| ≤ Coverlap := by
    simpa [show max N 1 = N by omega, show max T 1 = T by omega] using hOverlapLog
  have hDlog : Real.pi * (replicaOverlap N - replicaOverlap T) ≤
      Real.log ((N : ℝ) / (T : ℝ)) + Coverlap := by
    have := (abs_le.mp hOverlapLog').2
    linarith
  have hDupper :
      replicaOverlap N - replicaOverlap T ≤ Dcoef * ((K : ℝ) + 1 - (s : ℝ)) := by
    have hlogPlus : Real.log ((N : ℝ) / (T : ℝ)) + Coverlap ≤
          (Cclock' + Coverlap) * ((K : ℝ) + 1 - (s : ℝ)) := by
      calc
        _ ≤ Cclock' * ((K : ℝ) + 1 - (s : ℝ)) + Coverlap :=
          add_le_add hlogratio (le_refl Coverlap)
        _ ≤ (Cclock' + Coverlap) * ((K : ℝ) + 1 - (s : ℝ)) := by
          have hgap' : 1 ≤ (K : ℝ) + 1 - (s : ℝ) := hgap
          nlinarith [mul_nonneg hCoverlap (sub_nonneg.mpr hgap')]
    have hprod : (replicaOverlap N - replicaOverlap T) * Real.pi ≤
        (Cclock' + Coverlap) * ((K : ℝ) + 1 - (s : ℝ)) := by
      calc
        _ ≤ Real.log ((N : ℝ) / (T : ℝ)) + Coverlap := by
          simpa [mul_comm] using hDlog
        _ ≤ (Cclock' + Coverlap) * ((K : ℝ) + 1 - (s : ℝ)) := hlogPlus
    have hdiv : replicaOverlap N - replicaOverlap T ≤
        ((Cclock' + Coverlap) * ((K : ℝ) + 1 - (s : ℝ))) / Real.pi :=
      (le_div_iff₀ Real.pi_pos).2 (by simpa [mul_comm] using hprod)
    calc
      _ ≤ ((Cclock' + Coverlap) * ((K : ℝ) + 1 - (s : ℝ))) / Real.pi := hdiv
      _ = Dcoef * ((K : ℝ) + 1 - (s : ℝ)) := by dsimp [Dcoef]; ring
  have hsmoothed := hsecN ϑ hϑ T N (by simpa [T] using hTle)
    (by omega) (by simp)
  have hNrealpos : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hden : Real.log (1 + (N : ℝ) / N) = Real.log 2 := by
    congr 1
    field_simp
    norm_num
  rw [hden] at hsmoothed
  have henergy :
      futureEnergy (criticalBeta ϑ N) T N (fun y => srwKernel T y) =
        ∫ ω, smoothedP2Plane (criticalBeta ϑ N) T N 0 ω ^ 2 ∂disorderLaw := by
    unfold futureEnergy
    apply integral_congr_ae
    filter_upwards [] with ω
    simpa using congrArg (fun z : ℝ => z ^ 2)
      (Polymer.profileP2Fun_srw_flat (criticalBeta ϑ N) T N 0 ω)
  rw [henergy]
  have hCsec_le : Csec ≤ Csec' := le_max_left _ _
  calc
    (∫ ω, smoothedP2Plane (criticalBeta ϑ N) T N 0 ω ^ 2 ∂disorderLaw) ≤
        1 + Csec' * (replicaOverlap N - replicaOverlap T) / Real.log 2 := by
      calc
        _ ≤ 1 + Csec * (replicaOverlap N - replicaOverlap T) / Real.log 2 := by
          exact hsmoothed
        _ ≤ _ := by
          have hcoeff := div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCsec_le hDnonneg) hlog2.le
          simpa [add_comm] using add_le_add_left hcoeff (1 : ℝ)
    _ ≤ C * ((K : ℝ) + 1 - (s : ℝ)) := by
      dsimp [C]
      have hmul : 0 ≤ Csec' * Dcoef / Real.log 2 := by positivity
      have hbound := mul_le_mul_of_nonneg_left hDupper hCsec'
      have hbound' := div_le_div_of_nonneg_right hbound hlog2.le
      calc
        1 + Csec' * (replicaOverlap N - replicaOverlap T) / Real.log 2 ≤
            1 + Csec' * (Dcoef * ((K : ℝ) + 1 - (s : ℝ))) / Real.log 2 :=
          by simpa [add_comm] using add_le_add_left hbound' (1 : ℝ)
        _ = 1 + (Csec' * Dcoef / Real.log 2) * ((K : ℝ) + 1 - (s : ℝ)) := by ring
        _ ≤ (1 + Csec' * Dcoef / Real.log 2) * ((K : ℝ) + 1 - (s : ℝ)) := by
          nlinarith [mul_nonneg hmul (sub_nonneg.mpr (by linarith :
            0 ≤ (K : ℝ) + 1 - (s : ℝ) - 1))]

end Critical2DKPZ.FutureProfiles

end
