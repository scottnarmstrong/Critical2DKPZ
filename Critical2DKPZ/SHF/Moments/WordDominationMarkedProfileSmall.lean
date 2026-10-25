/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationWeightedBoundaryNorms
public import Critical2DKPZ.SHF.Moments.WordDominationWeightedHorizonContraction
public import Critical2DKPZ.SHF.Moments.WordDominationNonpairOperatorSeries
public import Critical2DKPZ.SHF.Moments.WordDominationMarkedWordBound
public import Critical2DKPZ.SHF.Moments.WordDominationNonpairMoment
public import Critical2DKPZ.MomentBounds.AiiKDisorderMoment
import Mathlib.Tactic

/-! # Uniform smallness of marked compact start-profile expansions -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Filter Critical2DKPZ.MomentBounds Critical2DKPZ.Renewal Polymer

/-- The marked start-profile expansion retains an arbitrary small factor,
uniformly in every microscopic duration in a fixed diffusive window. -/
theorem eventually_collisionWord_markedProfile_le_small_scale
    (h : ℕ) (hh : 3 ≤ h) (ϑ : ℝ) (B : ℕ) (hB : 1 ≤ B)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in atTop,
      ∀ L : ℕ, L ≤ B * N →
      (∑ x ∈ Fintype.piFinset (fun _ : Fin h => collisionWordScaledBallSites N R),
        ∑ I ∈ collisionWordMarkedPartitionSequences h L,
          (∏ j : Fin L, |replicaPartitionDisorderMoment (criticalBeta ϑ N) (I j)|) *
            replicaPathWeight (List.ofFn I) x) ≤ δ * C * (N : ℝ) ^ h := by
  classical
  obtain ⟨cI, cQ, hcI, hcQ, hoperators⟩ := exists_collisionWord_weightedOperator_constants h hh B
  obtain ⟨C0, hC0, hnorms⟩ := exists_collisionWord_weightedBoundary_norms h (by omega) B R hR
  let P : ℝ := 2 ^ (h * h)
  have hP : 1 ≤ P := one_le_pow₀ (by norm_num)
  obtain ⟨lam, hlam, hcontract⟩ :=
    eventually_critical_alphabet_contraction_all_horizons ϑ B hB cI cQ P hcI hcQ hP
  obtain ⟨σ0, hσ0, hmoment⟩ := abs_replicaPartitionDisorderMoment_le_sigmaSq h
  have hMom : ∀ᶠ N : ℕ in atTop, ∀ I : ReplicaPartition h, I ≠ ⊥ →
      |replicaPartitionDisorderMoment (criticalBeta ϑ N) I| ≤ sigmaSq (criticalBeta ϑ N) := by
    filter_upwards [(tendsto_order.mp (tendsto_sigma_zero ϑ)).2 σ0 hσ0,
      criticalBeta_spec ϑ] with N hσ hβ
    apply hmoment
    have heq : sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N := by
      simpa [sigmaSq] using hβ
    rw [heq]
    exact hσ.le
  refine ⟨Real.exp lam * C0, mul_nonneg (Real.exp_nonneg _) hC0, ?_⟩
  intro δ hδ
  filter_upwards [hcontract, hMom,
    eventually_nonpairPartitionDisorderMoment_le_epsilon_sigmaSq h ϑ δ hδ,
    eventually_ge_atTop 1] with N hcontract hMom hBad hN
  intro L hL
  let β := criticalBeta ϑ N
  let κ := lam / ((B * N : ℕ) : ℝ)
  let A := collisionWordScaledBallSites N R
  let S := configBox h A L
  let W := replicaExponentialWeight ((Real.sqrt (N : ℝ))⁻¹) (h := h)
  let f : Site → ℝ := fun y => if y ∈ A then 1 else 0
  let u := fun I : ReplicaPartition h => hattedReplicaBoundaryVector L I A f
  let v := collisionIndicator (h := h)
  let σ := sigmaSq β
  let D := dampedOverlap κ L
  let cU := 1 + cI * (σ * D / (1 - σ * D))
  have hσ : 0 ≤ σ := sigmaSq_nonneg β
  have hD : 0 ≤ D := by
    unfold D dampedOverlap
    exact Finset.sum_nonneg (fun r hr => mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg _ _))
  have hsmall := hcontract L hL
  have hden : 0 < 1 - σ * D := by change 0 < 1 - sigmaSq β * dampedOverlap κ L; linarith [hsmall.1]
  have hcU : 0 ≤ cU := by dsimp [cU]; positivity
  have hκ : 0 ≤ κ := div_nonneg (zero_le_one.trans hlam) (Nat.cast_nonneg _)
  obtain ⟨left, right, hleft, hright, hleftBound, hrightBound, hproduct⟩ := hnorms hN hL S
  have hf : ∀ y, 0 ≤ f y := by intro y; dsimp [f]; split_ifs <;> norm_num
  have hu : ∀ I x, 0 ≤ u I x := fun I x =>
    hattedReplicaBoundaryVector_nonneg L I A f (fun y hy => hf y) x
  have hv : ∀ I x, 0 ≤ v I x := by
    intro I x
    by_cases hx : IsCollisionConfiguration I x <;> simp [v, collisionIndicator, hx]
  have hops := hoperators hN hL κ β hκ hMom hsmall.1
  have hratio : (cU * σ * P) * cQ < 1 / 4 := hsmall.2
  have hratio1 : (cU * σ * P) * cQ < 1 := by linarith
  have hpq : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hseries := collisionWord_nonpair_word_operator_series_bound S L κ β W
    (fun x hx => replicaExponentialWeight_pos _ _) hpq u v hu hv
    (replicaPartitionDisorderMoment β) σ δ cU cQ left right hσ hδ.le hMom hBad
    hcU (zero_le_one.trans hcQ) hleft hright hleftBound hrightBound
    (fun I hI f => hops.1 S I hI f)
    (fun I J hI hJ hIJ f => hops.2 S I J hI hJ hIJ f) hratio1
  have hA0 : 0 ≤ cU * σ * P := by positivity
  have hAle : cU * σ * P ≤ (cU * σ * P) * cQ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hcQ hA0
  have hseriesSmall :
      (δ * left * right) * (cU * σ * P) / (1 - (cU * σ * P) * cQ) ≤ δ * left * right := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - (cU * σ * P) * cQ)).mpr
    have hcoef : 0 ≤ δ * left * right := by positivity
    have ha : cU * σ * P ≤ 1 - (cU * σ * P) * cQ := by linarith
    exact mul_le_mul_of_nonneg_left ha hcoef
  have hκL : κ * L ≤ lam := by
    have hBN : (0 : ℝ) < (B * N : ℕ) := by exact_mod_cast (show 0 < B * N by positivity)
    calc
      _ ≤ κ * (B * N : ℕ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hL) hκ
      _ = lam := by dsimp [κ]; field_simp
  have hprofile := collisionWord_markedPartitionSum_le_wordRuns (h := h) (L := L) β κ hκ A f hf
  have hprofile' :
      (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
        ∑ I ∈ collisionWordMarkedPartitionSequences h L,
          (∏ j : Fin L, |replicaPartitionDisorderMoment β (I j)|) * replicaPathWeight (List.ofFn I) x) ≤
      Real.exp (κ * L) * (δ * left * right) := by
    have hprofileEq : (∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
        (∏ i : Fin h, f (x i)) *
          ∑ I ∈ collisionWordMarkedPartitionSequences h L,
            (∏ j : Fin L, |replicaPartitionDisorderMoment β (I j)|) * replicaPathWeight (List.ofFn I) x) =
        ∑ x ∈ Fintype.piFinset (fun _ : Fin h => A),
          ∑ I ∈ collisionWordMarkedPartitionSequences h L,
            (∏ j : Fin L, |replicaPartitionDisorderMoment β (I j)|) * replicaPathWeight (List.ofFn I) x := by
      apply Finset.sum_congr rfl
      intro x hx
      have hx' := Fintype.mem_piFinset.mp hx
      simp [f, hx']
    rw [hprofileEq] at hprofile
    exact hprofile.trans (mul_le_mul_of_nonneg_left
      (hseries.trans hseriesSmall) (Real.exp_nonneg _))
  calc
    _ ≤ Real.exp (κ * L) * (δ * left * right) := hprofile'
    _ ≤ Real.exp lam * (δ * (C0 * (N : ℝ) ^ h)) := by
      apply mul_le_mul (Real.exp_le_exp.mpr hκL)
        (by nlinarith only [mul_le_mul_of_nonneg_left hproduct hδ.le])
        (by positivity) (Real.exp_nonneg _)
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments

end
