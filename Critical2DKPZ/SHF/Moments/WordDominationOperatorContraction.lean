/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPairOperatorContraction
public import Critical2DKPZ.MomentBounds.CCR25FreeOperatorBound
import Mathlib.Tactic

/-! # Critical contraction with uniform operator bounds -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Filter
open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Critical2DKPZ.Renewal
open Polymer

/-- At critical tuning, one choice of interacting and free operator constants gives a uniform contraction for all sufficiently large lattice scales. -/
theorem eventually_critical_pairOperator_word_contraction_with_bounds
    (h : ℕ) (hh : 3 ≤ h) (ϑ : ℝ) (B : ℕ) (hB : 1 ≤ B) :
    ∃ cI cQ lam : ℝ, 1 ≤ cI ∧ 1 ≤ cQ ∧ 1 ≤ lam ∧
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (∀ I : ReplicaPartition h, I ≠ ⊥ →
          |replicaPartitionDisorderMoment (Critical2DKPZ.criticalBeta ϑ N) I| ≤
            Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N)) ∧
        Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
          dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) < 1 ∧
        (1 + cI * (Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
            dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
              (1 - Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
                dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)))) *
          Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
            (Fintype.card (CollisionPair h) : ℝ) * (4 * cQ) < 1 / 4 ∧
        (∀ I : ReplicaPartition h, I ≠ ⊥ →
          ∀ L : ℕ, ∀ lam β : ℝ, 0 ≤ lam →
          (∀ J : ReplicaPartition h, J ≠ ⊥ →
            |replicaPartitionDisorderMoment β J| ≤ Polymer.sigmaSq β) →
          Polymer.sigmaSq β * dampedOverlap lam L < 1 →
          ∀ (s : Finset (LatticeConfiguration h)),
          ∀ (f : LatticeConfiguration h → ℝ),
            finiteLpNorm s 2 (finiteKernelApply s
              (weightedKernel (replicaExponentialWeight 0)
                (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤
              (1 + cI * (Polymer.sigmaSq β * dampedOverlap lam L /
                (1 - Polymer.sigmaSq β * dampedOverlap lam L))) *
                finiteLpNorm s 2 f) ∧
        (∀ L : ℕ, ∀ s : Finset (LatticeConfiguration h),
          ∀ I J : ReplicaPartition h, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
          ∀ f : LatticeConfiguration h → ℝ,
            finiteLpNorm s 2 (finiteKernelApply s
              (weightedKernel (replicaExponentialWeight 0)
                (hattedFreeReplicaKernel L I J)) f) ≤
              4 * cQ * finiteLpNorm s 2 f) := by
  obtain ⟨cI, hcI, hIop⟩ :=
    finiteLpNorm_weighted_hattedInteractingReplicaKernelAbs_le h (by omega)
  obtain ⟨cQ, hcQ, hQop⟩ :=
    finiteLpNorm_weighted_hattedFreeReplicaKernel_le h hh
  obtain ⟨σ₀, hσ₀, hMoments⟩ :=
    abs_replicaPartitionDisorderMoment_le_sigmaSq h
  let P : ℝ := max 1 (Fintype.card (CollisionPair h) : ℝ)
  let K : ℝ := P * (4 * cQ)
  let ε : ℝ := 1 / (8 * cI * K)
  have hPone : 1 ≤ P := by dsimp [P]; exact le_max_left _ _
  have hPnonneg : 0 ≤ P := le_trans (by norm_num) hPone
  have hcardP : (Fintype.card (CollisionPair h) : ℝ) ≤ P := by
    dsimp [P]
    exact le_max_right _ _
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨lam, hlam, N₁, hDamping⟩ :=
    eventually_critical_damped_resolvent_small_mul_horizon ϑ ε hε B hB
  let δ : ℝ := min σ₀ (1 / (8 * K))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min hσ₀ (by positivity)
  have hσsmall : ∀ᶠ N : ℕ in atTop,
      Critical2DKPZ.criticalSigmaSq ϑ N < δ := by
    have h := tendsto_order.mp (tendsto_sigma_zero ϑ)
    exact h.2 δ hδpos
  have hβspec : ∀ᶠ N : ℕ in atTop,
      Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) =
        Critical2DKPZ.criticalSigmaSq ϑ N := by
    filter_upwards [Critical2DKPZ.criticalBeta_spec ϑ] with N hN
    simpa [Polymer.sigmaSq] using hN
  have hN₀ : ∀ᶠ N : ℕ in atTop, N₁ ≤ N := eventually_ge_atTop N₁
  have hgood : ∀ᶠ N : ℕ in atTop,
      (∀ I : ReplicaPartition h, I ≠ ⊥ →
        |replicaPartitionDisorderMoment (Critical2DKPZ.criticalBeta ϑ N) I| ≤
          Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N)) ∧
      Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
        dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) < 1 ∧
      (1 + cI * (Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
          dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
            (1 - Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
              dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)))) *
        Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
          (Fintype.card (CollisionPair h) : ℝ) * (4 * cQ) < 1 / 4 := by
    filter_upwards [hσsmall, hβspec, hN₀, criticalSigmaSq_eventually_pos ϑ,
      eventually_ge_atTop 1] with N hσsmall hβ hN₀ hσpos hN1
    let σ : ℝ := Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N)
    let D : ℝ := dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)
    have hσeq : σ = Critical2DKPZ.criticalSigmaSq ϑ N := hβ
    have hσnonneg : 0 ≤ σ := by rw [hσeq]; exact hσpos.le
    have hσsmall' : σ < δ := by rw [hσeq]; exact hσsmall
    have hσleσ₀ : σ ≤ σ₀ := by
      have h := hσsmall'
      dsimp [δ] at h
      exact h.le.trans (min_le_left _ _)
    have hMom : ∀ I : ReplicaPartition h, I ≠ ⊥ →
        |replicaPartitionDisorderMoment (Critical2DKPZ.criticalBeta ϑ N) I| ≤ σ := by
      intro I hI
      exact hMoments (Critical2DKPZ.criticalBeta ϑ N) hσleσ₀ I hI
    have hres := hDamping N hN₀
    rcases hres with ⟨hσnonneg', hsmall, hratio⟩
    have hσnonneg'' : 0 ≤ σ := by rw [hσeq]; exact hσnonneg'
    have hsmall' : σ * D < 1 := by
      rw [hσeq]
      simpa [D] using hsmall
    have hDnonneg : 0 ≤ D := by
      dsimp [D, dampedOverlap]
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (Real.exp_nonneg _) (Critical2DKPZ.srwKernel_nonneg _ _)
    have hden : 0 < 1 - σ * D := sub_pos.mpr hsmall'
    have hratio' : σ * (σ * D / (1 - σ * D)) ≤ ε := by
      rw [hσeq]
      simpa [D] using hratio
    have hratioNonneg : 0 ≤ σ * D / (1 - σ * D) :=
      div_nonneg (mul_nonneg hσnonneg'' hDnonneg) hden.le
    have hsigK : σ * K < 1 / 8 := by
      have hδ' : σ < 1 / (8 * K) := by
        have hm := min_le_right σ₀ (1 / (8 * K))
        exact lt_of_lt_of_le hσsmall' hm
      calc
        σ * K < (1 / (8 * K)) * K := mul_lt_mul_of_pos_right hδ' hKpos
        _ = 1 / 8 := by field_simp
    have hcI0 : 0 ≤ cI := le_trans (by norm_num) hcI
    have hratioK : cI * (σ * (σ * D / (1 - σ * D))) * K ≤ 1 / 8 := by
      calc
        _ ≤ cI * ε * K := by
          have h₁ := mul_le_mul_of_nonneg_left hratio' hcI0
          exact mul_le_mul_of_nonneg_right h₁ hKpos.le
        _ = 1 / 8 := by dsimp [ε]; field_simp
    have hfactorNonneg : 0 ≤ 1 + cI * (σ * D / (1 - σ * D)) := by positivity
    have hcontraction :
        (1 + cI * (σ * D / (1 - σ * D))) * σ *
          (Fintype.card (CollisionPair h) : ℝ) * (4 * cQ) < 1 / 4 := by
      calc
        _ ≤ (1 + cI * (σ * D / (1 - σ * D))) * σ * P * (4 * cQ) := by
          have hleft : 0 ≤ (1 + cI * (σ * D / (1 - σ * D))) * σ :=
            mul_nonneg hfactorNonneg hσnonneg''
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcardP hleft) (by positivity)
        _ = σ * K + cI * (σ * (σ * D / (1 - σ * D))) * K := by
          dsimp [K]
          ring
        _ < 1 / 8 + 1 / 8 := add_lt_add_of_lt_of_le hsigK hratioK
        _ = 1 / 4 := by norm_num
    exact ⟨hMom, hsmall', by simpa [σ, D] using hcontraction⟩
  have hgoodOps : ∀ᶠ N : ℕ in atTop,
      (∀ I : ReplicaPartition h, I ≠ ⊥ →
        ∀ L : ℕ, ∀ lam β : ℝ, 0 ≤ lam →
        (∀ J : ReplicaPartition h, J ≠ ⊥ →
          |replicaPartitionDisorderMoment β J| ≤ Polymer.sigmaSq β) →
        Polymer.sigmaSq β * dampedOverlap lam L < 1 →
        ∀ (s : Finset (LatticeConfiguration h)),
        ∀ (f : LatticeConfiguration h → ℝ),
          finiteLpNorm s 2 (finiteKernelApply s
            (weightedKernel (replicaExponentialWeight 0)
              (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤
            (1 + cI * (Polymer.sigmaSq β * dampedOverlap lam L /
              (1 - Polymer.sigmaSq β * dampedOverlap lam L))) *
              finiteLpNorm s 2 f) ∧
      (∀ L : ℕ, ∀ s : Finset (LatticeConfiguration h),
        ∀ I J : ReplicaPartition h, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
        ∀ f : LatticeConfiguration h → ℝ,
          finiteLpNorm s 2 (finiteKernelApply s
            (weightedKernel (replicaExponentialWeight 0)
              (hattedFreeReplicaKernel L I J)) f) ≤
            4 * cQ * finiteLpNorm s 2 f) := by
    filter_upwards [hgood] with N hgoodN
    obtain ⟨hMom, hsmall, _⟩ := hgoodN
    have hI : ∀ I : ReplicaPartition h, I ≠ ⊥ →
        ∀ L : ℕ, ∀ lam β : ℝ, 0 ≤ lam →
        (∀ J : ReplicaPartition h, J ≠ ⊥ →
          |replicaPartitionDisorderMoment β J| ≤ Polymer.sigmaSq β) →
        Polymer.sigmaSq β * dampedOverlap lam L < 1 →
        ∀ (s : Finset (LatticeConfiguration h)),
        ∀ (f : LatticeConfiguration h → ℝ),
          finiteLpNorm s 2 (finiteKernelApply s
            (weightedKernel (replicaExponentialWeight 0)
              (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤
            (1 + cI * (Polymer.sigmaSq β * dampedOverlap lam L /
              (1 - Polymer.sigmaSq β * dampedOverlap lam L))) *
              finiteLpNorm s 2 f := by
      intro I hI L lam β hlam hβ hsmall' s f
      have hb := hIop 0 (by norm_num) L lam β hlam hβ hsmall' 2 (by norm_num)
        s I hI f
      simpa using hb
    have hQ : ∀ L : ℕ, ∀ s : Finset (LatticeConfiguration h),
        ∀ I J : ReplicaPartition h, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
        ∀ f : LatticeConfiguration h → ℝ,
          finiteLpNorm s 2 (finiteKernelApply s
            (weightedKernel (replicaExponentialWeight 0)
              (hattedFreeReplicaKernel L I J)) f) ≤
            4 * cQ * finiteLpNorm s 2 f := by
      intro L s I J hI hJ hIJ f
      have hb := hQop 0 (by norm_num) L 2 (by norm_num) s I J hI hJ hIJ f
      have heq : cQ * Real.exp (cQ * (0 : ℝ) ^ 2 * (L : ℝ)) * 2 *
          (2 / (2 - 1 : ℝ)) = 4 * cQ := by
        norm_num [Real.exp_zero]
        ring
      calc
        _ ≤ cQ * Real.exp (cQ * (0 : ℝ) ^ 2 * (L : ℝ)) * 2 *
            (2 / (2 - 1 : ℝ)) * finiteLpNorm s 2 f := hb
        _ = 4 * cQ * finiteLpNorm s 2 f := by rw [heq]
    exact ⟨hI, hQ⟩
  have hcombined : ∀ᶠ N : ℕ in atTop,
      ((∀ I : ReplicaPartition h, I ≠ ⊥ →
        |replicaPartitionDisorderMoment (Critical2DKPZ.criticalBeta ϑ N) I| ≤
          Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N)) ∧
       Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
         dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) < 1 ∧
       (1 + cI * (Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
           dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
             (1 - Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
               dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)))) *
         Polymer.sigmaSq (Critical2DKPZ.criticalBeta ϑ N) *
           (Fintype.card (CollisionPair h) : ℝ) * (4 * cQ) < 1 / 4) ∧
      (∀ I : ReplicaPartition h, I ≠ ⊥ →
        ∀ L : ℕ, ∀ lam β : ℝ, 0 ≤ lam →
        (∀ J : ReplicaPartition h, J ≠ ⊥ →
          |replicaPartitionDisorderMoment β J| ≤ Polymer.sigmaSq β) →
        Polymer.sigmaSq β * dampedOverlap lam L < 1 →
        ∀ (s : Finset (LatticeConfiguration h)),
        ∀ (f : LatticeConfiguration h → ℝ),
          finiteLpNorm s 2 (finiteKernelApply s
            (weightedKernel (replicaExponentialWeight 0)
              (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤
            (1 + cI * (Polymer.sigmaSq β * dampedOverlap lam L /
              (1 - Polymer.sigmaSq β * dampedOverlap lam L))) *
              finiteLpNorm s 2 f) ∧
      (∀ L : ℕ, ∀ s : Finset (LatticeConfiguration h),
        ∀ I J : ReplicaPartition h, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
        ∀ f : LatticeConfiguration h → ℝ,
          finiteLpNorm s 2 (finiteKernelApply s
            (weightedKernel (replicaExponentialWeight 0)
              (hattedFreeReplicaKernel L I J)) f) ≤
            4 * cQ * finiteLpNorm s 2 f) := by
    exact hgood.and hgoodOps
  refine ⟨cI, cQ, lam, hcI, hcQ, hlam,
    (eventually_atTop.1 hcombined).choose, ?_⟩
  intro N hN
  have hspec := (eventually_atTop.1 hcombined).choose_spec N hN
  rcases hspec with ⟨hg, ho⟩
  rcases hg with ⟨hm, hs, hc⟩
  rcases ho with ⟨hi, hq⟩
  exact ⟨hm, hs, hc, hi, hq⟩

end Critical2DKPZ.SHF.Moments

end
