/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25MomentBoundFour
public import Critical2DKPZ.MomentBounds.CCR25GaussianSixthSeries
import Mathlib.Tactic

/-! # Sixth-order CCR moment-bound assembly -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- The full-support word-run estimate at the sixth moment order. -/
theorem wordRunsBound_six : WordRunsBound 6 := by
  intro β lam hlam L φ A hφ hA
  exact abs_centeredMoment_profileP2Fun_le_wordRuns
    (h := 6) (by norm_num) β lam hlam L φ A hφ hA

private lemma ccrMomentBoundSix_holderAlgebra {p q : ℝ} (hpq : p.HolderConjugate q) :
    1 < p ∧ 1 < q ∧ p = q / (q - 1) ∧ p / (p - 1) = q ∧ 1 ≤ p * q := by
  have hp1 : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  have hq1 : 1 < q := by
    have hformula : q = p / (p - 1) :=
      (Real.holderConjugate_iff_eq_conjExponent hp1).mp hpq
    rw [hformula]
    apply (lt_div_iff₀ (sub_pos.mpr hp1)).2
    simpa only [one_mul] using sub_lt_self p zero_lt_one
  have hpqFormula : p = q / (q - 1) :=
    (Real.holderConjugate_iff_eq_conjExponent hq1).mp hpq.symm
  have hpOver : p / (p - 1) = q := by
    rw [hpqFormula]
    field_simp [ne_of_gt (sub_pos.mpr hq1)]
    ring
  have hHone : 1 ≤ p * q :=
    one_le_mul_of_one_le_of_one_le (le_of_lt hp1) (le_of_lt hq1)
  exact ⟨hp1, hq1, hpqFormula, hpOver, hHone⟩

private lemma ccrMomentBoundSix_timeScale (t ℓ : ℝ) (ht : 0 < t) (htL : t ^ 2 ≤ ℓ) :
    0 < ℓ ∧ 0 < t / Real.sqrt ℓ ∧ t / Real.sqrt ℓ ≤ 1 ∧
      (t / Real.sqrt ℓ) ^ 2 * ℓ = t ^ 2 := by
  have hℓpos : 0 < ℓ := by
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    exact lt_of_lt_of_le ht2 htL
  have htwpos : 0 < t / Real.sqrt ℓ := div_pos ht (Real.sqrt_pos.2 hℓpos)
  have htwLeOne : t / Real.sqrt ℓ ≤ 1 := by
    have hsqrtT : t ≤ Real.sqrt ℓ := by
      calc
        t = Real.sqrt (t ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
        _ ≤ Real.sqrt ℓ := Real.sqrt_le_sqrt htL
    exact (div_le_one (Real.sqrt_pos.2 hℓpos)).2 hsqrtT
  have htw2 : (t / Real.sqrt ℓ) ^ 2 * ℓ = t ^ 2 := by
    rw [div_pow, Real.sq_sqrt hℓpos.le]
    field_simp
  exact ⟨hℓpos, htwpos, htwLeOne, htw2⟩

private lemma ccrMomentBoundSix_lambdaScale (lam ℓ : ℝ) (hlam : 0 ≤ lam) (hℓ : 0 < ℓ) :
    0 ≤ lam / ℓ ∧ (lam / ℓ) * ℓ = lam := by
  constructor
  · exact div_nonneg hlam hℓ.le
  · field_simp [ne_of_gt hℓ]

private lemma ccrMomentBoundSix_constantAbsorption
    (cColl q H M : ℝ) (hcColl : 1 ≤ cColl) (hq1 : 1 < q)
    (hqleH : q ≤ H) (hM : 0 ≤ M) :
    q * cColl ^ ((5 : ℝ) / q) * M ≤ cColl ^ 5 * M * H := by
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hnum : (5 : ℝ) ≤ 5 * q := by
    calc
      5 = 5 * 1 := by ring
      _ ≤ 5 * q := mul_le_mul_of_nonneg_left (le_of_lt hq1) (by norm_num)
  have hexp : (5 : ℝ) / q ≤ 5 := (div_le_iff₀ hqpos).2 hnum
  have hpowCollR : cColl ^ ((5 : ℝ) / q) ≤ cColl ^ (5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hcColl hexp
  have hpowColl : cColl ^ ((5 : ℝ) / q) ≤ cColl ^ (5 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact hpowCollR
  have hpowNonneg : 0 ≤ cColl ^ ((5 : ℝ) / q) :=
    Real.rpow_nonneg (zero_le_one.trans hcColl) _
  have hHnonneg : 0 ≤ H := zero_le_one.trans (le_trans (le_of_lt hq1) hqleH)
  have hfactor : q * cColl ^ ((5 : ℝ) / q) ≤ cColl ^ 5 * H := by
    calc
      _ ≤ H * cColl ^ ((5 : ℝ) / q) :=
        mul_le_mul_of_nonneg_right hqleH hpowNonneg
      _ ≤ H * cColl ^ 5 := mul_le_mul_of_nonneg_left hpowColl hHnonneg
      _ = cColl ^ 5 * H := by ring
  calc
    _ = (q * cColl ^ ((5 : ℝ) / q)) * M := by ring
    _ ≤ (cColl ^ 5 * H) * M := mul_le_mul_of_nonneg_right hfactor hM
    _ = cColl ^ 5 * M * H := by ring

private lemma ccrMomentBoundSix_boundaryApplication
    {cB : ℝ}
    (hBop : ∀ (t : ℝ), 0 ≤ t → ∀ (L : ℕ) (p : ℝ), 1 < p →
      ∀ (A : Finset Site) (f : Site → ℝ), (∀ y, 0 ≤ f y) →
      ∀ (s : Finset (LatticeConfiguration 6)) (I : ReplicaPartition 6), I ≠ ⊥ →
        finiteLpNorm s p
          (fun x => hattedReplicaBoundaryVector L I A f x /
            replicaExponentialWeight t x) ≤
          cB * Real.exp (cB * t ^ 2 * L) * (p / (p - 1)) *
            (∑ y ∈ A, f y * Real.exp (t * ‖siteToPlane y‖)) *
            finiteLpNorm A p
              (fun y => f y * Real.exp (t * ‖siteToPlane y‖)) ^ 5)
    (tw : ℝ) (htw : 0 ≤ tw) (L : ℕ) (p q : ℝ) (hp : 1 < p) (A : Finset Site)
    (φ : Site → ℝ) (hφ : ∀ y, 0 ≤ φ y) (s : Finset (LatticeConfiguration 6))
    (I : ReplicaPartition 6) (hI : I ≠ ⊥)
    (hpOver : p / (p - 1) = q) :
    finiteLpNorm s p
      (fun x => hattedReplicaBoundaryVector L I A φ x /
        replicaExponentialWeight tw x) ≤
      cB * Real.exp (cB * tw ^ 2 * (L : ℝ)) * q *
        (∑ y ∈ A, φ y * Real.exp (tw * ‖siteToPlane y‖)) *
        finiteLpNorm A p
          (fun y => φ y * Real.exp (tw * ‖siteToPlane y‖)) ^ 5 := by
  have h := hBop tw htw L p hp A φ hφ s I hI
  rw [hpOver] at h
  exact h

private lemma ccrMomentBoundSix_collisionApplication
    {cColl : ℝ}
    (hColl : ∀ (h : ℕ) (t : ℝ), 0 < t → t ≤ 1 → ∀ q : ℝ, 1 ≤ q →
      ∀ (s : Finset (LatticeConfiguration h)) (J : ReplicaPartition h), J ≠ ⊥ →
        finiteLpNorm s q
          (fun x => replicaExponentialWeight t x * collisionIndicator J x) ≤
          (cColl / t ^ 2) ^ (((h : ℝ) - 1) / q))
    (tw : ℝ) (htw : 0 < tw) (htwLeOne : tw ≤ 1) (q : ℝ)
    (hq : 1 ≤ q) (s : Finset (LatticeConfiguration 6)) (I : ReplicaPartition 6)
    (hI : I ≠ ⊥) :
    finiteLpNorm s q
      (fun x => replicaExponentialWeight tw x * collisionIndicator I x) ≤
      (cColl / tw ^ 2) ^ ((5 : ℝ) / q) := by
  have h := hColl 6 tw htw htwLeOne q hq s I hI
  norm_num at h
  exact h

private lemma ccrMomentBoundSix_interactingApplication
    {cI : ℝ}
    (hIop : ∀ (t : ℝ), 0 ≤ t → ∀ (L : ℕ) (lam β : ℝ), 0 ≤ lam →
      (∀ I : ReplicaPartition 6, I ≠ ⊥ →
        |replicaPartitionDisorderMoment β I| ≤ Polymer.sigmaSq β) →
      Polymer.sigmaSq β * dampedOverlap lam L < 1 → ∀ q : ℝ, 1 < q →
      ∀ (s : Finset (LatticeConfiguration 6)) (I : ReplicaPartition 6), I ≠ ⊥ →
      ∀ f : LatticeConfiguration 6 → ℝ,
        finiteLpNorm s q (finiteKernelApply s
          (weightedKernel (replicaExponentialWeight t)
            (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤
          (1 + cI * Real.exp (cI * t ^ 2 * L) *
            (Polymer.sigmaSq β * dampedOverlap lam L /
              (1 - Polymer.sigmaSq β * dampedOverlap lam L))) *
            finiteLpNorm s q f)
    (tw : ℝ) (htw : 0 ≤ tw) (L : ℕ) (lam β : ℝ) (hlam : 0 ≤ lam)
    (hMom : ∀ I : ReplicaPartition 6, I ≠ ⊥ →
      |replicaPartitionDisorderMoment β I| ≤ Polymer.sigmaSq β)
    (hsmall : Polymer.sigmaSq β * dampedOverlap lam L < 1) (q : ℝ)
    (hq : 1 < q) (s : Finset (LatticeConfiguration 6))
    (I : ReplicaPartition 6) (hI : I ≠ ⊥) (f : LatticeConfiguration 6 → ℝ) :
    finiteLpNorm s q (finiteKernelApply s
      (weightedKernel (replicaExponentialWeight tw)
        (ccr25LabelKernel L lam β (.interacting I))) f) ≤
      (1 + cI * Real.exp (cI * tw ^ 2 * L) *
        (Polymer.sigmaSq β * dampedOverlap lam L /
          (1 - Polymer.sigmaSq β * dampedOverlap lam L))) *
        finiteLpNorm s q f := by
  have h := hIop tw htw L lam β hlam hMom hsmall q hq s I hI f
  change finiteLpNorm s q (finiteKernelApply s
      (weightedKernel (replicaExponentialWeight tw)
        (hattedInteractingReplicaKernelAbs L lam β I)) f) ≤ _
  exact h

private lemma ccrMomentBoundSix_freeApplication
    {cQ : ℝ}
    (hQop : ∀ (t : ℝ), 0 ≤ t → ∀ (L : ℕ) (q : ℝ), 1 < q →
      ∀ (s : Finset (LatticeConfiguration 6)) (I J : ReplicaPartition 6),
        I ≠ ⊥ → J ≠ ⊥ → I ≠ J → ∀ f : LatticeConfiguration 6 → ℝ,
          finiteLpNorm s q (finiteKernelApply s
            (weightedKernel (replicaExponentialWeight t)
              (hattedFreeReplicaKernel L I J)) f) ≤
            cQ * Real.exp (cQ * t ^ 2 * L) * q * (q / (q - 1)) *
              finiteLpNorm s q f)
    (lam β tw : ℝ) (htw : 0 ≤ tw) (L : ℕ) (q p : ℝ) (hq : 1 < q)
    (hpqFormula : p = q / (q - 1)) (s : Finset (LatticeConfiguration 6))
    (I J : ReplicaPartition 6) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (hIJ : I ≠ J)
    (f : LatticeConfiguration 6 → ℝ) :
    finiteLpNorm s q (finiteKernelApply s
      (weightedKernel (replicaExponentialWeight tw)
        (ccr25LabelKernel L lam β (.free I J))) f) ≤
      cQ * Real.exp (cQ * tw ^ 2 * L) * (p * q) * finiteLpNorm s q f := by
  have h := hQop tw htw L q hq s I J hI hJ hIJ f
  change finiteLpNorm s q (finiteKernelApply s
      (weightedKernel (replicaExponentialWeight tw)
        (hattedFreeReplicaKernel L I J)) f) ≤
      cQ * Real.exp (cQ * tw ^ 2 * L) * (p * q) * finiteLpNorm s q f
  calc
    _ ≤ cQ * Real.exp (cQ * tw ^ 2 * L) * q * (q / (q - 1)) *
        finiteLpNorm s q f := h
    _ = cQ * Real.exp (cQ * tw ^ 2 * L) * (p * q) * finiteLpNorm s q f := by
      rw [← hpqFormula]
      ring

private lemma ccrMomentBoundSix_geometricRunSum
    (β lam lamw : ℝ) (hlamw : 0 ≤ lamw) (L : ℕ) (φ : Site → ℝ) (A : Finset Site)
    (hφ : ∀ z, 0 ≤ φ z) (hA : ∀ z ∉ A, φ z = 0)
    (left right A0 sig cQval : ℝ) (hW : WordRunsBound 6)
    (F : ℕ → ℝ) (hFnonneg : ∀ n, 0 ≤ F n)
    (hRun : Summable F ∧
      (∑' n, F n) ≤ left * right *
        (A0 * sig ^ 3 + A0 ^ 2 * cQval * sig ^ 3 +
          A0 ^ 3 * cQval ^ 2 * sig ^ 3 /
            (1 - (A0 * sig) * cQval)))
    (hFiniteEq :
      (∑ n ∈ Finset.range L, ∑ J ∈ ccr25AdmissibleWords 6 n,
        (∏ j, |replicaPartitionDisorderMoment β (J j)|) *
          ccr25FiniteWordPairing (configBox 6 A L) L lamw β J
            (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator) =
        ∑ n ∈ Finset.range L, F n)
    (hlamwL : lamw * (L : ℝ) = lam) :
    |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ 6 ∂disorderLaw| ≤
      Real.exp lam * (left * right *
        (A0 * sig ^ 3 + A0 ^ 2 * cQval * sig ^ 3 +
          A0 ^ 3 * cQval ^ 2 * sig ^ 3 /
            (1 - (A0 * sig) * cQval))) := by
  have hword := hW β lamw hlamw L φ A hφ hA
  have hsumle : ∑ n ∈ Finset.range L, F n ≤ ∑' n, F n :=
    hRun.1.sum_le_tsum (Finset.range L) (fun n hn => hFnonneg n)
  calc
    _ ≤ Real.exp (lamw * (L : ℝ)) *
        (∑ n ∈ Finset.range L, ∑ J ∈ ccr25AdmissibleWords 6 n,
          (∏ j, |replicaPartitionDisorderMoment β (J j)|) *
            ccr25FiniteWordPairing (configBox 6 A L) L lamw β J
              (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator) := hword
    _ = Real.exp lam * ∑ n ∈ Finset.range L, F n := by rw [hlamwL, hFiniteEq]
    _ ≤ Real.exp lam * ∑' n, F n :=
      mul_le_mul_of_nonneg_left hsumle (Real.exp_nonneg _)
    _ ≤ Real.exp lam *
        (left * right *
          (A0 * sig ^ 3 + A0 ^ 2 * cQval * sig ^ 3 +
            A0 ^ 3 * cQval ^ 2 * sig ^ 3 /
              (1 - (A0 * sig) * cQval))) := by
      have hrunShape :
          (∑' n, F n) ≤ left * right *
            (A0 * sig ^ 3 + A0 ^ 2 * cQval * sig ^ 3 +
              A0 ^ 3 * cQval ^ 2 * sig ^ 3 /
                (1 - (A0 * sig) * cQval)) := by
        calc
          _ ≤ left * right *
              (A0 * sig ^ 3 + A0 ^ 2 * cQval * sig ^ 3 +
                A0 ^ 3 * cQval ^ 2 * sig ^ 3 /
                  (1 - (A0 * sig) * cQval)) := hRun.2
          _ = _ := by ring
      exact mul_le_mul_of_nonneg_left hrunShape (Real.exp_nonneg _)

/-- The sixth-order word-run expansion implies the CSZ25 sixth-moment bound. -/
theorem ccrMomentBound_six_of_wordRuns (hW : WordRunsBound 6) : CCRMomentBound 6 := by
  classical
  obtain ⟨cB, hcB, hBop⟩ := finiteLpNorm_hattedReplicaBoundaryVector_le 6 (by omega)
  obtain ⟨cI, hcI, hIop⟩ := finiteLpNorm_weighted_hattedInteractingReplicaKernelAbs_le 6 (by omega)
  obtain ⟨cQ, hcQ, hQop⟩ := finiteLpNorm_weighted_hattedFreeReplicaKernel_le 6 (by omega)
  obtain ⟨σm, hσm, hMoments⟩ := abs_replicaPartitionDisorderMoment_le_sigmaSq 6
  obtain ⟨cColl, hcColl, hColl⟩ := finiteLpNorm_weight_mul_collisionIndicator_le
  let Bgauss : ℝ := (max 1 (ccr25GaussianMomentUniformConstant 6)) ^ 6 * (2 ^ 36 : ℝ)
  have hBgauss : 1 ≤ Bgauss := by
    dsimp [Bgauss]
    have h1 : 1 ≤ max 1 (ccr25GaussianMomentUniformConstant 6) := le_max_left _ _
    have hpow : 1 ≤ (max 1 (ccr25GaussianMomentUniformConstant 6)) ^ 6 :=
      one_le_pow₀ h1
    exact one_le_mul_of_one_le_of_one_le hpow (by norm_num)
  intro t ht
  let EU : ℝ := cI * Real.exp (cI * t ^ 2)
  let EQ : ℝ := cQ * Real.exp (cQ * t ^ 2)
  let Abar : ℝ := Bgauss * (1 + EU)
  let K : ℝ := Abar * EQ
  let σ₀ : ℝ := min σm 1
  let Cbase : ℝ := cB * Real.exp (cB * t ^ 2) * cColl ^ 5 *
    (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2)
  have hEU : 0 ≤ EU := by dsimp [EU]; positivity
  have hEQone : 1 ≤ EQ := by
    dsimp [EQ]
    have hcQ1 : 1 ≤ cQ := hcQ
    have hexp : 1 ≤ Real.exp (cQ * t ^ 2) := by
      apply Real.one_le_exp_iff.mpr
      positivity
    exact one_le_mul_of_one_le_of_one_le hcQ1 hexp
  have hAbarone : 1 ≤ Abar := by
    dsimp [Abar]
    have hsum : 1 ≤ 1 + EU := by
      calc
        1 = 0 + 1 := by ring
        _ ≤ EU + 1 := add_le_add_left hEU 1
        _ = 1 + EU := by ring
    exact one_le_mul_of_one_le_of_one_le hBgauss hsum
  have hKone : 1 ≤ K := by
    dsimp [K]
    exact one_le_mul_of_one_le_of_one_le hAbarone hEQone
  have hσ₀pos : 0 < σ₀ := lt_min hσm (by norm_num)
  have hCbasepos : 0 < Cbase := by
    dsimp [Cbase]
    have hcBpos : 0 < cB := lt_of_lt_of_le (by norm_num) hcB
    have hcCollpos : 0 < cColl := lt_of_lt_of_le (by norm_num) hcColl
    positivity
  refine ⟨σ₀, K, hσ₀pos, lt_of_lt_of_le (by norm_num) hKone, ?_⟩
  intro lam hlam
  let C : ℝ := Real.exp lam * Cbase
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCpos, ?_⟩
  intro β hβ L htL hσD p q hpq hsmall φ A hφ hA
  let sig : ℝ := Polymer.sigmaSq β
  let D : ℝ := dampedOverlap (lam / L) L
  let den : ℝ := 1 - sig * D
  let tw : ℝ := t / Real.sqrt L
  let lamw : ℝ := lam / L
  let H : ℝ := p * q
  let y : ℝ := K * sig / den
  let xpos : ℝ := H * y
  obtain ⟨hLpos, htwpos, htwLeOne, htw2⟩ :=
    ccrMomentBoundSix_timeScale t (L : ℝ) ht (by exact_mod_cast htL)
  have hsigmaNonneg : 0 ≤ sig := by
    dsimp [sig]
    exact sigmaSq_nonneg β
  have hsigLeMom : sig ≤ σm := by
    dsimp [sig]
    exact hβ.trans (min_le_left _ _)
  have hsigLeOne : sig ≤ 1 := by
    dsimp [sig]
    exact hβ.trans (min_le_right _ _)
  have hMom : ∀ I : ReplicaPartition 6, I ≠ ⊥ →
      |replicaPartitionDisorderMoment β I| ≤ sig := by
    intro I hI'
    exact hMoments β hsigLeMom I hI'
  have hDnonneg : 0 ≤ D := by
    dsimp [D, dampedOverlap]
    apply Finset.sum_nonneg
    intro n hn
    exact mul_nonneg (Real.exp_nonneg _) (srwKernel_nonneg (2 * n) 0)
  have hsigD : 0 ≤ sig * D := mul_nonneg hsigmaNonneg hDnonneg
  have hden : 0 < den := by
    dsimp [den, sig, D]
    exact sub_pos.mpr hσD
  have hdenLeOne : den ≤ 1 := by
    dsimp [den]
    exact sub_le_self 1 hsigD
  have hsigDltOne : sig * D < 1 := by
    have hd : 0 < 1 - sig * D := by simpa only [den] using hden
    exact (sub_pos.mp hd)
  obtain ⟨hp1, hq1, hpqFormula, hpOver, hHone⟩ :=
    ccrMomentBoundSix_holderAlgebra hpq
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hHone
  obtain ⟨hlamw, hlamwL⟩ :=
    ccrMomentBoundSix_lambdaScale lam (L : ℝ) hlam hLpos
  have hxpos : 0 ≤ xpos := by
    dsimp [xpos, H]
    exact mul_nonneg (mul_nonneg (le_of_lt (lt_trans zero_lt_one hp1))
        (le_of_lt (lt_trans zero_lt_one hq1)))
      (div_nonneg (mul_nonneg (zero_le_one.trans hKone) hsigmaNonneg) hden.le)
  have hxlt : xpos < 1 := by
    dsimp [xpos, y, H]
    simpa only [mul_assoc] using hsmall
  let s : Finset (LatticeConfiguration 6) := configBox 6 A L
  let W : LatticeConfiguration 6 → ℝ := replicaExponentialWeight tw
  let u : ReplicaPartition 6 → LatticeConfiguration 6 → ℝ :=
    fun I x => hattedReplicaBoundaryVector L I A φ x
  let v : ReplicaPartition 6 → LatticeConfiguration 6 → ℝ := fun I => collisionIndicator I
  let cU : ℝ := 1 + cI * Real.exp (cI * tw ^ 2 * (L : ℝ)) *
    (sig * D / den)
  let cQval : ℝ := cQ * Real.exp (cQ * tw ^ 2 * (L : ℝ)) * (p * q)
  let left : ℝ := cB * Real.exp (cB * tw ^ 2 * (L : ℝ)) * q *
    (∑ z ∈ A, φ z * Real.exp (tw * ‖siteToPlane z‖)) *
    finiteLpNorm A p (fun z => φ z * Real.exp (tw * ‖siteToPlane z‖)) ^ 5
  let right : ℝ := (cColl / tw ^ 2) ^ ((5 : ℝ) / q)
  let G : ℝ := (max 1 (ccr25GaussianMomentUniformConstant 6)) ^ 6 * (2 ^ 36 : ℝ)
  let A0 : ℝ := ccr25GaussianFiniteWordOperatorScale 6 cU
  have hG : G = Bgauss := by rfl
  have hGpos : 0 < G := lt_of_lt_of_le (by norm_num) hBgauss
  have hcUpos : 0 ≤ cU := by dsimp [cU]; positivity
  have hcQpos : 0 ≤ cQval := by dsimp [cQval]; positivity
  have hleftpos : 0 ≤ left := by
    have hsum : 0 ≤ ∑ z ∈ A, φ z * Real.exp (tw * ‖siteToPlane z‖) := by
      apply Finset.sum_nonneg
      intro z hz
      exact mul_nonneg (hφ z) (Real.exp_nonneg _)
    have hnorm : 0 ≤ finiteLpNorm A p
        (fun z => φ z * Real.exp (tw * ‖siteToPlane z‖)) :=
      finiteLpNorm_nonneg A p _
    dsimp [left]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (zero_le_one.trans hcB) (Real.exp_nonneg _)) (le_of_lt (lt_trans zero_lt_one hq1))) hsum)
      (pow_nonneg hnorm 5)
  have hrightpos : 0 ≤ right := by
    dsimp [right]
    positivity
  have hWpos : ∀ x ∈ s, 0 < W x := by
    intro x hx
    exact replicaExponentialWeight_pos tw x
  have hleftBound : ∀ I : ReplicaPartition 6, I ≠ ⊥ →
      finiteLpNorm s p (fun x => u I x / W x) ≤ left := by
    intro I hI'
    have h := ccrMomentBoundSix_boundaryApplication hBop tw (le_of_lt htwpos)
      L p q hp1 A φ hφ s I hI' hpOver
    simpa only [u, W, left] using h
  have hrightBound : ∀ I : ReplicaPartition 6, I ≠ ⊥ →
      finiteLpNorm s q (fun x => W x * v I x) ≤ right := by
    intro I hI'
    have h := ccrMomentBoundSix_collisionApplication hColl tw htwpos htwLeOne q
      (le_of_lt hq1) s I hI'
    simpa only [W, v, right] using h
  have hu : ∀ I x, 0 ≤ u I x := by
    intro I x
    exact hattedReplicaBoundaryVector_nonneg L I A φ (fun z hz => hφ z) x
  have hv : ∀ I x, 0 ≤ v I x := by
    intro I x
    by_cases hcoll : IsCollisionConfiguration I x
    · simp only [v, collisionIndicator, hcoll]
      norm_num
    · simp only [v, collisionIndicator, hcoll]
      norm_num
  have hUbound : ∀ I : ReplicaPartition 6, I ≠ ⊥ → ∀ f : LatticeConfiguration 6 → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lamw β (.interacting I))) f) ≤
        cU * finiteLpNorm s q f := by
    intro I hI' f
    have h := ccrMomentBoundSix_interactingApplication hIop tw (le_of_lt htwpos)
      L lamw β hlamw hMom hσD q hq1 s I hI' f
    simpa only [W, cU, sig, D, den, ccr25LabelKernel] using h
  have hQbound : ∀ I J : ReplicaPartition 6, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
      ∀ f : LatticeConfiguration 6 → ℝ,
        finiteLpNorm s q
          (finiteKernelApply s
            (weightedKernel W (ccr25LabelKernel L lamw β (.free I J))) f) ≤
          cQval * finiteLpNorm s q f := by
    intro I J hI' hJ' hIJ f
    have h := ccrMomentBoundSix_freeApplication hQop lamw β tw (le_of_lt htwpos)
      L q p hq1 hpqFormula s I J hI' hJ' hIJ f
    simpa only [W, cQval, ccr25LabelKernel] using h
  have hcUle : cU ≤ (1 + EU) / den := by
    have hfrac : sig * D / den ≤ 1 / den :=
      div_le_div_of_nonneg_right (le_of_lt hsigDltOne) hden.le
    have harg : cI * tw ^ 2 * (L : ℝ) = cI * t ^ 2 := by
      calc
        cI * tw ^ 2 * (L : ℝ) = cI * (tw ^ 2 * (L : ℝ)) := by ring
        _ = cI * t ^ 2 := by rw [htw2]
    have hcoef : cI * Real.exp (cI * tw ^ 2 * (L : ℝ)) = EU := by
      change cI * Real.exp (cI * tw ^ 2 * (L : ℝ)) = cI * Real.exp (cI * t ^ 2)
      rw [harg]
    dsimp [cU]
    rw [hcoef]
    have hinv : 1 ≤ 1 / den := (one_le_div₀ hden).2 hdenLeOne
    calc
      1 + EU * (sig * D / den) ≤ 1 + EU * (1 / den) := by
        simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hfrac hEU) 1
      _ ≤ 1 / den + EU / den := by
        rw [mul_one_div]
        simpa only [add_comm] using add_le_add_right hinv (EU / den)
      _ = (1 + EU) / den := by ring
  have hA0le : A0 ≤ (Abar / den) := by
    have hA0eq : A0 = cU * G := by
      dsimp [A0, G, ccr25GaussianFiniteWordOperatorScale]
      ring
    rw [hA0eq]
    have h := mul_le_mul_of_nonneg_right hcUle hGpos.le
    calc
      cU * G ≤ ((1 + EU) / den) * G := by simpa only [mul_comm] using h
      _ = Abar / den := by dsimp [Abar]; ring
  have hA0nonneg : 0 ≤ A0 := by
    rw [show A0 = cU * G by
      dsimp [A0, G, ccr25GaussianFiniteWordOperatorScale]; ring]
    exact mul_nonneg hcUpos hGpos.le
  have hQarg : cQ * tw ^ 2 * (L : ℝ) = cQ * t ^ 2 := by
    calc
      cQ * tw ^ 2 * (L : ℝ) = cQ * (tw ^ 2 * (L : ℝ)) := by ring
      _ = cQ * t ^ 2 := by rw [htw2]
  have hcQeq : cQval = EQ * H := by
    change cQ * Real.exp (cQ * tw ^ 2 * (L : ℝ)) * (p * q) =
      cQ * Real.exp (cQ * t ^ 2) * (p * q)
    rw [hQarg]
  have hcQeq' : cQval = EQ * (p * q) := by simpa only [H] using hcQeq
  have hA0run : (A0 * sig) * cQval ≤ xpos := by
    calc
      (A0 * sig) * cQval = (A0 * sig) * (EQ * H) := by rw [hcQeq]
      _ ≤ ((Abar / den) * sig) * (EQ * H) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hA0le hsigmaNonneg)
        exact mul_nonneg (zero_le_one.trans hEQone) hHpos.le
      _ = xpos := by
        dsimp [xpos, y, H, K]
        field_simp [ne_of_gt hden]
  have hsmallRun : (A0 * sig) * cQval < 1 := lt_of_le_of_lt hA0run hxlt
  have hRun := ccr25GaussianFiniteWordRun_sixth_tsum_bound s L lamw β W hWpos
    hpq u v cU cQval left right hcUpos hcQpos hleftpos hrightpos hleftBound hrightBound
    hUbound hQbound hu hv hsigLeOne hsmallRun
  let F : ℕ → ℝ := fun n => ccr25GaussianFiniteWordRun s L lamw β u v n
  have hFnonneg : ∀ n, 0 ≤ F n := by
    intro n
    exact ccr25GaussianFiniteWordRun_nonneg s L lamw β u v hu hv n
  have hFiniteEq :
      (∑ n ∈ Finset.range L, ∑ J ∈ ccr25AdmissibleWords 6 n,
        (∏ j, |replicaPartitionDisorderMoment β (J j)|) *
          ccr25FiniteWordPairing s L lamw β J
            (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator) =
        ∑ n ∈ Finset.range L, F n := by
    apply Finset.sum_congr rfl
    intro n hn
    change
      (∑ J ∈ ccr25AdmissibleWords 6 n,
        (∏ j, |replicaPartitionDisorderMoment β (J j)|) *
          ccr25FiniteWordPairing (configBox 6 A L) L lamw β J
            (fun I => hattedReplicaBoundaryVector L I A φ) collisionIndicator) =
        ccr25GaussianFiniteWordRun s L lamw β u v n
    rfl
  have hMomentBound := ccrMomentBoundSix_geometricRunSum β lam lamw hlamw L φ A hφ hA
    left right A0 sig cQval hW F hFnonneg hRun hFiniteEq hlamwL
  have hxden : 0 < 1 - xpos := sub_pos.mpr hxlt
  have hdenCompare : 1 - xpos ≤ 1 - (A0 * sig) * cQval :=
    sub_le_sub_left hA0run 1
  have hdenRun : 0 < 1 - (A0 * sig) * cQval :=
    lt_of_lt_of_le hxden hdenCompare
  have hypos : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (mul_nonneg (zero_le_one.trans hKone) hsigmaNonneg) hden.le
  have hdenLeOne' : 1 - xpos ≤ 1 := sub_le_self 1 hxpos
  have hfactorOne : 1 ≤ H ^ 2 / (1 - xpos) := by
    have hHsq : 1 ≤ H ^ 2 := one_le_pow₀ hHone
    have hinv : 1 ≤ 1 / (1 - xpos) := (one_le_div₀ hxden).2 hdenLeOne'
    calc
      1 = 1 * 1 := by ring
      _ ≤ H ^ 2 * 1 := mul_le_mul_of_nonneg_right hHsq (by norm_num)
      _ ≤ H ^ 2 * (1 / (1 - xpos)) := mul_le_mul_of_nonneg_left hinv (sq_nonneg H)
      _ = H ^ 2 / (1 - xpos) := by ring
  have hsigDivDen : sig ^ 3 / den ≤ y ^ 3 := by
    have hden2 : den ^ 2 ≤ 1 := by
      calc
        den ^ 2 = den * den := by ring
        _ ≤ den * 1 := mul_le_mul_of_nonneg_left hdenLeOne hden.le
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_right hdenLeOne (by norm_num)
        _ = 1 := by ring
    have hKcube : 1 ≤ K ^ 3 := one_le_pow₀ hKone
    have hcross : sig ^ 3 * den ^ 2 ≤ K ^ 3 * sig ^ 3 := by
      calc
        sig ^ 3 * den ^ 2 ≤ sig ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hden2 (pow_nonneg hsigmaNonneg 3)
        _ = 1 * sig ^ 3 := by ring
        _ ≤ K ^ 3 * sig ^ 3 :=
          mul_le_mul_of_nonneg_right hKcube (pow_nonneg hsigmaNonneg 3)
    have hratio : sig ^ 3 / den ≤ K ^ 3 * sig ^ 3 / den ^ 3 := by
      rw [div_le_div_iff₀ hden (pow_pos hden 3)]
      calc
        sig ^ 3 * den ^ 3 = (sig ^ 3 * den ^ 2) * den := by ring
        _ ≤ (K ^ 3 * sig ^ 3) * den :=
          mul_le_mul_of_nonneg_right hcross hden.le
        _ = K ^ 3 * sig ^ 3 * den := by ring
    have hycube : y ^ 3 = K ^ 3 * (sig ^ 3 / den ^ 3) := by
      dsimp [y]
      rw [div_pow, mul_pow]
      ring
    calc
      sig ^ 3 / den ≤ K ^ 3 * sig ^ 3 / den ^ 3 := hratio
      _ = K ^ 3 * (sig ^ 3 / den ^ 3) := by ring
      _ = y ^ 3 := hycube.symm
  have hsigDivDenSq : sig ^ 3 / den ^ 2 ≤ y ^ 3 := by
    have hdenLe : den ≤ 1 := hdenLeOne
    have hKcube : 1 ≤ K ^ 3 := one_le_pow₀ hKone
    have hcross : sig ^ 3 * den ≤ K ^ 3 * sig ^ 3 := by
      calc
        sig ^ 3 * den ≤ sig ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hdenLe (pow_nonneg hsigmaNonneg 3)
        _ = 1 * sig ^ 3 := by ring
        _ ≤ K ^ 3 * sig ^ 3 :=
          mul_le_mul_of_nonneg_right hKcube (pow_nonneg hsigmaNonneg 3)
    have hratio : sig ^ 3 / den ^ 2 ≤ K ^ 3 * sig ^ 3 / den ^ 3 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hden) (pow_pos hden 3)]
      calc
        sig ^ 3 * den ^ 3 = (sig ^ 3 * den) * den ^ 2 := by ring
        _ ≤ (K ^ 3 * sig ^ 3) * den ^ 2 :=
          mul_le_mul_of_nonneg_right hcross (sq_nonneg den)
        _ = K ^ 3 * sig ^ 3 * den ^ 2 := by ring
    have hycube : y ^ 3 = K ^ 3 * (sig ^ 3 / den ^ 3) := by
      dsimp [y]
      rw [div_pow, mul_pow]
      ring
    calc
      sig ^ 3 / den ^ 2 ≤ K ^ 3 * sig ^ 3 / den ^ 3 := hratio
      _ = K ^ 3 * (sig ^ 3 / den ^ 3) := by ring
      _ = y ^ 3 := hycube.symm
  have hsigDivDenCube : sig ^ 3 / den ^ 3 ≤ y ^ 3 := by
    have hKcube : 1 ≤ K ^ 3 := one_le_pow₀ hKone
    have hbase : sig ^ 3 / den ^ 3 ≤ K ^ 3 * (sig ^ 3 / den ^ 3) :=
      by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hKcube
            (div_nonneg (pow_nonneg hsigmaNonneg 3) (pow_nonneg hden.le 3)))
    have hycube : y ^ 3 = K ^ 3 * (sig ^ 3 / den ^ 3) := by
      dsimp [y]
      rw [div_pow, mul_pow]
      ring
    rw [hycube]
    exact hbase
  have hAfirst : A0 * sig ^ 3 ≤ Abar * H ^ 2 * y ^ 3 / (1 - xpos) := by
    have hfirst0 : A0 * sig ^ 3 ≤ Abar * (sig ^ 3 / den) := by
      calc
        A0 * sig ^ 3 ≤ (Abar / den) * sig ^ 3 :=
          mul_le_mul_of_nonneg_right hA0le (pow_nonneg hsigmaNonneg 3)
        _ = Abar * (sig ^ 3 / den) := by ring
    calc
      _ ≤ Abar * (sig ^ 3 / den) := hfirst0
      _ ≤ Abar * y ^ 3 :=
        mul_le_mul_of_nonneg_left hsigDivDen (zero_le_one.trans hAbarone)
      _ ≤ Abar * H ^ 2 * y ^ 3 / (1 - xpos) := by
        have hnonneg : 0 ≤ Abar * y ^ 3 :=
          mul_nonneg (zero_le_one.trans hAbarone) (pow_nonneg hypos 3)
        calc
          Abar * y ^ 3 = (Abar * y ^ 3) * 1 := by ring
          _ ≤ (Abar * y ^ 3) * (H ^ 2 / (1 - xpos)) :=
            mul_le_mul_of_nonneg_left hfactorOne hnonneg
          _ = Abar * H ^ 2 * y ^ 3 / (1 - xpos) := by ring
  have hA0sq : A0 ^ 2 ≤ (Abar / den) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA0le 2
  have hA0cube : A0 ^ 3 ≤ (Abar / den) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hA0le 3
  have hdenRel : 1 - xpos ≤ 1 - (A0 * sig) * cQval := sub_le_sub_left hA0run 1
  have hAsecond : A0 ^ 2 * cQval * sig ^ 3 ≤
      Abar ^ 2 * EQ * H ^ 2 * y ^ 3 / (1 - xpos) := by
    have hnum : A0 ^ 2 * cQval * sig ^ 3 ≤
        Abar ^ 2 * EQ * H * sig ^ 3 / den ^ 2 := by
      rw [hcQeq]
      calc
        A0 ^ 2 * (EQ * H) * sig ^ 3 ≤
            (Abar / den) ^ 2 * (EQ * H) * sig ^ 3 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hA0sq
                  (mul_nonneg (zero_le_one.trans hEQone) hHpos.le))
                (pow_nonneg hsigmaNonneg 3)
        _ = Abar ^ 2 * EQ * H * sig ^ 3 / den ^ 2 := by
          field_simp [ne_of_gt hden]
    calc
      _ ≤ Abar ^ 2 * EQ * H * (sig ^ 3 / den ^ 2) := by
        calc
          A0 ^ 2 * cQval * sig ^ 3 ≤
              Abar ^ 2 * EQ * H * sig ^ 3 / den ^ 2 := hnum
          _ = Abar ^ 2 * EQ * H * (sig ^ 3 / den ^ 2) := by ring
      _ ≤ Abar ^ 2 * EQ * H * y ^ 3 := by
        apply mul_le_mul_of_nonneg_left hsigDivDenSq
        positivity
      _ ≤ Abar ^ 2 * EQ * H ^ 2 * y ^ 3 := by
        have hbase : 0 ≤ Abar ^ 2 * EQ * H * y ^ 3 := by positivity
        calc
          _ = (Abar ^ 2 * EQ * H * y ^ 3) * 1 := by ring
          _ ≤ (Abar ^ 2 * EQ * H * y ^ 3) * H :=
            mul_le_mul_of_nonneg_left hHone hbase
          _ = _ := by ring
      _ ≤ Abar ^ 2 * EQ * H ^ 2 * y ^ 3 / (1 - xpos) := by
        have hbase : 0 ≤ Abar ^ 2 * EQ * H ^ 2 * y ^ 3 := by positivity
        calc
          _ = (Abar ^ 2 * EQ * H ^ 2 * y ^ 3) * 1 := by ring
          _ ≤ (Abar ^ 2 * EQ * H ^ 2 * y ^ 3) * (1 / (1 - xpos)) :=
            mul_le_mul_of_nonneg_left
              ((one_le_div₀ hxden).2 (sub_le_self 1 hxpos)) hbase
          _ = _ := by ring
  have hAthird : A0 ^ 3 * cQval ^ 2 * sig ^ 3 /
      (1 - (A0 * sig) * cQval) ≤
      Abar ^ 3 * EQ ^ 2 * H ^ 2 * y ^ 3 / (1 - xpos) := by
    have hnum : A0 ^ 3 * cQval ^ 2 * sig ^ 3 ≤
        Abar ^ 3 * EQ ^ 2 * H ^ 2 * (sig ^ 3 / den ^ 3) := by
      rw [hcQeq]
      calc
        A0 ^ 3 * (EQ * H) ^ 2 * sig ^ 3 ≤
            (Abar / den) ^ 3 * (EQ * H) ^ 2 * sig ^ 3 := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hA0cube
                  (sq_nonneg (EQ * H))) (pow_nonneg hsigmaNonneg 3)
        _ = Abar ^ 3 * EQ ^ 2 * H ^ 2 * (sig ^ 3 / den ^ 3) := by
          field_simp [ne_of_gt hden]
    calc
      _ ≤ (Abar ^ 3 * EQ ^ 2 * H ^ 2 * (sig ^ 3 / den ^ 3)) /
          (1 - (A0 * sig) * cQval) :=
            div_le_div_of_nonneg_right hnum (le_of_lt hdenRun)
      _ ≤ (Abar ^ 3 * EQ ^ 2 * H ^ 2 * (sig ^ 3 / den ^ 3)) / (1 - xpos) := by
        apply div_le_div_of_nonneg_left _ hxden hdenRel
        positivity
      _ ≤ Abar ^ 3 * EQ ^ 2 * H ^ 2 * y ^ 3 / (1 - xpos) := by
        apply div_le_div_of_nonneg_right _ hxden.le
        apply mul_le_mul_of_nonneg_left hsigDivDenCube
        positivity
  have hMnonneg : 0 ≤ Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2 := by positivity
  have hcoeff :
      A0 * sig ^ 3 + A0 ^ 2 * cQval * sig ^ 3 +
        A0 ^ 3 * cQval ^ 2 * sig ^ 3 /
          (1 - (A0 * sig) * cQval) ≤
        (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2 * y ^ 3 /
          (1 - xpos) := by
    calc
      _ ≤ Abar * H ^ 2 * y ^ 3 / (1 - xpos) +
          Abar ^ 2 * EQ * H ^ 2 * y ^ 3 / (1 - xpos) +
          Abar ^ 3 * EQ ^ 2 * H ^ 2 * y ^ 3 / (1 - xpos) :=
        add_le_add (add_le_add hAfirst hAsecond) hAthird
      _ = _ := by ring
  have hleftEq : left = cB * Real.exp (cB * t ^ 2) * q *
      (∑ z ∈ A, φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) *
      finiteLpNorm A p
        (fun z => φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) ^ 5 := by
    dsimp [left]
    have hargB : cB * tw ^ 2 * (L : ℝ) = cB * t ^ 2 := by
      calc
        cB * tw ^ 2 * (L : ℝ) = cB * (tw ^ 2 * (L : ℝ)) := by ring
        _ = cB * t ^ 2 := by rw [htw2]
    rw [hargB]
    have hexp (z : Site) : tw * ‖siteToPlane z‖ =
        t * ‖siteToPlane z‖ / Real.sqrt L := by
      dsimp [tw]
      ring
    have hfun : (fun z => φ z * Real.exp (tw * ‖siteToPlane z‖)) =
        (fun z => φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) := by
      funext z
      rw [hexp z]
    have hsum : (∑ z ∈ A, φ z * Real.exp (tw * ‖siteToPlane z‖)) =
        (∑ z ∈ A, φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hexp z]
    have hnorm : finiteLpNorm A p
        (fun z => φ z * Real.exp (tw * ‖siteToPlane z‖)) =
        finiteLpNorm A p
          (fun z => φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) := by
      rw [hfun]
    rw [hsum, hnorm]
  have htwSq : tw ^ 2 = t ^ 2 / (L : ℝ) := by
    apply (eq_div_iff (ne_of_gt hLpos)).2
    exact htw2
  have hrightEq : right = cColl ^ ((5 : ℝ) / q) *
      ((L : ℝ) / t ^ 2) ^ ((5 : ℝ) / q) := by
    dsimp [right]
    rw [htwSq]
    have ht0 : t ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos ht)
    have hbase : cColl / (t ^ 2 / (L : ℝ)) = cColl * ((L : ℝ) / t ^ 2) := by
      field_simp [ne_of_gt hLpos, ht0]
    rw [hbase, Real.mul_rpow (by positivity) (by positivity)]
  have hqleH : q ≤ H := by
    dsimp [H]
    have hq0 : 0 ≤ q := (lt_trans zero_lt_one hq1).le
    calc
      q = 1 * q := by ring
      _ ≤ p * q := mul_le_mul_of_nonneg_right (le_of_lt hp1) hq0
  calc
    |∫ ω, (profileP2Fun β 0 L φ (fun _ => 1) ω -
        ∫ ω', profileP2Fun β 0 L φ (fun _ => 1) ω' ∂disorderLaw) ^ 6 ∂disorderLaw|
      ≤ Real.exp lam * (left * right) *
          (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2 * y ^ 3 / (1 - xpos) := by
        calc
          _ ≤ Real.exp lam * (left * right) *
              (A0 * sig ^ 3 + A0 ^ 2 * cQval * sig ^ 3 +
                A0 ^ 3 * cQval ^ 2 * sig ^ 3 /
                  (1 - (A0 * sig) * cQval)) := by
              simpa only [mul_assoc] using hMomentBound
          _ ≤ _ := by
            have hscale : 0 ≤ Real.exp lam * (left * right) :=
              mul_nonneg (Real.exp_nonneg _) (mul_nonneg hleftpos hrightpos)
            have hmul := mul_le_mul_of_nonneg_left hcoeff hscale
            calc
              _ ≤ Real.exp lam * (left * right) *
                  ((Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2 * y ^ 3 /
                    (1 - xpos)) := hmul
              _ = Real.exp lam * (left * right) *
                  (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2 * y ^ 3 /
                    (1 - xpos) := by ring
    _ ≤ C * xpos ^ 3 / (1 - xpos) *
          (∑ z ∈ A, φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) *
          finiteLpNorm A p
            (fun z => φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) ^ 5 *
          ((L : ℝ) / t ^ 2) ^ ((5 : ℝ) / q) := by
        let S : ℝ := ∑ z ∈ A, φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)
        let N : ℝ := finiteLpNorm A p
          (fun z => φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L))
        let T : ℝ := ((L : ℝ) / t ^ 2) ^ ((5 : ℝ) / q)
        let E : ℝ := Real.exp lam * (cB * Real.exp (cB * t ^ 2)) * S * N ^ 5 * T
        have hS : 0 ≤ S := by
          dsimp [S]
          apply Finset.sum_nonneg
          intro z hz
          exact mul_nonneg (hφ z) (Real.exp_nonneg _)
        have hN : 0 ≤ N := by
          dsimp [N]
          exact finiteLpNorm_nonneg A p _
        have hT : 0 ≤ T := by
          dsimp [T]
          exact Real.rpow_nonneg
            (div_nonneg (by exact_mod_cast (Nat.zero_le L)) (sq_pos_of_pos ht).le) _
        have hE : 0 ≤ E := by
          dsimp [E]
          positivity
        have hcoeffP := ccrMomentBoundSix_constantAbsorption cColl q H
          (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) hcColl hq1 hqleH hMnonneg
        have hcoeffPH : q * cColl ^ ((5 : ℝ) / q) *
            (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2 ≤
            cColl ^ 5 * (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 3 := by
          calc
            _ = (q * cColl ^ ((5 : ℝ) / q) *
                (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2)) * H ^ 2 := by ring
            _ ≤ (cColl ^ 5 * (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H) * H ^ 2 :=
              mul_le_mul_of_nonneg_right hcoeffP (sq_nonneg H)
            _ = cColl ^ 5 * (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 3 := by ring
        have hyDen : 0 ≤ y ^ 3 / (1 - xpos) := div_nonneg (pow_nonneg hypos 3) hxden.le
        have hcoeffFinal : q * cColl ^ ((5 : ℝ) / q) *
            (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2 *
              (y ^ 3 / (1 - xpos)) ≤
            cColl ^ 5 * (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 3 *
              (y ^ 3 / (1 - xpos)) := by
          calc
            _ = (q * cColl ^ ((5 : ℝ) / q) *
                (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2) *
                (y ^ 3 / (1 - xpos)) := by ring
            _ ≤ (cColl ^ 5 * (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 3) *
                (y ^ 3 / (1 - xpos)) :=
              mul_le_mul_of_nonneg_right hcoeffPH hyDen
            _ = _ := by ring
        have hscaled := mul_le_mul_of_nonneg_left hcoeffFinal hE
        have hstart : Real.exp lam * (left * right) *
            (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2 * y ^ 3 /
              (1 - xpos) =
            E * (q * cColl ^ ((5 : ℝ) / q) *
              (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 2 *
                (y ^ 3 / (1 - xpos))) := by
          rw [hleftEq, hrightEq]
          dsimp [E, S, N, T]
          ring
        have hend : C * xpos ^ 3 / (1 - xpos) * S * N ^ 5 * T =
            E * (cColl ^ 5 * (Abar + Abar ^ 2 * EQ + Abar ^ 3 * EQ ^ 2) * H ^ 3 *
              (y ^ 3 / (1 - xpos))) := by
          dsimp [C, Cbase, xpos, y, H, K, E]
          ring
        rw [hstart, hend]
        exact hscaled
    _ = C * (p * q * (K * Polymer.sigmaSq β /
          (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L))) ^ ((6 : ℝ) / 2) /
          (1 - p * q * (K * Polymer.sigmaSq β /
            (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L))) *
          (∑ z ∈ A, φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) *
          finiteLpNorm A p
            (fun z => φ z * Real.exp (t * ‖siteToPlane z‖ / Real.sqrt L)) ^ (6 - 1) *
          ((L : ℝ) / t ^ 2) ^ (((6 : ℝ) - 1) / q) := by
      have hmomentArg : xpos = p * q *
          (K * Polymer.sigmaSq β /
            (1 - Polymer.sigmaSq β * dampedOverlap (lam / L) L)) := by
        dsimp [xpos, y, H, sig, den, D]
      rw [hmomentArg]
      have hhalf : (6 : ℝ) / 2 = 3 := by norm_num
      have hnat : (6 : ℕ) - 1 = 5 := by norm_num
      have hreal : (6 : ℝ) - 1 = 5 := by norm_num
      rw [hhalf, hnat, hreal]
      rw [← Real.rpow_natCast]
      rfl

/-- CSZ25 Theorem 5.7's estimate holds at the sixth moment order for the profile observable. -/
theorem ccrMomentBound_six : CCRMomentBound 6 :=
  ccrMomentBound_six_of_wordRuns wordRunsBound_six


end Critical2DKPZ.MomentBounds

end
