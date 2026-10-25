/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.StringSumTailBound
public import Critical2DKPZ.Blocks.ChaosIdentity
public import Critical2DKPZ.Blocks.DiscrepancyMoments
public import Critical2DKPZ.Blocks.HalfShiftedGrid
public import Critical2DKPZ.Blocks.GridAlignment
import Critical2DKPZ.Collision.BackwardChain
import Critical2DKPZ.Collision.RenewalStringIntegral
import Mathlib.Tactic

/-! # Discrepancy-string second-moment bounds -/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped ENNReal

namespace Critical2DKPZ.Blocks

private theorem renewalStringSum_backwardChain_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ (m : ℕ) (lo hi : Fin (m + 1) → ℕ),
        (∀ j, lo j < hi j) → (∀ j : Fin m, hi j.castSucc ≤ lo j.succ) →
        hi (Fin.last m) ≤ N →
        let S : Fin (m + 1) → ℝ := fun j => ((lo j : ℝ) + 1 / 2) / N
        let T : Fin (m + 1) → ℝ := fun j => ((hi j : ℝ) + 1 / 2) / N
        0 < S 0 → 2 * S 0 ≤ T 0 →
        (∀ j : Fin m, 4 * S j.succ ≤ T j.succ) →
        (∀ j : Fin m, T j.castSucc ≤ S j.succ) →
        (∀ j, T j < 1) →
        ENNReal.ofReal (renewalStringSum ϑ N m lo hi) ≤
          ENNReal.ofReal ((C : ℝ) ^ (m + 1) * Real.log (T 0 / S 0) *
            (∏ j : Fin m, T j.castSucc / S j.succ) *
            ∏ j, (-Real.log (T j))⁻¹) := by
  obtain ⟨C₆, hC₆, hRenewalStringIntegralInput⟩ := Collision.renewalString_sum_le_integral A
  obtain ⟨C₇, hC₇, hBackwardChainIntegralInput⟩ := Collision.lintegral_backwardChain_le A
  refine ⟨C₆ * C₇, mul_pos hC₆ hC₇, ?_⟩
  intro N hN ϑ hϑ m lo hi hlo hsep hlast S T hS hfirst hblock hchain hT
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h06 := hRenewalStringIntegralInput N hN ϑ hϑ m lo hi hlo hsep hlast
  have h07 := hBackwardChainIntegralInput ϑ hϑ m S T hS hfirst hblock hchain hT
  have hdomains :
      {p : Fin (m + 1) → ℝ × ℝ | ∀ j,
        ((lo j : ℝ) + 1 / 2) / N < (p j).1 ∧
        (p j).1 < (p j).2 ∧ (p j).2 ≤ ((hi j : ℝ) + 1 / 2) / N} =
      {p : Fin (m + 1) → ℝ × ℝ | ∀ j,
        S j < (p j).1 ∧ (p j).1 < (p j).2 ∧ (p j).2 ≤ T j} := by
    ext p
    simp only [Set.mem_ofPred_eq, S, T]
  rw [hdomains] at h06
  let Q := Real.log (T 0 / S 0) *
    (∏ j : Fin m, T j.castSucc / S j.succ) *
    ∏ j, (-Real.log (T j))⁻¹
  have hfinal :
      ENNReal.ofReal (∑ a ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
        ∑ b ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
          if ∀ j, a j ≤ b j then
            (a 0 : ℝ)⁻¹ * (∏ j, criticalSigmaSq ϑ N *
              Renewal.criticalRenewalMass ϑ N (b j - a j)) *
                ∏ j : Fin m, (b j.castSucc : ℝ) /
                  (a j.succ * ((a j.succ : ℝ) - b j.castSucc))
          else 0) ≤ ENNReal.ofReal (C₆ ^ (m + 1)) *
            ENNReal.ofReal (C₇ ^ (m + 1) * Q) := by
    simpa [Q, mul_assoc] using h06.trans (mul_le_mul' le_rfl h07)
  have hpow : C₆ ^ (m + 1) * C₇ ^ (m + 1) = (C₆ * C₇) ^ (m + 1) := by ring
  calc
    ENNReal.ofReal (renewalStringSum ϑ N m lo hi) =
        ENNReal.ofReal (∑ a ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
          ∑ b ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
            if ∀ j, a j ≤ b j then
              (a 0 : ℝ)⁻¹ * (∏ j, criticalSigmaSq ϑ N *
                Renewal.criticalRenewalMass ϑ N (b j - a j)) *
                  ∏ j : Fin m, (b j.castSucc : ℝ) /
                    (a j.succ * ((a j.succ : ℝ) - b j.castSucc))
            else 0) := rfl
    _ ≤ ENNReal.ofReal (C₆ ^ (m + 1)) * ENNReal.ofReal (C₇ ^ (m + 1) * Q) := hfinal
    _ = ENNReal.ofReal (C₆ ^ (m + 1) * (C₇ ^ (m + 1) * Q)) :=
      (ENNReal.ofReal_mul (pow_nonneg hC₆.le _)).symm
    _ = ENNReal.ofReal ((C₆ * C₇) ^ (m + 1) * Q) := by
      congr 1
      calc
        C₆ ^ (m + 1) * (C₇ ^ (m + 1) * Q) =
            (C₆ ^ (m + 1) * C₇ ^ (m + 1)) * Q := by ring
        _ = (C₆ * C₇) ^ (m + 1) * Q := by rw [hpow]
    _ = ENNReal.ofReal ((C₆ * C₇) ^ (m + 1) *
          Real.log (T 0 / S 0) *
            (∏ j : Fin m, T j.castSucc / S j.succ) *
            ∏ j, (-Real.log (T j))⁻¹) := by
      congr 1
      dsimp [Q]
      ring

theorem renewalStringSum_backwardChain_open_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ (m : ℕ) (lo hi : Fin (m + 2) → ℕ),
        (∀ j, lo j < hi j) → (∀ j : Fin (m + 1), hi j.castSucc ≤ lo j.succ) →
        hi (Fin.last (m + 1)) ≤ N →
        let S : Fin (m + 2) → ℝ := fun j => ((lo j : ℝ) + 1 / 2) / N
        let T : Fin (m + 2) → ℝ := fun j => ((hi j : ℝ) + 1 / 2) / N
        0 < S 0 → 2 * S 0 ≤ T 0 →
        (∀ j : Fin (m + 1), 4 * S j.succ ≤ T j.succ) →
        (∀ j : Fin (m + 1), T j.castSucc ≤ S j.succ) →
        (∀ j : Fin (m + 1), T j.castSucc < 1) →
        T (Fin.last (m + 1)) ≤ 2 →
        ENNReal.ofReal (renewalStringSum ϑ N (m + 1) lo hi) ≤
          ENNReal.ofReal ((C : ℝ) ^ (m + 2) * Real.log (T 0 / S 0) *
            (∏ j : Fin (m + 1), T j.castSucc / S j.succ) *
            ∏ j : Fin (m + 1), (-Real.log (T j.castSucc))⁻¹) := by
  obtain ⟨C₆, hC₆, hRenewalStringIntegralInput⟩ := Collision.renewalString_sum_le_integral A
  obtain ⟨C₇, hC₇, hBackwardChainIntegralInput⟩ := Collision.lintegral_backwardChain_open_le A
  refine ⟨C₆ * C₇, mul_pos hC₆ hC₇, ?_⟩
  intro N hN ϑ hϑ m lo hi hlo hsep hlast S T hS hfirst hblock hchain hT hTlast
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h06 := hRenewalStringIntegralInput N hN ϑ hϑ (m + 1) lo hi hlo hsep hlast
  have h07 := hBackwardChainIntegralInput ϑ hϑ m S T hS hfirst hblock hchain hT hTlast
  have hdomains :
      {p : Fin (m + 2) → ℝ × ℝ | ∀ j,
        ((lo j : ℝ) + 1 / 2) / N < (p j).1 ∧
        (p j).1 < (p j).2 ∧ (p j).2 ≤ ((hi j : ℝ) + 1 / 2) / N} =
      {p : Fin (m + 2) → ℝ × ℝ | ∀ j,
        S j < (p j).1 ∧ (p j).1 < (p j).2 ∧ (p j).2 ≤ T j} := by
    ext p
    simp only [Set.mem_ofPred_eq, S, T]
  rw [hdomains] at h06
  let Q := Real.log (T 0 / S 0) *
    (∏ j : Fin (m + 1), T j.castSucc / S j.succ) *
    ∏ j : Fin (m + 1), (-Real.log (T j.castSucc))⁻¹
  have hfinal :
      ENNReal.ofReal (∑ a ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
        ∑ b ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
          if ∀ j, a j ≤ b j then
            (a 0 : ℝ)⁻¹ * (∏ j, criticalSigmaSq ϑ N *
              Renewal.criticalRenewalMass ϑ N (b j - a j)) *
                ∏ j : Fin (m + 1), (b j.castSucc : ℝ) /
                  (a j.succ * ((a j.succ : ℝ) - b j.castSucc))
          else 0) ≤ ENNReal.ofReal (C₆ ^ (m + 2)) *
            ENNReal.ofReal (C₇ ^ (m + 2) * Q) := by
    simpa [Q, mul_assoc] using h06.trans (mul_le_mul' le_rfl h07)
  have hpow : C₆ ^ (m + 2) * C₇ ^ (m + 2) = (C₆ * C₇) ^ (m + 2) := by ring
  calc
    ENNReal.ofReal (renewalStringSum ϑ N (m + 1) lo hi) =
        ENNReal.ofReal (∑ a ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
          ∑ b ∈ Fintype.piFinset (fun j => Finset.Ioc (lo j) (hi j)),
            if ∀ j, a j ≤ b j then
              (a 0 : ℝ)⁻¹ * (∏ j, criticalSigmaSq ϑ N *
                Renewal.criticalRenewalMass ϑ N (b j - a j)) *
                  ∏ j : Fin (m + 1), (b j.castSucc : ℝ) /
                    (a j.succ * ((a j.succ : ℝ) - b j.castSucc))
            else 0) := rfl
    _ ≤ ENNReal.ofReal (C₆ ^ (m + 2)) * ENNReal.ofReal (C₇ ^ (m + 2) * Q) := hfinal
    _ = ENNReal.ofReal (C₆ ^ (m + 2) * (C₇ ^ (m + 2) * Q)) :=
      (ENNReal.ofReal_mul (pow_nonneg hC₆.le _)).symm
    _ = ENNReal.ofReal ((C₆ * C₇) ^ (m + 2) * Q) := by
      congr 1
      calc
        C₆ ^ (m + 2) * (C₇ ^ (m + 2) * Q) =
            (C₆ ^ (m + 2) * C₇ ^ (m + 2)) * Q := by ring
        _ = (C₆ * C₇) ^ (m + 2) * Q := by rw [hpow]
    _ = ENNReal.ofReal ((C₆ * C₇) ^ (m + 2) *
          Real.log (T 0 / S 0) *
            (∏ j : Fin (m + 1), T j.castSucc / S j.succ) *
            ∏ j : Fin (m + 1), (-Real.log (T j.castSucc))⁻¹) := by
      congr 1
      dsimp [Q]
      ring

private theorem inv_negLog_le_div_of_mul_le {D L G x : ℝ}
    (hD : 0 < D) (hL : 0 < L) (hx : 0 < x) (hxlt : x < 1)
    (hbound : D * L ≤ G * (-Real.log x)) :
    (-Real.log x)⁻¹ ≤ G / (D * L) := by
  have hy : 0 < -Real.log x := neg_pos.mpr (Real.log_neg hx hxlt)
  apply (le_div_iff₀ (mul_pos hD hL)).2
  calc
    (-Real.log x)⁻¹ * (D * L) = (D * L) * (-Real.log x)⁻¹ := mul_comm _ _
    _ ≤ (G * (-Real.log x)) * (-Real.log x)⁻¹ :=
      mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr hy.le)
    _ = G := by
      rw [mul_assoc, mul_inv_cancel₀ hy.ne', mul_one]

/-- The closed renewal-chain factor is bounded by a geometric rate and two endpoint losses. -/
private theorem closedBackwardFactor_le_occupiedRate
    {K u v m : ℕ} {ρ L G : ℝ} (idx : Fin (m + 1) → ℕ)
    (S T : Fin (m + 1) → ℝ)
    (hG : 1 ≤ G) (hL : 1 ≤ L) (hLleρ : L ≤ ρ)
    (hm : 1 ≤ m) (huv : u < v) (hvK : v + 1 ≤ K)
    (hidx0 : idx 0 = u) (hidxlast : idx (Fin.last m) = v)
    (hidxBound : ∀ j, idx j ≤ v)
    (hidxMono : StrictMono idx)
    (hSpos : ∀ j, 0 < S j) (hTpos : ∀ j, 0 < T j) (hTlt : ∀ j, T j < 1)
    (hSleT : S 0 ≤ T 0)
    (hlogfirst : Real.log (T 0 / S 0) ≤ G * L)
    (hlogcell : ∀ j, ((K : ℝ) - idx j) * L ≤ G * (-Real.log (T j)))
    (hstep : ∀ j : Fin m,
      T j.castSucc / S j.succ ≤
        (G / ρ) ^ (idx j.succ - idx j.castSucc - 1))
    (hsumDelta : ∑ j : Fin m, (idx j.succ - idx j.castSucc) = v - u) :
    Real.log (T 0 / S 0) *
        (∏ j : Fin m, T j.castSucc / S j.succ) *
        ∏ j, (-Real.log (T j))⁻¹ ≤
      G ^ 2 / ((K : ℝ) - u) *
        (G / L) ^ (v - u) / ((K : ℝ) - v) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hρpos : 0 < ρ := lt_of_lt_of_le hLpos hLleρ
  have hDnat : 1 ≤ K - v := by omega
  have hUnat : 1 ≤ K - u := by omega
  have hvKreal : (v : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hvK
  have huKreal : (u : ℝ) + 1 ≤ (K : ℝ) := by
    have huKnat : u + 1 ≤ K := by omega
    exact_mod_cast huKnat
  have hD : 1 ≤ (K : ℝ) - (v : ℝ) := by linarith
  have hU : 1 ≤ (K : ℝ) - (u : ℝ) := by linarith
  have hDpos : 0 < (K : ℝ) - v := by linarith
  have hUpos : 0 < (K : ℝ) - u := by linarith
  have hfirstInv : (-Real.log (T 0))⁻¹ ≤ G / (((K : ℝ) - u) * L) := by
    apply inv_negLog_le_div_of_mul_le hUpos hLpos (hTpos 0)
      (hTlt 0)
    simpa only [hidx0] using hlogcell 0
  have hfirstLogNonneg : 0 ≤ Real.log (T 0 / S 0) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (hSpos 0)]
    linarith
  have hnegLogPos (j : Fin (m + 1)) : 0 < -Real.log (T j) :=
    neg_pos.mpr (Real.log_neg (hTpos j) (hTlt j))
  have hfirstFactor :
      Real.log (T 0 / S 0) * (-Real.log (T 0))⁻¹ ≤
        G ^ 2 / ((K : ℝ) - u) := by
    calc
      _ ≤ (G * L) * (G / (((K : ℝ) - u) * L)) :=
        mul_le_mul hlogfirst hfirstInv
          (inv_nonneg.mpr (hnegLogPos 0).le)
          (by positivity : 0 ≤ G * L)
      _ = G ^ 2 / ((K : ℝ) - u) := by field_simp [ne_of_gt hUpos, ne_of_gt hLpos]
  have hbase : G / ρ ≤ G / L :=
    div_le_div_of_nonneg_left (by linarith : 0 ≤ G) hLpos hLleρ
  let r : ℝ := G / L
  have hr : 0 < r := div_pos (by linarith : 0 < G) hLpos
  have hstepBound (j : Fin m) :
      T j.castSucc / S j.succ * (-Real.log (T j.succ))⁻¹ ≤
        r ^ (idx j.succ - idx j.castSucc) / ((K : ℝ) - v) := by
    have hidxorder : idx j.castSucc ≤ idx j.succ :=
      (hidxMono (by exact Nat.lt_succ_self j)).le
    have hltIdx : idx j.castSucc < idx j.succ :=
      hidxMono Fin.castSucc_lt_succ
    have hgap : 0 < idx j.succ - idx j.castSucc := Nat.sub_pos_of_lt hltIdx
    have hgapEq : idx j.succ - idx j.castSucc - 1 + 1 =
        idx j.succ - idx j.castSucc := by omega
    have hnextDen :
        (((K : ℝ) - v) * L) ≤ ((K : ℝ) - idx j.succ) * L := by
      have hidxReal : (idx j.succ : ℝ) ≤ v := by exact_mod_cast (hidxBound j.succ)
      have hsub : (K : ℝ) - (v : ℝ) ≤ (K : ℝ) - (idx j.succ : ℝ) := by linarith
      exact mul_le_mul_of_nonneg_right hsub hLpos.le
    have hlogNext := hlogcell j.succ
    have hinvNext := inv_negLog_le_div_of_mul_le hDpos hLpos
      (hTpos j.succ) (hTlt j.succ) (hnextDen.trans hlogNext)
    have hInvCompare : G / (((K : ℝ) - v) * L) ≤
        (G / L) / ((K : ℝ) - v) := by
      field_simp
      norm_num
    have hpow : (G / ρ) ^ (idx j.succ - idx j.castSucc - 1) ≤
        r ^ (idx j.succ - idx j.castSucc - 1) := by
      exact pow_le_pow_left₀ (div_nonneg (by linarith) hρpos.le) hbase _
    have hfactor : (G / ρ) ^ (idx j.succ - idx j.castSucc - 1) *
        (-Real.log (T j.succ))⁻¹ ≤
        r ^ (idx j.succ - idx j.castSucc - 1) * (r / ((K : ℝ) - v)) :=
      mul_le_mul hpow (hinvNext.trans hInvCompare)
        (inv_nonneg.mpr (hnegLogPos j.succ).le)
        (by positivity : 0 ≤ r ^ (idx j.succ - idx j.castSucc - 1))
    calc
      _ ≤ (G / ρ) ^ (idx j.succ - idx j.castSucc - 1) *
          (-Real.log (T j.succ))⁻¹ :=
        mul_le_mul_of_nonneg_right (hstep j) (inv_nonneg.mpr (hnegLogPos j.succ).le)
      _ ≤ _ := hfactor
      _ = r ^ (idx j.succ - idx j.castSucc) / ((K : ℝ) - v) := by
        rw [div_eq_mul_inv, ← mul_assoc, ← pow_succ, hgapEq]
        rfl
  have hQfactor :
      Real.log (T 0 / S 0) *
          (∏ j : Fin m, T j.castSucc / S j.succ) *
          ∏ j : Fin (m + 1), (-Real.log (T j))⁻¹ =
        (Real.log (T 0 / S 0) * (-Real.log (T 0))⁻¹) *
          ∏ j : Fin m,
            (T j.castSucc / S j.succ * (-Real.log (T j.succ))⁻¹) := by
    rw [Fin.prod_univ_succ]
    calc
      _ = (Real.log (T 0 / S 0) * (-Real.log (T 0))⁻¹) *
          ((∏ j : Fin m, T j.castSucc / S j.succ) *
            ∏ j : Fin m, (-Real.log (T j.succ))⁻¹) := by ring
      _ = _ := by rw [← Finset.prod_mul_distrib]
  have hprod :
      (∏ j : Fin m, T j.castSucc / S j.succ * (-Real.log (T j.succ))⁻¹) ≤
        r ^ (v - u) / ((K : ℝ) - v) ^ m := by
    calc
      _ ≤ ∏ j : Fin m,
          (r ^ (idx j.succ - idx j.castSucc) / ((K : ℝ) - v)) :=
        Finset.prod_le_prod₀ (fun j hj => mul_nonneg
            (div_nonneg (hTpos j.castSucc).le (hSpos j.succ).le)
            (inv_nonneg.mpr (hnegLogPos j.succ).le))
          (fun j hj => hstepBound j)
      _ = r ^ (∑ j : Fin m, (idx j.succ - idx j.castSucc)) /
          ((K : ℝ) - v) ^ m := by
        rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = _ := by rw [hsumDelta]
  have hDpow : ((K : ℝ) - v) ≤ ((K : ℝ) - v) ^ m := by
    calc
      _ = ((K : ℝ) - v) ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hD (by omega)
  have hprod' :
      r ^ (v - u) / ((K : ℝ) - v) ^ m ≤
        r ^ (v - u) / ((K : ℝ) - v) :=
    div_le_div_of_nonneg_left (pow_nonneg hr.le _) hDpos hDpow
  calc
    _ = (Real.log (T 0 / S 0) * (-Real.log (T 0))⁻¹) *
        ∏ j : Fin m,
          (T j.castSucc / S j.succ * (-Real.log (T j.succ))⁻¹) := hQfactor
    _ ≤ (G ^ 2 / ((K : ℝ) - u)) *
        (r ^ (v - u) / ((K : ℝ) - v)) :=
      mul_le_mul hfirstFactor (hprod.trans hprod')
        (Finset.prod_nonneg fun j hj => mul_nonneg
          (div_nonneg (hTpos j.castSucc).le (hSpos j.succ).le)
          (inv_nonneg.mpr (hnegLogPos j.succ).le))
        (by positivity : 0 ≤ G ^ 2 / ((K : ℝ) - u))
    _ = _ := by dsimp [r]; ring

/-- The open renewal-chain factor has a geometric bound with one fewer rate step and one endpoint loss. -/
theorem openBackwardFactor_le_occupiedRate
    {K u v m : ℕ} {ρ L G : ℝ} (idx : Fin (m + 2) → ℕ)
    (S T : Fin (m + 2) → ℝ)
    (hG : 1 ≤ G) (hL : 1 ≤ L) (hLleρ : L ≤ ρ)
    (huv : u < v) (hvK : v + 1 ≤ K)
    (hidx0 : idx 0 = u) (hidxlast : idx (Fin.last (m + 1)) = v)
    (hidxBound : ∀ j, idx j ≤ v)
    (hidxMono : StrictMono idx)
    (hSpos : ∀ j, 0 < S j) (hTpos : ∀ j, 0 < T j)
    (hTlt : ∀ j : Fin (m + 1), T j.castSucc < 1)
    (hSleT : S 0 ≤ T 0)
    (hlogfirst : Real.log (T 0 / S 0) ≤ G * L)
    (hlogcell : ∀ j : Fin (m + 1),
      ((K : ℝ) - idx j.castSucc) * L ≤ G * (-Real.log (T j.castSucc)))
    (hstep : ∀ j : Fin (m + 1),
      T j.castSucc / S j.succ ≤
        (G / ρ) ^ (idx j.succ - idx j.castSucc - 1))
    (hsumDelta : ∑ j : Fin (m + 1),
      (idx j.succ - idx j.castSucc) = v - u) :
    Real.log (T 0 / S 0) *
        (∏ j : Fin (m + 1), T j.castSucc / S j.succ) *
        ∏ j : Fin (m + 1), (-Real.log (T j.castSucc))⁻¹ ≤
      G ^ 2 / ((K : ℝ) - u) *
        (G / L) ^ (v - u - 1) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hρpos : 0 < ρ := lt_of_lt_of_le hLpos hLleρ
  have hU : 1 ≤ (K : ℝ) - (u : ℝ) := by
    have hvKreal : (v : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast hvK
    have huKnat : u + 1 ≤ K := by omega
    have huKreal : (u : ℝ) + 1 ≤ (K : ℝ) := by exact_mod_cast huKnat
    linarith
  have hUpos : 0 < (K : ℝ) - u := by linarith
  have hfirstInv : (-Real.log (T 0))⁻¹ ≤ G / (((K : ℝ) - u) * L) := by
    have hfirstLogCell : ((K : ℝ) - u) * L ≤ G * (-Real.log (T 0)) := by
      simpa only [Fin.castSucc_zero, hidx0] using hlogcell 0
    exact inv_negLog_le_div_of_mul_le hUpos hLpos (hTpos 0) (hTlt 0) hfirstLogCell
  have hfirstLogNonneg : 0 ≤ Real.log (T 0 / S 0) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (hSpos 0)]
    linarith
  have hnegLogPos (j : Fin (m + 1)) : 0 < -Real.log (T j.castSucc) :=
    neg_pos.mpr (Real.log_neg (hTpos j.castSucc) (hTlt j))
  have hfirstFactor : Real.log (T 0 / S 0) * (-Real.log (T 0))⁻¹ ≤
      G ^ 2 / ((K : ℝ) - u) := by
    calc
      _ ≤ (G * L) * (G / (((K : ℝ) - u) * L)) :=
        mul_le_mul hlogfirst hfirstInv (inv_nonneg.mpr (hnegLogPos 0).le)
          (by positivity : 0 ≤ G * L)
      _ = _ := by field_simp [ne_of_gt hUpos, ne_of_gt hLpos]
  have hbase : G / ρ ≤ G / L :=
    div_le_div_of_nonneg_left (by linarith : 0 ≤ G) hLpos hLleρ
  let r : ℝ := G / L
  have hr : 0 < r := div_pos (by linarith : 0 < G) hLpos
  have hstepPrefix (j : Fin m) :
      T j.castSucc.castSucc / S j.castSucc.succ *
          (-Real.log (T j.castSucc.succ))⁻¹ ≤
        r ^ (idx j.castSucc.succ - idx j.castSucc.castSucc) := by
    have hnextDen : 1 * L ≤ ((K : ℝ) - idx j.succ.castSucc) * L := by
      have hcast : (1 : ℝ) ≤ (K : ℝ) - idx j.succ.castSucc := by
        have hidx' : idx (j.succ.castSucc) ≤ v := hidxBound (j.succ.castSucc)
        have hidxnat : idx (j.succ.castSucc) + 1 ≤ K := by omega
        have hidxreal : (idx j.succ.castSucc : ℝ) + 1 ≤ (K : ℝ) := by
          exact_mod_cast hidxnat
        linarith
      exact mul_le_mul_of_nonneg_right hcast hLpos.le
    have hinv' : (-Real.log (T j.succ.castSucc))⁻¹ ≤ G / L := by
      have hlog := hlogcell j.succ
      have hlower : L ≤ ((K : ℝ) - idx j.succ.castSucc) * L := by
        simpa using hnextDen
      have hbound := hlower.trans hlog
      have hinv' := inv_negLog_le_div_of_mul_le (by norm_num : (0 : ℝ) < 1)
        hLpos (hTpos j.succ.castSucc) (hTlt j.succ) (by simpa only [one_mul] using hbound)
      simpa using hinv'
    have hinv : (-Real.log (T j.castSucc.succ))⁻¹ ≤ G / L := by
      simpa only [Fin.castSucc_succ] using hinv'
    have hInvLeR : G / L ≤ r := le_rfl
    have hpow : (G / ρ) ^
        (idx j.castSucc.succ - idx j.castSucc.castSucc - 1) ≤
        r ^ (idx j.castSucc.succ - idx j.castSucc.castSucc - 1) :=
      pow_le_pow_left₀ (div_nonneg (by linarith) hρpos.le) hbase _
    have hgap : 0 < idx j.castSucc.succ - idx j.castSucc.castSucc := by
      have hfin : j.castSucc.castSucc < j.castSucc.succ := Fin.castSucc_lt_succ
      have := hidxMono hfin
      omega
    have hgapEq : idx j.castSucc.succ - idx j.castSucc.castSucc - 1 + 1 =
        idx j.castSucc.succ - idx j.castSucc.castSucc := by omega
    calc
      _ ≤ (G / ρ) ^
          (idx j.castSucc.succ - idx j.castSucc.castSucc - 1) *
          (-Real.log (T j.castSucc.succ))⁻¹ := by
        have h := mul_le_mul_of_nonneg_right (hstep j.castSucc)
          (inv_nonneg.mpr (by simpa only [Fin.castSucc_succ] using (hnegLogPos j.succ).le))
        simpa only [Fin.castSucc_succ] using h
      _ ≤ r ^ (idx j.castSucc.succ - idx j.castSucc.castSucc - 1) * r :=
        mul_le_mul hpow (hinv.trans hInvLeR)
          (inv_nonneg.mpr (by simpa only [Fin.castSucc_succ] using (hnegLogPos j.succ).le))
          (by positivity : 0 ≤ r ^ (idx j.castSucc.succ - idx j.castSucc.castSucc - 1))
      _ = _ := by rw [← pow_succ, hgapEq]
  have hlastStep :
      T (Fin.last m).castSucc / S (Fin.last m).succ ≤
        r ^ (idx (Fin.last m).succ - idx (Fin.last m).castSucc - 1) := by
    calc
      _ ≤ (G / ρ) ^ (idx (Fin.last m).succ - idx (Fin.last m).castSucc - 1) :=
        hstep (Fin.last m)
      _ ≤ _ := pow_le_pow_left₀ (div_nonneg (by linarith) hρpos.le) hbase _
  let R : Fin (m + 1) → ℝ := fun j => T j.castSucc / S j.succ
  let I : Fin (m + 1) → ℝ := fun j => (-Real.log (T j.castSucc))⁻¹
  have hQfactor :
      Real.log (T 0 / S 0) *
          (∏ j : Fin (m + 1), T j.castSucc / S j.succ) *
          ∏ j : Fin (m + 1), (-Real.log (T j.castSucc))⁻¹ =
        (Real.log (T 0 / S 0) * (-Real.log (T 0))⁻¹) *
          (∏ j : Fin m,
            (T j.castSucc.castSucc / S j.castSucc.succ *
              (-Real.log (T j.castSucc.succ))⁻¹)) *
          (T (Fin.last m).castSucc / S (Fin.last m.succ)) := by
    change Real.log (T 0 / S 0) * (∏ j : Fin (m + 1), R j) *
      (∏ j : Fin (m + 1), I j) = _
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_succ]
    simp only [R, I, Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last]
    calc
      _ = (Real.log (T 0 / S 0) * (-Real.log (T 0))⁻¹) *
          ((∏ j : Fin m, T j.castSucc.castSucc / S j.castSucc.succ) *
            ∏ j : Fin m, (-Real.log (T j.castSucc.succ))⁻¹) *
          (T (Fin.last m).castSucc / S (Fin.last m.succ)) := by ring
      _ = _ := by rw [← Finset.prod_mul_distrib]
  have hprodPrefix :
      (∏ j : Fin m,
        (T j.castSucc.castSucc / S j.castSucc.succ *
          (-Real.log (T j.castSucc.succ))⁻¹)) ≤
        r ^ (∑ j : Fin m, (idx j.castSucc.succ - idx j.castSucc.castSucc)) := by
    calc
      _ ≤ ∏ j : Fin m, r ^ (idx j.castSucc.succ - idx j.castSucc.castSucc) :=
        Finset.prod_le_prod₀
          (fun j hj => mul_nonneg
            (div_nonneg (hTpos j.castSucc.castSucc).le (hSpos j.castSucc.succ).le)
            (inv_nonneg.mpr (by simpa only [Fin.castSucc_succ] using (hnegLogPos j.succ).le)))
          (fun j hj => hstepPrefix j)
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum]
  have hsumPrefixLast :
      (∑ j : Fin m, (idx j.castSucc.succ - idx j.castSucc.castSucc)) +
          (idx (Fin.last m).succ - idx (Fin.last m).castSucc) = v - u := by
    simpa only [Fin.sum_univ_castSucc, ← Fin.castSucc_succ, Fin.castSucc_zero,
      Fin.succ_last] using hsumDelta
  have hlastGap : 1 ≤ idx (Fin.last m).succ - idx (Fin.last m).castSucc := by
    have hfin : (Fin.last m).castSucc < (Fin.last m).succ := Fin.castSucc_lt_succ
    have hlt := hidxMono hfin
    omega
  have hsumRate :
      (∑ j : Fin m, (idx j.castSucc.succ - idx j.castSucc.castSucc)) +
          (idx (Fin.last m).succ - idx (Fin.last m).castSucc - 1) = v - u - 1 := by
    omega
  have hprodLast :
      (∏ j : Fin m,
        (T j.castSucc.castSucc / S j.castSucc.succ *
          (-Real.log (T j.castSucc.succ))⁻¹)) *
        (T (Fin.last m).castSucc / S (Fin.last m.succ)) ≤
        r ^ (v - u - 1) := by
    calc
      _ ≤ r ^ (∑ j : Fin m, (idx j.castSucc.succ - idx j.castSucc.castSucc)) *
          r ^ (idx (Fin.last m).succ - idx (Fin.last m).castSucc - 1) :=
        mul_le_mul hprodPrefix hlastStep
          (div_nonneg (hTpos (Fin.last m).castSucc).le
            (hSpos (Fin.last m).succ).le)
          (by positivity : 0 ≤ r ^
            (∑ j : Fin m, (idx j.castSucc.succ - idx j.castSucc.castSucc)))
      _ = _ := by rw [← pow_add, hsumRate]
  have hprodOpenNonneg : 0 ≤
      (∏ j : Fin m,
        (T j.castSucc.castSucc / S j.castSucc.succ *
          (-Real.log (T j.castSucc.succ))⁻¹)) *
        (T (Fin.last m).castSucc / S (Fin.last m.succ)) := by
    apply mul_nonneg
    · exact Finset.prod_nonneg fun j hj => mul_nonneg
        (div_nonneg (hTpos j.castSucc.castSucc).le (hSpos j.castSucc.succ).le)
        (inv_nonneg.mpr (by simpa only [Fin.castSucc_succ] using (hnegLogPos j.succ).le))
    · exact div_nonneg ((hTpos (Fin.last m).castSucc).le)
        ((hSpos (Fin.last (m + 1))).le)
  calc
    _ = (Real.log (T 0 / S 0) * (-Real.log (T 0))⁻¹) *
        ((∏ j : Fin m,
          (T j.castSucc.castSucc / S j.castSucc.succ *
            (-Real.log (T j.castSucc.succ))⁻¹)) *
        (T (Fin.last m).castSucc / S (Fin.last m.succ))) := by
      simpa [mul_assoc] using hQfactor
    _ ≤ (G ^ 2 / ((K : ℝ) - u)) * r ^ (v - u - 1) :=
      mul_le_mul hfirstFactor hprodLast
        hprodOpenNonneg
        (by positivity : 0 ≤ G ^ 2 / ((K : ℝ) - u))
    _ = _ := by dsimp [r]

end Critical2DKPZ.Blocks

end

@[expose] public noncomputable section

open MeasureTheory
open Filter

namespace Critical2DKPZ.Blocks

theorem occupiedIndex_step_sum {u v : ℕ} {S : Finset ℕ}
    (huv : u < v) (hS : S ⊆ Finset.Ioo u v) :
    ∑ j : Fin (S.card + 1),
      (occupiedIndex u v S j.succ - occupiedIndex u v S j.castSucc) = v - u := by
  have hgap := sum_occupiedIndex_gap huv hS
  have hcardle : S.card ≤ v - u - 1 := by
    calc
      S.card ≤ (Finset.Ioo u v).card := Finset.card_le_card hS
      _ = v - u - 1 := by simp
  have hmono := occupiedIndex_strictMono huv hS
  have hstep (j : Fin (S.card + 1)) :
      occupiedIndex u v S j.succ - occupiedIndex u v S j.castSucc =
        (occupiedIndex u v S j.succ - occupiedIndex u v S j.castSucc - 1) + 1 := by
    have h := hmono (Fin.castSucc_lt_succ : j.castSucc < j.succ)
    omega
  calc
    _ = ∑ j : Fin (S.card + 1),
        ((occupiedIndex u v S j.succ - occupiedIndex u v S j.castSucc - 1) + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hstep j
    _ = (∑ j : Fin (S.card + 1),
          (occupiedIndex u v S j.succ - occupiedIndex u v S j.castSucc - 1)) +
        ∑ _j : Fin (S.card + 1), (1 : ℕ) := Finset.sum_add_distrib
    _ = v - u := by
      simp only [hgap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one]
      calc
        (v - u - 1 - S.card) + (S.card + 1) = v - u := by
          calc
            _ = (v - u - 1 - S.card + S.card) + 1 := by omega
            _ = (v - u - 1) + 1 := by rw [Nat.sub_add_cancel hcardle]
            _ = v - u := by omega

theorem occupied_powerset_card_le {u v : ℕ} (huv : u < v) :
    ((Finset.Ioo u v).powerset.card : ℝ) ≤ 2 ^ (v - u + 1 : ℕ) := by
  have hIoo : (Finset.Ioo u v).card ≤ v - u + 1 := by
    calc
      (Finset.Ioo u v).card ≤ (Finset.Icc u v).card :=
        Finset.card_le_card (by
          intro x hx
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioo.mp hx).1.le,
            (Finset.mem_Ioo.mp hx).2.le⟩)
      _ = v - u + 1 := by
        simp
        rw [Nat.sub_add_comm huv.le]
  have hpowerset : (Finset.Ioo u v).powerset.card = 2 ^ (Finset.Ioo u v).card :=
    Finset.card_powerset _
  have hpow : 2 ^ (Finset.Ioo u v).card ≤ 2 ^ (v - u + 1) :=
    Nat.pow_le_pow_right (by omega) hIoo
  exact_mod_cast hpowerset ▸ hpow

private theorem closedOccupiedRenewalTerm_le_of_backwardChain
    (N : ℕ) (ρ ϑ : ℝ) (u v : ℕ) (S : Finset ℕ)
    (C₅ Cchain Graw G D L : ℝ)
    (hC₅ : 0 < C₅) (hCchain : 0 < Cchain) (hDprod : C₅ * Cchain ≤ D)
    (hGrawpos : 0 < Graw) (hGrawleG : Graw ≤ G) (hG : 1 ≤ G) (hDone : 1 ≤ D)
    (hρone : 1 < ρ) (hLdef : L = Real.log ρ)
    (hLpos : 0 < L) (hLone : 1 ≤ L) (hLleρ : L ≤ ρ)
    (hN : 1 ≤ N) (hu : 1 ≤ u) (huv : u < v)
    (hvK : v + 1 ≤ blockCount N ρ)
    (hgridLocal : ∀ i, 1 ≤ i → i < blockCount N ρ →
      4 * ((blockTime N ρ (i - 1) : ℝ) + 1 / 2) ≤
        (blockTime N ρ i : ℝ) + 1 / 2)
    (hgridRatio : ∀ i j, 1 ≤ i → i ≤ j → j < blockCount N ρ →
      (blockTime N ρ i : ℝ) + 1 / 2 ≤
        (Graw / ρ) ^ (j - i) * ((blockTime N ρ j : ℝ) + 1 / 2))
    (hgridLogCell : ∀ i, 1 ≤ i → i < blockCount N ρ →
      ((blockCount N ρ : ℝ) - i) * L ≤
        Graw * -Real.log (((blockTime N ρ i : ℝ) + 1 / 2) / N))
    (hgridLogFirst : ∀ i, 1 ≤ i → i < blockCount N ρ →
      Real.log (((blockTime N ρ i : ℝ) + 1 / 2) /
        ((blockTime N ρ (i - 1) : ℝ) + 1 / 2)) ≤ Graw * L)
    (htimeMono : Monotone (blockTime N ρ))
    (htvN : blockTime N ρ v ≤ N)
    (hrenewal : ∀ (m : ℕ) (lo hi : Fin (m + 1) → ℕ),
      (∀ j, lo j < hi j) →
      (∀ j : Fin m, hi j.castSucc ≤ lo j.succ) →
      hi (Fin.last m) ≤ N →
      let Sgrid : Fin (m + 1) → ℝ := fun j => ((lo j : ℝ) + 1 / 2) / N
      let Tgrid : Fin (m + 1) → ℝ := fun j => ((hi j : ℝ) + 1 / 2) / N
      0 < Sgrid 0 → 2 * Sgrid 0 ≤ Tgrid 0 →
      (∀ j : Fin m, 4 * Sgrid j.succ ≤ Tgrid j.succ) →
      (∀ j : Fin m, Tgrid j.castSucc ≤ Sgrid j.succ) →
      (∀ j, Tgrid j < 1) →
      ENNReal.ofReal (renewalStringSum ϑ N m lo hi) ≤
        ENNReal.ofReal ((Cchain ^ (m + 1) * Real.log (Tgrid 0 / Sgrid 0) *
          (∏ j : Fin m, Tgrid j.castSucc / Sgrid j.succ)) *
          ∏ j, (-Real.log (Tgrid j))⁻¹))
    (hSsubset : S ⊆ Finset.Ioo u v) :
    let d : ℕ := v - u
    let Den : ℝ := ((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v)
    C₅ ^ (S.card + 2) * renewalStringSum ϑ N (S.card + 1)
      (occupiedLo (blockTime N ρ) u v S) (occupiedHi (blockTime N ρ) u v S) ≤
      (D ^ (d + 3) * G ^ 2 * (G / L) ^ d) / Den := by
    let d : ℕ := v - u
    let Den : ℝ := ((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v)
    change C₅ ^ (S.card + 2) * renewalStringSum ϑ N (S.card + 1)
      (occupiedLo (blockTime N ρ) u v S) (occupiedHi (blockTime N ρ) u v S) ≤
      (D ^ (d + 3) * G ^ 2 * (G / L) ^ d) / Den
    classical
    have hSbound : S.card ≤ v - u + 1 := by
      have hsub : S ⊆ Finset.Icc u v := by
        intro x hx
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ioo.mp (hSsubset hx)).1.le,
          (Finset.mem_Ioo.mp (hSsubset hx)).2.le⟩
      calc
        S.card ≤ (Finset.Icc u v).card := Finset.card_le_card hsub
        _ = v - u + 1 := by
          simp
          rw [Nat.sub_add_comm huv.le]
    have hScard : S.card + 2 ≤ d + 3 := by dsimp [d]; omega
    let M : ℕ := S.card + 1
    let idx : Fin (M + 1) → ℕ := occupiedIndex u v S
    let lo : Fin (M + 1) → ℕ := occupiedLo (blockTime N ρ) u v S
    let hi : Fin (M + 1) → ℕ := occupiedHi (blockTime N ρ) u v S
    let sh : ℕ → ℝ := fun i => (blockTime N ρ i : ℝ) + 1 / 2
    let sgrid : Fin (M + 1) → ℝ := fun j => ((lo j : ℝ) + 1 / 2) / N
    let tgrid : Fin (M + 1) → ℝ := fun j => ((hi j : ℝ) + 1 / 2) / N
    have hidx0 : idx 0 = u := by simp [idx, occupiedIndex_zero]
    have hidxlast : idx (Fin.last M) = v := by
      simpa [idx, M] using occupiedIndex_last u v S
    have hidxmono : StrictMono idx := by
      simpa [idx] using occupiedIndex_strictMono huv hSsubset
    have hidxle : ∀ j, idx j ≤ v := by
      intro j
      have hjle : j ≤ Fin.last M := Fin.le_iff_val_le_val.mpr (by
        have hjval : (j : ℕ) ≤ M := Nat.le_of_lt_succ j.isLt
        simpa using hjval)
      have h := hidxmono.monotone hjle
      simpa [hidxlast] using h
    have hidxlo : ∀ j, 1 ≤ idx j := by
      intro j
      have hjle : (0 : Fin (M + 1)) ≤ j := Fin.zero_le j
      have h := hidxmono.monotone hjle
      rw [hidx0] at h
      exact le_trans (by exact_mod_cast hu) h
    have hidxltK : ∀ j, idx j < blockCount N ρ := by
      intro j
      have h := hidxle j
      omega
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hDenu : 0 < (blockCount N ρ : ℝ) - u := by
      have huKreal : (u : ℝ) < blockCount N ρ := by
        exact_mod_cast (by omega : u < blockCount N ρ)
      exact sub_pos.mpr huKreal
    have hDenv : 0 < (blockCount N ρ : ℝ) - v := by
      have hvKreal : (v : ℝ) < blockCount N ρ := by
        exact_mod_cast (by omega : v < blockCount N ρ)
      exact sub_pos.mpr hvKreal
    have hlo : ∀ j, lo j < hi j := by
      intro j
      have hg := hgridLocal (idx j) (hidxlo j) (hidxltK j)
      have hcast : (blockTime N ρ (idx j - 1) : ℝ) <
          (blockTime N ρ (idx j) : ℝ) := by
        have hprev : 0 ≤ (blockTime N ρ (idx j - 1) : ℝ) := Nat.cast_nonneg _
        nlinarith [hg, hprev]
      dsimp [lo, hi, occupiedLo, occupiedHi]
      exact_mod_cast hcast
    have hsep : ∀ j : Fin M, hi j.castSucc ≤ lo j.succ := by
      intro j
      have hidx : idx j.castSucc ≤ idx j.succ - 1 := by
        have hstrict := hidxmono (Fin.castSucc_lt_succ : j.castSucc < j.succ)
        omega
      have hmono := htimeMono hidx
      simpa [hi, lo, occupiedHi, occupiedLo, idx] using hmono
    have hlast : hi (Fin.last M) ≤ N := by
      change blockTime N ρ (idx (Fin.last M)) ≤ N
      rw [hidxlast]
      exact htvN
    have hspos : ∀ j, 0 < sgrid j := by
      intro j
      dsimp [sgrid, lo, occupiedLo]
      positivity
    have htpos : ∀ j, 0 < tgrid j := by
      intro j
      dsimp [tgrid, hi, occupiedHi]
      positivity
    have hfirst : 2 * sgrid 0 ≤ tgrid 0 := by
      have h := hgridLocal u hu (by omega : u < blockCount N ρ)
      change 2 * (sh (idx 0 - 1) / N) ≤ sh (idx 0) / N
      rw [hidx0]
      dsimp [sh]
      have hhalf : 2 * ((blockTime N ρ (u - 1) : ℝ) + 1 / 2) ≤
          (blockTime N ρ u : ℝ) + 1 / 2 := by linarith [h]
      calc
        2 * (((blockTime N ρ (u - 1) : ℝ) + 1 / 2) / N) =
            (2 * ((blockTime N ρ (u - 1) : ℝ) + 1 / 2)) / N := by ring
        _ ≤ ((blockTime N ρ u : ℝ) + 1 / 2) / N :=
          div_le_div_of_nonneg_right hhalf hNpos.le
    have hblock : ∀ j : Fin M, 4 * sgrid j.succ ≤ tgrid j.succ := by
      intro j
      have hiidx := hidxlo j.succ
      have h := hgridLocal (idx j.succ) hiidx (hidxltK j.succ)
      change 4 * (sh (idx j.succ - 1) / N) ≤ sh (idx j.succ) / N
      dsimp [sh]
      calc
        4 * (((blockTime N ρ (idx j.succ - 1) : ℝ) + 1 / 2) / N) =
            (4 * ((blockTime N ρ (idx j.succ - 1) : ℝ) + 1 / 2)) / N := by ring
        _ ≤ ((blockTime N ρ (idx j.succ) : ℝ) + 1 / 2) / N :=
          div_le_div_of_nonneg_right h hNpos.le
    have hchain : ∀ j : Fin M, tgrid j.castSucc ≤ sgrid j.succ := by
      intro j
      have hnat : blockTime N ρ (idx j.castSucc) ≤
          blockTime N ρ (idx j.succ - 1) := by
        simpa [hi, lo, occupiedHi, occupiedLo] using hsep j
      change sh (idx j.castSucc) / N ≤ sh (idx j.succ - 1) / N
      have hcast : (blockTime N ρ (idx j.castSucc) : ℝ) ≤
          blockTime N ρ (idx j.succ - 1) := by exact_mod_cast hnat
      have hshift : sh (idx j.castSucc) ≤ sh (idx j.succ - 1) := by
        dsimp [sh]
        linarith [hcast]
      exact div_le_div_of_nonneg_right hshift hNpos.le
    have htlt : ∀ j, tgrid j < 1 := by
      intro j
      have hiidx := hidxlo j
      have h := hgridLogCell (idx j) hiidx (hidxltK j)
      have hleft : 0 < ((blockCount N ρ : ℝ) - idx j) * L := by
        have hidxReal : (idx j : ℝ) < blockCount N ρ := by exact_mod_cast hidxltK j
        have hdiff : 0 < (blockCount N ρ : ℝ) - idx j := by exact sub_pos.mpr hidxReal
        rw [hLdef]
        exact mul_pos hdiff (Real.log_pos hρone)
      have hleft' := hleft
      have hgridLog : ((blockCount N ρ : ℝ) - idx j) * L ≤
          Graw * (-Real.log (tgrid j)) := by
        simpa only [tgrid, hi, occupiedHi, idx] using h
      have hlogneg : Real.log (tgrid j) < 0 := by
        have hneglog : 0 < -Real.log (tgrid j) := by
          by_contra hnot
          have hnonpos : -Real.log (tgrid j) ≤ 0 := le_of_not_gt hnot
          have hprod : Graw * (-Real.log (tgrid j)) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hGrawpos.le hnonpos
          linarith only [hleft', hgridLog, hprod]
        exact neg_pos.mp hneglog
      exact (Real.log_neg_iff (htpos j)).1 hlogneg
    have hlogfirst : Real.log (tgrid 0 / sgrid 0) ≤ G * L := by
      have h := hgridLogFirst u hu (by omega : u < blockCount N ρ)
      have hratio : tgrid 0 / sgrid 0 =
          ((blockTime N ρ u : ℝ) + 1 / 2) /
            ((blockTime N ρ (u - 1) : ℝ) + 1 / 2) := by
        simp [tgrid, sgrid, hi, lo, occupiedHi, occupiedLo,
          occupiedIndex_zero]
        field_simp [ne_of_gt hNpos]
      have hraw : Real.log (tgrid 0 / sgrid 0) ≤ Graw * L := by
        rw [hratio]
        simpa [hLdef] using h
      exact hraw.trans (mul_le_mul_of_nonneg_right hGrawleG hLpos.le)
    have hlogcell : ∀ j, ((blockCount N ρ : ℝ) - idx j) * L ≤
        G * (-Real.log (tgrid j)) := by
      intro j
      have h := hgridLogCell (idx j) (hidxlo j) (hidxltK j)
      have hraw : ((blockCount N ρ : ℝ) - idx j) * L ≤
          Graw * (-Real.log (tgrid j)) := by
        simpa only [tgrid, hi, occupiedHi, idx] using h
      exact hraw.trans (mul_le_mul_of_nonneg_right hGrawleG
        (by have h := Real.log_neg (htpos j) (htlt j); linarith))
    have hstep : ∀ j : Fin M,
        tgrid j.castSucc / sgrid j.succ ≤
          (G / ρ) ^ (idx j.succ - idx j.castSucc - 1) := by
      intro j
      have hidxstep := hidxmono (Fin.castSucc_lt_succ : j.castSucc < j.succ)
      let a := idx j.castSucc
      let b := idx j.succ - 1
      have ha : 1 ≤ a := by dsimp [a]; exact hidxlo j.castSucc
      have hab : a ≤ b := by dsimp [a, b]; omega
      have hbK : b < blockCount N ρ := by
        dsimp [b]
        have := hidxltK j.succ
        omega
      have hgridratio := hgridRatio a b ha hab hbK
      have hbase : Graw / ρ ≤ G / ρ :=
        div_le_div_of_nonneg_right hGrawleG (by linarith : 0 ≤ ρ)
      have hshpos : 0 < sh b := by dsimp [sh]; positivity
      have hratioRaw : sh a / sh b ≤ (Graw / ρ) ^ (b - a) :=
        (div_le_iff₀ hshpos).2 hgridratio
      have hratio : sh a / sh b ≤ (G / ρ) ^ (b - a) :=
        hratioRaw.trans (pow_le_pow_left₀
          (div_nonneg hGrawpos.le (by linarith : 0 ≤ ρ)) hbase _)
      have heq : tgrid j.castSucc / sgrid j.succ = sh a / sh b := by
        dsimp [tgrid, sgrid, hi, lo, occupiedHi, occupiedLo, idx, sh, a, b]
        field_simp
      have hexp : b - a = idx j.succ - idx j.castSucc - 1 := by
        dsimp [a, b]
        omega
      rw [heq, ← hexp]
      exact hratio
    have hsumDelta : ∑ j : Fin M, (idx j.succ - idx j.castSucc) = v - u := by
      simpa [idx, M] using occupiedIndex_step_sum huv hSsubset
    have hSleT : sgrid 0 ≤ tgrid 0 := by nlinarith [hfirst, hspos 0]
    have hfactor := closedBackwardFactor_le_occupiedRate idx sgrid tgrid
      (by linarith [hG]) hLone hLleρ (by omega) huv hvK hidx0 hidxlast hidxle hidxmono
      hspos htpos htlt hSleT hlogfirst hlogcell hstep hsumDelta
    have hlognonneg : 0 ≤ Real.log (tgrid 0 / sgrid 0) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (hspos 0)]
      simpa only [one_mul] using hSleT
    have hqnonneg : 0 ≤ Real.log (tgrid 0 / sgrid 0) *
        (∏ j : Fin M, tgrid j.castSucc / sgrid j.succ) *
        ∏ j, (-Real.log (tgrid j))⁻¹ := by
      apply mul_nonneg
      · apply mul_nonneg hlognonneg
        exact Finset.prod_nonneg fun j _ => div_nonneg (htpos _).le (hspos _).le
      · exact Finset.prod_nonneg fun j _ => inv_nonneg.mpr (neg_pos.mpr
          (Real.log_neg (htpos _) (htlt _))).le
    have hsposRaw : ∀ j, 0 < ((lo j : ℝ) + 1 / 2) / N := by
      simpa only [sgrid] using hspos
    have htposRaw : ∀ j, 0 < ((hi j : ℝ) + 1 / 2) / N := by
      simpa only [tgrid] using htpos
    have hfirstRaw : 2 * (((lo 0 : ℝ) + 1 / 2) / N) ≤
        ((hi 0 : ℝ) + 1 / 2) / N := by simpa only [sgrid, tgrid] using hfirst
    have hblockRaw : ∀ j : Fin M,
        4 * (((lo j.succ : ℝ) + 1 / 2) / N) ≤
          ((hi j.succ : ℝ) + 1 / 2) / N := by
      simpa only [sgrid, tgrid] using hblock
    have hchainRaw : ∀ j : Fin M,
        ((hi j.castSucc : ℝ) + 1 / 2) / N ≤
          ((lo j.succ : ℝ) + 1 / 2) / N := by
      simpa only [sgrid, tgrid] using hchain
    have htltRaw : ∀ j, ((hi j : ℝ) + 1 / 2) / N < 1 := by
      simpa only [tgrid] using htlt
    have hchainBound := hrenewal M lo hi hlo hsep hlast
      (hsposRaw 0) hfirstRaw hblockRaw hchainRaw htltRaw
    have hGpos : 0 < G := lt_of_lt_of_le zero_lt_one hG
    have hfactorPos : 0 <
        G ^ 2 / ((blockCount N ρ : ℝ) - u) *
          (G / L) ^ d / ((blockCount N ρ : ℝ) - v) := by
      have hfirstPos : 0 < G ^ 2 / ((blockCount N ρ : ℝ) - u) :=
        div_pos (sq_pos_of_pos hGpos) hDenu
      have hpowerPos : 0 < (G / L) ^ d := pow_pos (div_pos hGpos hLpos) _
      exact div_pos (mul_pos hfirstPos hpowerPos) hDenv
    have hrenewalTargetPos : 0 < Cchain ^ (M + 1) *
        (G ^ 2 / ((blockCount N ρ : ℝ) - u) *
          (G / L) ^ d / ((blockCount N ρ : ℝ) - v)) :=
      mul_pos (pow_pos hCchain _) hfactorPos
    have hrealRenewal : renewalStringSum ϑ N M lo hi ≤
        Cchain ^ (M + 1) *
          (G ^ 2 / ((blockCount N ρ : ℝ) - u) *
            (G / L) ^ d / ((blockCount N ρ : ℝ) - v)) := by
      apply (ENNReal.ofReal_le_ofReal_iff hrenewalTargetPos.le).mp
      calc
        ENNReal.ofReal (renewalStringSum ϑ N M lo hi) ≤
            ENNReal.ofReal (Cchain ^ (M + 1) *
              (Real.log (tgrid 0 / sgrid 0) *
              (∏ j : Fin M, tgrid j.castSucc / sgrid j.succ) *
                ∏ j, (-Real.log (tgrid j))⁻¹)) := by
          simpa only [sgrid, tgrid, M, mul_assoc] using hchainBound
        _ ≤ ENNReal.ofReal (Cchain ^ (M + 1) *
              (G ^ 2 / ((blockCount N ρ : ℝ) - u) *
                (G / L) ^ d / ((blockCount N ρ : ℝ) - v))) := by
          apply ENNReal.ofReal_le_ofReal
          have hpow : 0 ≤ Cchain ^ (M + 1) := pow_nonneg hCchain.le _
          have hfactor' :
              Real.log (tgrid 0 / sgrid 0) *
                (∏ j : Fin M, tgrid j.castSucc / sgrid j.succ) *
                ∏ j, (-Real.log (tgrid j))⁻¹ ≤
              G ^ 2 / ((blockCount N ρ : ℝ) - u) *
                (G / L) ^ d / ((blockCount N ρ : ℝ) - v) := by
              simpa [hLdef, d] using hfactor
          exact mul_le_mul_of_nonneg_left hfactor' hpow
    have hprodPow : C₅ ^ (S.card + 2) * Cchain ^ (M + 1) ≤ D ^ (d + 3) := by
      have heq : C₅ ^ (S.card + 2) * Cchain ^ (M + 1) =
          (C₅ * Cchain) ^ (S.card + 2) := by
        simp [M, ← mul_pow]
      rw [heq]
      calc
        (C₅ * Cchain) ^ (S.card + 2) ≤ D ^ (S.card + 2) :=
          pow_le_pow_left₀ (by positivity) hDprod _
        _ ≤ D ^ (d + 3) := pow_le_pow_right₀ hDone hScard
    have hfactorNonneg : 0 ≤
        G ^ 2 / ((blockCount N ρ : ℝ) - u) *
          (G / L) ^ d / ((blockCount N ρ : ℝ) - v) := hfactorPos.le
    calc
      _ ≤ C₅ ^ (S.card + 2) *
          (Cchain ^ (M + 1) *
            (G ^ 2 / ((blockCount N ρ : ℝ) - u) *
              (G / L) ^ d / ((blockCount N ρ : ℝ) - v))) :=
        mul_le_mul_of_nonneg_left hrealRenewal (pow_nonneg hC₅.le _)
      _ ≤ D ^ (d + 3) *
          (G ^ 2 / ((blockCount N ρ : ℝ) - u) *
            (G / L) ^ d / ((blockCount N ρ : ℝ) - v)) := by
        calc
          _ = (C₅ ^ (S.card + 2) * Cchain ^ (M + 1)) *
              (G ^ 2 / ((blockCount N ρ : ℝ) - u) *
                (G / L) ^ d / ((blockCount N ρ : ℝ) - v)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hprodPow hfactorNonneg
      _ = (D ^ (d + 3) * G ^ 2 * (G / L) ^ d) / Den := by
        dsimp [Den]
        field_simp [ne_of_gt hDenu, ne_of_gt hDenv, ne_of_gt hLpos]


private theorem powerset_renewal_algebra (d : ℕ) (D G Den L : ℝ)
    (hDen : Den ≠ 0) (hL : L ≠ 0) :
    2 ^ (d + 1) * ((D ^ (d + 3) * G ^ 2 * (G / L) ^ d) / Den) =
      (2 * D ^ 3 * G ^ 2 * (2 * D * G) ^ d) / (Den * L ^ d) := by
  have hprodPow : (2 * D * G) ^ d = 2 ^ d * D ^ d * G ^ d := by
    rw [mul_pow, mul_pow]
  have hnum : 2 ^ (d + 1) * (D ^ (d + 3) * G ^ 2 * G ^ d) =
      2 * D ^ 3 * G ^ 2 * (2 * D * G) ^ d := by
    rw [pow_add, pow_add, hprodPow]
    ring
  rw [div_pow]
  calc
    _ = (2 ^ (d + 1) * (D ^ (d + 3) * G ^ 2 * G ^ d)) /
        (Den * L ^ d) := by
      field_simp [hDen, hL]
    _ = _ := by rw [hnum]

/-- The closed discrepancy has a geometric second-moment bound with two endpoint losses and integrability supplied by `memLp_closedDiscrepancy` at `p = 2`. -/
theorem closedDiscrepancy_sq_integral_le (A : ℝ) :
    ∃ C C₀ : ℝ, 0 < C₀ ∧ ∀ ρ : ℝ, Real.exp (C₀ ^ 2) < ρ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ u v : ℕ, 1 ≤ u → u < v → v + 1 ≤ blockCount N ρ →
        ∫ ω, closedDiscrepancy (criticalBeta ϑ N) (blockTime N ρ) u v ω ^ 2 ∂disorderLaw ≤
          (C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u)) ^ 2 /
            (((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v)) := by
  obtain ⟨C₅, hC₅, hstring⟩ := closedStringSum_le_renewalStringSum A
  obtain ⟨Graw, ρ₀, hGraw, hρ₀, hgridRaw⟩ := halfShiftedGrid_bounds
  let G : ℝ := max 1 Graw
  have hG : 1 ≤ G := by dsimp [G]; exact le_max_left _ _
  have hGrawleG : Graw ≤ G := by dsimp [G]; exact le_max_right _ _
  have hGpos : 0 < G := lt_of_lt_of_le zero_lt_one hG
  have hGrawpos : 0 < Graw := hGraw
  obtain ⟨Cchain, hCchain, hrenewal⟩ := renewalStringSum_backwardChain_le A
  let D : ℝ := max 2 (max (C₅ * Cchain) G)
  let C : ℝ := 2 * D ^ 2 * G
  let C₀ : ℝ := 2 * D * G + Real.sqrt (Real.log ρ₀) + 1
  have hDtwo : 2 ≤ D := by dsimp [D]; exact le_max_left _ _
  have hDprod : C₅ * Cchain ≤ D := by
    dsimp [D]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hDG : G ≤ D := by
    dsimp [D]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hDpos : 0 < D := by linarith
  have hDone : 1 ≤ D := by linarith
  have hC₀pos : 0 < C₀ := by
    dsimp [C₀]
    have hlog₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
    positivity
  have hC₀base : 2 * D * G ≤ C₀ := by
    dsimp [C₀]
    have hlog₀ : 0 ≤ Real.log ρ₀ := (Real.log_pos hρ₀).le
    have hsqrt : 0 ≤ Real.sqrt (Real.log ρ₀) := Real.sqrt_nonneg _
    linarith
  have hρ₀exp : ρ₀ ≤ Real.exp (C₀ ^ 2) := by
    have hlog₀ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
    have hsqrtSq : (Real.sqrt (Real.log ρ₀)) ^ 2 = Real.log ρ₀ :=
      Real.sq_sqrt hlog₀.le
    have hrootle : Real.sqrt (Real.log ρ₀) ≤ C₀ := by
      dsimp [C₀]
      nlinarith [Real.sqrt_nonneg (Real.log ρ₀), hDpos, hGpos]
    have hsqle : Real.log ρ₀ ≤ C₀ ^ 2 := by nlinarith [Real.sqrt_nonneg (Real.log ρ₀)]
    calc
      ρ₀ = Real.exp (Real.log ρ₀) := (Real.exp_log (by linarith : 0 < ρ₀)).symm
      _ ≤ Real.exp (C₀ ^ 2) := Real.exp_le_exp.mpr hsqle
  refine ⟨C, C₀, hC₀pos, ?_⟩
  intro ρ hρ
  have hlogρ : C₀ ^ 2 < Real.log ρ := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hρ
  have hρlarge : ρ₀ ≤ ρ := (lt_of_le_of_lt hρ₀exp hρ).le
  have hρone : 1 < ρ := by
    have hC₀sq : 0 < C₀ ^ 2 := sq_pos_of_pos hC₀pos
    have hexp : 1 < Real.exp (C₀ ^ 2) := by
      simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hC₀sq
    exact lt_trans hexp hρ
  have hLpos : 0 < Real.log ρ := Real.log_pos hρone
  have hLone : 1 ≤ Real.log ρ := by
    have hDGe : 1 ≤ 2 * D * G := by nlinarith [hDtwo, hG]
    have hC₀ge : 1 ≤ C₀ := by
      dsimp [C₀]
      have hsqrt : 0 ≤ Real.sqrt (Real.log ρ₀) := Real.sqrt_nonneg _
      nlinarith [hDpos, hGpos]
    have hsq : 1 ≤ C₀ ^ 2 := by nlinarith
    linarith
  have hLleρ : Real.log ρ ≤ ρ := by
    have h := Real.log_le_sub_one_of_pos (show 0 < ρ by linarith)
    linarith
  filter_upwards [hstring, hgridRaw ρ hρlarge, blockTime_monotone hρone] with
    N hstringN hgridN htimeMono
  intro ϑ hϑ u v hu huv hvK
  have hK : 1 ≤ blockCount N ρ := by omega
  have hKne : blockCount N ρ ≠ 0 := by omega
  have hN : 1 ≤ N := by
    by_contra hn
    have hNzero : N = 0 := by omega
    subst N
    have hsepU := hgridN.1 u hu (by omega : u < blockCount 0 ρ)
    have htimeU : blockTime 0 ρ u = 0 := by simp [blockTime]
    have htimePrev : blockTime 0 ρ (u - 1) = 0 := by simp [blockTime]
    rw [htimeU, htimePrev] at hsepU
    norm_num at hsepU
  have hKtime : blockTime N ρ (blockCount N ρ) = N := by
    simp [blockTime, hKne]
  have htvN : blockTime N ρ v ≤ N := by
    have hle := htimeMono (show v ≤ blockCount N ρ by omega)
    simpa [hKtime] using hle
  have hmonoOn : MonotoneOn (blockTime N ρ) (Set.Iic v) := by
    intro i hi j hj hij
    exact htimeMono hij
  have hsum := hstringN ϑ hϑ (blockTime N ρ) u v hmonoOn htvN hu huv
  rw [closedDiscrepancy_sq_integral_eq (criticalBeta ϑ N)
    (t := blockTime N ρ) (u := u) (v := v) hmonoOn hu huv]
  have hKreal : (v : ℝ) + 1 ≤ (blockCount N ρ : ℝ) := by exact_mod_cast hvK
  let L : ℝ := Real.log ρ
  let d : ℕ := v - u
  let Den : ℝ := ((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v)
  have hDenu : 0 < (blockCount N ρ : ℝ) - u := by
    have huK : u + 1 ≤ blockCount N ρ := by omega
    have huKreal : (u : ℝ) < blockCount N ρ := by exact_mod_cast (by omega : u < blockCount N ρ)
    exact sub_pos.mpr huKreal
  have hDenv : 0 < (blockCount N ρ : ℝ) - v := by
    have hvKreal' : (v : ℝ) < blockCount N ρ := by exact_mod_cast (by omega : v < blockCount N ρ)
    exact sub_pos.mpr hvKreal'
  have hDenpos : 0 < Den := by dsimp [Den]; positivity
  have hcardBase : 1 ≤ 2 * D * G := by
    have hGone : 1 ≤ G := by linarith
    nlinarith
  have hC0large : 2 * D * G ≤ C₀ := hC₀base
  have hterm : ∀ S ∈ (Finset.Ioo u v).powerset,
      C₅ ^ (S.card + 2) *
          renewalStringSum ϑ N (S.card + 1)
            (occupiedLo (blockTime N ρ) u v S) (occupiedHi (blockTime N ρ) u v S) ≤
        (D ^ (d + 3) * G ^ 2 * (G / L) ^ d) / Den := by
    intro S hSmem
    exact closedOccupiedRenewalTerm_le_of_backwardChain
      N ρ ϑ u v S C₅ Cchain Graw G D L hC₅ hCchain hDprod
      hGrawpos hGrawleG hG hDone hρone rfl hLpos hLone hLleρ hN hu huv hvK
      hgridN.1 hgridN.2.1 hgridN.2.2.1 hgridN.2.2.2 htimeMono htvN
      (hrenewal N hN ϑ hϑ) (Finset.mem_powerset.mp hSmem)
  have htermUniform := Finset.sum_le_sum hterm
  have hcardPower : ((Finset.Ioo u v).powerset.card : ℝ) ≤ 2 ^ (d + 1 : ℕ) := by
    have h := occupied_powerset_card_le huv
    simpa [d] using h
  have hsumCoarse :
      ∑ S ∈ (Finset.Ioo u v).powerset,
        C₅ ^ (S.card + 2) *
          renewalStringSum ϑ N (S.card + 1)
            (occupiedLo (blockTime N ρ) u v S) (occupiedHi (blockTime N ρ) u v S) ≤
        (2 * D ^ 3 * G ^ 2 * (2 * D * G) ^ d) / (Den * L ^ d) := by
    calc
      _ ≤ ∑ S ∈ (Finset.Ioo u v).powerset,
          (D ^ (d + 3) * G ^ 2 * (G / L) ^ d) / Den := by
        exact htermUniform
      _ = ((Finset.Ioo u v).powerset.card : ℝ) *
          ((D ^ (d + 3) * G ^ 2 * (G / L) ^ d) / Den) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 ^ (d + 1)) *
          ((D ^ (d + 3) * G ^ 2 * (G / L) ^ d) / Den) :=
        mul_le_mul_of_nonneg_right hcardPower (by positivity)
      _ = (2 * D ^ 3 * G ^ 2 * (2 * D * G) ^ d) / (Den * L ^ d) :=
        powerset_renewal_algebra d D G Den L hDenpos.ne' hLpos.ne'
  have hsumResult := hsum.trans hsumCoarse
  have hroot : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have hrootPow : (Real.sqrt L) ^ (2 * d) = L ^ d := by
    rw [pow_mul, Real.sq_sqrt hLpos.le]
  have htargetEq : (C * (C₀ / Real.sqrt L) ^ d) ^ 2 =
      C ^ 2 * C₀ ^ (2 * d) / L ^ d := by
    calc
      _ = C ^ 2 * (C₀ / Real.sqrt L) ^ (d * 2) := by
        rw [mul_pow, ← pow_mul]
      _ = C ^ 2 * (C₀ / Real.sqrt L) ^ (2 * d) := by rw [Nat.mul_comm d 2]
      _ = C ^ 2 * (C₀ ^ (2 * d) / (Real.sqrt L) ^ (2 * d)) := by rw [div_pow]
      _ = _ := by rw [hrootPow]; ring
  have hbasepow : (2 * D * G) ^ d ≤ C₀ ^ (2 * d) := by
    have hbase : 1 ≤ 2 * D * G := hcardBase
    calc
      (2 * D * G) ^ d ≤ C₀ ^ d := pow_le_pow_left₀ (by positivity) hC₀base _
      _ ≤ C₀ ^ (2 * d) := by
        apply pow_le_pow_right₀ (by linarith [hC₀pos])
        omega
  have hconst : 2 * D ^ 3 * G ^ 2 ≤ C ^ 2 := by
    calc
      2 * D ^ 3 * G ^ 2 ≤ 4 * D ^ 4 * G ^ 2 := by
        have hDpow : 2 * D ^ 3 ≤ 4 * D ^ 4 := by
          calc
            2 * D ^ 3 = D ^ 3 * 2 := by ring
            _ ≤ D ^ 3 * (4 * D) :=
              mul_le_mul_of_nonneg_left (by linarith [hDtwo] : 2 ≤ 4 * D)
                (pow_nonneg hDpos.le 3)
            _ = 4 * D ^ 4 := by ring
        exact mul_le_mul_of_nonneg_right hDpow (sq_nonneg G)
      _ = C ^ 2 := by dsimp [C]; ring
  have htargetNumerator :
      2 * D ^ 3 * G ^ 2 * (2 * D * G) ^ d ≤ C ^ 2 * C₀ ^ (2 * d) := by
    calc
      _ ≤ C ^ 2 * (2 * D * G) ^ d :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbasepow (by positivity)
  have hfinal :
      (2 * D ^ 3 * G ^ 2 * (2 * D * G) ^ d) / (Den * L ^ d) ≤
        (C * (C₀ / Real.sqrt L) ^ d) ^ 2 / Den := by
    rw [htargetEq]
    have hdiv : (C ^ 2 * C₀ ^ (2 * d) / L ^ d) / Den =
        (C ^ 2 * C₀ ^ (2 * d)) / (Den * L ^ d) := by
      calc
        _ = (C ^ 2 * C₀ ^ (2 * d)) / (L ^ d * Den) := by rw [div_div]
        _ = _ := by congr 1; ring
    rw [hdiv]
    have hDenL : 0 < Den * L ^ d := mul_pos hDenpos (pow_pos hLpos _)
    apply (div_le_div_iff₀ hDenL hDenL).2
    exact mul_le_mul_of_nonneg_right htargetNumerator hDenL.le
  exact hsumResult.trans hfinal

end Critical2DKPZ.Blocks

end
