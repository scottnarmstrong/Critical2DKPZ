/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.TruncatedRenewalLower

/-! # Bounded scaled renewal mass forces an at-most-critical coupling

Truncate increments at `L/Q`. At the comparison coupling `1/(R_{L/Q}+4A/Q)`, the
first-moment error is at most half the geometric sum. Choosing `Q > 8AB` contradicts
`σ U_σ(L/2) ≤ B` if the original coupling exceeds this comparison value.
-/

@[expose] public noncomputable section

open Critical2DKPZ.Renewal

namespace Critical2DKPZ.MomentBounds

private theorem cutoffMass_sub_div_le (q : ℕ → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (hu : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * q r ≤ A)
    (L Q : ℕ) (hQ : 0 < Q) : cutoffMass q L - cutoffMass q (L / Q) ≤ A * Q := by
  let n := L / Q
  let S := Finset.Icc 1 L \ Finset.Icc 1 n
  have hsub : Finset.Icc 1 n ⊆ Finset.Icc 1 L := Finset.Icc_subset_Icc_right (Nat.div_le_self L Q)
  have hsplit := Finset.sum_sdiff (f := q) hsub
  have heq : cutoffMass q L - cutoffMass q n = ∑ r ∈ S, q r := by
    change (∑ r ∈ Finset.Icc 1 L, q r) - (∑ r ∈ Finset.Icc 1 n, q r) = _
    linarith only [hsplit]
  have hcard : S.card ≤ L := by
    have h := Finset.card_le_card (Finset.sdiff_subset : S ⊆ Finset.Icc 1 L)
    simpa using h
  have hLQ : (L : ℝ) ≤ (Q : ℝ) * (n + 1) := by
    have he := Nat.div_add_mod L Q
    have hr := Nat.mod_lt L hQ
    have hnat : L ≤ Q * (n + 1) := by dsimp [n]; nlinarith only [he, hr]
    exact_mod_cast hnat
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  rw [heq]
  calc
    _ ≤ ∑ _r ∈ S, A / (n + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨hrL, hrnot⟩ := Finset.mem_sdiff.1 hr
      have hr1 := (Finset.mem_Icc.1 hrL).1
      have hnr : n + 1 ≤ r := by
        simp only [Finset.mem_Icc, not_and] at hrnot
        have h := hrnot hr1
        omega
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      exact ((le_div_iff₀ hr0).2 (by simpa only [mul_comm] using hu r hr1)).trans
        (div_le_div_of_nonneg_left hA hn0 (by exact_mod_cast hnr))
    _ ≤ (L : ℝ) * (A / (n + 1 : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (div_nonneg hA hn0.le)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hn0).2 hLQ) hA
      convert h using 1
      ring

/-- A uniform bound on the coupling times the renewal function gives a uniform additive
shift from criticality. The statement has no reciprocal-domain restriction. -/
theorem exists_shift_of_bounded_scaled_renewal (q : ℕ → ℝ) (hq : ∀ r, 0 ≤ q r)
    {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B)
    (hu : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * q r ≤ A) :
    ∃ θ : ℝ, 0 ≤ θ ∧ ∀ σ : ℝ, 0 ≤ σ → ∀ L : ℕ,
      σ * renewalFunction (fun r => σ * q r) (L / 2) ≤ B →
        σ * (cutoffMass q L - θ) ≤ 1 := by
  let Q := ⌈16 * A * (B + 1)⌉₊ + 1
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  let ε := 4 * A / Q
  have hε : 0 < ε := div_pos (mul_pos (by norm_num) hA) hQr
  have hQB : B < 1 / (2 * ε) := by
    have hceil : 8 * A * B < (Q : ℝ) := by
      have hBA : 8 * A * B ≤ 16 * A * (B + 1) := by
        calc
          _ ≤ 16 * A * B := mul_le_mul_of_nonneg_right (by linarith only [hA]) hB
          _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
      have h := Nat.le_ceil (16 * A * (B + 1))
      apply lt_of_le_of_lt (hBA.trans h)
      dsimp [Q]
      push_cast
      linarith
    calc
      B < (Q : ℝ) / (8 * A) := (lt_div_iff₀ (by positivity)).2 (by nlinarith only [hceil])
      _ = _ := by dsimp [ε]; field_simp; norm_num
  refine ⟨A * Q, mul_nonneg hA.le hQr.le, fun σ hσ L hbound => ?_⟩
  let n := L / Q
  let D := cutoffMass q n
  have hD : 0 ≤ D := Finset.sum_nonneg fun r _ => hq r
  let s := 1 / (D + ε)
  have hs : 0 < s := one_div_pos.2 (add_pos_of_nonneg_of_pos hD hε)
  let v : ℕ → ℝ := fun r => s * (if r ∈ Finset.Icc 1 n then q r else 0)
  have hv : ∀ r, 0 ≤ v r := by
    intro r
    dsimp [v]
    split_ifs
    · exact mul_nonneg hs.le (hq r)
    · simp only [mul_zero, le_refl]
  have hsubset : Finset.Icc 1 n ⊆ Finset.Icc 1 L := Finset.Icc_subset_Icc_right (Nat.div_le_self L Q)
  have hmass : cutoffMass v L = s * D := by
    dsimp [cutoffMass, v]
    simp only [mul_ite, mul_zero, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsubset]
    rw [← Finset.mul_sum]
    rfl
  have hfirst : cutoffFirstMoment v L ≤ s * A * n := by
    dsimp [cutoffFirstMoment, v]
    simp only [mul_ite, mul_zero, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsubset]
    calc
      _ ≤ ∑ _r ∈ Finset.Icc 1 n, s * A := by
        apply Finset.sum_le_sum
        intro r hr
        have h := mul_le_mul_of_nonneg_left (hu r (Finset.mem_Icc.1 hr).1) hs.le
        nlinarith only [h]
      _ = _ := by simp [mul_comm]
  have hgap : s * (D + ε) = 1 := by dsimp [s]; field_simp
  have hsub : cutoffMass v L < 1 := by
    rw [hmass]
    nlinarith only [hgap, mul_pos hs hε]
  have hbudget : 2 * A * n ≤ (L / 2 + 1 : ℕ) * ε := by
    have hnQ : (n * Q : ℕ) ≤ L := Nat.div_mul_le_self L Q
    have hhalf : L ≤ 2 * (L / 2 + 1) := by omega
    have hr : (n : ℝ) * Q ≤ 2 * ((L / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hnQ.trans hhalf
    dsimp [ε]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hQr).2
    have h := mul_le_mul_of_nonneg_left hr hA.le
    nlinarith only [h]
  have hsmall : 2 * cutoffFirstMoment v L ≤ (↑(L / 2) + 1 : ℝ) * (1 - cutoffMass v L) := by
    rw [hmass]
    have h := mul_le_mul_of_nonneg_left hbudget hs.le
    have heq : (↑(L / 2) + 1 : ℝ) * (1 - s * D) = (↑(L / 2) + 1 : ℝ) * (s * ε) := by
      congr 1
      nlinarith only [hgap]
    rw [heq]
    push_cast at h
    nlinarith only [h, hfirst]
  have hlower := half_geometric_le_renewalFunction hv (Nat.div_le_self L 2) hsub hsmall
  rw [hmass] at hlower
  have hσs : σ < s := by
    by_contra hnot
    have hle : s ≤ σ := le_of_not_gt hnot
    have hvq : ∀ r, v r ≤ σ * q r := by
      intro r
      dsimp [v]
      split_ifs
      · exact mul_le_mul_of_nonneg_right hle (hq r)
      · simpa only [mul_zero] using mul_nonneg hσ (hq r)
    have hmono := renewalFunction_mono hv hvq (L / 2)
    have hp : s * renewalFunction v (L / 2) ≤ σ * renewalFunction (fun r => σ * q r) (L / 2) :=
      mul_le_mul hle hmono (zero_le_one.trans (one_le_renewalFunction hv _)) hσ
    have heq : s * (1 / (2 * (1 - s * D))) = 1 / (2 * ε) := by
      rw [show 1 - s * D = s * ε by nlinarith only [hgap]]
      field_simp
    have hlow := mul_le_mul_of_nonneg_left hlower hs.le
    rw [heq] at hlow
    exact not_le_of_gt hQB (hlow.trans (hp.trans hbound))
  have hσD : σ * (D + ε) ≤ 1 := by
    exact (le_div_iff₀ (add_pos_of_nonneg_of_pos hD hε)).1 hσs.le
  have hcut := cutoffMass_sub_div_le q hA.le hu L Q hQ
  have hcompare : cutoffMass q L - A * Q ≤ D + ε := by linarith only [hcut, hε]
  exact (mul_le_mul_of_nonneg_left hcompare hσ).trans hσD

end Critical2DKPZ.MomentBounds
