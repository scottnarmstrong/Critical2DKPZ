/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.WalkTails.LogConcavity
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Maximum atoms of finite symmetric log-concave profiles

The proof compares the tail of a symmetric log-concave profile with a
geometric sequence whose decay scale is set by its central mass.
-/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.WalkTails

private def profileRatio (p : ℕ → ℝ) (n : ℕ) : ℝ := p (n + 1) / p n

/-- A sequence with nonincreasing adjacent values is antitone. -/
theorem symmetricProfile_antitone_of_adjacent {p : ℕ → ℝ}
    (hmono : ∀ k, p (k + 1) ≤ p k) {i j : ℕ} (hij : i ≤ j) :
    p j ≤ p i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ k hk ih => exact (hmono k).trans ih

private theorem profileRatio_step {N : ℕ} (p : ℕ → ℝ)
    (hpos : ∀ k ≤ N, 0 < p k)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    {k : ℕ} (hk : k + 2 ≤ N) :
    profileRatio p (k + 1) ≤ profileRatio p k := by
  unfold profileRatio
  have hkpos : 0 < k + 1 := by omega
  have h := hlc (k + 1) hkpos (by omega)
  have hkminus : k + 1 - 1 = k := by omega
  rw [hkminus] at h
  rw [div_le_div_iff₀ (hpos (k + 1) (by omega)) (hpos k (by omega))]
  nlinarith [h]

private theorem profileRatio_antitone {N : ℕ} (p : ℕ → ℝ)
    (hpos : ∀ k ≤ N, 0 < p k)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    {i j : ℕ} (hij : i ≤ j) (hj : j < N) :
    profileRatio p j ≤ profileRatio p i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
      exact (profileRatio_step p hpos hlc (by omega)).trans (ih (by omega))

/-- A nonincreasing log-concave profile with central value `M` satisfies
`p k ≤ M/2 * (1 - 1/(2R))^k` for `k ≥ R`, under the stated support, normalization and radius
assumptions. -/
theorem symmetricProfile_tail_geometric
    {N R : ℕ} (p : ℕ → ℝ) (M : ℝ)
    (hM : 0 < M) (hp0 : p 0 = M)
    (hpos : ∀ k ≤ N, 0 < p k)
    (hzero : ∀ k, N < k → p k = 0)
    (hmono : ∀ k, p (k + 1) ≤ p k)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    (hnorm : M + 2 * (∑ k ∈ Finset.range N, p (k + 1)) = 1)
    (hRscale : 2 ≤ M * (R : ℝ)) (hRN : R < N) :
    ∀ k, R ≤ k → p k ≤ M / 2 * (1 - 1 / (2 * R)) ^ k := by
  classical
  let q : ℝ := 1 - 1 / (2 * (R : ℝ))
  have hRpos : 0 < R := by
    by_contra hn
    have : R = 0 := by omega
    subst R
    norm_num at hRscale
  have hqpos : 0 < q := by
    dsimp [q]
    have hRcast : (1 : ℝ) ≤ R := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have hden : (0 : ℝ) < 2 * (R : ℝ) := by positivity
    have hfrac : 1 / (2 * (R : ℝ)) ≤ (1 : ℝ) / 2 := by
      apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [hRcast]
    linarith
  have hqle : q ≤ 1 := by
    dsimp [q]
    have hfrac : 0 ≤ (1 : ℝ) / (2 * (R : ℝ)) := by positivity
    linarith
  have hqpow : (1 : ℝ) / 2 ≤ q ^ R := by
    have hbern := one_add_mul_sub_le_pow (a := q) (by linarith [hqpos]) R
    have hqsub : q - 1 = -(1 / (2 * (R : ℝ))) := by dsimp [q]; ring
    have hmul : (R : ℝ) * (1 / (2 * (R : ℝ))) = 1 / 2 := by
      field_simp
    have hnegmul : (R : ℝ) * -(1 / (2 * (R : ℝ))) = -(1 / 2) := by
      calc
        _ = -((R : ℝ) * (1 / (2 * (R : ℝ))) ) := by ring
        _ = -(1 / 2) := by rw [hmul]
    rw [hqsub, hnegmul] at hbern
    linarith
  have hpRle : p R ≤ M / 4 := by
    have hlowTerm : (∑ k ∈ Finset.range R, p R) ≤
        ∑ k ∈ Finset.range R, p (k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkR : k + 1 ≤ R := by simpa using Finset.mem_range.mp hk
      exact symmetricProfile_antitone_of_adjacent hmono hkR
    have hRsubset : Finset.range R ⊆ Finset.range N := Finset.range_mono (by omega)
    have hsumNonneg : ∀ k ∈ Finset.range N, 0 ≤ p (k + 1) := by
      intro k hk
      exact le_of_lt (hpos (k + 1) (by simpa using Finset.mem_range.mp hk))
    have hsmallSum :
        (∑ k ∈ Finset.range R, p (k + 1)) ≤
          ∑ k ∈ Finset.range N, p (k + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg hRsubset (fun k hk _ => hsumNonneg k hk)
    have hMterm : p R ≤ M := by
      rw [← hp0]
      exact symmetricProfile_antitone_of_adjacent hmono (Nat.zero_le R)
    have hRbound : (2 * (R : ℝ) + 1) * p R ≤ 1 := by
      have hcardMul : (R : ℝ) * p R =
          ∑ k ∈ Finset.range R, p R := by simp [Finset.sum_const, nsmul_eq_mul]
      have hsumLowR : (R : ℝ) * p R ≤
          ∑ k ∈ Finset.range N, p (k + 1) := by
        rw [hcardMul]
        exact hlowTerm.trans hsmallSum
      have hMtermR : p R ≤ M := hMterm
      calc
        (2 * (R : ℝ) + 1) * p R = p R + 2 * ((R : ℝ) * p R) := by ring
        _ ≤ M + 2 * (∑ k ∈ Finset.range N, p (k + 1)) := by nlinarith
        _ = 1 := hnorm
    have hRlarge : 4 ≤ M * (2 * (R : ℝ) + 1) := by
      nlinarith [hRscale, hM.le]
    nlinarith [hRbound, hRlarge]
  have hratioBound : profileRatio p R ≤ q := by
    by_contra hnot
    have hgt : q < profileRatio p R := lt_of_not_ge hnot
    have hratios : ∀ i < R, q < profileRatio p i := by
      intro i hi
      have hanti := profileRatio_antitone p hpos hlc (i := i) (j := R) (by omega) hRN
      exact hgt.trans_le hanti
    have hpowLower : ∀ k ≤ R, M * q ^ k ≤ p k := by
      intro k hk
      induction k with
      | zero => simp [hp0]
      | succ k ih =>
          have hkr : k < R := by omega
          have hkpos : 0 < p k := hpos k (by omega)
          have hratio : q < p (k + 1) / p k := by
            change q < profileRatio p k
            exact hratios k hkr
          have hstep : q * p k < p (k + 1) := by
            exact (lt_div_iff₀ hkpos).mp hratio
          have hkR : k ≤ R := by omega
          have hmult : M * q ^ k * q ≤ p k * q :=
            mul_le_mul_of_nonneg_right (ih hkR) hqpos.le
          calc
            M * q ^ (k + 1) = M * q ^ k * q := by rw [pow_succ]; ring
            _ ≤ p k * q := hmult
            _ ≤ p (k + 1) := le_of_lt (by nlinarith)
    have hpRlower : M * q ^ R ≤ p R := hpowLower R le_rfl
    have hpRhalf : M / 2 ≤ p R := by
      have := mul_le_mul_of_nonneg_left hqpow hM.le
      nlinarith
    linarith
  have hratioTail : ∀ k, R ≤ k → k < N → profileRatio p k ≤ q := by
    intro k hRk hkN
    exact (profileRatio_antitone p hpos hlc hRk hkN).trans hratioBound
  have htailWithin : ∀ k, R ≤ k → k ≤ N →
      p k ≤ p R * q ^ (k - R) := by
    intro k hRk hkN
    induction k, hRk using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
        have hkN' : k < N := by omega
        have hkpos : 0 < p k := hpos k (by omega)
        have hrat : p (k + 1) / p k ≤ q := by
          change profileRatio p k ≤ q
          exact hratioTail k hk hkN'
        have hstep : p (k + 1) ≤ q * p k := by
          exact (div_le_iff₀ hkpos).mp hrat
        have hpow : q ^ (k + 1 - R) = q ^ (k - R) * q := by
          calc
            q ^ (k + 1 - R) = q ^ ((k - R) + 1) := by congr 1; omega
            _ = q ^ (k - R) * q := by rw [pow_succ]
        rw [hpow]
        calc
          p (k + 1) ≤ q * p k := hstep
          _ ≤ q * (p R * q ^ (k - R)) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hqpos.le
          _ = p R * (q ^ (k - R) * q) := by ring
  intro k hRk
  by_cases hkN : k ≤ N
  · have hwithin := htailWithin k hRk hkN
    have hscaled : p R * q ^ (k - R) ≤ M / 4 * q ^ (k - R) :=
      mul_le_mul_of_nonneg_right hpRle (pow_nonneg hqpos.le _)
    have hpowEq : q ^ k = q ^ (k - R) * q ^ R := by
      calc
        q ^ k = q ^ ((k - R) + R) := by rw [Nat.sub_add_cancel hRk]
        _ = q ^ (k - R) * q ^ R := by rw [pow_add]
    have hqcompare : M / 4 * q ^ (k - R) ≤ M / 2 * q ^ k := by
      rw [hpowEq]
      have hmul := mul_le_mul_of_nonneg_left hqpow hM.le
      have hmul' := mul_le_mul_of_nonneg_left hmul (pow_nonneg hqpos.le (k - R))
      nlinarith
    exact hwithin.trans (hscaled.trans hqcompare)
  · rw [hzero k (by omega)]
    positivity

/-- The second moment of a finite symmetric log-concave profile is at most `18 M R³` under the
stated radius assumptions. -/
theorem symmetricProfile_variance_le
    {N R : ℕ} (p : ℕ → ℝ) (M : ℝ)
    (hM : 0 < M) (hp0 : p 0 = M)
    (hpos : ∀ k ≤ N, 0 < p k)
    (hzero : ∀ k, N < k → p k = 0)
    (hmono : ∀ k, p (k + 1) ≤ p k)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    (hnorm : M + 2 * (∑ k ∈ Finset.range N, p (k + 1)) = 1)
    (hRscale : 2 ≤ M * (R : ℝ)) (hRN : R < N) :
    2 * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) ≤
      18 * M * (R : ℝ) ^ 3 := by
  classical
  let q : ℝ := 1 - 1 / (2 * (R : ℝ))
  have htail := symmetricProfile_tail_geometric p M hM hp0 hpos hzero hmono hlc
    hnorm hRscale hRN
  have hRpos : 0 < R := by
    by_contra hR
    have hRzero : R = 0 := by omega
    subst R
    simp at hRscale
    linarith
  have hqpos : 0 < q := by
    dsimp [q]
    have hRcast : (1 : ℝ) ≤ R := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
    have hden : (0 : ℝ) < 2 * (R : ℝ) := by positivity
    have hfrac : 1 / (2 * (R : ℝ)) ≤ (1 : ℝ) / 2 := by
      apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2
      nlinarith [hRcast]
    linarith
  have hqle : q ≤ 1 := by
    dsimp [q]
    have hfrac : 0 ≤ (1 : ℝ) / (2 * (R : ℝ)) := by positivity
    linarith
  have hqLt : q < 1 := by
    dsimp [q]
    exact sub_lt_self _ (by positivity)
  have hqnorm : ‖q‖ < 1 := by
    rw [Real.norm_of_nonneg hqpos.le]
    exact hqLt
  have hgeom := tsum_sq_mul_geometric_of_norm_lt_one hqnorm
  have hgeomLe : (∑' k : ℕ, (k : ℝ) ^ 2 * q ^ k) ≤ 16 * (R : ℝ) ^ 3 := by
    have hden : 1 - q = 1 / (2 * (R : ℝ)) := by dsimp [q]; ring
    have hnum : q * (1 + q) ≤ 2 := by nlinarith [hqpos, hqle]
    rw [hgeom, hden]
    apply (div_le_iff₀ (by positivity : 0 < (1 / (2 * (R : ℝ))) ^ 3)).2
    have hcancel : 16 * (R : ℝ) ^ 3 * (1 / (2 * (R : ℝ))) ^ 3 = 2 := by
      have hRne : (R : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < R))
      field_simp [hRne]
      ring
    rw [hcancel]
    exact hnum
  have hsplit :
      (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) =
        (∑ k ∈ Finset.range R, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) +
          ∑ k ∈ Finset.range (N - R), ((R + k + 1 : ℕ) : ℝ) ^ 2 * p (R + k + 1) := by
    have hN : R + (N - R) = N := Nat.add_sub_of_le (by omega)
    rw [← hN, Finset.sum_range_add]
    have hsub : R + (N - R) - R = N - R := by omega
    rw [hsub]
  have hsmall :
      (∑ k ∈ Finset.range R, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) ≤
        M * (R : ℝ) ^ 3 := by
    calc
      _ ≤ ∑ k ∈ Finset.range R, (M * (R : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkR : k + 1 ≤ R := by simpa using Finset.mem_range.mp hk
        have hpbound : p (k + 1) ≤ M := by
          rw [← hp0]
          exact symmetricProfile_antitone_of_adjacent hmono (Nat.zero_le (k + 1))
        have hcast : ((k + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast hkR
        have hsq : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (R : ℝ) ^ 2 := by nlinarith
        have hpnonneg : 0 ≤ p (k + 1) := le_of_lt (hpos (k + 1) (by omega))
        calc
          _ ≤ (R : ℝ) ^ 2 * p (k + 1) := mul_le_mul_of_nonneg_right hsq hpnonneg
          _ ≤ (R : ℝ) ^ 2 * M := mul_le_mul_of_nonneg_left hpbound (sq_nonneg _)
          _ = M * (R : ℝ) ^ 2 := by ring
      _ = M * (R : ℝ) ^ 3 := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  let U : Finset ℕ := (Finset.range (N - R)).image (fun k => R + k + 1)
  have hmap :
      (∑ k ∈ Finset.range (N - R),
        ((R + k + 1 : ℕ) : ℝ) ^ 2 * q ^ (R + k + 1)) =
        ∑ n ∈ U, (n : ℝ) ^ 2 * q ^ n := by
    unfold U
    symm
    rw [Finset.sum_image]
    · intro a ha b hb hab
      have hab' : R + a = R + b := Nat.add_right_cancel hab
      exact Nat.add_left_cancel hab'
  have hsummable : Summable (fun n : ℕ => (n : ℝ) ^ 2 * q ^ n) := by
    exact summable_pow_mul_geometric_of_norm_lt_one 2 hqnorm
  have hUle : (∑ n ∈ U, (n : ℝ) ^ 2 * q ^ n) ≤
      ∑' n : ℕ, (n : ℝ) ^ 2 * q ^ n :=
    hsummable.sum_le_tsum U (fun n hn => by positivity)
  have htailSum :
      (∑ k ∈ Finset.range (N - R), ((R + k + 1 : ℕ) : ℝ) ^ 2 * p (R + k + 1)) ≤
        8 * M * (R : ℝ) ^ 3 := by
    calc
      _ ≤ ∑ k ∈ Finset.range (N - R),
          (M / 2) * ((R + k + 1 : ℕ) : ℝ) ^ 2 * q ^ (R + k + 1) := by
        apply Finset.sum_le_sum
        intro k hk
        have hklt : k < N - R := Finset.mem_range.mp hk
        have hNidx : R + k + 1 ≤ N := by omega
        have henv := htail (R + k + 1) (by omega)
        have hsqnon : 0 ≤ ((R + k + 1 : ℕ) : ℝ) ^ 2 := sq_nonneg _
        calc
          _ ≤ ((R + k + 1 : ℕ) : ℝ) ^ 2 *
              (M / 2 * q ^ (R + k + 1)) := mul_le_mul_of_nonneg_left henv hsqnon
          _ = (M / 2) * ((R + k + 1 : ℕ) : ℝ) ^ 2 * q ^ (R + k + 1) := by ring
      _ = (M / 2) * (∑ k ∈ Finset.range (N - R),
          ((R + k + 1 : ℕ) : ℝ) ^ 2 * q ^ (R + k + 1)) := by
        calc
          _ = ∑ k ∈ Finset.range (N - R),
              (M / 2) * (((R + k + 1 : ℕ) : ℝ) ^ 2 * q ^ (R + k + 1)) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
          _ = _ := by rw [Finset.mul_sum]
      _ = (M / 2) * (∑ n ∈ U, (n : ℝ) ^ 2 * q ^ n) := by rw [hmap]
      _ ≤ (M / 2) * (∑' n : ℕ, (n : ℝ) ^ 2 * q ^ n) :=
        mul_le_mul_of_nonneg_left hUle (by positivity)
      _ ≤ (M / 2) * (16 * (R : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hgeomLe (by positivity)
      _ = 8 * M * (R : ℝ) ^ 3 := by ring
  have hsum :
      (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) ≤
        9 * M * (R : ℝ) ^ 3 := by
    rw [hsplit]
    linarith [hsmall, htailSum]
  nlinarith [hsum]

/-- A finite symmetric log-concave probability law with interval support and maximal atom `M`
satisfies `M² (1 + Var) ≤ 487`. -/
theorem symmetricProfile_maxAtom_le
    {N : ℕ} (p : ℕ → ℝ) (M : ℝ)
    (hM : 0 < M) (hp0 : p 0 = M)
    (hpos : ∀ k ≤ N, 0 < p k)
    (hzero : ∀ k, N < k → p k = 0)
    (hmono : ∀ k, p (k + 1) ≤ p k)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    (hnorm : M + 2 * (∑ k ∈ Finset.range N, p (k + 1)) = 1) :
    M ^ 2 * (1 + 2 * (∑ k ∈ Finset.range N,
      ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1))) ≤ 487 := by
  classical
  have hsumNonneg : 0 ≤ ∑ k ∈ Finset.range N, p (k + 1) :=
    Finset.sum_nonneg fun k hk => le_of_lt (hpos (k + 1) (by simpa using Finset.mem_range.mp hk))
  have hMle : M ≤ 1 := by nlinarith [hnorm]
  let R : ℕ := Nat.ceil (2 / M)
  have hceilLower : 2 / M ≤ (R : ℝ) := by
    dsimp [R]
    exact Nat.le_ceil _
  have hRscale : 2 ≤ M * (R : ℝ) := by
    calc
      2 = M * (2 / M) := by field_simp [ne_of_gt hM]
      _ ≤ M * (R : ℝ) := mul_le_mul_of_nonneg_left hceilLower hM.le
  have hceilUpper : (R : ℝ) ≤ 2 / M + 1 := by
    have hceilNat : Nat.ceil (2 / M) ≤ Nat.floor (2 / M) + 1 :=
      Nat.ceil_le_floor_add_one _
    have hxpos : 0 < 2 / M := by positivity
    have hfloor : (Nat.floor (2 / M) : ℝ) ≤ 2 / M := Nat.floor_le hxpos.le
    have hcast : (Nat.ceil (2 / M) : ℝ) ≤ (Nat.floor (2 / M) : ℝ) + 1 := by
      exact_mod_cast hceilNat
    dsimp [R]
    exact hcast.trans (by linarith [hfloor])
  have hMInv : 1 ≤ 1 / M := (le_div_iff₀ hM).2 (by linarith)
  have hRupper : (R : ℝ) ≤ 3 / M := by
    have h := hceilUpper
    have hrecip : 3 / M = 2 / M + 1 / M := by ring
    have htwo : 2 / M + 1 ≤ 3 / M := by rw [hrecip]; linarith [hMInv]
    exact h.trans htwo
  by_cases hRN : R < N
  · have hvar := symmetricProfile_variance_le p M hM hp0 hpos hzero hmono hlc
      hnorm hRscale hRN
    have hMR : M * (R : ℝ) ≤ 3 := by
      calc
        M * (R : ℝ) ≤ M * (3 / M) := mul_le_mul_of_nonneg_left hRupper hM.le
        _ = 3 := by field_simp [ne_of_gt hM]
    have hMRnonneg : 0 ≤ M * (R : ℝ) := by positivity
    have hMRsq : (M * (R : ℝ)) ^ 2 ≤ 9 := by nlinarith
    have hMRcube : (M * (R : ℝ)) ^ 3 ≤ 27 := by
      have hmul := mul_le_mul_of_nonneg_right hMRsq hMRnonneg
      nlinarith
    have hvarScaled : M ^ 2 *
        (2 * (∑ k ∈ Finset.range N,
          ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1))) ≤ 486 := by
      calc
        _ ≤ M ^ 2 * (18 * M * (R : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hvar (sq_nonneg M)
        _ = 18 * (M * (R : ℝ)) ^ 3 := by ring
        _ ≤ 486 := by nlinarith
    have hMsq : M ^ 2 ≤ 1 := by nlinarith [mul_self_le_mul_self hM.le hMle]
    nlinarith
  · have hNR : N ≤ R := by omega
    have hvarSmall :
        2 * (∑ k ∈ Finset.range N,
          ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) ≤ (N : ℝ) ^ 2 := by
      have hterm : ∀ k ∈ Finset.range N,
          ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1) ≤ (N : ℝ) ^ 2 * p (k + 1) := by
        intro k hk
        have hkn : k + 1 ≤ N := by simpa using Finset.mem_range.mp hk
        have hcast : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hkn
        have hsq : ((k + 1 : ℕ) : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right hsq (le_of_lt (hpos (k + 1) (by omega)))
      have hsum := Finset.sum_le_sum hterm
      have hmass : 2 * (∑ k ∈ Finset.range N, p (k + 1)) = 1 - M := by nlinarith [hnorm]
      have hfactor :
          (∑ k ∈ Finset.range N, (N : ℝ) ^ 2 * p (k + 1)) =
            (N : ℝ) ^ 2 * (∑ k ∈ Finset.range N, p (k + 1)) := by
        rw [Finset.mul_sum]
      calc
        _ ≤ 2 * (∑ k ∈ Finset.range N, (N : ℝ) ^ 2 * p (k + 1)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
        _ = (N : ℝ) ^ 2 * (2 * ∑ k ∈ Finset.range N, p (k + 1)) := by
          rw [hfactor]
          ring
        _ = (N : ℝ) ^ 2 * (1 - M) := by rw [hmass]
        _ ≤ (N : ℝ) ^ 2 := by nlinarith [sq_nonneg (N : ℝ), hMle]
    have hMRglobal : M * (R : ℝ) ≤ 3 := by
      calc
        M * (R : ℝ) ≤ M * (3 / M) := mul_le_mul_of_nonneg_left hRupper hM.le
        _ = 3 := by field_simp [ne_of_gt hM]
    have hMN : M * (N : ℝ) ≤ 3 := by
      calc
        M * (N : ℝ) ≤ M * (R : ℝ) :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hNR) hM.le
        _ ≤ 3 := hMRglobal
    have hMNnonneg : 0 ≤ M * (N : ℝ) := by positivity
    have hMsq : M ^ 2 ≤ 1 := by nlinarith [mul_self_le_mul_self hM.le hMle]
    have hvarScaled : M ^ 2 *
        (2 * (∑ k ∈ Finset.range N,
          ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1))) ≤ 9 := by
      have hMNsq : (M * (N : ℝ)) ^ 2 ≤ 9 := by nlinarith
      calc
        _ ≤ M ^ 2 * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hvarSmall (sq_nonneg M)
        _ = (M * (N : ℝ)) ^ 2 := by ring
        _ ≤ 9 := hMNsq
    nlinarith

/-- A positive interval-supported log-concave profile with `p 1 ≤ p 0` is nonincreasing on the
nonnegative integers. -/
theorem symmetricProfile_antitone_of_logConcave
    {N : ℕ} (p : ℕ → ℝ)
    (hpos : ∀ k ≤ N, 0 < p k)
    (hzero : ∀ k, N < k → p k = 0)
    (hcenter : p 1 ≤ p 0)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1)) :
    ∀ k, p (k + 1) ≤ p k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hnN : n < N
      · by_cases hn0 : n = 0
        · subst n
          exact hcenter
        · have hnpos : 0 < n := by omega
          have hprev : p n ≤ p (n - 1) := by
            have hih := ih (n - 1) (by omega)
            have heq : n - 1 + 1 = n := by omega
            rw [heq] at hih
            exact hih
          have hprevpos : 0 < p (n - 1) := hpos (n - 1) (by omega)
          have hnvalpos : 0 < p n := hpos n (by omega)
          have hlog := hlc n hnpos (by omega)
          have hmul₁ : p (n - 1) * p (n + 1) ≤ p n * p n := by
            simpa [pow_two, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0)] using hlog
          have hmul₂ : p n * p n ≤ p (n - 1) * p n :=
            mul_le_mul_of_nonneg_right hprev hnvalpos.le
          have hprod : p (n - 1) * p (n + 1) ≤ p (n - 1) * p n := hmul₁.trans hmul₂
          have hcancel := (mul_le_mul_iff_of_pos_left hprevpos).mp hprod
          simpa using hcancel
      · have hnextzero : p (n + 1) = 0 := hzero (n + 1) (by omega)
        rw [hnextzero]
        by_cases hnle : n ≤ N
        · exact le_of_lt (hpos n hnle)
        · rw [hzero n (by omega)]

/-- The central-mass bound `M² (1 + Var) ≤ 487` holds under adjacent log-concavity and the
central-mode condition. -/
theorem symmetricProfile_maxAtom_le_of_logConcave
    {N : ℕ} (p : ℕ → ℝ) (M : ℝ)
    (hM : 0 < M) (hp0 : p 0 = M)
    (hpos : ∀ k ≤ N, 0 < p k)
    (hzero : ∀ k, N < k → p k = 0)
    (hcenter : p 1 ≤ p 0)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    (hnorm : M + 2 * (∑ k ∈ Finset.range N, p (k + 1)) = 1) :
    M ^ 2 * (1 + 2 * (∑ k ∈ Finset.range N,
      ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1))) ≤ 487 :=
  symmetricProfile_maxAtom_le p M hM hp0 hpos hzero
    (symmetricProfile_antitone_of_logConcave p hpos hzero hcenter hlc) hlc hnorm

/-- The integer-centred profile obtained by adding an independent fair
Bernoulli step to a half-integer-centred profile. -/
private def halfProfileSmooth (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => p 0
  | k + 1 => (p (k + 1) + p k) / 2

/-- A finite symmetric log-concave probability law with interval support and a half-integer
centre satisfies `M² (1 + Var) ≤ 487`, where `M` is its maximal atom. -/
theorem symmetricHalfProfile_maxAtom_le
    {N : ℕ} (p : ℕ → ℝ) (M : ℝ)
    (hM : 0 < M) (hp0 : p 0 = M)
    (hpos : ∀ k ≤ N, 0 < p k)
    (hzero : ∀ k, N < k → p k = 0)
    (hmono : ∀ k, p (k + 1) ≤ p k)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    (hnorm : 2 * (∑ k ∈ Finset.range (N + 1), p k) = 1) :
    M ^ 2 * (1 + 2 * (∑ k ∈ Finset.range (N + 1),
      (((k : ℝ) + 1 / 2) ^ 2) * p k)) ≤ 487 := by
  classical
  let q := halfProfileSmooth p
  have hq0 : q 0 = M := by simp [q, halfProfileSmooth, hp0]
  have hqpos : ∀ k ≤ N + 1, 0 < q k := by
    intro k hk
    cases k with
    | zero => simpa [hq0] using hM
    | succ j =>
        by_cases hj : j < N
        · have h1 : 0 < p (j + 1) := hpos (j + 1) (by omega)
          have h2 : 0 < p j := hpos j (by omega)
          simp only [q, halfProfileSmooth]
          positivity
        · have hjN : j = N := by omega
          subst j
          have hlast : p (N + 1) = 0 := hzero (N + 1) (by omega)
          have hNpos := hpos N le_rfl
          simp [q, halfProfileSmooth, hlast]
          positivity
  have hqzero : ∀ k, N + 1 < k → q k = 0 := by
    intro k hk
    have hk0 : k ≠ 0 := by omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hj : N < j := by omega
    have hj1 : N < j + 1 := by omega
    simp [q, halfProfileSmooth, hzero j hj, hzero (j + 1) hj1]
  have hqcenter : q 1 ≤ q 0 := by
    have hstep := hmono 0
    simp only [q, halfProfileSmooth]
    rw [hp0]
    dsimp [halfProfileSmooth] at hstep
    nlinarith
  have hqLC : ∀ k, 0 < k → k + 1 ≤ N + 1 →
      q k ^ 2 ≥ q (k - 1) * q (k + 1) := by
    intro k hk hkN
    have hkN' : k ≤ N := by omega
    by_cases hk1 : k = 1
    · subst k
      have hp2le : p 2 ≤ p 0 := (hmono 1).trans (hmono 0)
      have hp02 : p 1 ^ 2 ≥ p 0 * p 2 := by
        by_cases hN2 : 2 ≤ N
        · simpa using hlc 1 (by norm_num) hN2
        · have hp2zero : p 2 = 0 := hzero 2 (by omega)
          rw [hp2zero]
          nlinarith [sq_nonneg (p 1)]
      have hq1 : q 1 = (p 1 + p 0) / 2 := by simp [q, halfProfileSmooth]
      have hq2 : q 2 = (p 2 + p 1) / 2 := by simp [q, halfProfileSmooth]
      rw [hq0, hq1, hq2]
      have hp0p2 : p 0 * p 2 ≤ p 0 ^ 2 := by
        have hp0nonneg : 0 ≤ p 0 := by rw [hp0]; exact hM.le
        have hmul := mul_le_mul_of_nonneg_left hp2le hp0nonneg
        simpa only [pow_two] using hmul
      nlinarith [sq_nonneg (p 0)]
    · have hk2 : 2 ≤ k := by omega
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hjpos : 0 < j := by omega
      have hjle : j + 1 ≤ N := by omega
      have hqj : q (j + 1) = (p (j + 1) + p j) / 2 := by
        simp [q, halfProfileSmooth]
      have hqprev : q j = (p j + p (j - 1)) / 2 := by
        cases j with
        | zero => omega
        | succ l => simp [q, halfProfileSmooth]
      have hqnext : q (j + 2) = (p (j + 2) + p (j + 1)) / 2 := by
        simp [q, halfProfileSmooth]
      have hfirst : p (j + 1) ^ 2 ≥ p j * p (j + 2) := by
        by_cases hjlt : j + 2 ≤ N
        · exact hlc (j + 1) (by omega) hjlt
        · have hpnext : p (j + 2) = 0 := hzero (j + 2) (by omega)
          rw [hpnext]
          nlinarith [sq_nonneg (p (j + 1))]
      have hsecond : p j ^ 2 ≥ p (j - 1) * p (j + 1) :=
        hlc j hjpos hjle
      have hcross : p (j - 1) * p (j + 2) ≤ p j * p (j + 1) := by
        by_cases hjlt : j + 2 ≤ N
        · have hratio := profileRatio_antitone p hpos hlc
            (i := j - 1) (j := j + 1) (by omega) (by omega)
          have hdiv : p (j + 2) / p (j + 1) ≤ p j / p (j - 1) := by
            have hdiv' : p (j + 2) / p (j + 1) ≤
                p ((j - 1) + 1) / p (j - 1) := by
              simpa [profileRatio] using hratio
            simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by omega : j ≠ 0))]
              using hdiv'
          have hmul := (div_le_div_iff₀
            (hpos (j + 1) (by omega)) (hpos (j - 1) (by omega))).mp hdiv
          simpa [mul_comm] using hmul
        · have hpnext : p (j + 2) = 0 := hzero (j + 2) (by omega)
          rw [hpnext]
          simpa using mul_nonneg (le_of_lt (hpos j (by omega)))
            (le_of_lt (hpos (j + 1) (by omega)))
      change q (j + 1) ^ 2 ≥ q j * q (j + 2)
      rw [hqj, hqprev, hqnext]
      have hidentity :
          (p (j + 1) + p j) ^ 2 -
              (p j + p (j - 1)) * (p (j + 2) + p (j + 1)) =
            (p (j + 1) ^ 2 - p j * p (j + 2)) +
              (p j ^ 2 - p (j - 1) * p (j + 1)) +
              (p j * p (j + 1) - p (j - 1) * p (j + 2)) := by ring
      nlinarith [hfirst, hsecond, hcross]
  have hqnorm : q 0 + 2 * (∑ k ∈ Finset.range (N + 1), q (k + 1)) = 1 := by
    have hsum0 :
        (∑ k ∈ Finset.range (N + 1), p k) =
          p 0 + ∑ k ∈ Finset.range N, p (k + 1) := by
      simpa [add_comm] using (Finset.sum_range_succ' p N)
    have hsum1 :
        (∑ k ∈ Finset.range (N + 1), p (k + 1)) =
          (∑ k ∈ Finset.range N, p (k + 1)) + p (N + 1) := by
      simpa using (Finset.sum_range_succ (fun k => p (k + 1)) N)
    have hlast : p (N + 1) = 0 := hzero (N + 1) (by omega)
    have hsumq :
        (∑ k ∈ Finset.range (N + 1), q (k + 1)) =
          ((∑ k ∈ Finset.range (N + 1), p k) +
            (∑ k ∈ Finset.range (N + 1), p (k + 1))) / 2 := by
      calc
        _ = ∑ k ∈ Finset.range (N + 1), (p (k + 1) + p k) / 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          simp [q, halfProfileSmooth, add_comm]
        _ = (∑ k ∈ Finset.range (N + 1), (p (k + 1) + p k)) / 2 := by
          simp only [div_eq_mul_inv]
          rw [← Finset.sum_mul]
        _ = _ := by rw [Finset.sum_add_distrib]; ring
    rw [hsumq, hsum0, hsum1, hlast, hq0]
    rw [hsum0] at hnorm
    rw [hp0] at hnorm
    nlinarith [hnorm]
  have hqMoment :
      2 * (∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) ^ 2 * q (k + 1)) =
        2 * (∑ k ∈ Finset.range (N + 1), (((k : ℝ) + 1 / 2) ^ 2) * p k) + 1 / 4 := by
    have hshift :
        (∑ k ∈ Finset.range (N + 1), ((k : ℝ) ^ 2) * p k) =
          ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1) := by
      rw [Finset.sum_range_succ']
      norm_num
    have hlast : p (N + 1) = 0 := hzero (N + 1) (by omega)
    have hqExpand :
        2 * (∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) ^ 2 * q (k + 1)) =
          (∑ k ∈ Finset.range (N + 1),
            (((k + 1 : ℕ) : ℝ) ^ 2) * p k) +
          (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) := by
      have hpoint : ∀ k,
          2 * (((k + 1 : ℕ) : ℝ) ^ 2 * q (k + 1)) =
            ((k + 1 : ℕ) : ℝ) ^ 2 * p k +
              ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1) := by
        intro k
        simp [q, halfProfileSmooth]
        ring
      calc
        _ = ∑ k ∈ Finset.range (N + 1),
            (2 * (((k + 1 : ℕ) : ℝ) ^ 2 * q (k + 1))) := by
              rw [Finset.mul_sum]
        _ = ∑ k ∈ Finset.range (N + 1),
            ((((k + 1 : ℕ) : ℝ) ^ 2 * p k) +
              (((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1))) := by
              apply Finset.sum_congr rfl
              intro k hk
              exact hpoint k
        _ = (∑ k ∈ Finset.range (N + 1),
              ((k + 1 : ℕ) : ℝ) ^ 2 * p k) +
            ∑ k ∈ Finset.range (N + 1),
              ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1) := by
              rw [Finset.sum_add_distrib]
        _ = _ := by
              have htail :
                  (∑ k ∈ Finset.range (N + 1),
                    ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) =
                    ∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1) := by
                rw [Finset.sum_range_succ]
                simp [hlast]
              rw [htail]
    have hpolynomial :
        (∑ k ∈ Finset.range (N + 1), ((k : ℝ) ^ 2 + ((k + 1 : ℕ) : ℝ) ^ 2) * p k) =
          2 * (∑ k ∈ Finset.range (N + 1), (((k : ℝ) + 1 / 2) ^ 2) * p k) +
            (1 / 2) * (∑ k ∈ Finset.range (N + 1), p k) := by
      calc
        _ = ∑ k ∈ Finset.range (N + 1),
            (2 * ((((k : ℝ) + 1 / 2) ^ 2) * p k) + (1 / 2) * p k) := by
              apply Finset.sum_congr rfl
              intro k hk
              push_cast
              ring
        _ = _ := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hmerge :
        (∑ k ∈ Finset.range (N + 1), ((k + 1 : ℕ) : ℝ) ^ 2 * p k) +
          (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) =
        ∑ k ∈ Finset.range (N + 1),
          ((k : ℝ) ^ 2 + ((k + 1 : ℕ) : ℝ) ^ 2) * p k := by
      rw [← hshift, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hqExpand]
    have hsumP : ∑ k ∈ Finset.range (N + 1), p k = 1 / 2 := by linarith [hnorm]
    calc
      _ = ∑ k ∈ Finset.range (N + 1),
          ((k : ℝ) ^ 2 + ((k + 1 : ℕ) : ℝ) ^ 2) * p k := hmerge
      _ = 2 * (∑ k ∈ Finset.range (N + 1), (((k : ℝ) + 1 / 2) ^ 2) * p k) +
          (1 / 2) * (∑ k ∈ Finset.range (N + 1), p k) := hpolynomial
      _ = 2 * (∑ k ∈ Finset.range (N + 1), (((k : ℝ) + 1 / 2) ^ 2) * p k) + 1 / 4 := by
          rw [hsumP]
          ring
  have hqnorm' : M + 2 * (∑ k ∈ Finset.range (N + 1), q (k + 1)) = 1 := by
    simpa [hq0] using hqnorm
  have hqEstimate := symmetricProfile_maxAtom_le_of_logConcave q M hM hq0
    hqpos hqzero hqcenter hqLC hqnorm'
  rw [hqMoment] at hqEstimate
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  nlinarith [hqEstimate, hM2]








end Critical2DKPZ.WalkTails

end
