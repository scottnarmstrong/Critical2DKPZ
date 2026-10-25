/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LogNormality.LatticeInputs
public import Critical2DKPZ.LogNormality.Probability
public import Critical2DKPZ.Blocks.GridAlignment
public import Critical2DKPZ.MomentBounds.CCR25FreeKernelGaussian
import Mathlib.Tactic

/-! # Grid variance estimates for lattice log-normality -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.LogNormality

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer
open Critical2DKPZ.FutureProfiles Critical2DKPZ.Gaussian

private theorem sum_inv_nat_sq_interval_le_two {m U : ℕ} (hm : 1 ≤ m) :
    ∑ j ∈ Finset.Icc m U, ((j : ℝ)⁻¹) ^ 2 ≤ 2 := by
  have hfull : ∑ j ∈ Finset.Icc 1 U, ((j : ℝ)⁻¹) ^ 2 ≤ 2 := by
    calc
      _ = ∑ n ∈ Finset.range U, ((n : ℝ) + 1)⁻¹ ^ 2 := by
        apply Finset.sum_bij (fun j _ => j - 1)
        · intro j hj
          have hj' := Finset.mem_Icc.mp hj
          simp only [Finset.mem_range]
          omega
        · intro j hj k hk hEq
          have hj' := Finset.mem_Icc.mp hj
          have hk' := Finset.mem_Icc.mp hk
          omega
        · intro n hn
          refine ⟨n + 1, Finset.mem_Icc.mpr ?_, ?_⟩
          · simp only [Finset.mem_range] at hn
            omega
          · simp only [Nat.add_sub_cancel]
        · intro j hj
          have hj' := Finset.mem_Icc.mp hj
          have hjcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ j)]
            push_cast
            ring
          rw [hjcast]
      _ ≤ 2 := Critical2DKPZ.MomentBounds.ccr25_time_inverse_square_sum_le_two U
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 U, ((j : ℝ)⁻¹) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact Finset.mem_Icc.mpr ⟨hm.trans (Finset.mem_Icc.mp hj).1, (Finset.mem_Icc.mp hj).2⟩
      · intro j hj _
        positivity
    _ ≤ 2 := hfull

private theorem scaled_sum_inv_nat_sq_interval_le_two {m U : ℕ} (hm : 1 ≤ m)
    (D : ℝ) (hD : 0 ≤ D) :
    D * (∑ j ∈ Finset.Icc m U, ((j : ℝ)⁻¹) ^ 2) ≤ 2 * D := by
  have hsq := sum_inv_nat_sq_interval_le_two (m := m) (U := U) hm
  calc
    _ ≤ D * 2 := mul_le_mul_of_nonneg_left hsq hD
    _ = 2 * D := by ring

private theorem sum_reverse_Icc {K a b : ℕ} (hab : a ≤ b) (hbK : b ≤ K)
    (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc (K - b) (K - a), f (K - i) =
      ∑ j ∈ Finset.Icc a b, f j := by
  apply Finset.sum_bij (fun i _ => K - i)
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi k hk hEq
    have hi' := Finset.mem_Icc.mp hi
    have hk' := Finset.mem_Icc.mp hk
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨K - j, Finset.mem_Icc.mpr ?_, ?_⟩
    · omega
    · omega
  · intro i hi
    rfl

private theorem sum_sub_shift_Icc {a b : ℕ} (hab : a ≤ b) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.Icc (a + 1) b, (f i - f (i - 1)) = f b - f a := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      by_cases hab' : a = b
      · subst b
        simp
      · have habPrev : a ≤ b - 1 := by omega
        have hlt : b - 1 < b := by omega
        have hsum :
            (∑ i ∈ Finset.Icc (a + 1) b, (f i - f (i - 1))) =
              (∑ i ∈ Finset.Icc (a + 1) (b - 1), (f i - f (i - 1))) +
                (f b - f (b - 1)) := by
          have h := Finset.sum_Icc_succ_top (a := a + 1) (b := b - 1)
            (by omega : a + 1 ≤ (b - 1) + 1) (fun i => f i - f (i - 1))
          rw [show (b - 1) + 1 = b by omega] at h
          exact h
        rw [hsum, ih (b - 1) hlt (a := a) habPrev]
        linarith

private theorem sum_log_gap_ratio_forward_Icc {a b : ℕ} (hab : a < b)
    (g : ℕ → ℝ) (hg : ∀ j ∈ Finset.Icc a b, 0 < g j) :
    ∑ j ∈ Finset.Icc a (b - 1), Real.log (g (j + 1) / g j) =
      Real.log (g b / g a) := by
  have hterm (j : ℕ) (hj : j ∈ Finset.Icc a (b - 1)) :
      Real.log (g (j + 1) / g j) = Real.log (g (j + 1)) - Real.log (g j) := by
    have hj' := Finset.mem_Icc.mp hj
    have hgj : j ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨hj'.1, by omega⟩
    have hgj1 : j + 1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    rw [Real.log_div (hg (j + 1) hgj1).ne' (hg j hgj).ne']
  calc
    _ = ∑ j ∈ Finset.Icc a (b - 1),
        (Real.log (g (j + 1)) - Real.log (g j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm j hj
    _ = ∑ i ∈ Finset.Icc (a + 1) b,
        (Real.log (g i) - Real.log (g (i - 1))) := by
      apply Finset.sum_bij (fun j _ => j + 1)
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        simp only [Finset.mem_Icc]
        omega
      · intro j hj k hk hEq
        omega
      · intro i hi
        have hi' := Finset.mem_Icc.mp hi
        refine ⟨i - 1, Finset.mem_Icc.mpr ?_, ?_⟩
        · omega
        · omega
      · intro j hj
        simp only [Nat.add_sub_cancel_right]
    _ = Real.log (g b) - Real.log (g a) := by
      exact sum_sub_shift_Icc (a := a) (b := b) (Nat.le_of_lt hab)
        (fun j => Real.log (g j))
    _ = Real.log (g b / g a) := by
      rw [Real.log_div (hg b (Finset.mem_Icc.mpr ⟨Nat.le_of_lt hab, le_rfl⟩)).ne'
        (hg a (Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_of_lt hab⟩)).ne']


private theorem blockTime_grid_offset_eq {δ ρ : ℝ} {N j : ℕ}
    (hK : 2 * gridBlocks δ ρ < blockCount N (gridRatio δ ρ))
    (hj : 0 < j) (hj2J : j ≤ 2 * gridBlocks δ ρ) :
    blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) - j) =
      evenCeil ((N : ℝ) * (gridRatio δ ρ) ^ (-(j : ℝ))) := by
  let K := blockCount N (gridRatio δ ρ)
  have hjK : j < K := by dsimp [K]; omega
  have hidx0 : 0 < K - j := by dsimp [K]; omega
  have hidxK : K - j < blockCount N (gridRatio δ ρ) := by dsimp [K]; omega
  have hidx0' : 0 < blockCount N (gridRatio δ ρ) - j := by simpa [K] using hidx0
  have hcast : ((K - j : ℕ) : ℝ) - (blockCount N (gridRatio δ ρ) : ℝ) = -(j : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hjK)]
    ring
  rw [Critical2DKPZ.blockTime, ite_eq_right (Nat.ne_of_gt hidx0'), ite_eq_left hidxK]
  rw [hcast]

private theorem blockTime_grid_offset_bounds {δ ρ : ℝ} (hδ : 0 < δ) {N j : ℕ}
    (hK : 2 * gridBlocks δ ρ < blockCount N (gridRatio δ ρ))
    (hj : 0 < j) (hj2J : j ≤ 2 * gridBlocks δ ρ) :
    (N : ℝ) * (gridRatio δ ρ) ^ (-(j : ℝ)) ≤
        (blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) - j) : ℝ) ∧
      (blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) - j) : ℝ) <
        (N : ℝ) * (gridRatio δ ρ) ^ (-(j : ℝ)) + 2 := by
  rw [blockTime_grid_offset_eq hK hj hj2J]
  have hγ : 0 < gridRatio δ ρ := Real.rpow_pos_of_pos hδ _
  exact ⟨le_evenCeil _, evenCeil_lt_add_two
    (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hγ.le _))⟩

private theorem grid_offset_scaled_time_ge_two_eventually {δ ρ : ℝ}
    (hρ : 1 < ρ) (hδ : 0 < δ) (hδρ : δ ≤ ρ⁻¹ ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.Icc 1 (2 * gridBlocks δ ρ),
      2 ≤ (N : ℝ) * (gridRatio δ ρ) ^ (-(j : ℝ)) := by
  let γ := gridRatio δ ρ
  let J := gridBlocks δ ρ
  have hgrid := gridRatio_mem hρ hδ hδρ
  have hγpos : 0 < γ := lt_of_lt_of_le (by linarith : 0 < ρ) hgrid.1
  have hγone : 1 < γ := lt_of_lt_of_le hρ hgrid.1
  have hJnat := (gridBlocks_bounds hρ hδ hδρ).1
  have hJpos : 0 < (J : ℝ) := by
    dsimp [J]
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hJnat)
  have hγpow : γ ^ (-(2 * (J : ℝ))) = δ := by
    dsimp [γ, J]
    exact gridRatio_pow_double δ ρ hδ hJpos
  let nSmall : ℕ := ⌈2 / δ⌉₊
  have hsmallEvent : ∀ᶠ N : ℕ in atTop, nSmall ≤ N := eventually_ge_atTop nSmall
  filter_upwards [hsmallEvent] with N hsmall
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hNbound : 2 / δ ≤ (N : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hsmall)
  have hNc : 2 ≤ (N : ℝ) * δ := (div_le_iff₀ hδ).mp hNbound
  have hjCast : (j : ℝ) ≤ 2 * (J : ℝ) := by
    dsimp [J]
    exact_mod_cast hj'.2
  have hexp : -(2 * (J : ℝ)) ≤ -(j : ℝ) := by linarith
  have hpow : γ ^ (-(2 * (J : ℝ))) ≤ γ ^ (-(j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hγone.le hexp
  calc
    2 ≤ (N : ℝ) * δ := hNc
    _ = (N : ℝ) * γ ^ (-(2 * (J : ℝ))) := by rw [hγpow]
    _ ≤ (N : ℝ) * γ ^ (-(j : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg N)

private theorem criticalGap_grid_offset_bounds (ϑ ρ ε Cgap : ℝ)
    (hgap : ∀ᶠ N : ℕ in atTop, ∀ ϑ' ∈ Set.Icc (-|ϑ|) |ϑ|, ∀ t : ℕ, t ≤ N →
      |renewalGap (criticalBeta ϑ' N) t -
        Real.log ((N : ℝ) / ((max t 1 : ℕ) : ℝ))| ≤ Cgap)
    (hρ : 1 < ρ)
    (hε : 0 < ε) (hε1 : ε < 1) (hεscale : ε ^ 2 ≤ ρ⁻¹ ^ 2) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.Icc 1 (2 * gridBlocks (ε ^ 2) ρ),
      |renewalGap (criticalBeta ϑ N)
          (blockTime N (gridRatio (ε ^ 2) ρ)
            (blockCount N (gridRatio (ε ^ 2) ρ) - j)) -
        (j : ℝ) * Real.log (gridRatio (ε ^ 2) ρ)| ≤ |Cgap| + Real.log 2 := by
  let δ := ε ^ 2
  let γ := gridRatio δ ρ
  let J := gridBlocks δ ρ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ ≤ ρ⁻¹ ^ 2 := by simpa [δ] using hεscale
  have hgrid := gridRatio_mem hρ hδ hδρ
  have hγpos : 0 < γ := lt_of_lt_of_le (by linarith : 0 < ρ) hgrid.1
  have hγone : 1 < γ := lt_of_lt_of_le hρ hgrid.1
  have hlogγ : 0 < Real.log γ := Real.log_pos hγone
  have hJpos : 1 ≤ J := by
    dsimp [J, δ]
    exact (gridBlocks_bounds hρ hδ hδρ).1
  have hgridEvent := blockTime_gridRatio hρ hδ hδρ
  let c : ℝ := γ ^ (-(2 * (J : ℝ)))
  have hc : 0 < c := by dsimp [c]; exact Real.rpow_pos_of_pos hγpos _
  let nRound : ℕ := ⌈2 * ρ / (ρ - 1)⌉₊
  let nSmall : ℕ := ⌈2 / c⌉₊
  have hroundEvent : ∀ᶠ N : ℕ in atTop, nRound ≤ N := eventually_ge_atTop nRound
  have hsmallEvent : ∀ᶠ N : ℕ in atTop, nSmall ≤ N := eventually_ge_atTop nSmall
  filter_upwards [hgridEvent, hroundEvent, hsmallEvent,
    hgap, eventually_ge_atTop 2] with N hgridN hroundN hsmallN hgapN hN2
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hjpos : 0 < j := by omega
  have hK : 2 * J < blockCount N γ := by simpa [δ, γ, J] using hgridN.1
  have hj2J : j ≤ 2 * J := by simpa [J, δ] using hj'.2
  have hNpos : 0 < (N : ℝ) := by
    have hNlower : 0 < 2 * ρ / (ρ - 1) := by positivity
    have hNle : nRound ≤ N := hroundN
    have hNlower' : 2 * ρ / (ρ - 1) ≤ (N : ℝ) := by
      exact (Nat.le_ceil _).trans (by exact_mod_cast hNle)
    exact lt_of_lt_of_le hNlower hNlower'
  have hNround : 2 * ρ / (ρ - 1) ≤ (N : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hroundN)
  have hNsmall : 2 / c ≤ (N : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast hsmallN)
  have hNc : 2 ≤ (N : ℝ) * c := (div_le_iff₀ hc).mp hNsmall
  have hjExpLower : -(2 * (J : ℝ)) ≤ -(j : ℝ) := by
    have hjcast : (j : ℝ) ≤ 2 * (J : ℝ) := by exact_mod_cast hj2J
    linarith
  have hjExpUpper : -(j : ℝ) ≤ -1 := by
    have hjcast : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show 1 ≤ j by omega)
    linarith
  have hpowLower : c ≤ γ ^ (-(j : ℝ)) := by
    dsimp [c]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [hgrid.1]) hjExpLower
  have hpowUpper : γ ^ (-(j : ℝ)) ≤ γ⁻¹ := by
    calc
      γ ^ (-(j : ℝ)) ≤ γ ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hgrid.1]) hjExpUpper
      _ = γ⁻¹ := Real.rpow_neg_one γ
  have hinv : γ⁻¹ ≤ ρ⁻¹ := (inv_le_inv₀ hγpos (by linarith : 0 < ρ)).2 hgrid.1
  let q : ℝ := (N : ℝ) * γ ^ (-(j : ℝ))
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqLower : 2 ≤ q := by
    dsimp [q]
    calc
      2 ≤ (N : ℝ) * c := hNc
      _ ≤ (N : ℝ) * γ ^ (-(j : ℝ)) :=
        mul_le_mul_of_nonneg_left hpowLower (Nat.cast_nonneg N)
  have hqUpper : q ≤ (N : ℝ) / ρ := by
    dsimp [q]
    calc
      _ ≤ (N : ℝ) * ρ⁻¹ := mul_le_mul_of_nonneg_left
        (hpowUpper.trans hinv) (Nat.cast_nonneg N)
      _ = (N : ℝ) / ρ := by rw [div_eq_mul_inv]
  have hNmult : 2 * ρ ≤ (N : ℝ) * (ρ - 1) :=
    (div_le_iff₀ (by linarith : 0 < ρ - 1)).mp hNround
  have hNadd : 2 ≤ (N : ℝ) * (ρ - 1) / ρ :=
    (le_div_iff₀ (by linarith : 0 < ρ)).2 hNmult
  have hNround' : (N : ℝ) / ρ + 2 ≤ (N : ℝ) := by
    have hid : (N : ℝ) / ρ + (N : ℝ) * (ρ - 1) / ρ = (N : ℝ) := by
      field_simp [ne_of_gt (by linarith : 0 < ρ)]
      ring
    calc
      (N : ℝ) / ρ + 2 = 2 + (N : ℝ) / ρ := by ring
      _ ≤ (N : ℝ) * (ρ - 1) / ρ + (N : ℝ) / ρ := add_le_add_left hNadd _
      _ = (N : ℝ) / ρ + (N : ℝ) * (ρ - 1) / ρ := by ring
      _ = (N : ℝ) := hid
  have htime := blockTime_grid_offset_bounds hδ hK hjpos hj2J
  have htimeLE :
      (blockTime N γ (blockCount N γ - j) : ℝ) ≤ (N : ℝ) := by
    have hstrict : (blockTime N γ (blockCount N γ - j) : ℝ) < (N : ℝ) := calc
      _ < q + 2 := by simpa [q] using htime.2
      _ ≤ (N : ℝ) / ρ + 2 := by linarith [hqUpper]
      _ ≤ (N : ℝ) := hNround'
    exact hstrict.le
  have htimePos : 0 < (blockTime N γ (blockCount N γ - j) : ℝ) := by
    have hqle := htime.1
    have hq2 : 2 ≤ q := hqLower
    linarith
  have htimeNatLE : blockTime N γ (blockCount N γ - j) ≤ N := by
    exact_mod_cast htimeLE
  have hϑ : ϑ ∈ Set.Icc (-|ϑ|) |ϑ| :=
    Set.mem_Icc.mpr ⟨neg_abs_le ϑ, le_abs_self ϑ⟩
  have htimeNatPos : 0 < blockTime N γ (blockCount N γ - j) := by
    exact_mod_cast htimePos
  have hmax : max (blockTime N γ (blockCount N γ - j)) 1 =
      blockTime N γ (blockCount N γ - j) := max_eq_left (by omega :
        1 ≤ blockTime N γ (blockCount N γ - j))
  have hgapN' := hgapN ϑ hϑ (blockTime N γ (blockCount N γ - j)) htimeNatLE
  have hgapN'' :
      |renewalGap (criticalBeta ϑ N) (blockTime N γ (blockCount N γ - j)) -
        Real.log ((N : ℝ) / (blockTime N γ (blockCount N γ - j) : ℝ))| ≤ Cgap := by
    simpa only [hmax] using hgapN'
  have hlogq : Real.log q = Real.log (N : ℝ) - (j : ℝ) * Real.log γ := by
    dsimp [q]
    rw [Real.log_mul hNpos.ne' (Real.rpow_pos_of_pos hγpos _).ne',
      Real.rpow_neg hγpos.le, Real.log_inv, Real.rpow_natCast, Real.log_pow]
    ring
  have hlogtLower : Real.log q ≤
      Real.log (blockTime N γ (blockCount N γ - j) : ℝ) :=
    Real.log_le_log hqpos htime.1
  have hlogtUpper : Real.log (blockTime N γ (blockCount N γ - j) : ℝ) ≤
      Real.log (2 * q) := by
    apply Real.log_le_log htimePos
    have htimeUpper : (blockTime N γ (blockCount N γ - j) : ℝ) < 2 * q := by
      calc
        _ < q + 2 := by simpa [q] using htime.2
        _ ≤ 2 * q := by linarith [hqLower]
    exact htimeUpper.le
  have hlog2q : Real.log (2 * q) = Real.log 2 + Real.log q :=
    Real.log_mul (by norm_num) hqpos.ne'
  have hlogNt : Real.log ((N : ℝ) /
      (blockTime N γ (blockCount N γ - j) : ℝ)) =
      Real.log (N : ℝ) - Real.log (blockTime N γ (blockCount N γ - j) : ℝ) :=
    Real.log_div hNpos.ne' htimePos.ne'
  have hlogApprox : |Real.log ((N : ℝ) /
      (blockTime N γ (blockCount N γ - j) : ℝ)) - (j : ℝ) * Real.log γ| ≤ Real.log 2 := by
    rw [abs_le]
    constructor <;> linarith [hlogtLower, hlogtUpper, hlog2q, hlogNt, hlogq]
  have htriangle :
      |renewalGap (criticalBeta ϑ N) (blockTime N γ (blockCount N γ - j)) -
          (j : ℝ) * Real.log γ| ≤
        |renewalGap (criticalBeta ϑ N) (blockTime N γ (blockCount N γ - j)) -
          Real.log ((N : ℝ) / (blockTime N γ (blockCount N γ - j) : ℝ))| +
        |Real.log ((N : ℝ) / (blockTime N γ (blockCount N γ - j) : ℝ)) -
          (j : ℝ) * Real.log γ| := abs_sub_le _ _ _
  have hgapError :
      |renewalGap (criticalBeta ϑ N) (blockTime N γ (blockCount N γ - j)) -
          Real.log ((N : ℝ) / (blockTime N γ (blockCount N γ - j) : ℝ))| ≤ |Cgap| :=
    le_trans hgapN'' (le_abs_self Cgap)
  simpa [δ, γ] using htriangle.trans (add_le_add hgapError hlogApprox)

private theorem blockTime_adjacent_ratio_le {δ ρ : ℝ} (hδ : 0 < δ) {N j : ℕ}
    (hK : 2 * gridBlocks δ ρ < blockCount N (gridRatio δ ρ))
    (hj : 0 < j) (hj1 : j + 1 ≤ 2 * gridBlocks δ ρ)
    (hqprev : 2 ≤ (N : ℝ) * (gridRatio δ ρ) ^ (-((j + 1 : ℕ) : ℝ))) :
    (blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) - j) : ℝ) /
      (blockTime N (gridRatio δ ρ) (blockCount N (gridRatio δ ρ) - (j + 1)) : ℝ) ≤
        gridRatio δ ρ + 1 := by
  let γ := gridRatio δ ρ
  let q := (N : ℝ) * γ ^ (-(j : ℝ))
  let qprev := (N : ℝ) * γ ^ (-((j + 1 : ℕ) : ℝ))
  have hγ : 0 < γ := Real.rpow_pos_of_pos hδ _
  have hNpos : 0 < (N : ℝ) := by
    by_contra! hN
    have hpow : 0 ≤ γ ^ (-((j + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hγ.le _
    have hprod : (N : ℝ) * γ ^ (-((j + 1 : ℕ) : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hN hpow
    have hprod' : (N : ℝ) * (gridRatio δ ρ) ^ (-((j + 1 : ℕ) : ℝ)) ≤ 0 := by
      simpa only [γ] using hprod
    linarith
  have hqpos : 0 < q := by dsimp [q]; exact mul_pos hNpos (Real.rpow_pos_of_pos hγ _)
  have hqprevpos : 0 < qprev := by
    dsimp [qprev]
    exact mul_pos hNpos (Real.rpow_pos_of_pos hγ _)
  have hqprev2 : 2 ≤ qprev := by simpa [qprev, γ] using hqprev
  have hqrel : q = γ * qprev := by
    dsimp [q, qprev, γ]
    have hexp : -(j : ℝ) = -((j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hexp, Real.rpow_add hγ, Real.rpow_one]
    ring
  have ht := blockTime_grid_offset_bounds hδ hK hj (by omega)
  have htprev := blockTime_grid_offset_bounds hδ hK (by omega) hj1
  have hprevpos : 0 <
      (blockTime N γ (blockCount N γ - (j + 1)) : ℝ) := lt_of_lt_of_le hqprevpos htprev.1
  have hNumerator :
      (blockTime N γ (blockCount N γ - j) : ℝ) ≤
        (γ + 1) * (blockTime N γ (blockCount N γ - (j + 1)) : ℝ) := by
    have hround :
        (blockTime N γ (blockCount N γ - j) : ℝ) ≤ q + 2 := ht.2.le
    have hqstep : q + 2 ≤ (γ + 1) * qprev := by
      rw [hqrel]
      nlinarith [hqprev2]
    have hprevle : qprev ≤
        (blockTime N γ (blockCount N γ - (j + 1)) : ℝ) := by
      simpa [qprev, γ] using htprev.1
    calc
      _ ≤ q + 2 := hround
      _ ≤ (γ + 1) * qprev := hqstep
      _ ≤ (γ + 1) * (blockTime N γ (blockCount N γ - (j + 1)) : ℝ) :=
        mul_le_mul_of_nonneg_left hprevle (by positivity)
  exact (div_le_iff₀ hprevpos).2 hNumerator

private theorem variance_gap_log_approx {j : ℕ} (hj : 1 ≤ j) {L A C gprev g e V : ℝ}
    (hL : 0 < L) (hA : 2 * A ≤ L)
    (hgLower : (j : ℝ) * L - A ≤ g)
    (hgUpper : g ≤ (j : ℝ) * L + A)
    (hprevLower : ((j + 1 : ℕ) : ℝ) * L - A ≤ gprev)
    (hdiff : |gprev - g| ≤ 2 * L) (he : 0 ≤ e)
    (heUpper : e ≤ 8 * C / (j : ℝ) ^ 2)
    (hV : V = gprev / g - 1 - e) :
    |V - Real.log (gprev / g)| ≤ (48 + 8 * C) / (j : ℝ) ^ 2 := by
  have hjR : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hA' : A ≤ L / 2 := by nlinarith
  have hgLower' : (j : ℝ) * L / 2 ≤ g := by
    have hjL : L / 2 ≤ (j : ℝ) * L / 2 := by nlinarith
    linarith
  have hgpos : 0 < g := by
    have hjLpos : 0 < (j : ℝ) * L / 2 := by positivity
    linarith
  have hprevLower' : ((j + 1 : ℕ) : ℝ) * L / 2 ≤ gprev := by
    have hj1L : 2 * A ≤ ((j + 1 : ℕ) : ℝ) * L := by
      have hj1 : (1 : ℝ) ≤ (j + 1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 j)
      nlinarith
    linarith
  have hprevpos : 0 < gprev := by
    have hj1Lpos : 0 < ((j + 1 : ℕ) : ℝ) * L / 2 := by positivity
    linarith
  let z := gprev / g
  have hz : 0 < z := div_pos hprevpos hgpos
  have hInv : g / gprev ≤ 2 := by
    apply (div_le_iff₀ hprevpos).2
    have hgUp : g ≤ ((j + 1 : ℕ) : ℝ) * L := by
      have hjA : A ≤ L := by linarith
      have hjCast : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by norm_cast
      rw [← hjCast]
      nlinarith
    have hmul : 2 * g ≤ 4 * gprev := by nlinarith [hgUp, hprevLower']
    linarith
  have hratioDiff : |z - 1| ≤ 4 / (j : ℝ) := by
    have hzform : z - 1 = (gprev - g) / g := by
      dsimp [z]
      field_simp [ne_of_gt hgpos]
    rw [hzform, abs_div, abs_of_pos hgpos]
    apply (div_le_div_iff₀ hgpos (by positivity : 0 < (j : ℝ))).2
    have hdiffMul : |gprev - g| * (j : ℝ) ≤ 4 * g := by
      nlinarith [hdiff, hgLower']
    simpa [mul_comm] using hdiffMul
  have hratioSq : (z - 1) ^ 2 ≤ (4 / (j : ℝ)) ^ 2 := by
    rw [← sq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 4 / (j : ℝ))).2
    exact hratioDiff
  have hInvEq : z⁻¹ = g / gprev := by
    dsimp [z]
    field_simp [ne_of_gt hgpos, ne_of_gt hprevpos]
  have hfactor : 1 + z⁻¹ ≤ 3 := by rw [hInvEq]; linarith
  have hTaylor : |Real.log z - (z - 1)| ≤ (z - 1) ^ 2 * (1 + z⁻¹) :=
    abs_log_sub_sub_one_le hz
  have hTaylor' : |(z - 1) - Real.log z| ≤ 48 / (j : ℝ) ^ 2 := by
    have hsq : (4 / (j : ℝ)) ^ 2 = 16 / (j : ℝ) ^ 2 := by ring
    calc
      _ = |-(Real.log z - (z - 1))| := by congr 1; ring
      _ = |Real.log z - (z - 1)| := abs_neg _
      _ ≤ (z - 1) ^ 2 * (1 + z⁻¹) := hTaylor
      _ ≤ (4 / (j : ℝ)) ^ 2 * (1 + z⁻¹) :=
        mul_le_mul_of_nonneg_right hratioSq (by positivity)
      _ ≤ (4 / (j : ℝ)) ^ 2 * 3 :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = 48 / (j : ℝ) ^ 2 := by rw [hsq]; ring
  have hVform : V - Real.log z = ((z - 1) - Real.log z) - e := by rw [hV]; dsimp [z]; ring
  have htriangle : |((z - 1) - Real.log z) - e| ≤
      |(z - 1) - Real.log z| + |e| := by
    calc
      _ ≤ |((z - 1) - Real.log z) - (0 : ℝ)| + |(0 : ℝ) - e| :=
        abs_sub_le ((z - 1) - Real.log z) 0 e
      _ = |(z - 1) - Real.log z| + |e| := by
        rw [sub_zero]
        congr 1
        rw [show (0 : ℝ) - e = -e by ring, abs_neg]
  calc
    _ = |((z - 1) - Real.log z) - e| := by rw [hVform]
    _ ≤ |(z - 1) - Real.log z| + |e| := htriangle
    _ = |(z - 1) - Real.log z| + e := by rw [abs_of_nonneg he]
    _ ≤ 48 / (j : ℝ) ^ 2 + 8 * C / (j : ℝ) ^ 2 := add_le_add hTaylor' heUpper
    _ = (48 + 8 * C) / (j : ℝ) ^ 2 := by ring

private def SmoothedPartitionVarianceBounds (C : ℝ) : Prop :=
  ∀ β : ℝ, 0 < β → ∀ s t : ℕ, s ≤ t → 0 < renewalGap β t →
    Var[fun ω => smoothedP2Plane β s t 0 ω; disorderLaw] ≤
        renewalGap β s / renewalGap β t - 1 ∧
      (1 ≤ s → 2 * s ≤ t →
        renewalGap β s / renewalGap β t - 1 -
            C * Real.log ((t : ℝ) / s) / renewalGap β t ^ 2 ≤
          Var[fun ω => smoothedP2Plane β s t 0 ω; disorderLaw])

private theorem variance_blockMass_log_gap_of {β C L A gprev g : ℝ}
    {j i : ℕ} {T : ℕ → ℕ}
    (hj : 1 ≤ j) (hSmoothedPartitionVarianceInput : SmoothedPartitionVarianceBounds C) (hβ : 0 < β)
    (hL : 0 < L) (hLone : 1 ≤ L) (hA : 2 * A ≤ L)
    (hgLower : (j : ℝ) * L - A ≤ g)
    (hgUpper : g ≤ (j : ℝ) * L + A)
    (hprevLower : ((j + 1 : ℕ) : ℝ) * L - A ≤ gprev)
    (hdiff : |gprev - g| ≤ 2 * L)
    (hcurGap : renewalGap β (T i) = g)
    (hprevGap : renewalGap β (T (i - 1)) = gprev)
    (hs : 1 ≤ T (i - 1)) (hsep : 2 * T (i - 1) ≤ T i)
    (hlogR : 0 ≤ Real.log ((T i : ℝ) / (T (i - 1) : ℝ)))
    (hlogRUpper : Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) ≤ 2 * L) :
    |Var[fun ω => blockMass β T i ω; disorderLaw] -
        Real.log (gprev / g)| ≤ (48 + 8 * |C|) / (j : ℝ) ^ 2 := by
  have hjR : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hgpos : 0 < g := by
    have hjL : (1 : ℝ) ≤ (j : ℝ) := hjR
    nlinarith [hgLower]
  let V := Var[fun ω => blockMass β T i ω; disorderLaw]
  have hK := hSmoothedPartitionVarianceInput β hβ (T (i - 1)) (T i) (by omega)
    (by rw [hcurGap]; exact hgpos)
  have hVarRange : V ≤ gprev / g - 1 ∧
      gprev / g - 1 - C * Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2 ≤ V := by
    constructor
    · simpa [V, blockMass, hcurGap, hprevGap] using hK.1
    · have h := hK.2 hs hsep
      simpa [V, blockMass, hcurGap, hprevGap] using h
  let e := gprev / g - 1 - V
  have he : 0 ≤ e := by dsimp [e]; linarith [hVarRange.1]
  have hfacNonneg : 0 ≤ Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2 :=
    div_nonneg hlogR (sq_nonneg g)
  have heRaw : e ≤ C * Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2 := by
    dsimp [e]
    linarith [hVarRange.2]
  have heAbs : e ≤ |C| * Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2 := by
    calc
      _ ≤ C * Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2 := heRaw
      _ = C * (Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2) := by ring
      _ ≤ |C| * (Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hfacNonneg
      _ = |C| * Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2 := by ring
  have hnum : |C| * Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) ≤ |C| * (2 * L) :=
    mul_le_mul_of_nonneg_left hlogRUpper (abs_nonneg C)
  have hgapLower : (j : ℝ) * L / 2 ≤ g := by nlinarith [hgLower]
  have hjLnonneg : 0 ≤ (j : ℝ) * L / 2 := by positivity
  have hgNonneg : 0 ≤ g := le_trans hjLnonneg hgapLower
  have hgapSq : ((j : ℝ) * L / 2) ^ 2 ≤ g ^ 2 :=
    (sq_le_sq₀ hjLnonneg hgNonneg).2 hgapLower
  have hlowerSqPos : 0 < ((j : ℝ) * L / 2) ^ 2 := by positivity
  have hupperSqPos : 0 < g ^ 2 := by positivity
  have hquot : |C| * (2 * L) / g ^ 2 ≤
      |C| * (2 * L) / ((j : ℝ) * L / 2) ^ 2 := by
    apply (div_le_div_iff₀ hupperSqPos hlowerSqPos).2
    exact mul_le_mul_of_nonneg_left hgapSq (by positivity)
  have hconst : |C| * (2 * L) / ((j : ℝ) * L / 2) ^ 2 =
      8 * |C| / ((j : ℝ) ^ 2 * L) := by
    field_simp [ne_of_gt hL, ne_of_gt (show (0 : ℝ) < (j : ℝ) by positivity)]
    ring
  have hconstLe : 8 * |C| / ((j : ℝ) ^ 2 * L) ≤
      8 * |C| / (j : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos (by positivity) hL)
      (by positivity : 0 < (j : ℝ) ^ 2)).2
    exact mul_le_mul_of_nonneg_left
      (by simpa using mul_le_mul_of_nonneg_left hLone (sq_nonneg (j : ℝ)))
      (by positivity)
  have heUpper : e ≤ 8 * |C| / (j : ℝ) ^ 2 := by
    calc
      _ ≤ |C| * Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) / g ^ 2 := heAbs
      _ ≤ |C| * (2 * L) / g ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg g)
      _ ≤ |C| * (2 * L) / ((j : ℝ) * L / 2) ^ 2 := hquot
      _ = 8 * |C| / ((j : ℝ) ^ 2 * L) := hconst
      _ ≤ 8 * |C| / (j : ℝ) ^ 2 := hconstLe
  have hV : V = gprev / g - 1 - e := by dsimp [e]; ring
  exact variance_gap_log_approx hj hL hA hgLower hgUpper hprevLower hdiff he heUpper hV

private theorem variance_blockMass_grid_offsets_eventually (ϑ ρ ε Cgap Craw : ℝ)
    (hgap : ∀ᶠ N : ℕ in atTop, ∀ ϑ' ∈ Set.Icc (-|ϑ|) |ϑ|, ∀ t : ℕ, t ≤ N →
      |renewalGap (criticalBeta ϑ' N) t -
        Real.log ((N : ℝ) / ((max t 1 : ℕ) : ℝ))| ≤ Cgap)
    (hSmoothedPartitionVarianceInput : SmoothedPartitionVarianceBounds Craw)
    (hρ : 1 < ρ) (hε : 0 < ε) (hε1 : ε < 1)
    (hεscale : ε ^ 2 ≤ ρ⁻¹ ^ 2)
    (hLlarge : 2 * (|Cgap| + Real.log 2) + 4 ≤
      Real.log (gridRatio (ε ^ 2) ρ))
    (hγfour : 4 ≤ gridRatio (ε ^ 2) ρ) :
    ∀ᶠ N : ℕ in atTop, ∀ j ∈ Finset.Icc 1
        (2 * gridBlocks (ε ^ 2) ρ - 1),
      |Var[fun ω => blockMass (criticalBeta ϑ N)
          (blockTime N (gridRatio (ε ^ 2) ρ))
          (blockCount N (gridRatio (ε ^ 2) ρ) - j) ω; disorderLaw] -
        Real.log (
          renewalGap (criticalBeta ϑ N)
            (blockTime N (gridRatio (ε ^ 2) ρ)
              (blockCount N (gridRatio (ε ^ 2) ρ) - (j + 1))) /
          renewalGap (criticalBeta ϑ N)
            (blockTime N (gridRatio (ε ^ 2) ρ)
              (blockCount N (gridRatio (ε ^ 2) ρ) - j)))| ≤
        (48 + 8 * |Craw|) / (j : ℝ) ^ 2 := by
  let δ := ε ^ 2
  let γ := gridRatio δ ρ
  let J := gridBlocks δ ρ
  let L := Real.log γ
  let A := |Cgap| + Real.log 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ ≤ ρ⁻¹ ^ 2 := by simpa [δ] using hεscale
  have hgrid := gridRatio_mem hρ hδ hδρ
  have hγpos : 0 < γ := lt_of_lt_of_le (by linarith : 0 < ρ) hgrid.1
  have hγone : 1 < γ := lt_of_lt_of_le hρ hgrid.1
  have hLpos : 0 < L := Real.log_pos hγone
  have hLlarge' : 2 * A + 4 ≤ L := by simpa [A, L, γ, δ] using hLlarge
  have hA : 2 * A ≤ L := by linarith
  have hAnonneg : 0 ≤ A := by dsimp [A]; positivity
  have hLone : 1 ≤ L := by linarith
  have hgapEvent := criticalGap_grid_offset_bounds ϑ ρ ε Cgap hgap hρ hε hε1 hεscale
  have hgridEvent := blockTime_gridRatio hρ hδ hδρ
  have hqEvent := grid_offset_scaled_time_ge_two_eventually hρ hδ hδρ
  have hβEvent : ∀ᶠ N : ℕ in atTop, 0 < criticalBeta ϑ N := by
    have hlogEvent : ∀ᶠ N : ℕ in atTop, |ϑ| < Real.log (N : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |ϑ|
    filter_upwards [eventually_ge_atTop 1, hlogEvent] with N hN hlogN
    have hσ := criticalSigmaSq_pos_of_abs_lt_log hN hlogN
    dsimp [criticalBeta]
    apply Real.sqrt_pos.2
    exact Real.log_pos (by linarith)
  filter_upwards [hgapEvent, hgridEvent, hqEvent, hβEvent]
    with N hgapN hgridN hqN hβN
  intro j hj
  have hj' := Finset.mem_Icc.mp hj
  have hjpos : 1 ≤ j := hj'.1
  have hj2J : j + 1 ≤ 2 * J := by dsimp [J, δ]; omega
  have hjmem : j ∈ Finset.Icc 1 (2 * J) := Finset.mem_Icc.mpr ⟨hjpos, by omega⟩
  have hj1mem : j + 1 ∈ Finset.Icc 1 (2 * J) :=
    Finset.mem_Icc.mpr ⟨by omega, hj2J⟩
  have hK : 2 * J < blockCount N γ := by simpa [J, γ, δ] using hgridN.1
  have hgapJ := hgapN j (by simpa [J, δ] using hjmem)
  have hgapJ1 := hgapN (j + 1) (by simpa [J, δ] using hj1mem)
  let β := criticalBeta ϑ N
  let K := blockCount N γ
  let T := blockTime N γ
  let i := K - j
  let g : ℕ → ℝ := fun k => renewalGap β (T (K - k))
  have hgapAbs : |g j - (j : ℝ) * L| ≤ A := by
    simpa [g, β, T, K, A, L, γ, δ] using hgapJ
  have hgapPrevAbs : |g (j + 1) - ((j + 1 : ℕ) : ℝ) * L| ≤ A := by
    simpa [g, β, T, K, A, L, γ, δ] using hgapJ1
  have hgapAbs' := abs_le.mp hgapAbs
  have hgapPrevAbs' := abs_le.mp hgapPrevAbs
  have hgLower : (j : ℝ) * L - A ≤ g j := by linarith [hgapAbs'.1]
  have hgUpper : g j ≤ (j : ℝ) * L + A := by linarith [hgapAbs'.2]
  have hprevLower : ((j + 1 : ℕ) : ℝ) * L - A ≤ g (j + 1) := by
    linarith [hgapPrevAbs'.1]
  have hprevUpper : g (j + 1) ≤ ((j + 1 : ℕ) : ℝ) * L + A := by
    linarith [hgapPrevAbs'.2]
  have hcastJ : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by norm_cast
  have hdiff : |g (j + 1) - g j| ≤ 2 * L := by
    rw [abs_le]
    constructor
    · rw [hcastJ] at hprevLower
      linarith [hprevLower, hgUpper, hA]
    · rw [hcastJ] at hprevUpper
      linarith [hprevUpper, hgLower]
  let qprev := (N : ℝ) * γ ^ (-((j + 1 : ℕ) : ℝ))
  have hqprev : 2 ≤ qprev := by
    have h := hqN (j + 1) (by simpa [J, δ] using hj1mem)
    simpa [qprev, γ, δ] using h
  have hKgrid : 2 * gridBlocks δ ρ < blockCount N (gridRatio δ ρ) := by
    simpa only [J, γ] using hK
  have hjpos' : 0 < j := Nat.lt_of_lt_of_le Nat.zero_lt_one hjpos
  have htPrevBounds := blockTime_grid_offset_bounds (j := j + 1) hδ hKgrid (by omega)
    (by simpa [J] using hj2J)
  have hjLE2J : j ≤ 2 * J := Nat.le_trans (Nat.le_add_right j 1) hj2J
  have htCurBounds := blockTime_grid_offset_bounds (j := j) hδ hKgrid hjpos'
    (by simpa [J] using hjLE2J)
  have hqrel : (N : ℝ) * γ ^ (-(j : ℝ)) = γ * qprev := by
    dsimp [qprev]
    have hexp : -(j : ℝ) = -((j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [hexp, Real.rpow_add hγpos, Real.rpow_one]
    ring
  have hiPos : 0 < i := by dsimp [i, K]; omega
  have hiPrev : i - 1 = K - (j + 1) := by dsimp [i, K]; omega
  have hPrevLower : qprev ≤ (T (i - 1) : ℝ) := by
    simpa [T, K, hiPrev, qprev, γ, δ] using htPrevBounds.1
  have hsPos : 0 < (T (i - 1) : ℝ) := by
    have hqpos : 0 < qprev := lt_of_lt_of_le (by norm_num) hqprev
    exact lt_of_lt_of_le hqpos hPrevLower
  have htPos : 0 < (T i : ℝ) := by
    have hqpos : 0 < γ * qprev := mul_pos hγpos (lt_of_lt_of_le (by norm_num) hqprev)
    have hCurLower : (N : ℝ) * γ ^ (-(j : ℝ)) ≤
        (blockTime N γ (blockCount N γ - j) : ℝ) := by
      simpa [γ, δ] using htCurBounds.1
    have htimepos : 0 < (blockTime N γ (blockCount N γ - j) : ℝ) := by
      rw [hqrel] at hCurLower
      exact lt_of_lt_of_le hqpos hCurLower
    simpa [T, K, i] using htimepos
  have htimePrevUpper : (T (i - 1) : ℝ) < qprev + 2 := by
    simpa [T, K, hiPrev, qprev] using htPrevBounds.2
  have htimeCurLower : γ * qprev ≤ (T i : ℝ) := by
    have h : (N : ℝ) * γ ^ (-(j : ℝ)) ≤
        (blockTime N γ (blockCount N γ - j) : ℝ) := by
      simpa [γ, δ] using htCurBounds.1
    rw [hqrel] at h
    simpa [T, K, i] using h
  have hsepReal : 2 * (T (i - 1) : ℝ) ≤ (T i : ℝ) := by
    have hgamma : 4 * qprev ≤ γ * qprev :=
      mul_le_mul_of_nonneg_right hγfour (by positivity)
    have hround : 2 * (T (i - 1) : ℝ) < 4 * qprev := by
      linarith only [htimePrevUpper, hqprev]
    linarith
  have hsep : 2 * T (i - 1) ≤ T i := by exact_mod_cast hsepReal
  have hs : 1 ≤ T (i - 1) := by
    have hsreal : 1 ≤ (T (i - 1) : ℝ) := by linarith [hqprev, hPrevLower]
    exact_mod_cast hsreal
  have hst : T (i - 1) ≤ T i := by omega
  have hcurGap : renewalGap β (T i) = g j := by
    dsimp [g, β, T, K, i]
  have hprevGap : renewalGap β (T (i - 1)) = g (j + 1) := by
    dsimp [g, β, T, K]
    rw [hiPrev]
  have hratioPos : 0 < (T i : ℝ) / (T (i - 1) : ℝ) := div_pos htPos hsPos
  have hratioOne : 1 ≤ (T i : ℝ) / (T (i - 1) : ℝ) := by
    apply (le_div_iff₀ hsPos).2
    norm_num at hst ⊢
    exact_mod_cast hst
  have hlogR : 0 ≤ Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) :=
    Real.log_nonneg hratioOne
  have hadj := blockTime_adjacent_ratio_le hδ hKgrid (by omega) (by omega) hqprev
  have hcurTimeEq : T i = blockTime N γ (K - j) := rfl
  have hprevTimeEq : T (i - 1) = blockTime N γ (K - (j + 1)) := by
    dsimp [T, K]
    rw [hiPrev]
  have hadj' : (T i : ℝ) / (T (i - 1) : ℝ) ≤ γ + 1 := by
    rw [hcurTimeEq, hprevTimeEq]
    simpa [γ, δ, K] using hadj
  have h4γ : 4 * γ ≤ γ ^ 2 := by
    calc
      4 * γ = γ * 4 := by ring
      _ ≤ γ * γ := mul_le_mul_of_nonneg_left hγfour (by positivity : 0 ≤ γ)
      _ = γ ^ 2 := by ring
  have hγsq : γ + 1 ≤ γ ^ 2 := by
    calc
      γ + 1 ≤ 4 * γ := by nlinarith only [hγfour]
      _ ≤ γ ^ 2 := h4γ
  have hlogRUpper : Real.log ((T i : ℝ) / (T (i - 1) : ℝ)) ≤ 2 * L := by
    calc
      _ ≤ Real.log (γ + 1) := Real.log_le_log hratioPos hadj'
      _ ≤ Real.log (γ ^ 2) := Real.log_le_log (by positivity) hγsq
      _ = 2 * L := by rw [Real.log_pow]; rfl
  have hApprox := variance_blockMass_log_gap_of hjpos hSmoothedPartitionVarianceInput hβN hLpos hLone hA
    hgLower hgUpper hprevLower hdiff hcurGap hprevGap hs hsep hlogR hlogRUpper
  simpa [β, T, K, i, γ, δ, g] using hApprox


/-- Two-sided bounds compare the variance of a smoothed polymer mass with the renewal-gap ratio. -/
theorem variance_smoothedP2Plane_gapRatio_bounds :
    ∃ C : ℝ, ∀ β : ℝ, 0 < β → ∀ s t : ℕ, s ≤ t → 0 < renewalGap β t →
      renewalGap β s / renewalGap β t - 1 -
          C * (1 + replicaOverlap t - replicaOverlap s) / renewalGap β t ^ 2 ≤
        Var[fun ω => smoothedP2Plane β s t 0 ω; disorderLaw] ∧
      Var[fun ω => smoothedP2Plane β s t 0 ω; disorderLaw] ≤
        renewalGap β s / renewalGap β t - 1 ∧
      (1 ≤ s → 2 * s ≤ t →
        renewalGap β s / renewalGap β t - 1 -
            C * Real.log ((t : ℝ) / s) / renewalGap β t ^ 2 ≤
          Var[fun ω => smoothedP2Plane β s t 0 ω; disorderLaw]) := by
  obtain ⟨C, hSmoothedPartitionVarianceInput⟩ := smoothedP2Plane_secondMoment_renewalGap
  refine ⟨C, fun β hβ s t hst hgap => ?_⟩
  have hmem := Polymer.memLp_smoothedP2Plane β s t 0 2 (by norm_num)
  have hmean : ∫ ω, smoothedP2Plane β s t 0 ω ∂disorderLaw = 1 :=
    Polymer.integral_smoothedP2Plane β s t 0
  have hvar := variance_eq_sub hmem
  have hvar' : Var[fun ω => smoothedP2Plane β s t 0 ω; disorderLaw] =
      (∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw) - 1 := by
    simpa only [Pi.pow_apply, hmean, one_pow] using hvar
  have hsecond := hSmoothedPartitionVarianceInput β hβ s t hst hgap
  refine ⟨?_, ?_, ?_⟩
  · linarith [hvar', hsecond.2.1]
  · linarith [hvar', hsecond.1]
  · intro hs h2s
    linarith [hvar', hsecond.2.2 hs h2s]

/-- The grid-block variance sum differs from the log-log scale by a bounded amount. -/
theorem sum_variance_blockMass_grid_sub_loglog_le (ϑ : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ C ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ᶠ N : ℕ in atTop,
        |(∑ i ∈ Finset.Icc (blockCount N (gridRatio (ε ^ 2) ρ) - 2 * gridBlocks (ε ^ 2) ρ + 1)
              (blockCount N (gridRatio (ε ^ 2) ρ) - ℓ),
            Var[fun ω => blockMass (criticalBeta ϑ N) (blockTime N (gridRatio (ε ^ 2) ρ)) i ω;
              disorderLaw]) - Real.log (Real.log ε⁻¹)| ≤ C := by
  obtain ⟨Cgap, hgap⟩ := renewalGap_criticalBeta_sub_log_bounded |ϑ|
  obtain ⟨C14raw, hSmoothedPartitionVarianceInputRaw⟩ := variance_smoothedP2Plane_gapRatio_bounds
  have hSmoothedPartitionVarianceInput : SmoothedPartitionVarianceBounds C14raw := by
    intro β hβ s t hst hgapT
    have h := hSmoothedPartitionVarianceInputRaw β hβ s t hst hgapT
    exact ⟨h.2.1, h.2.2⟩
  let A := |Cgap| + Real.log 2
  have hAnonneg : 0 ≤ A := by dsimp [A]; positivity
  let ρ₀ := Real.exp (max (2 * A + 4) (Real.log 4))
  have hρ₀ : 1 < ρ₀ := by
    have harg : 0 < max (2 * A + 4) (Real.log 4) := by
      have hleft : 4 ≤ 2 * A + 4 := by linarith
      linarith [le_max_left (2 * A + 4) (Real.log 4)]
    dsimp [ρ₀]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr harg
  have hρ₀four : 4 ≤ ρ₀ := by
    dsimp [ρ₀]
    calc
      4 = Real.exp (Real.log 4) := (Real.exp_log (by norm_num : (0 : ℝ) < 4)).symm
      _ ≤ Real.exp (max (2 * A + 4) (Real.log 4)) :=
        Real.exp_le_exp.mpr (le_max_right _ _)
  have hlogρ₀ : Real.log ρ₀ = max (2 * A + 4) (Real.log 4) := by
    simp [ρ₀]
  have hρ₀large : 2 * A + 4 ≤ Real.log ρ₀ := by
    rw [hlogρ₀]
    exact le_max_left _ _
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ₀ρ ℓ hℓ
  have hρ : 1 < ρ := lt_of_lt_of_le hρ₀ hρ₀ρ
  have hρpos : 0 < ρ := by linarith
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have hlogρlarge : 2 * A + 4 ≤ Real.log ρ := by
    calc
      _ ≤ Real.log ρ₀ := hρ₀large
      _ ≤ Real.log ρ := Real.log_le_log (by linarith) hρ₀ρ
  have hρfour : 4 ≤ ρ := le_trans hρ₀four hρ₀ρ
  let ε₀ := min (ρ⁻¹) (min (Real.exp (-(2 * A + 2)))
    (Real.exp (-((ℓ : ℝ) + 2) * Real.log ρ)))
  have hε₀pos : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hε₀rho : ε₀ ≤ ρ⁻¹ := min_le_left _ _
  have hε₀A : ε₀ ≤ Real.exp (-(2 * A + 2)) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hε₀ell : ε₀ ≤ Real.exp (-((ℓ : ℝ) + 2) * Real.log ρ) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  let B := 2 * (ℓ : ℝ) * Real.log ρ + A
  let D := 48 + 8 * |C14raw|
  refine ⟨2 * D + Real.log 5 + Real.log B, ε₀, hε₀pos, ?_⟩
  intro ε hε hεsmall
  have hεrho : ε < ρ⁻¹ := lt_of_lt_of_le hεsmall hε₀rho
  have hεA : ε < Real.exp (-(2 * A + 2)) := lt_of_lt_of_le hεsmall hε₀A
  have hεell : ε < Real.exp (-((ℓ : ℝ) + 2) * Real.log ρ) :=
    lt_of_lt_of_le hεsmall hε₀ell
  have hε1 : ε < 1 := by
    have hInvLT : ρ⁻¹ < 1 := by simpa [one_div] using (div_lt_one hρpos).2 hρ
    exact lt_trans hεrho hInvLT
  have hyEq : Real.log (ε⁻¹) = -Real.log ε := by
    rw [Real.log_inv]
  have hy : 2 * A + 2 ≤ Real.log (ε⁻¹) := by
    have h := Real.log_lt_log hε hεA
    rw [Real.log_exp] at h
    rw [hyEq]
    linarith
  have hyℓ : ((ℓ : ℝ) + 2) * Real.log ρ ≤ Real.log (ε⁻¹) := by
    have h := Real.log_lt_log hε hεell
    rw [Real.log_exp] at h
    rw [hyEq]
    linarith
  have hεscale : ε ^ 2 ≤ ρ⁻¹ ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hεrho.le
  let δ := ε ^ 2
  let γ := gridRatio δ ρ
  let J := gridBlocks δ ρ
  let L := Real.log γ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hgrid := gridRatio_mem hρ hδ hεscale
  have hγpos : 0 < γ := lt_of_lt_of_le hρpos hgrid.1
  have hlogργ : Real.log ρ ≤ L := Real.log_le_log hρpos (by simpa [γ] using hgrid.1)
  have hlogγρ : L ≤ 2 * Real.log ρ := by
    have h := Real.log_le_log hγpos (by simpa [γ] using hgrid.2)
    simpa [L, Real.log_pow] using h
  have hLlarge : 2 * (|Cgap| + Real.log 2) + 4 ≤ L := le_trans hlogρlarge hlogργ
  have hγfour : 4 ≤ γ := le_trans hρfour (by simpa [γ] using hgrid.1)
  have hLpos : 0 < L := Real.log_pos (lt_of_lt_of_le (by norm_num) hγfour)
  have hvarianceEvent := variance_blockMass_grid_offsets_eventually ϑ ρ ε Cgap C14raw
    hgap hSmoothedPartitionVarianceInput hρ hε hε1 hεscale hLlarge hγfour
  have hgapEvent := criticalGap_grid_offset_bounds ϑ ρ ε Cgap hgap hρ hε hε1 hεscale
  have hgridEvent := blockTime_gridRatio hρ hδ hεscale
  have hgridBounds := gridBlocks_bounds hρ hδ hεscale
  have hlogδ : Real.log δ = 2 * Real.log ε := by
    dsimp [δ]
    rw [Real.log_pow]
    norm_num
  have hlogεneg : Real.log ε < 0 := Real.log_neg hε hε1
  have hyAbs : |Real.log δ| = 2 * Real.log (ε⁻¹) := by
    rw [hlogδ, abs_of_neg]
    · rw [hyEq]
      ring
    · linarith
  have hJlower : Real.log (ε⁻¹) / (2 * Real.log ρ) ≤ (J : ℝ) := by
    have h := hgridBounds.2.1
    rw [hyAbs] at h
    convert h using 1
    field_simp [ne_of_gt hlogρ]
    ring
  have hJupper : (J : ℝ) ≤ Real.log (ε⁻¹) / Real.log ρ := by
    have h := hgridBounds.2.2
    rw [hyAbs] at h
    convert h using 1; field_simp [ne_of_gt hlogρ]
  have h2JlowerL : Real.log (ε⁻¹) ≤ 2 * (J : ℝ) * L := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.log ρ)).mp hJlower
    calc
      _ ≤ (J : ℝ) * (2 * Real.log ρ) := h
      _ = 2 * (J : ℝ) * Real.log ρ := by ring
      _ ≤ 2 * (J : ℝ) * L :=
        mul_le_mul_of_nonneg_left hlogργ (by positivity)
  have h2JupperL : 2 * (J : ℝ) * L ≤ 4 * Real.log (ε⁻¹) := by
    have hJscaled : 2 * (J : ℝ) ≤ 2 * Real.log (ε⁻¹) / Real.log ρ := by
      have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
      have h := mul_le_mul_of_nonneg_left hJupper h2nonneg
      calc
        _ ≤ 2 * (Real.log (ε⁻¹) / Real.log ρ) := h
        _ = 2 * Real.log (ε⁻¹) / Real.log ρ := by rw [← mul_div_assoc]
    have hfirst := mul_le_mul_of_nonneg_right hJscaled (le_of_lt hLpos)
    have hYnonneg : 0 ≤ Real.log (ε⁻¹) := by linarith [hy, hAnonneg]
    have hmul : 2 * Real.log (ε⁻¹) * L ≤ 4 * Real.log (ε⁻¹) * Real.log ρ := by
      calc
        _ ≤ 2 * Real.log (ε⁻¹) * (2 * Real.log ρ) :=
          mul_le_mul_of_nonneg_left hlogγρ (mul_nonneg (by norm_num) hYnonneg)
        _ = 4 * Real.log (ε⁻¹) * Real.log ρ := by ring
    have hsecond : (2 * Real.log (ε⁻¹) / Real.log ρ) * L ≤
        4 * Real.log (ε⁻¹) := by
      calc
        _ = (2 * Real.log (ε⁻¹) * L) / Real.log ρ := by ring
        _ ≤ 4 * Real.log (ε⁻¹) := (div_le_iff₀ hlogρ).2 hmul
    calc
      _ ≤ (2 * Real.log (ε⁻¹) / Real.log ρ) * L := hfirst
      _ ≤ 4 * Real.log (ε⁻¹) := hsecond
  have hYdiv : Real.log (ε⁻¹) / Real.log ρ ≤ 2 * (J : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hJlower (by norm_num : 0 ≤ (2 : ℝ))
    convert h using 1; field_simp [ne_of_gt hlogρ]
  have hell2real : (ℓ : ℝ) + 2 ≤ 2 * (J : ℝ) := by
    have h := (le_div_iff₀ hlogρ).2 hyℓ
    exact h.trans hYdiv
  have hell2 : ℓ + 2 ≤ 2 * J := by exact_mod_cast hell2real
  have hellLt : ℓ < 2 * J := by omega
  filter_upwards [hvarianceEvent, hgapEvent, hgridEvent] with N hvarianceN hgapN hgridN
  have hK : 2 * J < blockCount N γ := by simpa [J, γ, δ] using hgridN.1
  let β := criticalBeta ϑ N
  let K := blockCount N γ
  let T := blockTime N γ
  let g : ℕ → ℝ := fun j => renewalGap β (T (K - j))
  let Voff : ℕ → ℝ := fun j => Var[fun ω => blockMass β T (K - j) ω; disorderLaw]
  have hgapJ (j : ℕ) (hj : j ∈ Finset.Icc 1 (2 * J)) :
      |g j - (j : ℝ) * L| ≤ A := by
    have h := hgapN j (by simpa [J, δ] using hj)
    simpa [g, β, T, K, A, L, γ, δ] using h
  have hgapPos (j : ℕ) (hj : j ∈ Finset.Icc ℓ (2 * J)) : 0 < g j := by
    have hj' := Finset.mem_Icc.mp hj
    have hj1 : 1 ≤ j := le_trans hℓ hj'.1
    have hMem : j ∈ Finset.Icc 1 (2 * J) := Finset.mem_Icc.mpr ⟨hj1, hj'.2⟩
    have hAbs := abs_le.mp (hgapJ j hMem)
    have hLbase : 2 * A + 4 ≤ L := by simpa [A] using hLlarge
    have hjR : 1 ≤ (j : ℝ) := by exact_mod_cast hj1
    have hjL : L ≤ (j : ℝ) * L := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hjR hLpos.le
    linarith only [hAbs.1, hLbase, hjL, hAnonneg]
  let B := 2 * (ℓ : ℝ) * Real.log ρ + A
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hGellAbs : |g ℓ - (ℓ : ℝ) * L| ≤ A :=
    hgapJ ℓ (Finset.mem_Icc.mpr ⟨hℓ, by omega⟩)
  have hG2Abs : |g (2 * J) - (2 * (J : ℝ)) * L| ≤ A := by
    simpa using hgapJ (2 * J) (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hGellAbs' := abs_le.mp hGellAbs
  have hGellLower : (ℓ : ℝ) * L - A ≤ g ℓ := by linarith [hGellAbs'.1]
  have hGellUpper : g ℓ ≤ (ℓ : ℝ) * L + A := by linarith [hGellAbs'.2]
  have hG2Lower : Real.log (ε⁻¹) - A ≤ g (2 * J) := by
    have h := (abs_le.mp hG2Abs).1
    linarith [h2JlowerL]
  have hG2Upper : g (2 * J) ≤ 4 * Real.log (ε⁻¹) + A := by
    have h := (abs_le.mp hG2Abs).2
    linarith [h2JupperL]
  have hYpos : 0 < Real.log (ε⁻¹) := by linarith [hy]
  have hG2pos : 0 < g (2 * J) := by linarith [hG2Lower, hy]
  have hAhalf : A ≤ Real.log (ε⁻¹) / 2 := by linarith [hy]
  have hG2gehalf : Real.log (ε⁻¹) / 2 ≤ g (2 * J) := by linarith [hG2Lower, hAhalf]
  have hG2ratioLower : (1 : ℝ) / 2 ≤ g (2 * J) / Real.log (ε⁻¹) := by
    apply (le_div_iff₀ hYpos).2
    calc
      (1 / 2 : ℝ) * Real.log (ε⁻¹) = Real.log (ε⁻¹) / 2 := by ring
      _ ≤ g (2 * J) := hG2gehalf
  have hAtoY : A ≤ Real.log (ε⁻¹) := by linarith [hy, hAnonneg]
  have hG2mul5 : g (2 * J) ≤ 5 * Real.log (ε⁻¹) := by
    linarith [hG2Upper, hAtoY]
  have hG2ratioUpper : g (2 * J) / Real.log (ε⁻¹) ≤ 5 := by
    apply (div_le_iff₀ hYpos).2
    exact hG2mul5
  have hlogG2ratio : |Real.log (g (2 * J) / Real.log (ε⁻¹))| ≤ Real.log 5 := by
    have hratioPos : 0 < g (2 * J) / Real.log (ε⁻¹) := div_pos hG2pos hYpos
    have hlogLower : Real.log (1 / 2) ≤
        Real.log (g (2 * J) / Real.log (ε⁻¹)) :=
      Real.log_le_log (by norm_num) hG2ratioLower
    have hlogUpper : Real.log (g (2 * J) / Real.log (ε⁻¹)) ≤ Real.log 5 :=
      Real.log_le_log hratioPos hG2ratioUpper
    have hloghalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.log_inv]
    have hlog25 : Real.log 2 ≤ Real.log 5 :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [abs_le]
    constructor
    · calc
        -Real.log 5 ≤ -Real.log 2 := by linarith [hlog25]
        _ = Real.log (1 / 2) := hloghalf.symm
        _ ≤ Real.log (g (2 * J) / Real.log (ε⁻¹)) := hlogLower
    · exact hlogUpper
  have hGellLowerOne : 1 ≤ g ℓ := by
    have hℓR : 1 ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    have hLminus : 4 ≤ L - A := by linarith [hLlarge, hAnonneg]
    have hscaled : L ≤ (ℓ : ℝ) * L := by
      simpa using mul_le_mul_of_nonneg_right hℓR (le_of_lt hLpos)
    have hlow : 1 ≤ (ℓ : ℝ) * L - A := by linarith [hLminus, hscaled]
    exact le_trans hlow hGellLower
  have hGellUpperB : g ℓ ≤ B := by
    have hℓR : 0 ≤ (ℓ : ℝ) := by positivity
    have hscaled : (ℓ : ℝ) * L ≤ (ℓ : ℝ) * (2 * Real.log ρ) :=
      mul_le_mul_of_nonneg_left hlogγρ hℓR
    dsimp [B]
    linarith [hGellUpper, hscaled]
  have hlogGell : 0 ≤ Real.log (g ℓ) ∧ Real.log (g ℓ) ≤ Real.log B := by
    constructor
    · exact Real.log_nonneg (by linarith [hGellLowerOne])
    · exact Real.log_le_log (by linarith [hGellLowerOne]) hGellUpperB
  have hlogEndpoint :
      |Real.log (g (2 * J) / g ℓ) - Real.log (Real.log ε⁻¹)| ≤
        Real.log 5 + Real.log B := by
    have hid : Real.log (g (2 * J) / g ℓ) - Real.log (Real.log ε⁻¹) =
        Real.log (g (2 * J) / Real.log (ε⁻¹)) - Real.log (g ℓ) := by
      have hgℓpos : 0 < g ℓ := lt_of_lt_of_le (by norm_num) hGellLowerOne
      rw [Real.log_div hG2pos.ne' hgℓpos.ne',
        Real.log_div hG2pos.ne' hYpos.ne']
      ring
    rw [hid]
    calc
      _ ≤ |Real.log (g (2 * J) / Real.log (ε⁻¹))| + |Real.log (g ℓ)| := by
        simpa using abs_sub_le (Real.log (g (2 * J) / Real.log (ε⁻¹))) 0
          (Real.log (g ℓ))
      _ = |Real.log (g (2 * J) / Real.log (ε⁻¹))| + |Real.log (g ℓ)| := by simp
      _ ≤ Real.log 5 + Real.log B := by
        rw [abs_of_nonneg hlogGell.1]
        exact add_le_add hlogG2ratio hlogGell.2
  have hGpos : ∀ j ∈ Finset.Icc ℓ (2 * J), 0 < g j := by
    intro j hj
    exact hgapPos j hj
  have hlogSum := sum_log_gap_ratio_forward_Icc hellLt g hGpos
  have hsumReverse :
      (∑ i ∈ Finset.Icc (K - 2 * J + 1) (K - ℓ),
        Var[fun ω => blockMass β T i ω; disorderLaw]) =
        ∑ j ∈ Finset.Icc ℓ (2 * J - 1), Voff j := by
    have hlow : K - 2 * J + 1 = K - (2 * J - 1) := by omega
    rw [hlow]
    calc
      _ = ∑ i ∈ Finset.Icc (K - (2 * J - 1)) (K - ℓ), Voff (K - i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiK : i ≤ K := by
          have hi' := Finset.mem_Icc.mp hi
          omega
        dsimp [Voff]
        have hKsub : K - (K - i) = i := by omega
        rw [hKsub]
      _ = ∑ j ∈ Finset.Icc ℓ (2 * J - 1), Voff j :=
        sum_reverse_Icc (K := K) (a := ℓ) (b := 2 * J - 1)
          (by omega) (by omega) Voff
  have hsumErr :
      |∑ j ∈ Finset.Icc ℓ (2 * J - 1),
          (Voff j - Real.log (g (j + 1) / g j))| ≤ 2 * D := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc ℓ (2 * J - 1),
          |Voff j - Real.log (g (j + 1) / g j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.Icc ℓ (2 * J - 1), D / (j : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Icc.mp hj
        have hjOne : 1 ≤ j := le_trans hℓ hj'.1
        have hjVar : j ∈ Finset.Icc 1 (2 * J - 1) :=
          Finset.mem_Icc.mpr ⟨hjOne, hj'.2⟩
        have h := hvarianceN j (by simpa [J, δ] using hjVar)
        simpa [Voff, D, β, T, K, γ, δ] using h
      _ = D * ∑ j ∈ Finset.Icc ℓ (2 * J - 1), ((j : ℝ)⁻¹) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjOne : 1 ≤ j := le_trans hℓ (Finset.mem_Icc.mp hj).1
        have hjposNat : 0 < j := lt_of_lt_of_le Nat.zero_lt_one hjOne
        have hjposR : 0 < (j : ℝ) := by exact_mod_cast hjposNat
        field_simp [ne_of_gt hjposR]
      _ ≤ 2 * D := by
        have hD : 0 ≤ D := by dsimp [D]; positivity
        exact scaled_sum_inv_nat_sq_interval_le_two (m := ℓ) (U := 2 * J - 1)
          hℓ D hD
  have hvarianceMinusLogEndpoint :
      |(∑ j ∈ Finset.Icc ℓ (2 * J - 1), Voff j) -
          Real.log (g (2 * J) / g ℓ)| ≤ 2 * D := by
    have hsumId :
        (∑ j ∈ Finset.Icc ℓ (2 * J - 1), Voff j) -
            Real.log (g (2 * J) / g ℓ) =
          ∑ j ∈ Finset.Icc ℓ (2 * J - 1),
            (Voff j - Real.log (g (j + 1) / g j)) := by
      rw [← hlogSum, Finset.sum_sub_distrib]
    rw [hsumId]
    exact hsumErr
  have hfinal :
      |(∑ j ∈ Finset.Icc ℓ (2 * J - 1), Voff j) - Real.log (Real.log ε⁻¹)| ≤
        2 * D + Real.log 5 + Real.log B := by
    calc
      _ ≤ |(∑ j ∈ Finset.Icc ℓ (2 * J - 1), Voff j) -
            Real.log (g (2 * J) / g ℓ)| +
          |Real.log (g (2 * J) / g ℓ) - Real.log (Real.log ε⁻¹)| :=
        abs_sub_le _ _ _
      _ ≤ 2 * D + (Real.log 5 + Real.log B) :=
        add_le_add hvarianceMinusLogEndpoint hlogEndpoint
      _ = 2 * D + Real.log 5 + Real.log B := by ring
  rw [hsumReverse]
  simpa [D, B, β, T, K, J, γ, δ] using hfinal


end Critical2DKPZ.LogNormality

end
