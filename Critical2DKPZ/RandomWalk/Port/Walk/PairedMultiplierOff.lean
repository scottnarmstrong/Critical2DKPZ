/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib
public import Critical2DKPZ.RandomWalk.Port.Walk.PairedFourier

/-!
# The paired Fourier multiplier off the Gaussian region

Off the Gaussian region of the torus, where one coordinate of `θ` is within `π/2` of `0` and
another is not, `|φ(θ)| ≤ 1 - 1/d`; where every coordinate is within `π/2` of `±π`,
`φ ≤ 0`, `|φ(θ)| ≤ e^{-2|ψ|²/(π²d)}` and `0 ≤ 1 + φ(θ) ≤ |ψ|²/(2d)` with
`ψᵢ = π - |θᵢ|`, so the factor `1 + φ` of the paired multiplier vanishes at the antipode.
Together these give the majorant `offBound` of `φⁿ(1 + φ)` (`abs_charFn_pow_mul_le_offBound`).
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace LatticeProb.LocalCLT

open ContinuousTime

variable {d : ℕ}

/-- The majorant of the paired Fourier multiplier `φⁿ(1 + φ)` off the Gaussian region:
`2(1 - 1/d)ⁿ` where some coordinate is inner and some outer, plus, where every coordinate is
outer, `∑ⱼ ψⱼ²/(2d) ∏ᵢ e^{-2nψᵢ²/(π²d)}` with `ψᵢ = π - |θᵢ|`. -/
def offBound (d n : ℕ) (θ : Fin d → ℝ) : ℝ :=
  2 * (1 - 1 / (d : ℝ)) ^ n
    + ∑ j, (Real.pi - |θ j|) ^ 2 / (2 * d)
      * ∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
          (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2)) (θ i)

/-- Where some coordinate of `θ` is within `π/2` of `0` and another is not,
`|φ(θ)| ≤ 1 - 1/d`. -/
theorem abs_charFn_le_of_mixed (hd : 1 ≤ d) {θ : Fin d → ℝ} (hT : θ ∈ torusBox d)
    {i j : Fin d}
    (hi : |θ i| ≤ Real.pi / 2) (hj : Real.pi / 2 < |θ j|) :
    |charFn d θ| ≤ 1 - 1 / (d : ℝ) := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hTabs : ∀ k, |θ k| ≤ Real.pi := by
    intro k
    have hk := Set.mem_Icc.mp hT
    exact abs_le.mpr ⟨by linarith [hk.1 k], by linarith [hk.2 k]⟩
  have hcos_j : Real.cos (θ j) ≤ 0 := by
    have h2 : |θ j| ≤ Real.pi + Real.pi / 2 := by linarith [hTabs j]
    have h3 : Real.cos |θ j| ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hj.le h2
    rwa [Real.cos_abs] at h3
  have hcos_i : 0 ≤ Real.cos (θ i) := Real.cos_nonneg_of_mem_Icc (abs_le.mp hi)
  have hupper : ∑ k, Real.cos (θ k) ≤ (d : ℝ) - 1 := by
    rw [← Finset.sum_erase_add Finset.univ (fun k => Real.cos (θ k)) (Finset.mem_univ j)]
    have h1 : ∑ k ∈ Finset.univ.erase j, Real.cos (θ k) ≤ (d : ℝ) - 1 := by
      calc ∑ k ∈ Finset.univ.erase j, Real.cos (θ k)
            ≤ ∑ _k ∈ Finset.univ.erase j, (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => Real.cos_le_one (θ k))
        _ = (d : ℝ) - 1 := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hd]
            simp
    linarith
  have hlow : -((d : ℝ) - 1) ≤ ∑ k, Real.cos (θ k) := by
    rw [← Finset.sum_erase_add Finset.univ (fun k => Real.cos (θ k)) (Finset.mem_univ i)]
    have h1 : -((d : ℝ) - 1) ≤ ∑ k ∈ Finset.univ.erase i, Real.cos (θ k) := by
      calc -((d : ℝ) - 1) = ∑ _k ∈ Finset.univ.erase i, (-1 : ℝ) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hd]
            ring
        _ ≤ ∑ k ∈ Finset.univ.erase i, Real.cos (θ k) :=
            Finset.sum_le_sum (fun k _ => Real.neg_one_le_cos (θ k))
    linarith
  have habs : |∑ k, Real.cos (θ k)| ≤ (d : ℝ) - 1 := abs_le.mpr ⟨hlow, hupper⟩
  rw [charFn, abs_div, abs_of_pos hdpos, div_le_iff₀ hdpos]
  have hcalc : (1 - 1 / (d : ℝ)) * (d : ℝ) = (d : ℝ) - 1 := by field_simp
  rw [hcalc]
  exact habs

/-- Where every coordinate of `θ` is within `π/2` of `±π`, the paired multiplier is at most
`|ψ|²/(2d) · e^{-2n|ψ|²/(π²d)}`, `ψᵢ = π - |θᵢ|`: the factor `1 + φ` vanishes at the
antipode. -/
theorem abs_charFn_pow_mul_le_of_outer (hd : 1 ≤ d) {θ : Fin d → ℝ} (hT : θ ∈ torusBox d)
    (hout : ∀ i, Real.pi / 2 < |θ i|) (n : ℕ) :
    |charFn d θ ^ n * (1 + charFn d θ)|
      ≤ (∑ i, (Real.pi - |θ i|) ^ 2) / (2 * d)
        * Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * ∑ i, (Real.pi - |θ i|) ^ 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  rw [torusBox, Set.mem_Icc, Pi.le_def, Pi.le_def] at hT
  have habs : ∀ i, |θ i| ≤ Real.pi := fun i => abs_le.mpr ⟨hT.1 i, hT.2 i⟩
  have hpsi0 : ∀ i, 0 ≤ Real.pi - |θ i| := fun i => by linarith [habs i]
  have hpsi_le : ∀ i, Real.pi - |θ i| ≤ Real.pi / 2 := fun i => by linarith [hout i]
  have hcos_psi_nonneg : ∀ i, 0 ≤ Real.cos (Real.pi - |θ i|) := fun i =>
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hpsi0 i, Real.pi_pos]) (hpsi_le i)
  have hcos_le : ∀ i,
      Real.cos (Real.pi - |θ i|) ≤ 1 - 2 / Real.pi ^ 2 * (Real.pi - |θ i|) ^ 2 := fun i =>
    Real.cos_le_one_sub_mul_cos_sq (by
      rw [abs_of_nonneg (hpsi0 i)]
      linarith [hpsi_le i, Real.pi_pos])
  have hcos : ∀ i, Real.cos (θ i) = -Real.cos (Real.pi - |θ i|) := by
    intro i
    rw [(Real.cos_abs (θ i)).symm]
    conv_lhs => rw [show |θ i| = Real.pi - (Real.pi - |θ i|) by ring]
    rw [Real.cos_pi_sub]
  have hcharFn : charFn d θ = -((∑ i, Real.cos (Real.pi - |θ i|)) / d) := by
    rw [charFn]
    simp only [hcos]
    rw [Finset.sum_neg_distrib, neg_div]
  set S : ℝ := ∑ i, (Real.pi - |θ i|) ^ 2 with hS
  set c : ℝ := 2 / (Real.pi ^ 2 * d) with hc
  have hS_nonneg : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsum_le : (∑ i, Real.cos (Real.pi - |θ i|)) ≤ (d : ℝ) - 2 / Real.pi ^ 2 * S := by
    calc ∑ i, Real.cos (Real.pi - |θ i|)
        ≤ ∑ i, (1 - 2 / Real.pi ^ 2 * (Real.pi - |θ i|) ^ 2) :=
          Finset.sum_le_sum (fun i _ => hcos_le i)
      _ = (d : ℝ) - 2 / Real.pi ^ 2 * S := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one, ← Finset.mul_sum, ← hS]
  have hdiv_le : (∑ i, Real.cos (Real.pi - |θ i|)) / d ≤ 1 - c * S := by
    rw [div_le_iff₀ hd0]
    have hmul : (1 - c * S) * d = (d : ℝ) - 2 / Real.pi ^ 2 * S := by
      rw [sub_mul, one_mul, hc]
      field_simp
    rw [hmul]
    exact hsum_le
  have hsum_cos_nonneg : 0 ≤ ∑ i, Real.cos (Real.pi - |θ i|) :=
    Finset.sum_nonneg (fun i _ => hcos_psi_nonneg i)
  have hcharFn_abs : |charFn d θ| = (∑ i, Real.cos (Real.pi - |θ i|)) / d := by
    rw [hcharFn, abs_neg, abs_of_nonneg (div_nonneg hsum_cos_nonneg hd0.le)]
  have habs_pow : |charFn d θ| ^ n ≤ Real.exp (-c * n * S) := by
    have hbase : |charFn d θ| ≤ Real.exp (-c * S) := by
      calc |charFn d θ| = (∑ i, Real.cos (Real.pi - |θ i|)) / d := hcharFn_abs
        _ ≤ 1 - c * S := hdiv_le
        _ ≤ Real.exp (-c * S) := by
            simpa [neg_mul] using Real.one_sub_le_exp_neg (c * S)
    calc |charFn d θ| ^ n ≤ Real.exp (-c * S) ^ n :=
          pow_le_pow_left₀ (abs_nonneg _) hbase n
      _ = Real.exp (-c * n * S) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hone_add : 1 + charFn d θ = (∑ i, (1 - Real.cos (Real.pi - |θ i|))) / d := by
    rw [hcharFn]
    rw [show (1 : ℝ) + -((∑ i, Real.cos (Real.pi - |θ i|)) / d)
        = ((d : ℝ) - ∑ i, Real.cos (Real.pi - |θ i|)) / d by
      field_simp
      ring]
    rw [show (d : ℝ) = ∑ _i : Fin d, (1 : ℝ) by simp]
    rw [← Finset.sum_sub_distrib]
  have hone_nonneg : 0 ≤ 1 + charFn d θ := by
    rw [hone_add]
    exact div_nonneg
      (Finset.sum_nonneg (fun i _ => by linarith [Real.cos_le_one (Real.pi - |θ i|)])) hd0.le
  have hone_le : 1 + charFn d θ ≤ S / (2 * d) := by
    rw [hone_add]
    have hsum_one_le : (∑ i, (1 - Real.cos (Real.pi - |θ i|))) ≤ S / 2 := by
      calc ∑ i, (1 - Real.cos (Real.pi - |θ i|))
          ≤ ∑ i, (Real.pi - |θ i|) ^ 2 / 2 :=
            Finset.sum_le_sum (fun i _ => by
              linarith [Real.one_sub_sq_div_two_le_cos (x := Real.pi - |θ i|)])
        _ = S / 2 := by rw [← Finset.sum_div, ← hS]
    calc (∑ i, (1 - Real.cos (Real.pi - |θ i|))) / d
        ≤ (S / 2) / d := div_le_div_of_nonneg_right hsum_one_le hd0.le
      _ = S / (2 * d) := by ring
  calc |charFn d θ ^ n * (1 + charFn d θ)|
      = |charFn d θ| ^ n * (1 + charFn d θ) := by
          rw [abs_mul, abs_pow, abs_of_nonneg hone_nonneg]
    _ ≤ Real.exp (-c * n * S) * (S / (2 * d)) :=
          mul_le_mul habs_pow hone_le hone_nonneg (Real.exp_pos _).le
    _ = S / (2 * d) * Real.exp (-c * n * S) := by ring

/-- Off the Gaussian region the paired multiplier is at most `offBound`. -/
theorem abs_charFn_pow_mul_le_offBound (hd : 1 ≤ d) {θ : Fin d → ℝ} (hT : θ ∈ torusBox d)
    (hG : θ ∉ gaussRegion d) (n : ℕ) :
    |charFn d θ ^ n * (1 + charFn d θ)| ≤ offBound d n θ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hbase_nn : 0 ≤ 1 - 1 / (d : ℝ) := by
    rw [sub_nonneg, div_le_one₀ hd0]
    exact_mod_cast hd
  have houter : ∃ j, Real.pi / 2 < |θ j| := by
    by_contra h
    apply hG
    rw [gaussRegion, Set.mem_ofPred_eq]
    intro i
    exact le_of_not_gt (fun hi => h ⟨i, hi⟩)
  obtain ⟨j0, hj0⟩ := houter
  by_cases hall : ∀ i, Real.pi / 2 < |θ i|
  · have hle := abs_charFn_pow_mul_le_of_outer hd hT hall n
    have hoff_eq : offBound d n θ = 2 * (1 - 1 / (d : ℝ)) ^ n
        + (∑ i, (Real.pi - |θ i|) ^ 2) / (2 * d)
          * Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * ∑ i, (Real.pi - |θ i|) ^ 2) := by
      rw [offBound]
      congr 1
      have hprod : ∀ j : Fin d,
          (∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
              (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2))
              (θ i))
            = Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * ∑ i, (Real.pi - |θ i|) ^ 2) := by
        intro j
        have hprod' : (∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
              (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2))
              (θ i))
            = ∏ i, Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |θ i|) ^ 2) := by
          apply Finset.prod_congr rfl
          intro i _
          have hmem : θ i ∈ {t : ℝ | Real.pi / 2 < |t|} := hall i
          rw [Set.indicator_of_mem hmem]
        rw [hprod', ← Real.exp_sum]
        congr 1
        rw [← Finset.mul_sum]
      calc ∑ j, (Real.pi - |θ j|) ^ 2 / (2 * d)
            * (∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
                (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2))
                (θ i))
          = ∑ j, (Real.pi - |θ j|) ^ 2 / (2 * d)
              * Real.exp (-(2 / (Real.pi ^ 2 * d)) * n
                  * ∑ i, (Real.pi - |θ i|) ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hprod j]
        _ = (∑ i, (Real.pi - |θ i|) ^ 2) / (2 * d)
              * Real.exp (-(2 / (Real.pi ^ 2 * d)) * n
                  * ∑ i, (Real.pi - |θ i|) ^ 2) := by
            rw [← Finset.sum_mul, ← Finset.sum_div]
    rw [hoff_eq]
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg (by norm_num) (pow_nonneg hbase_nn n)))
  · simp only [not_forall, not_lt] at hall
    obtain ⟨i0, hi0⟩ := hall
    have hmixed := abs_charFn_le_of_mixed hd hT hi0 hj0
    have hpow : |charFn d θ| ^ n ≤ (1 - 1 / (d : ℝ)) ^ n :=
      pow_le_pow_left₀ (abs_nonneg _) hmixed n
    have hcharFn_le_one : |charFn d θ| ≤ 1 := by
      rw [charFn, abs_div, abs_of_pos hd0, div_le_one₀ hd0]
      calc |∑ i, Real.cos (θ i)| ≤ ∑ i, |Real.cos (θ i)| :=
            Finset.abs_sum_le_sum_abs (fun i => Real.cos (θ i)) Finset.univ
        _ ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum (fun i _ => Real.abs_cos_le_one (θ i))
        _ = d := by simp
    have h1phi : |1 + charFn d θ| ≤ 2 := by
      calc |1 + charFn d θ| ≤ |(1 : ℝ)| + |charFn d θ| := abs_add_le _ _
        _ = 1 + |charFn d θ| := by rw [abs_one]
        _ ≤ 2 := by linarith [hcharFn_le_one]
    rw [abs_mul, abs_pow]
    calc |charFn d θ| ^ n * |1 + charFn d θ|
        ≤ (1 - 1 / (d : ℝ)) ^ n * 2 :=
          mul_le_mul hpow h1phi (abs_nonneg _) (pow_nonneg hbase_nn n)
      _ = 2 * (1 - 1 / (d : ℝ)) ^ n := by ring
      _ ≤ offBound d n θ := by
          rw [offBound]
          have hsd : 0 ≤ ∑ j, (Real.pi - |θ j|) ^ 2 / (2 * d)
              * (∏ i, Set.indicator {t : ℝ | Real.pi / 2 < |t|}
                  (fun t => Real.exp (-(2 / (Real.pi ^ 2 * d)) * n * (Real.pi - |t|) ^ 2))
                  (θ i)) := by
            apply Finset.sum_nonneg
            intro j _
            apply mul_nonneg
            · positivity
            · apply Finset.prod_nonneg
              intro i _
              by_cases h : Real.pi / 2 < |θ i|
              · have hmem : θ i ∈ {t : ℝ | Real.pi / 2 < |t|} := h
                rw [Set.indicator_of_mem hmem]
                exact (Real.exp_pos _).le
              · have hmem : θ i ∉ {t : ℝ | Real.pi / 2 < |t|} := h
                rw [Set.indicator_of_notMem hmem]
          linarith

end LatticeProb.LocalCLT

end
