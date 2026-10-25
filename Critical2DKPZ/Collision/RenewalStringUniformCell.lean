/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.RenewalStringCells
public import Critical2DKPZ.Polymer.SummableCovariance
import Mathlib.Tactic
import Critical2DKPZ.SHF.DeltaBose.Measurability

/-!
# Uniform renewal pair-cell comparisons

Finite exceptional scales are controlled absolutely; the large-scale estimate
comes from the logarithmic renewal bounds.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Collision

/-- On a compact critical-parameter interval, every admissible finite-scale
coupling has a fixed absolute bound. -/
theorem abs_criticalSigmaSq_le_compact (A : ℝ) (hA : 0 ≤ A) {N : ℕ}
    (hN : 1 ≤ N) {ϑ : ℝ} (hϑ : ϑ ∈ Set.Icc (-A) A) :
    |criticalSigmaSq ϑ N| ≤ (1 + A / Real.log 2) / srwKernel 2 0 := by
  have hq : 0 < srwKernel 2 0 := srwKernel_two_zero_pos
  have hRpos : 0 < replicaOverlap N := replicaOverlap_pos hN
  have hRlower : srwKernel 2 0 ≤ replicaOverlap N :=
    Finset.single_le_sum (f := fun n : ℕ => srwKernel (2 * n) 0)
      (fun n hn => srwKernel_nonneg (2 * n) 0)
      (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩)
  have hAabs : |ϑ| ≤ A := abs_le.mpr ⟨by linarith [hϑ.1], hϑ.2⟩
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  by_cases hN1 : N = 1
  · subst N
    have hRone : replicaOverlap 1 = srwKernel 2 0 := by
      simp [replicaOverlap]
    rw [show criticalSigmaSq ϑ 1 = (1 : ℝ) / replicaOverlap 1 by
      unfold criticalSigmaSq
      simp [Real.log_one]]
    rw [hRone, abs_of_pos (div_pos (by norm_num) hq)]
    have hM : 1 ≤ 1 + A / Real.log 2 := by
      simpa [add_comm] using add_le_add_left (div_nonneg hA hlog2.le) 1
    exact div_le_div_of_nonneg_right hM hq.le
  · have hN2 : 2 ≤ N := by omega
    have hlogN : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlog2le : Real.log 2 ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN2)
    have hinv : (Real.log (N : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ :=
      (inv_le_inv₀ hlogN hlog2).2 hlog2le
    have hparam : |1 + ϑ / Real.log N| ≤ 1 + A / Real.log 2 := by
      calc
        |1 + ϑ / Real.log N| ≤ |(1 : ℝ)| + |ϑ / Real.log N| := abs_add_le _ _
        _ = 1 + |ϑ| * (Real.log N)⁻¹ := by
          rw [abs_one, abs_div, abs_of_pos hlogN]
          ring
        _ ≤ 1 + A * (Real.log 2)⁻¹ := by
          gcongr
        _ = 1 + A / Real.log 2 := by rw [div_eq_mul_inv]
    have hsigma : |criticalSigmaSq ϑ N| =
        |1 + ϑ / Real.log N| / replicaOverlap N := by
      unfold criticalSigmaSq
      rw [abs_div, abs_of_pos hRpos]
    calc
      |criticalSigmaSq ϑ N| ≤ (1 + A / Real.log 2) / replicaOverlap N := by
        rw [hsigma]
        exact div_le_div_of_nonneg_right hparam hRpos.le
      _ ≤ (1 + A / Real.log 2) / srwKernel 2 0 := by
        have hM : 0 ≤ 1 + A / Real.log 2 := by positivity
        have hinvR : (replicaOverlap N)⁻¹ ≤ (srwKernel 2 0)⁻¹ :=
          (inv_le_inv₀ hRpos hq).2 hRlower
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hinvR hM

/-- A crude absolute bound for a finite renewal mass from a uniform kernel bound. -/
theorem abs_renewalMass_le_pow_of_kernel_bound {w : ℕ → ℝ} {S : ℝ}
    (hS : 0 ≤ S) (hw : ∀ r, |w r| ≤ S) (M n : ℕ) (hn : n ≤ M) :
    |Renewal.renewalMass w n| ≤ ((M + 1 : ℕ) * (1 + S)) ^ n := by
  let B : ℝ := ((M + 1 : ℕ) : ℝ) * (1 + S)
  have hB : 1 ≤ B := by
    dsimp [B]
    have hM : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le M))
    have hprod := mul_nonneg (sub_nonneg.mpr hM) hS
    nlinarith
  have hcoeff : ((M + 1 : ℕ) : ℝ) * S ≤ B := by dsimp [B]; nlinarith
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [Renewal.renewalMass_zero]
      | succ n =>
          have hnM : n + 1 ≤ M := by omega
          rw [Renewal.renewalMass_succ]
          have hterm (r : ℕ) (hr : r ∈ Finset.Icc 1 (n + 1)) :
              |w r * Renewal.renewalMass w (n + 1 - r)| ≤ S * B ^ n := by
            have hrpow : n + 1 - r ≤ n := by
              have := (Finset.mem_Icc.mp hr).1
              omega
            calc
              |w r * Renewal.renewalMass w (n + 1 - r)| =
                  |w r| * |Renewal.renewalMass w (n + 1 - r)| := abs_mul _ _
              _ ≤ S * B ^ (n + 1 - r) := mul_le_mul (hw r)
                  (ih (n + 1 - r) (by omega) (by omega)) (abs_nonneg _) hS
              _ ≤ S * B ^ n := mul_le_mul_of_nonneg_left
                  (pow_le_pow_right₀ hB hrpow) hS
          have hBnonneg : 0 ≤ B := by linarith
          have hcard : ((Finset.Icc 1 (n + 1)).card : ℝ) ≤ M + 1 := by
            have hnat : (Finset.Icc 1 (n + 1)).card = n + 1 := by
              simp [Nat.card_Icc]
            rw [hnat]
            exact_mod_cast (show n + 1 ≤ M + 1 by omega)
          calc
            |∑ r ∈ Finset.Icc 1 (n + 1),
                w r * Renewal.renewalMass w (n + 1 - r)| ≤
                ∑ r ∈ Finset.Icc 1 (n + 1),
                  |w r * Renewal.renewalMass w (n + 1 - r)| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r ∈ Finset.Icc 1 (n + 1), S * B ^ n :=
              Finset.sum_le_sum fun r hr => hterm r hr
            _ = ((Finset.Icc 1 (n + 1)).card : ℝ) * (S * B ^ n) := by
              simp [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (M + 1) * (S * B ^ n) :=
              mul_le_mul_of_nonneg_right hcard (mul_nonneg hS (pow_nonneg hBnonneg _))
            _ = ((M + 1 : ℕ) : ℝ) * S * B ^ n := by push_cast; ring
            _ ≤ B * B ^ n := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hBnonneg _)
            _ = B ^ (n + 1) := by rw [pow_succ]; ring

/-- The critical renewal mass is uniformly bounded in absolute value on bounded scales, including parameters with negative coupling. -/
theorem abs_criticalRenewalMass_le_finite_range (A : ℝ) (hA : 0 ≤ A)
    (M N d : ℕ) (hN : 1 ≤ N) (hdM : d ≤ M)
    (ϑ : ℝ) (hϑ : ϑ ∈ Set.Icc (-A) A) :
    |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d| ≤
      ((1 + A / Real.log 2) / srwKernel 2 0) *
        (((M + 1 : ℕ) : ℝ) *
          (1 + (1 + A / Real.log 2) / srwKernel 2 0)) ^ M := by
  let S : ℝ := (1 + A / Real.log 2) / srwKernel 2 0
  let B : ℝ := ((M + 1 : ℕ) : ℝ) * (1 + S)
  have hq : 0 < srwKernel 2 0 := srwKernel_two_zero_pos
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hSig : |criticalSigmaSq ϑ N| ≤ S := by
    simpa [S] using abs_criticalSigmaSq_le_compact A hA hN hϑ
  have hreturn (r : ℕ) : |Renewal.returnWeight r| ≤ 1 := by
    have hnonneg : 0 ≤ Renewal.returnWeight r := by
      exact srwKernel_nonneg (2 * r) 0
    rw [abs_of_nonneg hnonneg]
    exact Polymer.srwKernel_le_one (2 * r) 0
  have hw (r : ℕ) :
      |criticalSigmaSq ϑ N * Renewal.returnWeight r| ≤ S := by
    calc
      |criticalSigmaSq ϑ N * Renewal.returnWeight r| =
          |criticalSigmaSq ϑ N| * |Renewal.returnWeight r| := abs_mul _ _
      _ ≤ S * 1 := mul_le_mul hSig (hreturn r) (abs_nonneg _) hS
      _ = S := by ring
  have hmass := abs_renewalMass_le_pow_of_kernel_bound hS hw M d hdM
  have hB : 1 ≤ B := by
    dsimp [B]
    have hMc : (1 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le M))
    have hprod := mul_nonneg (sub_nonneg.mpr hMc) hS
    nlinarith
  calc
    |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d| =
        |criticalSigmaSq ϑ N| *
          |Renewal.renewalMass
            (fun r => criticalSigmaSq ϑ N * Renewal.returnWeight r) d| := by
          simp only [Renewal.criticalRenewalMass, abs_mul]
    _ ≤ S * B ^ d := by
      exact mul_le_mul hSig (by simpa [B] using hmass) (abs_nonneg _) hS
    _ ≤ S * B ^ M := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hB (by exact_mod_cast hdM)) hS
    _ = (1 + A / Real.log 2) / srwKernel 2 0 *
        (((M + 1 : ℕ) : ℝ) *
          (1 + (1 + A / Real.log 2) / srwKernel 2 0)) ^ M := by
          simp [S, B]

/-- Lower bound on the diagonal pair-cell `renewalStringPairCell N a a` for `N ≤ M`: if the
scalar density has mass at least `cI / (1 - log h)` on `(0, h)` for each `h ≤ 1`, then its
integral in the difference variable over the cell is at least
`cI / (4 (1 + log (4 M)) N²)`. -/
theorem renewalStringPairCell_diagonal_integral_lower
    (N a M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (θ cI : ℝ) (hcI : 0 < cI)
    (hInt : ∀ h : ℝ, 0 < h → h ≤ 1 →
      ENNReal.ofReal (cI / (1 - Real.log h)) ≤
        ∫⁻ u in Ioo (0 : ℝ) h,
          ENNReal.ofReal (DeltaBose.scalarDensity θ u)) :
    ENNReal.ofReal (cI / (4 * (1 + Real.log (4 * (M : ℝ))) * (N : ℝ) ^ 2)) ≤
      ∫⁻ p in renewalStringPairCell N a a,
        ENNReal.ofReal (DeltaBose.scalarDensity θ (p.2 - p.1)) := by
  let width : ℝ := 1 / (4 * (N : ℝ))
  let l : ℝ := ((a : ℝ) - 1 / 2) / N
  let r : ℝ := ((a : ℝ) - 1 / 4) / N
  let F : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (DeltaBose.scalarDensity θ u)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNge1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hMge1 : (1 : ℝ) ≤ M := by exact_mod_cast (Nat.le_trans hN hNM)
  have hwidth : 0 < width := by dsimp [width]; positivity
  have hwidthle : width ≤ 1 := by
    dsimp [width]
    have hden : (1 : ℝ) ≤ 4 * N := by nlinarith
    exact (div_le_one (by positivity)).2 hden
  have hcell : renewalStringPairCell N a a =
      {p | ((a : ℝ) - 1 / 2) / N < p.1 ∧
        p.1 < ((a : ℝ) - 1 / 4) / N ∧ p.1 < p.2 ∧
        p.2 < p.1 + (1 : ℝ) / (4 * (N : ℝ))} := by
    ext p
    simp [renewalStringPairCell, div_eq_mul_inv]
  have hF : Measurable F := by
    change Measurable (fun u : ℝ => ENNReal.ofReal (DeltaBose.scalarDensity θ u))
    exact (DeltaBose.measurable_scalarDensity.comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have htriangle := lintegral_renewalPair_triangle_eq
    (l := l) (r := r) (h := width) F hF
  have htriangle' :
      (∫⁻ p : ℝ × ℝ in renewalStringPairCell N a a, F (p.2 - p.1)) =
        ENNReal.ofReal width * (∫⁻ u in Ioo (0 : ℝ) width, F u) := by
    rw [hcell]
    convert htriangle using 1
    dsimp [l, r, width]
    congr 1
    ring_nf
  have hsmall := hInt width hwidth hwidthle
  have hwidthEq : width = (4 * (N : ℝ))⁻¹ := by
    dsimp [width]
    field_simp
  have hdenEq : 1 - Real.log width = 1 + Real.log (4 * (N : ℝ)) := by
    rw [hwidthEq, Real.log_inv]
    ring
  have hNMreal : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have h4Nle : 4 * (N : ℝ) ≤ 4 * (M : ℝ) := by
    have hNMreal : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
    nlinarith
  have hlog4Nle : Real.log (4 * (N : ℝ)) ≤ Real.log (4 * (M : ℝ)) :=
    Real.log_le_log (by positivity) h4Nle
  have hLdiag : 0 < 1 + Real.log (4 * (M : ℝ)) := by
    have harg : (1 : ℝ) < 4 * (M : ℝ) := by nlinarith
    linarith [Real.log_pos harg]
  have hdenle : 1 - Real.log width ≤ 1 + Real.log (4 * (M : ℝ)) := by
    rw [hdenEq]
    simpa [add_comm] using add_le_add_left hlog4Nle 1
  have hdenpos : 0 < 1 - Real.log width := by
    have hlogw : Real.log width ≤ 0 := Real.log_nonpos hwidth.le hwidthle
    linarith
  have hdenprod : 4 * (1 - Real.log width) * N ≤
      4 * (1 + Real.log (4 * (M : ℝ))) * (N : ℝ) ^ 2 := by
    have hdenN : (1 - Real.log width) * N ≤
        (1 + Real.log (4 * (M : ℝ))) * N :=
      mul_le_mul_of_nonneg_right hdenle hNpos.le
    have hNsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have hLN : (1 + Real.log (4 * (M : ℝ))) * N ≤
        (1 + Real.log (4 * (M : ℝ))) * (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hNsq hLdiag.le
    nlinarith
  have hdiagReal : cI / (4 * (1 + Real.log (4 * (M : ℝ))) * (N : ℝ) ^ 2) ≤
      width * (cI / (1 - Real.log width)) := by
    have hdencomp := div_le_div_of_nonneg_left hcI.le
      (by positivity : 0 < 4 * (1 - Real.log width) * N) hdenprod
    calc
      cI / (4 * (1 + Real.log (4 * (M : ℝ))) * (N : ℝ) ^ 2) ≤
          cI / (4 * (1 - Real.log width) * N) := by
            exact hdencomp
      _ = width * (cI / (1 - Real.log width)) := by
        dsimp [width]
        field_simp [ne_of_gt hdenpos, ne_of_gt hNpos]
  have hsmallMul := mul_le_mul_of_nonneg_left hsmall
    (by positivity : 0 ≤ ENNReal.ofReal width)
  have hdiagENN : ENNReal.ofReal (width * (cI / (1 - Real.log width))) ≤
      ∫⁻ p : ℝ × ℝ in renewalStringPairCell N a a, F (p.2 - p.1) := by
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ width)]
    calc
      ENNReal.ofReal width * ENNReal.ofReal (cI / (1 - Real.log width)) ≤
          ENNReal.ofReal width * (∫⁻ u in Ioo (0 : ℝ) width, F u) := hsmallMul
      _ = _ := htriangle'.symm
  exact (ENNReal.ofReal_le_ofReal hdiagReal).trans hdiagENN

/-- A uniformly positive lower bound for a separated pair-cell on a finite
range of mesh sizes. -/
theorem renewalStringPairCell_offdiag_integral_lower
    (N a b M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) (ha : 1 ≤ a)
    (hab : a < b) (hbN : b ≤ N) (θ B cDensity : ℝ) (hcDensity : 0 < cDensity)
    (hθ : θ ∈ Set.Icc (-B) B)
    (hDensity : ∀ θ' u : ℝ, θ' ∈ Set.Icc (-B) B → 0 < u → u ≤ 1 →
      cDensity / (u * (1 - Real.log u) ^ 2) ≤ DeltaBose.scalarDensity θ' u) :
    ENNReal.ofReal (cDensity /
      (8 * (1 + (Real.log 2)⁻¹) ^ 2 * (Real.log (1 + (M : ℝ))) ^ 2 *
        (N : ℝ) ^ 2)) ≤
      ∫⁻ p in renewalStringPairCell N a b,
        ENNReal.ofReal (DeltaBose.scalarDensity θ (p.2 - p.1)) := by
  let d : ℕ := b - a
  let Mlog : ℝ := 1 + (Real.log 2)⁻¹
  let L : ℝ := Real.log (1 + (N : ℝ) / d)
  let Lmax : ℝ := Real.log (1 + (M : ℝ))
  let floor : ℝ := cDensity / (2 * Mlog ^ 2 * Lmax ^ 2)
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (DeltaBose.scalarDensity θ (p.2 - p.1))
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdN : d + 1 ≤ N := by dsimp [d]; omega
  have hN2 : 2 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hMgeN : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hMlog : 0 < Mlog := by dsimp [Mlog]; positivity
  have hL : 0 < L := by
    dsimp [L]
    apply Real.log_pos
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    have hratio : 0 < (N : ℝ) / d := div_pos hNpos hdpos
    linarith
  have hLmax : 0 < Lmax := by
    dsimp [Lmax]
    have harg : (1 : ℝ) < 1 + (M : ℝ) := by
      have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
      linarith
    exact Real.log_pos harg
  have hNdiv : (N : ℝ) / d ≤ N := by
    have hdcast : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hNcast : (0 : ℝ) ≤ N := by positivity
    apply (div_le_iff₀ (by exact_mod_cast hd)).2
    nlinarith
  have hNdivM : (N : ℝ) / d ≤ M := hNdiv.trans hMgeN
  have hLupper : L ≤ Lmax := by
    dsimp [L, Lmax]
    apply Real.log_le_log
    · exact add_pos (by norm_num) (div_pos hNpos (by exact_mod_cast (by omega : 0 < d)))
    · simpa [add_comm] using add_le_add_left hNdivM 1
  have hdcast : (d : ℝ) ≤ N := by exact_mod_cast (by omega : d ≤ N)
  have hcore : (d : ℝ) * L ^ 2 ≤ N * Lmax ^ 2 := by
    calc
      (d : ℝ) * L ^ 2 ≤ d * Lmax ^ 2 :=
        mul_le_mul_of_nonneg_left (sq_le_sq₀ hL.le hLmax.le |>.2 hLupper) (by positivity)
      _ ≤ N * Lmax ^ 2 := mul_le_mul_of_nonneg_right hdcast (sq_nonneg Lmax)
  have hpointFloor : floor ≤ cDensity * N /
      (2 * d * Mlog ^ 2 * L ^ 2) := by
    have hdenA : 0 < Mlog ^ 2 * Lmax ^ 2 := by positivity
    have hdenB : 0 < (d : ℝ) * Mlog ^ 2 * L ^ 2 := by positivity
    have hcross : (d : ℝ) * Mlog ^ 2 * L ^ 2 ≤
        N * (Mlog ^ 2 * Lmax ^ 2) := by
      calc
        (d : ℝ) * Mlog ^ 2 * L ^ 2 = Mlog ^ 2 * (d * L ^ 2) := by ring
        _ ≤ Mlog ^ 2 * (N * Lmax ^ 2) :=
          mul_le_mul_of_nonneg_left hcore (sq_nonneg Mlog)
        _ = N * (Mlog ^ 2 * Lmax ^ 2) := by ring
    have hratio : 1 / (Mlog ^ 2 * Lmax ^ 2) ≤
        N / ((d : ℝ) * Mlog ^ 2 * L ^ 2) := by
      apply (div_le_div_iff₀ hdenA hdenB).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcross
    calc
      cDensity / (2 * Mlog ^ 2 * Lmax ^ 2) =
          (cDensity / 2) * (1 / (Mlog ^ 2 * Lmax ^ 2)) := by ring_nf
      _ ≤ (cDensity / 2) * (N / ((d : ℝ) * Mlog ^ 2 * L ^ 2)) :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = cDensity * N / (2 * d * Mlog ^ 2 * L ^ 2) := by ring_nf
  have hcell : renewalStringPairCell N a b =
      Ioo (((a : ℝ) - 1 / 2) / N) ((a : ℝ) / N) ×ˢ
        Ioo ((b : ℝ) / N) (((b : ℝ) + 1 / 2) / N) := by
    ext p
    simp [renewalStringPairCell, ne_of_lt hab, Set.mem_Ioo, and_assoc]
  have hF : Measurable F := by
    have hpair : Measurable (fun p : ℝ × ℝ => (θ, p.2 - p.1)) :=
      measurable_const.prodMk (measurable_snd.sub measurable_fst)
    exact (DeltaBose.measurable_scalarDensity.comp hpair).ennreal_ofReal
  have hpointwise : ∀ p ∈
      Ioo (((a : ℝ) - 1 / 2) / N) ((a : ℝ) / N) ×ˢ
        Ioo ((b : ℝ) / N) (((b : ℝ) + 1 / 2) / N),
      ENNReal.ofReal floor ≤ F p := by
    intro p hp
    have hcellmem : p ∈ renewalStringPairCell N a b := by rw [hcell]; exact hp
    obtain ⟨hlo, hhi, hst, htop, _, hbot⟩ :=
      renewalStringPairCell_bounds N a b (by omega) (Nat.le_of_lt hab) hcellmem
    have hdcast' : (d : ℝ) = (b : ℝ) - a := by
      dsimp [d]
      exact Nat.cast_sub (Nat.le_of_lt hab)
    have hlower : (d : ℝ) / N ≤ p.2 - p.1 := by
      have hbt := hbot hab
      have hdiff : (b : ℝ) / N - (a : ℝ) / N = (d : ℝ) / N := by
        rw [← sub_div, hdcast']
      rw [← hdiff]
      linarith
    have hupper : p.2 - p.1 ≤ ((d + 1 : ℕ) : ℝ) / N := by
      have hdiff : (((b : ℝ) + 1 / 2) / N) -
          (((a : ℝ) - 1 / 2) / N) = ((d + 1 : ℕ) : ℝ) / N := by
        rw [← sub_div]
        rw [show ((b : ℝ) + 1 / 2) - ((a : ℝ) - 1 / 2) =
          ((b : ℝ) - (a : ℝ)) + 1 by ring]
        rw [Nat.cast_add, Nat.cast_one, hdcast']
      linarith
    have hpoint := scalarDensity_lower_on_scaled_gap hcDensity hDensity N d
      hN2 hd hdN hθ (p.2 - p.1) hlower hupper
    have hpointFloor' : floor ≤
        cDensity * N / (2 * d * Mlog ^ 2 * L ^ 2) := by
      simpa [floor, Mlog, L] using hpointFloor
    exact ENNReal.ofReal_le_ofReal (hpointFloor'.trans hpoint)
  have hrect := lintegral_Ioo_prod_lower F (ENNReal.ofReal floor) hpointwise
  have hcellIntegral :
      (∫⁻ p in renewalStringPairCell N a b, F p) =
        ∫⁻ p in Ioo (((a : ℝ) - 1 / 2) / N) ((a : ℝ) / N) ×ˢ
          Ioo ((b : ℝ) / N) (((b : ℝ) + 1 / 2) / N), F p := by rw [hcell]
  have hwidthA : (a : ℝ) / N - ((a : ℝ) - 1 / 2) / N = 1 / (2 * N) := by
    field_simp
    ring
  have hwidthB : ((b : ℝ) + 1 / 2) / N - (b : ℝ) / N = 1 / (2 * N) := by
    field_simp
    ring
  have hrect' : ENNReal.ofReal floor * ENNReal.ofReal (1 / (2 * N)) *
      ENNReal.ofReal (1 / (2 * N)) ≤ ∫⁻ p in renewalStringPairCell N a b, F p := by
    rw [hwidthA, hwidthB] at hrect
    rw [hcellIntegral]
    exact hrect
  have hprod : ENNReal.ofReal (floor / (4 * (N : ℝ) ^ 2)) =
      ENNReal.ofReal floor * ENNReal.ofReal (1 / (2 * N)) *
        ENNReal.ofReal (1 / (2 * N)) := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    calc
      ENNReal.ofReal (floor / (4 * (N : ℝ) ^ 2)) =
          ENNReal.ofReal (floor * (1 / (2 * N)) * (1 / (2 * N))) := by
            congr 1
            field_simp [ne_of_gt hNpos]
            ring
      _ = ENNReal.ofReal (floor * (1 / (2 * N))) * ENNReal.ofReal (1 / (2 * N)) :=
        ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal floor * ENNReal.ofReal (1 / (2 * N)) *
          ENNReal.ofReal (1 / (2 * N)) := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ floor)]
  have hreal : cDensity /
      (8 * Mlog ^ 2 * Lmax ^ 2 * (N : ℝ) ^ 2) = floor / (4 * (N : ℝ) ^ 2) := by
    dsimp [floor]
    field_simp [ne_of_gt hcDensity, ne_of_gt hMlog, ne_of_gt hLmax, ne_of_gt hNpos]
    ring_nf
  rw [hreal, hprod]
  exact hrect'

/-- Uniform finite-scale lower mass for every selected pair-cell.  This uses a
compact-parameter lower envelope for the scalar density and the integrated
logarithmic lower bound on diagonal cells. -/
theorem renewalStringPairCell_integral_floor_finite (A : ℝ) (hA : 0 ≤ A)
    (M : ℕ) (hM : 1 ≤ M) :
    ∃ k : ℝ, 0 < k ∧ ∀ N : ℕ, 1 ≤ N → N ≤ M →
      ∀ ϑ : ℝ, ϑ ∈ Set.Icc (-A) A → ∀ a b : ℕ,
        1 ≤ a → a ≤ b → b ≤ N →
          ENNReal.ofReal (k / (N : ℝ) ^ 2) ≤
            ∫⁻ p in renewalStringPairCell N a b,
              ENNReal.ofReal (DeltaBose.scalarDensity
                (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) := by
  let B : ℝ := A + |Real.eulerMascheroniConstant|
  obtain ⟨cDensity, hcDensity, hDensity⟩ :=
    exists_scalarDensity_lower_log B (by dsimp [B]; positivity)
  obtain ⟨cIntegral, hcIntegral, hIntegral⟩ :=
    exists_lintegral_scalarDensity_lower_log B (by dsimp [B]; positivity)
  let Mlog : ℝ := 1 + (Real.log 2)⁻¹
  let D : ℝ := cIntegral / (4 * (1 + Real.log (4 * (M : ℝ))) )
  let O : ℝ := cDensity /
    (8 * Mlog ^ 2 * (Real.log (1 + (M : ℝ))) ^ 2)
  let k : ℝ := min D O
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMge : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMlog : 0 < Mlog := by dsimp [Mlog]; positivity
  have hlog4M : 0 < 1 + Real.log (4 * (M : ℝ)) := by
    have harg : (1 : ℝ) < 4 * (M : ℝ) := by nlinarith
    linarith [Real.log_pos harg]
  have hlog1M : 0 < Real.log (1 + (M : ℝ)) := by
    apply Real.log_pos
    linarith
  have hD : 0 < D := by dsimp [D]; positivity
  have hO : 0 < O := by dsimp [O]; positivity
  have hk : 0 < k := lt_min hD hO
  refine ⟨k, hk, ?_⟩
  intro N hN hNM ϑ hϑ a b ha hab hbN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hθ : ϑ - Real.eulerMascheroniConstant ∈ Set.Icc (-B) B := by
    constructor
    · change -(A + |Real.eulerMascheroniConstant|) ≤
        ϑ - Real.eulerMascheroniConstant
      have hγ := neg_le_neg (le_abs_self Real.eulerMascheroniConstant)
      linarith [hϑ.1]
    · change ϑ - Real.eulerMascheroniConstant ≤
        A + |Real.eulerMascheroniConstant|
      have hγ := neg_le_abs Real.eulerMascheroniConstant
      linarith [hϑ.2]
  by_cases habEq : a = b
  · subst b
    have hdiag := renewalStringPairCell_diagonal_integral_lower N a M hN hNM
      (ϑ - Real.eulerMascheroniConstant) cIntegral hcIntegral
      (fun h hh hh1 => hIntegral (ϑ - Real.eulerMascheroniConstant) h hθ hh hh1)
    have hcoeff : k / (N : ℝ) ^ 2 ≤
        cIntegral / (4 * (1 + Real.log (4 * (M : ℝ))) * (N : ℝ) ^ 2) := by
      have hkD : k ≤ D := by simp [k]
      calc
        k / (N : ℝ) ^ 2 ≤ D / (N : ℝ) ^ 2 :=
          div_le_div_of_nonneg_right hkD (sq_nonneg (N : ℝ))
        _ = cIntegral /
            (4 * (1 + Real.log (4 * (M : ℝ))) * (N : ℝ) ^ 2) := by
          dsimp [D]
          field_simp [ne_of_gt hlog4M, ne_of_gt hNpos]
    exact (ENNReal.ofReal_le_ofReal hcoeff).trans hdiag
  · have hablt : a < b := by omega
    have hoff := renewalStringPairCell_offdiag_integral_lower N a b M hN hNM ha
      hablt hbN (ϑ - Real.eulerMascheroniConstant) B cDensity hcDensity hθ hDensity
    have hcoeff : k / (N : ℝ) ^ 2 ≤
        cDensity /
          (8 * Mlog ^ 2 * (Real.log (1 + (M : ℝ))) ^ 2 * (N : ℝ) ^ 2) := by
      have hkO : k ≤ O := by simp [k]
      dsimp [O] at hkO
      have hfirst : k / (N : ℝ) ^ 2 ≤ O / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hkO (sq_nonneg (N : ℝ))
      calc
        k / (N : ℝ) ^ 2 ≤ O / (N : ℝ) ^ 2 := hfirst
        _ = cDensity /
            (8 * Mlog ^ 2 * (Real.log (1 + (M : ℝ))) ^ 2 * (N : ℝ) ^ 2) := by
          dsimp [O]
          field_simp [ne_of_gt hMlog, ne_of_gt hlog1M, ne_of_gt hNpos]
    exact (ENNReal.ofReal_le_ofReal hcoeff).trans hoff

/-- Uniform lower comparison for every renewal-pair cell and every scale
`N ≥ 1`.  The finite range is handled by compact density bounds; at large
scales we use the sharper asymptotic renewal comparison. -/
theorem exists_renewalStringPairCell_lower_all (A : ℝ) (hA : 0 ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ ϑ : ℝ, ϑ ∈ Set.Icc (-A) A → ∀ a b : ℕ,
        1 ≤ a → a ≤ b → b ≤ N →
          ENNReal.ofReal (c / (N : ℝ) *
            |criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a)|) ≤
            ∫⁻ p in renewalStringPairCell N a b,
              ENNReal.ofReal (DeltaBose.scalarDensity
                (ϑ - Real.eulerMascheroniConstant) (p.2 - p.1)) := by
  obtain ⟨cLarge, hcLarge, hLarge⟩ := exists_renewalStringPairCell_lower A hA
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hLarge
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_criticalSigmaSq_uniform_log_bound A hA)
  let M : ℕ := max (max N₀ N₁) 1
  have hM : 1 ≤ M := by dsimp [M]; exact le_max_right _ _
  have hN₀M : N₀ ≤ M := by dsimp [M]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hN₁M : N₁ ≤ M := by dsimp [M]; exact (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨k, hk, hFloor⟩ := renewalStringPairCell_integral_floor_finite A hA M hM
  let S : ℝ := (1 + A / Real.log 2) / srwKernel 2 0
  let massBound : ℝ := S * (((M + 1 : ℕ) : ℝ) * (1 + S)) ^ M
  let cSmall : ℝ := k / ((M : ℝ) * massBound)
  let c : ℝ := min cSmall cLarge
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hq : 0 < srwKernel 2 0 := srwKernel_two_zero_pos
  have hS : 0 < S := by
    dsimp [S]
    apply div_pos
    · have hAdiv : 0 ≤ A / Real.log 2 := div_nonneg hA hlog2.le
      linarith
    · exact hq
  have hMassBound : 0 < massBound := by
    dsimp [massBound]
    have hMc : 0 < ((M + 1 : ℕ) : ℝ) := by positivity
    have hfactor : 0 < 1 + S := by linarith
    positivity
  have hMreal : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hcSmall : 0 < cSmall := by dsimp [cSmall]; positivity
  have hc : 0 < c := lt_min hcSmall hcLarge
  refine ⟨c, hc, ?_⟩
  intro N hN ϑ hϑ a b ha hab hbN
  let x : ℝ := criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N (b - a)
  by_cases hNM : N ≤ M
  · have hfloor := hFloor N hN hNM ϑ hϑ a b ha hab hbN
    have hmass := abs_criticalRenewalMass_le_finite_range A hA M N (b - a)
      hN (by omega) ϑ hϑ
    have hxabs : |x| ≤ massBound := by simpa [x, massBound, S] using hmass
    have hNreal : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hMN : (N : ℝ) ≤ M := by exact_mod_cast hNM
    have hden : (N : ℝ) ^ 2 ≤ (M : ℝ) * N := by nlinarith
    have hcsmallmul : cSmall / N * massBound = k / ((M : ℝ) * N) := by
      dsimp [cSmall]
      field_simp [ne_of_gt hMreal, ne_of_gt hMassBound, ne_of_gt hNreal]
    have hbound : cSmall / N * massBound ≤ k / (N : ℝ) ^ 2 := by
      rw [hcsmallmul]
      exact div_le_div_of_nonneg_left hk.le (by positivity) hden
    have hc_le : c ≤ cSmall := by exact min_le_left _ _
    have hcoeff : c / N ≤ cSmall / N :=
      div_le_div_of_nonneg_right hc_le (by positivity)
    have hreal : c / N * |x| ≤ k / (N : ℝ) ^ 2 := by
      calc
        c / N * |x| ≤ cSmall / N * |x| := mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
        _ ≤ cSmall / N * massBound :=
          mul_le_mul_of_nonneg_left hxabs (div_nonneg hcSmall.le (by positivity))
        _ ≤ k / (N : ℝ) ^ 2 := hbound
    exact (ENNReal.ofReal_le_ofReal (by simpa [x] using hreal)).trans hfloor
  · have hMN : M ≤ N := by omega
    have hLargeN := hN₀ N (le_trans hN₀M hMN) ϑ hϑ a b ha hab hbN
    have hSigmaN := hN₁ N (le_trans hN₁M hMN) ϑ hϑ
    have hσ : 0 < criticalSigmaSq ϑ N := hSigmaN.1
    have hmass : 0 ≤ Renewal.criticalRenewalMass ϑ N (b - a) := by
      change 0 ≤ Renewal.renewalMass
        (fun r => criticalSigmaSq ϑ N * Renewal.returnWeight r) (b - a)
      apply Renewal.renewalMass_nonneg
      intro r
      exact mul_nonneg hσ.le (srwKernel_nonneg (2 * r) 0)
    have hx : 0 ≤ x := by simpa [x] using mul_nonneg hσ.le hmass
    have habs : |x| = x := abs_of_nonneg hx
    have hc_le : c ≤ cLarge := min_le_right _ _
    have hcoeff : c / (N : ℝ) ≤ cLarge / (N : ℝ) :=
      div_le_div_of_nonneg_right hc_le (by positivity)
    have hreal : c / (N : ℝ) * |x| ≤ cLarge / (N : ℝ) * x := by
      rw [habs]
      exact mul_le_mul_of_nonneg_right hcoeff hx
    exact (ENNReal.ofReal_le_ofReal (by simpa [x] using hreal)).trans hLargeN


end Critical2DKPZ.Collision

end
