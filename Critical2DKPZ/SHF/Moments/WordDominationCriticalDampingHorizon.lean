/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25DampingChoice
public import Critical2DKPZ.MomentBounds.CSZ25ReturnWeights
public import Critical2DKPZ.Renewal.CriticalWindow
public import Mathlib.Tactic
public import Critical2DKPZ.RandomWalk.ReplicaOverlap
import Mathlib.Tactic

/-! # Critical damping on fixed multiples of the macroscopic horizon -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds Critical2DKPZ.Renewal
open Filter

/-- For each fixed integer horizon multiple `B`, sufficiently strong damping makes the critical variance times the overlap resolvent small. The damping scale `B * N` makes the estimate uniform over shorter lattice durations. -/
theorem eventually_critical_damped_resolvent_small_mul_horizon
    (ϑ ε : ℝ) (hε : 0 < ε) (B : ℕ) (hB : 1 ≤ B) :
    ∃ lam : ℝ, 1 ≤ lam ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      0 ≤ criticalSigmaSq ϑ N ∧
      criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) < 1 ∧
      criticalSigmaSq ϑ N *
        (criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
          (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N))) ≤ ε := by
  obtain ⟨aLo, _, haLo, _, hreturn⟩ := srwKernel_two_mul_zero_bounds
  obtain ⟨C, hC⟩ := Critical2DKPZ.replicaOverlap_log_bound
  let shift : ℝ := (1 / Real.pi) * Real.log B + 2 * C
  have hshift_nonneg : 0 ≤ shift := by
    dsimp [shift]
    have hlogB : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg (by
      exact_mod_cast hB : (1 : ℝ) ≤ (B : ℝ))
    have h1 := hC 1 (by omega)
    have hCpos : 0 ≤ C := le_trans (abs_nonneg _) h1
    positivity
  have hshift_bound : ∀ N : ℕ, 1 ≤ N →
      Critical2DKPZ.replicaOverlap (B * N) - Critical2DKPZ.replicaOverlap N ≤ shift := by
    intro N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hBN : 1 ≤ B * N := by exact Nat.one_le_iff_ne_zero.mpr (by
      exact mul_ne_zero (by omega) (by omega))
    have hlogBN : Real.log ((B * N : ℕ) : ℝ) = Real.log B + Real.log N := by
      rw [Nat.cast_mul, Real.log_mul (ne_of_gt hBpos) (ne_of_gt hNpos)]
    have hu := (abs_le.mp (hC (B * N) hBN)).2
    have hl := (abs_le.mp (hC N hN)).1
    rw [hlogBN] at hu
    change Critical2DKPZ.replicaOverlap (B * N) - (1 / Real.pi) *
        (Real.log B + Real.log N) ≤ C at hu
    change -C ≤ Critical2DKPZ.replicaOverlap N - (1 / Real.pi) * Real.log N at hl
    dsimp [shift]
    linarith
  let c : ℝ := (4 / Real.pi) * (|ϑ| + 2 * Real.pi / ε + 2 * Real.pi * shift + 1)
  let k : ℝ := (2 / aLo) * c
  let lam : ℝ := 2 * Real.exp k
  have hc : 0 < c := by dsimp [c]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  have hlam : 1 ≤ lam := by
    dsimp [lam]
    have he : 1 ≤ Real.exp k := Real.one_le_exp_iff.mpr hk.le
    linarith
  have hloglam : Real.log (lam / 2) = k := by
    dsimp [lam]
    rw [show (2 * Real.exp k) / 2 = Real.exp k by ring, Real.log_exp]
  have hmargin : 2 * Real.pi / ε < Real.pi / 2 * c - (|ϑ| + 2 * Real.pi * shift) := by
    dsimp [c]
    have hϑ : 0 ≤ |ϑ| := abs_nonneg ϑ
    have hfactor : Real.pi / 2 * (4 / Real.pi) = 2 := by
      field_simp [ne_of_gt Real.pi_pos]
      norm_num
    rw [← mul_assoc, hfactor]
    nlinarith [Real.pi_pos, hϑ, hε, hshift_nonneg]
  have hsigmaLog : ∀ᶠ N : ℕ in atTop,
      Real.pi / 2 < criticalSigmaSq ϑ N * Real.log (N : ℝ) ∧
        criticalSigmaSq ϑ N * Real.log (N : ℝ) < 2 * Real.pi := by
    have h := tendsto_order.mp (tendsto_sigma_mul_log ϑ)
    filter_upwards [h.1 (Real.pi / 2) (by nlinarith [Real.pi_pos]),
      h.2 (2 * Real.pi) (by nlinarith [Real.pi_pos])] with N hlow hupp
    exact ⟨hlow, hupp⟩
  have hNlam : ∀ᶠ N : ℕ in atTop, lam ≤ ((B * N : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈lam / B⌉₊] with N hN
    have hceil : lam / B ≤ (⌈lam / B⌉₊ : ℝ) := Nat.le_ceil _
    have hBreal : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
    have hceilN : (⌈lam / B⌉₊ : ℝ) ≤ N := by exact_mod_cast hN
    have hquot : lam / B ≤ N := le_trans hceil hceilN
    have hmul : lam ≤ N * (B : ℝ) := (div_le_iff₀ hBreal).1 hquot
    simpa only [Nat.cast_mul, mul_comm] using hmul
  have hN2 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have hgood : ∀ᶠ N : ℕ in atTop,
      0 ≤ criticalSigmaSq ϑ N ∧
        criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) < 1 ∧
        criticalSigmaSq ϑ N *
          (criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
            (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N))) ≤ ε := by
    filter_upwards [hsigmaLog, hNlam, hN2, criticalSigmaSq_eventually_pos ϑ,
      eventually_ge_atTop 1] with N hσlog hNl hN2 hσpos hN1
    have hlogpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hσ : 0 < criticalSigmaSq ϑ N := hσpos
    have hdam := dampedOverlap_le_replicaOverlap_sub_log
      (aLo := aLo) haLo.le (fun n hn => (hreturn n hn).1)
      (L := B * N) (lam := lam) hlam (by exact_mod_cast hNl)
    have hcrit := criticalSigmaSq_mul_overlap ϑ (show 1 ≤ N by omega)
    have hσupper : criticalSigmaSq ϑ N ≤ 2 * Real.pi / Real.log (N : ℝ) := by
      apply (le_div_iff₀ hlogpos).2
      exact hσlog.2.le
    have hprod :
        criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) ≤
          1 + (ϑ + 2 * Real.pi * shift) / Real.log (N : ℝ) -
            criticalSigmaSq ϑ N * c := by
      have hdiff := hshift_bound N hN1
      have hcEq : aLo / 2 * Real.log (lam / 2) = c := by
        dsimp [k] at hloglam ⊢
        rw [hloglam]
        dsimp [c]
        field_simp [ne_of_gt haLo]
      rw [hcEq] at hdam
      have hdam' : dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) ≤
          Critical2DKPZ.replicaOverlap (B * N) - c := by
        exact hdam
      have htop : Critical2DKPZ.replicaOverlap (B * N) ≤
          Critical2DKPZ.replicaOverlap N + shift := by linarith [hdiff]
      have hbase : criticalSigmaSq ϑ N * Critical2DKPZ.replicaOverlap N =
          1 + ϑ / Real.log (N : ℝ) := hcrit
      have : criticalSigmaSq ϑ N *
          (Critical2DKPZ.replicaOverlap (B * N) - c) ≤
            1 + ϑ / Real.log (N : ℝ) + criticalSigmaSq ϑ N * shift -
              criticalSigmaSq ϑ N * c := by
        calc
          _ ≤ criticalSigmaSq ϑ N *
              (Critical2DKPZ.replicaOverlap N + shift - c) :=
                mul_le_mul_of_nonneg_left (sub_le_sub_right htop c) hσ.le
          _ = _ := by
                rw [mul_sub, mul_add, hbase]
      have hshiftTerm : criticalSigmaSq ϑ N * shift ≤ 2 * Real.pi * shift /
          Real.log (N : ℝ) := by
        calc
          _ ≤ (2 * Real.pi / Real.log (N : ℝ)) * shift :=
            mul_le_mul_of_nonneg_right hσupper hshift_nonneg
          _ = 2 * Real.pi * shift / Real.log (N : ℝ) := by ring
      calc
        _ ≤ criticalSigmaSq ϑ N *
            (Critical2DKPZ.replicaOverlap (B * N) - c) := by
              exact mul_le_mul_of_nonneg_left hdam' hσ.le
        _ ≤ 1 + ϑ / Real.log (N : ℝ) + criticalSigmaSq ϑ N * shift -
            criticalSigmaSq ϑ N * c := this
        _ ≤ 1 + ϑ / Real.log (N : ℝ) +
            (2 * Real.pi * shift / Real.log (N : ℝ)) -
              criticalSigmaSq ϑ N * c := by
                linarith [hshiftTerm]
        _ = 1 + (ϑ / Real.log (N : ℝ) +
            2 * Real.pi * shift / Real.log (N : ℝ)) -
              criticalSigmaSq ϑ N * c := by ring
        _ = 1 + (ϑ + 2 * Real.pi * shift) / Real.log (N : ℝ) -
            criticalSigmaSq ϑ N * c := by rw [← add_div]
    have hmarginPos : 0 < Real.pi / 2 * c - (|ϑ| + 2 * Real.pi * shift) :=
      lt_trans (by positivity) hmargin
    have hlower :
        1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) ≥
          (Real.pi / 2 * c - (|ϑ| + 2 * Real.pi * shift)) / Real.log (N : ℝ) := by
      have hσlower : Real.pi / 2 ≤ criticalSigmaSq ϑ N * Real.log (N : ℝ) := hσlog.1.le
      have hcoeff :
          criticalSigmaSq ϑ N * c ≥ (Real.pi / 2 * c) / Real.log (N : ℝ) := by
        apply (div_le_iff₀ hlogpos).2
        calc
          Real.pi / 2 * c ≤ (criticalSigmaSq ϑ N * Real.log (N : ℝ)) * c :=
            mul_le_mul_of_nonneg_right hσlower hc.le
          _ = (criticalSigmaSq ϑ N * c) * Real.log (N : ℝ) := by ring
      have herror :
          (ϑ + 2 * Real.pi * shift) / Real.log (N : ℝ) ≤
            (|ϑ| + 2 * Real.pi * shift) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right (by linarith [le_abs_self ϑ]) hlogpos.le
      have hdenTarget :
          1 - (1 + (ϑ + 2 * Real.pi * shift) / Real.log (N : ℝ) -
              criticalSigmaSq ϑ N * c) ≥
            (Real.pi / 2 * c - (|ϑ| + 2 * Real.pi * shift)) / Real.log (N : ℝ) := by
        calc
          _ = criticalSigmaSq ϑ N * c -
              (ϑ + 2 * Real.pi * shift) / Real.log (N : ℝ) := by ring
          _ ≥ (Real.pi / 2 * c) / Real.log (N : ℝ) -
              (|ϑ| + 2 * Real.pi * shift) / Real.log (N : ℝ) := sub_le_sub hcoeff herror
          _ = _ := by rw [← sub_div]
      exact hdenTarget.trans (sub_le_sub_left hprod 1)
    have hden : 0 < 1 -
        criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) :=
      lt_of_lt_of_le (div_pos hmarginPos hlogpos) hlower
    have hsub : criticalSigmaSq ϑ N *
        dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) < 1 := sub_pos.mp hden
    have hnum : criticalSigmaSq ϑ N ^ 2 *
        dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) ≤ criticalSigmaSq ϑ N := by
      calc
        _ = criticalSigmaSq ϑ N * (criticalSigmaSq ϑ N *
            dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)) := by ring
        _ ≤ criticalSigmaSq ϑ N * 1 := mul_le_mul_of_nonneg_left hsub.le hσ.le
        _ = _ := by ring
    have hratio : criticalSigmaSq ϑ N *
        (criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
          (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N))) ≤ ε := by
      let margin : ℝ := Real.pi / 2 * c - (|ϑ| + 2 * Real.pi * shift)
      have hmarginPos' : 0 < margin := hmarginPos
      have hmarginNe : margin ≠ 0 := ne_of_gt hmarginPos'
      have hlogNe : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogpos
      have hratioId :
          (2 * Real.pi / margin) * (margin / Real.log (N : ℝ)) =
            2 * Real.pi / Real.log (N : ℝ) := by
        calc
          _ = (2 * Real.pi) * (margin⁻¹ * margin) * (Real.log (N : ℝ))⁻¹ := by
            simp only [div_eq_mul_inv]
            ring
          _ = (2 * Real.pi) * (Real.log (N : ℝ))⁻¹ := by
            rw [inv_mul_cancel₀ hmarginNe]
            ring
          _ = _ := by rw [div_eq_mul_inv]
      have hnum' : criticalSigmaSq ϑ N ^ 2 *
          dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
            (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)) ≤ ε := by
        have hsigmaDiv : criticalSigmaSq ϑ N /
              (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)) ≤
            (2 * Real.pi) / margin := by
          apply (div_le_iff₀ hden).2
          calc
            criticalSigmaSq ϑ N ≤ (2 * Real.pi) / Real.log (N : ℝ) := hσupper
            _ = (2 * Real.pi / margin) * (margin / Real.log (N : ℝ)) := hratioId.symm
            _ ≤ (2 * Real.pi / margin) *
                (1 - criticalSigmaSq ϑ N *
                  dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)) :=
              mul_le_mul_of_nonneg_left hlower (div_nonneg (by positivity) hmarginPos'.le)
        have hfactor : criticalSigmaSq ϑ N ^ 2 *
            dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
              (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)) ≤
            criticalSigmaSq ϑ N /
              (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)) := by
          exact div_le_div_of_nonneg_right hnum hden.le
        calc
          _ ≤ criticalSigmaSq ϑ N /
              (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)) := hfactor
          _ ≤ (2 * Real.pi) /
              margin := hsigmaDiv
          _ ≤ ε := by
            apply (div_le_iff₀ hmarginPos').2
            have hmul := (div_lt_iff₀ hε).1 hmargin
            simpa [margin, mul_comm] using hmul.le
      have hid : criticalSigmaSq ϑ N *
          (criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
            (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N))) =
          criticalSigmaSq ϑ N ^ 2 *
            dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N) /
              (1 - criticalSigmaSq ϑ N * dampedOverlap (lam / ((B * N : ℕ) : ℝ)) (B * N)) := by ring
      rw [hid]
      exact hnum'
    exact ⟨hσ.le, hsub, hratio⟩
  exact ⟨lam, hlam, (eventually_atTop.1 hgood).choose,
    (eventually_atTop.1 hgood).choose_spec⟩

end Critical2DKPZ.SHF.Moments

end
