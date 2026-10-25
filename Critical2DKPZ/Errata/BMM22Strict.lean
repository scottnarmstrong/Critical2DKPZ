/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Errata.BMM22
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic

/-! # Normalization of two-sided geometric profiles

The profile in BMM22 Lemma 7.1 has the stated normalization for `0 ≤ q < 1`, including the point-mass case `M = 1` and `q = 0`. -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Errata

/-- The actual two-sided profile in BMM22, summed with its central mass. -/
theorem bmm22_geometric_hasSum_strict (M : ℝ) {q : ℝ}
    (hq : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun k : ℤ => q ^ k.natAbs * M) (M * (1 + q) / (1 - q)) := by
  have hn : HasSum (fun n : ℕ => q ^ n * M) ((1 - q)⁻¹ * M) :=
    (hasSum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hq])).mul_right M
  have hm : HasSum (fun n : ℕ => q ^ (n + 1) * M) (q * ((1 - q)⁻¹ * M)) := by
    convert hn.mul_left q using 1
    funext n
    rw [pow_succ]
    ring
  have h : HasSum (fun k : ℤ => q ^ k.natAbs * M)
      (((1 - q)⁻¹ * M) + q * ((1 - q)⁻¹ * M)) := by
    apply HasSum.of_nat_of_neg_add_one
    · simpa using hn
    · have habs (n : ℕ) : (-(↑n + 1) : ℤ).natAbs = n + 1 := by
        have hc : (↑n + 1 : ℤ) = ((n + 1 : ℕ) : ℤ) := by omega
        rw [hc, Int.natAbs_neg, Int.natAbs_natCast]
      simpa only [habs] using hm
  convert h using 1
  rw [div_eq_mul_inv]
  ring

/-- The integer-indexed geometric profile has finite total mass for `0 ≤ q < 1`. -/
theorem bmm22_normalization_continuousOn_strict (M : ℝ) :
    ContinuousOn (fun q : ℝ => ∑' k : ℤ, q ^ k.natAbs * M) (Set.Ico 0 1) := by
  have hc : ContinuousOn (fun q : ℝ => M * (1 + q) / (1 - q)) (Set.Ico 0 1) :=
    (continuous_const.mul (continuous_const.add continuous_id)).continuousOn.div
      (continuous_const.sub continuous_id).continuousOn
      (fun q hq => (sub_pos.mpr hq.2).ne')
  apply hc.congr
  intro q hq
  exact (bmm22_geometric_hasSum_strict M hq.1 hq.2).tsum_eq

/-- Every admissible maximum `M` has a unique normalized geometric profile with `q = (1 - M) / (1 + M)`. -/
theorem bmm22_geometric_normalization_strict_corrected {M : ℝ}
    (hM : 0 < M) (hM1 : M ≤ 1) :
    ∃! q : ℝ, 0 ≤ q ∧ q < 1 ∧ HasSum (fun k : ℤ => q ^ k.natAbs * M) 1 := by
  let q : ℝ := (1 - M) / (1 + M)
  have hd : 0 < 1 + M := by linarith only [hM]
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr hM1) hd.le
  have hq1 : q < 1 := by
    apply (div_lt_one hd).mpr
    linarith only [hM]
  have hn : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hvalue : M * (1 + q) / (1 - q) = 1 := by
    apply (div_eq_one_iff_eq hn).mpr
    have hqeq : q * (1 + M) = 1 - M := div_mul_cancel₀ _ hd.ne'
    nlinarith only [hqeq]
  refine ⟨q, ⟨hq, hq1, hvalue ▸ bmm22_geometric_hasSum_strict M hq hq1⟩, ?_⟩
  intro r hr
  have hs := (bmm22_geometric_hasSum_strict M hr.1 hr.2.1).unique hr.2.2
  have hrn : 1 - r ≠ 0 := (sub_pos.mpr hr.2.1).ne'
  have he : M * (1 + r) = 1 - r := (div_eq_one_iff_eq hrn).mp hs
  apply (eq_div_iff hd.ne').mpr
  nlinarith only [he]

end Critical2DKPZ.Errata
