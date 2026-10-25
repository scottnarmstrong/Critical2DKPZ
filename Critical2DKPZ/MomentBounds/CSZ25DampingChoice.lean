/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25Green
public import Critical2DKPZ.Lattice.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Damping the replica overlap in CSZ25 Lemma 5.6 -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Positive damping can only decrease the finite overlap. -/
theorem dampedOverlap_le_replicaOverlap {lam : ℝ} (hlam : 0 ≤ lam) (L : ℕ) :
    dampedOverlap lam L ≤ replicaOverlap L := by
  apply Finset.sum_le_sum
  intro r _
  exact mul_le_of_le_one_left (srwKernel_nonneg _ _)
    (Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 hlam) (Nat.cast_nonneg r)))

/-- The reciprocal sum over a natural interval bounds its logarithmic ratio. -/
theorem log_div_le_sum_Icc_inv {K L : ℕ} (hK : 1 ≤ K) (hKL : K ≤ L) :
    Real.log ((L : ℝ) / K) ≤ ∑ r ∈ Finset.Icc K L, (r : ℝ)⁻¹ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hi := AntitoneOn.integral_le_sum_Ico (f := fun x : ℝ => x⁻¹)
    (a := K) (b := L + 1) (by omega) (inv_antitoneOn_Icc_right hK0)
  rw [integral_inv (by
    rw [Set.uIcc_of_le (by exact_mod_cast (show K ≤ L + 1 by omega))]
    exact fun h => (not_le_of_gt hK0) h.1)] at hi
  have hlog : Real.log ((L : ℝ) / K) ≤ Real.log (((L + 1 : ℕ) : ℝ) / K) :=
    Real.log_le_log (div_pos hL0 hK0)
      (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ L) hK0.le)
  exact hlog.trans (by simpa only [Finset.Ico_add_one_right_eq_Icc] using hi)

/-- Damping reduces the replica overlap by at least `aLo / 2 * log (lam / 2)`, as in CSZ25 Lemma 5.6. -/
theorem dampedOverlap_le_replicaOverlap_sub_log {aLo : ℝ} (ha₀ : 0 ≤ aLo)
    (ha : ∀ n : ℕ, 1 ≤ n → aLo / n ≤ srwKernel (2 * n) 0) {L : ℕ} {lam : ℝ}
    (hlam : 1 ≤ lam) (hlamL : lam ≤ L) :
    dampedOverlap (lam / L) L ≤ replicaOverlap L - aLo / 2 * Real.log (lam / 2) := by
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hL0 : (0 : ℝ) < L := hlam0.trans_le hlamL
  have hbase := dampedOverlap_le_replicaOverlap (div_nonneg hlam0.le hL0.le) L
  by_cases hsmall : lam ≤ 2
  · have hlog : Real.log (lam / 2) ≤ 0 := Real.log_nonpos (by positivity) (by linarith only [hsmall])
    have hneg : aLo / 2 * Real.log (lam / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (div_nonneg ha₀ (by norm_num)) hlog
    exact hbase.trans (by linarith only [hneg])
  let K := ⌈(L : ℝ) / lam⌉₊
  have hK : 1 ≤ K := Nat.one_le_ceil_iff.2 (div_pos hL0 hlam0)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKL : K ≤ L := Nat.ceil_le.2 ((div_le_iff₀ hlam0).2 (by nlinarith only [hlam]))
  have hceil : (K : ℝ) ≤ (L : ℝ) / lam + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hmul : (K : ℝ) * lam ≤ (L : ℝ) + lam := by
    calc
      _ ≤ ((L : ℝ) / lam + 1) * lam := mul_le_mul_of_nonneg_right hceil hlam0.le
      _ = _ := by field_simp
  have hratio : lam / 2 ≤ (L : ℝ) / K := (le_div_iff₀ hK0).2 (by nlinarith only [hmul, hlamL])
  have hlog := (Real.log_le_log (by positivity : 0 < lam / 2) hratio).trans
    (log_div_le_sum_Icc_inv hK hKL)
  have hehalf : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2)
      (by linarith only [Real.add_one_le_exp (1 : ℝ)]) :
        1 / Real.exp 1 ≤ 1 / 2)
  have hterm : ∀ r ∈ Finset.Icc K L,
      aLo / 2 * (r : ℝ)⁻¹ ≤ (1 - Real.exp (-(lam / L) * r)) * srwKernel (2 * r) 0 := by
    intro r hr
    have hr1 : 1 ≤ r := hK.trans (Finset.mem_Icc.1 hr).1
    have hkr : (L : ℝ) / lam ≤ r :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Finset.mem_Icc.1 hr).1)
    have hthreshold : 1 ≤ lam / L * r := by
      have ht := (div_le_iff₀ hlam0).1 hkr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hL0).2
      nlinarith only [ht]
    have he : Real.exp (-(lam / L) * r) ≤ 1 / 2 :=
      (Real.exp_le_exp.2 (by nlinarith only [hthreshold])).trans hehalf
    calc
      _ = (1 / 2 : ℝ) * (aLo / r) := by ring
      _ ≤ (1 / 2 : ℝ) * srwKernel (2 * r) 0 := mul_le_mul_of_nonneg_left (ha r hr1) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [he]) (srwKernel_nonneg _ _)
  have hloss : aLo / 2 * (∑ r ∈ Finset.Icc K L, (r : ℝ)⁻¹) ≤
      replicaOverlap L - dampedOverlap (lam / L) L := by
    rw [replicaOverlap, dampedOverlap, ← Finset.sum_sub_distrib, Finset.mul_sum]
    calc
      _ ≤ ∑ r ∈ Finset.Icc K L, (1 - Real.exp (-(lam / L) * r)) * srwKernel (2 * r) 0 :=
        Finset.sum_le_sum hterm
      _ ≤ ∑ r ∈ Finset.Icc 1 L, (1 - Real.exp (-(lam / L) * r)) * srwKernel (2 * r) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left hK)
          (fun r _ _ => mul_nonneg (sub_nonneg.2 (Real.exp_le_one_iff.2
            (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (div_nonneg hlam0.le hL0.le))
              (Nat.cast_nonneg r)))) (srwKernel_nonneg _ _))
      _ = _ := Finset.sum_congr rfl (fun r _ => by ring)
  have h := (mul_le_mul_of_nonneg_left hlog (div_nonneg ha₀ (by norm_num))).trans hloss
  linarith only [h]

end Critical2DKPZ.MomentBounds
