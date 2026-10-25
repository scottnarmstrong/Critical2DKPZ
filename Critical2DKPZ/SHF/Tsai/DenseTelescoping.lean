/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.DensePartitions
public import Critical2DKPZ.SHF.Tsai.PartitionMesh
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Order.Fin.Basic

/-! # Vanishing superlinear increment bounds on a dense time set

Dense partitions with vanishing maximum mesh let the local increment bounds
telescope. The canonical maximum-mesh estimate makes their total error tend
to zero when the exponent exceeds one.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- A uniform increment bound of exponent greater than one forces endpoint equality on a dense time set. -/
theorem eq_endpoints_of_dense_increment_rpow_bound {D : Set ℝ} {s t α C : ℝ}
    (hD : Icc s t ⊆ closure D) (hs : s ∈ D) (ht : t ∈ D) (hst : s < t) (hα : 1 < α)
    (F : ℝ → ℝ)
    (hF : ∀ a ∈ D, ∀ b ∈ D, s ≤ a → a < b → b ≤ t → |F a - F b| ≤ C * (b - a) ^ α) :
    F s = F t := by
  classical
  choose r hr0 hrend hrmem hrgap using fun j : ℕ =>
    exists_dense_partition hD hs ht hst (j + 1) (by omega)
  have hrmono (j : ℕ) : StrictMono (fun i : Fin (j + 3) => r j i) := by
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    exact sub_pos.mp (hrgap j i i.is_lt).1
  have hrIcc (j i : ℕ) (hi : i ≤ j + 2) : r j i ∈ Icc s t := by
    have hzero : (0 : Fin (j + 3)) ≤ ⟨i, by omega⟩ := Fin.zero_le _
    have hlast : (⟨i, by omega⟩ : Fin (j + 3)) ≤ Fin.last (j + 2) := Fin.le_last _
    constructor
    · simpa only [Fin.val_zero, hr0] using (hrmono j).monotone hzero
    · simpa only [Fin.val_last, hrend] using (hrmono j).monotone hlast
  let δ (j : ℕ) : ℝ := 2 * (t - s) * (1 / ((j : ℝ) + 1))
  have hwidth : 0 < t - s := sub_pos.mpr hst
  have hδ (j : ℕ) : 0 ≤ δ j := by dsimp only [δ]; positivity
  have hmesh (j i : ℕ) (hi : i < j + 2) : r j (i + 1) - r j i ≤ δ j := by
    exact (hrgap j i hi).2.trans_eq (by dsimp only [δ]; push_cast; ring)
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 * (t - s))
  have hlim := tendsto_sum_increment_rpow_zero (fun j => j + 2) r hδ hα
    (fun j i hi => (hrgap j i hi).1.le) hmesh
    (T := t - s) (fun j => by rw [hr0, hrend]) hδlim
  have hwhole (j : ℕ) : |F s - F t| ≤ C *
      ∑ i ∈ Finset.range (j + 2), (r j (i + 1) - r j i) ^ α := by
    have hlocal (i : ℕ) (hi : i < j + 2) :
        dist (F (r j i)) (F (r j (i + 1))) ≤ C * (r j (i + 1) - r j i) ^ α := by
      rw [Real.dist_eq]
      exact hF _ (hrmem j i (by omega)) _ (hrmem j (i + 1) (by omega))
        (hrIcc j i (by omega)).1 (sub_pos.mp (hrgap j i hi).1) (hrIcc j (i + 1) (by omega)).2
    have hbound := dist_le_range_sum_of_dist_le (f := fun i => F (r j i)) (j + 2) (fun {i} hi => hlocal i hi)
    simpa only [Real.dist_eq, hr0, hrend, Finset.mul_sum] using hbound
  have hle : |F s - F t| ≤ 0 := by
    have htend : Tendsto (fun j => C * ∑ i ∈ Finset.range (j + 2),
        (r j (i + 1) - r j i) ^ α) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul C
    exact ge_of_tendsto htend (Eventually.of_forall hwhole)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

/-- Vanishing-mesh telescoping applies to eventual increment estimates with arbitrary positive slack. -/
theorem eq_endpoints_of_dense_eventual_increment_bound {D : Set ℝ} {s t α C A B : ℝ}
    (hD : Icc s t ⊆ closure D) (hs : s ∈ D) (ht : t ∈ D) (hst : s < t) (hα : 1 < α)
    (R : ℝ → ℕ → ℝ) (hsR : ∀ ℓ, R s ℓ = A) (htR : ∀ ℓ, R t ℓ = B)
    (hlim : ∀ c ∈ D, s ≤ c → c ≤ t → ∃ L : ℝ, Tendsto (R c) atTop (𝓝 L))
    (hstep : ∀ a ∈ D, ∀ b ∈ D, s ≤ a → a < b → b ≤ t →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ ℓ in atTop, |R a ℓ - R b ℓ| ≤ C * (b - a) ^ α + ε) : A = B := by
  classical
  let L (c : ℝ) : ℝ := if hc : c ∈ D ∧ s ≤ c ∧ c ≤ t then
    Classical.choose (hlim c hc.1 hc.2.1 hc.2.2) else 0
  have hL (c : ℝ) (hc : c ∈ D) (hsc : s ≤ c) (hct : c ≤ t) :
      Tendsto (R c) atTop (𝓝 (L c)) := by
    have hc' : c ∈ D ∧ s ≤ c ∧ c ≤ t := ⟨hc, hsc, hct⟩
    simpa only [L, dite_eq_left hc'] using Classical.choose_spec (hlim c hc hsc hct)
  have hbound (a : ℝ) (ha : a ∈ D) (b : ℝ) (hb : b ∈ D)
      (hsa : s ≤ a) (hab : a < b) (hbt : b ≤ t) : |L a - L b| ≤ C * (b - a) ^ α := by
    have hconv := ((hL a ha hsa (hab.le.trans hbt)).sub
      (hL b hb (hsa.trans hab.le) hbt)).abs
    apply le_of_forall_pos_le_add
    intro ε hε
    exact le_of_tendsto hconv (hstep a ha b hb hsa hab hbt ε hε)
  have hEq : L s = L t := eq_endpoints_of_dense_increment_rpow_bound hD hs ht hst hα L hbound
  have hsL : L s = A := tendsto_nhds_unique
    ((hL s hs le_rfl hst.le).congr (fun ℓ => hsR ℓ)) tendsto_const_nhds
  have htL : L t = B := tendsto_nhds_unique
    ((hL t ht hst.le le_rfl).congr (fun ℓ => htR ℓ)) tendsto_const_nhds
  exact hsL.symm.trans (hEq.trans htL)

end Critical2DKPZ.SHF.Tsai

end
