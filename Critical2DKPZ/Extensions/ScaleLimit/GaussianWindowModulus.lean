/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.WindowProbabilityBound
public import Critical2DKPZ.Extensions.ScaleLimit.GaussianMeshBudget
public import Critical2DKPZ.Extensions.ScaleLimit.ModulusMesh
import Mathlib.Tactic

/-! # A Gaussian window bound implies a uniform modulus in probability -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Finite overlapping windows turn the Gaussian truncated window estimate
into a uniform modulus. No measurability of the oscillation events is needed. -/
theorem modulus_of_gaussian_window_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Set.Ioi (0 : ℝ) → ℝ → Ω → ℝ)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c)
    (hwindow : ∀ s t η : ℝ, 0 ≤ s → s < t → 0 < η →
      limsup (fun L : Set.Ioi (0 : ℝ) => P (windowOscillationEvent (X L) s t η)) atTop ≤
        ENNReal.ofReal (C * (t - s) / η ^ 2 *
          ∫ y : ℝ, squareTail (c * η / Real.sqrt (t - s)) y ∂gaussianReal 0 1))
    {S : ℝ} (hS : 0 < S) (η : ℝ) (hη : 0 < η) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ L : Set.Ioi (0 : ℝ) in atTop,
      P {ω | ∃ p q : Set.Icc (0 : ℝ) S,
        dist (p : ℝ) (q : ℝ) ≤ δ ∧ η < |X L p ω - X L q ω|} ≤ ENNReal.ofReal ρ := by
  obtain ⟨m, hm, hbudget⟩ := exists_gaussian_mesh_budget hC hc hS hη (half_pos hρ)
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  let h := S / (m : ℝ)
  have hh : 0 < h := div_pos hS hmR
  let K := C * (2 * h) / η ^ 2 *
    ∫ y : ℝ, squareTail (c * η / Real.sqrt (2 * h)) y ∂gaussianReal 0 1
  have hK : 0 ≤ K := mul_nonneg (by positivity) (integral_nonneg fun y => squareTail_nonneg _ y)
  change (m : ℝ) * K < ρ / 2 at hbudget
  let ε := ρ / (4 * (m : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hKB : (m : ℝ) * (K + ε) < ρ := by
    have heq : (m : ℝ) * ε = ρ / 4 := by dsimp [ε]; field_simp
    rw [mul_add, heq]
    linarith
  have hw (k : ℕ) : ∀ᶠ L : Set.Ioi (0 : ℝ) in atTop,
      P (windowOscillationEvent (X L) ((k : ℝ) * h) (((k : ℝ) + 2) * h) η) ≤
        ENNReal.ofReal (K + ε) := by
    have hleft : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
    have hlt : (k : ℝ) * h < ((k : ℝ) + 2) * h := by nlinarith only [hh]
    have hlen : ((k : ℝ) + 2) * h - (k : ℝ) * h = 2 * h := by ring
    have hb := hwindow ((k : ℝ) * h) (((k : ℝ) + 2) * h) η hleft hlt hη
    rw [hlen] at hb
    have hstrict : ENNReal.ofReal K < ENNReal.ofReal (K + ε) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (lt_add_of_pos_right K hε)
    exact (eventually_lt_of_limsup_lt (hb.trans_lt hstrict)).mono fun _ h => h.le
  have hall : ∀ᶠ L : Set.Ioi (0 : ℝ) in atTop, ∀ k ∈ Finset.range m,
      P (windowOscillationEvent (X L) ((k : ℝ) * h) (((k : ℝ) + 2) * h) η) ≤
        ENNReal.ofReal (K + ε) := (eventually_all_finset (Finset.range m)).mpr fun k _ => hw k
  refine ⟨h, hh, ?_⟩
  filter_upwards [hall] with L hL
  have hmh : (m : ℝ) * h = S := by dsimp [h]; field_simp
  have hsub : {ω | ∃ p q : Set.Icc (0 : ℝ) S, dist (p : ℝ) (q : ℝ) ≤ h ∧
      η < |X L p ω - X L q ω|} ⊆
      {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ (m : ℝ) * h ∧ t - s ≤ h ∧
        η < |X L t ω - X L s ω|} := by
    rintro ω ⟨p, q, hpq, hX⟩
    rcases le_total (p : ℝ) (q : ℝ) with hpq' | hqp'
    · have hd : dist (p : ℝ) (q : ℝ) = (q : ℝ) - p := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hpq')]
        ring
      rw [hd] at hpq
      refine ⟨p, q, p.property.1, hpq', ?_, hpq, ?_⟩
      · rw [hmh]; exact q.property.2
      · rwa [abs_sub_comm]
    · have hd : dist (p : ℝ) (q : ℝ) = (p : ℝ) - q := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hqp')]
      rw [hd] at hpq
      refine ⟨q, p, q.property.1, hqp', ?_, hpq, hX⟩
      rw [hmh]; exact p.property.2
  have hsubwin (k : ℕ) : {ω | ∃ s t : ℝ, (k : ℝ) * h ≤ s ∧ s ≤ t ∧
        t ≤ ((k : ℝ) + 2) * h ∧ η < |X L t ω - X L s ω|} ⊆
      windowOscillationEvent (X L) ((k : ℝ) * h) (((k : ℝ) + 2) * h) η := by
    rintro ω ⟨s, t, hks, hst, htk, hX⟩
    exact ⟨⟨t, ⟨hks.trans hst, htk⟩⟩, ⟨s, ⟨hks, hst.trans htk⟩⟩, hX⟩
  calc
    _ ≤ P {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ (m : ℝ) * h ∧ t - s ≤ h ∧
        η < |X L t ω - X L s ω|} := measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range m, P {ω | ∃ s t : ℝ,
        (k : ℝ) * h ≤ s ∧ s ≤ t ∧ t ≤ ((k : ℝ) + 2) * h ∧ η < |X L t ω - X L s ω|} :=
      short_increment_measure_le P (X L) hh hm η
    _ ≤ ∑ k ∈ Finset.range m, P (windowOscillationEvent (X L)
        ((k : ℝ) * h) (((k : ℝ) + 2) * h) η) :=
      Finset.sum_le_sum fun k _ => measure_mono (hsubwin k)
    _ ≤ ∑ _k ∈ Finset.range m, ENNReal.ofReal (K + ε) := Finset.sum_le_sum fun k hk => hL k hk
    _ = ENNReal.ofReal ((m : ℝ) * (K + ε)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => add_nonneg hK hε.le)]
      congr 1
      simp [mul_add]
    _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal hKB.le

end Critical2DKPZ.Extensions.ScaleLimit
