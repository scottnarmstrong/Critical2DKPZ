/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Errata.CSZ25
public import Critical2DKPZ.Errata.CSZ25Strict
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! # Renewal floor cutoffs and exponential-sum bounds

The scalar estimates used in the proof of CSZ25 Lemma 5.4 hold with a floor cutoff and a separate small-overlap case. -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Errata.CSZ25

/-- The floor cutoff gives the Markov threshold at the actual overlap. -/
theorem csz25_08_corrected_overlap_cutoff (L k : ℕ) (hL : 1 ≤ L)
    {a : ℝ} (ha : 0 < a) (hk : k ≤ ⌊replicaOverlap L / (4 * a)⌋₊) :
    (k : ℝ) / replicaOverlap L * a * L ≤ (L : ℝ) / 4 := by
  exact csz25_floor_markov_threshold (replicaOverlap_pos hL) ha
    (Nat.cast_nonneg L) hk

/-- Above the overlap threshold the floor retains at least half its real argument. -/
theorem csz25_08_floor_cutoff_lower (L : ℕ) {a : ℝ} (ha : 0 < a)
    (hlarge : 8 * a ≤ replicaOverlap L) :
    replicaOverlap L / (8 * a) ≤ (⌊replicaOverlap L / (4 * a)⌋₊ : ℝ) := by
  have hx : (2 : ℝ) ≤ replicaOverlap L / (4 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * a)).mpr
    linarith only [hlarge]
  have hf := Nat.sub_one_lt_floor (replicaOverlap L / (4 * a))
  have hhalf : replicaOverlap L / (8 * a) =
      (replicaOverlap L / (4 * a)) / 2 := by ring
  rw [hhalf]
  linarith only [hx, hf]

/-- The last Jensen step with the floor has coefficient and exponent denominator `16a`. -/
theorem csz25_08_corrected_jensen_last_step (L : ℕ) {a θ : ℝ}
    (ha : 0 < a) (hθ : 0 ≤ θ) (hlarge : 8 * a ≤ replicaOverlap L) :
    replicaOverlap L / (16 * a) * Real.exp (θ / (16 * a)) ≤
      ((⌊replicaOverlap L / (4 * a)⌋₊ : ℝ) / 2) *
        Real.exp (θ / replicaOverlap L *
          ((⌊replicaOverlap L / (4 * a)⌋₊ : ℝ) / 2)) := by
  have hR : 0 < replicaOverlap L := (by positivity : 0 < 8 * a).trans_le hlarge
  have hK := csz25_08_floor_cutoff_lower L ha hlarge
  have hcoeff : replicaOverlap L / (16 * a) ≤
      (⌊replicaOverlap L / (4 * a)⌋₊ : ℝ) / 2 := by
    have heq : replicaOverlap L / (16 * a) =
        (replicaOverlap L / (8 * a)) / 2 := by ring
    rw [heq]
    exact div_le_div_of_nonneg_right hK (by norm_num)
  have hexponent : θ / (16 * a) ≤ θ / replicaOverlap L *
      ((⌊replicaOverlap L / (4 * a)⌋₊ : ℝ) / 2) := by
    calc
      θ / (16 * a) = θ / replicaOverlap L * (replicaOverlap L / (16 * a)) := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hcoeff (div_nonneg hθ hR.le)
  exact mul_le_mul hcoeff (Real.exp_le_exp.mpr hexponent)
    (Real.exp_pos _).le (by positivity)

/-- Below the overlap threshold the original parameter range directly bounds theta. -/
theorem csz25_08_small_overlap_theta_bound (L : ℕ) {a θ : ℝ}
    (hθR : θ < replicaOverlap L) (hsmall : replicaOverlap L < 8 * a) :
    θ < 8 * a := hθR.trans hsmall

end Critical2DKPZ.Errata.CSZ25
