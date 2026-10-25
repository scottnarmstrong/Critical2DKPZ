/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.TruncatedLogs
public import Critical2DKPZ.Extensions.ScaleLimit.BlockPositivity
import Mathlib.Tactic

/-! # Deterministic logarithmic estimates on the block-good event -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Split a partial sum into its initial part and its late blocks. -/
theorem partialSum_split {Ω : Type*} (Z : ℝ → ℝ → Ω → MeasureTheory.Measure (Plane × Plane))
    (ρ : ℝ) {n ℓ : ℕ} (hℓn : ℓ ≤ n) (ω : Ω) :
    partialSum Z ρ n ω = partialSum Z ρ ℓ ω + ∑ j ∈ Finset.Ioc ℓ n, logTrunc Z ρ j ω := by
  classical
  have hu : Finset.Icc 1 n = Finset.Icc 1 ℓ ∪ Finset.Ioc ℓ n := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 ℓ) (Finset.Ioc ℓ n) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hj hj'
    omega
  simp only [partialSum, hu, Finset.sum_union hd]

/-- The bounded initial logarithmic sum costs at most `ℓ log 2`. -/
theorem abs_partialSum_le {Ω : Type*} (Z : ℝ → ℝ → Ω → MeasureTheory.Measure (Plane × Plane))
    (ρ : ℝ) (ℓ : ℕ) (ω : Ω) : |partialSum Z ρ ℓ ω| ≤ (ℓ : ℝ) * Real.log 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.Icc 1 ℓ, |logTrunc Z ρ j ω| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.Icc 1 ℓ, Real.log 2 := Finset.sum_le_sum (fun j _ => abs_logTrunc_le Z ρ j ω)
    _ = (ℓ : ℝ) * Real.log 2 := by simp

/-- Good blocks, a good ratio, and a two-sided remaining-interval bound give the
pointwise block approximation at a single outcome. -/
theorem block_error_le_of_good {Ω : Type*}
    (Z : ℝ → ℝ → Ω → MeasureTheory.Measure (Plane × Plane)) (ρ : ℝ)
    {n ℓ : ℕ} (hℓn : ℓ ≤ n) (ω : Ω) {u : ℝ}
    (hdec : Fheat Z (tau ρ n) 0 ω = Real.log (blockQ Z ρ n ℓ ω) +
      Real.log (blockR Z ρ n ℓ ω) + ∑ j ∈ Finset.Ioc ℓ n, Real.log (blockMass Z ρ j ω))
    (hblocks : ∀ j ∈ Finset.Ioc ℓ n, |blockMass Z ρ j ω - 1| ≤ 1 / 2)
    (hR : |blockR Z ρ n ℓ ω - 1| ≤ 1 / 2)
    (hQlo : Real.exp (-u) ≤ blockQ Z ρ n ℓ ω) (hQhi : blockQ Z ρ n ℓ ω ≤ Real.exp u) :
    |Fheat Z (tau ρ n) 0 ω - partialSum Z ρ n ω| ≤
      (ℓ : ℝ) * Real.log 2 + Real.log 2 + u := by
  have hQpos : 0 < blockQ Z ρ n ℓ ω := (Real.exp_pos _).trans_le hQlo
  have hlogQ : |Real.log (blockQ Z ρ n ℓ ω)| ≤ u :=
    abs_le.mpr ⟨(Real.le_log_iff_exp_le hQpos).mpr hQlo,
      (Real.log_le_iff_le_exp hQpos).mpr hQhi⟩
  have hlogR := abs_log_le_log_two hR
  have hs : (∑ j ∈ Finset.Ioc ℓ n, logTrunc Z ρ j ω) =
      ∑ j ∈ Finset.Ioc ℓ n, Real.log (blockMass Z ρ j ω) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact ite_eq_left (hblocks j hj)
  have heq : Fheat Z (tau ρ n) 0 ω - partialSum Z ρ n ω =
      Real.log (blockQ Z ρ n ℓ ω) + Real.log (blockR Z ρ n ℓ ω) - partialSum Z ρ ℓ ω := by
    rw [partialSum_split Z ρ hℓn ω, hs, hdec]
    ring
  rw [heq]
  calc
    _ ≤ |Real.log (blockQ Z ρ n ℓ ω) + Real.log (blockR Z ρ n ℓ ω)| +
        |partialSum Z ρ ℓ ω| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (Real.log (blockQ Z ρ n ℓ ω) + Real.log (blockR Z ρ n ℓ ω))
              (-partialSum Z ρ ℓ ω))
    _ ≤ |Real.log (blockQ Z ρ n ℓ ω)| + |Real.log (blockR Z ρ n ℓ ω)| +
        |partialSum Z ρ ℓ ω| := add_le_add (abs_add_le _ _) le_rfl
    _ ≤ u + Real.log 2 + (ℓ : ℝ) * Real.log 2 :=
      add_le_add (add_le_add hlogQ hlogR) (abs_partialSum_le Z ρ ℓ ω)
    _ = _ := by ring

end Critical2DKPZ.Extensions.ScaleLimit
