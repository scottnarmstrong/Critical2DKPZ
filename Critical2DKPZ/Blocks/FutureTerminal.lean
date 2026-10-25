/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.FiniteProfileMoments
public import Critical2DKPZ.Blocks.BlockResampling
import Mathlib.Tactic

/-! # Annealing a slab while freezing a random future terminal profile -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Blocks

/-- Finite signed incoming data with fourth-moment random terminal data give a square-integrable mass. -/
theorem memLp_two_finite_randomTerminalProfile (β : ℝ) (a n : ℕ)
    (A : Finset Site) (ν : Site → ℝ) (f : Disorder → Site → ℝ)
    (hf : ∀ z, MemLp (fun ω => f ω z) 4 disorderLaw) :
    MemLp (fun ω => ∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z ω * f ω z))
      2 disorderLaw := by
  apply memLp_finsetSum
  intro w _
  apply MemLp.const_mul
  have heq : (fun ω => ∑' z, pointToPoint β a n w z ω * f ω z) =
      (fun ω => ∑ z ∈ Polymer.endpoints w n, pointToPoint β a n w z ω * f ω z) := by
    funext ω
    apply tsum_eq_sum
    intro z hz
    rw [Polymer.pointToPoint_eq_zero_of_not_mem β a n w z ω hz, zero_mul]
  rw [heq]
  apply memLp_finsetSum
  intro z _
  exact Polymer.memLp_mul_double 2
    (by convert Polymer.memLp_pointToPoint β a n w z 4 (by norm_num) using 1; norm_num)
    (by convert hf z using 1; norm_num)

/-- Independently resampling a time slab while keeping the future terminal profile fixed preserves
the second moment, and the resulting iterated integral is integrable. -/
theorem finite_randomTerminalProfile_sq_integral_anneal (β : ℝ) (a n T : ℕ)
    (A : Finset Site) (ν : Site → ℝ) (f : Disorder → Site → ℝ)
    (hfm : ∀ z, Measurable[Gaussian.disorderBlock (a + n) T] (fun ω => f ω z))
    (hf : ∀ z, MemLp (fun ω => f ω z) 4 disorderLaw) :
    Integrable (fun ω => ∫ η,
      (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z η * f ω z)) ^ 2 ∂disorderLaw)
      disorderLaw ∧
    (∫ ω, (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z ω * f ω z)) ^ 2
      ∂disorderLaw) =
      ∫ ω, ∫ η, (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z η * f ω z)) ^ 2
        ∂disorderLaw ∂disorderLaw := by
  let X : Disorder → ℝ := fun ω =>
    (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z ω * f ω z)) ^ 2
  have hfglobal (z) : Measurable (fun ω => f ω z) :=
    (hfm z).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hXm : Measurable X := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro w _
    apply Measurable.const_mul
    exact Measurable.tsum fun z => (Polymer.measurable_pointToPoint β a n w z).mul (hfglobal z)
  have hX : Integrable X disorderLaw := by
    have h := (memLp_two_finite_randomTerminalProfile β a n A ν f hf).integrable_norm_pow'
    simpa only [X, Real.norm_eq_abs, sq_abs] using h
  have hresample (ω η : Disorder) :
      X (Gaussian.resample (Gaussian.timeBlock (a + n) T) ω η) =
      (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z η * f ω z)) ^ 2 := by
    apply congrArg (fun q : ℝ => q ^ 2)
    apply Finset.sum_congr rfl
    intro w _
    apply congrArg (fun q : ℝ => ν w * q)
    apply tsum_congr
    intro z
    rw [blockMeasurable_resample_earlier le_rfl
      (Polymer.measurable_pointToPoint_block β a n w z),
      blockMeasurable_resample_keep (hfm z)]
  have hce := Gaussian.condExp_disorderBlock_ae_eq (a + n) T hXm hX
  have hce' : disorderLaw[X | Gaussian.disorderBlock (a + n) T] =ᵐ[disorderLaw]
      (fun ω => ∫ η,
        (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z η * f ω z)) ^ 2 ∂disorderLaw) := by
    simpa only [hresample] using hce
  refine ⟨integrable_condExp.congr hce', ?_⟩
  calc
    _ = ∫ ω, ∫ η, X (Gaussian.resample (Gaussian.timeBlock (a + n) T) ω η)
        ∂disorderLaw ∂disorderLaw :=
      (integral_integral_resample_block (a + n) T X hXm hX).symm
    _ = _ := by simp only [hresample]

end Critical2DKPZ.Blocks
