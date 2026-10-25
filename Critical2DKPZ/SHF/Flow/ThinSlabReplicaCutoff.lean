/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.CutoffConvergence
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks

/-! # Removing the four middle-coordinate cutoffs of a replica test -/

@[expose] public noncomputable section

open MeasureTheory Filter Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped Topology

namespace Critical2DKPZ.SHF.Flow

/-- The four middle-coordinate cutoffs in the square of a slab connector pairing. -/
def slabReplicaCutoff (R : ℝ) (p : Fin 2 → Configuration 2 × Configuration 2) : ℝ :=
  ∏ i : Fin 2, ballCutoff R ((p 0).2 i) * ballCutoff R ((p 1).1 i)

/-- The replica cutoff is continuous in the path variables. -/
theorem continuous_slabReplicaCutoff (R : ℝ) : Continuous (slabReplicaCutoff R) := by
  apply continuous_finsetProd
  intro i hi
  exact ((continuous_ballCutoff R).comp (by fun_prop)).mul
    ((continuous_ballCutoff R).comp (by fun_prop))

/-- Every replica cutoff lies between zero and one. -/
theorem slabReplicaCutoff_mem_Icc (R : ℝ)
    (p : Fin 2 → Configuration 2 × Configuration 2) :
    slabReplicaCutoff R p ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg fun i _ =>
      mul_nonneg (ballCutoff_mem_Icc R _).1 (ballCutoff_mem_Icc R _).1
  · apply Finset.prod_le_one₀
    · intro i hi
      exact mul_nonneg (ballCutoff_mem_Icc R _).1 (ballCutoff_mem_Icc R _).1
    · intro i hi
      calc
        _ ≤ ballCutoff R ((p 0).2 i) * 1 :=
          mul_le_mul_of_nonneg_left (ballCutoff_mem_Icc R _).2 (ballCutoff_mem_Icc R _).1
        _ ≤ 1 := by simpa only [mul_one] using (ballCutoff_mem_Icc R ((p 0).2 i)).2

/-- The replica cutoff tends pointwise to one as its radius grows. -/
theorem tendsto_slabReplicaCutoff (p : Fin 2 → Configuration 2 × Configuration 2) :
    Tendsto (fun R : ℝ => slabReplicaCutoff R p) atTop (𝓝 1) := by
  have h := tendsto_finsetProd Finset.univ (fun i (_ : i ∈ Finset.univ) =>
    (tendsto_ballCutoff ((p 0).2 i)).mul (tendsto_ballCutoff ((p 1).1 i)))
  simpa only [slabReplicaCutoff, mul_one, Finset.prod_const_one] using h

/-- An integrable continuum path test is recovered by removing the four middle-coordinate
cutoffs. Signed tests are allowed. -/
theorem integral_slabReplicaCutoff_tendsto
    (μ : Measure (Fin 2 → Configuration 2 × Configuration 2))
    {F : (Fin 2 → Configuration 2 × Configuration 2) → ℝ} (hF : Integrable F μ) :
    Tendsto (fun R : ℝ => ∫ p, F p * slabReplicaCutoff R p ∂μ) atTop
      (𝓝 (∫ p, F p ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun p => |F p|)
  · exact Eventually.of_forall fun R => hF.aestronglyMeasurable.mul
      (continuous_slabReplicaCutoff R).aestronglyMeasurable
  · exact Eventually.of_forall fun R => Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (slabReplicaCutoff_mem_Icc R p).1]
      exact (mul_le_mul_of_nonneg_left (slabReplicaCutoff_mem_Icc R p).2
        (abs_nonneg (F p))).trans_eq (mul_one _)
  · exact hF.abs
  · exact Eventually.of_forall fun p => by
      simpa only [mul_one] using
        (tendsto_const_nhds (x := F p)).mul (tendsto_slabReplicaCutoff p)

end Critical2DKPZ.SHF.Flow

end
