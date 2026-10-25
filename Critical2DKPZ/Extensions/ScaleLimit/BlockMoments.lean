/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockIndependence
public import Critical2DKPZ.Extensions.ScaleLimit.LatticeBlockMoments
import Critical2DKPZ.Extensions.ScaleLimit.DistributionBounds
import Mathlib.Tactic

/-! # Second and fourth moments of geometric flow blocks

The lattice constant is fixed before the block index. At each fixed index,
nonnegative continuous moments pass to the flow by Portmanteau and Fatou.
No convergence of moments or uniform integrability is asserted.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A single lattice block converges to the corresponding positive-index flow block. -/
theorem lattice_blockMass_tendsto (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (j : ℕ) :
    TendstoInDistribution (fun N => latticeGeometricMass ϑ ρ N (j + 1) j) atTop
      (blockMass Z ρ (j + 1)) (fun _ => disorderLaw) P := by
  have h := latticeGeometricMass_joint_tendsto ϑ P Z hZ hρ 1
    (fun _ => j + 1) (fun _ => j) (fun _ => Nat.lt_succ_self j)
  convert! h.continuous_comp (continuous_apply (0 : Fin 1)) using 1

/-- Uniform second and fourth centered moments for all positive-index blocks. -/
theorem block_moments (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      Integrable (fun ω => (blockMass Z ρ (j + 1) ω - 1) ^ 2) P ∧
      Integrable (fun ω => (blockMass Z ρ (j + 1) ω - 1) ^ 4) P ∧
      (∫ ω, (blockMass Z ρ (j + 1) ω - 1) ^ 2 ∂P) ≤ C / (j + 1 : ℕ) ∧
      (∫ ω, (blockMass Z ρ (j + 1) ω - 1) ^ 4 ∂P) ≤ C / (j + 1 : ℕ) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := lattice_geometric_block_moments ϑ hρ
  refine ⟨C, hC0, ?_⟩
  intro j
  have hdist := lattice_blockMass_tendsto ϑ P Z hZ hρ j
  have hi2 : ∀ N, Integrable
      (fun ω => (latticeGeometricMass ϑ ρ N (j + 1) j ω - 1) ^ 2) disorderLaw := by
    intro N
    simpa only [sq_abs] using integrable_abs_latticeGeometricMass_sub_pow ϑ ρ N (j + 1) j 2
  have hi4 : ∀ N, Integrable
      (fun ω => (latticeGeometricMass ϑ ρ N (j + 1) j ω - 1) ^ 4) disorderLaw := by
    intro N
    simpa only [(show Even 4 from by decide).pow_abs] using
      integrable_abs_latticeGeometricMass_sub_pow ϑ ρ N (j + 1) j 4
  have h2 := integral_continuous_nonneg_le_of_tendstoInDistribution hdist
    (fun z : ℝ => (z - 1) ^ 2) (by fun_prop) (fun z => sq_nonneg _)
    (C / (j + 1 : ℕ)) (Filter.Eventually.of_forall hi2) ((hC j).mono fun N hN => hN.1)
  have hb4 : ∀ᶠ N : ℕ in atTop,
      (∫ ω, (latticeGeometricMass ϑ ρ N (j + 1) j ω - 1) ^ 4 ∂disorderLaw) ≤
        C / (j + 1 : ℕ) ^ 2 := by
    simpa only [(show Even 4 from by decide).pow_abs] using (hC j).mono (fun N hN => hN.2)
  have h4 := integral_continuous_nonneg_le_of_tendstoInDistribution hdist
    (fun z : ℝ => (z - 1) ^ 4) (by fun_prop) (fun z => (show Even 4 from by decide).pow_nonneg _)
    (C / (j + 1 : ℕ) ^ 2) (Filter.Eventually.of_forall hi4) hb4
  exact ⟨h2.1, h4.1, h2.2, h4.2⟩

end Critical2DKPZ.Extensions.ScaleLimit
