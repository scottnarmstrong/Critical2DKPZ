/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.LatticeBlockConvergence
import Critical2DKPZ.Provider.BlockMoments
import Critical2DKPZ.Polymer.Profiles
import Mathlib.Tactic

/-! # Uniform lattice moments at a fixed reversed block index -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Centered geometric lattice masses have finite absolute moments. -/
theorem integrable_abs_latticeGeometricMass_sub_pow (ϑ ρ : ℝ) (N a b p : ℕ) :
    Integrable (fun ω => |latticeGeometricMass ϑ ρ N a b ω - 1| ^ p) disorderLaw := by
  have hmem : MemLp (fun ω => latticeGeometricMass ϑ ρ N a b ω - 1) p disorderLaw :=
    (Polymer.memLp_smoothedP2Plane _ _ _ _ p (by simp)).sub (memLp_const 1)
  simpa only [Real.norm_eq_abs] using hmem.integrable_norm_pow'

/-- At every fixed reversed block, the lattice second and fourth moments have
bounds with a single constant chosen before the reversed block index. -/
theorem lattice_geometric_block_moments (ϑ : ℝ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, ∀ᶠ N : ℕ in atTop,
      (∫ ω, (latticeGeometricMass ϑ ρ N (j + 1) j ω - 1) ^ 2 ∂disorderLaw) ≤
        C / (j + 1 : ℕ) ∧
      (∫ ω, |latticeGeometricMass ϑ ρ N (j + 1) j ω - 1| ^ 4 ∂disorderLaw) ≤
        C / (j + 1 : ℕ) ^ 2 := by
  obtain ⟨C, hC⟩ := Provider.blockMoments |ϑ| ρ ρ hρ
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro j
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (f := fun N : ℕ => N) (fun N => by omega) tendsto_id
  have hK := ((Blocks.blockCount_tendsto_atTop hρ).comp h2).eventually_ge_atTop (j + 1)
  have hbound := h2.eventually (hC ρ ⟨le_rfl, le_rfl⟩)
  filter_upwards [hK, hbound] with N hK hN
  let K := blockCount (2 * N) ρ
  change j + 1 ≤ K at hK
  have hi : 1 ≤ K - j := by dsimp [K]; omega
  have hiK : K - j ≤ K := Nat.sub_le _ _
  have hb := hN ϑ ⟨neg_abs_le ϑ, le_abs_self ϑ⟩ (K - j) hi hiK
  have hstart : K - j - 1 = K - (j + 1) := by omega
  have hden : (K : ℝ) + 1 - ((K - j : ℕ) : ℝ) = (j + 1 : ℕ) := by
    rw [Nat.cast_sub (by dsimp [K]; omega)]
    push_cast
    ring
  have hvar : variance (latticeGeometricMass ϑ ρ N (j + 1) j) disorderLaw =
      ∫ ω, (latticeGeometricMass ϑ ρ N (j + 1) j ω - 1) ^ 2 ∂disorderLaw := by
    have hm : AEMeasurable (latticeGeometricMass ϑ ρ N (j + 1) j) disorderLaw :=
      (Polymer.measurable_smoothedP2Plane _ _ _ _).aemeasurable
    rw [variance_eq_integral hm]
    change (∫ ω, (latticeGeometricMass ϑ ρ N (j + 1) j ω -
      ∫ ω', latticeGeometricMass ϑ ρ N (j + 1) j ω' ∂disorderLaw) ^ 2 ∂disorderLaw) = _
    rw [show (∫ ω', latticeGeometricMass ϑ ρ N (j + 1) j ω' ∂disorderLaw) = 1 from
      Polymer.integral_smoothedP2Plane _ _ _ _]
  change variance (fun ω => smoothedP2Plane (criticalBeta ϑ (2 * N))
    (blockTime (2 * N) ρ (K - j - 1)) (blockTime (2 * N) ρ (K - j)) 0 ω) disorderLaw ≤ _ ∧ _ at hb
  rw [hstart, hden] at hb
  change variance (latticeGeometricMass ϑ ρ N (j + 1) j) disorderLaw ≤ _ ∧ _ at hb
  rw [hvar] at hb
  constructor
  · exact hb.1.trans (div_le_div_of_nonneg_right (le_max_left _ _) (by positivity))
  · exact hb.2.trans (div_le_div_of_nonneg_right (le_max_left _ _) (sq_nonneg _))

end Critical2DKPZ.Extensions.ScaleLimit
