/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.KernelLimit
public import Critical2DKPZ.Definitions.RescaledP2P
public import Critical2DKPZ.Polymer.Moments
import Critical2DKPZ.Analysis.Lattice.Basic
import Mathlib.Tactic

/-! # First moments under diffusive rescaling

Even ceilings determine the time intervals and nearest-even cells determine the spatial sampling; the annealed kernel converges to the planar heat kernel. -/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- Taking the diffusive lattice representative preserves subtraction. -/
theorem latticeRepresentative_sub (N : ℕ) (z w : Site) :
    latticeRepresentative N (z - w) = latticeRepresentative N z - latticeRepresentative N w := by
  have h : siteToPlane (z - w) = siteToPlane z - siteToPlane w := by
    ext i
    change ((z i - w i : ℤ) : ℝ) = (z i : ℝ) - (w i : ℝ)
    exact Int.cast_sub _ _
  simp only [latticeRepresentative, h, smul_sub]

/-- The natural difference of two even rounded clocks is even. -/
theorem even_evenCeil_sub (s t : ℝ) : Even (evenCeil t - evenCeil s) := by
  refine ⟨⌈t / 2⌉₊ - ⌈s / 2⌉₊, ?_⟩
  unfold evenCeil
  omega

/-- The difference of two lattice sampling sites has the correct parity for every even time. -/
theorem latticePoint_gap_phase (N n : ℕ) (hn : Even n) (x y : Plane) :
    Even ((latticePoint N y - latticePoint N x) 0 +
      (latticePoint N y - latticePoint N x) 1 + (n : ℤ)) := by
  have hx : Even (latticePoint N x 0 + latticePoint N x 1) := latticePoint_mem_evenLattice N x
  have hy : Even (latticePoint N y 0 + latticePoint N y 1) := latticePoint_mem_evenLattice N y
  have hn' : Even (n : ℤ) := by exact_mod_cast hn
  convert (hy.sub hx).add hn' using 1
  simp only [Pi.sub_apply]
  ring

/-- The expectation of the rescaled polymer density equals the rescaled walk kernel. -/
theorem integral_rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ) (p : Plane × Plane) :
    (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) =
      (N : ℝ) / 4 * srwKernel (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
        (latticePoint N p.2 - latticePoint N p.1) := by
  change (∫ ω, (N : ℝ) / 4 * pointToPoint _ _ _ _ _ ω ∂disorderLaw) = _
  rw [integral_const_mul, Polymer.integral_pointToPoint]

/-- At nonnegative ordered times, the annealed rescaled kernel converges to the planar heat kernel. -/
theorem tendsto_integral_rescaledP2P (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (p : Plane × Plane) :
    Tendsto (fun N : ℕ => ∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw)
      atTop (𝓝 (heatKernel (t - s) (p.2 - p.1))) := by
  simp_rw [integral_rescaledP2P]
  apply tendsto_scaled_srwKernel (sub_pos.mpr hst) (tendsto_evenCeil_gap_div hs hst.le)
  · simp_rw [latticeRepresentative_sub]
    exact (tendsto_cellSample p.2).sub (tendsto_cellSample p.1)
  · exact Filter.Eventually.of_forall fun N => latticePoint_gap_phase N _
      (even_evenCeil_sub _ _) p.1 p.2

end Critical2DKPZ.SHF.Moments
