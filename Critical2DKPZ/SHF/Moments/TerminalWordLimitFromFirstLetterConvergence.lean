/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminal
public import Critical2DKPZ.SHF.Moments.SinglePairWordTerminal
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! # The empty-word base of the fixed-start induction -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- At moving positive clocks and moving starting configurations, the empty-word
terminal functional converges to the free heat semigroup on tensor tests. -/
theorem tendsto_wordTerminalTest_nil_tensor {h : ℕ} (σN : ℕ → ℝ) (θ : ℝ)
    {τ : ℝ} (hτ : 0 < τ) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → Fin h → Site) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop,
      Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (ψ : Fin h → C_c(Plane, ℝ)) :
    Tendsto (fun N => wordTerminalTest N (σN N) [] (nN N) (xN N)
      (fun y => ∏ i, ψ i (y i))) atTop
      (𝓝 (∫ y : Configuration h, (∏ i, ψ i (y i)) *
        (diagramKernel θ [] τ x y).toReal)) := by
  classical
  have hwalk (i : Fin h) : Tendsto (fun N =>
      ∑ z ∈ endpoints (xN N i) (nN N),
        srwKernel (nN N) (z - xN N i) * ψ i (latticeRepresentative N z)) atTop
      (𝓝 (∫ z : Plane, ψ i z * heatKernel τ (z - x i))) := by
    have hi := tendsto_terminalWalkTest_moving hτ nN hn
      (fun N => xN N i) (x i) (hx i) (hphase i) (ψ i)
    apply hi.congr'
    filter_upwards with N
    apply Finset.sum_congr rfl
    intro z hz
    exact mul_comm _ _
  have hprod := tendsto_finsetProd Finset.univ (fun i hi => hwalk i)
  have htarget :
      (∫ y : Configuration h, (∏ i, ψ i (y i)) *
        (diagramKernel θ [] τ x y).toReal) =
      ∏ i : Fin h, ∫ z : Plane, ψ i z * heatKernel τ (z - x i) := by
    have hkernel (y : Configuration h) :
        (diagramKernel θ [] τ x y).toReal = freeKernel h τ x y := by
      rw [diagramKernel, ENNReal.toReal_ofReal (freeKernel_pos h hτ x y).le]
    simp_rw [hkernel]
    simp only [freeKernel, ← Finset.prod_mul_distrib]
    exact integral_fintype_prod_volume_eq_prod
      (fun i z => ψ i z * heatKernel τ (z - x i))
  rw [htarget]
  apply hprod.congr'
  filter_upwards with N
  exact (wordTerminalTest_nil_tensor N (σN N) (nN N) (xN N) (fun i => ψ i)).symm



end Critical2DKPZ.SHF.Moments
