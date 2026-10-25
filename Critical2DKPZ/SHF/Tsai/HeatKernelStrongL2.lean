/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeatKernelCompactL2
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Strong heat approximation on spatial `L²`

Planar heat convolution converges strongly to the identity on `L²` as positive times tend
to zero, with contraction controlling approximation by compact continuous tests.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The heat approximation error is controlled by that of a comparison test and twice
its `L²` distance. Integrability and contraction are supplied by `mollifierAction_heat_memLp_and_eLpNorm_le`. -/
theorem eLpNorm_heat_sub_le_of_comparison {t : ℝ} (ht : 0 < t)
    (φ ψ : Plane → ℝ) (hφ : MemLp φ 2) (hψ : MemLp ψ 2) :
    eLpNorm (mollifierAction (heatKernel t) φ - φ) 2 ≤
      2 * eLpNorm (φ - ψ) 2 + eLpNorm (mollifierAction (heatKernel t) ψ - ψ) 2 := by
  let D := φ - ψ
  let E := mollifierAction (heatKernel t) ψ - ψ
  have hfun : mollifierAction (heatKernel t) φ - φ =
      (mollifierAction (heatKernel t) D + E) - D := by
    dsimp only [D, E]
    rw [mollifierAction_sub (memLp_heatKernel ht) hφ hψ]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [hfun]
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hsub := eLpNorm_sub_le (f := mollifierAction (heatKernel t) D + E) (g := D)
    (μ := (volume : Measure Plane)) hp
  have hadd := eLpNorm_add_le (f := mollifierAction (heatKernel t) D) (g := E)
    (μ := (volume : Measure Plane)) hp
  have hcontract := (mollifierAction_heat_memLp_and_eLpNorm_le ht D (hφ.sub hψ)).2
  have hfirst := hsub.trans (add_le_add hadd (le_refl (eLpNorm D 2)))
  have hsecond := add_le_add (add_le_add hcontract (le_refl (eLpNorm E 2)))
    (le_refl (eLpNorm D 2))
  have heq : (eLpNorm D 2 + eLpNorm E 2) + eLpNorm D 2 =
      2 * eLpNorm D 2 + eLpNorm E 2 := by
    rw [two_mul]
    exact add_right_comm _ _ _
  exact (hfirst.trans hsecond).trans_eq heq

/-- Positive heat times tending to zero approximate every actual spatial `L²` representative. -/
theorem tendsto_eLpNorm_heat_sub (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (htlim : Tendsto t atTop (𝓝 0)) (φ : Plane → ℝ) (hφ : MemLp φ 2) :
    Tendsto (fun n => eLpNorm (mollifierAction (heatKernel (t n)) φ - φ) 2) atTop (𝓝 0) := by
  classical
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  have hquarter : 0 < ε / 2 / 2 := ENNReal.half_pos hhalf.ne'
  obtain ⟨ψ, hsupport, happrox, hcont, hmem⟩ :=
    hφ.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hquarter.ne'
  let g : C_c(Plane, ℝ) := ⟨⟨ψ, hcont⟩, hsupport⟩
  have hglim := tendsto_eLpNorm_heat_sub_compact t ht htlim g
  have hevent := (ENNReal.tendsto_nhds_zero.1 hglim) (ε / 2) hhalf
  filter_upwards [hevent] with n hn
  have hcomparison := eLpNorm_heat_sub_le_of_comparison (ht n) φ ψ hφ hmem
  have hsmall : 2 * eLpNorm (φ - ψ) 2 + eLpNorm (mollifierAction (heatKernel (t n)) ψ - ψ) 2 ≤
      2 * (ε / 2 / 2) + ε / 2 := add_le_add (mul_le_mul' (le_refl (2 : ℝ≥0∞)) happrox) hn
  have heq : (2 : ℝ≥0∞) * (ε / 2 / 2) + ε / 2 = ε := by
    rw [two_mul, ENNReal.add_halves, ENNReal.add_halves]
  exact hcomparison.trans (hsmall.trans_eq heq)

end Critical2DKPZ.SHF.Tsai

end
