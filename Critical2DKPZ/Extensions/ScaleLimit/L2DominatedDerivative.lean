/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.L2DominatedLimit
public import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! # Differentiating explicitly represented L2 curves -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A pointwise derivative and a square-integrable local slope bound give
an L2 derivative. All representative and domination requirements are explicit. -/
theorem hasDerivAt_L2_of_dominated_slope {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (μ : Measure α) (F : ℝ → Lp E 2 μ) (G : Lp E 2 μ)
    (f : ℝ → α → E) (g : α → E) (r : ℝ)
    (hF : ∀ᶠ q in 𝓝 r, (F q : α → E) =ᵐ[μ] f q)
    (hFr : (F r : α → E) =ᵐ[μ] f r) (hG : (G : α → E) =ᵐ[μ] g)
    {B : α → ℝ} (hB : Integrable B μ)
    (hbound : ∀ᶠ q in 𝓝[≠] r, ∀ᵐ ξ ∂μ,
      ‖slope (fun t => f t ξ) r q - g ξ‖ ^ 2 ≤ B ξ)
    (hder : ∀ᵐ ξ ∂μ, HasDerivAt (fun t => f t ξ) (g ξ) r) :
    HasDerivAt F G r := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply tendsto_L2_of_dominated_sq μ (slope F r) G
    (fun q ξ => slope (fun t => f t ξ) r q) g _ hG hB hbound
    (hder.mono fun _ h => h.tendsto_slope)
  filter_upwards [hF.filter_mono nhdsWithin_le_nhds] with q hFq
  simp only [slope_def_module]
  filter_upwards [Lp.coeFn_smul (q - r)⁻¹ (F q - F r), Lp.coeFn_sub (F q) (F r),
    hFq, hFr] with ξ hs hsub hq hr
  change ((q - r)⁻¹ • (F q - F r)) ξ = (q - r)⁻¹ • (f q ξ - f r ξ)
  change ((q - r)⁻¹ • (F q - F r)) ξ = (q - r)⁻¹ • (F q - F r) ξ at hs
  change (F q - F r) ξ = F q ξ - F r ξ at hsub
  rw [hs, hsub, hq, hr]

end Critical2DKPZ.Extensions.ScaleLimit
