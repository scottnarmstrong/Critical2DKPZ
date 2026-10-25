/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CenteredThreeBlockLimits
public import Critical2DKPZ.SHF.Tsai.CompactMomentTests
import Critical2DKPZ.SHF.Tsai.FourthMomentSumLimits

/-! # The deterministic limit of the full interior Taylor remainder

The fourth power of each tensor sum expands into ordered fourfold products.
Their limits are the centered middle-kernel forms on compact-tensor semigroup
tests. The resulting deterministic finite sum is the actual nonnegative limit
of the integrable Taylor remainder for every applicable connector family.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The explicit finite centered-kernel form that is the limit of a three-block fourth remainder. -/
def centeredThreeBlockFourthLimit (θ : ℝ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ 2, 0 < τ k)
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ)) : ℝ :=
  ∑ a, ∑ q : Fin 4 → Fin r, ∫ x, ∫ y,
    momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega)) (fun i => g a (q i)) x *
      centeredMomentKernel 4 θ (τ 1) x y *
        momentTensorTest (by decide : 4 ≤ 4) θ (hτ 2 le_rfl) (fun i => g' a (q i)) y


/-- The full centered fourth remainder converges to its deterministic kernel form, with integrability and nonnegativity. -/
theorem tendsto_integral_sum_centeredThreeBlockPairings_four {θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ 2, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ 2, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin 3 => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k))
    {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ)) :
    0 ≤ centeredThreeBlockFourthLimit θ τ hτ g g' ∧
    (∀ ℓ, Integrable (fun ω => ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) 2) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) 1 (heatBlock (τ 1))) (fun k => w k ℓ) 2) ^ 4) P) ∧
    Tendsto (fun ℓ => ∫ ω, ∑ a, ((∑ b, ∫ p, g a b p.1 * g' a b p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) 2) -
      ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) 1 (heatBlock (τ 1))) (fun k => w k ℓ) 2) ^ 4 ∂P)
      atTop (𝓝 (centeredThreeBlockFourthLimit θ τ hτ g g')) := by
  classical
  let X (ℓ : ℕ) (a : Fin m) (b : Fin r) (ω : Ω) :=
    (∫ p, g a b p.1 * g' a b p.2 ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) 2) -
      ∫ p, g a b p.1 * g' a b p.2 ∂chainProduct
        (Function.update (fun k => B k ω) 1 (heatBlock (τ 1))) (fun k => w k ℓ) 2
  let L (a : Fin m) (q : Fin 4 → Fin r) := ∫ x, ∫ y,
    momentTensorTest (by decide : 4 ≤ 4) θ (hτ 0 (by omega)) (fun i => g a (q i)) x *
      centeredMomentKernel 4 θ (τ 1) x y *
        momentTensorTest (by decide : 4 ≤ 4) θ (hτ 2 le_rfl) (fun i => g' a (q i)) y
  have hI (ℓ : ℕ) (a : Fin m) (q : Fin 4 → Fin r) :
      Integrable (fun ω => ∏ i, X ℓ a (q i) ω) P :=
    (integral_prod_centeredChainPairings_eq 2 1 (by omega) τ hτ B hB hind
      (n := 4) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw) ℓ
      (fun i => g a (q i)) (fun i => g' a (q i))
      (fun i => (g a (q i)).continuous.memLp_of_hasCompactSupport (g a (q i)).hasCompactSupport)
      (fun i => (g' a (q i)).continuous.memLp_of_hasCompactSupport (g' a (q i)).hasCompactSupport)).1
  have hConv (a : Fin m) (q : Fin 4 → Fin r) :
      Tendsto (fun ℓ => ∫ ω, ∏ i, X ℓ a (q i) ω ∂P) atTop (𝓝 (L a q)) :=
    tendsto_integral_prod_centeredThreeBlockPairings τ hτ B hB hind (n := 4) (by norm_num) (by norm_num)
      (fun _ => w) (fun _ => hw) (fun i => g a (q i)) (fun i => g' a (q i))
      (fun i => (g a (q i)).continuous.memLp_of_hasCompactSupport (g a (q i)).hasCompactSupport)
      (fun i => (g' a (q i)).continuous.memLp_of_hasCompactSupport (g' a (q i)).hasCompactSupport)
  have hData := tendsto_integral_sum_sum_pow_four_of_mixed_limits P X L hI hConv
  have hNonneg : 0 ≤ ∑ a, ∑ q, L a q := ge_of_tendsto hData.2
    (Eventually.of_forall (fun ℓ => integral_nonneg (fun ω =>
      Finset.sum_nonneg (fun a _ => (show Even 4 from ⟨2, rfl⟩).pow_nonneg _))))
  simpa only [X, L, Finset.sum_sub_distrib, centeredThreeBlockFourthLimit] using And.intro hNonneg hData

end Critical2DKPZ.SHF.Tsai

end
