/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.ShfPairing
public import Critical2DKPZ.Definitions.KpzLatticeReversed
public import Critical2DKPZ.Definitions.KpzLatticeReversedReg
public import Critical2DKPZ.Definitions.TestFn
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Basic joint-convergence identities

Truncated logarithms and time reversal identities used by the fixed-width approximation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.JointConvergence

/-- The quantitative lattice approximation estimate for regularized tested fields. -/
def ExtensionApproxBound : Prop := ∀ (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (a b A : ℝ), 0 < a → a ≤ b →
  ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ ϑ ∈ Set.Icc (-A) A, ∀ t T : ℝ, 0 ≤ t →
        T - t ∈ Set.Icc a b → ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          eLpNorm (fun ω => ∫ x, φ x * (kpzLatticeReversed ϑ N t T h₀ x ω -
              kpzLatticeReversedReg ϑ N t T δ h₀ x ω)) 2 disorderLaw ≤
            ENNReal.ofReal (C * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε)

/-- The truncated logarithm clamps the logarithm to a bounded interval. -/
def logTrunc (R u : ℝ) : ℝ := max (-R) (min (Real.log u) R)


/-- Reversing the SHF time interval and swapping coordinates exchanges the two test functions. -/
theorem shfPairing_reverse {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (T s t : ℝ)
    (f g : Plane → ℝ) (ω : Ω) :
    shfPairing Z s t f g ω =
      shfPairing (fun s' t' ω' => (Z (T - t') (T - s') ω').map Prod.swap)
        (T - t) (T - s) g f ω := by
  simp only [shfPairing, sub_sub_cancel]
  change (∫ p, f p.1 * g p.2 ∂Z s t ω) =
    ∫ p, g p.1 * f p.2 ∂(Z s t ω).map
      (MeasurableEquiv.prodComm : Plane × Plane ≃ᵐ Plane × Plane)
  rw [integral_map_equiv]
  change (∫ p, f p.1 * g p.2 ∂Z s t ω) =
    ∫ p, g (Prod.swap p).1 * f (Prod.swap p).2 ∂Z s t ω
  simp only [Prod.fst_swap, Prod.snd_swap]
  congr 1
  ext p
  ring_nf

end Critical2DKPZ.JointConvergence

end
