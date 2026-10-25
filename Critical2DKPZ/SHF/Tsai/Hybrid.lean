/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeatMollifier
public import Critical2DKPZ.SHF.Tsai.Products

/-! # Hybrid expectations from two independent flows

Splicing one flow before a time and another after it gives a hybrid pairing vector on
the product probability space. At the splice endpoints its nonlinear expectation equals
the corresponding original flow expectation.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The hybrid pairing vector on the coupling `Ω' × Ω`: `Z'` on `[s, c]`, then `Z` on `[c, t]`. -/
def hybridPairing {Ω Ω' : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (s c t : ℝ) (u : Plane → ℝ) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ)) (ω : Ω' × Ω) : Fin m → ℝ :=
  fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(smoothedProductMeasure (Z' s c ω.1) u (Z c t ω.2))

/-- Tsai's `r_i(ℓ)`, with `r = E h(Z f)` at `c = s` and `r = E h(Z' f)` at `c = t`. -/
def hybridValue {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    (P' : Measure Ω') (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (s t : ℝ) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ)) (H : (Fin m → ℝ) → ℝ) (c : ℝ) (ℓ : ℕ) : ℝ :=
  if c = s then ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(Z s t ω)) ∂P
  else if c = t then ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂(Z' s t ω)) ∂P'
  else ∫ ω, H (hybridPairing Z Z' s c t (heatMollifier ℓ) g g' ω) ∂(P'.prod P)

/-- At the initial endpoint the hybrid is the original flow expectation. -/
theorem hybridValue_left {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (s t : ℝ) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ)) (H : (Fin m → ℝ) → ℝ) (ℓ : ℕ) :
    hybridValue P P' Z Z' s t g g' H s ℓ =
      ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z s t ω) ∂P := by
  simp only [hybridValue, ite_true]

/-- At the terminal endpoint the hybrid is the replacement flow expectation. -/
theorem hybridValue_right {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) {s t : ℝ} (hst : s < t) {m r : ℕ}
    (g g' : Fin m → Fin r → C_c(Plane, ℝ)) (H : (Fin m → ℝ) → ℝ) (ℓ : ℕ) :
    hybridValue P P' Z Z' s t g g' H t ℓ =
      ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z' s t ω) ∂P' := by
  simp only [hybridValue, ite_eq_right (ne_of_gt hst), ite_true]

end Critical2DKPZ.SHF.Tsai

end
