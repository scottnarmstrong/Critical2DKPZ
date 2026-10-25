/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.LatticeBlockConvergence
import Critical2DKPZ.Extensions.ScaleLimit.LatticeProfileBounds
import Mathlib.Tactic

/-! # Remaining-interval lattice tails in reversed block coordinates -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The remaining lattice interval, relative to its accumulated past mass. -/
def latticeBlockQ (ϑ ρ : ℝ) (N n ℓ : ℕ) (ω : Disorder) : ℝ :=
  latticeGeometricMass ϑ ρ N n 0 ω / latticeGeometricMass ϑ ρ N n ℓ ω

/-- Each lattice ratio is positive, including the harmless initial sizes. -/
theorem latticeBlockQ_pos (ϑ ρ : ℝ) (N n ℓ : ℕ) (ω : Disorder) :
    0 < latticeBlockQ ϑ ρ N n ℓ ω :=
  div_pos (Polymer.smoothedP2Plane_pos _ _ _ _ _) (Polymer.smoothedP2Plane_pos _ _ _ _ _)

/-- Uniform lattice tail bounds, with fixed reversed endpoints before the
lattice-size limit. The constants do not depend on either reversed endpoint. -/
theorem latticeBlockQ_tail_bounds (ϑ : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ (C : ℝ) (ℓ₀ : ℕ),
      ∀ n ℓ : ℕ, ℓ₀ ≤ ℓ → ℓ < n → ∀ u : ℝ, 0 ≤ u → ∀ᶠ N : ℕ in atTop,
        disorderLaw {ω | latticeBlockQ ϑ ρ N n ℓ ω < Real.exp (-u)} ≤
          ENNReal.ofReal (C / ℓ + C * ℓ * Real.exp (-u)) ∧
        disorderLaw {ω | Real.exp u < latticeBlockQ ϑ ρ N n ℓ ω} ≤
          ENNReal.ofReal (Real.exp (-u)) := by
  obtain ⟨ρ₀, hρ₀, htail⟩ := lattice_lastInterval_log_tail |ϑ|
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  obtain ⟨C, ℓ₀, hC⟩ := htail ρ
  refine ⟨C, max ℓ₀ 1, ?_⟩
  intro n ℓ hℓ hℓn u hu
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (f := fun N : ℕ => N) (fun N => by omega) tendsto_id
  have hbound := h2.eventually (hC ρ ⟨hρ, le_rfl⟩)
  have hK := ((Blocks.blockCount_tendsto_atTop hρ1).comp h2).eventually_ge_atTop n
  filter_upwards [hbound, hK] with N hN hnK
  change n ≤ blockCount (2 * N) ρ at hnK
  let K := blockCount (2 * N) ρ
  have hKpos : K ≠ 0 := by dsimp [K]; omega
  have hKtime : blockTime (2 * N) ρ K = 2 * N := by
    rw [blockTime, ite_eq_right hKpos, ite_eq_right (lt_irrefl _)]
  have hindex : K - n + ℓ + 1 ≤ K := by dsimp [K]; omega
  have ht := hN ϑ ⟨neg_abs_le ϑ, le_abs_self ϑ⟩ (K - n) ℓ
    ((le_max_left _ _).trans hℓ) hindex u hu
  have hQeq (ω : Disorder) : latticeBlockQ ϑ ρ N n ℓ ω =
      smoothedP2Plane (criticalBeta ϑ (2 * N)) (blockTime (2 * N) ρ (K - n)) (2 * N) 0 ω /
        smoothedP2Plane (criticalBeta ϑ (2 * N)) (blockTime (2 * N) ρ (K - n))
          (blockTime (2 * N) ρ (K - ℓ)) 0 ω := by
    change smoothedP2Plane (criticalBeta ϑ (2 * N)) (blockTime (2 * N) ρ (K - n))
      (blockTime (2 * N) ρ K) 0 ω /
      smoothedP2Plane (criticalBeta ϑ (2 * N)) (blockTime (2 * N) ρ (K - n))
        (blockTime (2 * N) ρ (K - ℓ)) 0 ω = _
    rw [hKtime]
  have hlow : {ω | latticeBlockQ ϑ ρ N n ℓ ω < Real.exp (-u)} =
      {ω | Real.log (latticeBlockQ ϑ ρ N n ℓ ω) < -u} := by
    ext ω
    exact (Real.log_lt_iff_lt_exp (latticeBlockQ_pos ϑ ρ N n ℓ ω)).symm
  have hupp : {ω | Real.exp u < latticeBlockQ ϑ ρ N n ℓ ω} =
      {ω | u < Real.log (latticeBlockQ ϑ ρ N n ℓ ω)} := by
    ext ω
    exact (Real.lt_log_iff_exp_lt (latticeBlockQ_pos ϑ ρ N n ℓ ω)).symm
  constructor
  · rw [hlow]
    simp_rw [hQeq]
    rw [← ENNReal.ofReal_toReal (measure_ne_top disorderLaw _)]
    exact ENNReal.ofReal_le_ofReal ht.1
  · rw [hupp]
    simp_rw [hQeq]
    rw [← ENNReal.ofReal_toReal (measure_ne_top disorderLaw _)]
    exact ENNReal.ofReal_le_ofReal ht.2

end Critical2DKPZ.Extensions.ScaleLimit
