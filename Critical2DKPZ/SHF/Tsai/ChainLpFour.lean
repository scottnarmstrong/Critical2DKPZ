/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainFourthMomentLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Genuine `L⁴` chain pairings and their approximation seminorms

The first and fourth signed chain moments put each actual pairing in `L⁴`.
Convergence of the fourth moment of an error then gives convergence of its
`L⁴` seminorm by the exact positive fourth-root formula.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Critical2DKPZ.SHF.Tsai

/-- An actual endpoint-chain pairing belongs to `L⁴`, for arbitrary `L²` endpoint representatives. -/
theorem memLp_chainPairing_four {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ)
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    MemLp (fun ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B k ω) (fun k => w k ℓ) K) 4 P := by
  have h1 := (integral_prod_chainProduct_eq K τ hτ B hB hind (n := 1) (by norm_num) (by norm_num)
    (fun _ => w) (fun _ => hw) ℓ (fun _ => g) (fun _ => g') (fun _ => hg) (fun _ => hg')).2.1
  simp only [Fin.prod_univ_one] at h1
  have h4 := (integral_prod_chainProduct_eq K τ hτ B hB hind (n := 4) (by norm_num) (by norm_num)
    (fun _ => w) (fun _ => hw) ℓ (fun _ => g) (fun _ => g') (fun _ => hg) (fun _ => hg')).2.1
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h4
  apply (integrable_norm_rpow_iff h1.aestronglyMeasurable
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)).1
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat, Real.norm_eq_abs,
    Even.pow_abs (show Even 4 from ⟨2, rfl⟩)] using h4

/-- The exact `L⁴` seminorm is the fourth root of the positive fourth moment. -/
theorem eLpNorm_four_eq_integral_pow_four {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {f : Ω → ℝ} (hfm : AEStronglyMeasurable f P) (hI : Integrable (fun ω => f ω ^ 4) P) :
    eLpNorm f 4 P = (ENNReal.ofReal (∫ ω, f ω ^ 4 ∂P)) ^ (1 / 4 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ⊤) hfm]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall (fun ω => (show Even 4 from ⟨2, rfl⟩).pow_nonneg (f ω)))]
  apply lintegral_congr
  intro ω
  rw [ENNReal.rpow_ofNat _ 4, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg (f ω)), Even.pow_abs (show Even 4 from ⟨2, rfl⟩)]

/-- The positive fourth moment equals the fourth power of the `L⁴` seminorm. -/
theorem ofReal_integral_pow_four_eq_eLpNorm_pow_four {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {f : Ω → ℝ} (hfm : AEStronglyMeasurable f P)
    (hI : Integrable (fun ω => f ω ^ 4) P) :
    ENNReal.ofReal (∫ ω, f ω ^ 4 ∂P) = eLpNorm f 4 P ^ (4 : ℕ) := by
  rw [eLpNorm_four_eq_integral_pow_four P hfm hI,
    ← ENNReal.rpow_ofNat _ 4, ← ENNReal.rpow_mul]
  norm_num

/-- Vanishing `L⁴` seminorms imply vanishing integrable fourth moments. -/
theorem tendsto_integral_pow_four_of_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ) (hfm : ∀ j, AEStronglyMeasurable (f j) P)
    (hI : ∀ j, Integrable (fun ω => f j ω ^ 4) P)
    (hlim : Tendsto (fun j => eLpNorm (f j) 4 P) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ ω, f j ω ^ 4 ∂P) atTop (𝓝 0) := by
  have hp : Tendsto (fun j => eLpNorm (f j) 4 P ^ (4 : ℕ)) atTop (𝓝 0) := by
    simpa only [ENNReal.rpow_ofNat, zero_pow (by norm_num : (4 : ℕ) ≠ 0)] using
      hlim.ennrpow_const (4 : ℝ)
  have hr := (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hp
  simp only [ENNReal.toReal_zero, Function.comp_def] at hr
  have heq (j) : (eLpNorm (f j) 4 P ^ (4 : ℕ)).toReal = ∫ ω, f j ω ^ 4 ∂P := by
    rw [← ofReal_integral_pow_four_eq_eLpNorm_pow_four P (hfm j) (hI j),
      ENNReal.toReal_ofReal (integral_nonneg (fun ω =>
        (show Even 4 from ⟨2, rfl⟩).pow_nonneg (f j ω)))]
  simpa only [heq] using hr

/-- Vanishing integrable fourth moments imply convergence of the actual `L⁴` seminorms to zero. -/
theorem tendsto_eLpNorm_four_of_integral_pow_four {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : ℕ → Ω → ℝ) (hfm : ∀ j, AEStronglyMeasurable (f j) P)
    (hI : ∀ j, Integrable (fun ω => f j ω ^ 4) P)
    (hlim : Tendsto (fun j => ∫ ω, f j ω ^ 4 ∂P) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm (f j) 4 P) atTop (𝓝 0) := by
  have hENN := (ENNReal.continuous_ofReal.tendsto 0).comp hlim
  have hroot := hENN.ennrpow_const (1 / 4 : ℝ)
  have heq : (fun j => eLpNorm (f j) 4 P) =
      fun j => (ENNReal.ofReal (∫ ω, f j ω ^ 4 ∂P)) ^ (1 / 4 : ℝ) := by
    funext j
    exact eLpNorm_four_eq_integral_pow_four P (hfm j) (hI j)
  rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero,
    ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] using hroot

end Critical2DKPZ.SHF.Tsai

end
