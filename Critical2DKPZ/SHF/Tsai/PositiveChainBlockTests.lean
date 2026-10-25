/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainBlockTests

/-! # Nonnegative endpoint tests for a chain block

Integrating out all coordinates except one block gives a nonnegative endpoint test for the
chain pairing. This test expresses the integral of the absolute signed row integrand and
bounds the absolute signed endpoint test.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The positive endpoint test obtained by integrating every path coordinate except one block. -/
def positiveChainBlockTest (K : ℕ) (j : Fin (K + 1)) (μ : ℕ → Measure (Plane × Plane))
    (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ≥0∞) (p : Plane × Plane) : ℝ≥0∞ :=
  ∫⁻ q : Fin K → Plane × Plane, chainPathTest K w F (Fin.insertNth (α := fun _ : Fin (K + 1) => Plane × Plane) j p q)
    ∂Measure.pi (fun i : Fin K => μ (j.succAbove i))

/-- The selected block does not enter the positive endpoint test. -/
theorem positiveChainBlockTest_update (K : ℕ) (j : Fin (K + 1))
    (μ : ℕ → Measure (Plane × Plane)) (ν : Measure (Plane × Plane))
    (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ≥0∞) :
    positiveChainBlockTest K j (Function.update μ j ν) w F = positiveChainBlockTest K j μ w F := by
  classical
  have hμ : (fun i : Fin K => Function.update μ j ν (j.succAbove i)) =
      fun i : Fin K => μ (j.succAbove i) := by
    funext i
    apply Function.update_of_ne
    intro h
    exact (Fin.succAbove_ne j i) (Fin.ext h)
  funext p
  simp only [positiveChainBlockTest, hμ]

/-- Tonelli represents a positive chain pairing as the positive endpoint test of any block. -/
theorem lintegral_chainProduct_eq_lintegral_blockTest (μ : ℕ → Measure (Plane × Plane))
    [∀ k, SigmaFinite (μ k)] {w : ℕ → Plane → ℝ} (hw : ∀ k, Measurable (w k))
    (K : ℕ) (j : Fin (K + 1)) (F : Plane × Plane → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F p ∂chainProduct μ w K) = ∫⁻ p, positiveChainBlockTest K j μ w F p ∂μ j := by
  rw [lintegral_chainProduct_eq_lintegral_path μ hw K hF]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => Plane × Plane) j
  have he := measurePreserving_piFinSuccAbove (fun k : Fin (K + 1) => μ k) j
  have hJ := measurable_chainPathTest K hw hF
  have hcomp := (he.symm e).lintegral_comp hJ
  have hprod := lintegral_prod (μ := μ j)
    (ν := Measure.pi (fun i : Fin K => μ (j.succAbove i)))
    (fun p => chainPathTest K w F (e.symm p)) (hJ.comp e.symm.measurable).aemeasurable
  exact hcomp.symm.trans hprod

/-- The positive endpoint test is measurable for any fixed sigma-finite outer blocks. -/
theorem measurable_positiveChainBlockTest_fixed (μ : ℕ → Measure (Plane × Plane))
    [∀ k, SigmaFinite (μ k)] (K : ℕ) (j : Fin (K + 1))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k))
    (F : Plane × Plane → ℝ≥0∞) (hF : Measurable F) :
    Measurable (positiveChainBlockTest K j μ w F) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => Plane × Plane) j
  have hJ : Measurable (fun pq : (Plane × Plane) × (Fin K → Plane × Plane) =>
      chainPathTest K w F (e.symm pq)) :=
    (measurable_chainPathTest K hw hF).comp e.symm.measurable
  exact hJ.lintegral_prod_right'

/-- The positive slice is exactly the integral of the signed slice's pointwise norm. -/
theorem lintegral_enorm_chainBlockIntegrand_eq (K : ℕ) (j : Fin (K + 1))
    (μ : ℕ → Measure (Plane × Plane)) (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ)
    (p : Plane × Plane) :
    (∫⁻ q : Fin K → Plane × Plane,
      ‖(chainPathTest K w (fun _ => 1) (Fin.insertNth (α := fun _ : Fin (K + 1) => Plane × Plane) j p q)).toReal *
        F (((Fin.insertNth (α := fun _ : Fin (K + 1) => Plane × Plane) j p q) 0).1, ((Fin.insertNth (α := fun _ : Fin (K + 1) => Plane × Plane) j p q) (Fin.last K)).2)‖ₑ
      ∂Measure.pi (fun i : Fin K => μ (j.succAbove i))) =
        positiveChainBlockTest K j μ w (fun p => ENNReal.ofReal |F p|) p := by
  apply lintegral_congr
  intro q
  let r := Fin.insertNth (α := fun _ : Fin (K + 1) => Plane × Plane) j p q
  change ‖(chainPathTest K w (fun _ => 1) r).toReal * F ((r 0).1, (r (Fin.last K)).2)‖ₑ = _
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (chainPathWeight_ne_top K w r), Real.enorm_eq_ofReal_abs]
  simp only [chainPathTest, mul_one]
  rfl


/-- The nonnegative absolute endpoint test bounds the absolute value of the signed endpoint test. -/
theorem ofReal_abs_chainBlockTest_le (K : ℕ) (j : Fin (K + 1))
    (μ : ℕ → Measure (Plane × Plane)) (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ)
    (p : Plane × Plane) :
    ENNReal.ofReal |chainBlockTest K j μ w F p| ≤
      positiveChainBlockTest K j μ w (fun p => ENNReal.ofReal |F p|) p := by
  rw [← Real.enorm_eq_ofReal_abs]
  exact (enorm_integral_le_lintegral_enorm _).trans_eq
    (lintegral_enorm_chainBlockIntegrand_eq K j μ w F p)

end Critical2DKPZ.SHF.Tsai

end
