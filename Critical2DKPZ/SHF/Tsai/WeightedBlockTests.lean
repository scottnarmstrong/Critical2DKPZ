/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.WeightedTranslateAveraging
public import Critical2DKPZ.SHF.Tsai.BlockMarginals

/-! # Spatial `L²` tests obtained from a weighted block

Weighting the initial marginal by the absolute endpoint test gives a finite
measure. Its bounded signed coefficient recovers the actual signed pairing.
Finite translate averaging proves spatial `L²` membership and absolute row
integrability, including for the random outer blocks of the merge argument.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- A block with finite absolute initial marginal mass produces an actual spatial `L²` test.
The conclusion includes almost-everywhere absolute convergence of the defining rows. -/
theorem memLp_weighted_block_left_test (A : Measure (Plane × Plane))
    (g : Plane → ℝ) (hg : Measurable g)
    (hM : (∫⁻ p, ENNReal.ofReal |g p.1| ∂A) < ⊤)
    (w : Plane → ℝ) (hwm : Measurable w) (hw : MemLp w 2) :
    MemLp (fun y => ∫ p, g p.1 * w (p.2 - y) ∂A) 2 ∧
    (∀ᵐ y ∂volume, Integrable (fun p : Plane × Plane => g p.1 * w (p.2 - y)) A) := by
  simpa only [Function.comp_def] using memLp_weighted_translate_average A Prod.snd measurable_snd
    (fun p : Plane × Plane => g p.1) (hg.comp measurable_fst) hM w hwm hw

/-- An outer moment block gives an actual spatial `L²` test almost surely. -/
theorem HasDeltaBoseMoments.ae_memLp_weighted_left_test {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ) (g : C_c(Plane, ℝ))
    (w : Plane → ℝ) (hwm : Measurable w) (hw : MemLp w 2) :
    ∀ᵐ ω ∂P, MemLp (fun y => ∫ p, g p.1 * w (p.2 - y) ∂B ω) 2 ∧
      ∀ᵐ y ∂volume, Integrable (fun p : Plane × Plane => g p.1 * w (p.2 - y)) (B ω) := by
  filter_upwards [hB.ae_initial_marginal_mass_lt_top hτ g] with ω hω
  exact memLp_weighted_block_left_test (B ω) g (map_continuous g).measurable hω w hwm hw

/-- The terminally weighted block yields the reflected spatial `L²` test,
with absolute convergence of almost every row. -/
theorem memLp_weighted_block_right_test (A : Measure (Plane × Plane))
    (g : Plane → ℝ) (hg : Measurable g)
    (hM : (∫⁻ p, ENNReal.ofReal |g p.2| ∂A) < ⊤)
    (w : Plane → ℝ) (hwm : Measurable w) (hw : MemLp w 2) :
    MemLp (fun y => ∫ p, w (y - p.1) * g p.2 ∂A) 2 ∧
    (∀ᵐ y ∂volume, Integrable (fun p : Plane × Plane => w (y - p.1) * g p.2) A) := by
  have hwr : MemLp (fun x : Plane => w (-x)) 2 :=
    hw.comp_measurePreserving (Measure.measurePreserving_neg volume)
  have h := memLp_weighted_translate_average A Prod.fst measurable_fst
    (fun p : Plane × Plane => g p.2) (hg.comp measurable_snd) hM
    (fun x => w (-x)) (hwm.comp measurable_neg) hwr
  simpa only [neg_sub, mul_comm] using h

/-- The terminal test from an outer moment block belongs to spatial `L²` almost surely. -/
theorem HasDeltaBoseMoments.ae_memLp_weighted_right_test {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ) (g : C_c(Plane, ℝ))
    (w : Plane → ℝ) (hwm : Measurable w) (hw : MemLp w 2) :
    ∀ᵐ ω ∂P, MemLp (fun y => ∫ p, w (y - p.1) * g p.2 ∂B ω) 2 ∧
      ∀ᵐ y ∂volume, Integrable (fun p : Plane × Plane => w (y - p.1) * g p.2) (B ω) := by
  filter_upwards [hB.ae_terminal_marginal_mass_lt_top hτ g] with ω hω
  exact memLp_weighted_block_right_test (B ω) g (map_continuous g).measurable hω w hwm hw

end Critical2DKPZ.SHF.Tsai

end
