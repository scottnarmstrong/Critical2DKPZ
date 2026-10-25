/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainPathMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-! # Isolating one block in a signed chain pairing

Split the actual weighted product path at the selected coordinate. Fubini
represents an integrable chain pairing as a linear test of that block. The
test uses only the other block measures and is unchanged by replacement of
the selected block.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- The signed endpoint test of one block obtained by integrating all other path coordinates. -/
def chainBlockTest (K : ℕ) (j : Fin (K + 1)) (μ : ℕ → Measure (Plane × Plane))
    (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ) (p : Plane × Plane) : ℝ :=
  ∫ q : Fin K → Plane × Plane,
    let r := Fin.insertNth j p q
    (chainPathTest K w (fun _ => 1) r).toReal * F ((r 0).1, (r (Fin.last K)).2)
      ∂Measure.pi (fun i : Fin K => μ (j.succAbove i))

/-- The selected block measure does not enter its associated endpoint test. -/
theorem chainBlockTest_update (K : ℕ) (j : Fin (K + 1)) (μ : ℕ → Measure (Plane × Plane))
    (ν : Measure (Plane × Plane)) (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ) :
    chainBlockTest K j (Function.update μ j ν) w F = chainBlockTest K j μ w F := by
  classical
  have hμ : (fun i : Fin K => Function.update μ j ν (j.succAbove i)) =
      fun i : Fin K => μ (j.succAbove i) := by
    funext i
    apply Function.update_of_ne
    intro h
    exact (Fin.succAbove_ne j i) (Fin.ext h)
  funext p
  simp only [chainBlockTest, hμ]

/-- An integrable signed chain pairing is the integrable test of any selected input block. -/
theorem integral_chainProduct_eq_integral_blockTest (μ : ℕ → Measure (Plane × Plane))
    [∀ k, SigmaFinite (μ k)] {w : ℕ → Plane → ℝ} (hw : ∀ k, Measurable (w k))
    (K : ℕ) (j : Fin (K + 1)) (F : Plane × Plane → ℝ) (hF : Integrable F (chainProduct μ w K)) :
    Integrable (chainBlockTest K j μ w F) (μ j) ∧
      (∫ p, F p ∂chainProduct μ w K) = ∫ p, chainBlockTest K j μ w F p ∂μ j := by
  let J (p : Fin (K + 1) → Plane × Plane) :=
    (chainPathTest K w (fun _ => 1) p).toReal * F ((p 0).1, (p (Fin.last K)).2)
  obtain ⟨hJI, hEq⟩ := integral_chainProduct_eq_integral_weightedPath μ hw K F hF
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => Plane × Plane) j
  have he := measurePreserving_piFinSuccAbove (fun k : Fin (K + 1) => μ k) j
  have hsplit : Integrable (J ∘ e.symm)
      ((μ j).prod (Measure.pi (fun i : Fin K => μ (j.succAbove i)))) :=
    ((he.symm e).integrable_comp_emb e.symm.measurableEmbedding).2 hJI
  have hrow (p : Plane × Plane) : (∫ q : Fin K → Plane × Plane, J (e.symm (p, q))
      ∂Measure.pi (fun i : Fin K => μ (j.succAbove i))) = chainBlockTest K j μ w F p := by
    rfl
  have houter := hsplit.integral_prod_left
  refine ⟨?_, ?_⟩
  · exact houter.congr (Filter.Eventually.of_forall hrow)
  · have hcomp := (he.symm e).integral_comp e.symm.measurableEmbedding J
    have hprod := integral_prod (μ := μ j)
      (ν := Measure.pi (fun i : Fin K => μ (j.succAbove i))) (J ∘ e.symm) hsplit
    have hlast : (∫ p, ∫ q : Fin K → Plane × Plane, J (e.symm (p, q))
        ∂Measure.pi (fun i : Fin K => μ (j.succAbove i)) ∂μ j) =
        ∫ p, chainBlockTest K j μ w F p ∂μ j :=
      integral_congr_ae (Filter.Eventually.of_forall hrow)
    exact hEq.trans (hcomp.symm.trans (hprod.trans hlast))

end Critical2DKPZ.SHF.Tsai

end
