/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Products
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Positive path tests for endpoint chains

A path contains one endpoint pair for each input block. Its weight is the
product of the connectors, and its test retains the two outer endpoints.
Appending the final block produces exactly the endpoint-product recursion.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The actual connector-weighted endpoint test on a finite sequence of block pairs. -/
def chainPathTest (K : ℕ) (w : ℕ → Plane → ℝ) (H : Plane × Plane → ℝ≥0∞)
    (p : Fin (K + 1) → Plane × Plane) : ℝ≥0∞ :=
  (∏ k : Fin K, ENNReal.ofReal (w k ((p k.castSucc).2 - (p k.succ).1))) *
    H ((p 0).1, (p (Fin.last K)).2)

/-- The literal path weight is measurable. -/
theorem measurable_chainPathTest (K : ℕ) {w : ℕ → Plane → ℝ}
    (hw : ∀ k, Measurable (w k)) {H : Plane × Plane → ℝ≥0∞} (hH : Measurable H) :
    Measurable (chainPathTest K w H) := by
  unfold chainPathTest
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro k _
    exact ((hw k).comp (((measurable_pi_apply k.castSucc).snd).sub
      ((measurable_pi_apply k.succ).fst))).ennreal_ofReal
  · exact hH.comp ((measurable_pi_apply 0).fst.prodMk
      (measurable_pi_apply (Fin.last K)).snd)

/-- Appending a path pair yields the last connector and the updated endpoint test. -/
theorem chainPathTest_snoc (K : ℕ) (w : ℕ → Plane → ℝ) (H : Plane × Plane → ℝ≥0∞)
    (p : Fin (K + 1) → Plane × Plane) (z : Plane × Plane) :
    chainPathTest (K + 1) w H (Fin.snoc p z) =
      chainPathTest K w (fun q => ENNReal.ofReal (w K (q.2 - z.1)) * H (q.1, z.2)) p := by
  simp only [chainPathTest, Fin.prod_univ_castSucc, Fin.val_castSucc, ← Fin.castSucc_succ,
    Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last, Fin.succ_last, Fin.snoc_apply_zero, mul_assoc]

/-- Every endpoint chain of s-finite input blocks is s-finite. -/
theorem sFinite_chainProduct (μ : ℕ → Measure (Plane × Plane))
    (hμ : ∀ k, SFinite (μ k)) (w : ℕ → Plane → ℝ) (K : ℕ) :
    SFinite (chainProduct μ w K) := by
  induction K with
  | zero => exact hμ 0
  | succ K ih =>
    let : SFinite (chainProduct μ w K) := ih
    let : SFinite (μ (K + 1)) := hμ (K + 1)
    dsimp only [chainProduct, smoothedProductMeasure]
    infer_instance

end Critical2DKPZ.SHF.Tsai

end
