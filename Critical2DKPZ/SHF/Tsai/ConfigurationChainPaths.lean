/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainPathIntegrals
public import Critical2DKPZ.SHF.Tsai.ChainFormBounds
public import Critical2DKPZ.SHF.Tsai.TupleChainPaths

/-! # Configuration path tests for positive kernel chains

Grouping the particle weights gives the configuration connector at every
interface. Appending the last block retains the usual endpoint-test recursion.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Connector-weighted configuration path test with separate outer endpoint factors. -/
def configurationChainPathTest {n : ℕ} (K : ℕ) (w : Fin n → ℕ → Plane → ℝ)
    (G F : Configuration n → ℝ≥0∞)
    (p : Fin (K + 1) → Configuration n × Configuration n) : ℝ≥0∞ :=
  (∏ k : Fin K, connectorKernel (fun i => w i k) (p k.castSucc).2 (p k.succ).1) *
    G (p 0).1 * F (p (Fin.last K)).2

/-- The full configuration path test is measurable. -/
theorem measurable_configurationChainPathTest {n : ℕ} (K : ℕ)
    {w : Fin n → ℕ → Plane → ℝ} (hw : ∀ i k, Measurable (w i k))
    {G F : Configuration n → ℝ≥0∞} (hG : Measurable G) (hF : Measurable F) :
    Measurable (configurationChainPathTest K w G F) := by
  unfold configurationChainPathTest
  apply Measurable.mul
  · apply Measurable.mul
    · apply Finset.measurable_prod
      intro k _
      exact (measurable_connectorKernel _ (fun i => hw i k)).comp
        ((measurable_pi_apply k.castSucc).snd.prodMk (measurable_pi_apply k.succ).fst)
    · exact hG.comp (measurable_pi_apply 0).fst
  · exact hF.comp (measurable_pi_apply (Fin.last K)).snd

/-- The last interface becomes part of the previous terminal test when a block is appended. -/
theorem configurationChainPathTest_snoc {n : ℕ} (K : ℕ) (w : Fin n → ℕ → Plane → ℝ)
    (G F : Configuration n → ℝ≥0∞) (p : Fin (K + 1) → Configuration n × Configuration n)
    (z : Configuration n × Configuration n) :
    configurationChainPathTest (K + 1) w G F (Fin.snoc p z) =
      configurationChainPathTest K w G (fun y => connectorKernel (fun i => w i K) y z.1 * F z.2) p := by
  simp only [configurationChainPathTest, Fin.prod_univ_castSucc, Fin.val_castSucc,
    ← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last,
    Fin.succ_last, Fin.snoc_apply_zero]
  ac_rfl

/-- Particle path tests with tensor endpoint factors equal the configuration path test. -/
theorem tupleChainPathTest_tensor_eq {n : ℕ} (K : ℕ) (w : Fin n → ℕ → Plane → ℝ)
    (f g : Fin n → Plane → ℝ≥0∞) (p : Fin (K + 1) → Configuration n × Configuration n) :
    tupleChainPathTest K w (fun i q => f i q.1 * g i q.2) p =
      configurationChainPathTest K w (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) p := by
  unfold tupleChainPathTest chainPathTest configurationChainPathTest connectorKernel
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_comm]
  ac_rfl

end Critical2DKPZ.SHF.Tsai

end
