/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationChainPaths

/-! # Integrating the final configuration block of a path

Tonelli moves the last block integral inside the previous path integral. Its
connector-weighted terminal pairing is then the updated terminal test. All
integrals are positive and may be infinite.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The positive path integral recursion obtained by integrating the last block. -/
theorem lintegral_configurationChainPathTest_succ {n : ℕ} (K : ℕ)
    (μ : ℕ → Measure (Configuration n × Configuration n)) [∀ k, SigmaFinite (μ k)]
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k))
    (G F : Configuration n → ℝ≥0∞) (hG : Measurable G) (hF : Measurable F) :
    (∫⁻ p, configurationChainPathTest (K + 1) w G F p
      ∂Measure.pi (fun k : Fin (K + 2) => μ k)) =
      ∫⁻ p, configurationChainPathTest K w G
        (fun y => ∫⁻ z, connectorKernel (fun i => w i K) y z.1 * F z.2 ∂μ (K + 1)) p
        ∂Measure.pi (fun k : Fin (K + 1) => μ k) := by
  let A := configurationChainPathTest K w G (fun _ => 1)
  have hAm : Measurable A := measurable_configurationChainPathTest K hw hG measurable_const
  have hcm := measurable_connectorKernel (fun i => w i K) (fun i => hw i K)
  have hsnoc (p : Fin (K + 1) → Configuration n × Configuration n)
      (z : Configuration n × Configuration n) :
      configurationChainPathTest (K + 1) w G F (Fin.snoc p z) =
        A p * (connectorKernel (fun i => w i K) (p (Fin.last K)).2 z.1 * F z.2) := by
    rw [configurationChainPathTest_snoc]
    simp only [configurationChainPathTest, A, mul_one]
  have hJm : Measurable (fun q : (Configuration n × Configuration n) ×
      (Fin (K + 1) → Configuration n × Configuration n) =>
      A q.2 * (connectorKernel (fun i => w i K) (q.2 (Fin.last K)).2 q.1.1 * F q.1.2)) := by
    exact (hAm.comp measurable_snd).mul
      ((hcm.comp ((((measurable_pi_apply (Fin.last K)).comp measurable_snd).snd).prodMk
        measurable_fst.fst)).mul (hF.comp measurable_fst.snd))
  rw [lintegral_path_snoc (K + 1) _ (measurable_configurationChainPathTest (K + 1) hw hG hF)]
  simp_rw [hsnoc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [lintegral_lintegral_swap (μ := μ (K + 1))
    (ν := Measure.pi (fun k : Fin (K + 1) => μ k))
    (f := fun z p => A p * (connectorKernel (fun i => w i K) (p (Fin.last K)).2 z.1 * F z.2))
    hJm.aemeasurable]
  apply lintegral_congr
  intro p
  have hlast : Measurable (fun z : Configuration n × Configuration n =>
      connectorKernel (fun i => w i K) (p (Fin.last K)).2 z.1 * F z.2) :=
    (hcm.comp (measurable_const.prodMk measurable_fst)).mul (hF.comp measurable_snd)
  rw [lintegral_const_mul _ hlast]
  simp only [A, configurationChainPathTest, mul_one]

end Critical2DKPZ.SHF.Tsai

end
