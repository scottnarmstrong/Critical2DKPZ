/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainPathIntegrals
public import Critical2DKPZ.SHF.Tsai.BlockTupleMeasures
public import Critical2DKPZ.SHF.Tsai.ProductMeasureTranspose
import Critical2DKPZ.Collision.RenewalStringCells

/-! # Regrouping particle chains into block tuple paths

Finite-product Tonelli and measure-preserving transposition turn a product of
endpoint-chain integrals into one path integral grouped by input block. This
is the deterministic regrouping used before independence factors the means.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The product of the particle path tests, grouped by the block index. -/
def tupleChainPathTest {n : ℕ} (K : ℕ) (w : Fin n → ℕ → Plane → ℝ)
    (H : Fin n → Plane × Plane → ℝ≥0∞)
    (p : Fin (K + 1) → Configuration n × Configuration n) : ℝ≥0∞ :=
  ∏ i, chainPathTest K (w i) (H i) (fun k => ((p k).1 i, (p k).2 i))

/-- The regrouped path test is jointly measurable. -/
theorem measurable_tupleChainPathTest {n : ℕ} (K : ℕ) {w : Fin n → ℕ → Plane → ℝ}
    (hw : ∀ i k, Measurable (w i k)) {H : Fin n → Plane × Plane → ℝ≥0∞}
    (hH : ∀ i, Measurable (H i)) : Measurable (tupleChainPathTest K w H) := by
  unfold tupleChainPathTest
  apply Finset.measurable_prod
  intro i _
  apply (measurable_chainPathTest K (hw i) (hH i)).comp
  apply measurable_pi_iff.mpr
  intro k
  exact (((measurable_pi_apply i).comp (measurable_pi_apply k).fst).prodMk
    ((measurable_pi_apply i).comp (measurable_pi_apply k).snd))

/-- Particle-dependent endpoint measures regroup into the actual endpoint tuple paths. -/
theorem lintegral_prod_chainProduct_eq_lintegral_endpointTuplePaths {n : ℕ} (K : ℕ)
    (μ : Fin n → ℕ → Measure (Plane × Plane)) [∀ i k, SigmaFinite (μ i k)]
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k))
    (H : Fin n → Plane × Plane → ℝ≥0∞) (hH : ∀ i, Measurable (H i)) :
    (∏ i, ∫⁻ p, H i p ∂chainProduct (μ i) (w i) K) =
      ∫⁻ p, tupleChainPathTest K w H p
        ∂Measure.pi (fun k : Fin (K + 1) => endpointTupleMeasure (fun i => μ i k)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin n)
  have hsf (k : Fin (K + 1)) : SigmaFinite (endpointTupleMeasure (fun i => μ i k)) :=
    e.sigmaFinite_map
  let : ∀ k : Fin (K + 1), SigmaFinite (endpointTupleMeasure (fun i => μ i k)) := hsf
  have hends (k : Fin (K + 1)) : MeasurePreserving e
      (Measure.pi (fun i : Fin n => μ i k)) (endpointTupleMeasure (fun i => μ i k)) := ⟨e.measurable, rfl⟩
  have hgroup := measurePreserving_pi
    (fun k : Fin (K + 1) => Measure.pi (fun i : Fin n => μ i k))
    (fun k => endpointTupleMeasure (fun i => μ i k)) hends
  let J (p : Fin n → Fin (K + 1) → Plane × Plane) :=
    ∏ i, chainPathTest K (w i) (H i) (p i)
  have hJ : Measurable J := Finset.measurable_prod _
    (fun i _ => (measurable_chainPathTest K (hw i) (hH i)).comp (measurable_pi_apply i))
  have ht := (measurePreserving_pi_transpose_family (K + 1) n (fun k i => μ i k)).lintegral_comp hJ
  have hg := hgroup.lintegral_comp (measurable_tupleChainPathTest K hw hH)
  calc
    _ = ∏ i, ∫⁻ p, chainPathTest K (w i) (H i) p
        ∂Measure.pi (fun k : Fin (K + 1) => μ i k) := by
      apply Finset.prod_congr rfl
      intro i _
      exact lintegral_chainProduct_eq_lintegral_path (μ i) (hw i) K (hH i)
    _ = ∫⁻ p, J p ∂Measure.pi (fun i : Fin n => Measure.pi (fun k : Fin (K + 1) => μ i k)) :=
      (Collision.lintegral_fin_nat_prod_eq_prod_collision _ _
        (fun i => measurable_chainPathTest K (hw i) (hH i))).symm
    _ = ∫⁻ p, J (fun i k => p k i)
        ∂Measure.pi (fun k : Fin (K + 1) => Measure.pi (fun i : Fin n => μ i k)) := ht.symm
    _ = _ := hg

/-- Product endpoint pairings equal the path integral grouped by the actual block tuple measures. -/
theorem lintegral_prod_chainProduct_eq_lintegral_tuplePaths {n : ℕ} (K : ℕ)
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k))
    (H : Fin n → Plane × Plane → ℝ≥0∞) (hH : ∀ i, Measurable (H i)) :
    (∏ i, ∫⁻ p, H i p ∂chainProduct μ (w i) K) =
      ∫⁻ p, tupleChainPathTest K w H p
        ∂Measure.pi (fun k : Fin (K + 1) => blockTupleMeasure n (μ k)) :=
  lintegral_prod_chainProduct_eq_lintegral_endpointTuplePaths K (fun _ => μ) w hw H hH

end Critical2DKPZ.SHF.Tsai

end
