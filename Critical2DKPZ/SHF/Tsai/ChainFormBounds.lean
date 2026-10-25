/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainKernels
public import Critical2DKPZ.SHF.Tsai.PiFormBounds

/-! # Form bounds for positive moment chains

A finite chain of positive block kernels and coordinatewise convolution connectors
has a form bound given by the product of their form constants.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The coordinatewise connector at a single chain interface. -/
def connectorKernel {n : ℕ} (w : Fin n → Plane → ℝ) (x y : Configuration n) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (w i (x i - y i))

/-- A tensor connector kernel is jointly measurable when each coordinate test is measurable. -/
theorem measurable_connectorKernel {n : ℕ} (w : Fin n → Plane → ℝ) (hw : ∀ i, Measurable (w i)) :
    Measurable (Function.uncurry (connectorKernel w)) := by
  unfold connectorKernel
  apply Finset.measurable_prod
  intro i _
  exact ((hw i).comp (((measurable_pi_apply i).comp measurable_fst).sub
    ((measurable_pi_apply i).comp measurable_snd))).ennreal_ofReal

/-- The configuration connector has the product of its planar form constants. -/
theorem formBound_connectorKernel {n : ℕ} (w : Fin n → Plane → ℝ)
    (hw : ∀ i, Measurable (w i)) (M : Fin n → ℝ≥0∞)
    (hM : ∀ i, FormBound volume volume (fun x y : Plane => ENNReal.ofReal (w i (x - y))) (M i)) :
    FormBound volume volume (connectorKernel w) (∏ i, M i) := by
  exact formBound_configuration_prod n (fun i x y => ENNReal.ofReal (w i (x - y)))
    (fun i => ((hw i).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal) M hM

/-- The two positive integrals in a successor chain are the composition of its connector and block. -/
theorem chainKernel_succ_eq_comp {n : ℕ}
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k)))
    (w : Fin n → ℕ → Plane → ℝ) (hw : ∀ i k, Measurable (w i k)) (K : ℕ) :
    chainKernel n Kb w (K + 1) = spatialKernelComp volume (chainKernel n Kb w K)
      (spatialKernelComp volume (connectorKernel (fun i => w i K)) (Kb (K + 1))) := by
  funext x y
  change (∫⁻ z, ∫⁻ z', chainKernel n Kb w K x z *
      connectorKernel (fun i => w i K) z z' * Kb (K + 1) z' y) =
    ∫⁻ z, chainKernel n Kb w K x z *
      (∫⁻ z', connectorKernel (fun i => w i K) z z' * Kb (K + 1) z' y)
  apply lintegral_congr
  intro z
  have hm : Measurable (fun z' => connectorKernel (fun i => w i K) z z' * Kb (K + 1) z' y) :=
    ((measurable_connectorKernel _ (fun i => hw i K)).comp
      (measurable_const.prodMk measurable_id)).mul
      ((hKb (K + 1)).comp (measurable_id.prodMk measurable_const))
  simp only [mul_assoc]
  exact lintegral_const_mul _ hm

/-- Compose positive block and connector form bounds along a finite chain. -/
theorem formBound_chainKernel {n : ℕ} (K : ℕ)
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k))) (c : ℕ → ℝ≥0∞)
    (hQ : ∀ k ≤ K, FormBound volume volume (Kb k) (c k))
    (w : Fin n → ℕ → Plane → ℝ) (hwm : ∀ i k, Measurable (w i k)) (M : Fin n → ℕ → ℝ≥0∞)
    (hM : ∀ i, ∀ k < K, FormBound volume volume
      (fun x y : Plane => ENNReal.ofReal (w i k (x - y))) (M i k)) :
    FormBound volume volume (chainKernel n Kb w K)
      ((∏ k ∈ Finset.range (K + 1), c k) * ∏ k ∈ Finset.range K, ∏ i, M i k) := by
  revert hQ hM
  induction K with
  | zero =>
    intro hQ hM
    simpa only [chainKernel, Finset.prod_range_zero, Finset.prod_range_succ, one_mul, mul_one] using
      hQ 0 (by omega)
  | succ K ih =>
    intro hQ hM
    have hprev := ih (fun k hk => hQ k (by omega)) (fun i k hk => hM i k (by omega))
    have hCm := measurable_connectorKernel (fun i => w i K) (fun i => hwm i K)
    have hCF := formBound_connectorKernel (fun i => w i K) (fun i => hwm i K)
      (fun i => M i K) (fun i => hM i K (by omega))
    have hlast := hCF.comp volume volume volume hCm (hKb (K + 1)) (hQ (K + 1) le_rfl)
    have hlastm := measurable_spatialKernelComp volume hCm (hKb (K + 1))
    have h := hprev.comp volume volume volume (measurable_chainKernel Kb hKb w hwm K) hlastm hlast
    rw [← chainKernel_succ_eq_comp Kb hKb w hwm K] at h
    convert h using 1
    simp only [Finset.prod_range_succ]
    ring


end Critical2DKPZ.SHF.Tsai

end
