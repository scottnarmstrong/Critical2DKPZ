/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainFormBounds
public import Critical2DKPZ.SHF.Tsai.MollifierFormBounds
public import Critical2DKPZ.SHF.DeltaBose.MomentKernelFormBounds

/-! # Uniform finite form bounds for chains of moment kernels

A finite chain with fixed applicable mollifier families has a finite form constant uniform
over their approximation indices and all endpoint tests.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Finite measurable block form bounds and fixed applicable mollifier families give a chain form constant uniform in the approximation index. -/
theorem exists_formBound_chainKernel_uniform {n : ℕ} (K : ℕ)
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k))) (c : ℕ → ℝ≥0∞)
    (hc : ∀ k ≤ K, c k ≠ ⊤) (hQ : ∀ k ≤ K, FormBound volume volume (Kb k) (c k))
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ℓ,
      FormBound volume volume (chainKernel n Kb (fun i k => w i k ℓ) K) C := by
  choose M hMfin hM using fun i k => exists_formBound_mollifier_uniform (hw i k)
  let R := (∏ k ∈ Finset.range (K + 1), c k) * ∏ k ∈ Finset.range K, ∏ i, M i k
  have hRfin : R ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.prod_ne_top (fun k hk => hc k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
    (ENNReal.prod_ne_top (fun k _ => ENNReal.prod_ne_top (fun i _ => hMfin i k)))
  exact ⟨R, hRfin, fun ℓ => formBound_chainKernel K Kb hKb c hQ (fun i k => w i k ℓ)
    (fun i k => ((hw i k).2.1 ℓ).measurable) M (fun i k _ => hM i k ℓ)⟩

/-- A finite chain has one form constant uniform over all mollifier indices and endpoint tests. -/
theorem exists_formBound_chainMomentKernel_uniform (θ : ℝ) (K : ℕ) (τ : ℕ → ℝ)
    (hτ : ∀ k ≤ K, 0 < τ k) {n : ℕ} (w : Fin n → ℕ → ℕ → Plane → ℝ)
    (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ℓ,
      FormBound volume volume (chainMomentKernel n θ τ (fun i k => w i k ℓ) K) C := by
  obtain ⟨C, rate, _, hC⟩ := exists_formBound_momentKernel n θ
  let c k := ENNReal.ofReal (C * Real.exp (rate * τ k) * min (τ k) 1 ^ (-(n : ℝ)))
  have hc (k) : c k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQ (k) (hk : k ≤ K) : FormBound volume volume (momentKernel n θ (τ k)) (c k) :=
    hC θ le_rfl (τ k) (hτ k hk)
  have hKm (k) : Measurable (Function.uncurry (momentKernel n θ (τ k))) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  exact exists_formBound_chainKernel_uniform K _ hKm c (fun k _ => hc k) hQ w hw

end Critical2DKPZ.SHF.Tsai

end
