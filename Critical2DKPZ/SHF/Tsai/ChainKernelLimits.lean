/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainKernelOperators

/-! # Limits of the literal chain kernel integrals

Strong connector convergence passes through a finite chain of bounded block
operators. The operator representation identifies the limit with the actual
kernel integrals. Finite form bounds, constructed in `ChainKernelOperators`,
supply their absolute integrability via `configurationKernel_real_form_bound`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The chain uses only the block kernels in its finite prefix. -/
theorem chainKernel_congr_prefix {n : ℕ} (K : ℕ)
    {Kb Lb : ℕ → Configuration n → Configuration n → ℝ≥0∞}
    (h : ∀ k ≤ K, Kb k = Lb k) (w : Fin n → ℕ → Plane → ℝ) :
    chainKernel n Kb w K = chainKernel n Lb w K := by
  induction K with
  | zero => exact h 0 le_rfl
  | succ K ih =>
    have hp := ih (fun k hk => h k (by omega))
    simp only [chainKernel, hp, h (K + 1) le_rfl]

/-- The connector-free chain also uses only its finite block prefix. -/
theorem chainKernelLimit_congr_prefix {n : ℕ} (K : ℕ)
    {Kb Lb : ℕ → Configuration n → Configuration n → ℝ≥0∞}
    (h : ∀ k ≤ K, Kb k = Lb k) : chainKernelLimit n Kb K = chainKernelLimit n Lb K := by
  induction K with
  | zero => exact h 0 le_rfl
  | succ K ih =>
    have hp := ih (fun k hk => h k (by omega))
    simp only [chainKernelLimit, hp, h (K + 1) le_rfl]

/-- Applicable connectors can be removed in tested chain-kernel integrals when measurable finite form bounds are specified for all block kernels. -/
theorem tendsto_integral_chainKernel_of_all {n : ℕ} (K : ℕ)
    (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k, Measurable (Function.uncurry (Kb k)))
    (c : ℕ → ℝ≥0∞) (hc : ∀ k, c k ≠ ⊤) (hQ : ∀ k, FormBound volume volume (Kb k) (c k))
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k))
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    Tendsto (fun j => ∫ x, ∫ y, G x * (chainKernel n Kb (fun i k => w i k j) K x y).toReal * F y)
      atTop (𝓝 (∫ x, ∫ y, G x * (chainKernelLimit n Kb K x y).toReal * F y)) := by
  choose d hd hC using fun k => exists_formBound_connector_uniform (fun i => hw i k)
  let Q k := configurationKernelOperator (hKb k) (hc k) (hQ k)
  let W k j := configurationKernelOperator
    (measurable_connectorKernel _ (fun i => ((hw i k).2.1 j).measurable)) (hd k) (hC k j)
  have hW (k) (f : Lp ℝ 2 (volume : Measure (Configuration n))) :
      Tendsto (fun j => W k j f) atTop (𝓝 f) :=
    tendsto_connectorKernelOperator (fun i => hw i k) (fun _ => d k) (fun _ => hd k) (hC k) f
  have hlim := tendsto_operatorChain Q W hW K (hF.toLp F)
  have hinter := hlim.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hG.toLp G))
  have heq (j) : (∫ x, ∫ y, G x * (chainKernel n Kb (fun i k => w i k j) K x y).toReal * F y) =
      ⟪operatorChain Q (fun k => W k j) K (hF.toLp F), hG.toLp G⟫_ℝ := by
    obtain ⟨C, hfin, hB, hop⟩ := exists_chainKernelOperator_eq Kb hKb c hc hQ
      (fun i k => w i k j) (fun i k => ((hw i k).2.1 j).measurable) d hd (fun k => hC k j) K
    have h := inner_configurationKernelOperator_toLp
      (measurable_chainKernel Kb hKb _ (fun i k => ((hw i k).2.1 j).measurable) K) hfin hB hG hF
    rw [hop] at h
    exact h.symm
  have heqlim : (∫ x, ∫ y, G x * (chainKernelLimit n Kb K x y).toReal * F y) =
      ⟪operatorChain Q (fun _ => ContinuousLinearMap.id ℝ _) K (hF.toLp F), hG.toLp G⟫_ℝ := by
    obtain ⟨C, hfin, hB, hop⟩ := exists_chainKernelLimitOperator_eq Kb hKb c hc hQ K
    have h := inner_configurationKernelOperator_toLp (measurable_chainKernelLimit Kb hKb K) hfin hB hG hF
    rw [hop] at h
    exact h.symm
  simpa only [heq, heqlim] using hinter

/-- Applicable connectors can be removed in tested chain-kernel integrals under measurable finite form bounds on the blocks in the finite chain. -/
theorem tendsto_integral_chainKernel (K : ℕ) {n : ℕ} (Kb : ℕ → Configuration n → Configuration n → ℝ≥0∞)
    (hKb : ∀ k ≤ K, Measurable (Function.uncurry (Kb k))) (c : ℕ → ℝ≥0∞) (hc : ∀ k ≤ K, c k ≠ ⊤)
    (hKbF : ∀ k ≤ K, FormBound volume volume (Kb k) (c k))
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k))
    (G F : Configuration n → ℝ) (hG : MemLp G 2) (hF : MemLp F 2) :
    Tendsto (fun ℓ => ∫ x, ∫ y, G x * (chainKernel n Kb (fun i k => w i k ℓ) K x y).toReal * F y)
      atTop (𝓝 (∫ x, ∫ y, G x * (chainKernelLimit n Kb K x y).toReal * F y)) := by
  classical
  let Lb k := if k ≤ K then Kb k else 0
  let b k := if k ≤ K then c k else 0
  have hLm (k) : Measurable (Function.uncurry (Lb k)) := by
    by_cases hk : k ≤ K
    · simpa only [Lb, ite_eq_left hk] using hKb k hk
    · simp only [Lb, ite_eq_right hk]; exact measurable_const
  have hb (k) : b k ≠ ⊤ := by
    by_cases hk : k ≤ K
    · simpa only [b, ite_eq_left hk] using hc k hk
    · simp only [b, ite_eq_right hk]; exact ENNReal.zero_ne_top
  have hLF (k) : FormBound volume volume (Lb k) (b k) := by
    by_cases hk : k ≤ K
    · simpa only [Lb, b, ite_eq_left hk] using hKbF k hk
    · simp only [Lb, b, ite_eq_right hk]
      intro f g hf hg
      simp only [Pi.zero_apply, zero_mul, lintegral_zero, mul_zero, le_refl]
  have hp (k) (hk : k ≤ K) : Lb k = Kb k := ite_eq_left hk
  have hlim := tendsto_integral_chainKernel_of_all K Lb hLm b hb hLF w hw G F hG hF
  have hchain (j) := chainKernel_congr_prefix K hp (fun i k => w i k j)
  have hlimit := chainKernelLimit_congr_prefix K hp
  simpa only [hchain, hlimit] using hlim

end Critical2DKPZ.SHF.Tsai

end
