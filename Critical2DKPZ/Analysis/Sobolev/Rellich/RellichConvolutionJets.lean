/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichKernelFamilyBounds
public import Critical2DKPZ.Analysis.Sobolev.Rellich.ConvolutionStructure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Iterated derivatives, support and uniform derivative bounds for convolution.

Adapted from work of A. Bou-Rabee, licensed under Apache 2.0. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ENNReal Pointwise Convolution

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

private theorem contDiff_uncurry_fderiv {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : P → E → F}
    (hg : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry g)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : P × E => fderiv ℝ (g z.1) z.2) := by
  have haux : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun z : P × E => g z.1)) :=
    hg.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact haux.fderiv contDiff_snd (by simp)

private theorem contDiff_uncurry_iteratedFDeriv {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : P → E → F}
    (hg : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry g)) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : P × E => iteratedFDeriv ℝ n (g z.1) z.2) := by
  induction n with
  | zero =>
    exact hg.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E F).symm : F →L[ℝ] E [×0]→L[ℝ] F)
  | succ n ih =>
    have hd := contDiff_uncurry_fderiv
      (g := fun p x => iteratedFDeriv ℝ n (g p) x) ih
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm :
        (E →L[ℝ] E [×n]→L[ℝ] F) →L[ℝ] E [×(n + 1)]→L[ℝ] F)

/-- Iterated directional differentiation, with the directions retained as parameters. -/
noncomputable def rellichDirectionalKernel {d : ℕ} (ρ : Space d → ℝ) :
    (k : ℕ) → (Fin k → Space d) → Space d → ℝ
  | 0, _, x => ρ x
  | k + 1, v, x => fderiv ℝ (rellichDirectionalKernel ρ k (Fin.tail v)) x (v 0)

/-- The recursively differentiated kernel is the full iterated derivative evaluation. -/
theorem rellichDirectionalKernel_eq_iteratedFDeriv {d : ℕ} {ρ : Space d → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (k : ℕ) (v : Fin k → Space d) (x : Space d) :
    rellichDirectionalKernel ρ k v x = iteratedFDeriv ℝ k ρ x v := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have he : rellichDirectionalKernel ρ k (Fin.tail v) =
        fun y => iteratedFDeriv ℝ k ρ y (Fin.tail v) := funext (fun y => ih (Fin.tail v) y)
    rw [rellichDirectionalKernel, he]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k ρ) x :=
      (hρ.differentiable_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)) x
    exact (DifferentiableAt.iteratedFDeriv_succ_apply_left' (m := v) hd).symm

private theorem contDiff_directionalKernel {d : ℕ} {ρ : Space d → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (Fin k → Space d) × Space d => rellichDirectionalKernel ρ k z.1 z.2) := by
  induction k with
  | zero => exact hρ.comp contDiff_snd
  | succ k ih =>
    have haux : ContDiff ℝ (⊤ : ℕ∞)
        (Function.uncurry (fun z : (Fin (k + 1) → Space d) × Space d =>
          rellichDirectionalKernel ρ k (Fin.tail z.1))) := by
      have htail : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : ((Fin (k + 1) → Space d) × Space d) × Space d => Fin.tail z.1.1) :=
        contDiff_pi.mpr fun i : Fin k =>
          (contDiff_apply ℝ (Space d) i.succ).comp
            (contDiff_fst.fst : ContDiff ℝ (⊤ : ℕ∞)
              (fun z : ((Fin (k + 1) → Space d) × Space d) × Space d => z.1.1))
      have hmap : ContDiff ℝ (⊤ : ℕ∞)
          (fun z : ((Fin (k + 1) → Space d) × Space d) × Space d =>
            (Fin.tail z.1.1, z.2)) := htail.prodMk contDiff_snd
      exact ih.comp hmap
    exact haux.fderiv_apply contDiff_snd
      ((contDiff_apply ℝ (Space d) 0).comp contDiff_fst) (by simp)

private theorem isTestFn_directionalKernel {d : ℕ} {D : Set (Space d)}
    {ρ : Space d → ℝ} (hρ : IsTestFn D ρ) (k : ℕ) (v : Fin k → Space d) :
    IsTestFn D (rellichDirectionalKernel ρ k v) := by
  induction k with
  | zero => exact hρ
  | succ k ih => exact (ih (Fin.tail v)).fderiv_apply (v 0)

/-- Directional derivatives of convolution equal pairings with the differentiated kernel. -/
theorem rellichDirectionalKernel_convReal {d : ℕ} {D R : Set (Space d)}
    {φ ρ : Space d → ℝ} (hφ : IsTestFn D φ) (hρ : IsTestFn R ρ)
    (k : ℕ) (v : Fin k → Space d) :
    rellichDirectionalKernel (convReal φ ρ) k v =
      convReal φ (rellichDirectionalKernel ρ k v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    ext x
    rw [rellichDirectionalKernel, ih (Fin.tail v)]
    let κ := rellichDirectionalKernel ρ k (Fin.tail v)
    have hκ := isTestFn_directionalKernel hρ k (Fin.tail v)
    have hd := hκ.2.1.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hφ.integrable.locallyIntegrable
      (hκ.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl _)) x
    change fderiv ℝ (convReal φ κ) x (v 0) =
      convReal φ (fun y => fderiv ℝ κ y (v 0)) x
    rw [show fderiv ℝ (convReal φ κ) x =
      (φ ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompR (Space d), volume]
        fderiv ℝ κ) x from hd.fderiv]
    exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ)
      hφ.integrable.locallyIntegrable (hκ.2.1.fderiv ℝ)
      ((hκ.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous) x (v 0)

/-- The full topological support of every convolution lies in one compact sum. -/
theorem tsupport_convReal_subset_sum {d : ℕ} {D : Set (Space d)}
    {φ ρ : Space d → ℝ} (hD : Bornology.IsBounded D) (hφ : IsTestFn D φ)
    (hρ : HasCompactSupport ρ) :
    tsupport (convReal φ ρ) ⊆ tsupport ρ + closure D := by
  apply closure_minimal
  · exact (support_convolution_subset_swap (ContinuousLinearMap.mul ℝ ℝ)).trans
      (add_subset_add subset_closure (subset_closure.trans (hφ.2.2.trans subset_closure)))
  · exact (hρ.isCompact.add hD.isCompact_closure).isClosed

/-- Every derivative order of the convolved unit ball has a uniform global bound. -/
theorem exists_convReal_derivative_bound {d : ℕ} {D : Set (Space d)}
    (hD : Bornology.IsBounded D) {ρ : Space d → ℝ}
    (hρsm : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ)
    (s : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : Space d → ℝ,
      IsTestFn D φ → sobolevNormSq d s φ ≤ 1 → ∀ x,
        ‖iteratedFDeriv ℝ k (convReal φ ρ) x‖ ≤ C := by
  classical
  let K := tsupport ρ + closure D
  have hK : IsCompact K := hρcs.isCompact.add hD.isCompact_closure
  let V := Metric.closedBall (0 : Fin k → Space d) 2
  have hV : IsCompact V := isCompact_closedBall 0 2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let P := K × V
  let L := K - tsupport ρ
  have hL : IsCompact L := by
    rw [show L = K - tsupport ρ from rfl, ← Set.sub_image_prod]
    exact (hK.prod hρcs.isCompact).image (continuous_fst.sub continuous_snd)
  have hρ : IsTestFn (tsupport ρ) ρ := ⟨hρsm, hρcs, subset_rfl⟩
  let g (p : P) (t : Space d) :=
    rellichDirectionalKernel ρ k p.2.val (p.1.val - t)
  have htest : ∀ p : P, IsTestFn L (g p) := by
    intro p
    have ht := (isTestFn_directionalKernel hρ k p.2.val).comp_sub_left p.1.val
    refine ⟨ht.1, ht.2.1, ht.2.2.trans ?_⟩
    intro t ht
    exact ⟨p.1.val, p.1.property, p.1.val - t, ht, by abel_nf⟩
  have hjoint : ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry (fun p : Space d × (Fin k → Space d) =>
        fun t => rellichDirectionalKernel ρ k p.2 (p.1 - t))) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : (Space d × (Fin k → Space d)) × Space d =>
          (z.1.2, z.1.1 - z.2)) :=
      contDiff_fst.snd.prodMk (contDiff_fst.fst.sub contDiff_snd)
    exact (contDiff_directionalKernel hρsm k).comp hmap
  have hcont : ∀ n : ℕ,
      Continuous (fun z : P × Space d => iteratedFDeriv ℝ n (g z.1) z.2) := by
    intro n
    have hmap : Continuous (fun z : P × Space d => ((z.1.1.val, z.1.2.val), z.2)) :=
      ((continuous_subtype_val.comp continuous_fst.fst).prodMk
        (continuous_subtype_val.comp continuous_fst.snd)).prodMk continuous_snd
    exact (contDiff_uncurry_iteratedFDeriv hjoint n).continuous.comp hmap
  obtain ⟨C, hC, hpair⟩ := exists_uniform_test_pairing_bound g hL
    (fun p => (htest p).1) (fun p => (htest p).2.2) hcont s
  refine ⟨C, hC, ?_⟩
  intro φ hφ hunit x
  have hsm := contDiff_convReal hφ.integrable.locallyIntegrable hρsm hρcs
  by_cases hx : x ∈ K
  · let q := iteratedFDeriv ℝ k (convReal φ ρ) x
    apply ContinuousMultilinearMap.opNorm_le_bound hC.le
    intro v
    apply q.toMultilinearMap.bound_of_shell_of_continuous q.cont
      (ε := fun _ => 2) (c := fun _ => (2 : ℝ)) (fun _ => by norm_num)
      (fun _ => by norm_num)
    intro w hwlow hwhigh
    have hwV : w ∈ V := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).2
        (fun i => (hwhigh i).le)
    have hp := hpair (⟨x, hx⟩, ⟨w, hwV⟩) D φ hφ hunit
    have he : q w = ∫ t, φ t * g (⟨x, hx⟩, ⟨w, hwV⟩) t := by
      rw [← rellichDirectionalKernel_eq_iteratedFDeriv hsm k w x]
      rw [rellichDirectionalKernel_convReal hφ hρ k w]
      rfl
    have hprod : (1 : ℝ) ≤ ∏ i, ‖w i‖ := by
      apply Finset.one_le_prod₀
      intro i hi
      simpa using hwlow i
    calc ‖q w‖ = |∫ t, φ t * g (⟨x, hx⟩, ⟨w, hwV⟩) t| := by
          rw [he, Real.norm_eq_abs]
      _ ≤ C := hp
      _ ≤ C * ∏ i, ‖w i‖ := by nlinarith
  · have hz : iteratedFDeriv ℝ k (convReal φ ρ) x = 0 := by
      by_contra hn
      exact hx ((tsupport_convReal_subset_sum hD hφ hρcs)
        (support_iteratedFDeriv_subset k hn))
    rw [hz, norm_zero]
    exact hC.le

/-- One constant controls all derivatives through a requested finite order. -/
theorem exists_convReal_uniform_jets {d : ℕ} {D : Set (Space d)}
    (hD : Bornology.IsBounded D) {ρ : Space d → ℝ}
    (hρsm : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρcs : HasCompactSupport ρ)
    (s : ℝ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : Space d → ℝ,
      IsTestFn D φ → sobolevNormSq d s φ ≤ 1 → ∀ k ≤ m, ∀ x,
        ‖iteratedFDeriv ℝ k (convReal φ ρ) x‖ ≤ C := by
  classical
  choose C hC hbound using exists_convReal_derivative_bound hD hρsm hρcs s
  have ht : (Finset.range (m + 1)).Nonempty := ⟨0, by simp⟩
  let A := (Finset.range (m + 1)).sup' ht C
  have hA : 0 < A := (hC 0).trans_le (Finset.le_sup' C (by simp))
  refine ⟨A, hA, ?_⟩
  intro φ hφ hunit k hk x
  exact (hbound k φ hφ hunit x).trans
    (Finset.le_sup' C (Finset.mem_range.mpr (by omega)))

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
