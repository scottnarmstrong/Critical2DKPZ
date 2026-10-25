/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.TestFnMulCos
public import Critical2DKPZ.Definitions.TestFnMulSin
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Tactic.FunProp

/-! Jointly smooth test-function families with a common compact support are continuous in the test-function topology. -/

public section

noncomputable section

open Set TopologicalSpace
open scoped Topology Distributions BoundedContinuousFunction

namespace Critical2DKPZ

/-- Partial iterated derivatives of a jointly smooth family are jointly smooth. -/
theorem contDiff_param_iteratedFDeriv {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : P → E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P × E => iteratedFDeriv ℝ n (f p.1) p.2) := by
  induction n with
  | zero =>
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def, Function.uncurry_def,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
        (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.contDiff.comp hf
  | succ n ih =>
      have hg : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (P × E) × E => iteratedFDeriv ℝ n (f p.1.1) p.2) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ (⊤ : ℕ∞) (fun p : P × E =>
          fderiv ℝ (iteratedFDeriv ℝ n (f p.1)) p.2) :=
        hg.fderiv contDiff_snd (by simp)
      simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def, Function.uncurry_def] using
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.contDiff.comp hd

/-- A jointly continuous family supported in one compact set is continuous in the sup norm. -/
theorem continuous_bounded_family_of_support {P G : Type*} [PseudoMetricSpace P]
    [NormedAddCommGroup G] (K : Compacts Plane) (f : P → Plane →ᵇ G)
    (hf : Continuous (fun p : P × Plane => f p.1 p.2))
    (hz : ∀ p x, x ∉ K → f p x = 0) : Continuous f := by
  let r (p : P) : C(K, G) := ⟨fun x => f p x.val,
    (f p).continuous.comp continuous_subtype_val⟩
  have hr : Continuous r := ContinuousMap.continuous_of_continuous_uncurry r
    (hf.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  apply continuous_iff_continuousAt.mpr
  intro p
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hr.continuousAt ε hε
  refine ⟨δ, hδ, fun {q} hq => ?_⟩
  have hbound : dist (f q) (f p) ≤ dist (r q) (r p) := by
    apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
    intro x
    by_cases hx : x ∈ K
    · exact ContinuousMap.dist_apply_le_dist (f := r q) (g := r p) ⟨x, hx⟩
    · rw [hz q x hx, hz p x hx, dist_self]
      exact dist_nonneg
  exact hbound.trans_lt (hd hq)

/-- Smooth compactly supported families are continuous on the fixed-support test-function space. -/
theorem continuous_supported_test_family {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (K : Compacts Plane) (f : P → 𝓓_{K}(Plane, ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun p : P × Plane => f p.1 p.2)) : Continuous f := by
  apply (ContDiffMapSupportedIn.continuous_iff_comp f).mpr
  intro n
  apply continuous_bounded_family_of_support K
  · simpa only [Function.comp_def, Function.uncurry_def, ContDiffMapSupportedIn.structureMapCLM_top_apply] using
      (contDiff_param_iteratedFDeriv (f := fun p x => f p x) hf n).continuous
  · intro p x hx
    change iteratedFDeriv ℝ n (f p) x = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hx
      ((f p).tsupport_subset (tsupport_iteratedFDeriv_subset n h)))

/-- Joint smoothness and a common compact support imply continuity in the LF test topology. -/
theorem continuous_testFn_family {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (K : Compacts Plane) (f : P → TestFn)
    (hs : ∀ p, tsupport (f p) ⊆ K)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun p : P × Plane => f p.1 p.2)) : Continuous f := by
  let g (p : P) : 𝓓_{K}(Plane, ℝ) :=
    ⟨f p, (f p).contDiff, fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs p h))⟩
  have hg : Continuous g := continuous_supported_test_family K g hf
  have hi := TestFunction.continuous_ofSupportedIn (F := ℝ) (n := (⊤ : ℕ∞)) (show (K : Set Plane) ⊆ (⊤ : Opens Plane) from
    fun _ _ => trivial)
  convert hi.comp hg using 1
  funext p
  apply TestFunction.ext
  intro x
  rfl

/-- Cosine modulation evaluates to the test function times the cosine of the phase. -/
@[simp] theorem TestFn.mulCos_apply (χ : TestFn) (ξ x : Plane) :
    χ.mulCos ξ x = χ x * Real.cos (inner ℝ ξ x) := rfl

/-- Sine modulation evaluates to the test function times the sine of the phase. -/
@[simp] theorem TestFn.mulSin_apply (χ : TestFn) (ξ x : Plane) :
    χ.mulSin ξ x = χ x * Real.sin (inner ℝ ξ x) := rfl

/-- Cosine modulation of a fixed test function depends continuously on frequency. -/
theorem continuous_testFn_mulCos (χ : TestFn) : Continuous χ.mulCos := by
  apply continuous_testFn_family ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩ χ.mulCos
  · intro ξ
    exact tsupport_mul_subset_left
  · change ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => χ p.2 * Real.cos (inner ℝ p.1 p.2))
    exact (χ.contDiff.comp contDiff_snd).mul
      (Real.contDiff_cos.comp (contDiff_fst.inner ℝ contDiff_snd))

/-- Sine modulation of a fixed test function depends continuously on frequency. -/
theorem continuous_testFn_mulSin (χ : TestFn) : Continuous χ.mulSin := by
  apply continuous_testFn_family ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩ χ.mulSin
  · intro ξ
    exact tsupport_mul_subset_left
  · change ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => χ p.2 * Real.sin (inner ℝ p.1 p.2))
    exact (χ.contDiff.comp contDiff_snd).mul
      (Real.contDiff_sin.comp (contDiff_fst.inner ℝ contDiff_snd))

end Critical2DKPZ

end
