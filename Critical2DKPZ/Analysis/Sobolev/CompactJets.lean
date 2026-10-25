/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.FiniteOrder
public import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Tactic.Ring

/-! On a fixed compact support, a distribution factors through finitely many bounded derivative fields and extends continuously to their Banach space. -/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions BoundedContinuousFunction NNReal

namespace Critical2DKPZ

/-- The Banach space of bounded derivative fields through order `m`. -/
abbrev CompactJetSpace (m : ℕ) :=
  (i : Fin (m + 1)) → Plane →ᵇ (Plane [×i.val]→L[ℝ] ℝ)

/-- Finite derivative fields form a normed additive commutative group under the supremum norm. -/
instance compactJetSpaceNormedAddCommGroup (m : ℕ) :
    NormedAddCommGroup (CompactJetSpace m) := inferInstance

/-- Finite derivative fields form a real normed vector space. -/
instance compactJetSpaceNormedSpace (m : ℕ) :
    NormedSpace ℝ (CompactJetSpace m) := inferInstance

/-- The continuous linear map taking a smooth function with fixed compact support to its derivatives through a finite order. -/
def compactTestJet (K : Compacts Plane) (m : ℕ) :
    ContDiffMapSupportedIn Plane ℝ ⊤ K →L[ℝ] CompactJetSpace m :=
  ContinuousLinearMap.pi fun i => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i.val

/-- The finite jet containing the zeroth derivative determines its smooth function. -/
theorem compactTestJet_injective (K : Compacts Plane) (m : ℕ) :
    Function.Injective (compactTestJet K m) := by
  intro φ ψ h
  ext x
  have he := congrArg (fun F : CompactJetSpace m => (F ⟨0, Nat.zero_lt_succ m⟩ x) (fun _ => 0)) h
  simpa only [compactTestJet, ContinuousLinearMap.pi_apply,
    ContDiffMapSupportedIn.structureMapCLM_top_apply, iteratedFDeriv_zero_apply] using he

/-- The derivative supremum seminorm is bounded by the norm of the compact test jet. -/
theorem supSeminorm_le_norm_compactTestJet (K : Compacts Plane) (m : ℕ)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K) :
    ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ ≤ ‖compactTestJet K m φ‖ := by
  apply Seminorm.finset_sup_apply_le (norm_nonneg _)
  intro j hj
  rw [ContDiffMapSupportedIn.seminorm_apply]
  exact norm_le_pi_norm (compactTestJet K m φ) ⟨j, Nat.lt_succ_of_le (Finset.mem_Iic.mp hj)⟩

/-- A common bound on the first `m` derivative fields bounds the finite jet norm. -/
theorem norm_compactTestJet_le (K : Compacts Plane) (m : ℕ)
    (φ : ContDiffMapSupportedIn Plane ℝ ⊤ K) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j φ x‖ ≤ C) :
    ‖compactTestJet K m φ‖ ≤ C := by
  change ‖fun i : Fin (m + 1) => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i.val φ‖ ≤ C
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (BoundedContinuousFunction.norm_le hC).mpr
  intro x
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact hφ i.val (Nat.le_of_lt_succ i.isLt) x

/-- Evaluation of a chosen derivative field at a point. -/
def compactJetEvalCLM (m : ℕ) (i : Fin (m + 1)) (x : Plane) :
    CompactJetSpace m →L[ℝ] (Plane [×i.val]→L[ℝ] ℝ) :=
  (BoundedContinuousFunction.evalCLM (𝕜 := ℝ) x).comp (ContinuousLinearMap.proj i)

/-- Jet evaluation returns the selected derivative component at the chosen point. -/
@[simp] theorem compactJetEvalCLM_apply (m : ℕ) (i : Fin (m + 1)) (x : Plane)
    (J : CompactJetSpace m) : compactJetEvalCLM m i x J = J i x := rfl

/-- A distribution restricted to a fixed compact support extends continuously to a finite-order Banach jet space. -/
theorem exists_distribution_compact_jet_extension (T : Distr) (K : Compacts Plane) :
    ∃ (m : ℕ) (L : StrongDual ℝ (CompactJetSpace m)),
      ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
        L (compactTestJet K m φ) = T (TestFunction.ofSupportedIn (Set.subset_univ _) φ) := by
  obtain ⟨m, C, hC, hbound⟩ := exists_distribution_compact_order_bound T K
  let J := compactTestJet K m
  let e := LinearEquiv.ofInjective J.toLinearMap (compactTestJet_injective K m)
  let iK : ContDiffMapSupportedIn Plane ℝ ⊤ K →L[ℝ] TestFn :=
    TestFunction.ofSupportedInCLM ℝ (Set.subset_univ _)
  let f : Module.Dual ℝ J.toLinearMap.range :=
    (T.toLinearMap.comp iK.toLinearMap).comp e.symm.toLinearMap
  let p : Seminorm ℝ (CompactJetSpace m) := {
    toFun x := C * ‖x‖
    map_zero' := by simp only [norm_zero, mul_zero]
    add_le' x y := by
      simpa only [mul_add] using mul_le_mul_of_nonneg_left (norm_add_le x y) hC
    neg' x := by simp only [norm_neg]
    smul' c x := by rw [norm_smul]; ring }
  have hp : Continuous p := continuous_const.mul continuous_norm
  have hf : ∀ x : J.toLinearMap.range, ‖f x‖ ≤ p x.val := by
    intro x
    change ‖T (iK (e.symm x))‖ ≤ C * ‖x.val‖
    have hj : J (e.symm x) = x.val := LinearEquiv.ofInjective_symm_apply J.toLinearMap x
    calc
      _ ≤ C * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m (e.symm x) := hbound _
      _ ≤ C * ‖J (e.symm x)‖ :=
        mul_le_mul_of_nonneg_left (supSeminorm_le_norm_compactTestJet K m _) hC
      _ = _ := by rw [hj]
  obtain ⟨L, hL, _⟩ := Module.Dual.exists_continuous_extension_of_le_seminorm
    J.toLinearMap.range f hp hf
  refine ⟨m, L, fun φ => ?_⟩
  have he := hL (e φ)
  simpa only [e, iK, LinearEquiv.ofInjective_apply, f, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using! he

end Critical2DKPZ

end
