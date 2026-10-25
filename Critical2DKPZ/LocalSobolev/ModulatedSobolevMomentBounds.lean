/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichKernelFamilyBounds
public import Critical2DKPZ.Analysis.Sobolev.TestFunctionFamily

/-! # Uniform Sobolev bounds for compact families of Fourier modulations -/

@[expose] public section

noncomputable section

open Set
open TopologicalSpace
open scoped Distributions ENNReal

namespace Critical2DKPZ.LocalSobolev

private theorem contDiff_mulCos_family (χ : TestFn) :
    ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry fun ξ x => χ.mulCos ξ x) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun p : Plane × Plane => χ p.2 * Real.cos (inner ℝ p.1 p.2))
  exact (χ.contDiff.comp contDiff_snd).mul
    (Real.contDiff_cos.comp (contDiff_fst.inner ℝ contDiff_snd))

private theorem contDiff_mulSin_family (χ : TestFn) :
    ContDiff ℝ (⊤ : ℕ∞)
      (Function.uncurry fun ξ x => χ.mulSin ξ x) := by
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun p : Plane × Plane => χ p.2 * Real.sin (inner ℝ p.1 p.2))
  exact (χ.contDiff.comp contDiff_snd).mul
    (Real.contDiff_sin.comp (contDiff_fst.inner ℝ contDiff_snd))

/-- On every compact frequency ball, the cosine modulations of one test function have uniformly
bounded positive Sobolev norm. -/
theorem exists_uniform_sobolev_bound_mulCos (χ : TestFn) (s R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ ∈ Metric.closedBall (0 : Plane) R,
      Analysis.Sobolev.Rellich.sobolevNormSq 2 s (χ.mulCos ξ) ≤ ENNReal.ofReal C := by
  have hcompact : CompactSpace {ξ : Plane // ξ ∈ Metric.closedBall (0 : Plane) R} :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Plane) R)
  let α := {ξ : Plane // ξ ∈ Metric.closedBall (0 : Plane) R}
  let K : Compacts Plane := ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩
  let g : {ξ : Plane // ξ ∈ Metric.closedBall (0 : Plane) R} → Plane → ℝ :=
    fun ξ => χ.mulCos ξ.1
  have hK : IsCompact (tsupport χ) := χ.hasCompactSupport.isCompact
  let gK : Plane → 𝓓_{K}(Plane, ℝ) := fun ξ =>
    ⟨χ.mulCos ξ, (χ.mulCos ξ).contDiff, fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_mul_subset_left h))⟩
  have hgK : Continuous gK := by
    apply Critical2DKPZ.continuous_supported_test_family K gK
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => χ.mulCos p.1 p.2)
    exact contDiff_mulCos_family χ
  have hsm : ∀ ξ, ContDiff ℝ (⊤ : ℕ∞) (g ξ) := by
    intro ξ
    simpa [g] using (χ.mulCos ξ.1).contDiff
  have hsupp : ∀ ξ, tsupport (g ξ) ⊆ tsupport χ := by
    intro ξ
    change tsupport (fun x : Plane => χ x * Real.cos (inner ℝ ξ.1 x)) ⊆ tsupport χ
    exact tsupport_mul_subset_left
  have hcont (n : ℕ) : Continuous (fun z : α × Plane =>
      iteratedFDeriv ℝ n (g z.1) z.2) := by
    let D := fun ξ : Plane => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n (gK ξ)
    have hD : Continuous D :=
      (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n).continuous.comp hgK
    have hD' : Continuous (fun ξ : α => D ξ.1) := hD.comp continuous_subtype_val
    have hev : Continuous (fun z :
        BoundedContinuousFunction Plane
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ) × Plane => z.1 z.2) :=
      continuous_eval
    have hmap : Continuous (fun z : α × Plane => (D z.1.1, z.2)) :=
      (hD'.comp continuous_fst).prodMk continuous_snd
    have hevalBall : Continuous (fun z : α × Plane => D z.1.1 z.2) := by
      change Continuous ((fun p :
        BoundedContinuousFunction Plane
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ) × Plane => p.1 p.2) ∘
        (fun z : α × Plane => (D z.1.1, z.2)))
      exact hev.comp hmap
    have hEq : (fun z : α × Plane => iteratedFDeriv ℝ n (g z.1) z.2) =
        (fun z => D z.1.1 z.2) := by
      funext z
      simp only [D, ContDiffMapSupportedIn.structureMapCLM_top_apply]
      rfl
    rw [hEq]
    exact hevalBall
  obtain ⟨C, hC, hbound⟩ :=
    @Analysis.Sobolev.Rellich.exists_uniform_sobolev_kernel_bound
      2 {ξ : Plane // ξ ∈ Metric.closedBall (0 : Plane) R} inferInstance hcompact
      g (tsupport χ) hK hsm hsupp hcont s
  refine ⟨C, hC, ?_⟩
  intro ξ hξ
  exact hbound ⟨ξ, hξ⟩

/-- On every compact frequency ball, the sine modulations of one test function have uniformly
bounded positive Sobolev norm. -/
theorem exists_uniform_sobolev_bound_mulSin (χ : TestFn) (s R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ ∈ Metric.closedBall (0 : Plane) R,
      Analysis.Sobolev.Rellich.sobolevNormSq 2 s (χ.mulSin ξ) ≤ ENNReal.ofReal C := by
  have hcompact : CompactSpace {ξ : Plane // ξ ∈ Metric.closedBall (0 : Plane) R} :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Plane) R)
  let α := {ξ : Plane // ξ ∈ Metric.closedBall (0 : Plane) R}
  let K : Compacts Plane := ⟨tsupport χ, χ.hasCompactSupport.isCompact⟩
  let g : {ξ : Plane // ξ ∈ Metric.closedBall (0 : Plane) R} → Plane → ℝ :=
    fun ξ => χ.mulSin ξ.1
  have hK : IsCompact (tsupport χ) := χ.hasCompactSupport.isCompact
  let gK : Plane → 𝓓_{K}(Plane, ℝ) := fun ξ =>
    ⟨χ.mulSin ξ, (χ.mulSin ξ).contDiff, fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_mul_subset_left h))⟩
  have hgK : Continuous gK := by
    apply Critical2DKPZ.continuous_supported_test_family K gK
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => χ.mulSin p.1 p.2)
    exact contDiff_mulSin_family χ
  have hsm : ∀ ξ, ContDiff ℝ (⊤ : ℕ∞) (g ξ) := by
    intro ξ
    simpa [g] using (χ.mulSin ξ.1).contDiff
  have hsupp : ∀ ξ, tsupport (g ξ) ⊆ tsupport χ := by
    intro ξ
    change tsupport (fun x : Plane => χ x * Real.sin (inner ℝ ξ.1 x)) ⊆ tsupport χ
    exact tsupport_mul_subset_left
  have hcont (n : ℕ) : Continuous (fun z : α × Plane =>
      iteratedFDeriv ℝ n (g z.1) z.2) := by
    let D := fun ξ : Plane => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n (gK ξ)
    have hD : Continuous D :=
      (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n).continuous.comp hgK
    have hD' : Continuous (fun ξ : α => D ξ.1) := hD.comp continuous_subtype_val
    have hev : Continuous (fun z :
        BoundedContinuousFunction Plane
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ) × Plane => z.1 z.2) :=
      continuous_eval
    have hmap : Continuous (fun z : α × Plane => (D z.1.1, z.2)) :=
      (hD'.comp continuous_fst).prodMk continuous_snd
    have hevalBall : Continuous (fun z : α × Plane => D z.1.1 z.2) := by
      change Continuous ((fun p :
        BoundedContinuousFunction Plane
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => Plane) ℝ) × Plane => p.1 p.2) ∘
        (fun z : α × Plane => (D z.1.1, z.2)))
      exact hev.comp hmap
    have hEq : (fun z : α × Plane => iteratedFDeriv ℝ n (g z.1) z.2) =
        (fun z => D z.1.1 z.2) := by
      funext z
      simp only [D, ContDiffMapSupportedIn.structureMapCLM_top_apply]
      rfl
    rw [hEq]
    exact hevalBall
  obtain ⟨C, hC, hbound⟩ :=
    @Analysis.Sobolev.Rellich.exists_uniform_sobolev_kernel_bound
      2 {ξ : Plane // ξ ∈ Metric.closedBall (0 : Plane) R} inferInstance hcompact
      g (tsupport χ) hK hsm hsupp hcont s
  refine ⟨C, hC, ?_⟩
  intro ξ hξ
  exact hbound ⟨ξ, hξ⟩

end Critical2DKPZ.LocalSobolev

end
