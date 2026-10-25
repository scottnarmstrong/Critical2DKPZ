/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.SmoothCompactSupport
public import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.Convolution

/-!
# Distributional integration against translates of a compact kernel

A compactly supported smooth kernel of integral one averages translates of a test function back
to that same test function. The distributional integral identity applies this averaging inside any
real distribution.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions Pointwise

namespace Critical2DKPZ.Analysis.Sobolev

/-- Averaging a compactly supported test function against translates of a compactly supported
unit-mass kernel commutes with every real distribution. -/
theorem distribution_integral_translated_testFn (T : Distr) (φ ρ : TestFn)
    (hρ : ∫ x : Plane, ρ x = 1) :
    ∃ (K S : Compacts Plane)
      (F : Plane → ContDiffMapSupportedIn Plane ℝ ⊤ K),
      ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2) ∧
      (∀ y, y ∉ S → F y = 0) ∧
      (∀ x, φ x = ∫ y, F y x) ∧
      Continuous (fun y => T (TestFunction.ofSupportedIn (Set.subset_univ _) (F y))) ∧
      HasCompactSupport (fun y => T (TestFunction.ofSupportedIn (Set.subset_univ _) (F y))) ∧
      Integrable (fun y => T (TestFunction.ofSupportedIn (Set.subset_univ _) (F y))) volume ∧
      T φ =
        ∫ y, T (TestFunction.ofSupportedIn (Set.subset_univ _) (F y)) := by
  let K : Compacts Plane := ⟨tsupport φ, φ.hasCompactSupport.isCompact⟩
  let L : Compacts Plane := ⟨tsupport ρ, ρ.hasCompactSupport.isCompact⟩
  let S : Compacts Plane := ⟨(K : Set Plane) + (L : Set Plane), K.2.add L.2⟩
  let F (y : Plane) : ContDiffMapSupportedIn Plane ℝ ⊤ K := {
    toFun := fun x => φ x * ρ (y - x)
    contDiff' := by
      have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => y - x) := by
        simpa only [id_eq] using (contDiff_const.sub contDiff_id)
      exact φ.contDiff.mul (ρ.contDiff.comp hs)
    zero_on_compl' := by
      intro x hx
      have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hφ] }
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => F p.1 p.2) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => φ p.2 * ρ (p.1 - p.2))
    exact (φ.contDiff.comp contDiff_snd).mul
      (ρ.contDiff.comp (contDiff_fst.sub contDiff_snd))
  have hS : ∀ y, y ∉ S → F y = 0 := by
    intro y hy
    apply ContDiffMapSupportedIn.ext
    intro x
    change φ x * ρ (y - x) = 0
    by_cases hφ : φ x = 0
    · simp [hφ]
    · by_cases hρx : ρ (y - x) = 0
      · simp [hρx]
      · have hx : x ∈ (K : Set Plane) := subset_tsupport φ hφ
        have hyx : y - x ∈ (L : Set Plane) := subset_tsupport ρ hρx
        have hmem : y ∈ (K : Set Plane) + (L : Set Plane) := by
          have hadd := Set.add_mem_add hx hyx
          convert hadd using 1
          abel
        exact (hy hmem).elim
  have hφ : ∀ x, φ x = ∫ y, F y x := by
    intro x
    change φ x = ∫ y, φ x * ρ (y - x)
    rw [integral_const_mul]
    rw [integral_sub_right_eq_self (fun y : Plane => ρ y) x]
    rw [hρ]
    simp
  have hcomm := distribution_integral_compact_smooth_test_family volume T S K F hF hS
    (⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport hx⟩) hφ
  have hcF := continuous_supported_test_family K F hF
  have hcIncl : Continuous (fun g : ContDiffMapSupportedIn Plane ℝ ⊤ K =>
      TestFunction.ofSupportedIn (Set.subset_univ _) g) :=
    TestFunction.continuous_ofSupportedIn (F := ℝ) (n := ⊤)
      (show (K : Set Plane) ⊆ (⊤ : Opens Plane) from fun _ _ => trivial)
  have hcont : Continuous (fun y =>
      T (TestFunction.ofSupportedIn (Set.subset_univ _) (F y))) :=
    T.continuous.comp (hcIncl.comp hcF)
  have hparamSupport : HasCompactSupport (fun y =>
      T (TestFunction.ofSupportedIn (Set.subset_univ _) (F y))) := by
    apply HasCompactSupport.of_support_subset_isCompact S.2
    intro y hy
    by_contra hys
    have hzero : T (TestFunction.ofSupportedIn (Set.subset_univ _) (F y)) = 0 := by
      rw [hS y hys]
      have hzeroFn : TestFunction.ofSupportedIn (Set.subset_univ _)
          (0 : ContDiffMapSupportedIn Plane ℝ ⊤ K) = (0 : TestFn) := by
        ext x
        rfl
      rw [hzeroFn]
      exact map_zero T
    exact (Function.mem_support.mp hy) hzero
  have hparamInt : Integrable (fun y =>
      T (TestFunction.ofSupportedIn (Set.subset_univ _) (F y))) volume :=
    hcont.integrable_of_hasCompactSupport hparamSupport
  have hco : TestFunction.ofSupportedIn (Set.subset_univ _)
      (⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport hx⟩ :
        ContDiffMapSupportedIn Plane ℝ ⊤ K) = φ := by
    ext x
    rfl
  refine ⟨K, S, F, hF, hS, hφ, hcont, hparamSupport, hparamInt, ?_⟩
  rw [← hco]
  exact hcomm

end Critical2DKPZ.Analysis.Sobolev

end
