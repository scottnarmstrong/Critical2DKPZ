/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.TranslatedTestIntegral

/-!
# Continuous compactly supported translated pairings of distributions

A real distribution paired against translates of a compact smooth kernel defines a continuous,
compactly supported function of the translation parameter. Its integral recovers the original
test-function pairing when the kernel has mass one.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions Pointwise

namespace Critical2DKPZ.Analysis.Sobolev

/-- The compact set used to package the support of a test function. -/
def compactTestSupport (φ : TestFn) : Compacts Plane :=
  ⟨tsupport φ, φ.hasCompactSupport.isCompact⟩

/-- The translated product family `x ↦ φ(x)ρ(y-x)` on the fixed support of `φ`. -/
@[expose] def translatedTestFamily (φ ρ : TestFn) (y : Plane) :
    ContDiffMapSupportedIn Plane ℝ ⊤ (compactTestSupport φ) := {
  toFun := fun x => φ x * ρ (y - x)
  contDiff' := by
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => y - x) := by
      simpa only [id_eq] using (contDiff_const.sub contDiff_id)
    exact φ.contDiff.mul (ρ.contDiff.comp hs)
  zero_on_compl' := by
    intro x hx
    have hφ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [hφ] }

/-- The translated test family is jointly smooth in the translation and test variables. -/
theorem contDiff_translatedTestFamily (φ ρ : TestFn) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Plane × Plane => translatedTestFamily φ ρ p.1 p.2) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : Plane × Plane => φ p.2 * ρ (p.1 - p.2))
  exact (φ.contDiff.comp contDiff_snd).mul
    (ρ.contDiff.comp (contDiff_fst.sub contDiff_snd))

/-- Outside the sum of the two test supports, the translated family vanishes. -/
theorem translatedTestFamily_eq_zero_outside (φ ρ : TestFn) {y : Plane}
    (hy : y ∉ (compactTestSupport φ : Set Plane) + (compactTestSupport ρ : Set Plane)) :
    translatedTestFamily φ ρ y = 0 := by
  apply ContDiffMapSupportedIn.ext
  intro x
  change φ x * ρ (y - x) = 0
  by_cases hφ : φ x = 0
  · simp [hφ]
  · by_cases hρ : ρ (y - x) = 0
    · simp [hρ]
    · have hx : x ∈ compactTestSupport φ := subset_tsupport φ hφ
      have hyx : y - x ∈ compactTestSupport ρ := subset_tsupport ρ hρ
      have hmem : y ∈ (compactTestSupport φ : Set Plane) + (compactTestSupport ρ : Set Plane) := by
        have hadd := Set.add_mem_add hx hyx
        convert hadd using 1
        abel
      exact (hy hmem).elim

/-- A distribution paired against a translated test family. -/
@[expose] def translatedDistributionPairing (T : Distr) (φ ρ : TestFn) (y : Plane) : ℝ :=
  T (TestFunction.ofSupportedIn (Set.subset_univ _) (translatedTestFamily φ ρ y))

/-- Evaluation formula for the translated distribution pairing. -/
@[simp] theorem translatedDistributionPairing_apply (T : Distr) (φ ρ : TestFn) (y : Plane) :
    translatedDistributionPairing T φ ρ y =
      T (TestFunction.ofSupportedIn (Set.subset_univ _) (translatedTestFamily φ ρ y)) := rfl

/-- The translated distribution pairing is continuous. -/
theorem continuous_translatedDistributionPairing (T : Distr) (φ ρ : TestFn) :
    Continuous (translatedDistributionPairing T φ ρ) := by
  let K := compactTestSupport φ
  have hF := continuous_supported_test_family K (translatedTestFamily φ ρ)
    (contDiff_translatedTestFamily φ ρ)
  have hI : Continuous (fun f : ContDiffMapSupportedIn Plane ℝ ⊤ K =>
      TestFunction.ofSupportedIn (Set.subset_univ _) f) :=
    TestFunction.continuous_ofSupportedIn (F := ℝ) (n := ⊤)
      (show (K : Set Plane) ⊆ (⊤ : Opens Plane) from fun _ _ => trivial)
  exact T.continuous.comp (hI.comp hF)

/-- The translated distribution pairing is compactly supported in the sum of the two test
supports. -/
theorem hasCompactSupport_translatedDistributionPairing (T : Distr) (φ ρ : TestFn) :
    HasCompactSupport (translatedDistributionPairing T φ ρ) := by
  let K := compactTestSupport φ
  let L := compactTestSupport ρ
  have hKL : IsCompact ((K : Set Plane) + (L : Set Plane)) := K.2.add L.2
  apply HasCompactSupport.of_support_subset_isCompact hKL
  intro y hy
  by_contra hys
  have hzero : translatedDistributionPairing T φ ρ y = 0 := by
    change T (TestFunction.ofSupportedIn (Set.subset_univ _) (translatedTestFamily φ ρ y)) = 0
    rw [translatedTestFamily_eq_zero_outside φ ρ hys]
    have hzeroFn : TestFunction.ofSupportedIn (Set.subset_univ _)
        (0 : ContDiffMapSupportedIn Plane ℝ ⊤ K) = (0 : TestFn) := by
      ext x
      rfl
    rw [hzeroFn]
    exact map_zero T
  exact (Function.mem_support.mp hy) hzero

/-- The translated distribution pairing is Bochner integrable. -/
theorem integrable_translatedDistributionPairing (T : Distr) (φ ρ : TestFn) :
    Integrable (translatedDistributionPairing T φ ρ) volume :=
  (continuous_translatedDistributionPairing T φ ρ).integrable_of_hasCompactSupport
    (hasCompactSupport_translatedDistributionPairing T φ ρ)

/-- Integrating the translated distribution pairing recovers the original test-function pairing
when the kernel has mass one. -/
theorem integral_translatedDistributionPairing (T : Distr) (φ ρ : TestFn)
    (hρ : ∫ x : Plane, ρ x = 1) :
    ∫ y, translatedDistributionPairing T φ ρ y = T φ := by
  let K := compactTestSupport φ
  let L := compactTestSupport ρ
  let S : Compacts Plane := ⟨(K : Set Plane) + (L : Set Plane), K.2.add L.2⟩
  have hF := contDiff_translatedTestFamily φ ρ
  have hS : ∀ y, y ∉ (K : Set Plane) + (L : Set Plane) →
      translatedTestFamily φ ρ y = 0 := by
    intro y hy
    exact translatedTestFamily_eq_zero_outside φ ρ hy
  have hφ : ∀ x, φ x = ∫ y, translatedTestFamily φ ρ y x := by
    intro x
    change φ x = ∫ y, φ x * ρ (y - x)
    rw [integral_const_mul]
    rw [integral_sub_right_eq_self (fun y : Plane => ρ y) x]
    rw [hρ]
    simp
  let φK : ContDiffMapSupportedIn Plane ℝ ⊤ K :=
    ⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport hx⟩
  have hcomm := distribution_integral_compact_smooth_test_family volume T S K
    (translatedTestFamily φ ρ) hF hS φK hφ
  have hco : TestFunction.ofSupportedIn (Set.subset_univ _) φK = φ := by
    ext x
    rfl
  calc
    ∫ y, translatedDistributionPairing T φ ρ y
        = ∫ y, T (TestFunction.ofSupportedIn (Set.subset_univ _)
            (translatedTestFamily φ ρ y)) := rfl
    _ = T (TestFunction.ofSupportedIn (Set.subset_univ _) φK) := hcomm.symm
    _ = T φ := by rw [hco]

end Critical2DKPZ.Analysis.Sobolev

end
