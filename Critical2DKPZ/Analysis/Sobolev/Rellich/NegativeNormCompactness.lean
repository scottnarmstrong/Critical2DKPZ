/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichConvolvedCompact
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! A finite set of test pairings controls a weaker negative Sobolev norm up to an error bounded by a stronger norm.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal FourierTransform Topology

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

variable {d : ℕ} {D : Set (Space d)}

/-- Multiplication by a scalar preserves the test-function class. -/
theorem IsTestFn.const_mul {φ : Space d → ℝ} (hφ : IsTestFn D φ) (c : ℝ) :
    IsTestFn D (fun x => c * φ x) := by
  refine ⟨hφ.1.const_smul c, ?_, ?_⟩
  · apply hφ.2.1.mono
    intro x hx
    by_contra h
    rw [Function.mem_support] at hx
    exact hx (by rw [Function.notMem_support.mp h, mul_zero])
  exact (tsupport_mul_subset_right (f := fun _ : Space d => c) (g := φ)).trans hφ.2.2

/-- The test-function class is closed under addition. -/
theorem IsTestFn.add {φ ψ : Space d → ℝ} (hφ : IsTestFn D φ) (hψ : IsTestFn D ψ) :
    IsTestFn D (fun x => φ x + ψ x) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  calc tsupport (fun x => φ x + ψ x)
      ⊆ closure (Function.support φ ∪ Function.support ψ) :=
        closure_mono (by
          intro x hx
          simp only [Function.mem_support, ne_eq] at hx ⊢
          by_cases hφ0 : φ x = 0
          · right
            intro hψ0
            exact hx (by simp [hφ0, hψ0])
          · exact Or.inl hφ0)
    _ = tsupport φ ∪ tsupport ψ := closure_union
    _ ⊆ D := Set.union_subset hφ.2.2 hψ.2.2

/-- The test-function class is closed under subtraction. -/
theorem IsTestFn.sub {φ ψ : Space d → ℝ} (hφ : IsTestFn D φ) (hψ : IsTestFn D ψ) :
    IsTestFn D (fun x => φ x - ψ x) := by
  refine ⟨hφ.1.sub hψ.1, hφ.2.1.sub hψ.2.1, ?_⟩
  calc tsupport (fun x => φ x - ψ x)
      ⊆ closure (Function.support φ ∪ Function.support ψ) :=
        closure_mono (fun x hx => by
          simp only [Function.mem_support, sub_ne_zero] at hx
          by_cases h : φ x = 0
          · exact Or.inr (by simpa [h, eq_comm] using hx)
          · exact Or.inl h)
    _ = tsupport φ ∪ tsupport ψ := closure_union
    _ ⊆ D := Set.union_subset hφ.2.2 hψ.2.2

/-- Regard a smooth compactly supported planar function as a test function. -/
def testFnOfRellich {φ : Space 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcs : HasCompactSupport φ) : TestFn :=
  ⟨φ, hφ, hcs, Set.subset_univ _⟩

/-- Extend a distribution pairing to arbitrary functions by zero outside the smooth compactly supported test class. This extension is linear on test functions. -/
noncomputable def distributionFunctional (T : Distr) (φ : Space 2 → ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ ψ : TestFn, (ψ : Plane → ℝ) = φ then T h.choose else 0

/-- On a smooth compactly supported test, `distributionFunctional` agrees with the distribution pairing. -/
theorem distributionFunctional_apply {D : Set (Space 2)} (T : Distr)
    {φ : Space 2 → ℝ} (hφ : IsTestFn D φ) :
    distributionFunctional T φ = T (testFnOfRellich hφ.1 hφ.2.1) := by
  classical
  let ψ₀ : TestFn := testFnOfRellich hφ.1 hφ.2.1
  have hex : ∃ ψ : TestFn, (ψ : Plane → ℝ) = φ := ⟨ψ₀, rfl⟩
  have heq : hex.choose = ψ₀ := by
    apply TestFunction.ext
    intro x
    exact congrFun (Classical.choose_spec hex) x
  unfold distributionFunctional
  rw [dite_eq_left hex, heq]

/-- The test-function representative of a sum is the sum of the representatives. -/
theorem testFunction_mk_add {D : Set (Space 2)} {φ ψ : Space 2 → ℝ}
    (hφ : IsTestFn D φ) (hψ : IsTestFn D ψ) :
    testFnOfRellich (hφ.add hψ).1 (hφ.add hψ).2.1 =
      testFnOfRellich hφ.1 hφ.2.1 + testFnOfRellich hψ.1 hψ.2.1 := by
  apply TestFunction.ext
  intro x
  rfl

/-- The test-function representative of a scalar multiple is the scalar multiple of its
representative. -/
theorem testFunction_mk_const_mul {D : Set (Space 2)} {φ : Space 2 → ℝ}
    (hφ : IsTestFn D φ) (c : ℝ) :
    testFnOfRellich (hφ.const_mul c).1 (hφ.const_mul c).2.1 =
      c • testFnOfRellich hφ.1 hφ.2.1 := by
  apply TestFunction.ext
  intro x
  change c * φ x = c * φ x
  rfl

/-- A distribution pairing is additive on the smooth compactly supported test-function class. -/
theorem distributionFunctional_add {D : Set (Space 2)} (T : Distr)
    {φ ψ : Space 2 → ℝ} (hφ : IsTestFn D φ) (hψ : IsTestFn D ψ) :
    distributionFunctional T (φ + ψ) = distributionFunctional T φ + distributionFunctional T ψ := by
  change distributionFunctional T (fun x => φ x + ψ x) = _
  rw [distributionFunctional_apply T (hφ.add hψ), distributionFunctional_apply T hφ,
    distributionFunctional_apply T hψ, testFunction_mk_add hφ hψ, map_add]

/-- A distribution pairing is homogeneous on the smooth compactly supported test-function class. -/
theorem distributionFunctional_smul {D : Set (Space 2)} (T : Distr)
    {φ : Space 2 → ℝ} (hφ : IsTestFn D φ) (c : ℝ) :
    distributionFunctional T (fun x => c * φ x) = c * distributionFunctional T φ := by
  rw [distributionFunctional_apply T (hφ.const_mul c), distributionFunctional_apply T hφ,
    testFunction_mk_const_mul hφ c, map_smul]
  simp [smul_eq_mul]

/-- A test function whose `H^s` square is at most `η²` has pairing bounded by `η` times the
negative Sobolev dual norm. -/
theorem abs_apply_le_negSobolevNorm (s η : ℝ) (hη : 0 < η)
    (F : (Space d → ℝ) → ℝ)
    (hsmul : ∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
      F (fun x => c * φ x) = c * F φ)
    {φ : Space d → ℝ} (hφ : IsTestFn D φ)
    (hn : sobolevNormSq d s φ ≤ ENNReal.ofReal (η ^ 2)) :
    ENNReal.ofReal |F φ| ≤ ENNReal.ofReal η * negSobolevNorm d s D F := by
  have hscale : sobolevNormSq d s (fun x => (1 / η) * φ x) ≤ 1 := by
    rw [sobolevNormSq_const_mul]
    calc ENNReal.ofReal ((1 / η) ^ 2) * sobolevNormSq d s φ
        ≤ ENNReal.ofReal ((1 / η) ^ 2) * ENNReal.ofReal (η ^ 2) := mul_le_mul_right hn _
      _ = ENNReal.ofReal ((1 / η) ^ 2 * η ^ 2) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ = 1 := by
        rw [show (1 / η) ^ 2 * η ^ 2 = 1 by field_simp]
        simp
  have hφ' : IsTestFn D (fun x => (1 / η) * φ x) := hφ.const_mul _
  have h1 : ENNReal.ofReal |F (fun x => (1 / η) * φ x)| ≤ negSobolevNorm d s D F :=
    le_sSup ⟨_, hφ', hscale, rfl⟩
  rw [hsmul _ φ hφ] at h1
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / η)] at h1
  calc ENNReal.ofReal |F φ|
      = ENNReal.ofReal (η * ((1 / η) * |F φ|)) := by
          rw [show η * ((1 / η) * |F φ|) = |F φ| by field_simp]
    _ = ENNReal.ofReal η * ENNReal.ofReal ((1 / η) * |F φ|) :=
        ENNReal.ofReal_mul (by positivity)
    _ ≤ ENNReal.ofReal η * negSobolevNorm d s D F := mul_le_mul_right h1 _

/-- A finite `η`-net of the `H^s` unit ball in `H^{s₀}` bounds the `H^{-s}` dual norm by its
finite set of pairings, plus `η` times the `H^{-s₀}` dual norm. -/
theorem negSobolevNorm_le_sup_add {s₀ s : ℝ}
    (η : ℝ) (hη : 0 < η) (N : ℕ) (ψ : Fin N → Space d → ℝ) (M : ℝ≥0∞)
    (hψt : ∀ i, IsTestFn D (ψ i))
    (hnet : ∀ φ : Space d → ℝ, IsTestFn D φ → sobolevNormSq d s φ ≤ 1 →
      ∃ i, sobolevNormSq d s₀ (fun x => φ x - ψ i x) ≤ ENNReal.ofReal (η ^ 2))
    (F : (Space d → ℝ) → ℝ)
    (hadd : ∀ φ ψ : Space d → ℝ, IsTestFn D φ → IsTestFn D ψ →
      F (φ + ψ) = F φ + F ψ)
    (hsmul : ∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
      F (fun x => c * φ x) = c * F φ)
    (hF : negSobolevNorm d s₀ D F ≤ M) :
    negSobolevNorm d s D F ≤
      (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η * M := by
  unfold negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  obtain ⟨i, hi⟩ := hnet φ hφ hn
  have hsmall : ENNReal.ofReal |F (fun x => φ x - ψ i x)| ≤ ENNReal.ofReal η * M := by
    have h1 := abs_apply_le_negSobolevNorm (D := D) s₀ η hη F hsmul
      (hφ.sub (hψt i)) hi
    calc ENNReal.ofReal |F (fun x => φ x - ψ i x)|
        ≤ ENNReal.ofReal η * negSobolevNorm d s₀ D F := h1
      _ ≤ ENNReal.ofReal η * M := mul_le_mul_right hF _
  have hg : (fun x : Space d => φ x - ψ i x) = φ + (fun x => (-1) * ψ i x) := by
    funext x
    simp
    ring
  have hsplit : F φ = F (fun x => φ x - ψ i x) + F (ψ i) := by
    rw [hg, hadd φ _ hφ ((hψt i).const_mul _), hsmul (-1) (ψ i) (hψt i)]
    ring
  calc ENNReal.ofReal |F φ|
      = ENNReal.ofReal |F (fun x => φ x - ψ i x) + F (ψ i)| := by rw [hsplit]
    _ ≤ ENNReal.ofReal (|F (fun x => φ x - ψ i x)| + |F (ψ i)|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ENNReal.ofReal |F (fun x => φ x - ψ i x)| + ENNReal.ofReal |F (ψ i)| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ ENNReal.ofReal η * M + (⨆ i, ENNReal.ofReal |F (ψ i)|) :=
          add_le_add hsmall (le_iSup (fun i => ENNReal.ofReal |F (ψ i)|) i)
    _ = (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η * M := add_comm _ _

/-- The Rellich finite-net theorem gives a finite-coordinate estimate for every linear functional
bounded in the stronger negative Sobolev norm. -/
theorem negSobolevNorm_le_finset_sup_add (hD : IsDomain D) {s₀ s : ℝ} (h : s₀ < s)
    (η : ℝ) (hη : 0 < η) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
      ∀ F : (Space d → ℝ) → ℝ,
        (∀ φ ψ : Space d → ℝ, IsTestFn D φ → IsTestFn D ψ →
          F (φ + ψ) = F φ + F ψ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
          F (fun x => c * φ x) = c * F φ) →
        negSobolevNorm d s₀ D F ≤ 1 →
          negSobolevNorm d s D F ≤ (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η := by
  obtain ⟨N, ψ, hψt, hnet⟩ :=
    rellichKondrachovNegSobolev_holds d D hD s₀ s h η hη
  refine ⟨N, ψ, hψt, ?_⟩
  intro F hadd hsmul hF
  simpa using (negSobolevNorm_le_sup_add (D := D) η hη N ψ 1 hψt hnet F hadd hsmul hF)

/-- If the finitely many pairings supplied by Rellich are uniformly bounded by `B`, then the
weaker negative Sobolev dual norm is bounded by `B + η`. -/
theorem negSobolevNorm_le_of_finset_pairing_bound (hD : IsDomain D) {s₀ s : ℝ}
    (h : s₀ < s) (η : ℝ) (hη : 0 < η) (B : ℝ≥0∞) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
      ∀ F : (Space d → ℝ) → ℝ,
        (∀ φ ψ : Space d → ℝ, IsTestFn D φ → IsTestFn D ψ →
          F (φ + ψ) = F φ + F ψ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
          F (fun x => c * φ x) = c * F φ) →
        negSobolevNorm d s₀ D F ≤ 1 →
        (∀ i, ENNReal.ofReal |F (ψ i)| ≤ B) →
          negSobolevNorm d s D F ≤ B + ENNReal.ofReal η := by
  obtain ⟨N, ψ, hψt, hbound⟩ := negSobolevNorm_le_finset_sup_add hD h η hη
  refine ⟨N, ψ, hψt, fun F hadd hsmul hF hcoords => ?_⟩
  calc negSobolevNorm d s D F
      ≤ (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η :=
        hbound F hadd hsmul hF
    _ ≤ B + ENNReal.ofReal η := add_le_add (iSup_le hcoords) le_rfl

/-- A finite Rellich net controls the weaker negative norm for any prescribed stronger-norm
bound. The error scales with that bound. -/
theorem negSobolevNorm_le_of_finset_pairings (hD : IsDomain D) {s₀ s : ℝ}
    (h : s₀ < s) (η : ℝ) (hη : 0 < η) (M B : ℝ≥0∞) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
      ∀ F : (Space d → ℝ) → ℝ,
        (∀ φ ψ : Space d → ℝ, IsTestFn D φ → IsTestFn D ψ →
          F (φ + ψ) = F φ + F ψ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
          F (fun x => c * φ x) = c * F φ) →
        negSobolevNorm d s₀ D F ≤ M →
        (∀ i, ENNReal.ofReal |F (ψ i)| ≤ B) →
          negSobolevNorm d s D F ≤ B + ENNReal.ofReal η * M := by
  obtain ⟨N, ψ, hψt, hnet⟩ :=
    rellichKondrachovNegSobolev_holds d D hD s₀ s h η hη
  refine ⟨N, ψ, hψt, fun F hadd hsmul hF hcoords => ?_⟩
  calc negSobolevNorm d s D F
      ≤ (⨆ i, ENNReal.ofReal |F (ψ i)|) + ENNReal.ofReal η * M :=
        negSobolevNorm_le_sup_add (D := D) η hη N ψ M hψt hnet F hadd hsmul hF
    _ ≤ B + ENNReal.ofReal η * M :=
      add_le_add (iSup_le hcoords) le_rfl

/-- On a common finite Rellich net, bounded stronger norms and close pairings imply a bound on the
weaker negative norm of the difference. -/
theorem negSobolevNorm_sub_le_of_finset_pairings_with_unit_centers
    (hD : IsDomain D) {s₀ s : ℝ}
    (h : s₀ < s) (η : ℝ) (hη : 0 < η) (M B : ℝ≥0∞) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ),
      (∀ i, IsTestFn D (ψ i) ∧ sobolevNormSq d s (ψ i) ≤ 1) ∧
      ∀ F G : (Space d → ℝ) → ℝ,
        (∀ φ χ : Space d → ℝ, IsTestFn D φ → IsTestFn D χ →
          F (φ + χ) = F φ + F χ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
          F (fun x => c * φ x) = c * F φ) →
        (∀ φ χ : Space d → ℝ, IsTestFn D φ → IsTestFn D χ →
          G (φ + χ) = G φ + G χ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
          G (fun x => c * φ x) = c * G φ) →
        negSobolevNorm d s₀ D F ≤ M → negSobolevNorm d s₀ D G ≤ M →
        (∀ i, ENNReal.ofReal |F (ψ i) - G (ψ i)| ≤ B) →
          negSobolevNorm d s D (fun φ => F φ - G φ) ≤
            B + ENNReal.ofReal η * (M + M) := by
  obtain ⟨N, ψ, hψunit, hnet⟩ :=
    rellichKondrachovNegSobolev_holds_with_unit_centers d D hD s₀ s h η hη
  have hψt : ∀ i, IsTestFn D (ψ i) := fun i => (hψunit i).1
  refine ⟨N, ψ, hψunit, fun F G hFadd hFsmul hGadd hGsmul hF hG hcoords => ?_⟩
  have hsubadd : ∀ φ χ : Space d → ℝ, IsTestFn D φ → IsTestFn D χ →
      (fun x => F x - G x) (φ + χ) = (fun x => F x - G x) φ + (fun x => F x - G x) χ := by
    intro φ χ hφ hχ
    change F (φ + χ) - G (φ + χ) = (F φ - G φ) + (F χ - G χ)
    rw [hFadd φ χ hφ hχ, hGadd φ χ hφ hχ]
    ring
  have hsubsmul : ∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
      (fun x => F x - G x) (fun x => c * φ x) = c * (fun x => F x - G x) φ := by
    intro c φ hφ
    change F (fun x => c * φ x) - G (fun x => c * φ x) = c * (F φ - G φ)
    rw [hFsmul c φ hφ, hGsmul c φ hφ]
    ring
  have hsubnorm : negSobolevNorm d s₀ D (fun φ => F φ - G φ) ≤ M + M := by
    exact (negSobolevNorm_sub_le s₀ D F G).trans (add_le_add hF hG)
  have hres := negSobolevNorm_le_sup_add (D := D) η hη N ψ (M + M) hψt hnet
    (fun φ => F φ - G φ) hsubadd hsubsmul hsubnorm
  calc
    negSobolevNorm d s D (fun φ => F φ - G φ)
        ≤ (⨆ i, ENNReal.ofReal |F (ψ i) - G (ψ i)|) + ENNReal.ofReal η * (M + M) := hres
    _ ≤ B + ENNReal.ofReal η * (M + M) := add_le_add (iSup_le hcoords) le_rfl

/-- A finite set of test functions controls the weaker negative Sobolev norm of a difference from bounds on the stronger norms and on those test pairings. -/
theorem negSobolevNorm_sub_le_of_finset_pairings (hD : IsDomain D) {s₀ s : ℝ}
    (h : s₀ < s) (η : ℝ) (hη : 0 < η) (M B : ℝ≥0∞) :
    ∃ (N : ℕ) (ψ : Fin N → Space d → ℝ), (∀ i, IsTestFn D (ψ i)) ∧
      ∀ F G : (Space d → ℝ) → ℝ,
        (∀ φ χ : Space d → ℝ, IsTestFn D φ → IsTestFn D χ →
          F (φ + χ) = F φ + F χ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
          F (fun x => c * φ x) = c * F φ) →
        (∀ φ χ : Space d → ℝ, IsTestFn D φ → IsTestFn D χ →
          G (φ + χ) = G φ + G χ) →
        (∀ (c : ℝ) (φ : Space d → ℝ), IsTestFn D φ →
          G (fun x => c * φ x) = c * G φ) →
        negSobolevNorm d s₀ D F ≤ M → negSobolevNorm d s₀ D G ≤ M →
        (∀ i, ENNReal.ofReal |F (ψ i) - G (ψ i)| ≤ B) →
          negSobolevNorm d s D (fun φ => F φ - G φ) ≤
            B + ENNReal.ofReal η * (M + M) := by
  obtain ⟨N, ψ, hψ, hnet⟩ :=
    negSobolevNorm_sub_le_of_finset_pairings_with_unit_centers hD h η hη M B
  exact ⟨N, ψ, fun i => (hψ i).1, hnet⟩

/-- A sequence of linear functionals that is uniformly bounded in `H^{-s₀}` and Cauchy on every
test function is Cauchy in the weaker `H^{-s}` dual norm when `s₀ < s`. -/
theorem cauchySeq_negSobolevNorm_of_pointwise_cauchy (hD : IsDomain D) {s₀ s : ℝ}
    (h : s₀ < s) {M : ℝ} (hM : 0 ≤ M)
    (F : ℕ → (Space d → ℝ) → ℝ)
    (hadd : ∀ n φ ψ, IsTestFn D φ → IsTestFn D ψ →
      F n (φ + ψ) = F n φ + F n ψ)
    (hsmul : ∀ n (c : ℝ) φ, IsTestFn D φ →
      F n (fun x => c * φ x) = c * F n φ)
    (hbound : ∀ n, negSobolevNorm d s₀ D (F n) ≤ ENNReal.ofReal M)
    (hpair : ∀ φ, IsTestFn D φ → ∀ δ : ℝ, 0 < δ →
      ∃ K, ∀ n m, K ≤ n → K ≤ m → |F n φ - F m φ| ≤ δ) :
    ∀ ε : ℝ, 0 < ε → ∃ K, ∀ n m, K ≤ n → K ≤ m →
      negSobolevNorm d s D (fun φ => F n φ - F m φ) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let δ : ℝ := ε / 2
  let η : ℝ := ε / (4 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hden : 0 < 4 * (M + 1) := by positivity
  have hsmall : η * (M + M) ≤ ε / 2 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith
  have herr : δ + η * (M + M) ≤ ε := by
    dsimp [δ]
    linarith
  obtain ⟨N, ψ, hψt, hnet⟩ :=
    negSobolevNorm_sub_le_of_finset_pairings hD h η hη
      (ENNReal.ofReal M) (ENNReal.ofReal δ)
  have hcoords : ∀ i, ∃ K, ∀ n m, K ≤ n → K ≤ m →
      ENNReal.ofReal |F n (ψ i) - F m (ψ i)| ≤ ENNReal.ofReal δ := by
    intro i
    obtain ⟨K, hK⟩ := hpair (ψ i) (hψt i) δ hδ
    refine ⟨K, fun n m hn hm => ?_⟩
    exact ENNReal.ofReal_le_ofReal (hK n m hn hm)
  classical
  choose K hK using hcoords
  refine ⟨Finset.univ.sup K, ?_⟩
  intro n m hn hm
  have hcoord : ∀ i, ENNReal.ofReal |F n (ψ i) - F m (ψ i)| ≤ ENNReal.ofReal δ := by
    intro i
    have hi : K i ≤ Finset.univ.sup K := Finset.le_sup (Finset.mem_univ i)
    exact hK i n m (le_trans hi hn) (le_trans hi hm)
  have hresult := hnet (F n) (F m) (hadd n) (hsmul n) (hadd m) (hsmul m)
    (hbound n) (hbound m) hcoord
  calc negSobolevNorm d s D (fun φ => F n φ - F m φ)
      ≤ ENNReal.ofReal δ + ENNReal.ofReal η *
          (ENNReal.ofReal M + ENNReal.ofReal M) := hresult
    _ = ENNReal.ofReal (δ + η * (M + M)) := by
      rw [← ENNReal.ofReal_add hM hM, ← ENNReal.ofReal_mul hη.le,
        ← ENNReal.ofReal_add hδ.le (mul_nonneg hη.le (add_nonneg hM hM))]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal herr

/-- A uniformly stronger-norm-bounded sequence of linear functionals that is pointwise Cauchy on
all functions has a pointwise limit, and converges to it in each strictly weaker negative norm. -/
theorem exists_limit_negSobolevFunctional_of_pointwise_cauchy (hD : IsDomain D)
    {s₀ s : ℝ} (h : s₀ < s) {M : ℝ} (hM : 0 ≤ M)
    (F : ℕ → (Space d → ℝ) → ℝ)
    (hadd : ∀ n φ ψ, IsTestFn D φ → IsTestFn D ψ →
      F n (φ + ψ) = F n φ + F n ψ)
    (hsmul : ∀ n (c : ℝ) φ, IsTestFn D φ →
      F n (fun x => c * φ x) = c * F n φ)
    (hbound : ∀ n, negSobolevNorm d s₀ D (F n) ≤ ENNReal.ofReal M)
    (hpointwise : ∀ φ, IsTestFn D φ → ∀ δ : ℝ, 0 < δ →
      ∃ K, ∀ n m, K ≤ n → K ≤ m → |F n φ - F m φ| ≤ δ) :
    ∃ G : (Space d → ℝ) → ℝ,
      (∀ φ ψ, IsTestFn D φ → IsTestFn D ψ → G (φ + ψ) = G φ + G ψ) ∧
      (∀ (c : ℝ) φ, IsTestFn D φ → G (fun x => c * φ x) = c * G φ) ∧
      negSobolevNorm d s₀ D G ≤ ENNReal.ofReal M ∧
      ∀ ε : ℝ, 0 < ε → ∃ K, ∀ n, K ≤ n →
        negSobolevNorm d s D (fun φ => F n φ - G φ) ≤ ENNReal.ofReal ε := by
  have hCauchy (φ : Space d → ℝ) (hφ : IsTestFn D φ) :
      CauchySeq (fun n => F n φ) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨K, hK⟩ := hpointwise φ hφ (ε / 2) (by linarith)
    refine ⟨K, fun m hm n hn => ?_⟩
    have hdist : dist (F m φ) (F n φ) = |F n φ - F m φ| := by
      rw [Real.dist_eq, abs_sub_comm]
    rw [hdist]
    exact lt_of_le_of_lt (hK n m hn hm) (by linarith)
  classical
  let G : (Space d → ℝ) → ℝ := fun φ =>
    if hφ : IsTestFn D φ then limUnder atTop (fun n => F n φ) else 0
  have hlim (φ : Space d → ℝ) (hφ : IsTestFn D φ) :
      Tendsto (fun n => F n φ) atTop (𝓝 (G φ)) := by
    change Tendsto (fun n => F n φ) atTop
      (𝓝 (if h : IsTestFn D φ then limUnder atTop (fun n => F n φ) else 0))
    rw [dite_eq_left hφ]
    exact (hCauchy φ hφ).tendsto_limUnder
  have hGadd : ∀ φ ψ, IsTestFn D φ → IsTestFn D ψ → G (φ + ψ) = G φ + G ψ := by
    intro φ ψ hφ hψ
    apply tendsto_nhds_unique (hlim (φ + ψ) (hφ.add hψ))
    have hsum : Tendsto (fun n => F n φ + F n ψ) atTop (𝓝 (G φ + G ψ)) :=
      (hlim φ hφ).add (hlim ψ hψ)
    have heq : (fun n => F n φ + F n ψ) = fun n => F n (φ + ψ) := by
      funext n
      exact (hadd n φ ψ hφ hψ).symm
    simpa only [heq] using hsum
  have hGsmul : ∀ (c : ℝ) φ, IsTestFn D φ → G (fun x => c * φ x) = c * G φ := by
    intro c φ hφ
    apply tendsto_nhds_unique (hlim (fun x => c * φ x) (hφ.const_mul c))
    have hmul : Tendsto (fun n => c * F n φ) atTop (𝓝 (c * G φ)) :=
      tendsto_const_nhds.mul (hlim φ hφ)
    have heq : (fun n => c * F n φ) = fun n => F n (fun x => c * φ x) := by
      funext n
      exact (hsmul n c φ hφ).symm
    simpa only [heq] using hmul
  have hGbound : negSobolevNorm d s₀ D G ≤ ENNReal.ofReal M := by
    unfold negSobolevNorm
    apply sSup_le
    rintro v ⟨φ, hφ, hn, rfl⟩
    have hFnBound (n : ℕ) : |F n φ| ≤ M := by
      have hval : ENNReal.ofReal |F n φ| ≤ negSobolevNorm d s₀ D (F n) := by
        unfold negSobolevNorm
        apply le_sSup
        exact ⟨φ, hφ, hn, rfl⟩
      exact (ENNReal.ofReal_le_ofReal_iff hM).mp (hval.trans (hbound n))
    have hIcc : ∀ᶠ n in atTop, F n φ ∈ Set.Icc (-M) M :=
      Filter.Eventually.of_forall fun n => abs_le.mp (hFnBound n)
    have hGmem : G φ ∈ Set.Icc (-M) M :=
      isClosed_Icc.mem_of_tendsto (hlim φ hφ) hIcc
    exact ENNReal.ofReal_le_ofReal (abs_le.mpr ⟨hGmem.1, hGmem.2⟩)
  refine ⟨G, hGadd, hGsmul, hGbound, ?_⟩
  intro ε hε
  let δ : ℝ := ε / 2
  let η : ℝ := ε / (4 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hden : 0 < 4 * (M + 1) := by positivity
  have hsmall : η * (M + M) ≤ ε / 2 := by
    dsimp [η]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith
  have herr : δ + η * (M + M) ≤ ε := by
    dsimp [δ]
    linarith
  obtain ⟨N, ψ, hψt, hnet⟩ :=
    negSobolevNorm_sub_le_of_finset_pairings hD h η hη
      (ENNReal.ofReal M) (ENNReal.ofReal δ)
  have hcoords : ∀ i, ∃ K, ∀ n, K ≤ n →
      ENNReal.ofReal |F n (ψ i) - G (ψ i)| ≤ ENNReal.ofReal δ := by
    intro i
    rcases Metric.tendsto_atTop.mp (hlim (ψ i) (hψt i)) δ hδ with ⟨K, hK⟩
    refine ⟨K, fun n hn => ?_⟩
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.dist_eq]
    exact le_of_lt (hK n hn)
  classical
  choose K hK using hcoords
  refine ⟨Finset.univ.sup K, ?_⟩
  intro n hn
  have hcoord : ∀ i, ENNReal.ofReal |F n (ψ i) - G (ψ i)| ≤ ENNReal.ofReal δ := by
    intro i
    have hi : K i ≤ Finset.univ.sup K := Finset.le_sup (Finset.mem_univ i)
    exact hK i n (le_trans hi hn)
  have hresult := hnet (F n) G (hadd n) (hsmul n) hGadd hGsmul
    (hbound n) hGbound hcoord
  calc negSobolevNorm d s D (fun φ => F n φ - G φ)
      ≤ ENNReal.ofReal δ + ENNReal.ofReal η *
          (ENNReal.ofReal M + ENNReal.ofReal M) := hresult
    _ = ENNReal.ofReal (δ + η * (M + M)) := by
      rw [← ENNReal.ofReal_add hM hM, ← ENNReal.ofReal_mul hη.le,
        ← ENNReal.ofReal_add hδ.le (mul_nonneg hη.le (add_nonneg hM hM))]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal herr

/-- A sequence of distributions with uniformly bounded stronger norms and Cauchy test pairings has a limiting linear functional, with convergence in every strictly weaker negative Sobolev dual norm. -/
theorem exists_limit_distribution_pairingFunctional_of_pointwise_cauchy
    {D₂ : Set (Space 2)} (hD : IsDomain D₂) {s₀ s : ℝ} (h : s₀ < s)
    {M : ℝ} (hM : 0 ≤ M)
    (T : ℕ → Distr)
    (hbound : ∀ n, negSobolevNorm 2 s₀ D₂ (distributionFunctional (T n)) ≤ ENNReal.ofReal M)
    (hpair : ∀ φ (hφ : IsTestFn D₂ φ), ∀ δ : ℝ, 0 < δ →
      ∃ K, ∀ n m, K ≤ n → K ≤ m →
        |T n (testFnOfRellich hφ.1 hφ.2.1) - T m (testFnOfRellich hφ.1 hφ.2.1)| ≤ δ) :
    ∃ G : (Space 2 → ℝ) → ℝ,
      (∀ φ ψ, IsTestFn D₂ φ → IsTestFn D₂ ψ → G (φ + ψ) = G φ + G ψ) ∧
      (∀ (c : ℝ) φ, IsTestFn D₂ φ → G (fun x => c * φ x) = c * G φ) ∧
      negSobolevNorm 2 s₀ D₂ G ≤ ENNReal.ofReal M ∧
      ∀ ε : ℝ, 0 < ε → ∃ K, ∀ n, K ≤ n →
        negSobolevNorm 2 s D₂ (fun φ => distributionFunctional (T n) φ - G φ)
          ≤ ENNReal.ofReal ε := by
  have hadd : ∀ n φ ψ, IsTestFn D₂ φ → IsTestFn D₂ ψ →
      distributionFunctional (T n) (φ + ψ) =
        distributionFunctional (T n) φ + distributionFunctional (T n) ψ := by
    intro n φ ψ hφ hψ
    exact distributionFunctional_add (T n) hφ hψ
  have hsmul : ∀ n (c : ℝ) φ, IsTestFn D₂ φ →
      distributionFunctional (T n) (fun x => c * φ x) =
        c * distributionFunctional (T n) φ := by
    intro n c φ hφ
    exact distributionFunctional_smul (T n) hφ c
  have hpointwise : ∀ φ, IsTestFn D₂ φ → ∀ δ : ℝ, 0 < δ →
      ∃ K, ∀ n m, K ≤ n → K ≤ m →
        |distributionFunctional (T n) φ - distributionFunctional (T m) φ| ≤ δ := by
    intro φ hφ δ hδ
    obtain ⟨K, hK⟩ := hpair φ hφ δ hδ
    refine ⟨K, fun n m hn hm => ?_⟩
    rw [distributionFunctional_apply (T n) hφ, distributionFunctional_apply (T m) hφ]
    exact hK n m hn hm
  exact exists_limit_negSobolevFunctional_of_pointwise_cauchy (d := 2) (D := D₂) hD h hM
    (fun n => distributionFunctional (T n)) hadd hsmul hbound hpointwise

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
