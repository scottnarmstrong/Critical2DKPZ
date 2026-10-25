/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.Fields
public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Definitions.TestFnScale
public import Critical2DKPZ.Definitions.TestFnCompAffine
import Critical2DKPZ.Extensions.GffTangent.FlowMartingale
import Critical2DKPZ.Provider.CriticalKPZInvariance
import Critical2DKPZ.Provider.ShfSymmetries
import Critical2DKPZ.Extensions.Common.Canonical

/-! # Microscopic scaling and fixed-time reduction to the forward flow -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

universe u

/-- Parameter of the rescaled flow at microscopic spatial width `ε`. -/
def microscopicParameter (ϑ ε : ℝ) : ℝ := 2 * Real.log ε⁻¹ - ϑ

/-- The forward flow at parameter `-l`, obtained from the original flow by parabolic scaling. -/
def gffScaledFlow {Ω : Type u}
    (ϑ : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (l : ℝ) :
    ℝ → ℝ → Ω → Measure (Plane × Plane) :=
  let a := Real.exp (-l - ϑ)
  fun s t ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map
    (fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2))

/-- Rescaling uses the same probability space and changes the critical parameter to `-l`. -/
theorem gffScaledFlow_critical (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) (l : ℝ) :
    IsCriticalSHF (-l) P (gffScaledFlow ϑ Z l) := by
  have hparam : ϑ + Real.log (Real.exp (-l - ϑ)) = -l := by rw [Real.log_exp]; ring
  simpa only [gffScaledFlow, hparam] using
    (Critical2DKPZ.Provider.shf_symmetries ϑ P Z hZ).2.2.2.1
      (Real.exp (-l - ϑ)) (Real.exp_pos _)

/-- The microscopic parameter gives exactly the spatial square as the time scaling. -/
theorem microscopicParameter_exp (ϑ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Real.exp (-microscopicParameter ϑ ε - ϑ) = ε ^ 2 := by
  have he : -microscopicParameter ϑ ε - ϑ = 2 * Real.log ε := by
    rw [microscopicParameter, Real.log_inv]
    ring
  rw [he, show (2 : ℝ) * Real.log ε = Real.log ε + Real.log ε by ring,
    Real.exp_add, Real.exp_log hε, pow_two]

/-- The original and rescaled time horizons agree exactly. -/
theorem microscopic_horizon_eq (ϑ t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    t / ε ^ 2 = (t * Real.exp ϑ) * Real.exp (microscopicParameter ϑ ε) := by
  have hh := microscopicParameter_exp ϑ hε
  rw [Real.exp_sub, Real.exp_neg] at hh
  have he : Real.exp (microscopicParameter ϑ ε) * ε ^ 2 = (Real.exp ϑ)⁻¹ := by
    rw [← hh]
    field_simp
  apply (div_eq_iff (pow_ne_zero 2 hε.ne')).mpr
  calc
    t = t * ((Real.exp ϑ) * (Real.exp ϑ)⁻¹) := by rw [mul_inv_cancel₀ (Real.exp_ne_zero _), mul_one]
    _ = (t * Real.exp ϑ * Real.exp (microscopicParameter ϑ ε)) * ε ^ 2 := by rw [← he]; ring

/-- Parabolic scaling of a test is the microscopic dilation at the origin. -/
theorem scale_sq_eq_dilate (f : TestFn) {ε : ℝ} (hε : 0 < ε) :
    f.scale (ε ^ 2) = f.dilate ε 0 := by
  ext y
  simp only [TestFn.scale, TestFn.dilate, Real.sqrt_sq_eq_abs, abs_of_pos hε, sub_zero]

/-- Translation of the centered microscopic test produces the test at the chosen centre. -/
theorem dilate_compAffine_neg (f : TestFn) (ε : ℝ) (x : Plane) :
    (f.dilate ε 0).compAffine (-x) (LinearIsometryEquiv.refl ℝ Plane) = f.dilate ε x := by
  ext y
  change ε⁻¹ ^ 2 * f (ε⁻¹ • ((-x + y) - 0)) = ε⁻¹ ^ 2 * f (ε⁻¹ • (y - x))
  rw [sub_zero, neg_add_eq_sub]

/-- Translation invariance removes the microscopic test's spatial centre. -/
theorem microscopic_law_translate (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (ε : ℝ) (x : Plane) (n : ℕ) (f : Fin n → TestFn) :
    P.map (fun ω i => H t 0 ω ((f i).dilate ε x)) =
      P.map (fun ω i => H t 0 ω ((f i).dilate ε 0)) := by
  simpa only [dilate_compAffine_neg] using
    (Critical2DKPZ.Provider.criticalKPZ_invariance.{u, u} ϑ P Z hZ H hH n
      (fun _ => t) (fun _ => ht) (fun i => (f i).dilate ε 0)).2.1
      (-x) (LinearIsometryEquiv.refl ℝ Plane) (by simp)

/-- The full microscopic vector has the law of the chosen forward-flow limit.
The law identity holds for every positive width; zero test integrals are needed
only when identifying `kField` with the uncentred entrance averages. -/
theorem reduction_law_eq (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) (x : Plane)
    (n : ℕ) (f : Fin n → TestFn) :
    let l := microscopicParameter ϑ ε
    let Zl := gffScaledFlow ϑ Z l
    let hZl := gffScaledFlow_critical ϑ P Z hZ l
    P.map (fun ω i => H t 0 ω ((f i).dilate ε x)) =
      P.map (fun ω i => kField (-l) P Zl hZl (t / ε ^ 2)
        (div_pos ht (pow_pos hε 2)) (f i) ω) := by
  dsimp only
  let l := microscopicParameter ϑ ε
  let Zl := gffScaledFlow ϑ Z l
  have hZl := gffScaledFlow_critical ϑ P Z hZ l
  obtain ⟨Hl, hHl, _⟩ := Common.exists_canonical_criticalKPZ (-l) P Zl hZl
  have htime : 0 < t / ε ^ 2 := div_pos ht (pow_pos hε 2)
  have hparam : ϑ + Real.log (ε ^ 2) = -l := by
    dsimp [l, microscopicParameter]
    rw [Real.log_pow, Real.log_inv]
    ring
  have hlaw := (Critical2DKPZ.Provider.criticalKPZ_invariance.{u, u} ϑ P Z hZ H hH n
    (fun _ => t / ε ^ 2) (fun _ => htime) f).2.2 (ε ^ 2) (pow_pos hε 2)
    P Zl (by rwa [hparam]) Hl hHl
  have hcancel : ε ^ 2 * (t / ε ^ 2) = t := mul_div_cancel₀ t (pow_ne_zero 2 hε.ne')
  rw [hcancel] at hlaw
  simp only [scale_sq_eq_dilate _ hε] at hlaw
  exact (microscopic_law_translate ϑ P Z hZ H hH t ht ε x n f).trans
    (hlaw.trans (kField_law_eq (-l) P Zl hZl (t / ε ^ 2) htime Hl hHl n f).symm)

/-- Translation of all time intervals moves a delayed linear observable to time zero. -/
theorem law_timeShift_vector (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {m S : ℝ} (hm : 0 ≤ m) (hmS : m < S) (n : ℕ) (g : Fin n → Plane → ℝ)
    (hg : ∀ i, Measurable (g i)) :
    P.map (fun ω i => shfPairing Z m S (g i) (fun _ => 1) ω) =
      P.map (fun ω i => shfPairing Z 0 (S - m) (g i) (fun _ => 1) ω) := by
  simpa only [zero_add, sub_add_cancel] using
    law_shfPairing_timeShift ϑ P Z hZ (fun _ : Fin n => 0) (fun _ => S - m)
      (fun _ => ⟨le_rfl, sub_pos.mpr hmS⟩) m hm g (fun _ _ => 1) hg
      (fun _ => measurable_const)


end Critical2DKPZ.Extensions.GffTangent
