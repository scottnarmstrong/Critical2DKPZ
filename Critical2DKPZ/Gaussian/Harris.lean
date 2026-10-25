/-
Copyright (c) 2026 Ahmed Bou-Rabee and the formal-math contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Modified for Critical2DKPZ, 2026.
Ported from Lattice-Probability, commit d14824e5d44553f28824a7f4feb6a6b27c62f805.
-/
/- Adapted from https://github.com/anthropics/formal-math, commit 795efb86,
percolation/Percolation/Literature/HarrisInequality.lean, under the Apache License 2.0. -/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Order.PropInstances
public import Mathlib.Probability.ProductMeasure

/-! Increasing measurable events in an arbitrary product of linearly ordered probability spaces are positively correlated (Harris, Lemma 4.1; Grimmett, Theorem 2.4). -/

@[expose] public section

namespace Critical2DKPZ.Gaussian

open MeasureTheory Measure Filter Set Function
open scoped ENNReal symmDiff

/-! ### One coordinate: Chebyshev's inequality for monotone functions -/

section OneDim

variable {Y : Type*} [MeasurableSpace Y] [LinearOrder Y] (ν : Measure Y) [IsProbabilityMeasure ν]

/-- Increasing bounded measurable functions on a linearly ordered probability space are positively correlated (Grimmett, Theorem 2.4, one-coordinate case). -/
theorem integral_mul_integral_le_integral_mul_of_monotone {φ ψ : Y → ℝ} (hφ : Monotone φ)
    (hψ : Monotone ψ) (hφm : Measurable φ) (hψm : Measurable ψ) {C : ℝ} (hφb : ∀ y, ‖φ y‖ ≤ C)
    (hψb : ∀ y, ‖ψ y‖ ≤ C) :
    (∫ y, φ y ∂ν) * (∫ y, ψ y ∂ν) ≤ ∫ y, φ y * ψ y ∂ν := by
  have iφ : Integrable φ ν := .of_bound hφm.aestronglyMeasurable C (ae_of_all _ hφb)
  have iψ : Integrable ψ ν := .of_bound hψm.aestronglyMeasurable C (ae_of_all _ hψb)
  have iφψ : Integrable (fun y => φ y * ψ y) ν :=
    .of_bound (hφm.mul hψm).aestronglyMeasurable (C * C) (ae_of_all _ fun y => by
      rw [norm_mul]
      exact mul_le_mul (hφb y) (hψb y) (norm_nonneg _) ((norm_nonneg _).trans (hφb y)))
  set a := ∫ y, φ y ∂ν with ha
  set b := ∫ y, ψ y ∂ν with hb
  set c := ∫ y, φ y * ψ y ∂ν with hc
  have hpt : ∀ x y, 0 ≤ (φ x - φ y) * (ψ x - ψ y) := by
    intro x y
    rcases le_total x y with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 (hφ h)) (sub_nonpos.2 (hψ h))
    · exact mul_nonneg (sub_nonneg.2 (hφ h)) (sub_nonneg.2 (hψ h))
  have h1 : ∀ y, ∫ x, (φ x - φ y) * (ψ x - ψ y) ∂ν = c - φ y * b - ψ y * a + φ y * ψ y := by
    intro y
    have e : (fun x => (φ x - φ y) * (ψ x - ψ y)) =
        fun x => (φ x * ψ x - φ y * ψ x - ψ y * φ x) + φ y * ψ y := by
      funext x; ring
    rw [e, integral_add, integral_sub, integral_sub, integral_const_mul, integral_const_mul,
      integral_const]
    · simp [ha, hb, hc]
    all_goals first
      | exact integrable_const _
      | exact iφψ
      | exact iψ.const_mul _
      | exact iφ.const_mul _
      | exact iφψ.sub (iψ.const_mul _)
      | exact (iφψ.sub (iψ.const_mul _)).sub (iφ.const_mul _)
  have h2 : 0 ≤ ∫ y, (c - φ y * b - ψ y * a + φ y * ψ y) ∂ν := by
    have h0 : 0 ≤ ∫ y, ∫ x, (φ x - φ y) * (ψ x - ψ y) ∂ν ∂ν :=
      integral_nonneg fun y => integral_nonneg fun x => hpt x y
    simpa only [h1] using h0
  have h3 : ∫ y, (c - φ y * b - ψ y * a + φ y * ψ y) ∂ν = c - a * b - b * a + c := by
    rw [integral_add, integral_sub, integral_sub, integral_mul_const, integral_mul_const,
      integral_const]
    · simp [ha, hb, hc]
    all_goals first
      | exact integrable_const _
      | exact iφψ
      | exact iφ.mul_const _
      | exact iψ.mul_const _
      | exact (integrable_const c).sub (iφ.mul_const _)
      | exact ((integrable_const c).sub (iφ.mul_const _)).sub (iψ.mul_const _)
  rw [h3] at h2
  linarith

end OneDim

/-! ### The averaging (conditional expectation) operator on a product space -/

section Product

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [hμ : ∀ i, IsProbabilityMeasure (μ i)]

section Piecewise

variable [DecidableEq ι] (s : Finset ι)

omit hμ in
/-- The gluing map `(ω, η) ↦ s.piecewise ω η` (coordinates in `s` from `ω`, the others from `η`) is
measurable. -/
theorem measurable_finsetPiecewise :
    Measurable fun p : (Π i, X i) × (Π i, X i) => s.piecewise p.1 p.2 := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : j ∈ s
  · simp only [Finset.piecewise_eq_of_mem _ _ _ hj]; fun_prop
  · simp only [Finset.piecewise_eq_of_notMem _ _ _ hj]; fun_prop

omit hμ in
/-- For fixed `ω`, `η ↦ s.piecewise ω η` is measurable. -/
theorem measurable_finsetPiecewise_right (ω : Π i, X i) :
    Measurable fun η : Π i, X i => s.piecewise ω η :=
  (measurable_finsetPiecewise s).comp measurable_prodMk_left

/-- Gluing two independent samples of the product measure along a finite set of coordinates gives
a sample of the product measure: `(μ∞ ⊗ μ∞).map (s.piecewise) = μ∞`. (Grimmett 1999, §2.2,
implicit in (2.9).) -/
theorem infinitePi_prod_map_piecewise :
    ((infinitePi μ).prod (infinitePi μ)).map (fun p => s.piecewise p.1 p.2) = infinitePi μ := by
  refine eq_infinitePi μ fun I t ht => ?_
  rw [Measure.map_apply (measurable_finsetPiecewise s)
    (.pi I.countable_toSet fun j _ => ht j)]
  have : (fun p : (Π i, X i) × (Π i, X i) => s.piecewise p.1 p.2) ⁻¹' Set.pi ↑I t =
      Set.pi ↑(I.filter (· ∈ s)) t ×ˢ Set.pi ↑(I.filter (· ∉ s)) t := by
    ext ⟨ω, η⟩
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod, Finset.mem_filter]
    constructor
    · intro h
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · simpa [Finset.piecewise_eq_of_mem _ _ _ hj.2] using h j hj.1
      · simpa [Finset.piecewise_eq_of_notMem _ _ _ hj.2] using h j hj.1
    · rintro ⟨h1, h2⟩ j hj
      by_cases hjs : j ∈ s
      · rw [Finset.piecewise_eq_of_mem _ _ _ hjs]; exact h1 j ⟨hj, hjs⟩
      · rw [Finset.piecewise_eq_of_notMem _ _ _ hjs]; exact h2 j ⟨hj, hjs⟩
  rw [this, Measure.prod_prod, infinitePi_pi _ (fun j _ => ht j), infinitePi_pi _ (fun j _ => ht j),
    Finset.prod_filter_mul_prod_filter_not]

/-! Integrating out coordinates outside a finite set gives conditional expectation onto the retained coordinates. -/

variable {s}

/-- A bounded measurable function has integrable sections `η ↦ f (s.piecewise ω η)`. -/
theorem integrable_comp_piecewise {f : (Π i, X i) → ℝ} (hfm : Measurable f) {C : ℝ}
    (hb : ∀ ω, ‖f ω‖ ≤ C) (ω : Π i, X i) :
    Integrable (fun η => f (s.piecewise ω η)) (infinitePi μ) :=
  .of_bound (hfm.comp (measurable_finsetPiecewise_right s ω)).aestronglyMeasurable C
    (ae_of_all _ fun _ => hb _)

/-- Averaging preserves the integral: `∫ T_s f dμ∞ = ∫ f dμ∞` (tower property / Fubini for the
gluing map). -/
theorem integral_integral_piecewise {f : (Π i, X i) → ℝ} (hf : Integrable f (infinitePi μ)) :
    ∫ ω, ∫ η, f (s.piecewise ω η) ∂infinitePi μ ∂infinitePi μ = ∫ ω, f ω ∂infinitePi μ := by
  have hae : AEStronglyMeasurable f
      (((infinitePi μ).prod (infinitePi μ)).map (fun p => s.piecewise p.1 p.2)) := by
    rw [infinitePi_prod_map_piecewise]; exact hf.aestronglyMeasurable
  have hint : Integrable (fun p : (Π i, X i) × (Π i, X i) => f (s.piecewise p.1 p.2))
      ((infinitePi μ).prod (infinitePi μ)) := by
    have h := hf
    rw [← infinitePi_prod_map_piecewise μ s] at h
    exact h.comp_measurable (measurable_finsetPiecewise s)
  calc ∫ ω, ∫ η, f (s.piecewise ω η) ∂infinitePi μ ∂infinitePi μ
      = ∫ p, f (s.piecewise p.1 p.2) ∂(infinitePi μ).prod (infinitePi μ) :=
        (integral_prod _ hint).symm
    _ = ∫ ω, f ω ∂((infinitePi μ).prod (infinitePi μ)).map (fun p => s.piecewise p.1 p.2) :=
        (integral_map (measurable_finsetPiecewise s).aemeasurable hae).symm
    _ = ∫ ω, f ω ∂infinitePi μ := by rw [infinitePi_prod_map_piecewise]

/-- Averaging an increasing function over independent coordinates preserves monotonicity. -/
theorem monotone_integral_piecewise [∀ i, Preorder (X i)] {f : (Π i, X i) → ℝ} (hf : Monotone f)
    (hfm : Measurable f) {C : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ C) :
    Monotone fun ω => ∫ η, f (s.piecewise ω η) ∂infinitePi μ := by
  intro ω ω' h
  exact integral_mono (integrable_comp_piecewise μ hfm hb ω)
    (integrable_comp_piecewise μ hfm hb ω')
    fun η => hf (Finset.piecewise_le_piecewise _ h le_rfl)

/-- `ω ↦ ∫ f (s.piecewise ω η) dμ∞(η)` is measurable (Fubini). -/
theorem measurable_integral_piecewise {f : (Π i, X i) → ℝ} (hfm : Measurable f) :
    Measurable fun ω => ∫ η, f (s.piecewise ω η) ∂infinitePi μ :=
  ((hfm.comp (measurable_finsetPiecewise s)).stronglyMeasurable.integral_prod_right'
    (ν := infinitePi μ)).measurable

/-- Averaging is a contraction for the sup norm. -/
theorem norm_integral_piecewise_le {f : (Π i, X i) → ℝ} {C : ℝ} (hb : ∀ ω, ‖f ω‖ ≤ C)
    (ω : Π i, X i) : ‖∫ η, f (s.piecewise ω η) ∂infinitePi μ‖ ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := infinitePi μ)
    (ae_of_all _ fun η => hb (s.piecewise ω η))
  rwa [probReal_univ, mul_one] at h

omit hμ in
/-- `ω ↦ ∫ f (s.piecewise ω η) dμ∞(η)` depends only on the coordinates in `s`. -/
theorem dependsOn_integral_piecewise (f : (Π i, X i) → ℝ) :
    DependsOn (fun ω => ∫ η, f (s.piecewise ω η) ∂infinitePi μ) ↑s := by
  intro ω ω' h
  dsimp only
  congr 1 with η
  rw [s.piecewise_congr (fun j hj => h j hj) fun _ (_ : _ ∉ s) => (rfl : η _ = η _)]



end Piecewise

/-! ### Harris' inequality: finitely many coordinates -/

/-- Increasing bounded measurable functions depending on finitely many coordinates of a product probability space are positively correlated (Harris, Lemma 4.1; Grimmett, Theorem 2.4). -/
theorem infinitePi_harris_dependsOn [DecidableEq ι] [∀ i, LinearOrder (X i)] (s : Finset ι) :
    ∀ {f g : (Π i, X i) → ℝ} {C : ℝ}, Monotone f → Monotone g → Measurable f → Measurable g →
      DependsOn f ↑s → DependsOn g ↑s → (∀ ω, ‖f ω‖ ≤ C) → (∀ ω, ‖g ω‖ ≤ C) →
      (∫ ω, f ω ∂infinitePi μ) * (∫ ω, g ω ∂infinitePi μ) ≤ ∫ ω, f ω * g ω ∂infinitePi μ := by
  induction s using Finset.induction_on with
  | empty =>
    intro f g C hf hg hfm hgm hfs hgs hfb hgb
    rcases isEmpty_or_nonempty (Π i, X i) with h | ⟨⟨ω₀⟩⟩
    · simp [Measure.eq_zero_of_isEmpty (infinitePi μ)]
    · have hf' : f = fun _ => f ω₀ := funext fun ω => hfs (by simp)
      have hg' : g = fun _ => g ω₀ := funext fun ω => hgs (by simp)
      rw [hf', hg']
      simp [integral_const]
  | insert i s hi ih =>
    intro f g C hf hg hfm hgm hfs hgs hfb hgb
    -- integrability of bounded measurable functions on the probability space `μ∞`
    have iB : ∀ {h : (Π i, X i) → ℝ}, Measurable h → ∀ {C : ℝ}, (∀ ω, ‖h ω‖ ≤ C) →
        Integrable h (infinitePi μ) := fun hm C hb =>
      .of_bound hm.aestronglyMeasurable C (ae_of_all _ hb)
    have hprod : ∀ {u v : (Π i, X i) → ℝ} {C : ℝ}, (∀ ω, ‖u ω‖ ≤ C) → (∀ ω, ‖v ω‖ ≤ C) →
        ∀ ω, ‖u ω * v ω‖ ≤ C * C := fun hu hv ω => by
      rw [norm_mul]
      exact mul_le_mul (hu ω) (hv ω) (norm_nonneg _) ((norm_nonneg _).trans (hu ω))
    have hfgs : DependsOn (fun ω => f ω * g ω) ↑(insert i s) := fun x y h => by
      simp only [hfs h, hgs h]
    -- Step 1: for fixed `ω`, averaging over the coordinates outside `s` of a function depending on
    -- `insert i s` is a one-dimensional integral in the coordinate `i`; apply Chebyshev there.
    have red : ∀ {h : (Π i, X i) → ℝ}, DependsOn h ↑(insert i s) → Measurable h → ∀ ω,
        ∫ η, h (s.piecewise ω η) ∂infinitePi μ = ∫ x, h (update ω i x) ∂μ i := by
      intro h hh hhm ω
      have e : ∀ η, h (s.piecewise ω η) = h (update ω i (η i)) := by
        intro η
        apply hh
        intro j hj
        rcases Finset.mem_insert.1 hj with rfl | hj
        · simp [Finset.piecewise_eq_of_notMem _ _ _ hi]
        · have hji : j ≠ i := fun h' => hi (h' ▸ hj)
          simp [Finset.piecewise_eq_of_mem _ _ _ hj, update_of_ne hji]
      simp only [e]
      rw [← infinitePi_map_eval μ i, integral_map (measurable_pi_apply i).aemeasurable]
      exact (hhm.comp (measurable_update ω)).aestronglyMeasurable
    have key : ∀ ω, (∫ η, f (s.piecewise ω η) ∂infinitePi μ) * (∫ η, g (s.piecewise ω η) ∂infinitePi μ)
        ≤ ∫ η, f (s.piecewise ω η) * g (s.piecewise ω η) ∂infinitePi μ := by
      intro ω
      rw [red hfs hfm, red hgs hgm, red hfgs (hfm.mul hgm)]
      exact integral_mul_integral_le_integral_mul_of_monotone (μ i) (hf.comp update_mono)
        (hg.comp update_mono) (hfm.comp (measurable_update ω)) (hgm.comp (measurable_update ω))
        (fun x => hfb _) (fun x => hgb _)
    -- Step 2: induction hypothesis for the averaged functions, which depend on `s` only.
    have hF := ih (monotone_integral_piecewise μ hf hfm hfb) (monotone_integral_piecewise μ hg hgm hgb)
      (measurable_integral_piecewise μ hfm) (measurable_integral_piecewise μ hgm)
      (dependsOn_integral_piecewise μ f) (dependsOn_integral_piecewise μ g)
      (norm_integral_piecewise_le μ hfb) (norm_integral_piecewise_le μ hgb)
    rw [integral_integral_piecewise μ (iB hfm hfb), integral_integral_piecewise μ (iB hgm hgb)] at hF
    calc (∫ ω, f ω ∂infinitePi μ) * (∫ ω, g ω ∂infinitePi μ)
        ≤ ∫ ω, (∫ η, f (s.piecewise ω η) ∂infinitePi μ) * (∫ η, g (s.piecewise ω η) ∂infinitePi μ)
            ∂infinitePi μ := hF
      _ ≤ ∫ ω, ∫ η, f (s.piecewise ω η) * g (s.piecewise ω η) ∂infinitePi μ ∂infinitePi μ :=
          integral_mono (iB ((measurable_integral_piecewise μ hfm).mul
              (measurable_integral_piecewise μ hgm))
            (hprod (norm_integral_piecewise_le μ hfb) (norm_integral_piecewise_le μ hgb)))
            (iB (measurable_integral_piecewise μ (hfm.mul hgm))
              (norm_integral_piecewise_le μ (hprod hfb hgb))) key
      _ = ∫ ω, f ω * g ω ∂infinitePi μ :=
          integral_integral_piecewise μ (iB (hfm.mul hgm) (hprod hfb hgb))

/-! ### Harris' inequality: general measurable increasing events -/



end Product

end Critical2DKPZ.Gaussian

end
