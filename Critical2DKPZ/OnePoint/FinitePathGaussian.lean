/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Provider.GaussianConvexity
public import Critical2DKPZ.PolymerCalculus.NormalizedPathBounds
public import Critical2DKPZ.PolymerCalculus.BoundarySliceDisorder
import Mathlib.Tactic

/-! # Gaussian convexity for finite polymer path masses on the disorder -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

private def pathCoordinateSet {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) : Finset (ℕ × Site) :=
  PolymerCalculus.finitePathCoordinates a n w

private def pathCoordinateMap {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) : Fin (pathCoordinateSet a n w).card → ℕ × Site :=
  fun i => ((pathCoordinateSet a n w).equivFin.symm i).val

private def pathCoordinateVector {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) (ω : Disorder) :
    EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card) :=
  PolymerCalculus.disorderSliceCoordinates (pathCoordinateMap a n w) ω

private def pathCoordinateExtension {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) :
    EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card) →ₗ[ℝ] Disorder where
  toFun x := fun p => if hp : p ∈ pathCoordinateSet a n w then
    x ((pathCoordinateSet a n w).equivFin ⟨p, hp⟩) else 0
  map_add' x y := by
    funext p
    by_cases hp : p ∈ pathCoordinateSet a n w <;>
      simp [hp, Pi.add_apply]
  map_smul' c x := by
    funext p
    by_cases hp : p ∈ pathCoordinateSet a n w <;>
      simp [hp, smul_eq_mul]

private theorem pathCoordinateExtension_vector_eq {ι : Type*} [Fintype ι]
    (a n : ℕ) (w : ι → Site) (ω : Disorder) (p : ℕ × Site)
    (hp : p ∈ pathCoordinateSet a n w) :
    pathCoordinateExtension a n w (pathCoordinateVector a n w ω) p = ω p := by
  change (if h : p ∈ pathCoordinateSet a n w then
    pathCoordinateVector a n w ω ((pathCoordinateSet a n w).equivFin ⟨p, h⟩) else 0) = ω p
  simp [hp, pathCoordinateVector, PolymerCalculus.disorderSliceCoordinates,
    pathCoordinateMap]

/-- The normalized log-MGF ratio of a finite positive path mass is convex under the disorder law. -/
theorem logMGFRatio_finitePathMass_convex {ι : Type*} [Fintype ι]
    (β : ℝ) (a n : ℕ) (w : ι → Site)
    {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hpos : ∃ p, 0 < c p) :
    ConvexOn ℝ
      (integrableExpSet
        (fun ω => Real.log (PolymerCalculus.finitePathMass β a n w c ω)) disorderLaw)
      (logMGFRatio disorderLaw
        (fun ω => Real.log (PolymerCalculus.finitePathMass β a n w c ω))) := by
  let π := pathCoordinateVector a n w
  let L := pathCoordinateExtension a n w
  let F : Disorder → ℝ := fun ω =>
    Real.log (PolymerCalculus.finitePathMass β a n w c ω)
  let G : EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card) → ℝ := fun x => F (L x)
  have hπlaw : HasLaw π
      (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))) disorderLaw := by
    have he : Function.Injective (pathCoordinateMap a n w) := by
      intro i j hij
      have hsub : (pathCoordinateSet a n w).equivFin.symm i =
          (pathCoordinateSet a n w).equivFin.symm j := Subtype.ext hij
      exact (pathCoordinateSet a n w).equivFin.symm.injective hsub
    change HasLaw (pathCoordinateVector a n w)
      (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))) disorderLaw
    exact PolymerCalculus.hasLaw_disorderSliceCoordinates (pathCoordinateMap a n w) he
  have hπmeas : Measurable π := by
    change Measurable (fun ω : Disorder =>
      WithLp.toLp 2 (fun i => ω (pathCoordinateMap a n w i)))
    have hraw : Measurable (fun ω : Disorder =>
        fun i : Fin (pathCoordinateSet a n w).card => ω (pathCoordinateMap a n w i)) :=
      measurable_pi_iff.mpr (fun i => Gaussian.measurable_disorder_eval
        (pathCoordinateMap a n w i))
    have hto : Measurable (fun x : (Fin (pathCoordinateSet a n w).card → ℝ) =>
        WithLp.toLp 2 x) := by fun_prop
    exact hto.comp hraw
  have hcoordEq (ω : Disorder) (p : ℕ × Site) (hp : p ∈ pathCoordinateSet a n w) :
      L (π ω) p = ω p := by
    simpa only [L, π] using pathCoordinateExtension_vector_eq a n w ω p hp
  have hdep : DependsOn
      (PolymerCalculus.finitePathMass β a n w c) (pathCoordinateSet a n w : Set (ℕ × Site)) :=
    PolymerCalculus.dependsOn_finitePathMass β a n w c
  have hmassEq (ω : Disorder) :
      PolymerCalculus.finitePathMass β a n w c (L (π ω)) =
        PolymerCalculus.finitePathMass β a n w c ω := by
    exact hdep (by
      intro p hp
      exact hcoordEq ω p hp)
  have hFcomp : F = fun ω => G (π ω) := by
    funext ω
    dsimp [F, G]
    exact congrArg Real.log (hmassEq ω).symm
  have hconvDisorder : ConvexOn ℝ univ F := by
    simpa only [F] using
      PolymerCalculus.convexOn_log_finitePathMass β a n w hc hpos
  have hconvG : ConvexOn ℝ univ G := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ u v hu hv huv
    change F (L (u • x + v • y)) ≤ u * F (L x) + v * F (L y)
    have hlin : L (u • x + v • y) = u • L x + v • L y := by simp
    rw [hlin]
    exact hconvDisorder.2 (Set.mem_univ (L x)) (Set.mem_univ (L y)) hu hv huv
  have hLmeas : Measurable L := by
    apply measurable_pi_iff.mpr
    intro p
    dsimp [L, pathCoordinateExtension]
    split_ifs <;> fun_prop
  have hGmeas : Measurable G := by
    exact (PolymerCalculus.measurable_log_finitePathMass β a n w c).comp
      hLmeas
  have hFmeas : Measurable F := by
    simpa only [F] using PolymerCalculus.measurable_log_finitePathMass β a n w c
  have hFdom : integrableExpSet F disorderLaw = univ := by
    simpa only [F] using PolymerCalculus.integrableExpSet_log_finitePathMass β a n w hc hpos
  have hExpG (q : ℝ) (hq : 0 < q) :
      Integrable (fun x => Real.exp (q * G x))
        (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))) := by
    have hExpF : Integrable (fun ω => Real.exp (q * F ω)) disorderLaw := by
      simpa only [F] using
        PolymerCalculus.integrable_exp_mul_log_finitePathMass β a n w hc hpos q
    have hExpComp : Integrable (fun ω => Real.exp (q * G (π ω))) disorderLaw := by
      simpa only [hFcomp, Function.comp_apply] using hExpF
    have hmapEq := hπlaw.map_eq
    rw [← hmapEq]
    exact (integrable_map_measure (by fun_prop) hπlaw.aemeasurable).2 hExpComp
  have hC1 := Critical2DKPZ.Provider.gaussian_convexity
    (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))) G hconvG hExpG
  have hmeasure : disorderLaw.map F =
      (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))).map G := by
    rw [hFcomp]
    calc
      disorderLaw.map (fun ω => G (π ω)) =
          disorderLaw.map (G ∘ π) := rfl
      _ = (disorderLaw.map π).map G := (Measure.map_map hGmeas hπmeas).symm
      _ = (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))).map G := by
        rw [hπlaw.map_eq]
  have hratio (q : ℝ) :
      logMGFRatio disorderLaw F q =
        logMGFRatio (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))) G q := by
    calc
      logMGFRatio disorderLaw F q = logMGFRatio (disorderLaw.map F) id q :=
        (GaussianConvexity.logMGFRatio_map disorderLaw F hFmeas q).symm
      _ = logMGFRatio
          ((stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))).map G) id q := by
            rw [hmeasure]
      _ = logMGFRatio
          (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))) G q :=
        GaussianConvexity.logMGFRatio_map _ G hGmeas q
  have hfun : logMGFRatio disorderLaw F =
      logMGFRatio
        (stdGaussian (EuclideanSpace ℝ (Fin (pathCoordinateSet a n w).card))) G := funext hratio
  rw [hFdom, hfun]
  exact hC1

end Critical2DKPZ.OnePoint

end
