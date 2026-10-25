/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Critical2DKPZ.LogNormality.Lyapunov

/-! # Transport of the uniform Lyapunov estimate to arbitrary universes

A finite row is pushed forward to its real coordinate space. Independence
identifies this law with the product of the marginal laws. The existing uniform
estimate can then be applied on a probability space in universe zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The uniform Lyapunov test estimate for a finite row on any probability space.
Every random variable has an explicit a.e. measurability hypothesis. -/
theorem exists_lyapunov_clt_bound_fin (h : ℝ →ᵇ ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (m : ℕ) (X : Fin m → Ω → ℝ) (s : ℝ), 0 < s →
      iIndepFun X P → (∀ i, AEMeasurable (X i) P) →
      (∀ i, MemLp (X i) 3 P) → (∀ i, (∫ ω, X i ω ∂P) = 0) →
      |(∑ i, (∫ ω, X i ω ^ 2 ∂P)) - s ^ 2| ≤ δ * s ^ 2 →
      (∑ i, (∫ ω, |X i ω| ^ 3 ∂P)) ≤ δ * s ^ 3 →
      |(∫ ω, h ((∑ i, X i ω) / s) ∂P) -
        (∫ y, h y ∂(gaussianReal 0 1))| ≤ η := by
  obtain ⟨δ, hδ, hbound⟩ := LogNormality.exists_lyapunov_clt_bound h hη
  refine ⟨δ, hδ, ?_⟩
  intro Ω _ P _ m X s hs hind hm hmem hmean hvar hthird
  let V : Ω → (Fin m → ℝ) := fun ω i => X i ω
  have hV : AEMeasurable V P := aemeasurable_pi_iff.mpr hm
  let ν : Measure (Fin m → ℝ) := P.map V
  have hν : ν = Measure.pi (fun i => P.map (X i)) :=
    hind.map_fun_eq_pi_map hm
  have hcoord : iIndepFun (fun i (v : Fin m → ℝ) => v i) ν := by
    rw [hν]
    exact iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hmemν (i : Fin m) : MemLp (fun v : Fin m → ℝ => v i) 3 ν :=
    (memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable hV).mpr (hmem i)
  have hint (g : (Fin m → ℝ) → ℝ) (hg : Measurable g) :
      (∫ v, g v ∂ν) = ∫ ω, g (V ω) ∂P :=
    integral_map hV hg.aestronglyMeasurable
  have hmeanν (i : Fin m) : (∫ v, v i ∂ν) = 0 := by
    rw [hint _ (measurable_pi_apply i)]
    exact hmean i
  have hsq (i : Fin m) : (∫ v, v i ^ 2 ∂ν) = ∫ ω, X i ω ^ 2 ∂P :=
    hint _ (by fun_prop)
  have hcube (i : Fin m) : (∫ v, |v i| ^ 3 ∂ν) = ∫ ω, |X i ω| ^ 3 ∂P :=
    hint _ (by fun_prop)
  have hrow := hbound ν Finset.univ (fun i (v : Fin m → ℝ) => v i)
    (fun _ => 0) s hs hcoord (fun i => measurable_pi_apply i) measurable_const
    (fun i _ => hmemν i) (fun i _ => hmeanν i)
    (by simpa only [hsq] using hvar) (by simpa only [hcube] using hthird)
    (by
      have hnot : ¬ δ * s < 0 := not_lt.mpr (mul_pos hδ hs).le
      simpa only [abs_zero, hnot, Set.ofPred_false, measure_empty, ENNReal.toReal_zero]
        using hδ.le)
  have hrow' : |(∫ v, h ((∑ i, v i) / s) ∂ν) -
      (∫ y, h y ∂gaussianReal 0 1)| ≤ η := by
    simpa only [add_zero] using hrow
  rw [hint _ (by fun_prop)] at hrow'
  exact hrow' 

end Critical2DKPZ.Extensions.ScaleLimit
