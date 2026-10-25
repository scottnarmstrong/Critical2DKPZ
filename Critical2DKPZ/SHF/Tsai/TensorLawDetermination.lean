/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SmoothLawDetermination
public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Laws of finite vectors of compact tensor pairings

Finite vectors of compact tensor pairings are measurable, and their bounded smooth
nonlinear expectations determine their joint laws.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Finite vectors of tensor pairings of a measurable random measure are measurable. -/
theorem measurable_tensorPairings {Ω ι : Type*} [MeasurableSpace Ω]
    (Z : Ω → Measure (Plane × Plane)) (hZ : Measurable Z)
    (g g' : ι → C_c(Plane, ℝ)) :
    Measurable (fun ω i => ∫ p, g i p.1 * g' i p.2 ∂Z ω) := by
  let κ : Kernel Ω (Plane × Plane) := ⟨Z, hZ⟩
  apply Measurable.of_eval
  intro i
  have hm : Measurable (fun p : Plane × Plane => g i p.1 * g' i p.2) :=
    ((g i).continuous.measurable.comp measurable_fst).mul
      ((g' i).continuous.measurable.comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_kernel (κ := κ)).measurable

/-- Smooth nonlinear expectations determine the joint law of a fixed finite tensor-sum vector. -/
theorem map_tensorSumPairings_eq_of_integral_contDiff_eq {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : Ω → Measure (Plane × Plane)) (Z' : Ω' → Measure (Plane × Plane))
    (hZ : Measurable Z) (hZ' : Measurable Z') (m r : ℕ)
    (g g' : Fin m → Fin r → C_c(Plane, ℝ))
    (h : ∀ H : (Fin m → ℝ) → ℝ, ContDiff ℝ 4 H →
      (∃ C : ℝ, ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ C) →
      (∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z ω) ∂P) =
        ∫ ω, H (fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z' ω) ∂P') :
    P.map (fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z ω) =
      P'.map (fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z' ω) := by
  have hm (a b) : Measurable (fun ω => ∫ p, g a b p.1 * g' a b p.2 ∂Z ω) :=
    (measurable_pi_apply b).comp (measurable_tensorPairings Z hZ (g a) (g' a))
  have hm' (a b) : Measurable (fun ω => ∫ p, g a b p.1 * g' a b p.2 ∂Z' ω) :=
    (measurable_pi_apply b).comp (measurable_tensorPairings Z' hZ' (g a) (g' a))
  have hVm : Measurable (fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z ω) :=
    Measurable.of_eval fun a => Finset.measurable_sum _ (fun b _ => hm a b)
  have hVm' : Measurable (fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z' ω) :=
    Measurable.of_eval fun a => Finset.measurable_sum _ (fun b _ => hm' a b)
  apply measure_eq_of_integral_contDiff_bounded_eq
  intro H hH hC
  rw [integral_map hVm.aemeasurable hH.continuous.aestronglyMeasurable,
    integral_map hVm'.aemeasurable hH.continuous.aestronglyMeasurable]
  exact h H hH hC

/-- Equality of all finite tensor-vector laws also compares sums with different numbers of terms in each row. -/
theorem map_sum_pairings_eq_of_tensor_laws {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    (Z : Ω → Measure (Plane × Plane)) (Z' : Ω' → Measure (Plane × Plane))
    (hZ : Measurable Z) (hZ' : Measurable Z')
    (h : ∀ n : ℕ, ∀ g g' : Fin n → C_c(Plane, ℝ),
      P.map (fun ω i => ∫ p, g i p.1 * g' i p.2 ∂Z ω) =
        P'.map (fun ω i => ∫ p, g i p.1 * g' i p.2 ∂Z' ω))
    {m : ℕ} (r : Fin m → ℕ) (g g' : (a : Fin m) → Fin (r a) → C_c(Plane, ℝ)) :
    P.map (fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z ω) =
      P'.map (fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z' ω) := by
  classical
  let I := (a : Fin m) × Fin (r a)
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let u (i : Fin (Fintype.card I)) := g (e.symm i).1 (e.symm i).2
  let u' (i : Fin (Fintype.card I)) := g' (e.symm i).1 (e.symm i).2
  let Ψ (z : Fin (Fintype.card I) → ℝ) (a : Fin m) := ∑ b, z (e ⟨a, b⟩)
  have hΨ : Measurable Ψ := Measurable.of_eval fun a =>
    Finset.measurable_sum _ (fun b _ => measurable_pi_apply (e ⟨a, b⟩))
  have hMap := congrArg (fun ν : Measure (Fin (Fintype.card I) → ℝ) => ν.map Ψ)
    (h (Fintype.card I) u u')
  rw [Measure.map_map hΨ (measurable_tensorPairings Z hZ u u'),
    Measure.map_map hΨ (measurable_tensorPairings Z' hZ' u u')] at hMap
  have hei (a : Fin m) (b : Fin (r a)) : e.symm (e ⟨a, b⟩) = ⟨a, b⟩ := e.symm_apply_apply _
  have hu (a : Fin m) (b : Fin (r a)) : u (e ⟨a, b⟩) = g a b := by
    dsimp only [u]
    rw [hei]
  have hu' (a : Fin m) (b : Fin (r a)) : u' (e ⟨a, b⟩) = g' a b := by
    dsimp only [u']
    rw [hei]
  have hcomp (μ : Measure (Plane × Plane)) :
      Ψ (fun i => ∫ p, u i p.1 * u' i p.2 ∂μ) =
        fun a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂μ := by
    funext a
    change (∑ b, ∫ p, u (e ⟨a, b⟩) p.1 * u' (e ⟨a, b⟩) p.2 ∂μ) = _
    apply Finset.sum_congr rfl
    intro b _
    rw [hu, hu']
  have hleft : Ψ ∘ (fun ω i => ∫ p, u i p.1 * u' i p.2 ∂Z ω) =
      fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z ω := by
    funext ω
    exact hcomp (Z ω)
  have hright : Ψ ∘ (fun ω i => ∫ p, u i p.1 * u' i p.2 ∂Z' ω) =
      fun ω a => ∑ b, ∫ p, g a b p.1 * g' a b p.2 ∂Z' ω := by
    funext ω
    exact hcomp (Z' ω)
  rw [hleft, hright] at hMap
  exact hMap

end Critical2DKPZ.SHF.Tsai

end
