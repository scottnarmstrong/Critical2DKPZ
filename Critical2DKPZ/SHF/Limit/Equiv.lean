/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.FlatBound
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Pairing formulation of critical SHF convergence -/

@[expose] public section

open MeasureTheory Filter
open scoped CompactlySupported Topology

noncomputable section

namespace Critical2DKPZ.SHF.Limit

private theorem aemeasurable_polymerCompactPairing (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (f : C_c(Plane × Plane, ℝ)) :
    AEMeasurable (fun ω => ∫ p, f p ∂(polymerMeasure ϑ N s t ω)) disorderLaw := by
  have hpair := SHF.Moments.integrable_pairing_rescaledP2P ϑ N s t
    f.continuous f.hasCompactSupport
  have hmeas0 := hpair.swap.aestronglyMeasurable.integral_prod_right'.aemeasurable
  have hmeas : AEMeasurable (fun ω =>
      ∫ p, f p * rescaledP2P ϑ N s t p ω ∂(volume : Measure (Plane × Plane)))
      disorderLaw := by
    change AEMeasurable (fun ω => ∫ p,
      (f : Plane × Plane → ℝ) p * rescaledP2P ϑ N s t p ω) disorderLaw at hmeas0
    exact hmeas0
  have hEq : (fun ω => ∫ p, f p ∂(polymerMeasure ϑ N s t ω)) =ᵐ[disorderLaw]
      (fun ω => ∫ p, f p * rescaledP2P ϑ N s t p ω) :=
    Filter.Eventually.of_forall fun ω => integral_polymerMeasure ϑ N s t ω f
  exact hmeas.congr hEq.symm

private theorem aemeasurable_polymerMarginalPairing (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (f : C_c(Plane, ℝ)) :
    AEMeasurable (fun ω => ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst))
      disorderLaw := by
  by_cases hN0 : N = 0
  · subst N
    have hzero (ω : Disorder) : polymerMeasure ϑ 0 s t ω = 0 := by
      rw [polymerMeasure]
      ext A hA
      simp [rescaledP2P]
    have hEq : (fun ω => ∫ x, f x ∂((polymerMeasure ϑ 0 s t ω).map Prod.fst)) =ᵐ[
        disorderLaw] fun _ => (0 : ℝ) := by
      filter_upwards [] with ω
      rw [hzero]
      simp
    exact aemeasurable_const.congr hEq.symm
  · have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have hmeas := aemeasurable_rescaledP2Plane_pairing ϑ N s t f
    have hEq : (fun ω => ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst)) =ᵐ[
        disorderLaw] fun ω => ∫ x, f x * rescaledP2Plane ϑ N s t x ω :=
      Filter.Eventually.of_forall fun ω => integral_map_fst_polymerMeasure ϑ hN s t ω f
    exact hmeas.congr hEq.symm

private theorem aemeasurable_frozenCompactPairing (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (f : C_c(Plane × Plane, ℝ)) :
    AEMeasurable (fun ω => ∫ p, f p * rescaledP2P ϑ N s t p ω) disorderLaw := by
  have hpair := SHF.Moments.integrable_pairing_rescaledP2P ϑ N s t
    f.continuous f.hasCompactSupport
  have hmeas0 := hpair.swap.aestronglyMeasurable.integral_prod_right'.aemeasurable
  change AEMeasurable (fun ω => ∫ p,
    (f : Plane × Plane → ℝ) p * rescaledP2P ϑ N s t p ω) disorderLaw at hmeas0
  exact hmeas0

private theorem aemeasurable_polymerReadout (ϑ : ℝ) (N : ℕ) (k : ℕ)
    (s t : Fin k → ℝ) (φ : Fin k → C_c(Plane × Plane, ℝ))
    (χ : Fin k → C_c(Plane, ℝ)) :
    AEMeasurable (fun ω i =>
      ((∫ p, φ i p ∂(polymerMeasure ϑ N (s i) (t i) ω)),
       (∫ x, χ i x ∂((polymerMeasure ϑ N (s i) (t i) ω).map Prod.fst))))
      disorderLaw := by
  apply aemeasurable_pi_iff.mpr
  intro i
  exact (aemeasurable_polymerCompactPairing ϑ N (s i) (t i) (φ i)).prodMk
    (aemeasurable_polymerMarginalPairing ϑ N (s i) (t i) (χ i))

private theorem aemeasurable_frozenReadout (ϑ : ℝ) (N : ℕ) (k : ℕ)
    (s t : Fin k → ℝ) (φ : Fin k → C_c(Plane × Plane, ℝ))
    (χ : Fin k → C_c(Plane, ℝ)) :
    AEMeasurable (fun ω i =>
      ((∫ p, φ i p * rescaledP2P ϑ N (s i) (t i) p ω),
       (∫ x, χ i x * rescaledP2Plane ϑ N (s i) (t i) x ω)))
      disorderLaw := by
  apply aemeasurable_pi_iff.mpr
  intro i
  exact (aemeasurable_frozenCompactPairing ϑ N (s i) (t i) (φ i)).prodMk
    (aemeasurable_rescaledP2Plane_pairing ϑ N (s i) (t i) (χ i))

private theorem polymerMeasure_pairings_eq_frozen_eventually (ϑ : ℝ) (k : ℕ)
    (s t : Fin k → ℝ) (φ : Fin k → C_c(Plane × Plane, ℝ))
    (χ : Fin k → C_c(Plane, ℝ)) :
    ∀ᶠ N : ℕ in atTop,
      (fun ω i =>
        ((∫ p, φ i p ∂(polymerMeasure ϑ N (s i) (t i) ω)),
         (∫ x, χ i x ∂((polymerMeasure ϑ N (s i) (t i) ω).map Prod.fst)))) =ᵐ[
        disorderLaw]
      (fun ω i =>
        ((∫ p, φ i p * rescaledP2P ϑ N (s i) (t i) p ω),
         (∫ x, χ i x * rescaledP2Plane ϑ N (s i) (t i) x ω))) := by
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  filter_upwards [] with ω
  funext i
  apply Prod.ext
  · exact integral_polymerMeasure ϑ N (s i) (t i) ω (φ i)
  · exact integral_map_fst_polymerMeasure ϑ hN (s i) (t i) ω (χ i)

private noncomputable def disorderProbability : ProbabilityMeasure Disorder :=
  ⟨disorderLaw, inferInstance⟩

private def polymerReadout (ϑ : ℝ) (N k : ℕ) (s t : Fin k → ℝ)
    (φ : Fin k → C_c(Plane × Plane, ℝ)) (χ : Fin k → C_c(Plane, ℝ)) :
    Disorder → Fin k → ℝ × ℝ := fun ω i =>
      ((∫ p, φ i p ∂(polymerMeasure ϑ N (s i) (t i) ω)),
       (∫ x, χ i x ∂((polymerMeasure ϑ N (s i) (t i) ω).map Prod.fst)))

private def frozenReadout (ϑ : ℝ) (N k : ℕ) (s t : Fin k → ℝ)
    (φ : Fin k → C_c(Plane × Plane, ℝ)) (χ : Fin k → C_c(Plane, ℝ)) :
    Disorder → Fin k → ℝ × ℝ := fun ω i =>
      ((∫ p, φ i p * rescaledP2P ϑ N (s i) (t i) p ω),
       (∫ x, χ i x * rescaledP2Plane ϑ N (s i) (t i) x ω))

private theorem polymerMeasure_pairings_map_eq_frozen_eventually (ϑ : ℝ) (k : ℕ)
    (s t : Fin k → ℝ) (φ : Fin k → C_c(Plane × Plane, ℝ))
    (χ : Fin k → C_c(Plane, ℝ)) :
    (fun N : ℕ => disorderProbability.map (polymerReadout ϑ N k s t φ χ)) =ᶠ[atTop]
    (fun N : ℕ => disorderProbability.map (frozenReadout ϑ N k s t φ χ)) := by
  filter_upwards [polymerMeasure_pairings_eq_frozen_eventually ϑ k s t φ χ] with N hN
  apply Subtype.ext
  exact Measure.map_congr hN

/-- Critical SHF convergence is equivalent to convergence of the associated
polymer measures against compact and flat tests. -/
theorem isCriticalSHF_iff_polymerMeasure (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) :
    IsCriticalSHF ϑ P Z ↔
      (∀ s t, 0 ≤ s → s < t → Measurable (Z s t)) ∧
      (∀ s t, 0 ≤ s → s < t → ∀ᵐ ω ∂P,
        IsLocallyFiniteMeasure (Z s t ω) ∧
          IsLocallyFiniteMeasure ((Z s t ω).map Prod.fst)) ∧
      ∀ (k : ℕ) (s t : Fin k → ℝ), (∀ i, 0 ≤ s i ∧ s i < t i) →
        ∀ (φ : Fin k → C_c(Plane × Plane, ℝ)) (ψ : Fin k → C_c(Plane, ℝ)),
          TendstoInDistribution
            (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
              ((∫ p, φ i p ∂(polymerMeasure ϑ N (s i) (t i) ω)),
               (∫ x, ψ i x ∂((polymerMeasure ϑ N (s i) (t i) ω).map Prod.fst))))
            atTop
            (fun ω i => ((∫ p, φ i p ∂(Z (s i) (t i) ω)),
                         (∫ x, ψ i x ∂((Z (s i) (t i) ω).map Prod.fst))))
            (fun _ => disorderLaw) P := by
  unfold IsCriticalSHF
  constructor
  · rintro ⟨hMeas, hLF, hconv⟩
    refine ⟨hMeas, hLF, ?_⟩
    intro k s t hst φ ψ
    have hdist := hconv k s t hst φ ψ
    have hmaps := polymerMeasure_pairings_map_eq_frozen_eventually ϑ k s t φ ψ
    have hmaps' : (fun N : ℕ => disorderProbability.map (frozenReadout ϑ N k s t φ ψ)) =ᶠ[
        atTop] fun N => disorderProbability.map (polymerReadout ϑ N k s t φ ψ) := by
      filter_upwards [hmaps] with N hN
      exact hN.symm
    exact {
      forall_aemeasurable := fun N => aemeasurable_polymerReadout ϑ N k s t φ ψ
      aemeasurable_limit := hdist.aemeasurable_limit
      tendsto := Tendsto.congr' hmaps' hdist.tendsto }
  · rintro ⟨hMeas, hLF, hconv⟩
    refine ⟨hMeas, hLF, ?_⟩
    intro k s t hst φ ψ
    have hdist := hconv k s t hst φ ψ
    have hmaps := polymerMeasure_pairings_map_eq_frozen_eventually ϑ k s t φ ψ
    exact {
      forall_aemeasurable := fun N => aemeasurable_frozenReadout ϑ N k s t φ ψ
      aemeasurable_limit := hdist.aemeasurable_limit
      tendsto := Tendsto.congr' hmaps hdist.tendsto }

end Critical2DKPZ.SHF.Limit

end
