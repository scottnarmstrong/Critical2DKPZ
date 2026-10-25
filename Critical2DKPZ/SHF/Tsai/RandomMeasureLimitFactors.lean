/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MeasurableLimitFactors
public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.RandomMeasure.GeneralPolish
public import Critical2DKPZ.RandomMeasure.GeneralRandom

/-! # Random-measure factors from compact pairing limits

Limits in probability of compact-test integrals recover a measurable Radon-measure-valued
function of the common input. Almost-sure local finiteness identifies this factor with the
original random measure.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Compact pairing limits of measurable functions of one input recover a locally finite measure-valued factor. -/
theorem exists_measure_factor_of_pairing_limits {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (X : Ω → S) (Z : Ω → Measure (Plane × Plane))
    (hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z ω))
    (v : C_c(Plane × Plane, ℝ) → ℕ → S → ℝ)
    (hv : ∀ f n, Measurable (v f n))
    (hconv : ∀ f : C_c(Plane × Plane, ℝ),
      TendstoInMeasure P (fun n ω => v f n (X ω)) atTop (fun ω => ∫ p, f p ∂Z ω)) :
    ∃ φ : S → Measure (Plane × Plane), Measurable φ ∧
      (∀ x, IsLocallyFiniteMeasure (φ x)) ∧ Z =ᵐ[P] φ ∘ X := by
  classical
  let K := CompactExhaustion.choice (Plane × Plane)
  let E := RandomMeasure.PositiveRadonMeasure (Plane × Plane)
  let : Nonempty E := ⟨⟨0, inferInstance⟩⟩
  let : PolishSpace E := RandomMeasure.vaguePolishSpace
  let F : Ω → E := RandomMeasure.radonValuedModification K Z
  let e : E → ((ℕ × ℕ) ⊕ ℕ) → ℝ := RandomMeasure.countableVagueReadout K
  have heMeas : Measurable e := Measurable.of_eval fun i =>
    RandomMeasure.measurable_vaguePairing_eval (RandomMeasure.countableVagueTest K i)
  have he : MeasurableEmbedding e :=
    heMeas.measurableEmbedding (RandomMeasure.countableVagueReadout_injective K)
  have hF : (fun ω => (F ω : Measure (Plane × Plane))) =ᵐ[P] Z :=
    RandomMeasure.ae_eq_radonValuedModification K P Z hlf
  have hconvRead (i : (ℕ × ℕ) ⊕ ℕ) :
      TendstoInMeasure P (fun n ω => v (RandomMeasure.countableVagueTest K i) n (X ω)) atTop
        (fun ω => e (F ω) i) := by
    have hread : (fun ω => ∫ p, RandomMeasure.countableVagueTest K i p ∂Z ω) =ᵐ[P]
        fun ω => e (F ω) i := by
      filter_upwards [hF] with ω hω
      change (∫ p, RandomMeasure.countableVagueTest K i p ∂Z ω) =
        ∫ p, RandomMeasure.countableVagueTest K i p ∂(F ω : Measure (Plane × Plane))
      rw [hω]
    exact (hconv _).congr (fun _ => Filter.EventuallyEq.rfl) hread
  obtain ⟨ψ, hψ, hψAE⟩ := exists_measurable_factor_of_coordinate_limits P X F e he
    (fun i => v (RandomMeasure.countableVagueTest K i)) (fun i n => hv _ n) hconvRead
  refine ⟨fun x => (ψ x : Measure (Plane × Plane)), measurable_subtype_coe.comp hψ,
    (fun x => (ψ x).property), ?_⟩
  exact hF.symm.trans (hψAE.fun_comp Subtype.val)

end Critical2DKPZ.SHF.Tsai

end
