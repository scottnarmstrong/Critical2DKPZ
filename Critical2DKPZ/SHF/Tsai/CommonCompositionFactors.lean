/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompositionFactors
public import Critical2DKPZ.SHF.Tsai.TwoBlockReadoutLimits
public import Critical2DKPZ.SHF.Tsai.ProbabilityLimitTransport
public import Critical2DKPZ.SHF.Tsai.AEPairingIdentification
public import Critical2DKPZ.SHF.Tsai.HeatMollifier

/-! # Common measurable composition factors for two dense flows

Equal adjacent-block laws transport probability limits of the canonical
heat readouts. Uniqueness identifies their coarse tensor pairings; the
almost-sure tensor criterion identifies the full coarse measures. Hence
one measurable composition factor works for both processes.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Equal adjacent-block laws give one measurable locally finite composition factor for both dense flows. -/
theorem exists_common_measurable_composition_factor {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {a b c : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hab : a < b) (hbc : b < c)
    (hLaw : P.map (fun ω => (Z a b ω, Z b c ω)) = P'.map (fun ω => (Z' a b ω, Z' b c ω))) :
    ∃ φ : Measure (Plane × Plane) × Measure (Plane × Plane) → Measure (Plane × Plane),
      Measurable φ ∧ (∀ q, IsLocallyFiniteMeasure (φ q)) ∧
      (Z a c =ᵐ[P] fun ω => φ (Z a b ω, Z b c ω)) ∧
      (Z' a c =ᵐ[P'] fun ω => φ (Z' a b ω, Z' b c ω)) := by
  obtain ⟨φ, hφ, hφlf, hφAE⟩ := hZ.exists_measurable_composition_factor P Z ha hb hc hab hbc
  refine ⟨φ, hφ, hφlf, hφAE, ?_⟩
  apply ae_eq_of_ae_tensorPairings_eq P' (Z' a c) (fun ω => φ (Z' a b ω, Z' b c ω))
    (hZ'.1 a ha c hc (hab.trans hbc)).2 (Filter.Eventually.of_forall (fun _ => hφlf _))
  intro g g'
  let E := CompactExhaustion.choice (Plane × Plane)
  let v (n : ℕ) := modifiedTwoBlockReadout E (heatMollifier n) (compactTensorTest g g')
  have hv (n : ℕ) : Measurable (v n) := measurable_modifiedTwoBlockReadout E _
    ((isL2ApplicableMollifier_heatMollifier.2.1 n).measurable) _ (compactTensorTest g g').continuous.measurable
  let F (q : Measure (Plane × Plane) × Measure (Plane × Plane)) := ∫ p, g p.1 * g' p.2 ∂φ q
  let κ : Kernel (Measure (Plane × Plane) × Measure (Plane × Plane)) (Plane × Plane) := ⟨φ, hφ⟩
  have hFm : Measurable F :=
    ((compactTensorTest g g').continuous.measurable.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hF : (fun ω => ∫ p, g p.1 * g' p.2 ∂Z a c ω) =ᵐ[P]
      F ∘ (fun ω => (Z a b ω, Z b c ω)) := by
    filter_upwards [hφAE] with ω hω
    change (∫ p, g p.1 * g' p.2 ∂Z a c ω) = ∫ p, g p.1 * g' p.2 ∂φ (Z a b ω, Z b c ω)
    rw [hω]
  have hconv := hZ.tendstoInMeasure_modifiedTwoBlockReadout_tensor P Z ha hb hc hab hbc E
    heatMollifier isL2ApplicableMollifier_heatMollifier g g'
  have hconv' := hZ'.tendstoInMeasure_modifiedTwoBlockReadout_tensor P' Z' ha hb hc hab hbc E
    heatMollifier isL2ApplicableMollifier_heatMollifier g g'
  exact ae_eq_factor_of_map_eq_of_limits P P' _ _
    ((hZ.1 a ha b hb hab).1.prodMk (hZ.1 b hb c hc hbc).1)
    ((hZ'.1 a ha b hb hab).1.prodMk (hZ'.1 b hb c hc hbc).1)
    hLaw v hv F hFm _ _ hF hconv hconv'

end Critical2DKPZ.SHF.Tsai

end
