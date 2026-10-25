/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.CompactTensorApproximation
public import Critical2DKPZ.SHF.Tsai.CompactPairingApproximation
public import Critical2DKPZ.RandomMeasure.GeneralMetric

/-! # Almost-sure identification by endpoint tensors

Almost-sure equality of compact endpoint tensor pairings identifies locally finite random
measures on one event of full probability, using countably many determining tests.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Equality almost surely of all tensor pairings implies the same for each compact plane-pair test. -/
theorem ae_compactPairings_eq_of_ae_tensorPairings_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z Z' : Ω → Measure (Plane × Plane))
    (hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z ω)) (hlf' : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z' ω))
    (h : ∀ g g' : C_c(Plane, ℝ),
      (fun ω => ∫ p, g p.1 * g' p.2 ∂Z ω) =ᵐ[P] fun ω => ∫ p, g p.1 * g' p.2 ∂Z' ω)
    (f : C_c(Plane × Plane, ℝ)) :
    (fun ω => ∫ p, f p ∂Z ω) =ᵐ[P] fun ω => ∫ p, f p ∂Z' ω := by
  classical
  obtain ⟨K, hK, r, g, g', hvSupport, hvApprox⟩ := exists_compactTensorSum_sequence f
  let v (n : ℕ) : C_c(Plane × Plane, ℝ) := ∑ b, compactTensorTest (g n b) (g' n b)
  have hEq (n : ℕ) : (fun ω => ∫ p, v n p ∂Z ω) =ᵐ[P] fun ω => ∫ p, v n p ∂Z' ω := by
    filter_upwards [hlf, hlf', ae_all_iff.2 (fun b : Fin (r n) => h (g n b) (g' n b))]
      with ω hω hω' hωEq
    let : IsLocallyFiniteMeasure (Z ω) := hω
    let : IsLocallyFiniteMeasure (Z' ω) := hω'
    simp only [v, CompactlySupportedContinuousMap.sum_apply]
    rw [integral_finsetSum _ (fun b _ => (compactTensorTest (g n b) (g' n b)).integrable),
      integral_finsetSum _ (fun b _ => (compactTensorTest (g n b) (g' n b)).integrable)]
    exact Finset.sum_congr rfl (fun b _ => hωEq b)
  filter_upwards [hlf, hlf', ae_all_iff.2 hEq] with ω hω hω' hωEq
  let : IsLocallyFiniteMeasure (Z ω) := hω
  let : IsLocallyFiniteMeasure (Z' ω) := hω'
  have hlimit (μ : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ] :
      Tendsto (fun n => ∫ p, v n p ∂μ) atTop (𝓝 (∫ p, f p ∂μ)) :=
    tendsto_integral_of_uniform_compact_support μ f v (K ∪ tsupport (f : Plane × Plane → ℝ))
      (hK.union f.hasCompactSupport) Set.subset_union_right
      (fun n => (hvSupport n).trans Set.subset_union_left) hvApprox
  exact tendsto_nhds_unique ((hlimit (Z ω)).congr hωEq) (hlimit (Z' ω))

/-- Equality almost surely of every compact test pairing identifies locally finite random measures. -/
theorem ae_eq_of_ae_compactPairings_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z Z' : Ω → Measure (Plane × Plane))
    (hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z ω)) (hlf' : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z' ω))
    (h : ∀ f : C_c(Plane × Plane, ℝ),
      (fun ω => ∫ p, f p ∂Z ω) =ᵐ[P] fun ω => ∫ p, f p ∂Z' ω) : Z =ᵐ[P] Z' := by
  let K := CompactExhaustion.choice (Plane × Plane)
  have hAll := ae_all_iff.2 (fun i : (ℕ × ℕ) ⊕ ℕ => h (RandomMeasure.countableVagueTest K i))
  filter_upwards [hlf, hlf', hAll] with ω hω hω' hωEq
  let μ : RandomMeasure.PositiveRadonMeasure (Plane × Plane) := ⟨Z ω, hω⟩
  let ν : RandomMeasure.PositiveRadonMeasure (Plane × Plane) := ⟨Z' ω, hω'⟩
  have hRead : RandomMeasure.countableVagueReadout K μ = RandomMeasure.countableVagueReadout K ν :=
    funext hωEq
  exact congrArg Subtype.val (RandomMeasure.countableVagueReadout_injective K hRead)

/-- Compact endpoint tensors identify locally finite random measures almost surely. -/
theorem ae_eq_of_ae_tensorPairings_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z Z' : Ω → Measure (Plane × Plane))
    (hlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z ω)) (hlf' : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z' ω))
    (h : ∀ g g' : C_c(Plane, ℝ),
      (fun ω => ∫ p, g p.1 * g' p.2 ∂Z ω) =ᵐ[P] fun ω => ∫ p, g p.1 * g' p.2 ∂Z' ω) : Z =ᵐ[P] Z' :=
  ae_eq_of_ae_compactPairings_eq P Z Z' hlf hlf'
    (ae_compactPairings_eq_of_ae_tensorPairings_eq P Z Z' hlf hlf' h)

end Critical2DKPZ.SHF.Tsai

end
