/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.CanonicalUnitLimit
import Critical2DKPZ.Extensions.ScaleLimit.ScalingReduction
import Critical2DKPZ.Extensions.ScaleLimit.TranslationReduction
import Critical2DKPZ.Extensions.ScaleLimit.FiniteFamilyLaw
import Critical2DKPZ.Extensions.ScaleLimit.SeqReduction
import Critical2DKPZ.Extensions.ScaleLimit.ZeroReduction
import Critical2DKPZ.Extensions.ScaleLimit.Centring
import Mathlib.Tactic

/-! # Finite-dimensional Brownian limits at arbitrary positive horizon and center -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Scaling and translation transport the canonical unit-time finite-dimensional
limit to the given KPZ version at any positive horizon and spatial center. -/
theorem kpz_scale_finiteDimensional_tendstoInDistribution_positive
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (x : Plane) (φ : TestFn)
    (hφ : ∀ y, 0 ≤ φ y) (hφ1 : (∫ y, φ y) = 1)
    (I : Finset ℝ≥0) (hI : ∀ i ∈ I, 0 < i) :
    TendstoInDistribution (fun (L : Set.Ioi (0 : ℝ)) ω (i : I) =>
      scaledPairing (H t 0 ω) φ x L (i.val : ℝ)) atTop id
      (fun _ => P) (BrownianReal.projectiveFamily I) := by
  obtain ⟨Z', H', hZ', hH', hScale⟩ := scaling_reduction ϑ P Z hZ H hH (I := I) ht φ x
  let φt := φ.dilate (Real.sqrt t)⁻¹ 0
  let x' := (Real.sqrt t)⁻¹ • x
  have hφt := dilate_nonneg_mass φ hφ hφ1 (inv_pos.mpr (Real.sqrt_pos.mpr ht)) 0
  have hUnit := canonical_unit_kpz_joint_limit (ϑ + Real.log t) P Z' hZ' H' hH' φt hφt.1 hφt.2 I hI
  have hm (L : Set.Ioi (0 : ℝ)) : AEMeasurable
      (fun ω (i : I) => scaledPairing (H t 0 ω) φ x L (i.val : ℝ)) P :=
    aemeasurable_pi_iff.mpr fun i => (memLp_scaledPairing_two ϑ P Z hZ H hH ht φ x L i.val).aemeasurable
  have hmaps (L : Set.Ioi (0 : ℝ)) :
      P.map (fun ω (i : I) => scaledPairing (H t 0 ω) φ x L (i.val : ℝ)) =
      P.map (fun ω (i : I) => scaledPairing (H' 1 0 ω) φt 0 L (i.val : ℝ)) := by
    let ε : I → ℝ := fun i => scaleRadius L (i.val : ℝ)
    have harg (i : I) : φ.dilate (ε i / Real.sqrt t) x' = φt.dilate (ε i) x' := by
      change φ.dilate (ε i / Real.sqrt t) x' = (φ.dilate (Real.sqrt t)⁻¹ 0).dilate (ε i) x'
      rw [dilate_dilate_zero]
      congr 1
      ring
    have hsc : P.map (fun ω i => H t 0 ω (φ.dilate (ε i) x)) =
        P.map (fun ω i => H' 1 0 ω (φt.dilate (ε i) x')) := by
      have h0 := hScale ε
      change P.map (fun ω i => H t 0 ω (φ.dilate (ε i) x)) =
        P.map (fun ω i => H' 1 0 ω (φ.dilate (ε i / Real.sqrt t) x')) at h0
      simpa only [harg] using h0
    have hraw : P.map (fun ω i => H t 0 ω (φ.dilate (ε i) x)) =
        P.map (fun ω i => H' 1 0 ω (φt.dilate (ε i) 0)) :=
      hsc.trans (translation_dilate_law (ϑ + Real.log t) P Z' hZ' H' hH' zero_lt_one φt x' ε)
    have hXm : AEMeasurable (fun ω i => H t 0 ω (φ.dilate (ε i) x)) P :=
      aemeasurable_pi_iff.mpr fun i => (memLp_kpz_two ϑ P Z hZ H hH t ht _).aemeasurable
    have hYm : AEMeasurable (fun ω i => H' 1 0 ω (φt.dilate (ε i) 0)) P :=
      aemeasurable_pi_iff.mpr fun i =>
        (memLp_kpz_two (ϑ + Real.log t) P Z' hZ' H' hH' 1 zero_lt_one _).aemeasurable
    exact map_div_family_eq P P _ _ hXm hYm hraw (Real.sqrt L)
  exact (tendstoInDistribution_congr_of_map_eq hm hUnit.forall_aemeasurable aemeasurable_id hmaps).mpr hUnit

end Critical2DKPZ.Extensions.ScaleLimit
