/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordTimeIntegral
public import Critical2DKPZ.SHF.Moments.SinglePairWordTruncation
import Critical2DKPZ.Renewal.Primitive
import Mathlib.Tactic

/-! # Endpoint integrability for the tested two-particle future profile -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- The continuum future spatial profile is integrable in renewal time up to
both endpoints. The integrable scalar renewal density is a common majorant. -/
theorem integrableOn_pairTwoTestedSpatialProfile_time
    (θ H : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    IntegrableOn (fun u => pairTwoTestedSpatialProfile θ u (H - u) φ a z) (Set.Icc 0 H) := by
  let K : ℝ := 16 * Real.pi * ‖(φ 0).toBoundedContinuousFunction‖ *
    ‖(φ 1).toBoundedContinuousFunction‖
  have hρ : IntegrableOn (DeltaBose.scalarDensity θ) (Set.Ioo 0 H) :=
    (Renewal.integrableOn_scalarDensity_Ioc θ H).mono_set Set.Ioo_subset_Ioc_self
  have hmeas := (continuousOn_pairTwoTestedSpatialProfile_time θ H φ a z).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  have hIoo : IntegrableOn (fun u => pairTwoTestedSpatialProfile θ u (H - u) φ a z)
      (Set.Ioo 0 H) := by
    apply (hρ.const_mul K).mono' hmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have h := (pairTwoTestedSpatialProfile_integrable_bound θ u (H - u)
      hu.1 (sub_pos.mpr hu.2) φ a z).2
    rw [Real.norm_eq_abs]
    convert h using 1
    dsimp [K]
    ring
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  exact hIoo

/-- On every subinterval of the future horizon the absolute profile integral
is bounded by the same scalar-density integral, uniformly in all locations. -/
theorem abs_integral_pairTwoTestedSpatialProfile_le_scalar
    (θ H : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ H) :
    IntervalIntegrable (fun u => pairTwoTestedSpatialProfile θ u (H - u) φ a z) volume s t ∧
    |∫ u in s..t, pairTwoTestedSpatialProfile θ u (H - u) φ a z| ≤
      (16 * Real.pi * ‖(φ 0).toBoundedContinuousFunction‖ *
        ‖(φ 1).toBoundedContinuousFunction‖) * ∫ u in s..t, DeltaBose.scalarDensity θ u := by
  let K : ℝ := 16 * Real.pi * ‖(φ 0).toBoundedContinuousFunction‖ *
    ‖(φ 1).toBoundedContinuousFunction‖
  have hi := integrableOn_pairTwoTestedSpatialProfile_time θ H φ a z
  have hsub : Set.Icc s t ⊆ Set.Icc 0 H := fun u hu => ⟨hs.trans hu.1, hu.2.trans ht⟩
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hst).mpr (hi.mono_set hsub), ?_⟩
  have hρ : IntegrableOn (fun u => K * DeltaBose.scalarDensity θ u) (Set.Ioc s t) :=
    ((Renewal.integrableOn_scalarDensity_Ioc θ H).mono_set
      (fun u hu => ⟨hs.trans_lt hu.1, hu.2.trans ht⟩)).const_mul K
  have hb : ∀ᵐ u ∂volume.restrict (Set.Ioc s t),
      ‖pairTwoTestedSpatialProfile θ u (H - u) φ a z‖ ≤ K * DeltaBose.scalarDensity θ u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    by_cases hEnd : u = H
    · subst u
      have hK : 0 ≤ K := by dsimp [K]; positivity
      have hρ : 0 ≤ DeltaBose.scalarDensity θ H :=
        (DeltaBose.scalarDensity_pos θ (hs.trans_lt hu.1)).le
      simpa [pairTwoTestedSpatialProfile, pairTwoTerminalConvolution] using mul_nonneg hK hρ
    have huH : u < H := lt_of_le_of_ne (hu.2.trans ht) hEnd
    have he := (pairTwoTestedSpatialProfile_integrable_bound θ u (H - u)
      (hs.trans_lt hu.1) (sub_pos.mpr huH) φ a z).2
    rw [Real.norm_eq_abs]
    convert he using 1
    dsimp [K]
    ring
  have he := norm_integral_le_of_norm_le hρ hb
  simpa only [K, intervalIntegral.integral_of_le hst, Real.norm_eq_abs, integral_const_mul] using he

private theorem scalarDensity_endpoint_integrals_small (θ H : ℝ) (hH : 0 < H)
    (R : ℝ) (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ H / 2 ∧ δ ≤ R ∧
      |∫ u in (0 : ℝ)..δ, DeltaBose.scalarDensity θ u| ≤ ε ∧
      |∫ u in (H - δ)..H, DeltaBose.scalarDensity θ u| ≤ ε := by
  have hi : IntegrableOn (DeltaBose.scalarDensity θ) (Set.uIcc 0 H) := by
    rw [Set.uIcc_of_le hH.le, integrableOn_Icc_iff_integrableOn_Ioc]
    exact Renewal.integrableOn_scalarDensity_Ioc θ H
  have h₀ := intervalIntegral.continuousOn_primitive_interval hi
  have h₁ := intervalIntegral.continuousOn_primitive_interval_left hi
  have hm₀ : (0 : ℝ) ∈ Set.uIcc 0 H := Set.left_mem_uIcc
  have hm₁ : H ∈ Set.uIcc 0 H := Set.right_mem_uIcc
  obtain ⟨δ₀, hδ₀, he₀⟩ := Metric.continuousWithinAt_iff.mp (h₀ 0 hm₀) ε hε
  obtain ⟨δ₁, hδ₁, he₁⟩ := Metric.continuousWithinAt_iff.mp (h₁ H hm₁) ε hε
  let δ : ℝ := min (min (H / 2) R) (min (δ₀ / 2) (δ₁ / 2))
  have hδ : 0 < δ := lt_min (lt_min (half_pos hH) hR) (lt_min (half_pos hδ₀) (half_pos hδ₁))
  have hδH : δ ≤ H / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδR : δ ≤ R := (min_le_left _ _).trans (min_le_right _ _)
  have hδ₀' : δ < δ₀ :=
    (le_trans (min_le_right _ _) (min_le_left _ _)).trans_lt (half_lt_self hδ₀)
  have hδ₁' : δ < δ₁ :=
    (le_trans (min_le_right _ _) (min_le_right _ _)).trans_lt (half_lt_self hδ₁)
  have hmδ : δ ∈ Set.uIcc 0 H := by
    rw [Set.uIcc_of_le hH.le]
    exact ⟨hδ.le, hδH.trans (half_le_self hH.le)⟩
  have hmHδ : H - δ ∈ Set.uIcc 0 H := by
    rw [Set.uIcc_of_le hH.le]
    constructor <;> linarith only [hδ, hδH, hH]
  have hd₀ : dist δ 0 < δ₀ := by simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ] using hδ₀'
  have hd₁ : dist (H - δ) H < δ₁ := by
    simpa only [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hδ] using hδ₁'
  refine ⟨δ, hδ, hδH, hδR, ?_, ?_⟩
  · simpa only [intervalIntegral.integral_same, Real.dist_eq, sub_zero] using (he₀ hmδ hd₀).le
  · simpa only [intervalIntegral.integral_same, Real.dist_eq, sub_zero] using (he₁ hmHδ hd₁).le

/-- Both continuum endpoint strips are uniformly small in all spatial
locations. Integrability of each strip is retained in the statement. -/
theorem pairTwoTestedSpatialProfile_endpoint_strips_small_below
    (θ H : ℝ) (hH : 0 < H) (R : ℝ) (hR : 0 < R)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ H / 2 ∧ δ ≤ R ∧
      ∀ a : Fin 2 → Plane, ∀ z : Plane,
        IntervalIntegrable (fun u => pairTwoTestedSpatialProfile θ u (H - u) φ a z)
          volume 0 δ ∧
        IntervalIntegrable (fun u => pairTwoTestedSpatialProfile θ u (H - u) φ a z)
          volume (H - δ) H ∧
        |∫ u in (0 : ℝ)..δ, pairTwoTestedSpatialProfile θ u (H - u) φ a z| ≤ ε ∧
        |∫ u in (H - δ)..H, pairTwoTestedSpatialProfile θ u (H - u) φ a z| ≤ ε := by
  intro ε hε
  let K : ℝ := 16 * Real.pi * ‖(φ 0).toBoundedContinuousFunction‖ *
    ‖(φ 1).toBoundedContinuousFunction‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let η : ℝ := ε / (K + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hδH, hδR, hs₀, hs₁⟩ := scalarDensity_endpoint_integrals_small θ H hH R hR hη
  refine ⟨δ, hδ, hδH, hδR, ?_⟩
  intro a z
  have hδH' : δ ≤ H := hδH.trans (half_le_self hH.le)
  have hHδ : 0 ≤ H - δ := sub_nonneg.mpr hδH'
  have h₀ := abs_integral_pairTwoTestedSpatialProfile_le_scalar θ H φ a z (s := 0) (t := δ)
    le_rfl hδ.le hδH'
  have h₁ := abs_integral_pairTwoTestedSpatialProfile_le_scalar θ H φ a z (s := H - δ) (t := H)
    hHδ (sub_le_self H hδ.le) le_rfl
  have hKη : K * η ≤ ε := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < K + 1)).2
    nlinarith only [hε]
  refine ⟨h₀.1, h₁.1, ?_, ?_⟩
  · calc
      _ ≤ K * (∫ u in (0 : ℝ)..δ, DeltaBose.scalarDensity θ u) := h₀.2
      _ ≤ K * η := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hs₀) hK
      _ ≤ ε := hKη
  · calc
      _ ≤ K * (∫ u in (H - δ)..H, DeltaBose.scalarDensity θ u) := h₁.2
      _ ≤ K * η := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hs₁) hK
      _ ≤ ε := hKη


end Critical2DKPZ.SHF.Moments

end
