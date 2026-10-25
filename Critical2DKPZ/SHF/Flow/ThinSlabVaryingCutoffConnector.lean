/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabVaryingConnectorMoment
public import Critical2DKPZ.SHF.Flow.ThinSlabConnectorSecondMoment
import Mathlib.Tactic

/-! Compact connector pairings admit second-moment limits for varying connectors. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Flow

/-- Measurable connectors converging uniformly on compact sets may vary with
`N` in the second moment of a pairing with fixed middle cutoffs.
The conclusion also records eventual integrability of these squares. -/
theorem tendsto_slabVaryingCutoffConnector_sq_with_integrability (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) (hru : r < u)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : ℕ → Plane × Plane → ℝ)
    (hκ : ∀ N, Measurable (κ N)) (κlim : C(Plane × Plane, ℝ))
    (hUniform : ∀ K : Set (Plane × Plane), IsCompact K → ∀ δ > 0,
      ∀ᶠ N : ℕ in atTop, ∀ p ∈ K, |κ N p - κlim p| ≤ δ) (R : ℝ) :
    Tendsto
      (fun N => ∫ ω,
        (∫ q, Φ (q.1.1, q.2.2) * κ N (q.1.2, q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
            ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N r u ω))) ^ 2 ∂disorderLaw)
      atTop (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)
        (slabReplicaSourceTest (slabCutoffConnectorTest Φ κlim R)))) ∧
      ∀ᶠ N : ℕ in atTop, Integrable (fun ω =>
        (∫ q, Φ (q.1.1, q.2.2) * κ N (q.1.2, q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
            ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N r u ω))) ^ 2) disorderLaw := by
  let A : Set Plane := Prod.fst '' tsupport (Φ : Plane × Plane → ℝ)
  let B : Set Plane := Prod.snd '' tsupport (Φ : Plane × Plane → ℝ)
  let C : Set Plane := tsupport (ballCutoff R)
  let K : Set (Plane × Plane) := (A ×ˢ C) ∪ (C ×ˢ B)
  have hA : IsCompact A := Φ.hasCompactSupport.image continuous_fst
  have hB : IsCompact B := Φ.hasCompactSupport.image continuous_snd
  have hC : IsCompact C := hasCompactSupport_ballCutoff R
  have hK : IsCompact K := (hA.prod hC).union (hC.prod hB)
  let G : ℕ → ((Plane × Plane) × (Plane × Plane)) → ℝ := fun N q =>
    Φ (q.1.1, q.2.2) * κ N (q.1.2, q.2.1) * ballCutoff R q.1.2 * ballCutoff R q.2.1
  have hsupport (k : Plane × Plane → ℝ) :
      Function.support (fun q : (Plane × Plane) × (Plane × Plane) =>
        Φ (q.1.1, q.2.2) * k (q.1.2, q.2.1) * ballCutoff R q.1.2 * ballCutoff R q.2.1) ⊆ K ×ˢ K := by
    intro q hq
    have hΦ : Φ (q.1.1, q.2.2) ≠ 0 := by intro hz; exact hq (by simp only [hz, zero_mul])
    have hχ₁ : ballCutoff R q.1.2 ≠ 0 := by intro hz; exact hq (by simp only [hz, mul_zero, zero_mul])
    have hχ₂ : ballCutoff R q.2.1 ≠ 0 := by intro hz; exact hq (by simp only [hz, mul_zero])
    exact ⟨Or.inl ⟨⟨(q.1.1, q.2.2), subset_tsupport _ hΦ, rfl⟩, subset_tsupport _ hχ₁⟩,
      Or.inr ⟨subset_tsupport _ hχ₂, ⟨(q.1.1, q.2.2), subset_tsupport _ hΦ, rfl⟩⟩⟩
  have hGm (N : ℕ) : Measurable (G N) := by
    exact (Φ.measurable.comp (by fun_prop)).mul ((hκ N).comp (by fun_prop)) |>.mul
      ((continuous_ballCutoff R).measurable.comp (by fun_prop)) |>.mul
      ((continuous_ballCutoff R).measurable.comp (by fun_prop))
  obtain ⟨M, hM⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hΦBound (p : Plane × Plane) : |Φ p| ≤ M := by
    change ‖Φ.toContinuousMap p‖ ≤ M
    exact hM p
  have hApprox : ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ q,
      |G N q - slabCutoffConnectorTest Φ κlim R q| ≤ ε := by
    intro ε hε
    let δ : ℝ := ε / (M + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hδM : M * δ ≤ ε := by
      have heq : δ * (M + 1) = ε := by dsimp [δ]; field_simp
      nlinarith only [hδ.le, heq]
    filter_upwards [hUniform (C ×ˢ C) (hC.prod hC) δ hδ] with N hN q
    change |Φ (q.1.1, q.2.2) * κ N (q.1.2, q.2.1) * ballCutoff R q.1.2 * ballCutoff R q.2.1 -
      Φ (q.1.1, q.2.2) * κlim (q.1.2, q.2.1) * ballCutoff R q.1.2 * ballCutoff R q.2.1| ≤ ε
    by_cases hχ₁ : ballCutoff R q.1.2 = 0
    · simp only [hχ₁, mul_zero, zero_mul, sub_self, abs_zero]; exact hε.le
    by_cases hχ₂ : ballCutoff R q.2.1 = 0
    · simp only [hχ₂, mul_zero, sub_self, abs_zero]; exact hε.le
    have hsmall := hN (q.1.2, q.2.1) ⟨subset_tsupport _ hχ₁, subset_tsupport _ hχ₂⟩
    have hc₁ := ballCutoff_mem_Icc R q.1.2
    have hc₂ := ballCutoff_mem_Icc R q.2.1
    calc
      _ = |Φ (q.1.1, q.2.2) * (κ N (q.1.2, q.2.1) - κlim (q.1.2, q.2.1)) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1| := by congr 1; ring
      _ = |Φ (q.1.1, q.2.2)| * |κ N (q.1.2, q.2.1) - κlim (q.1.2, q.2.1)| *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 := by
        simp only [abs_mul, abs_of_nonneg hc₁.1, abs_of_nonneg hc₂.1]
      _ ≤ M * δ * 1 * 1 := by
        exact mul_le_mul (mul_le_mul
          (mul_le_mul (hΦBound _) hsmall (abs_nonneg _) hM0) hc₁.2 hc₁.1 (by positivity))
          hc₂.2 hc₂.1 (by positivity)
      _ ≤ ε := by simpa only [mul_one] using hδM
  exact tendsto_slabVaryingCompactPairing_sq_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru
    (slabCutoffConnectorTest Φ κlim R) G hGm K hK (hsupport κlim)
    (fun N => hsupport (κ N)) hApprox

/-- The second moments of pairings with varying compact connectors converge to their continuum limit. Eventual square integrability is supplied by `tendsto_slabVaryingCutoffConnector_sq_with_integrability`. -/
theorem tendsto_slabVaryingCutoffConnector_sq (ϑ : ℝ)
    (hPolymerMomentInput : PolymerMomentLimit ϑ) (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    {s t r u : ℝ} (hs : 0 ≤ s) (hst : s < t) (htr : t ≤ r) (hru : r < u)
    (Φ : C_c(Plane × Plane, ℝ)) (κ : ℕ → Plane × Plane → ℝ)
    (hκ : ∀ N, Measurable (κ N)) (κlim : C(Plane × Plane, ℝ))
    (hUniform : ∀ K : Set (Plane × Plane), IsCompact K → ∀ δ > 0,
      ∀ᶠ N : ℕ in atTop, ∀ p ∈ K, |κ N p - κlim p| ≤ δ) (R : ℝ) :
    Tendsto
      (fun N => ∫ ω,
        (∫ q, Φ (q.1.1, q.2.2) * κ N (q.1.2, q.2.1) *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
            ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N r u ω))) ^ 2 ∂disorderLaw)
      atTop (𝓝 (slabSeparatedMomentIntegral (ϑ - Real.eulerMascheroniConstant) (t - s) (u - r)
        (slabReplicaSourceTest (slabCutoffConnectorTest Φ κlim R)))) :=
  (tendsto_slabVaryingCutoffConnector_sq_with_integrability ϑ hPolymerMomentInput hFlatSixthMomentInput hs hst htr hru
    Φ κ hκ κlim hUniform R).1

end Critical2DKPZ.SHF.Flow

end
