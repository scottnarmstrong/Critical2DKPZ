/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.DenseTelescoping
public import Critical2DKPZ.SHF.Tsai.LawDetermination
public import Critical2DKPZ.SHF.Tsai.HybridLimits

/-! # Interval-law uniqueness from hybrid increment bounds

On a dense time set in a compact interval, a superlinear bound on hybrid expectation
increments identifies the single-interval laws of two flows.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology CompactlySupported ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A superlinear hybrid increment bound gives equality of single-interval laws for dense-time flows on a compact interval. -/
theorem isDenseSHF_law_eq_of_hybridValue_step_le
    (θ B : ℝ) (_hB : 0 < B) (D : Set ℝ) (hD : D ⊆ Set.Icc 0 B)
    (hdense : Set.Icc 0 B ⊆ closure D) {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsDenseSHF θ D P Z) (hZ' : IsDenseSHF θ D P' Z')
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    (hstep : ∀ {m r : ℕ} (g g' : Fin m → Fin r → C_c(Plane, ℝ))
      (H : (Fin m → ℝ) → ℝ) (_hH : ContDiff ℝ 4 H) (CH : ℝ)
      (_hCH : ∀ k ≤ 4, ∀ x, ‖iteratedFDeriv ℝ k H x‖ ≤ CH)
      {p : ℝ≥0∞} (_hp : 6 < p) (_hp' : p ≠ ⊤),
      ∃ C : ℝ, ∀ a ∈ D, ∀ b ∈ D, s ≤ a → a < b → b ≤ t → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ ℓ in Filter.atTop,
          |hybridValue P P' Z Z' s t g g' H a ℓ -
            hybridValue P P' Z Z' s t g g' H b ℓ| ≤
              C * (b - a) ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) + ε) :
    P.map (Z s t) = P'.map (Z' s t) := by
  have hsB : s ∈ Set.Icc 0 B := hD hs
  have htB : t ∈ Set.Icc 0 B := hD ht
  have hstD : Set.Icc s t ⊆ closure D := by
    intro x hx
    apply hdense
    exact ⟨le_trans hsB.1 hx.1, le_trans hx.2 htB.2⟩
  apply map_eq_of_forall_integral_contDiff_eq P P' (fun ω => Z s t ω) (fun ω => Z' s t ω)
  · exact (hZ.1 s hs t ht hst).1
  · exact (hZ'.1 s hs t ht hst).1
  · exact (hZ.1 s hs t ht hst).2
  · exact (hZ'.1 s hs t ht hst).2
  · intro m r g g' H hH CH
    obtain ⟨CH, hCH⟩ := CH
    have hH0 (z : Fin m → ℝ) : ‖H z‖ ≤ CH := by
      simpa only [norm_iteratedFDeriv_zero] using hCH 0 (by omega) z
    have hbound := hstep g g' H hH CH hCH (p := (8 : ℝ≥0∞)) (by norm_num) (by simp)
    obtain ⟨C, hbound⟩ := hbound
    have h8 : (8 : ℝ≥0∞).toReal = (8 : ℝ) := by simp
    have hpow : 1 < (3 / 2 : ℝ) * (1 - 2 / (8 : ℝ)) := by norm_num
    let R (c : ℝ) (ℓ : ℕ) := hybridValue P P' Z Z' s t g g' H c ℓ
    have hlim (c : ℝ) (hc : c ∈ D) (hsc : s ≤ c) (hct : c ≤ t) :
        ∃ L, Tendsto (R c) Filter.atTop (𝓝 L) :=
      exists_hybridValue_limit D P P' Z Z' hZ hZ' hs hc ht hsc hct
        g g' H hH.continuous CH hH0
    have hsR (ℓ : ℕ) : R s ℓ =
        ∫ ω, H (fun i => ∑ k, ∫ q, g i k q.1 * g' i k q.2 ∂Z s t ω) ∂P := by
      simp [R, hybridValue]
    have htR (ℓ : ℕ) : R t ℓ =
        ∫ ω, H (fun i => ∑ k, ∫ q, g i k q.1 * g' i k q.2 ∂Z' s t ω) ∂P' := by
      simp [R, hybridValue, ne_of_gt hst]
    have hreadout := eq_endpoints_of_dense_eventual_increment_bound hstD hs ht hst hpow
      R hsR htR hlim (fun a ha b hb hsa hab hbt ε hε => by
        simpa only [R, h8] using hbound a ha b hb hsa hab hbt ε hε)
    simpa only [hsR, htR] using hreadout

end Critical2DKPZ.SHF.Tsai

end
