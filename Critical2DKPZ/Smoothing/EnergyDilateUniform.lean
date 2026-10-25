/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.UnitHorizonPerturbed
public import Critical2DKPZ.Smoothing.SpatialRescaling
public import Critical2DKPZ.SmallScales.Inputs
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Uniform heat-energy bounds for dilated tests -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.Smoothing

/-- The unit-horizon smoothing error obeys a heat-energy bound uniform over compact ranges of positive dilations. -/
def LatticeSmoothingErrorEnergyDilate : Prop :=
  ∀ A H : ℝ,
  ∃ C δ₁ : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ φ : Plane → ℝ, Measurable φ → HasCompactSupport φ →
      Integrable φ → (∃ M : ℝ, ∀ x, |φ x| ≤ M) → ∀ c₀ c₁ : ℝ, 0 < c₀ → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ M : ℕ in atTop, Even M → ∀ c ∈ Set.Icc c₀ c₁,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ j k : ℕ, Even j → Even k →
        (j : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ j + 6 →
        (k : ℤ) ≤ evenCeil (δ * M) + 6 → (evenCeil (δ * M) : ℤ) ≤ k + 6 →
        ∀ h₀ : Plane →ᵇ ℝ, ‖h₀‖ ≤ H →
          eLpNorm (latticeSmoothingError (criticalBeta ϑ M) M M k j h₀
              (fun y => c * φ (Real.sqrt c • y))) 2 disorderLaw ≤
            ENNReal.ofReal (Real.sqrt
                (C * heatEnergy (Real.sqrt δ) (fun y => c * φ (Real.sqrt c • y)) /
                  |Real.log δ|) +
              C * (∫ x, |c * φ (Real.sqrt c • x)|) * |Real.log δ| ^ (-(1 : ℝ) / 40) + ε)


/-- A positive planar dilation preserves the `L¹` mass of a test function. -/
theorem integral_abs_dilate_eq (φ : Plane → ℝ) (hφ : Integrable φ) {c : ℝ} (hc : 0 < c) :
    (∫ x, |c * φ (Real.sqrt c • x)|) = ∫ x, |φ x| := by
  have hcomp : Integrable (fun x : Plane => |φ (Real.sqrt c • x)|) :=
    hφ.norm.comp_smul (ne_of_gt (Real.sqrt_pos.2 hc))
  calc
    (∫ x, |c * φ (Real.sqrt c • x)|) =
        ∫ x, c * |φ (Real.sqrt c • x)| := by
          congr 1
          funext x
          rw [abs_mul, abs_of_pos hc]
    _ = c * ∫ x, |φ (Real.sqrt c • x)| := integral_const_mul _ _
    _ = ∫ x, |φ x| := by
      simpa using (integral_plane_sqrt_scale hc (fun x : Plane => |φ x|)).symm

/-- Measurability of a positive dilation of a measurable profile. -/
theorem measurable_dilate (φ : Plane → ℝ) (hφ : Measurable φ) (c : ℝ) :
    Measurable (fun x : Plane => c * φ (Real.sqrt c • x)) := by
  apply measurable_const.mul
  apply hφ.comp
  fun_prop

/-- Integrability of a positive dilation of an integrable profile. -/
theorem integrable_dilate (φ : Plane → ℝ) (hφ : Integrable φ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : Plane => c * φ (Real.sqrt c • x)) := by
  exact (hφ.comp_smul (ne_of_gt (Real.sqrt_pos.2 hc))).const_mul c

/-- Compact support is preserved under positive dilation. -/
theorem hasCompactSupport_dilate (φ : Plane → ℝ) (hφ : HasCompactSupport φ) {c : ℝ}
    (hc : 0 < c) : HasCompactSupport (fun x : Plane => c * φ (Real.sqrt c • x)) := by
  exact (hφ.comp_smul (ne_of_gt (Real.sqrt_pos.2 hc))).mul_left



private theorem tendsto_integral_abs_compact_dilate (ψ : Plane → ℝ) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    Tendsto (fun c => ∫ x, |c * ψ (Real.sqrt c • x) - c₀ * ψ (Real.sqrt c₀ • x)|)
      (nhds c₀) (𝓝 0) := by
  obtain ⟨K, hK, hψK⟩ := exists_compact_iff_hasCompactSupport.mpr hψc
  let s : Set ℝ := Set.Icc (c₀ / 2) (2 * c₀)
  let S : Set (ℝ × Plane) := s ×ˢ K
  let e : ℝ × Plane → Plane := fun q => (Real.sqrt q.1)⁻¹ • q.2
  let k : Set Plane := e '' S
  have hs : IsCompact s := isCompact_Icc
  have hS : IsCompact S := hs.prod hK
  have heCont : ContinuousOn e S := by
    have hsqrt : ContinuousOn (fun q : ℝ × Plane => Real.sqrt q.1) S :=
      Real.continuous_sqrt.continuousOn.comp continuousOn_fst (fun q hq => hq.1)
    have hsqrtNe : ∀ q ∈ S, Real.sqrt q.1 ≠ 0 := by
      intro q hq
      have hqpos : 0 < q.1 := by
        have hlo : c₀ / 2 ≤ q.1 := hq.1.1
        linarith [hc₀]
      exact ne_of_gt (Real.sqrt_pos.2 hqpos)
    exact (hsqrt.inv₀ hsqrtNe).smul continuousOn_snd
  have hk : IsCompact k := hS.image_of_continuousOn heCont
  have hc₀s : c₀ ∈ s := by
    dsimp [s]
    constructor <;> nlinarith [hc₀]
  have hzero (c : ℝ) (hc : c ∈ s) (x : Plane) (hx : x ∉ k) :
      ψ (Real.sqrt c • x) = 0 := by
    have hcpos : 0 < c := by
      have hlo : c₀ / 2 ≤ c := hc.1
      linarith [hc₀]
    by_contra hne
    have hyK : Real.sqrt c • x ∈ K := by
      by_contra hy
      exact hne (hψK _ hy)
    have hpoint : (Real.sqrt c)⁻¹ • (Real.sqrt c • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.2 hcpos)), one_smul]
    apply hx
    rw [← hpoint]
    exact ⟨(c, Real.sqrt c • x), ⟨hc, hyK⟩, rfl⟩
  let f : ℝ → Plane → ℝ := fun c x =>
    |c * ψ (Real.sqrt c • x) - c₀ * ψ (Real.sqrt c₀ • x)|
  have hf : Continuous (Function.uncurry f) := by
    change Continuous (fun p : ℝ × Plane =>
      |p.1 * ψ (Real.sqrt p.1 • p.2) - c₀ * ψ (Real.sqrt c₀ • p.2)|)
    fun_prop
  have hfSupport : ∀ c x, c ∈ s → x ∉ k → f c x = 0 := by
    intro c x hc hx
    have hz₁ := hzero c hc x hx
    have hz₂ := hzero c₀ hc₀s x hx
    simp [f, hz₁, hz₂]
  have hcontOn := continuousOn_integral_of_compact_support (μ := (volume : Measure Plane))
    (f := f) (s := s) (k := k)
    hk hf.continuousOn hfSupport
  have hleft : c₀ / 2 < c₀ := by linarith
  have hright : c₀ < 2 * c₀ := by nlinarith
  have hmem : s ∈ 𝓝 c₀ := by
    dsimp [s]
    exact Icc_mem_nhds hleft hright
  have hcontAt := hcontOn.continuousAt hmem
  change ContinuousAt (fun c => ∫ x, f c x) c₀ at hcontAt
  have hvalue : (∫ x, f c₀ x) = 0 := by simp [f]
  have ht := hcontAt.tendsto
  rw [hvalue] at ht
  simpa [f] using ht

private theorem lpNorm_dilate_eq (φ : Plane → ℝ) (hφ : Integrable φ) {c : ℝ}
    (hc : 0 < c) :
    lpNorm (fun x : Plane => c * φ (Real.sqrt c • x)) 1 volume =
      lpNorm φ 1 volume := by
  rw [lpNorm_one_eq_integral_norm
      (integrable_dilate φ hφ hc).aestronglyMeasurable,
    lpNorm_one_eq_integral_norm hφ.aestronglyMeasurable]
  simpa only [Real.norm_eq_abs] using integral_abs_dilate_eq φ hφ hc

theorem tendsto_integral_abs_dilate (φ : Plane → ℝ) (hφ : Integrable φ)
    {c₀ : ℝ} (hc₀ : 0 < c₀) :
    Tendsto (fun c => ∫ x, |c * φ (Real.sqrt c • x) -
      c₀ * φ (Real.sqrt c₀ • x)|) (nhds c₀) (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  let η : ℝ := ε / 8
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨ψ, hψc, happrox, hψcont, hψmem⟩ :=
    (memLp_one_iff_integrable.2 hφ).exists_hasCompactSupport_eLpNorm_sub_le
      (ε := ENNReal.ofReal η) ENNReal.one_ne_top
      (ne_of_gt (ENNReal.ofReal_pos.mpr hη))
  have hψint : Integrable ψ := memLp_one_iff_integrable.mp hψmem
  have hφψint : Integrable (fun x : Plane => φ x - ψ x) := hφ.sub hψint
  have happroxReal := ENNReal.toReal_mono (by simp) happrox
  have happroxLp : lpNorm (fun x : Plane => φ x - ψ x) 1 volume ≤ η := by
    rw [MeasureTheory.toReal_eLpNorm] at happroxReal
    change lpNorm (φ - ψ) 1 volume ≤ η
    simpa only [ENNReal.toReal_ofReal hη.le] using happroxReal
  have happroxRev : lpNorm (fun x : Plane => ψ x - φ x) 1 volume ≤ η := by
    have heq : (fun x : Plane => ψ x - φ x) = -(fun x => φ x - ψ x) := by
      funext x
      simp only [Pi.neg_apply]
      ring
    rw [heq, lpNorm_neg]
    exact happroxLp
  have happroxLp' : lpNorm (φ - ψ) 1 volume ≤ η := by
    change lpNorm (fun x : Plane => φ x - ψ x) 1 volume ≤ η
    exact happroxLp
  have happroxRev' : lpNorm (ψ - φ) 1 volume ≤ η := by
    change lpNorm (fun x : Plane => ψ x - φ x) 1 volume ≤ η
    exact happroxRev
  have hψevent : ∀ᶠ c in nhds c₀,
      (∫ x, |c * ψ (Real.sqrt c • x) - c₀ * ψ (Real.sqrt c₀ • x)|) < ε / 2 :=
    (tendsto_integral_abs_compact_dilate ψ hψcont hψc hc₀).eventually
      (Iio_mem_nhds (by linarith))
  have hcEvent : ∀ᶠ c in nhds c₀, 0 < c := Ioi_mem_nhds hc₀
  filter_upwards [hψevent, hcEvent] with c hψsmall hc
  have hφc : Integrable (fun x : Plane => c * φ (Real.sqrt c • x)) :=
    integrable_dilate φ hφ hc
  have hψc' : Integrable (fun x : Plane => c * ψ (Real.sqrt c • x)) :=
    integrable_dilate ψ hψint hc
  have hφc₀ : Integrable (fun x : Plane => c₀ * φ (Real.sqrt c₀ • x)) :=
    integrable_dilate φ hφ hc₀
  have hψc₀ : Integrable (fun x : Plane => c₀ * ψ (Real.sqrt c₀ • x)) :=
    integrable_dilate ψ hψint hc₀
  have hmemφc : MemLp (fun x : Plane => c * φ (Real.sqrt c • x)) 1 volume :=
    memLp_one_iff_integrable.mpr hφc
  have hmemψc : MemLp (fun x : Plane => c * ψ (Real.sqrt c • x)) 1 volume :=
    memLp_one_iff_integrable.mpr hψc'
  have hmemψc₀ : MemLp (fun x : Plane => c₀ * ψ (Real.sqrt c₀ • x)) 1 volume :=
    memLp_one_iff_integrable.mpr hψc₀
  have htri₁ : lpNorm (fun x : Plane =>
      c * φ (Real.sqrt c • x) - c₀ * φ (Real.sqrt c₀ • x)) 1 volume ≤
      lpNorm (fun x : Plane => c * φ (Real.sqrt c • x) - c * ψ (Real.sqrt c • x)) 1 volume +
        lpNorm (fun x : Plane => c * ψ (Real.sqrt c • x) -
          c₀ * φ (Real.sqrt c₀ • x)) 1 volume :=
    lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub hmemφc hmemψc
      (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have htri₂ : lpNorm (fun x : Plane =>
      c * ψ (Real.sqrt c • x) - c₀ * φ (Real.sqrt c₀ • x)) 1 volume ≤
      lpNorm (fun x : Plane => c * ψ (Real.sqrt c • x) -
          c₀ * ψ (Real.sqrt c₀ • x)) 1 volume +
        lpNorm (fun x : Plane => c₀ * ψ (Real.sqrt c₀ • x) -
          c₀ * φ (Real.sqrt c₀ • x)) 1 volume :=
    lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub hmemψc hmemψc₀
      (by norm_num : (1 : ℝ≥0∞) ≤ 1)
  have hψdistInt : Integrable (fun x : Plane =>
      c * ψ (Real.sqrt c • x) - c₀ * ψ (Real.sqrt c₀ • x)) := hψc'.sub hψc₀
  have hψdist : lpNorm (fun x : Plane =>
      c * ψ (Real.sqrt c • x) - c₀ * ψ (Real.sqrt c₀ • x)) 1 volume < ε / 2 := by
    rw [lpNorm_one_eq_integral_norm hψdistInt.aestronglyMeasurable]
    simpa only [Real.norm_eq_abs] using hψsmall
  have hfirst : lpNorm (fun x : Plane =>
      c * φ (Real.sqrt c • x) - c * ψ (Real.sqrt c • x)) 1 volume =
      lpNorm (fun x : Plane => c * (φ - ψ) (Real.sqrt c • x)) 1 volume := by
    congr 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have hlast : lpNorm (fun x : Plane =>
      c₀ * ψ (Real.sqrt c₀ • x) - c₀ * φ (Real.sqrt c₀ • x)) 1 volume =
      lpNorm (fun x : Plane => c₀ * (ψ - φ) (Real.sqrt c₀ • x)) 1 volume := by
    congr 1
    funext x
    simp only [Pi.sub_apply]
    ring
  have htriangle : lpNorm (fun x : Plane =>
      c * φ (Real.sqrt c • x) - c₀ * φ (Real.sqrt c₀ • x)) 1 volume ≤
      lpNorm (fun x : Plane => c * φ (Real.sqrt c • x) - c * ψ (Real.sqrt c • x)) 1 volume +
        lpNorm (fun x : Plane => c * ψ (Real.sqrt c • x) - c₀ * ψ (Real.sqrt c₀ • x)) 1 volume +
        lpNorm (fun x : Plane => c₀ * ψ (Real.sqrt c₀ • x) - c₀ * φ (Real.sqrt c₀ • x)) 1 volume := by
    calc
      _ ≤ lpNorm (fun x : Plane => c * φ (Real.sqrt c • x) - c * ψ (Real.sqrt c • x)) 1 volume +
          lpNorm (fun x : Plane => c * ψ (Real.sqrt c • x) - c₀ * φ (Real.sqrt c₀ • x)) 1 volume := htri₁
      _ ≤ _ := by linarith [htri₂]
  have hfirstBound : lpNorm (fun x : Plane =>
      c * φ (Real.sqrt c • x) - c * ψ (Real.sqrt c • x)) 1 volume ≤ η := by
    rw [hfirst, lpNorm_dilate_eq (φ - ψ) hφψint hc]
    exact happroxLp'
  have hlastBound : lpNorm (fun x : Plane =>
      c₀ * ψ (Real.sqrt c₀ • x) - c₀ * φ (Real.sqrt c₀ • x)) 1 volume ≤ η := by
    rw [hlast, lpNorm_dilate_eq (ψ - φ) (hψint.sub hφ) hc₀]
    exact happroxRev'
  have hbound : lpNorm (fun x : Plane =>
      c * φ (Real.sqrt c • x) - c₀ * φ (Real.sqrt c₀ • x)) 1 volume < ε := by
    calc
      _ ≤ η + ε / 2 + η := by linarith [htriangle, hfirstBound, hψdist, hlastBound]
      _ < ε := by dsimp [η]; linarith
  have htargetInt : Integrable (fun x : Plane =>
      c * φ (Real.sqrt c • x) - c₀ * φ (Real.sqrt c₀ • x)) := hφc.sub hφc₀
  rw [lpNorm_one_eq_integral_norm htargetInt.aestronglyMeasurable] at hbound
  have hnonneg : 0 ≤ ∫ x : Plane,
      |c * φ (Real.sqrt c • x) - c₀ * φ (Real.sqrt c₀ • x)| :=
    integral_nonneg (fun x => abs_nonneg _)
  have hbound' : (∫ x : Plane,
      |c * φ (Real.sqrt c • x) - c₀ * φ (Real.sqrt c₀ • x)|) < ε := by
    simpa only [Real.norm_eq_abs] using hbound
  simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound'

end Critical2DKPZ.Smoothing

end
