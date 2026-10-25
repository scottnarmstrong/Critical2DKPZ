/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.OnePoint.Annealing
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.OnePoint.BlockMomentAndTiltedRatioBounds
public import Critical2DKPZ.Polymer.Locality
public import Critical2DKPZ.Definitions.EvenCeil
public import Critical2DKPZ.PolymerCalculus.Clocks
public import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-! # Moment comparison and auxiliary statements -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ProbabilityTheory

namespace Critical2DKPZ.OnePoint

/-- Jensen's reciprocal inequality for a normalized smoothed polymer mass. -/
theorem one_le_integral_inv_smoothedP2Plane (β : ℝ) (s n : ℕ) (x : Site) :
    1 ≤ ∫ ω, (smoothedP2Plane β s n x ω)⁻¹ ∂disorderLaw := by
  let Z : Disorder → ℝ := smoothedP2Plane β s n x
  have hZpos (ω : Disorder) : 0 < Z ω := Polymer.smoothedP2Plane_pos β s n x ω
  have hmean : ∫ ω, Z ω ∂disorderLaw = 1 := by
    dsimp [Z]
    exact Polymer.integral_smoothedP2Plane β s n x
  have hZint : Integrable Z disorderLaw := integrable_of_integral_eq_one hmean
  have hInvPow : Integrable (fun ω => Z ω ^ (-1 : ℝ)) disorderLaw := by
    simpa [Z] using integrable_rpow_smoothedP2Plane β s n x (-1)
  have hInvEq : (fun ω => (Z ω)⁻¹) = fun ω => Z ω ^ (-1 : ℝ) := by
    funext ω
    rw [Real.rpow_neg_one]
  have hInvInt : Integrable (fun ω => (Z ω)⁻¹) disorderLaw := hInvEq.symm ▸ hInvPow
  have hlinearInt : Integrable (fun ω => 2 - Z ω) disorderLaw :=
    (integrable_const (2 : ℝ)).sub hZint
  have hpoint (ω : Disorder) : 2 - Z ω ≤ (Z ω)⁻¹ := by
    have hsquare : 0 ≤ (Z ω - 1) ^ 2 / Z ω :=
      div_nonneg (sq_nonneg _) (le_of_lt (hZpos ω))
    have halgebra : (Z ω - 1) ^ 2 / Z ω = Z ω + (Z ω)⁻¹ - 2 := by
      field_simp [ne_of_gt (hZpos ω)]
      ring
    rw [halgebra] at hsquare
    linarith
  have hmono := integral_mono hlinearInt hInvInt hpoint
  have hlinear : ∫ ω, (2 - Z ω) ∂disorderLaw = 1 := by
    rw [integral_sub (integrable_const (2 : ℝ)) hZint, hmean]
    norm_num
  calc
    1 = ∫ ω, (2 - Z ω) ∂disorderLaw := hlinear.symm
    _ ≤ ∫ ω, (Z ω)⁻¹ ∂disorderLaw := hmono
    _ = ∫ ω, (smoothedP2Plane β s n x ω)⁻¹ ∂disorderLaw := by rfl

/-- Translating the starting point translates the set of reachable endpoints. -/
theorem endpoints_translate (s : ℕ) (x : Site) :
    Polymer.endpoints x s = (Polymer.endpoints 0 s).image (fun z => z + x) := by
  classical
  ext y
  simp only [Finset.mem_image]
  constructor
  · intro hy
    obtain ⟨p, hp⟩ := (Polymer.mem_endpoints_iff x y s).mp hy
    refine ⟨Critical2DKPZ.walkPosition 0 p s, ?_, ?_⟩
    · exact (Polymer.mem_endpoints_iff 0 (Critical2DKPZ.walkPosition 0 p s) s).mpr ⟨p, rfl⟩
    · calc
        Critical2DKPZ.walkPosition 0 p s + x = Critical2DKPZ.walkPosition (0 + x) p s :=
          (Polymer.walkPosition_translate 0 x p s).symm
        _ = y := by simpa only [zero_add] using hp
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨p, hp⟩ := (Polymer.mem_endpoints_iff 0 z s).mp hz
    apply (Polymer.mem_endpoints_iff x (z + x) s).mpr
    refine ⟨p, ?_⟩
    calc
      Critical2DKPZ.walkPosition x p s = Critical2DKPZ.walkPosition (0 + x) p s := by rw [zero_add]
      _ = Critical2DKPZ.walkPosition 0 p s + x := Polymer.walkPosition_translate 0 x p s
      _ = z + x := by rw [hp]

/-- The smoothed profile is a spatial translate in the disorder environment. -/
theorem smoothedP2Plane_translate_env (β : ℝ) (s n : ℕ) (x : Site)
    (ω : Disorder) :
    smoothedP2Plane β s n x ω =
      smoothedP2Plane β s n 0 (fun p => ω (p.1, p.2 + x)) := by
  classical
  let τ : Disorder := fun p => ω (p.1, p.2 + x)
  rw [Polymer.smoothedP2Plane_eq_sum β s n x ω,
    Polymer.smoothedP2Plane_eq_sum β s n 0 τ, endpoints_translate]
  have hinj : Set.InjOn (fun z : Site => z + x) (Polymer.endpoints 0 s) := by
    intro z hz w hw hzw
    apply add_left_injective x
    simpa [add_comm] using hzw
  rw [Finset.sum_image (s := Polymer.endpoints 0 s) (g := fun z : Site => z + x)
    (f := fun y => srwKernel s (y - x) * pointToPlane β s (n - s) y ω) hinj]
  apply Finset.sum_congr rfl
  intro z hz
  have hP : pointToPlane β s (n - s) (z + x) ω =
      pointToPlane β s (n - s) z τ := by
    simpa [τ] using Polymer.pointToPlane_translate β s (n - s) z x ω
  rw [hP]
  simp only [add_sub_cancel_right, sub_zero]

/-- Translation invariance of both smoothed moments and the logarithmic Gaussianity defect. -/
theorem smoothedP2Plane_moments_translate (β : ℝ) (s n : ℕ) (x : Site) :
    (∫ ω, smoothedP2Plane β s n x ω ^ 2 ∂disorderLaw) =
        ∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw ∧
    (∫ ω, (smoothedP2Plane β s n x ω)⁻¹ ∂disorderLaw) =
        ∫ ω, (smoothedP2Plane β s n 0 ω)⁻¹ ∂disorderLaw ∧
    gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane β s n x ω)) =
        gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane β s n 0 ω)) := by
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x)
  let τeq : Disorder ≃ᵐ Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ)
      (Gaussian.spatialTranslation x).symm
  have hτeq : τ = τeq := by
    funext ω p
    simp [τ, τeq, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
      Gaussian.spatialTranslation]
  have hτmeas : MeasurableEmbedding τ := hτeq ▸ τeq.measurableEmbedding
  have hMP := Gaussian.measurePreserving_disorder_translation x
  have hZ (ω : Disorder) : smoothedP2Plane β s n x ω = smoothedP2Plane β s n 0 (τ ω) := by
    exact smoothedP2Plane_translate_env β s n x ω
  have hZmeas : Measurable (smoothedP2Plane β s n 0) :=
    Polymer.measurable_smoothedP2Plane β s n 0
  have hFmeas : Measurable (fun ω => Real.log (smoothedP2Plane β s n 0 ω)) :=
    Real.measurable_log.comp hZmeas
  have hmeanF :
      (∫ ω, Real.log (smoothedP2Plane β s n x ω) ∂disorderLaw) =
        ∫ ω, Real.log (smoothedP2Plane β s n 0 ω) ∂disorderLaw := by
    calc
      _ = ∫ ω, Real.log (smoothedP2Plane β s n 0 (τ ω)) ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hZ]
      _ = _ := hMP.integral_comp hτmeas (fun ω => Real.log (smoothedP2Plane β s n 0 ω))
  have hVarF :
      Var[fun ω => Real.log (smoothedP2Plane β s n x ω); disorderLaw] =
        Var[fun ω => Real.log (smoothedP2Plane β s n 0 ω); disorderLaw] := by
    have hVarX := ProbabilityTheory.variance_eq_integral
      (X := fun ω => Real.log (smoothedP2Plane β s n x ω)) (μ := disorderLaw)
      ((Real.measurable_log.comp
        (Polymer.measurable_smoothedP2Plane β s n x)).aemeasurable)
    have hVar0 := ProbabilityTheory.variance_eq_integral
      (X := fun ω => Real.log (smoothedP2Plane β s n 0 ω)) (μ := disorderLaw)
      hFmeas.aemeasurable
    rw [hVarX, hVar0, hmeanF]
    calc
      _ = ∫ ω, (Real.log (smoothedP2Plane β s n 0 (τ ω)) -
          ∫ ω, Real.log (smoothedP2Plane β s n 0 ω) ∂disorderLaw) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hZ]
      _ = _ := hMP.integral_comp hτmeas (fun ω =>
        (Real.log (smoothedP2Plane β s n 0 ω) -
          ∫ ω', Real.log (smoothedP2Plane β s n 0 ω') ∂disorderLaw) ^ 2)
  constructor
  · calc
      _ = ∫ ω, smoothedP2Plane β s n 0 (τ ω) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hZ]
      _ = _ := hMP.integral_comp hτmeas (fun ω => smoothedP2Plane β s n 0 ω ^ 2)
  constructor
  · calc
      _ = ∫ ω, (smoothedP2Plane β s n 0 (τ ω))⁻¹ ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hZ]
      _ = _ := hMP.integral_comp hτmeas (fun ω => (smoothedP2Plane β s n 0 ω)⁻¹)
  · unfold gaussianityDefect
    rw [hmeanF, hVarF]

/-- Assuming the small-time origin bound, the second-to-reciprocal moment ratio satisfies the small-time estimate of Proposition 4.1(2). -/
theorem prop_VD_part2_of (A : ℝ) (hsmall : SmallTimeOriginBound A) :
    ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ o : ℕ → ℝ, Tendsto o atTop (nhds 0) ∧ ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
        ∀ (x : Site) (s : ℕ), Even s → s ≤ evenCeil (Real.sqrt δ * N) →
          Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s
              (evenCeil (Real.sqrt δ * N)) x ω ^ 2 ∂disorderLaw) /
            ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s
              (evenCeil (Real.sqrt δ * N)) x ω)⁻¹ ∂disorderLaw) ≤
            C / |Real.log δ| ^ ((1 : ℝ) / 4) + o N := by
  obtain ⟨δ₀, C, hδ₀pos, hδ₀lt, hsmall'⟩ := hsmall
  refine ⟨δ₀, C, hδ₀pos, hδ₀lt, fun δ hδ hδle => ?_⟩
  obtain ⟨o, ho, hN⟩ := hsmall' δ hδ hδle
  refine ⟨o, ho, ?_⟩
  filter_upwards [hN] with N hN
  intro ϑ hϑ x s hs hsn
  have h0 := hN ϑ hϑ s hs hsn
  have htranslate := smoothedP2Plane_moments_translate (criticalBeta ϑ N) s
    (evenCeil (Real.sqrt δ * N)) x
  rcases htranslate with ⟨hmoment, hinverse, _⟩
  rw [hmoment, hinverse]
  exact h0

/-- The smoothed second moment is logarithmically bounded above on a macroscopic time interval. -/
theorem smoothedP2Plane_secondMoment_le_log (A T₀ T₁ : ℝ) (hT₀ : 0 < T₀) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ s n : ℕ, s ≤ n → T₀ * N ≤ n →
      (n : ℝ) ≤ T₁ * N →
        ∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n 0 ω ^ 2 ∂disorderLaw ≤
          C * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := by
  obtain ⟨C₀, hC₀⟩ := smoothedP2Plane_secondMoment_le_uniform A T₁
  obtain ⟨D, hD⟩ := replicaOverlap_sub_log_bounded
  have hDnonneg : 0 ≤ D := by
    have h := hD 0 0 (by omega)
    simpa using h
  let Tplus : ℝ := max T₁ 1
  let d₀ : ℝ := Real.log (1 + 1 / Tplus)
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    apply Real.log_pos
    have hTplus : 0 < Tplus := by dsimp [Tplus]; positivity
    have hrecip : 0 < 1 / Tplus := one_div_pos.mpr hTplus
    linarith
  let C : ℝ := 1 + |C₀| * (1 + |D|) / (Real.pi * d₀)
  refine ⟨C, ?_⟩
  filter_upwards [hC₀, eventually_ge_atTop 1] with N hN hN1
  intro ϑ hϑ s n hsn hT₀N hnT₁
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnpos : 0 < (n : ℝ) :=
    lt_of_lt_of_le (mul_pos hT₀ hNpos) hT₀N
  have hn1 : 1 ≤ n := by exact_mod_cast hnpos
  have hsecond := hN ϑ hϑ s n hsn hn1 hnT₁
  have hRnonneg : 0 ≤ replicaOverlap n - replicaOverlap s := by
    rw [replicaOverlap_sub_eq_sum s n hsn]
    exact Finset.sum_nonneg fun r hr => Critical2DKPZ.srwKernel_nonneg (2 * r) 0
  have hmaxn : max n 1 = n := max_eq_left (by omega)
  have hdenPos : 0 < Real.log (1 + (N : ℝ) / n) := by
    apply Real.log_pos
    have hratio : 0 < (N : ℝ) / n := div_pos hNpos hnpos
    linarith
  have hTplusPos : 0 < Tplus := by dsimp [Tplus]; positivity
  have hnTplus : (n : ℝ) ≤ Tplus * N := by
    exact le_trans hnT₁
      (mul_le_mul_of_nonneg_right (le_max_left T₁ 1) hNpos.le)
  have hNdiv : 1 / Tplus ≤ (N : ℝ) / n := by
    rw [div_le_div_iff₀ hTplusPos hnpos]
    nlinarith [hnTplus]
  have hd₀le : d₀ ≤ Real.log (1 + (N : ℝ) / n) := by
    dsimp [d₀]
    apply Real.log_le_log
    · positivity
    · linarith
  have hlogRatioNonneg : 0 ≤ Real.log ((n : ℝ) / (max s 1 : ℕ)) := by
    apply Real.log_nonneg
    apply (one_le_div (by exact_mod_cast (show 0 < max s 1 by omega))).2
    exact_mod_cast (show max s 1 ≤ n by omega)
  have hOverlap := hD s n hsn
  rw [hmaxn] at hOverlap
  have hRupper : replicaOverlap n - replicaOverlap s ≤
      (Real.log ((n : ℝ) / (max s 1 : ℕ)) + |D|) / Real.pi := by
    have htop := (abs_le.mp hOverlap).2
    have hpi : Real.pi * (replicaOverlap n - replicaOverlap s) ≤
        Real.log ((n : ℝ) / (max s 1 : ℕ)) + |D| := by
      have hDabs : D ≤ |D| := le_abs_self _
      linarith
    apply (le_div_iff₀ Real.pi_pos).2
    simpa only [mul_comm] using hpi
  have hfactor : 0 ≤ (replicaOverlap n - replicaOverlap s) /
      Real.log (1 + (N : ℝ) / n) := div_nonneg hRnonneg hdenPos.le
  have hC₀term : C₀ * (replicaOverlap n - replicaOverlap s) /
      Real.log (1 + (N : ℝ) / n) ≤
        |C₀| * (replicaOverlap n - replicaOverlap s) /
          Real.log (1 + (N : ℝ) / n) :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self C₀) hRnonneg) hdenPos.le
  have hterm : |C₀| * (replicaOverlap n - replicaOverlap s) /
      Real.log (1 + (N : ℝ) / n) ≤
        |C₀| * (Real.log ((n : ℝ) / (max s 1 : ℕ)) + |D|) /
          (Real.pi * d₀) := by
    have hinv : 1 / Real.log (1 + (N : ℝ) / n) ≤ 1 / d₀ :=
      one_div_le_one_div_of_le hd₀ hd₀le
    calc
      _ = |C₀| * (replicaOverlap n - replicaOverlap s) *
          (1 / Real.log (1 + (N : ℝ) / n)) := by ring
      _ ≤ |C₀| * (replicaOverlap n - replicaOverlap s) * (1 / d₀) :=
        mul_le_mul_of_nonneg_left hinv (mul_nonneg (abs_nonneg _) hRnonneg)
      _ ≤ |C₀| * ((Real.log ((n : ℝ) / (max s 1 : ℕ)) + |D|) / Real.pi) *
          (1 / d₀) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hRupper (abs_nonneg _)
        · positivity
      _ = _ := by ring
  have hLbound : Real.log ((n : ℝ) / (max s 1 : ℕ)) + |D| ≤
      (1 + |D|) * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := by
    have hL := hlogRatioNonneg
    have hDabs : 0 ≤ |D| := abs_nonneg D
    nlinarith
  have hfinal := calc
      (∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n 0 ω ^ 2 ∂disorderLaw) ≤
          1 + C₀ * (replicaOverlap n - replicaOverlap s) /
            Real.log (1 + (N : ℝ) / n) := hsecond
      _ ≤ 1 + |C₀| * (replicaOverlap n - replicaOverlap s) /
            Real.log (1 + (N : ℝ) / n) := by linarith [hC₀term]
      _ ≤ 1 + |C₀| * (Real.log ((n : ℝ) / (max s 1 : ℕ)) + |D|) /
            (Real.pi * d₀) := by linarith [hterm]
      _ ≤ C * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := by
        dsimp [C]
        have hcoef : 0 ≤ |C₀| / (Real.pi * d₀) := by positivity
        have hmul : |C₀| * (Real.log ((n : ℝ) / (max s 1 : ℕ)) + |D|) /
            (Real.pi * d₀) ≤
            (|C₀| * (1 + |D|) / (Real.pi * d₀)) *
              (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := by
          calc
            _ = (|C₀| / (Real.pi * d₀)) *
                (Real.log ((n : ℝ) / (max s 1 : ℕ)) + |D|) := by ring
            _ ≤ (|C₀| / (Real.pi * d₀)) *
                ((1 + |D|) * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ)))) :=
                  mul_le_mul_of_nonneg_left hLbound hcoef
            _ = _ := by ring
        nlinarith [hmul, hlogRatioNonneg]
  exact hfinal

private theorem one_le_integral_smoothedP2Plane_sq (β : ℝ) (s n : ℕ) (x : Site) :
    1 ≤ ∫ ω, smoothedP2Plane β s n x ω ^ 2 ∂disorderLaw := by
  have hmem : MemLp (smoothedP2Plane β s n x) 2 disorderLaw :=
    Polymer.memLp_smoothedP2Plane β s n x 2 (by norm_num)
  have hv := ProbabilityTheory.variance_nonneg
    (smoothedP2Plane β s n x) disorderLaw
  rw [ProbabilityTheory.variance_eq_sub hmem,
    Polymer.integral_smoothedP2Plane] at hv
  norm_num at hv
  linarith

private theorem renewal_ratio_lower_of_error (G E R M : ℝ)
    (hGpos : 0 < G) (hE : 0 ≤ E) (hR : 0 ≤ R)
    (hGge1 : 1 ≤ G) (hGge2E : 2 * E ≤ G)
    (hGgeSlope : 2 * E / Real.pi ≤ G)
    (herr : 1 + (Real.pi / G) * R - M ≤ E * (1 + R) / G ^ 2) :
    1 / 2 + Real.pi * R / (2 * G) ≤ M := by
  have hGsq : 2 * E ≤ G ^ 2 := by
    calc
      2 * E = 1 * (2 * E) := by ring
      _ ≤ G * (2 * E) := mul_le_mul_of_nonneg_right hGge1
        (mul_nonneg (by norm_num) hE)
      _ ≤ G * G := mul_le_mul_of_nonneg_left hGge2E hGpos.le
      _ = G ^ 2 := by ring
  have hEover : E / G ^ 2 ≤ (1 : ℝ) / 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hGpos)]
    linarith only [hGsq]
  have hpiG : 2 * E ≤ Real.pi * G := by
    have h := (div_le_iff₀ Real.pi_pos).mp hGgeSlope
    nlinarith only [h]
  have hEslope : E / G ^ 2 ≤ Real.pi / (2 * G) := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hGpos)
      (mul_pos (by norm_num) hGpos)]
    have hprod := mul_le_mul_of_nonneg_right hpiG hGpos.le
    nlinarith only [hprod]
  have hsplit : E * (1 + R) / G ^ 2 = E / G ^ 2 + (E / G ^ 2) * R := by
    field_simp
  have hRterm : (E / G ^ 2) * R ≤ (Real.pi / (2 * G)) * R :=
    mul_le_mul_of_nonneg_right hEslope hR
  have herr' : 1 + (Real.pi / G) * R - M ≤
      1 / 2 + Real.pi * R / (2 * G) := by
    rw [hsplit] at herr
    calc
      _ ≤ E / G ^ 2 + (E / G ^ 2) * R := herr
      _ ≤ 1 / 2 + (Real.pi / (2 * G)) * R := add_le_add hEover hRterm
      _ = _ := by ring
  have hratioId :
      1 + (Real.pi / G) * R - (1 / 2 + Real.pi * R / (2 * G)) =
        1 / 2 + Real.pi * R / (2 * G) := by
    field_simp [ne_of_gt hGpos]
    ring
  linarith only [herr', hratioId]

/-- The smoothed second moment has a logarithmic lower bound at the small-time cutoff. The end
time is `evenCeil (√δ N)`; `n` enters only through the comparison scale `log (n / max s 1)`. -/
theorem smoothedP2Plane_secondMoment_ge_log (A T₀ T₁ : ℝ) (hT₀ : 0 < T₀)
    (hT : T₀ < T₁) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ Real.sqrt δ₁ < T₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₁ → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ s n : ℕ,
        s ≤ evenCeil (Real.sqrt δ * N) → T₀ * N ≤ n → (n : ℝ) ≤ T₁ * N →
          c * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) ≤
            ∫ ω, smoothedP2Plane (criticalBeta ϑ N) s
              (evenCeil (Real.sqrt δ * N)) 0 ω ^ 2 ∂disorderLaw := by
  obtain ⟨Cerr, hrenewal⟩ := smoothedP2Plane_secondMoment_renewalGap
  obtain ⟨Cgap, hgap⟩ := renewalGap_criticalBeta_sub_log_bounded A
  obtain ⟨D, hD⟩ := replicaOverlap_sub_log_bounded
  let E : ℝ := |Cerr|
  let Cg : ℝ := |Cgap|
  let Da : ℝ := |D|
  let G₀ : ℝ := 1 + 2 * E + 2 * E / Real.pi
  let B : ℝ := 2 * (G₀ + Real.log 2 + Cg + 1)
  have hE : 0 ≤ E := abs_nonneg Cerr
  have hCg : 0 ≤ Cg := abs_nonneg Cgap
  have hDa : 0 ≤ Da := abs_nonneg D
  have hG₀ : 0 < G₀ := by dsimp [G₀]; positivity
  have hB : 0 < B := by
    dsimp [B]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  let δ₁ : ℝ := min (1 / 2) (min (T₀ ^ 2 / 4) (Real.exp (-B)))
  have hδ₁ : 0 < δ₁ := by
    dsimp [δ₁]
    have hT : 0 < T₀ ^ 2 / 4 := by positivity
    have hexp : 0 < Real.exp (-B) := Real.exp_pos _
    positivity
  have hδ₁sqrt : Real.sqrt δ₁ < T₀ := by
    have hδ₁T : δ₁ ≤ T₀ ^ 2 / 4 := by
      dsimp [δ₁]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hroot : Real.sqrt δ₁ ≤ T₀ / 2 := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · nlinarith
    linarith
  refine ⟨δ₁, hδ₁, hδ₁sqrt, ?_⟩
  intro δ hδ hδle
  let q : ℝ := Real.sqrt δ
  let H : ℝ := |Real.log δ|
  have hq : 0 < q := by dsimp [q]; exact Real.sqrt_pos.2 hδ
  have hqT : q < T₀ := by
    dsimp [q]
    apply lt_of_le_of_lt (Real.sqrt_le_sqrt hδle) hδ₁sqrt
  have hδlehalf : δ ≤ (1 / 2 : ℝ) := by
    exact le_trans hδle (min_le_left _ _)
  have hqone : q < 1 := by
    have hqbound : q ≤ Real.sqrt (1 / 2 : ℝ) := by
      dsimp [q]
      exact Real.sqrt_le_sqrt hδlehalf
    have hsqrtHalf : Real.sqrt (1 / 2 : ℝ) < 1 := by
      apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
      norm_num
    exact lt_of_le_of_lt hqbound hsqrtHalf
  have hδlt : δ < 1 := by linarith
  have hlogδ : Real.log δ < 0 := by
    calc
      Real.log δ < Real.log 1 := Real.log_lt_log hδ (by linarith)
      _ = 0 := Real.log_one
  have hH : B ≤ H := by
    have hδexp : δ ≤ Real.exp (-B) := by
      exact le_trans hδle (le_trans (min_le_right _ _) (min_le_right _ _))
    have hlogbound : Real.log δ ≤ -B := by
      simpa only [Real.log_exp] using (Real.log_le_log hδ hδexp)
    dsimp [H]
    rw [abs_of_neg hlogδ]
    simpa only [neg_neg] using (neg_le_neg hlogbound)
  have hlogq : Real.log q = Real.log δ / 2 := by
    dsimp [q]
    exact Real.log_sqrt hδ.le
  have hlogInvq : Real.log q⁻¹ = H / 2 := by
    rw [Real.log_inv, hlogq]
    dsimp [H]
    rw [abs_of_neg hlogδ]
    ring
  have hqT1 : 0 < T₁ := by linarith
  have hTdiff : 0 < T₀ - q := by linarith
  have hqdiff : 0 < 1 - q := by linarith
  have hround1 : ∀ᶠ N : ℕ in atTop, 2 / q < (N : ℝ) :=
    (tendsto_natCast_atTop_atTop).eventually_gt_atTop (2 / q)
  have hround2 : ∀ᶠ N : ℕ in atTop, 2 / (1 - q) < (N : ℝ) :=
    (tendsto_natCast_atTop_atTop).eventually_gt_atTop (2 / (1 - q))
  have hround3 : ∀ᶠ N : ℕ in atTop, 2 / (T₀ - q) < (N : ℝ) :=
    (tendsto_natCast_atTop_atTop).eventually_gt_atTop (2 / (T₀ - q))
  have hlogN : ∀ᶠ N : ℕ in atTop, |A| < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |A|
  refine ⟨1 / (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q)), ?_, ?_⟩
  · have hK : 0 ≤ Real.log (T₁ / q) := by
      apply Real.log_nonneg
      rw [one_le_div hq]
      linarith
    positivity
  · filter_upwards [hgap, hround1, hround2, hround3, hlogN] with N hgapN hround1N hround2N hround3N hlogN
    intro ϑ hϑ s n hs nlow nhigh
    let n₀ : ℕ := evenCeil (q * N)
    let β : ℝ := criticalBeta ϑ N
    let G : ℝ := renewalGap β n₀
    let R : ℝ := replicaOverlap n₀ - replicaOverlap s
    let M : ℝ := ∫ ω, smoothedP2Plane β s n₀ 0 ω ^ 2 ∂disorderLaw
    have hNlarge1 : 2 < q * (N : ℝ) := by
      have hm := mul_lt_mul_of_pos_right hround1N hq
      have hcancel : (2 / q) * q = 2 := by field_simp [ne_of_gt hq]
      nlinarith only [hm, hcancel]
    have hNlarge2 : 2 < (1 - q) * (N : ℝ) := by
      have hm := mul_lt_mul_of_pos_right hround2N hqdiff
      have hcancel : (2 / (1 - q)) * (1 - q) = 2 := by field_simp [ne_of_gt hqdiff]
      nlinarith only [hm, hcancel]
    have hNlarge3 : 2 < (T₀ - q) * (N : ℝ) := by
      have hm := mul_lt_mul_of_pos_right hround3N hTdiff
      have hcancel : (2 / (T₀ - q)) * (T₀ - q) = 2 := by field_simp [ne_of_gt hTdiff]
      nlinarith only [hm, hcancel]
    have hn₀low : q * (N : ℝ) ≤ (n₀ : ℝ) := by
      dsimp [n₀, q]
      exact Critical2DKPZ.le_evenCeil _
    have hn₀high : (n₀ : ℝ) < q * (N : ℝ) + 2 := by
      dsimp [n₀, q]
      exact Critical2DKPZ.evenCeil_lt_add_two (by positivity)
    have hn₀two : (n₀ : ℝ) ≤ 2 * q * N := by
      have hqN : 2 ≤ q * (N : ℝ) := le_of_lt hNlarge1
      linarith only [hn₀high, hqN]
    have hn₀N : n₀ ≤ N := by
      have hn₀Nreal : (n₀ : ℝ) ≤ N := by
        linarith only [hn₀high, hNlarge2]
      exact_mod_cast hn₀Nreal
    have hn₀T : (n₀ : ℝ) ≤ T₀ * N := by
      linarith only [hn₀high, hNlarge3]
    have hn₀pos : 0 < n₀ := by
      exact_mod_cast (show (1 : ℝ) ≤ (n₀ : ℝ) by linarith only [hn₀low, hNlarge1])
    have hn₀one : 1 ≤ n₀ := hn₀pos
    have hsN₀ : s ≤ n₀ := by
      simpa [n₀, q] using hs
    have hn₀n : n₀ ≤ n := by
      exact_mod_cast (le_trans hn₀T nlow)
    have hA0 : 0 ≤ A := by linarith [hϑ.1, hϑ.2]
    have hθabs : |ϑ| ≤ |A| := by
      rw [abs_of_nonneg hA0]
      exact abs_le.mpr ⟨hϑ.1, hϑ.2⟩
    have hθlog : |ϑ| < Real.log (N : ℝ) := lt_of_le_of_lt hθabs hlogN
    have hNone : 1 ≤ N := by
      have hNpos : 0 < (N : ℝ) := by
        by_contra hN
        have hNle : (N : ℝ) ≤ 0 := le_of_not_gt hN
        have hprod : q * (N : ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq.le hNle
        linarith only [hNlarge1, hprod]
      exact_mod_cast hNpos
    have hβpos : 0 < β := by
      dsimp [β, criticalBeta]
      apply Real.sqrt_pos.2
      apply Real.log_pos
      have hσ := criticalSigmaSq_pos_of_abs_lt_log hNone hθlog
      linarith
    have hGapApprox := hgapN ϑ hϑ n₀ hn₀N
    have hlogNn₀low : Real.log (1 / (2 * q)) ≤ Real.log ((N : ℝ) / n₀) := by
      apply Real.log_le_log
      · positivity
      · have hn₀posR : 0 < (n₀ : ℝ) := by exact_mod_cast hn₀pos
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * q) hn₀posR]
        nlinarith only [hn₀two]
    have hlogNn₀high : Real.log ((N : ℝ) / n₀) ≤ Real.log q⁻¹ := by
      have hn₀posR : 0 < (n₀ : ℝ) := by exact_mod_cast hn₀pos
      have hratio : (N : ℝ) / n₀ ≤ q⁻¹ := by
        have hratio' : (N : ℝ) / n₀ ≤ (1 : ℝ) / q := by
          rw [div_le_div_iff₀ hn₀posR hq]
          nlinarith only [hn₀low]
        simpa only [one_div] using hratio'
      exact Real.log_le_log (by positivity) hratio
    have hlogLower : H / 2 - Real.log 2 ≤ Real.log ((N : ℝ) / n₀) := by
      have hlogId : Real.log (1 / (2 * q)) = H / 2 - Real.log 2 := by
        have hrecip : (1 : ℝ) / (2 * q) = (2 * q)⁻¹ := by ring
        rw [hrecip, Real.log_inv,
          Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hq), hlogq]
        dsimp [H]
        rw [abs_of_neg hlogδ]
        ring
      calc
        H / 2 - Real.log 2 = Real.log (1 / (2 * q)) := hlogId.symm
        _ ≤ Real.log ((N : ℝ) / n₀) := hlogNn₀low
    have hlogUpper : Real.log ((N : ℝ) / n₀) ≤ H / 2 := by
      rw [← hlogInvq]
      exact hlogNn₀high
    have hGapApprox' : |G - Real.log ((N : ℝ) / n₀)| ≤ Cg := by
      simpa [G, β, max_eq_left hn₀one] using
        (le_trans hGapApprox (le_abs_self Cgap))
    have hGlow : G₀ ≤ G := by
      have habs := abs_le.mp hGapApprox'
      have hH' : 2 * (G₀ + Real.log 2 + Cg + 1) ≤ H := by
        change B ≤ H at hH
        exact hH
      linarith only [hH', hlogLower, habs.1]
    have hGupper : G ≤ H / 2 + Cg := by
      have habs := abs_le.mp hGapApprox'
      linarith only [habs.2, hlogUpper]
    have hG0pos : 0 < G₀ := by dsimp [G₀]; positivity
    have hGpos : 0 < G := lt_of_lt_of_le hG0pos hGlow
    have hGformula : 1 + 2 * E + 2 * E / Real.pi ≤ G := by
      change G₀ ≤ G at hGlow
      exact hGlow
    have hEterm : 0 ≤ 2 * E := mul_nonneg (by norm_num) hE
    have hdivterm : 0 ≤ 2 * E / Real.pi := div_nonneg hEterm Real.pi_pos.le
    have hRnonneg : 0 ≤ R := by
      dsimp [R]
      rw [replicaOverlap_sub_eq_sum s n₀ hsN₀]
      exact Finset.sum_nonneg fun r hr => Critical2DKPZ.srwKernel_nonneg (2 * r) 0
    have hgapRatio : renewalGap β s / G = 1 + (Real.pi / G) * R := by
      have hgapDiff : renewalGap β s = G + Real.pi * R := by
        dsimp [G, R, renewalGap]
        ring
      rw [hgapDiff]
      field_simp [ne_of_gt hGpos]
    have hmoment := hrenewal β hβpos s n₀ hsN₀ hGpos
    have hGge1 : 1 ≤ G := by linarith only [hGformula, hEterm, hdivterm]
    have hGge2E : 2 * E ≤ G := by
      linarith only [hGformula, hdivterm]
    have hGgeSlope : 2 * E / Real.pi ≤ G := by
      linarith only [hGformula, hEterm]
    have hMlower : 1 / 2 + Real.pi * R / (2 * G) ≤ M := by
      have herror := hmoment.2.1
      have herror₀ :
          renewalGap β s / G - M ≤ Cerr * (1 + R) / G ^ 2 := by
        change renewalGap β s / renewalGap β n₀ -
          (∫ ω, smoothedP2Plane β s n₀ 0 ω ^ 2 ∂disorderLaw) ≤
          Cerr * (1 + (replicaOverlap n₀ - replicaOverlap s)) / renewalGap β n₀ ^ 2
        have hfactorEq : 1 + (replicaOverlap n₀ - replicaOverlap s) = 1 + replicaOverlap n₀ - replicaOverlap s := by ring
        rw [hfactorEq]
        exact herror
      have herror' :
          1 + (Real.pi / G) * R - M ≤ E * (1 + R) / G ^ 2 := by
        have hEbound : Cerr ≤ E := le_abs_self Cerr
        have hfactor : 0 ≤ 1 + R := add_nonneg (by norm_num) hRnonneg
        rw [hgapRatio] at herror₀
        calc
          _ ≤ Cerr * (1 + R) / G ^ 2 := herror₀
          _ ≤ E * (1 + R) / G ^ 2 := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hEbound hfactor) (sq_nonneg G)
      exact renewal_ratio_lower_of_error G E R M hGpos hE hRnonneg
        hGge1 hGge2E hGgeSlope herror'
    have hOverlap := hD s n₀ hsN₀
    have hOverlapLog : Real.log ((n₀ : ℝ) / (max s 1 : ℕ)) ≤ Real.pi * R + Da := by
      have hsmax : max n₀ 1 = n₀ := max_eq_left (by omega : 1 ≤ n₀)
      rw [hsmax] at hOverlap
      have hleft := (abs_le.mp hOverlap).1
      have hDle : D ≤ Da := le_abs_self D
      have hRdef : R = replicaOverlap n₀ - replicaOverlap s := rfl
      calc
        Real.log ((n₀ : ℝ) / (max s 1 : ℕ)) ≤
            Real.pi * (replicaOverlap n₀ - replicaOverlap s) + D := by
              linarith only [hleft]
        _ = D + Real.pi * (replicaOverlap n₀ - replicaOverlap s) := by ring
        _ ≤ Da + Real.pi * (replicaOverlap n₀ - replicaOverlap s) :=
              add_le_add_left hDle _
        _ = Real.pi * R + Da := by rw [hRdef]; ring
    have hRlog : Real.log ((n₀ : ℝ) / (max s 1 : ℕ)) ≤ 2 * G * M + Da := by
      have hprod : Real.pi * R ≤ 2 * G * M := by
        have h2Gnonneg : 0 ≤ 2 * G := mul_nonneg (by norm_num) hGpos.le
        have hmul := mul_le_mul_of_nonneg_left hMlower h2Gnonneg
        have hcancel : (2 * G) * (1 / 2 + Real.pi * R / (2 * G)) = G + Real.pi * R := by
          field_simp [ne_of_gt hGpos]
        rw [hcancel] at hmul
        linarith only [hmul, hGpos.le]
      calc
        _ ≤ Real.pi * R + Da := hOverlapLog
        _ ≤ 2 * G * M + Da := add_le_add hprod le_rfl
    have hratioN : (n : ℝ) / n₀ ≤ T₁ / q := by
      apply (div_le_div_iff₀ (by exact_mod_cast hn₀pos) hq).2
      calc
        (n : ℝ) * q = q * (n : ℝ) := by ring
        _ ≤ q * (T₁ * N) := mul_le_mul_of_nonneg_left nhigh hq.le
        _ = T₁ * (q * N) := by ring
        _ ≤ T₁ * n₀ := mul_le_mul_of_nonneg_left hn₀low hqT1.le
    have hnrealpos : 0 < (n : ℝ) :=
      lt_of_lt_of_le (mul_pos hT₀ (by exact_mod_cast hNone)) nlow
    have hn₀realpos : 0 < (n₀ : ℝ) := by exact_mod_cast hn₀pos
    have hlogratioN : Real.log ((n : ℝ) / n₀) ≤ Real.log (T₁ / q) := by
      exact Real.log_le_log (div_pos hnrealpos hn₀realpos) hratioN
    have hlogSplit :
        Real.log ((n : ℝ) / (max s 1 : ℕ)) =
          Real.log ((n : ℝ) / n₀) + Real.log ((n₀ : ℝ) / (max s 1 : ℕ)) := by
      have hposN : 0 < (n : ℝ) :=
        lt_of_lt_of_le (mul_pos hT₀ (by exact_mod_cast hNone)) nlow
      have hpos0 : 0 < (n₀ : ℝ) := by exact_mod_cast hn₀pos
      have hposs : 0 < ((max s 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < max s 1 by omega)
      rw [Real.log_div (ne_of_gt hposN) (ne_of_gt (by positivity : 0 < ((max s 1 : ℕ) : ℝ))),
        Real.log_div (ne_of_gt hposN) (ne_of_gt hpos0),
        Real.log_div (ne_of_gt hpos0) (ne_of_gt hposs)]
      ring
    have hMomentOne : 1 ≤ M := by
      dsimp [M]
      exact one_le_integral_smoothedP2Plane_sq β s n₀ 0
    have hfinal :
        (1 / (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q))) *
          (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) ≤ M := by
      have hL := calc
          1 + Real.log ((n : ℝ) / (max s 1 : ℕ))
              = 1 + Real.log ((n : ℝ) / n₀) +
                Real.log ((n₀ : ℝ) / (max s 1 : ℕ)) := by rw [hlogSplit]; ring
          _ ≤ 1 + Real.log (T₁ / q) + 2 * G * M + Da := by
            linarith only [hlogratioN, hRlog]
          _ ≤ (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q)) * M := by
            have hKnonneg : 0 ≤ Real.log (T₁ / q) := by
              apply Real.log_nonneg
              rw [one_le_div hq]
              linarith only [hT, hqT]
            have hcoefnonneg : 0 ≤ 1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q) := by
              have hHpos : 0 < H := lt_of_lt_of_le hB hH
              positivity
            have hGmul : 2 * G * M ≤ 2 * (H / 2 + Cg) * M := by
              have h2G : 2 * G ≤ 2 * (H / 2 + Cg) :=
                mul_le_mul_of_nonneg_left hGupper (by norm_num)
              exact mul_le_mul_of_nonneg_right h2G (by linarith only [hMomentOne])
            have hbase : 0 ≤ 1 + Real.log (T₁ / q) + Da := by positivity
            have hconst : 1 + Real.log (T₁ / q) + Da ≤
                (1 + Real.log (T₁ / q) + Da) * M :=
              calc
                _ = (1 + Real.log (T₁ / q) + Da) * 1 := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_left hMomentOne hbase
            calc
              1 + Real.log (T₁ / q) + 2 * G * M + Da =
                  (1 + Real.log (T₁ / q) + Da) + 2 * G * M := by ring
              _ ≤ (1 + Real.log (T₁ / q) + Da) * M +
                    2 * (H / 2 + Cg) * M := add_le_add hconst hGmul
              _ = (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q)) * M := by ring
      have hden : 0 < 1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q) := by
        have hlognonneg : 0 ≤ Real.log (T₁ / q) := by
          apply Real.log_nonneg
          rw [one_le_div hq]
          linarith
        positivity
      have hnum : 1 + Real.log ((n : ℝ) / (max s 1 : ℕ)) ≤
          M * (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q)) := by
        calc
          _ ≤ (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q)) * M := hL
          _ = M * (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q)) := by ring
      have hdiv :
          (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) /
            (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q)) ≤ M :=
        (div_le_iff₀ hden).2 hnum
      have hmul :
          (1 / (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q))) *
            (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) =
          (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) /
            (1 + 2 * (H / 2 + Cg) + Da + Real.log (T₁ / q)) := by
        field_simp [ne_of_gt hden]
      rw [hmul]
      exact hdiv
    exact hfinal

private theorem pointToPoint_resample_inside_block (β : ℝ) {s n₀ : ℕ}
    (hsn₀ : s ≤ n₀) (y z : Site) (ω ξ : Disorder) :
    Critical2DKPZ.pointToPoint β s (n₀ - s) y z
        (Gaussian.resample (Gaussian.timeBlock s n₀) ω ξ) =
      Critical2DKPZ.pointToPoint β s (n₀ - s) y z ω := by
  rw [Polymer.pointToPoint_eq_sum, Polymer.pointToPoint_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hweight : Polymer.pathWeight β s y p
      (Gaussian.resample (Gaussian.timeBlock s n₀) ω ξ) =
        Polymer.pathWeight β s y p ω := by
    unfold Polymer.pathWeight
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have htime : (s + j, Critical2DKPZ.walkPosition y p j) ∈ Gaussian.timeBlock s n₀ := by
      simp [Gaussian.timeBlock]
      constructor <;> omega
    simp [Gaussian.resample, htime]
  rw [hweight]

private theorem pointToPlane_resample_after_block (β : ℝ) {s n₀ n : ℕ}
    (z : Site) (ω ξ : Disorder) :
    Critical2DKPZ.pointToPlane β n₀ (n - n₀) z
        (Gaussian.resample (Gaussian.timeBlock s n₀) ω ξ) =
      Critical2DKPZ.pointToPlane β n₀ (n - n₀) z ξ := by
  rw [Polymer.pointToPlane_eq_sum, Polymer.pointToPlane_eq_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hweight : Polymer.pathWeight β n₀ z p
      (Gaussian.resample (Gaussian.timeBlock s n₀) ω ξ) =
        Polymer.pathWeight β n₀ z p ξ := by
    unfold Polymer.pathWeight
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have htime : (n₀ + j, Critical2DKPZ.walkPosition z p j) ∉ Gaussian.timeBlock s n₀ := by
      simp [Gaussian.timeBlock]
      omega
    simp [Gaussian.resample, htime]
  rw [hweight]

private theorem smoothed_resample_end_formula (β : ℝ) {s n₀ n : ℕ}
    (hsn₀ : s ≤ n₀) (hn₀n : n₀ ≤ n) (x : Site) (ω ξ : Disorder) :
    smoothedP2Plane β s n x (Gaussian.resample (Gaussian.timeBlock s n₀) ω ξ) =
      ∑ y ∈ Polymer.endpoints x s, srwKernel s (y - x) *
        ∑' z, Critical2DKPZ.pointToPoint β s (n₀ - s) y z ω *
          Critical2DKPZ.pointToPlane β n₀ (n - n₀) z ξ := by
  rw [Polymer.smoothedP2Plane_eq_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have hsplit : n - s = (n₀ - s) + (n - n₀) := by omega
  rw [hsplit, Polymer.pointToPlane_chapmanKolmogorov]
  have hstart : s + (n₀ - s) = n₀ := by omega
  rw [hstart]
  apply congrArg (fun v : ℝ => srwKernel s (y - x) * v)
  apply tsum_congr
  intro z
  rw [pointToPoint_resample_inside_block β hsn₀,
    pointToPlane_resample_after_block β]

private theorem integral_smoothed_resample_end (β : ℝ) {s n₀ n : ℕ}
    (hsn₀ : s ≤ n₀) (hn₀n : n₀ ≤ n) (x : Site) (ω : Disorder) :
    ∫ ξ, smoothedP2Plane β s n x
        (Gaussian.resample (Gaussian.timeBlock s n₀) ω ξ) ∂disorderLaw =
      smoothedP2Plane β s n₀ x ω := by
  simp_rw [smoothed_resample_end_formula β hsn₀ hn₀n x ω]
  let A := Polymer.endpoints x s
  let m := n₀ - s
  let l := n - n₀
  have hm : s + m = n₀ := by dsimp [m]; omega
  have hFint (y : Site) : Integrable
      (fun ξ => ∑' z, Critical2DKPZ.pointToPoint β s m y z ω *
        Critical2DKPZ.pointToPlane β n₀ l z ξ) disorderLaw := by
    have hEq : (fun ξ => ∑' z, Critical2DKPZ.pointToPoint β s m y z ω *
        Critical2DKPZ.pointToPlane β n₀ l z ξ) =
        fun ξ => ∑ z ∈ Polymer.endpoints y m,
          Critical2DKPZ.pointToPoint β s m y z ω * Critical2DKPZ.pointToPlane β n₀ l z ξ := by
      funext ξ
      exact Polymer.tsum_pointToPoint_mul_eq_sum β s m y
        (fun z => Critical2DKPZ.pointToPlane β n₀ l z ξ) ω
    rw [hEq]
    exact integrable_finsetSum _ fun z _ =>
      (memLp_one_iff_integrable.mp
        (Polymer.memLp_pointToPlane β n₀ l z 1 (by norm_num))).const_mul _
  have hFmean (y : Site) :
      ∫ ξ, (∑' z, Critical2DKPZ.pointToPoint β s m y z ω *
        Critical2DKPZ.pointToPlane β n₀ l z ξ) ∂disorderLaw =
        Critical2DKPZ.pointToPlane β s m y ω := by
    have hEq : (fun ξ => ∑' z, Critical2DKPZ.pointToPoint β s m y z ω *
        Critical2DKPZ.pointToPlane β n₀ l z ξ) =
        fun ξ => ∑ z ∈ Polymer.endpoints y m,
          Critical2DKPZ.pointToPoint β s m y z ω * Critical2DKPZ.pointToPlane β n₀ l z ξ := by
      funext ξ
      exact Polymer.tsum_pointToPoint_mul_eq_sum β s m y
        (fun z => Critical2DKPZ.pointToPlane β n₀ l z ξ) ω
    calc
      _ = ∫ ξ, ∑ z ∈ Polymer.endpoints y m,
          Critical2DKPZ.pointToPoint β s m y z ω * Critical2DKPZ.pointToPlane β n₀ l z ξ ∂disorderLaw := by
        rw [hEq]
      _ = ∑ z ∈ Polymer.endpoints y m,
          Critical2DKPZ.pointToPoint β s m y z ω *
            (∫ ξ, Critical2DKPZ.pointToPlane β n₀ l z ξ ∂disorderLaw) := by
        rw [integral_finsetSum _ fun z _ =>
          (memLp_one_iff_integrable.mp
            (Polymer.memLp_pointToPlane β n₀ l z 1 (by norm_num))).const_mul _]
        apply Finset.sum_congr rfl
        intro z hz
        rw [integral_const_mul]
      _ = Critical2DKPZ.pointToPlane β s m y ω := by
        simp only [Polymer.integral_pointToPlane, mul_one]
        calc
          _ = ∑' z, Critical2DKPZ.pointToPoint β s m y z ω := by
            simpa only [mul_one] using
              (Polymer.tsum_pointToPoint_mul_eq_sum β s m y (fun _ => 1) ω).symm
          _ = Critical2DKPZ.pointToPlane β s m y ω := Polymer.tsum_pointToPoint β s m y ω
  have houterInt (y : Site) : Integrable
      (fun ξ => srwKernel s (y - x) *
        (∑' z, Critical2DKPZ.pointToPoint β s m y z ω *
          Critical2DKPZ.pointToPlane β n₀ l z ξ)) disorderLaw :=
    (hFint y).const_mul _
  calc
    _ = ∑ y ∈ A, srwKernel s (y - x) *
        (∫ ξ, ∑' z, Critical2DKPZ.pointToPoint β s m y z ω *
          Critical2DKPZ.pointToPlane β n₀ l z ξ ∂disorderLaw) := by
      rw [integral_finsetSum _ fun y _ => (hFint y).const_mul _]
      apply Finset.sum_congr rfl
      intro y hy
      rw [integral_const_mul]
    _ = ∑ y ∈ Polymer.endpoints x s,
        srwKernel s (y - x) * Critical2DKPZ.pointToPlane β s m y ω := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hFmean]
    _ = smoothedP2Plane β s n₀ x ω := by
      simpa [A, m] using (Polymer.smoothedP2Plane_eq_sum β s n₀ x ω).symm

/-- The reciprocal moment increases when the end time is extended. -/
theorem integral_inv_smoothedP2Plane_mono_end (β : ℝ) (x : Site) {s n₀ n : ℕ}
    (h : s ≤ n₀) (h' : n₀ ≤ n) :
    ∫ ω, (smoothedP2Plane β s n₀ x ω)⁻¹ ∂disorderLaw ≤
      ∫ ω, (smoothedP2Plane β s n x ω)⁻¹ ∂disorderLaw := by
  let X := smoothedP2Plane β s n x
  let Y := smoothedP2Plane β s n₀ x
  have hXpos (ω : Disorder) : 0 < X ω := Polymer.smoothedP2Plane_pos β s n x ω
  have hYpos (ω : Disorder) : 0 < Y ω := Polymer.smoothedP2Plane_pos β s n₀ x ω
  have hXnonneg (ω : Disorder) : 0 ≤ X ω := (hXpos ω).le
  have hXmeas : Measurable X := Polymer.measurable_smoothedP2Plane β s n x
  have hXint : Integrable X disorderLaw := by
    exact memLp_one_iff_integrable.mp
      (Polymer.memLp_smoothedP2Plane β s n x 1 (by norm_num))
  have hYint : Integrable Y disorderLaw := by
    exact memLp_one_iff_integrable.mp
      (Polymer.memLp_smoothedP2Plane β s n₀ x 1 (by norm_num))
  have hXinvInt : Integrable (fun ω => (X ω)⁻¹) disorderLaw := by
    have h := integrable_rpow_smoothedP2Plane β s n x (-1)
    have heq : (fun ω => X ω ^ (-1 : ℝ)) = fun ω => (X ω)⁻¹ := by
      funext ω
      exact Real.rpow_neg_one _
    rw [← heq]
    exact h
  have hYinvInt : Integrable (fun ω => (Y ω)⁻¹) disorderLaw := by
    have h := integrable_rpow_smoothedP2Plane β s n₀ x (-1)
    have heq : (fun ω => Y ω ^ (-1 : ℝ)) = fun ω => (Y ω)⁻¹ := by
      funext ω
      exact Real.rpow_neg_one _
    rw [← heq]
    exact h
  have hYinvSqInt : Integrable (fun ω => (Y ω)⁻¹ ^ 2) disorderLaw := by
    have h := integrable_rpow_smoothedP2Plane β s n₀ x (-2)
    have heq : (fun ω => Y ω ^ (-2 : ℝ)) = fun ω => (Y ω)⁻¹ ^ 2 := by
      funext ω
      rw [show (-2 : ℝ) = (-1 : ℝ) * 2 by norm_num,
        Real.rpow_mul (hYpos ω).le, Real.rpow_neg_one]
      exact Real.rpow_natCast _ 2
    rw [← heq]
    exact h
  have hCE := Gaussian.condExp_disorderBlock_ae_eq s n₀ hXmeas hXint
  have hm : Gaussian.disorderBlock s n₀ ≤
      (inferInstance : MeasurableSpace Disorder) := Gaussian.disorderBlock_le s n₀
  have hshiftInt (ε : ℝ) (hε : 0 < ε) (Z : Disorder → ℝ) (hZmeas : Measurable Z)
      (hZnonneg : ∀ ω, 0 ≤ Z ω) :
      Integrable (fun ω => (ε + Z ω)⁻¹) disorderLaw := by
    apply (integrable_const (ε⁻¹)).mono'
    · have hmeas : Measurable (fun ω : Disorder => ε + Z ω) :=
          (measurable_const : Measurable (fun _ : Disorder => ε)).add hZmeas
      exact hmeas.inv.aestronglyMeasurable
    · filter_upwards with ω
      have hden : 0 < ε + Z ω := by linarith [hε, hZnonneg ω]
      have hbound : (ε + Z ω)⁻¹ ≤ ε⁻¹ := by
        apply (inv_le_inv₀ hden hε).2
        linarith [hZnonneg ω]
      simpa only [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hden),
        abs_of_pos (inv_pos.mpr hε)] using hbound
  have hshift (ε : ℝ) (hε : 0 < ε) :
      ∫ ω, (ε + Y ω)⁻¹ ∂disorderLaw ≤
        ∫ ω, (ε + X ω)⁻¹ ∂disorderLaw := by
    let φ : ℝ → ℝ := fun z => (ε + z)⁻¹
    let shift : ℝ →ᵃ[ℝ] ℝ :=
      (AffineMap.toConstProdLinearMap ℝ).symm (ε, LinearMap.id)
    have hshift_apply (z : ℝ) : shift z = ε + z := by
      simp [shift, AffineMap.toConstProdLinearMap_symm_apply]
      ring
    have hdomain : Set.Ici (0 : ℝ) ⊆ shift ⁻¹' Set.Ioi 0 := by
      intro z hz
      simp only [Set.mem_preimage, Set.mem_Ioi]
      rw [hshift_apply]
      have hz' : 0 ≤ z := hz
      linarith
    have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) φ := by
      have h := (convexOn_zpow (-1 : ℤ)).comp_affineMap shift
      have h := h.subset hdomain (convex_Ici (0 : ℝ))
      have hfun : (fun z : ℝ => z ^ (-1 : ℤ)) ∘ shift = φ := by
        funext z
        rw [Function.comp_apply, hshift_apply, zpow_neg_one]
      rw [hfun] at h
      exact h
    have hcont : ContinuousOn φ (Set.Ici (0 : ℝ)) := by
      change ContinuousOn (fun z : ℝ => (ε + z)⁻¹) (Set.Ici 0)
      apply ContinuousOn.inv₀ (continuous_const.continuousOn.add continuousOn_id)
      intro z hz
      have hz' : 0 ≤ z := hz
      exact (by linarith [hε, hz'] : ε + z ≠ 0)
    have hphiInt : Integrable (fun ω => φ (X ω)) disorderLaw := by
      simpa only [φ] using hshiftInt ε hε X hXmeas hXnonneg
    have hJ := hconv.map_condExp_le hm hcont.lowerSemicontinuousOn
      (Filter.Eventually.of_forall hXnonneg) isClosed_Ici hXint hphiInt
    have hCEY : disorderLaw[X | Gaussian.disorderBlock s n₀] =ᵐ[disorderLaw] Y := by
      filter_upwards [hCE] with ω hω
      rw [hω]
      exact integral_smoothed_resample_end β h h' x ω
    have hCEφ := hCEY.fun_comp φ
    have hleftInt : Integrable
        (fun ω => φ (disorderLaw[X | Gaussian.disorderBlock s n₀] ω)) disorderLaw := by
      apply (hshiftInt ε hε Y
        (Polymer.measurable_smoothedP2Plane β s n₀ x) (fun ω => (hYpos ω).le)).congr
      exact hCEφ.symm
    calc
      _ = ∫ ω, φ (disorderLaw[X | Gaussian.disorderBlock s n₀] ω) ∂disorderLaw := by
            apply integral_congr_ae
            exact hCEφ.symm
      _ ≤ ∫ ω, disorderLaw[φ ∘ X | Gaussian.disorderBlock s n₀] ω ∂disorderLaw :=
            integral_mono_ae hleftInt integrable_condExp hJ
      _ = ∫ ω, φ (X ω) ∂disorderLaw := integral_condExp hm
  let IX := ∫ ω, (X ω)⁻¹ ∂disorderLaw
  let IY := ∫ ω, (Y ω)⁻¹ ∂disorderLaw
  let M := ∫ ω, (Y ω)⁻¹ ^ 2 ∂disorderLaw
  have hMnonneg : 0 ≤ M := integral_nonneg fun ω => sq_nonneg ((Y ω)⁻¹)
  have hbound (ε : ℝ) (hε : 0 < ε) : IY ≤ IX + ε * M := by
    have hshiftY := hshiftInt ε hε Y
      (Polymer.measurable_smoothedP2Plane β s n₀ x) (fun ω => (hYpos ω).le)
    have hshiftX := hshiftInt ε hε X hXmeas hXnonneg
    have happrox (ω : Disorder) :
        (Y ω)⁻¹ ≤ (ε + Y ω)⁻¹ + ε * (Y ω)⁻¹ ^ 2 := by
      have hy : 0 < Y ω := hYpos ω
      have hden : 0 < ε + Y ω := by linarith [hε, hy]
      have hiden : (ε + Y ω)⁻¹ + ε * (Y ω)⁻¹ ^ 2 - (Y ω)⁻¹ =
          ε ^ 2 / ((Y ω) ^ 2 * (ε + Y ω)) := by
        field_simp [ne_of_gt hy, ne_of_gt hden]
        ring
      rw [← sub_nonneg]
      rw [hiden]
      positivity
    have hsumInt : Integrable
        (fun ω => (ε + Y ω)⁻¹ + ε * (Y ω)⁻¹ ^ 2) disorderLaw :=
      hshiftY.add (hYinvSqInt.const_mul ε)
    have hmono := integral_mono_ae hYinvInt hsumInt
      (Filter.Eventually.of_forall happrox)
    have hsum := integral_add hshiftY (hYinvSqInt.const_mul ε)
    rw [hsum, integral_const_mul] at hmono
    have hpoint (ω : Disorder) : (ε + X ω)⁻¹ ≤ (X ω)⁻¹ := by
      have hden : 0 < ε + X ω := by linarith [hε, hXpos ω]
      apply (inv_le_inv₀ hden (hXpos ω)).2
      linarith
    have hmonoX := integral_mono_ae hshiftX hXinvInt
      (Filter.Eventually.of_forall hpoint)
    have hshiftXY := hshift ε hε
    calc
      IY ≤ (∫ ω, (ε + Y ω)⁻¹ ∂disorderLaw) + ε * M := by
        dsimp [IY, M]
        linarith
      _ ≤ (∫ ω, (ε + X ω)⁻¹ ∂disorderLaw) + ε * M := add_le_add hshiftXY le_rfl
      _ ≤ IX + ε * M := by
        dsimp [IX]
        nlinarith [hmonoX]
  by_contra hnot
  have hlt : IX < IY := lt_of_not_ge hnot
  let ε := (IY - IX) / (M + 1)
  have hε : 0 < ε := div_pos (sub_pos.mpr hlt) (by linarith [hMnonneg])
  have hratio : M / (M + 1) < 1 := by
    apply (div_lt_iff₀ (by linarith [hMnonneg] : 0 < M + 1)).2
    linarith
  have hprod : ε * M < IY - IX := by
    calc
      ε * M = (IY - IX) * (M / (M + 1)) := by dsimp [ε]; ring
      _ < (IY - IX) * 1 := mul_lt_mul_of_pos_left hratio (sub_pos.mpr hlt)
      _ = IY - IX := by ring
  have hfinal := hbound ε hε
  dsimp [IX, IY] at hlt hfinal
  linarith

/-- Assuming the small-time origin bound, smoothed polymer masses satisfy the Gaussianity-defect and moment-ratio bounds of Proposition 4.1(1). -/
theorem prop_VD_part1_of (A : ℝ) (hsmall : SmallTimeOriginBound A) :
    ∀ T₀ T₁ : ℝ, 0 < T₀ → T₀ < T₁ → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ (x : Site) (s n : ℕ), Even s → Even n → s ≤ n → T₀ * N ≤ n → (n : ℝ) ≤ T₁ * N →
        0 ≤ gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s n x ω)) ∧
        gaussianityDefect disorderLaw (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) s n x ω)) ≤
          Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n x ω ^ 2 ∂disorderLaw) /
            ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n x ω)⁻¹ ∂disorderLaw) ∧
        Real.log ((∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n x ω ^ 2 ∂disorderLaw) /
            ∫ ω, (smoothedP2Plane (criticalBeta ϑ N) s n x ω)⁻¹ ∂disorderLaw) ≤ C := by
  intro T₀ T₁ hT₀ hT₀T₁
  obtain ⟨Cup, hupper⟩ := smoothedP2Plane_secondMoment_le_log A T₀ T₁ hT₀
  obtain ⟨δ₁, hδ₁pos, hδ₁sqrt, hlower⟩ :=
    smoothedP2Plane_secondMoment_ge_log A T₀ T₁ hT₀ hT₀T₁
  obtain ⟨δ₀, Csmall, hδ₀pos, hδ₀lt, hsmall'⟩ := hsmall
  let δ : ℝ := min δ₀ δ₁
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδle₀ : δ ≤ δ₀ := by dsimp [δ]; exact min_le_left _ _
  have hδle₁ : δ ≤ δ₁ := by dsimp [δ]; exact min_le_right _ _
  obtain ⟨c, hcpos, hlowerδ⟩ := hlower δ hδpos hδle₁
  obtain ⟨o, ho, hsmallδ⟩ := hsmall' δ hδpos hδle₀
  let q : ℝ := Real.sqrt δ
  have hqpos : 0 < q := by dsimp [q]; exact Real.sqrt_pos.2 hδpos
  have hqT₀ : q < T₀ := by
    dsimp [q]
    exact lt_of_le_of_lt (Real.sqrt_le_sqrt hδle₁) hδ₁sqrt
  have hqT₁ : q < T₁ := lt_trans hqT₀ hT₀T₁
  let U : ℝ := max Cup 1
  let K : ℝ := |Csmall / |Real.log δ| ^ ((1 : ℝ) / 4)| + 1
  have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
  let Clarge : ℝ := Real.log (max 1 (U * (1 + Real.log (T₁ / q))))
  let Csmall' : ℝ := Real.log (max 1 (U * Real.exp K / c))
  let C : ℝ := max Clarge Csmall'
  have hUge : Cup ≤ U := by dsimp [U]; exact le_max_left _ _
  have hUpos : 0 < U := by dsimp [U]; positivity
  have hδ₀δ₁ : δ < 1 := lt_of_le_of_lt hδle₀ hδ₀lt
  have hlogTq : 0 ≤ Real.log (T₁ / q) := by
    apply Real.log_nonneg
    rw [one_le_div hqpos]
    linarith
  have hKbound : Csmall / |Real.log δ| ^ ((1 : ℝ) / 4) + 1 ≤ K := by
    dsimp [K]
    linarith [le_abs_self (Csmall / |Real.log δ| ^ ((1 : ℝ) / 4))]
  have hsmallO : ∀ᶠ N : ℕ in atTop, o N ≤ 1 := by
    have h := ho.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [h] with N hN
    exact le_of_lt hN
  have hround : ∀ᶠ N : ℕ in atTop, 2 / (T₀ - q) < (N : ℝ) := by
    have hpos : 0 < T₀ - q := by linarith
    exact (tendsto_natCast_atTop_atTop).eventually_gt_atTop (2 / (T₀ - q))
  refine ⟨C, ?_⟩
  filter_upwards [hupper, hlowerδ, hsmallδ, hsmallO, hround, eventually_ge_atTop 1]
    with N hupperN hlowerN hsmallN hsmallON hroundN hN1
  intro ϑ hϑ x s n hs hn hsn hT₀n hnT₁
  let β : ℝ := criticalBeta ϑ N
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; exact Real.sqrt_nonneg _
  have hdefect := gaussianityDefect_log_smoothedP2Plane_bounds hβ s n x
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (mul_pos hT₀ hNpos) hT₀n
  have hn1 : 1 ≤ n := by exact_mod_cast hnpos
  have hlogL : 0 ≤ Real.log ((n : ℝ) / (max s 1 : ℕ)) := by
    apply Real.log_nonneg
    apply (one_le_div (by exact_mod_cast (show 0 < max s 1 by omega))).2
    exact_mod_cast (show max s 1 ≤ n by omega)
  have hLpos : 0 < 1 + Real.log ((n : ℝ) / (max s 1 : ℕ)) := by linarith
  have hupperMoment := hupperN ϑ hϑ s n hsn hT₀n hnT₁
  have hupperMoment' :
      (∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw) ≤
        U * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := by
    dsimp [β]
    calc
      _ ≤ Cup * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := hupperMoment
      _ ≤ U * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) :=
        mul_le_mul_of_nonneg_right hUge hLpos.le
  have htranslate := smoothedP2Plane_moments_translate β s n x
  rcases htranslate with ⟨hmoment, hinverse, _⟩
  have hratioBound :
      Real.log ((∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw) /
        ∫ ω, (smoothedP2Plane β s n 0 ω)⁻¹ ∂disorderLaw) ≤ C := by
    let M : ℝ := ∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw
    let I : ℝ := ∫ ω, (smoothedP2Plane β s n 0 ω)⁻¹ ∂disorderLaw
    have hMone : 1 ≤ M := by dsimp [M]; exact one_le_integral_smoothedP2Plane_sq β s n 0
    have hIone : 1 ≤ I := by dsimp [I]; exact one_le_integral_inv_smoothedP2Plane β s n 0
    have hIpos : 0 < I := lt_of_lt_of_le zero_lt_one hIone
    have hratioPos : 0 < M / I := div_pos (lt_of_lt_of_le zero_lt_one hMone) hIpos
    have hMupper : M ≤ U * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := by
      dsimp [M]
      exact hupperMoment'
    let n₀ : ℕ := evenCeil (q * N)
    have hn₀low : q * (N : ℝ) ≤ (n₀ : ℝ) := by
      dsimp [n₀, q]
      exact Critical2DKPZ.le_evenCeil _
    have hn₀high : (n₀ : ℝ) < q * (N : ℝ) + 2 := by
      dsimp [n₀, q]
      exact Critical2DKPZ.evenCeil_lt_add_two (by positivity)
    have hn₀le : n₀ ≤ n := by
      have hgap : 2 < (T₀ - q) * (N : ℝ) := by
        have hmul := mul_lt_mul_of_pos_left hroundN (sub_pos.mpr hqT₀)
        have hcancel : (T₀ - q) * (2 / (T₀ - q)) = 2 := by
          field_simp [ne_of_gt (sub_pos.mpr hqT₀)]
        nlinarith only [hmul, hcancel]
      have hn₀T₀ : (n₀ : ℝ) < T₀ * N := by nlinarith only [hn₀high, hgap]
      exact_mod_cast (le_trans hn₀T₀.le hT₀n)
    by_cases hslarge : n₀ ≤ s
    · have hn₀pos : 0 < n₀ := by
        have hreal : 0 < (n₀ : ℝ) := lt_of_lt_of_le (mul_pos hqpos hNpos) hn₀low
        exact_mod_cast hreal
      have hmaxlower : q * (N : ℝ) ≤ (max s 1 : ℕ) := by
        have hsreal : (n₀ : ℝ) ≤ (max s 1 : ℕ) := by
          exact_mod_cast (le_trans hslarge (le_max_left s 1))
        exact le_trans hn₀low hsreal
      have hratioUpper : (n : ℝ) / (max s 1 : ℕ) ≤ T₁ / q := by
        apply (div_le_div_iff₀ (by exact_mod_cast (show 0 < max s 1 by omega)) hqpos).2
        calc
          (n : ℝ) * q ≤ (T₁ * N) * q := mul_le_mul_of_nonneg_right hnT₁ hqpos.le
          _ = T₁ * (q * N) := by ring
          _ ≤ T₁ * (max s 1 : ℕ) := mul_le_mul_of_nonneg_left hmaxlower (by linarith)
      have hlogUpper : Real.log ((n : ℝ) / (max s 1 : ℕ)) ≤ Real.log (T₁ / q) :=
        Real.log_le_log (div_pos hnpos (by exact_mod_cast (show 0 < max s 1 by omega))) hratioUpper
      have hquotUpper : M / I ≤ U * (1 + Real.log (T₁ / q)) := by
        apply (div_le_iff₀ hIpos).2
        have hIbound : 1 ≤ I := hIone
        calc
          M ≤ U * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := hMupper
          _ ≤ U * (1 + Real.log (T₁ / q)) :=
            mul_le_mul_of_nonneg_left (by linarith) hUpos.le
          _ ≤ (U * (1 + Real.log (T₁ / q))) * I := by
            calc
              _ = (U * (1 + Real.log (T₁ / q))) * 1 := by rw [mul_one]
              _ ≤ (U * (1 + Real.log (T₁ / q))) * I :=
                mul_le_mul_of_nonneg_left hIbound
                  (mul_nonneg hUpos.le (by linarith [hlogTq]))
      have hquotMax : M / I ≤ max 1 (U * (1 + Real.log (T₁ / q))) :=
        le_trans hquotUpper (le_max_right _ _)
      have hlogQuot : Real.log (M / I) ≤ Clarge := by
        exact Real.log_le_log hratioPos hquotMax
      dsimp [C]
      exact le_trans hlogQuot (le_max_left _ _)
    · have hsmallS : s ≤ n₀ := le_of_not_ge hslarge
      let M₀ : ℝ := ∫ ω, smoothedP2Plane β s n₀ 0 ω ^ 2 ∂disorderLaw
      let I₀ : ℝ := ∫ ω, (smoothedP2Plane β s n₀ 0 ω)⁻¹ ∂disorderLaw
      have hM₀one : 1 ≤ M₀ := by dsimp [M₀]; exact one_le_integral_smoothedP2Plane_sq β s n₀ 0
      have hI₀one : 1 ≤ I₀ := by dsimp [I₀]; exact one_le_integral_inv_smoothedP2Plane β s n₀ 0
      have hI₀pos : 0 < I₀ := lt_of_lt_of_le zero_lt_one hI₀one
      have hsmallLog := hsmallN ϑ hϑ s hs hsmallS
      have hM₀ratioPos : 0 < M₀ / I₀ :=
        div_pos (lt_of_lt_of_le zero_lt_one hM₀one) hI₀pos
      have hM₀ratio : M₀ / I₀ ≤ Real.exp K := by
        apply (Real.log_le_iff_le_exp hM₀ratioPos).1
        calc
          Real.log (M₀ / I₀) ≤ Csmall / |Real.log δ| ^ ((1 : ℝ) / 4) + o N := hsmallLog
          _ ≤ K := by dsimp [K]; linarith [hKbound, hsmallON]
      have hM₀le : M₀ ≤ Real.exp K * I₀ := (div_le_iff₀ hI₀pos).1 hM₀ratio
      have hI₀lower : Real.exp (-K) * M₀ ≤ I₀ := by
        calc
          Real.exp (-K) * M₀ ≤ Real.exp (-K) * (Real.exp K * I₀) :=
            mul_le_mul_of_nonneg_left hM₀le (Real.exp_pos _).le
          _ = I₀ := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      have hIle : I₀ ≤ I := by
        dsimp [I₀, I, β]
        exact integral_inv_smoothedP2Plane_mono_end (criticalBeta ϑ N) 0 hsmallS hn₀le
      have hlowerM₀ := hlowerN ϑ hϑ s n hsmallS hT₀n hnT₁
      have hratioUpper : M / I ≤ U * Real.exp K / c := by
        have hdenLower : Real.exp (-K) * (c *
            (1 + Real.log ((n : ℝ) / (max s 1 : ℕ)))) ≤ I := by
          calc
            _ ≤ Real.exp (-K) * M₀ :=
              mul_le_mul_of_nonneg_left hlowerM₀ (Real.exp_pos _).le
            _ ≤ I₀ := hI₀lower
            _ ≤ I := hIle
        have hdenPos : 0 < Real.exp (-K) * (c *
            (1 + Real.log ((n : ℝ) / (max s 1 : ℕ)))) := by
          positivity
        have hcancel : (U * Real.exp K / c) *
            (Real.exp (-K) * (c * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))))) =
              U * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := by
          field_simp [ne_of_gt hcpos]
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        have hboundMul : M ≤ (U * Real.exp K / c) * I := by
          calc
            M ≤ U * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))) := hMupper
            _ = (U * Real.exp K / c) *
                (Real.exp (-K) * (c * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))))) := hcancel.symm
            _ ≤ (U * Real.exp K / c) * I :=
              mul_le_mul_of_nonneg_left hdenLower (by positivity)
        exact (div_le_iff₀ hIpos).2 hboundMul
      have hquotMax : M / I ≤ max 1 (U * Real.exp K / c) :=
        le_trans hratioUpper (le_max_right _ _)
      have hlogQuot : Real.log (M / I) ≤ Csmall' :=
        Real.log_le_log hratioPos hquotMax
      dsimp [C]
      exact le_trans hlogQuot (le_max_right _ _)
  refine ⟨hdefect.1, ?_, ?_⟩
  · exact hdefect.2
  · calc
      Real.log ((∫ ω, smoothedP2Plane β s n x ω ^ 2 ∂disorderLaw) /
          ∫ ω, (smoothedP2Plane β s n x ω)⁻¹ ∂disorderLaw) =
        Real.log ((∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw) /
          ∫ ω, (smoothedP2Plane β s n 0 ω)⁻¹ ∂disorderLaw) := by rw [hmoment, hinverse]
      _ ≤ C := hratioBound

end Critical2DKPZ.OnePoint

end
