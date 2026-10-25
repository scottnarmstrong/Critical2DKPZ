/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.ProfileLogTails
public import Critical2DKPZ.FutureProfiles.SmoothedEndpointProfile
public import Critical2DKPZ.OnePoint.OnePointInverseMomentComparison
public import Critical2DKPZ.OnePoint.RenewalGap
public import Critical2DKPZ.Polymer.ChapmanKolmogorov
public import Critical2DKPZ.Polymer.ProfileCovariance
public import Critical2DKPZ.Polymer.WalkKernel
public import Critical2DKPZ.FutureProfiles.LowerSecondMoment
public import Critical2DKPZ.Polymer.BlockMeasurability
import Mathlib.Tactic

/-! # Left tails of endpoint profiles -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open Critical2DKPZ.OnePoint

namespace Critical2DKPZ.FutureProfiles

private theorem integral_invSqrt_smoothedRatio_le (β : ℝ) (hβ : 0 ≤ β)
    {m n N : ℕ} (x : Site) :
    Integrable (fun ω =>
      (smoothedP2Plane β m N x ω / smoothedP2Plane β m n x ω) ^ (-(1 / 2 : ℝ))) disorderLaw ∧
    (∫ ω, (smoothedP2Plane β m N x ω / smoothedP2Plane β m n x ω) ^ (-(1 / 2 : ℝ))
      ∂disorderLaw) ≤ Real.sqrt (∫ ω, smoothedP2Plane β m N x ω ^ 2 ∂disorderLaw) := by
  let U : Disorder → ℝ := smoothedP2Plane β m N x
  let V : Disorder → ℝ := smoothedP2Plane β m n x
  let f : Disorder → ℝ := fun ω => V ω ^ (1 / 2 : ℝ)
  let g : Disorder → ℝ := fun ω => U ω ^ (-(1 / 2 : ℝ))
  have hUpos (ω : Disorder) : 0 < U ω := by
    exact Polymer.smoothedP2Plane_pos β m N x ω
  have hVpos (ω : Disorder) : 0 < V ω := by
    exact Polymer.smoothedP2Plane_pos β m n x ω
  have hfmeas : Measurable f := by
    dsimp [f, V]
    exact (Polymer.measurable_smoothedP2Plane β m n x).pow_const _
  have hgmeas : Measurable g := by
    dsimp [g, U]
    exact (Polymer.measurable_smoothedP2Plane β m N x).pow_const _
  have hVint : Integrable V disorderLaw := by
    have h := OnePoint.integrable_rpow_smoothedP2Plane β m n x 1
    simpa [V, Real.rpow_one] using h
  have hUinvint : Integrable (fun ω => U ω ^ (-1 : ℝ)) disorderLaw := by
    simpa [U] using OnePoint.integrable_rpow_smoothedP2Plane β m N x (-1)
  have hfSq : Integrable (fun ω => f ω ^ 2) disorderLaw := by
    have heq : (fun ω => f ω ^ 2) = V := by
      funext ω
      dsimp [f]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (hVpos ω))]
      norm_num
    rw [heq]
    exact hVint
  have hgSq : Integrable (fun ω => g ω ^ 2) disorderLaw := by
    have heq : (fun ω => g ω ^ 2) = fun ω => U ω ^ (-1 : ℝ) := by
      funext ω
      dsimp [g]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (hUpos ω))]
      norm_num
    rw [heq]
    exact hUinvint
  have hfmem : MemLp f 2 disorderLaw :=
    (memLp_two_iff_integrable_sq hfmeas.aestronglyMeasurable).2 hfSq
  have hgmem : MemLp g 2 disorderLaw :=
    (memLp_two_iff_integrable_sq hgmeas.aestronglyMeasurable).2 hgSq
  have hfmem' : MemLp f (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hfmem
  have hgmem' : MemLp g (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hgmem
  have hfnonneg : ∀ᵐ ω ∂disorderLaw, 0 ≤ f ω :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hVpos ω).le _
  have hgnonneg : ∀ᵐ ω ∂disorderLaw, 0 ≤ g ω :=
    Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hUpos ω).le _
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := disorderLaw) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    hfnonneg hgnonneg hfmem' hgmem'
  have hVmean : ∫ ω, V ω ∂disorderLaw = 1 := by
    dsimp [V]
    exact Polymer.integral_smoothedP2Plane β m n x
  have hUinvBound : ∫ ω, U ω ^ (-1 : ℝ) ∂disorderLaw ≤
      ∫ ω, U ω ^ 2 ∂disorderLaw := by
    let ν : Site → ℝ := fun y => srwKernel m (y - x)
    let A : Finset Site := Polymer.endpoints x m
    have hνA : ∀ y ∉ A, ν y = 0 := by
      intro y hy
      exact Polymer.srwKernel_eq_zero_of_not_mem m x y (by simpa [A] using hy)
    have hν0 : ∀ y, 0 ≤ ν y := fun y => Critical2DKPZ.srwKernel_nonneg m (y - x)
    have hν1 : ∑ y ∈ A, ν y = 1 := Polymer.sum_srwKernel_endpoints m x
    have hProfileInverseMomentInput := OnePoint.integral_rpow_neg_profileP2Fun_le (β := β)
      hβ m N ν A hνA hν0 hν1 (p := 1) (by norm_num)
    have hflat (ω : Disorder) :
        profileP2Fun β m N ν (fun _ => 1) ω = U ω := by
      dsimp [U, ν]
      exact Polymer.profileP2Fun_srw_flat β m N x ω
    have hexp : (1 : ℝ) * (1 + 1) / 2 = 1 := by norm_num
    simpa only [hflat, Real.rpow_neg_one, Real.rpow_one, hexp] using hProfileInverseMomentInput
  have hHolder' :
      ∫ ω, f ω * g ω ∂disorderLaw ≤
        (∫ ω, f ω ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) *
          (∫ ω, g ω ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := by
    convert hHolder using 1
    norm_num
  have hratio (ω : Disorder) :
      (U ω / V ω) ^ (-(1 / 2 : ℝ)) = f ω * g ω := by
    dsimp [f, g]
    rw [Real.div_rpow (hUpos ω).le (hVpos ω).le]
    rw [Real.rpow_neg (hUpos ω).le, Real.rpow_neg (hVpos ω).le]
    field_simp
  have hprodint : Integrable (fun ω => f ω * g ω) disorderLaw := by
    have hpqENN : ENNReal.HolderTriple
        (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 :=
      Real.HolderConjugate.two_two.ennrealOfReal
    have hprodmem : MemLp (fun ω => g ω * f ω) 1 disorderLaw := by
      exact @MemLp.mul Disorder inferInstance ℝ inferInstance disorderLaw
        (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1
        f g hgmem' hfmem' hpqENN
    have hprodint' : Integrable (fun ω => g ω * f ω) disorderLaw :=
      hprodmem.integrable (by norm_num)
    simpa only [mul_comm] using hprodint'
  have hratioint : Integrable
      (fun ω => (U ω / V ω) ^ (-(1 / 2 : ℝ))) disorderLaw := by
    apply hprodint.congr
    filter_upwards [] with ω
    exact (hratio ω).symm
  have hVroot : (∫ ω, f ω ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) = 1 := by
    rw [show (fun ω => f ω ^ 2) = V by
      funext ω
      dsimp [f]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (hVpos ω))]
      norm_num]
    rw [hVmean]
    norm_num
  have hUroot : (∫ ω, g ω ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) ≤
      Real.sqrt (∫ ω, U ω ^ 2 ∂disorderLaw) := by
    have hnonneg : 0 ≤ ∫ ω, g ω ^ 2 ∂disorderLaw :=
      integral_nonneg fun ω => sq_nonneg (g ω)
    have hbound : ∫ ω, g ω ^ 2 ∂disorderLaw ≤ ∫ ω, U ω ^ 2 ∂disorderLaw := by
      calc
        ∫ ω, g ω ^ 2 ∂disorderLaw = ∫ ω, U ω ^ (-1 : ℝ) ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [] with ω
          dsimp [g]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (hUpos ω))]
          norm_num
        _ ≤ ∫ ω, U ω ^ 2 ∂disorderLaw := hUinvBound
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow hnonneg hbound (by norm_num)
  constructor
  · exact hratioint
  · calc
      _ = ∫ ω, f ω * g ω ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact hratio ω
      _ ≤ (∫ ω, f ω ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) *
          (∫ ω, g ω ^ 2 ∂disorderLaw) ^ (1 / 2 : ℝ) := hHolder'
      _ ≤ Real.sqrt (∫ ω, U ω ^ 2 ∂disorderLaw) := by
        rw [hVroot]
        simpa only [one_mul, Real.sqrt_eq_rpow] using hUroot

/-- A negative half-power moment gives an exponential lower-tail estimate. -/
theorem measure_lt_exp_neg_le_of_integrable_rpow_neg
    {μ : Measure Disorder} [IsFiniteMeasure μ] (X : Disorder → ℝ) (u B : ℝ)
    (hXpos : ∀ ω, 0 < X ω)
    (hXint : Integrable (fun ω => X ω ^ (-(1 / 2 : ℝ))) μ)
    (hXbound : ∫ ω, X ω ^ (-(1 / 2 : ℝ)) ∂μ ≤ B) :
    (μ {ω | X ω < Real.exp (-u)}).toReal ≤ B * Real.exp (-u / 2) := by
  let Y : Disorder → ℝ := fun ω => X ω ^ (-(1 / 2 : ℝ)) * Real.exp (-u / 2)
  have hYint : Integrable Y μ := hXint.mul_const _
  have hYnonneg : 0 ≤ᵐ[μ] Y := by
    filter_upwards [] with ω
    exact mul_nonneg (Real.rpow_nonneg (hXpos ω).le _) (Real.exp_nonneg _)
  have hYmean : ∫ ω, Y ω ∂μ =
      (∫ ω, X ω ^ (-(1 / 2 : ℝ)) ∂μ) * Real.exp (-u / 2) := by
    simp only [Y, integral_mul_const]
  have hYbound : ∀ ω ∈ {ω | X ω < Real.exp (-u)}, 1 ≤ Y ω := by
    intro ω hω
    have hpow := Real.rpow_lt_rpow_of_neg (hXpos ω) hω (by norm_num : (-(1 / 2 : ℝ)) < 0)
    have hexp : Real.exp (-u) ^ (-(1 / 2 : ℝ)) = Real.exp (u / 2) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1
      ring
    rw [hexp] at hpow
    calc
      1 = Real.exp (u / 2) * Real.exp (-u / 2) := by
        rw [← Real.exp_zero, ← Real.exp_add]
        congr 1
        ring
      _ ≤ X ω ^ (-(1 / 2 : ℝ)) * Real.exp (-u / 2) :=
        le_of_lt (mul_lt_mul_of_pos_right hpow (Real.exp_pos _))
      _ = Y ω := rfl
  have hmarkov := hYint.measure_le_integral hYnonneg hYbound
  have hbound : μ {ω | X ω < Real.exp (-u)} ≤
      ENNReal.ofReal (B * Real.exp (-u / 2)) := by
    have hmeanle : ∫ ω, Y ω ∂μ ≤ B * Real.exp (-u / 2) := by
      rw [hYmean]
      exact mul_le_mul_of_nonneg_right hXbound (Real.exp_nonneg _)
    calc
      μ {ω | X ω < Real.exp (-u)} ≤ ENNReal.ofReal (∫ ω, Y ω ∂μ) := hmarkov
      _ ≤ ENNReal.ofReal (B * Real.exp (-u / 2)) := ENNReal.ofReal_le_ofReal hmeanle
  calc
    (μ {ω | X ω < Real.exp (-u)}).toReal ≤
        (ENNReal.ofReal (B * Real.exp (-u / 2))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = B * Real.exp (-u / 2) := by
      rw [ENNReal.toReal_ofReal]
      exact mul_nonneg
        (le_trans (integral_nonneg fun ω => Real.rpow_nonneg (hXpos ω).le _) hXbound)
        (Real.exp_nonneg _)

private theorem smoothedP2Plane_secondMoment_le_log (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∫ ω, smoothedP2Plane (criticalBeta ϑ N) 0 N 0 ω ^ 2 ∂disorderLaw ≤
        C * Real.log (N : ℝ) := by
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_uniform A 1
  obtain ⟨C_R, hC_R⟩ := OnePoint.replicaOverlap_sub_log_bounded
  let C : ℝ := 1 + |C₂| * (1 / Real.pi + C_R) / Real.log 2
  have hCR : 0 ≤ C_R := by
    have h := hC_R 0 0 (by omega)
    simpa using h
  have hCpos : 0 < C := by
    dsimp [C]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  have hN : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC₂, hlog, hN] with N hC₂N hlogN hN₂
  intro ϑ hϑ
  have hR : Critical2DKPZ.replicaOverlap N ≤
      (1 / Real.pi) * Real.log (N : ℝ) + C_R := by
    have h := hC_R 0 N (by omega)
    have hR0 : Critical2DKPZ.replicaOverlap 0 = 0 := by
      simp [Critical2DKPZ.replicaOverlap]
    have habs : |Real.pi * Critical2DKPZ.replicaOverlap N -
        Real.log (N : ℝ)| ≤ C_R := by
      simpa [hR0, max_eq_left (by omega : 1 ≤ N)] using h
    have habs' := (abs_le.mp habs).2
    have hpi : 0 < Real.pi := Real.pi_pos
    have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc
      Critical2DKPZ.replicaOverlap N ≤
          (Real.log (N : ℝ) + C_R) / Real.pi := by
            rw [le_div_iff₀ hpi]
            nlinarith
      _ ≤ Real.log (N : ℝ) / Real.pi + C_R := by
            have hcrdiv : C_R / Real.pi ≤ C_R := by
              rw [div_le_iff₀ hpi]
              nlinarith [hCR, Real.pi_gt_three]
            calc
              (Real.log (N : ℝ) + C_R) / Real.pi =
                  Real.log (N : ℝ) / Real.pi + C_R / Real.pi := by ring
              _ ≤ _ := by nlinarith [hcrdiv]
      _ = _ := by ring
  have hsecond := hC₂N ϑ hϑ 0 N (by omega) (by omega) (by norm_num)
  have hR0 : Critical2DKPZ.replicaOverlap 0 = 0 := by
    simp [Critical2DKPZ.replicaOverlap]
  have hden : Real.log (1 + (N : ℝ) / (N : ℝ)) = Real.log 2 := by
    congr 1
    field_simp
    norm_num
  rw [hR0, hden] at hsecond
  have hRnonneg : 0 ≤ Critical2DKPZ.replicaOverlap N :=
    (Critical2DKPZ.replicaOverlap_pos (by omega)).le
  have hsecond' :
      ∫ ω, smoothedP2Plane (criticalBeta ϑ N) 0 N 0 ω ^ 2 ∂disorderLaw ≤
        1 + |C₂| * (Critical2DKPZ.replicaOverlap N / Real.log 2) := by
    have hcoeff : C₂ * (Critical2DKPZ.replicaOverlap N / Real.log 2) ≤
        |C₂| * (Critical2DKPZ.replicaOverlap N / Real.log 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self C₂)
        (div_nonneg hRnonneg (Real.log_pos (by norm_num)).le)
    have hcoeff' :
        C₂ * (Critical2DKPZ.replicaOverlap N - 0) / Real.log 2 ≤
          |C₂| * (Critical2DKPZ.replicaOverlap N / Real.log 2) := by
      convert hcoeff using 1
      ring
    exact hsecond.trans (add_le_add le_rfl hcoeff')
  have hRupper : Critical2DKPZ.replicaOverlap N ≤
      (1 / Real.pi + C_R) * Real.log (N : ℝ) := by
    calc
      Critical2DKPZ.replicaOverlap N ≤ (1 / Real.pi) * Real.log (N : ℝ) + C_R := hR
      _ ≤ (1 / Real.pi + C_R) * Real.log (N : ℝ) := by
        have hlogdiff : 0 ≤ Real.log (N : ℝ) - 1 := by linarith [hlogN]
        have hcrprod := mul_nonneg hCR hlogdiff
        nlinarith [hcrprod]
  have hsecond'' :
      ∫ ω, smoothedP2Plane (criticalBeta ϑ N) 0 N 0 ω ^ 2 ∂disorderLaw ≤
        C * Real.log (N : ℝ) := by
    dsimp [C]
    let K : ℝ := |C₂| * (1 / Real.pi + C_R) / Real.log 2
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hratioBound :
        Critical2DKPZ.replicaOverlap N / Real.log 2 ≤
          ((1 / Real.pi + C_R) * Real.log (N : ℝ)) / Real.log 2 :=
      div_le_div_of_nonneg_right hRupper (Real.log_pos (by norm_num)).le
    have hscaled := mul_le_mul_of_nonneg_left hratioBound (abs_nonneg C₂)
    calc
      _ ≤ 1 + |C₂| * (Critical2DKPZ.replicaOverlap N / Real.log 2) := hsecond'
      _ ≤ 1 + K * Real.log (N : ℝ) := by
        dsimp [K]
        convert add_le_add_left hscaled 1 using 1 <;> ring
      _ ≤ Real.log (N : ℝ) + K * Real.log (N : ℝ) := by
        nlinarith [hlogN]
      _ = (1 + K) * Real.log (N : ℝ) := by ring
      _ = (1 + |C₂| * (1 / Real.pi + C_R) / Real.log 2) * Real.log (N : ℝ) := by
        dsimp [K]
  exact hsecond''

/-- An exponential left-tail bound for the endpoint log partition function. -/
theorem measure_profileP2Fun_endpointDist_lt_le (A : ℝ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ n : ℕ, n ≤ N →
      ∀ u : ℝ, 0 ≤ u →
        (disorderLaw {ω | profileP2Fun (criticalBeta ϑ N) n N
          (endpointDist (criticalBeta ϑ N) n 0 ω) (fun _ => 1) ω < Real.exp (-u)}).toReal ≤
          C * Real.sqrt (Real.log N) * Real.exp (-u / 2) := by
  obtain ⟨Cmom, hCmompos, hCmom⟩ := smoothedP2Plane_secondMoment_le_log A
  refine ⟨Real.sqrt Cmom, ?_⟩
  filter_upwards [hCmom, eventually_ge_atTop 2] with N hCmomN hN2
  intro ϑ hϑ n hn u hu
  let X : Disorder → ℝ := fun ω =>
    profileP2Fun (criticalBeta ϑ N) n N (endpointDist (criticalBeta ϑ N) n 0 ω)
      (fun _ => 1) ω
  let U : Disorder → ℝ := fun ω => smoothedP2Plane (criticalBeta ϑ N) 0 N 0 ω
  let V : Disorder → ℝ := fun ω => smoothedP2Plane (criticalBeta ϑ N) 0 n 0 ω
  have hβ : 0 ≤ criticalBeta ϑ N := by
    dsimp [criticalBeta]
    exact Real.sqrt_nonneg _
  have hVeq (ω : Disorder) : V ω = pointToPlane (criticalBeta ϑ N) 0 n 0 ω := by
    dsimp [V, smoothedP2Plane]
    simp [Critical2DKPZ.srwKernel_zero]
  have hUeq (ω : Disorder) : U ω = pointToPlane (criticalBeta ϑ N) 0 N 0 ω := by
    dsimp [U, smoothedP2Plane]
    simp [Critical2DKPZ.srwKernel_zero]
  have hratio (ω : Disorder) : X ω = U ω / V ω := by
    have h := Polymer.pointToPlane_endpoint_factorization
      (criticalBeta ϑ N) n N hn 0 ω
    calc
      X ω = (pointToPlane (criticalBeta ϑ N) 0 n 0 ω * X ω) /
          pointToPlane (criticalBeta ϑ N) 0 n 0 ω := by
            dsimp [X]
            field_simp [ne_of_gt (Polymer.pointToPlane_pos (criticalBeta ϑ N) 0 n 0 ω)]
      _ = pointToPlane (criticalBeta ϑ N) 0 N 0 ω /
          pointToPlane (criticalBeta ϑ N) 0 n 0 ω := by rw [← h]
      _ = U ω / V ω := by rw [hUeq, hVeq]
  have hXpos (ω : Disorder) : 0 < X ω := by
    rw [hratio]
    exact div_pos (Polymer.smoothedP2Plane_pos _ _ _ _ ω)
      (Polymer.smoothedP2Plane_pos _ _ _ _ ω)
  have hratioMoment := integral_invSqrt_smoothedRatio_le (criticalBeta ϑ N) hβ
    (m := 0) (n := n) (N := N) 0
  have hXint : Integrable (fun ω => X ω ^ (-(1 / 2 : ℝ))) disorderLaw := by
    apply hratioMoment.1.congr
    filter_upwards [] with ω
    rw [hratio]
  have hXbound : ∫ ω, X ω ^ (-(1 / 2 : ℝ)) ∂disorderLaw ≤
      Real.sqrt (∫ ω, U ω ^ 2 ∂disorderLaw) := by
    calc
      _ = ∫ ω, (U ω / V ω) ^ (-(1 / 2 : ℝ)) ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hratio]
      _ ≤ Real.sqrt (∫ ω, U ω ^ 2 ∂disorderLaw) := by
        simpa [U, V] using hratioMoment.2
  have hsecond := hCmomN ϑ hϑ
  have hbound : ∫ ω, X ω ^ (-(1 / 2 : ℝ)) ∂disorderLaw ≤
      Real.sqrt Cmom * Real.sqrt (Real.log (N : ℝ)) := by
    calc
      _ ≤ Real.sqrt (Cmom * Real.log (N : ℝ)) :=
        hXbound.trans (Real.sqrt_le_sqrt hsecond)
      _ = Real.sqrt Cmom * Real.sqrt (Real.log (N : ℝ)) := by
        rw [Real.sqrt_mul hCmompos.le]
  have htail := measure_lt_exp_neg_le_of_integrable_rpow_neg X u
    (Real.sqrt Cmom * Real.sqrt (Real.log (N : ℝ))) hXpos hXint hbound
  simpa [X, Real.sqrt_mul, mul_assoc, div_eq_mul_inv] using htail

/-- An exponential left-tail bound for the smoothed-endpoint log partition function. -/
theorem measure_profileP2Fun_smoothedEndpointDist_lt_le (A : ℝ) :
    ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ u : ℝ, 0 ≤ u →
        (disorderLaw {ω | profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
          (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N))
            (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω < Real.exp (-u)}).toReal ≤
          C * Real.sqrt |Real.log δ| * Real.exp (-u / 2) := by
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_uniform A 1
  obtain ⟨C_R, hC_R⟩ := OnePoint.replicaOverlap_sub_log_bounded
  have hCR : 0 ≤ C_R := by
    have h := hC_R 0 0 (by omega)
    simpa using h
  let D : ℝ := (1 + C_R) / Real.pi
  let Cmom : ℝ := 1 + |C₂| * D / Real.log 2
  have hCmompos : 0 < Cmom := by
    dsimp [Cmom, D]
    positivity
  have hδ₁pos : 0 < Real.exp (-2) := Real.exp_pos _
  refine ⟨Real.exp (-2), Real.sqrt Cmom, hδ₁pos, ?_⟩
  intro δ hδ hδsmall
  have hlogδlt : Real.log δ < -2 :=
    (Real.log_lt_iff_lt_exp hδ).2 (by simpa using hδsmall)
  have hδlt1 : δ < 1 := lt_trans hδsmall (Real.exp_lt_one_iff.mpr (by norm_num))
  have hδsqrtlt1 : Real.sqrt δ < 1 := by
    simpa using (Real.sqrt_lt_sqrt_iff hδ.le).2 hδlt1
  have habslog : 1 ≤ |Real.log δ| := by
    rw [abs_of_neg (lt_trans hlogδlt (by norm_num))]
    linarith
  have hδN : ∀ᶠ N : ℕ in atTop, 1 ≤ δ * (N : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hδ).eventually_ge_atTop 1
  have hmeshδ : ∀ᶠ N : ℕ in atTop, 2 ≤ (1 - δ) * (N : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hδlt1)).eventually_ge_atTop 2
  have hmeshRoot : ∀ᶠ N : ℕ in atTop,
      2 ≤ (1 - Real.sqrt δ) * (N : ℝ) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hδsqrtlt1)).eventually_ge_atTop 2
  have hlogN : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hC₂, hδN, hmeshδ, hmeshRoot, hlogN] with N hC₂N hδN hmeshδ hmeshRoot hlogN
  intro ϑ hϑ u hu
  let m : ℕ := evenCeil (δ * N)
  let n : ℕ := evenCeil (Real.sqrt δ * N)
  let β : ℝ := criticalBeta ϑ N
  let X : Disorder → ℝ := fun ω =>
    profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω
  let U : Disorder → ℝ := fun ω => smoothedP2Plane β m N 0 ω
  let V : Disorder → ℝ := fun ω => smoothedP2Plane β m n 0 ω
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; positivity
  have hδcast : δ * (N : ℝ) ≤ (m : ℝ) := by
    dsimp [m]
    exact Critical2DKPZ.le_evenCeil _
  have hmpos : 1 ≤ m := by
    have h : (1 : ℝ) ≤ (m : ℝ) := hδN.trans hδcast
    exact_mod_cast h
  have hN1 : 1 ≤ N := by
    have hNreal : 0 < (N : ℝ) := by nlinarith [hδN]
    have hNcast : (1 : ℝ) ≤ (N : ℝ) := by nlinarith [hδN, hδlt1]
    exact_mod_cast hNcast
  have hmleN : m ≤ N := by
    have hround := Critical2DKPZ.evenCeil_lt_add_two
      (mul_nonneg hδ.le (Nat.cast_nonneg N))
    have hupper : δ * (N : ℝ) + 2 ≤ (N : ℝ) := by
      nlinarith [hmeshδ]
    have hcast : (m : ℝ) ≤ (N : ℝ) :=
      le_trans hround.le hupper
    exact_mod_cast hcast
  have hrootcast : Real.sqrt δ * (N : ℝ) ≤ (n : ℝ) := by
    dsimp [n]
    exact Critical2DKPZ.le_evenCeil _
  have hnleN : n ≤ N := by
    have hround := Critical2DKPZ.evenCeil_lt_add_two
      (show 0 ≤ Real.sqrt δ * (N : ℝ) from
        mul_nonneg (Real.sqrt_nonneg δ) (Nat.cast_nonneg N))
    have hupper : Real.sqrt δ * (N : ℝ) + 2 ≤ (N : ℝ) := by
      nlinarith [hmeshRoot]
    have hcast : (n : ℝ) ≤ (N : ℝ) :=
      le_trans hround.le hupper
    exact_mod_cast hcast
  have hδsqrt : δ ≤ Real.sqrt δ := by
    exact (Real.le_sqrt hδ.le hδ.le).2 (by nlinarith [hδlt1])
  have hmn : m ≤ n := by
    dsimp [m, n]
    apply Critical2DKPZ.evenCeil_mono
    exact mul_le_mul_of_nonneg_right hδsqrt (Nat.cast_nonneg N)
  have hRdiffnonneg : 0 ≤ Critical2DKPZ.replicaOverlap N -
      Critical2DKPZ.replicaOverlap m := by
    rw [OnePoint.replicaOverlap_sub_eq_sum m N hmleN]
    exact Finset.sum_nonneg fun r hr =>
      Critical2DKPZ.srwKernel_nonneg (2 * r) 0
  have hNcastpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hN1)
  have hmcastpos : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hmpos)
  have hRratio : (N : ℝ) / (m : ℝ) ≤ δ⁻¹ := by
    calc
      (N : ℝ) / (m : ℝ) ≤ (N : ℝ) / (δ * (N : ℝ)) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) (mul_pos hδ hNcastpos) hδcast
      _ = δ⁻¹ := by field_simp [ne_of_gt hδ]
  have hRratioPos : 0 < (N : ℝ) / (m : ℝ) := by
    exact div_pos hNcastpos hmcastpos
  have hlogratio : Real.log ((N : ℝ) / m) ≤ |Real.log δ| := by
    have h := Real.log_le_log hRratioPos hRratio
    calc
      Real.log ((N : ℝ) / m) ≤ -Real.log δ := by simpa [Real.log_inv] using h
      _ = |Real.log δ| := (abs_of_neg (lt_trans hlogδlt (by norm_num))).symm
  have hRdiffbound :
      Critical2DKPZ.replicaOverlap N - Critical2DKPZ.replicaOverlap m ≤
        D * |Real.log δ| := by
    have h := hC_R m N hmleN
    have hmaxm : max m 1 = m := max_eq_left hmpos
    have hmaxN : max N 1 = N := max_eq_left hN1
    have happrox : |Real.pi *
        (Critical2DKPZ.replicaOverlap N - Critical2DKPZ.replicaOverlap m) -
          Real.log ((N : ℝ) / m)| ≤ C_R := by
      simpa [hmaxm, hmaxN] using h
    have hupper := (abs_le.mp happrox).2
    have hsum : Real.pi *
        (Critical2DKPZ.replicaOverlap N - Critical2DKPZ.replicaOverlap m) ≤
          |Real.log δ| + C_R := by
      nlinarith [hlogratio]
    have hprod : 0 ≤ C_R * (|Real.log δ| - 1) :=
      mul_nonneg hCR (by linarith)
    have hRdiffdiv :
        Critical2DKPZ.replicaOverlap N - Critical2DKPZ.replicaOverlap m ≤
          ((1 + C_R) * |Real.log δ|) / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [hsum, hprod, habslog]
    calc
      _ ≤ ((1 + C_R) * |Real.log δ|) / Real.pi := hRdiffdiv
      _ = D * |Real.log δ| := by dsimp [D]; ring
  have hsecond := hC₂N ϑ hϑ m N hmleN (by omega) (by norm_num)
  have hden : Real.log (1 + (N : ℝ) / (N : ℝ)) = Real.log 2 := by
    congr 1
    field_simp
    norm_num
  rw [hden] at hsecond
  have hsecond' :
      ∫ ω, U ω ^ 2 ∂disorderLaw ≤
        1 + |C₂| * ((Critical2DKPZ.replicaOverlap N -
          Critical2DKPZ.replicaOverlap m) / Real.log 2) := by
    have hcoeff : C₂ * ((
        Critical2DKPZ.replicaOverlap N - Critical2DKPZ.replicaOverlap m) /
          Real.log 2) ≤ |C₂| * ((
        Critical2DKPZ.replicaOverlap N - Critical2DKPZ.replicaOverlap m) /
          Real.log 2) :=
      mul_le_mul_of_nonneg_right (le_abs_self C₂)
        (div_nonneg hRdiffnonneg (Real.log_pos (by norm_num)).le)
    have hcoeff' :
        C₂ * (Critical2DKPZ.replicaOverlap N -
          Critical2DKPZ.replicaOverlap m) / Real.log 2 ≤
          |C₂| * ((Critical2DKPZ.replicaOverlap N -
            Critical2DKPZ.replicaOverlap m) / Real.log 2) := by
      convert hcoeff using 1
      ring
    simpa [U] using hsecond.trans (add_le_add le_rfl hcoeff')
  have hsecondBound :
      ∫ ω, U ω ^ 2 ∂disorderLaw ≤ Cmom * |Real.log δ| := by
    have hscale :
        (Critical2DKPZ.replicaOverlap N - Critical2DKPZ.replicaOverlap m) /
          Real.log 2 ≤ D * |Real.log δ| / Real.log 2 :=
      div_le_div_of_nonneg_right hRdiffbound (Real.log_pos (by norm_num)).le
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hfirst : 1 ≤ |Real.log δ| := habslog
    have hC : |C₂| * (D * |Real.log δ| / Real.log 2) =
        (|C₂| * D / Real.log 2) * |Real.log δ| := by ring
    calc
      _ ≤ 1 + |C₂| * ((Critical2DKPZ.replicaOverlap N -
          Critical2DKPZ.replicaOverlap m) / Real.log 2) := hsecond'
      _ ≤ 1 + |C₂| * (D * |Real.log δ| / Real.log 2) := by
        gcongr
      _ ≤ (1 + |C₂| * D / Real.log 2) * |Real.log δ| := by
        rw [hC]
        nlinarith [mul_nonneg (mul_nonneg (abs_nonneg C₂) (div_nonneg hD hlog2.le))
          (sub_nonneg.mpr (show 1 ≤ |Real.log δ| by exact habslog))]
      _ = Cmom * |Real.log δ| := rfl
  have hratioMoment := integral_invSqrt_smoothedRatio_le β hβ
    (m := m) (n := n) (N := N) 0
  have hXratio (ω : Disorder) :
      X ω = U ω / V ω := by
    dsimp [X, U, V]
    exact profileP2Fun_smoothedEndpointDist_eq_div β hmn hnleN 0 ω
  have hXpos (ω : Disorder) : 0 < X ω := by
    rw [hXratio]
    exact div_pos (Polymer.smoothedP2Plane_pos β m N 0 ω)
      (Polymer.smoothedP2Plane_pos β m n 0 ω)
  have hXint : Integrable (fun ω => X ω ^ (-(1 / 2 : ℝ))) disorderLaw := by
    apply hratioMoment.1.congr
    filter_upwards [] with ω
    rw [hXratio]
  have hXbound : ∫ ω, X ω ^ (-(1 / 2 : ℝ)) ∂disorderLaw ≤
      Real.sqrt Cmom * Real.sqrt |Real.log δ| := by
    calc
      _ = ∫ ω, (U ω / V ω) ^ (-(1 / 2 : ℝ)) ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hXratio]
      _ ≤ Real.sqrt (∫ ω, U ω ^ 2 ∂disorderLaw) := by
        simpa [U, V] using hratioMoment.2
      _ ≤ Real.sqrt (Cmom * |Real.log δ|) :=
        Real.sqrt_le_sqrt hsecondBound
      _ = Real.sqrt Cmom * Real.sqrt |Real.log δ| := by
        rw [Real.sqrt_mul hCmompos.le]
  have htail := measure_lt_exp_neg_le_of_integrable_rpow_neg X u
    (Real.sqrt Cmom * Real.sqrt |Real.log δ|) hXpos hXint hXbound
  simpa [X, mul_assoc] using htail

private def finiteWalkSupport (S : Finset Site) (t : ℕ) : Finset Site :=
  S.biUnion (fun w => Polymer.endpoints w t)

private def walkConvolution (S : Finset Site) (η : Site → ℝ) (t : ℕ) (y : Site) : ℝ :=
  ∑ w ∈ S, η w * srwKernel t (y - w)


private theorem walkConvolution_zero_of_not_mem (S : Finset Site) (η : Site → ℝ)
    (t : ℕ) {y : Site} (hy : y ∉ finiteWalkSupport S t) :
    walkConvolution S η t y = 0 := by
  classical
  unfold walkConvolution
  apply Finset.sum_eq_zero
  intro w hw
  have hnot : y ∉ Polymer.endpoints w t := by
    intro hmem
    exact hy (Finset.mem_biUnion.mpr ⟨w, hw, hmem⟩)
  rw [Polymer.srwKernel_eq_zero_of_not_mem t w y hnot, mul_zero]

private theorem walkCollision_sum_eq (S : Finset Site) (η : Site → ℝ)
    (t : ℕ) :
    (∑ w ∈ S, ∑ v ∈ S, η w * η v * srwKernel (2 * t) (v - w)) =
      ∑ y ∈ finiteWalkSupport S t, walkConvolution S η t y ^ 2 := by
  classical
  let T := finiteWalkSupport S t
  have hkernel (w v : Site) (hw : w ∈ S) :
      (∑ y ∈ T, srwKernel t (y - w) * srwKernel t (y - v)) =
        srwKernel (2 * t) (v - w) := by
    have hfinite :
        (∑' y, srwKernel t (y - w) * srwKernel t (y - v)) =
          ∑ y ∈ T, srwKernel t (y - w) * srwKernel t (y - v) := by
      apply tsum_eq_sum
      intro y hy
      have hnot : y ∉ Polymer.endpoints w t := by
        intro hmem
        exact hy (Finset.mem_biUnion.mpr ⟨w, hw, hmem⟩)
      rw [Polymer.srwKernel_eq_zero_of_not_mem t w y hnot, zero_mul]
    rw [← hfinite, Polymer.srwKernel_collision]
  have hsq (y : Site) :
      walkConvolution S η t y ^ 2 =
        ∑ w ∈ S, ∑ v ∈ S,
          η w * η v * (srwKernel t (y - w) * srwKernel t (y - v)) := by
    unfold walkConvolution
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have htotal :
      (∑ y ∈ T, walkConvolution S η t y ^ 2) =
        ∑ w ∈ S, ∑ v ∈ S,
          η w * η v * (∑ y ∈ T,
            srwKernel t (y - w) * srwKernel t (y - v)) := by
    calc
      _ = ∑ y ∈ T, ∑ w ∈ S, ∑ v ∈ S,
          η w * η v * (srwKernel t (y - w) * srwKernel t (y - v)) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact hsq y
      _ = ∑ w ∈ S, ∑ y ∈ T, ∑ v ∈ S,
          η w * η v * (srwKernel t (y - w) * srwKernel t (y - v)) := Finset.sum_comm
      _ = ∑ w ∈ S, ∑ v ∈ S, ∑ y ∈ T,
          η w * η v * (srwKernel t (y - w) * srwKernel t (y - v)) := by
        apply Finset.sum_congr rfl
        intro w hw
        exact Finset.sum_comm
      _ = ∑ w ∈ S, ∑ v ∈ S,
          η w * η v * (∑ y ∈ T,
            srwKernel t (y - w) * srwKernel t (y - v)) := by
        apply Finset.sum_congr rfl
        intro w hw
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mul_sum]
  calc
    (∑ w ∈ S, ∑ v ∈ S, η w * η v * srwKernel (2 * t) (v - w))
        = ∑ w ∈ S, ∑ v ∈ S,
            η w * η v * (∑ y ∈ T,
              srwKernel t (y - w) * srwKernel t (y - v)) := by
          apply Finset.sum_congr rfl
          intro w hw
          apply Finset.sum_congr rfl
          intro v hv
          rw [hkernel w v hw]
    _ = ∑ y ∈ T, walkConvolution S η t y ^ 2 := htotal.symm

private theorem walkConvolution_sq_antitone (S : Finset Site) (η : Site → ℝ)
    {r d : ℕ} (hrd : r ≤ d) :
    (∑ y ∈ finiteWalkSupport S d, walkConvolution S η d y ^ 2) ≤
      ∑ z ∈ finiteWalkSupport S r, walkConvolution S η r z ^ 2 := by
  classical
  let R := finiteWalkSupport S r
  let T := finiteWalkSupport S d
  let U := R ∪ T.biUnion (fun y => Polymer.endpoints y (d - r))
  have hrs : r + (d - r) = d := by omega
  have hRsubU : R ⊆ U := Finset.subset_union_left
  have hUcontains (y : Site) (hy : y ∈ T) :
      Polymer.endpoints y (d - r) ⊆ U := by
    intro z hz
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, hy, hz⟩)
  have hqzero (y z : Site) (hy : y ∈ T)
      (hz : z ∉ Polymer.endpoints y (d - r)) : srwKernel (d - r) (y - z) = 0 := by
    rw [Polymer.srwKernel_sub_swap]
    exact Polymer.srwKernel_eq_zero_of_not_mem (d - r) y z hz
  have hmassU (y : Site) (hy : y ∈ T) :
      (∑ z ∈ U, srwKernel (d - r) (y - z)) = 1 := by
    have hE : Polymer.endpoints y (d - r) ⊆ U := hUcontains y hy
    have hsum : (∑ z ∈ U, srwKernel (d - r) (y - z)) =
        ∑ z ∈ Polymer.endpoints y (d - r), srwKernel (d - r) (y - z) := by
      symm
      apply Finset.sum_subset hE
      intro z hzU hzE
      rw [hqzero y z hy hzE]
    rw [hsum]
    calc
      _ = ∑ z ∈ Polymer.endpoints y (d - r), srwKernel (d - r) (z - y) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact Polymer.srwKernel_sub_swap _ _ _
      _ = 1 := Polymer.sum_srwKernel_endpoints (d - r) y
  have hconv (y : Site) (hy : y ∈ T) :
      walkConvolution S η d y =
        ∑ z ∈ U, srwKernel (d - r) (y - z) * walkConvolution S η r z := by
    unfold walkConvolution
    calc
      _ = ∑ w ∈ S, η w * srwKernel (r + (d - r)) (y - w) := by rw [hrs]
      _ = ∑ w ∈ S, η w *
          (∑' z, srwKernel r (z - w) * srwKernel (d - r) (y - z)) := by
            apply Finset.sum_congr rfl
            intro w hw
            exact congrArg (fun q => η w * q)
              (Polymer.srwKernel_convolution r (d - r) w y)
      _ = ∑ w ∈ S, η w *
          (∑ z ∈ R, srwKernel r (z - w) * srwKernel (d - r) (y - z)) := by
            apply Finset.sum_congr rfl
            intro w hw
            have hfinite :
                (∑' z, srwKernel r (z - w) * srwKernel (d - r) (y - z)) =
                  ∑ z ∈ R, srwKernel r (z - w) * srwKernel (d - r) (y - z) := by
              apply tsum_eq_sum
              intro z hz
              have hnot : z ∉ Polymer.endpoints w r := by
                intro hmem
                exact hz (Finset.mem_biUnion.mpr ⟨w, hw, hmem⟩)
              rw [Polymer.srwKernel_eq_zero_of_not_mem r w z hnot, zero_mul]
            exact congrArg (fun f : ℝ => η w * f) hfinite
      _ = ∑ z ∈ R, srwKernel (d - r) (y - z) *
          (∑ w ∈ S, η w * srwKernel r (z - w)) := by
            calc
              _ = ∑ w ∈ S, ∑ z ∈ R,
                  η w * (srwKernel r (z - w) * srwKernel (d - r) (y - z)) := by
                    apply Finset.sum_congr rfl
                    intro w hw
                    rw [Finset.mul_sum]
              _ = ∑ z ∈ R, ∑ w ∈ S,
                  η w * (srwKernel r (z - w) * srwKernel (d - r) (y - z)) :=
                    Finset.sum_comm
              _ = ∑ z ∈ R, srwKernel (d - r) (y - z) *
                  (∑ w ∈ S, η w * srwKernel r (z - w)) := by
                    apply Finset.sum_congr rfl
                    intro z hz
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro w hw
                    ring
      _ = ∑ z ∈ R, srwKernel (d - r) (y - z) *
          walkConvolution S η r z := by
            apply Finset.sum_congr rfl
            intro z hz
            rfl
      _ = ∑ z ∈ U, srwKernel (d - r) (y - z) *
          walkConvolution S η r z := by
            apply Finset.sum_subset hRsubU
            intro z hzU hzR
            rw [walkConvolution_zero_of_not_mem S η r hzR, mul_zero]
  have hpoint (y : Site) (hy : y ∈ T) :
      walkConvolution S η d y ^ 2 ≤
        ∑ z ∈ U, srwKernel (d - r) (y - z) * walkConvolution S η r z ^ 2 := by
    rw [hconv y hy]
    have hJ :
        (∑ z ∈ U, srwKernel (d - r) (y - z) * walkConvolution S η r z) ^ 2 ≤
          (∑ z ∈ U, srwKernel (d - r) (y - z)) *
            ∑ z ∈ U, srwKernel (d - r) (y - z) * walkConvolution S η r z ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul U
      (r := fun z => srwKernel (d - r) (y - z) * walkConvolution S η r z)
      (f := fun z => srwKernel (d - r) (y - z))
      (g := fun z => srwKernel (d - r) (y - z) * walkConvolution S η r z ^ 2)
      (fun z hz => Critical2DKPZ.srwKernel_nonneg (d - r) (y - z))
      (fun z hz => mul_nonneg (Critical2DKPZ.srwKernel_nonneg (d - r) (y - z))
        (sq_nonneg _))
      (fun z hz => by
        calc
          _ = srwKernel (d - r) (y - z) *
              (srwKernel (d - r) (y - z) * walkConvolution S η r z ^ 2) := by ring
          _ ≤ _ := le_rfl)
    rw [hmassU y hy] at hJ
    simpa only [one_mul] using hJ
  have hsum :
      (∑ y ∈ T, ∑ z ∈ U,
          srwKernel (d - r) (y - z) * walkConvolution S η r z ^ 2) =
        ∑ z ∈ U, walkConvolution S η r z ^ 2 *
          (∑ y ∈ T, srwKernel (d - r) (y - z)) := by
    calc
      _ = ∑ z ∈ U, ∑ y ∈ T,
          srwKernel (d - r) (y - z) * walkConvolution S η r z ^ 2 := Finset.sum_comm
      _ = ∑ z ∈ U, walkConvolution S η r z ^ 2 *
          (∑ y ∈ T, srwKernel (d - r) (y - z)) := by
            apply Finset.sum_congr rfl
            intro z hz
            calc
              _ = (∑ y ∈ T, srwKernel (d - r) (y - z)) *
                  walkConvolution S η r z ^ 2 := by rw [← Finset.sum_mul]
              _ = _ := by ring
  have hmassT (z : Site) :
      (∑ y ∈ T, srwKernel (d - r) (y - z)) ≤ 1 := by
    let E := Polymer.endpoints z (d - r)
    have hzero (y : Site) (hy : y ∉ E) : srwKernel (d - r) (y - z) = 0 :=
      Polymer.srwKernel_eq_zero_of_not_mem (d - r) z y (by simpa [E] using hy)
    have hinter : (∑ y ∈ T, srwKernel (d - r) (y - z)) =
        ∑ y ∈ T ∩ E, srwKernel (d - r) (y - z) := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro y hyT hyNot
      have hyE : y ∉ E := by
        intro hyE
        exact hyNot (Finset.mem_inter.mpr ⟨hyT, hyE⟩)
      rw [hzero y hyE]
    have hsub : (∑ y ∈ T, srwKernel (d - r) (y - z)) ≤
        ∑ y ∈ E, srwKernel (d - r) (y - z) := by
      calc
        _ = ∑ y ∈ T ∩ E, srwKernel (d - r) (y - z) := hinter
        _ ≤ ∑ y ∈ E, srwKernel (d - r) (y - z) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
          intro y hyE hyNot
          exact Critical2DKPZ.srwKernel_nonneg (d - r) (y - z)
    have hEone : (∑ y ∈ E, srwKernel (d - r) (y - z)) = 1 := by
      dsimp [E]
      exact Polymer.sum_srwKernel_endpoints (d - r) z
    rw [hEone] at hsub
    exact hsub
  have hsupport :
      (∑ z ∈ U, walkConvolution S η r z ^ 2) =
        ∑ z ∈ R, walkConvolution S η r z ^ 2 := by
    symm
    apply Finset.sum_subset hRsubU
    intro z hzU hzR
    rw [walkConvolution_zero_of_not_mem S η r hzR, zero_pow (by decide : 2 ≠ 0)]
  calc
    _ = ∑ y ∈ T, walkConvolution S η d y ^ 2 := rfl
    _ ≤ ∑ y ∈ T, ∑ z ∈ U,
          srwKernel (d - r) (y - z) * walkConvolution S η r z ^ 2 :=
        Finset.sum_le_sum fun y hy => hpoint y hy
    _ = ∑ z ∈ U, walkConvolution S η r z ^ 2 *
          (∑ y ∈ T, srwKernel (d - r) (y - z)) := hsum
    _ ≤ ∑ z ∈ U, walkConvolution S η r z ^ 2 * 1 := by
        apply Finset.sum_le_sum
        intro z hz
        exact mul_le_mul_of_nonneg_left (hmassT z)
          (sq_nonneg (walkConvolution S η r z))
    _ = ∑ z ∈ R, walkConvolution S η r z ^ 2 := by
      calc
        _ = ∑ z ∈ U, walkConvolution S η r z ^ 2 := by simp
        _ = _ := hsupport

/-- Zero-mass profiles retain a linear number of collision times in their future energy. -/
theorem futureEnergy_ge_smoothed_sq (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ n : ℕ, 4 * n ≤ N →
      ∀ (η : Site → ℝ) (S : Finset Site), (∀ w ∉ S, η w = 0) → ∑ w ∈ S, η w = 0 →
        c * N * ∑' y, (∑ w ∈ S, η w * srwKernel (N - n) (y - w)) ^ 2 ≤
          futureEnergy (criticalBeta ϑ N) n N η := by
  obtain ⟨c₀, hc₀, hsecond⟩ := sigmaSq_secondMoment_ge A
  have hlogA : ∀ᶠ N : ℕ in atTop, |A| < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |A|
  have hN8 : ∀ᶠ N : ℕ in atTop, 8 ≤ N := eventually_ge_atTop 8
  let c : ℝ := c₀ / 8
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsecond, hlogA, hN8] with N hsecondN hlogAN hN8
  intro ϑ hϑ n hn η S hη hmass
  let β : ℝ := criticalBeta ϑ N
  let d : ℕ := N - n
  have hN1 : 1 ≤ N := by omega
  have hA0 : 0 ≤ A := by rcases hϑ with ⟨hlo, hhi⟩; linarith
  have hθabs : |ϑ| ≤ A := abs_le.mpr ⟨by linarith [hϑ.1], hϑ.2⟩
  have hθlog : |ϑ| < Real.log (N : ℝ) := by
    have hAeq : |A| = A := abs_of_nonneg hA0
    have hθabs' : |ϑ| ≤ |A| := by simpa [hAeq] using hθabs
    exact lt_of_le_of_lt hθabs' hlogAN
  have hspec : Real.exp (β ^ 2) - 1 = Critical2DKPZ.criticalSigmaSq ϑ N := by
    dsimp [β]
    exact OnePoint.criticalBeta_spec_of_abs_lt_log hN1 hθlog
  have hσeq : Polymer.sigmaSq β = Critical2DKPZ.criticalSigmaSq ϑ N := by
    simpa only [Polymer.sigmaSq] using hspec
  have hσnonneg : 0 ≤ Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
  have hnd : n + d = N := by dsimp [d]; omega
  have henergy : futureEnergy β n N η =
      ∑ r ∈ Finset.Icc 1 d,
        ∑ w ∈ S, ∑ v ∈ S,
          η w * η v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw) := by
    rw [← hnd]
    unfold futureEnergy
    have hpfc := Polymer.profile_firstCollision_finset β n d η η S S hη hη
    rw [hmass] at hpfc
    simpa only [pow_two, zero_mul, sub_zero] using hpfc
  have hnormSupport :
      (∑' y, (∑ w ∈ S, η w * srwKernel d (y - w)) ^ 2) =
        ∑ y ∈ finiteWalkSupport S d, walkConvolution S η d y ^ 2 := by
    apply tsum_eq_sum
    intro y hy
    have hzero : (∑ w ∈ S, η w * srwKernel d (y - w)) = 0 := by
      simpa [walkConvolution] using walkConvolution_zero_of_not_mem S η d hy
    rw [hzero, zero_pow (by decide : 2 ≠ 0)]
  have hN4upper : 4 * (N / 4) ≤ N := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self N 4
  have hnleN4 : n ≤ N / 4 := by omega
  have hdle : N / 4 ≤ d := by dsimp [d]; omega
  let Rtime : Finset ℕ := Finset.Icc 1 (N / 4)
  have hRsubset : Rtime ⊆ Finset.Icc 1 d := by
    intro r hr
    simp only [Rtime, Finset.mem_Icc] at hr ⊢
    exact ⟨hr.1, hr.2.trans hdle⟩
  have hRpositive : 1 ≤ N / 4 := by omega
  have hcard : Rtime.card = N / 4 := by
    change (Finset.Icc 1 (N / 4)).card = N / 4
    have hIcc : Finset.Icc 1 (N / 4) = (Finset.range (N / 4 + 1)).erase 0 := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
      omega
    rw [hIcc, Finset.card_erase_of_mem (by simp), Finset.card_range]
    omega
  have hquot : (N : ℝ) / 8 ≤ ((N / 4 : ℕ) : ℝ) := by
    have hdiv : N % 4 + 4 * (N / 4) = N := Nat.mod_add_div N 4
    have hmod : N % 4 < 4 := Nat.mod_lt N (by norm_num)
    have hdivR : ((N % 4 : ℕ) : ℝ) + 4 * ((N / 4 : ℕ) : ℝ) = (N : ℝ) := by
      exact_mod_cast hdiv
    have hmodR : ((N % 4 : ℕ) : ℝ) < 4 := by exact_mod_cast hmod
    have hfloor : (1 : ℝ) ≤ ((N / 4 : ℕ) : ℝ) := by exact_mod_cast hRpositive
    rw [← hdivR]
    nlinarith
  have hcoeff (r : ℕ) (hr : r ∈ Rtime) :
      c₀ ≤ Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw) := by
    have hr' : r ≤ N / 4 := (Finset.mem_Icc.mp hr).2
    have hnr : n ≤ N / 4 := by omega
    have hr4 : 4 * r ≤ N := by
      calc
        4 * r ≤ 4 * (N / 4) := Nat.mul_le_mul_left 4 hr'
        _ ≤ N := hN4upper
    have hkN : N ≤ 4 * (d - r) := by
      have hsum : 4 * n + 4 * r ≤ 2 * N := by omega
      omega
    have hkUpper : d - r ≤ N := by dsimp [d]; omega
    have hsecond := hsecondN ϑ hϑ (d - r) hkN hkUpper
    rw [← hσeq] at hsecond
    exact hsecond
  have hcoeffNonneg (r : ℕ) :
      0 ≤ Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw) :=
    mul_nonneg hσnonneg (integral_nonneg fun ω => sq_nonneg _)
  have hcollisionEnergy : futureEnergy β n N η =
      ∑ r ∈ Finset.Icc 1 d,
        (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) *
          (∑ y ∈ finiteWalkSupport S r, walkConvolution S η r y ^ 2) := by
    rw [henergy]
    apply Finset.sum_congr rfl
    intro r hr
    calc
      _ = ∑ w ∈ S, ∑ v ∈ S,
            (η w * η v * srwKernel (2 * r) (v - w)) *
              (Polymer.sigmaSq β *
                (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) := by
                  apply Finset.sum_congr rfl
                  intro w hw
                  apply Finset.sum_congr rfl
                  intro v hv
                  ring
      _ = (∑ w ∈ S, ∑ v ∈ S,
            η w * η v * srwKernel (2 * r) (v - w)) *
          (Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) := by
              calc
                _ = ∑ w ∈ S,
                    (∑ v ∈ S, η w * η v * srwKernel (2 * r) (v - w)) *
                      (Polymer.sigmaSq β *
                        (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) := by
                          apply Finset.sum_congr rfl
                          intro w hw
                          rw [← Finset.sum_mul]
                _ = _ := by rw [← Finset.sum_mul]
      _ = (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) *
          (∑ y ∈ finiteWalkSupport S r, walkConvolution S η r y ^ 2) := by
            rw [walkCollision_sum_eq]
            ring
  have hnonneg (r : ℕ) :
      0 ≤ (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) *
          (∑ y ∈ finiteWalkSupport S r, walkConvolution S η r y ^ 2) := by
    apply mul_nonneg (hcoeffNonneg r)
    exact Finset.sum_nonneg fun y hy => sq_nonneg _
  have hkeep :
      (∑ r ∈ Rtime, (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) *
          (∑ y ∈ finiteWalkSupport S r, walkConvolution S η r y ^ 2)) ≤
        futureEnergy β n N η := by
    rw [hcollisionEnergy]
    exact Finset.sum_le_sum_of_subset_of_nonneg hRsubset
      (fun r hr hnot => hnonneg r)
  let Dnorm : ℝ := ∑ y ∈ finiteWalkSupport S d, walkConvolution S η d y ^ 2
  have hDnorm : 0 ≤ Dnorm := by dsimp [Dnorm]; positivity
  have hpoint (r : ℕ) (hr : r ∈ Rtime) :
      c₀ * Dnorm ≤
        (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) *
          (∑ y ∈ finiteWalkSupport S r, walkConvolution S η r y ^ 2) := by
    have hle : r ≤ d := by
      exact (Finset.mem_Icc.mp hr).2.trans hdle
    have hcontract := walkConvolution_sq_antitone S η hle
    have hcoeff' := hcoeff r hr
    have hcoeffnn : 0 ≤ Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw) :=
      hcoeffNonneg r
    dsimp [Dnorm]
    calc
      _ ≤ (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) *
          (∑ y ∈ finiteWalkSupport S d, walkConvolution S η d y ^ 2) :=
        mul_le_mul_of_nonneg_right hcoeff' hDnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left hcontract hcoeffnn
  have hconstant :
      c₀ * ((N : ℝ) / 8) * Dnorm ≤
        ∑ r ∈ Rtime, (Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (d - r) 0 ω ^ 2 ∂disorderLaw)) *
          (∑ y ∈ finiteWalkSupport S r, walkConvolution S η r y ^ 2) := by
    calc
      _ ≤ ((N / 4 : ℕ) : ℝ) * (c₀ * Dnorm) := by
        have hcoef : c₀ * ((N : ℝ) / 8) ≤ ((N / 4 : ℕ) : ℝ) * c₀ := by
          calc
            _ ≤ c₀ * ((N / 4 : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hquot hc₀.le
            _ = _ := by ring
        calc
          _ = (c₀ * ((N : ℝ) / 8)) * Dnorm := by ring
          _ ≤ (((N / 4 : ℕ) : ℝ) * c₀) * Dnorm :=
            mul_le_mul_of_nonneg_right hcoef hDnorm
          _ = _ := by ring
      _ = ∑ r ∈ Rtime, c₀ * Dnorm := by
        symm
        rw [Finset.sum_const]
        simp only [nsmul_eq_mul, hcard]
      _ ≤ _ := Finset.sum_le_sum fun r hr => hpoint r hr
  have hfinal : (c₀ / 8) * (N : ℝ) * Dnorm ≤ futureEnergy β n N η :=
    (by
      calc
        _ = c₀ * ((N : ℝ) / 8) * Dnorm := by ring
        _ ≤ _ := hconstant
        _ ≤ _ := hkeep)
  dsimp [Dnorm] at hfinal
  rw [← hnormSupport] at hfinal
  simpa [c, β, d, walkConvolution] using hfinal

end Critical2DKPZ.FutureProfiles

end
