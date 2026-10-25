/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.ProfileLemmaFlow
public import Critical2DKPZ.FutureProfiles.AdaptiveLeftTail
import Critical2DKPZ.Smoothing.EndpointDistribution
import Critical2DKPZ.FutureProfiles.ProfileEstimates
import Critical2DKPZ.Provider.BlockMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Critical2DKPZ.Blocks.OpenDiscrepancyStringBounds
import Critical2DKPZ.OnePoint.BlockRatioOriginalLawEstimates

/-! # Logarithmic moments for profiles with arbitrary heat entrances -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

open FutureProfiles Critical2DKPZ.OnePoint Blocks Collision

/-- An arbitrary heat entrance admits a negative half-moment bound for its future ratio. -/
theorem profile_integral_invSqrt_smoothedRatio_le (β : ℝ) (hβ : 0 ≤ β)
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

/-- Conditional negative half moments for any earlier heat entrance, controlled by the
future energy at an intermediate time. -/
theorem profile_invSqrt_integral_le_of_futureEnergy
    (β : ℝ) (hβ : 0 ≤ β) {a M n N : ℕ} (haM : a ≤ M) (hMn : M ≤ n) (hnN : n ≤ N)
    (G : Set Disorder) (hG : MeasurableSet[disorderPast M] G) (D : ℝ)
    (hD : ∫ ω in G, futureEnergy β M N
      (smoothedEndpointDist β a M 0 ω) ∂disorderLaw ≤ D) :
    IntegrableOn (fun ω =>
      profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) (fun _ => 1) ω ^ (-(1 / 2 : ℝ)))
        G disorderLaw ∧
    (∫ ω in G,
      profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) (fun _ => 1) ω ^ (-(1 / 2 : ℝ))
        ∂disorderLaw) ≤ Real.sqrt D := by
  classical
  let S : Finset Site := (Polymer.endpoints 0 a).biUnion
    (fun y => Polymer.endpoints y (M - a))
  let η : Disorder → Site → ℝ := fun ω w => smoothedEndpointDist β a M 0 ω w
  let P : Disorder → ℝ := fun ω => profileP2Fun β M N (η ω) (fun _ => 1) ω
  let Q : Disorder → ℝ := fun ω => profileP2Fun β M n (η ω) (fun _ => 1) ω
  let X : Disorder → ℝ := fun ω =>
    profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) (fun _ => 1) ω
  have hηsupp : ∀ ω w, w ∉ S → η ω w = 0 := by
    intro ω w hw
    exact (Smoothing.smoothedEndpointDist_probability β haM 0 ω).1 w hw
  have hηnonneg : ∀ ω w, 0 ≤ η ω w := by
    intro ω w
    exact (Smoothing.smoothedEndpointDist_probability β haM 0 ω).2.1 w
  have hηmass : ∀ ω, ∑ w ∈ S, η ω w = 1 := by
    intro ω
    exact (Smoothing.smoothedEndpointDist_probability β haM 0 ω).2.2
  have hηmeas (w : Site) : Measurable[disorderPast M] (η · w) := by
    change Measurable[disorderPast M]
      (fun ω => smoothedEndpointDist β a M 0 ω w)
    exact (Polymer.measurable_smoothedEndpointDist_block β a M haM 0 w).mono
      (Gaussian.disorderBlock_mono (Nat.zero_le a) (le_refl M)) (le_refl _)
  have hηbdd : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B := by
    refine ⟨1, ?_⟩
    intro ω w
    rw [abs_of_nonneg (hηnonneg ω w)]
    by_cases hw : w ∈ S
    · exact (Finset.single_le_sum (fun y hy => hηnonneg ω y) hw).trans_eq (hηmass ω)
    · rw [hηsupp ω w hw]
      norm_num
  have hPmeas : Measurable P := by
    change Measurable (randomFlatProfilePolymer β M N η)
    exact measurable_randomTerminalProfilePolymer β M N S η (fun _ => 1)
      hηsupp hηmeas
  have hQmeas : Measurable Q := by
    change Measurable (randomFlatProfilePolymer β M n η)
    exact measurable_randomTerminalProfilePolymer β M n S η (fun _ => 1)
      hηsupp hηmeas
  have hQint : Integrable Q disorderLaw := by
    change Integrable (randomFlatProfilePolymer β M n η) disorderLaw
    exact integrable_randomTerminalProfilePolymer β M n S η (fun _ => 1)
      hηsupp hηbdd hηmeas 1 (by intro w; simp)
  have hPInvInt : Integrable (fun ω => P ω ^ (-1 : ℝ)) disorderLaw := by
    change Integrable
      (fun ω => profileP2Fun β M N (η ω) (fun _ => 1) ω ^ (-1 : ℝ)) disorderLaw
    exact integrableOn_rpow_neg_profileP2Fun_pastFrozen β (Nat.le_trans hMn hnN)
      η S hηsupp hηnonneg hηmass hηmeas (p := 1) (by norm_num)
  have hPpos (ω : Disorder) : 0 < P ω := by
    exact profileP2Fun_pos_of_normalized β M N (η ω) S (hηsupp ω)
      (hηnonneg ω) (hηmass ω) ω
  have hQpos (ω : Disorder) : 0 < Q ω := by
    exact profileP2Fun_pos_of_normalized β M n (η ω) S (hηsupp ω)
      (hηnonneg ω) (hηmass ω) ω
  have hPInvInt' : Integrable (fun ω => (P ω)⁻¹) disorderLaw := by
    have heq : (fun ω => (P ω)⁻¹) = fun ω => P ω ^ (-1 : ℝ) := by
      funext ω
      rw [Real.rpow_neg_one]
    rw [heq]
    exact hPInvInt
  have hPInvmeas : Measurable (fun ω => (P ω)⁻¹) := hPmeas.inv
  have hPInvnonneg (ω : Disorder) : 0 ≤ (P ω)⁻¹ := inv_nonneg.mpr (hPpos ω).le
  have hQnonneg (ω : Disorder) : 0 ≤ Q ω := (hQpos ω).le
  have hQmean : ∫ ω in G, Q ω ∂disorderLaw ≤ 1 := by
    have hmean := setIntegral_profileP2Fun_eq_sum β hMn η S hηsupp hηbdd hηmeas G hG
    have hmean' : ∫ ω in G, Q ω ∂disorderLaw = ∫ ω in G, (1 : ℝ) ∂disorderLaw := by
      rw [hmean]
      have hpast : disorderPast M ≤ (inferInstance : MeasurableSpace Disorder) := by
        rw [← Gaussian.disorderBlock_zero M]
        exact Gaussian.disorderBlock_le 0 M
      exact setIntegral_congr_fun (hpast G hG) (fun ω _ => hηmass ω)
    rw [hmean']
    calc
      ∫ ω in G, (1 : ℝ) ∂disorderLaw ≤ ∫ ω, (1 : ℝ) ∂disorderLaw :=
        setIntegral_le_integral (integrable_const (1 : ℝ))
          (Filter.Eventually.of_forall fun _ => by norm_num)
      _ = 1 := by simp
  have hProfileInverseMomentInput := setIntegral_rpow_neg_profileP2Fun_le β hβ (Nat.le_trans hMn hnN)
    η S hηsupp hηnonneg hηmass hηmeas G hG (p := 1) (by norm_num)
  have hPInvBound : ∫ ω in G, (P ω)⁻¹ ∂disorderLaw ≤ D := by
    calc
      ∫ ω in G, (P ω)⁻¹ ∂disorderLaw =
          ∫ ω in G,
            profileP2Fun β M N (η ω) (fun _ => 1) ω ^ (-1 : ℝ) ∂disorderLaw := by
              have hpast : disorderPast M ≤ (inferInstance : MeasurableSpace Disorder) := by
                rw [← Gaussian.disorderBlock_zero M]
                exact Gaussian.disorderBlock_le 0 M
              exact setIntegral_congr_fun (hpast G hG) (fun ω _ => by
                dsimp [P]
                rw [Real.rpow_neg_one])
      _ ≤ ∫ ω in G, futureEnergy β M N (η ω) ∂disorderLaw := by
          simpa [Real.rpow_neg_one, Real.rpow_one] using hProfileInverseMomentInput
      _ ≤ D := by simpa [η] using hD
  have hBintG : Integrable Q (disorderLaw.restrict G) := by
    exact hQint.mono_measure Measure.restrict_le_self
  have hAinvIntG : Integrable (fun ω => (P ω)⁻¹) (disorderLaw.restrict G) :=
    hPInvInt'.mono_measure Measure.restrict_le_self
  have hCS := integral_sqrt_mul_sqrt_le_of_integrable
    (μ := disorderLaw.restrict G) Q (fun ω => (P ω)⁻¹)
    hQmeas hPInvmeas hBintG hAinvIntG hQnonneg hPInvnonneg
  have hPdiv (ω : Disorder) : P ω =
      smoothedP2Plane β a N 0 ω / smoothedP2Plane β a M 0 ω := by
    dsimp [P, η]
    exact profileP2Fun_smoothedEndpointDist_eq_div β haM (Nat.le_trans hMn hnN) 0 ω
  have hQdiv (ω : Disorder) : Q ω =
      smoothedP2Plane β a n 0 ω / smoothedP2Plane β a M 0 ω := by
    dsimp [Q, η]
    exact profileP2Fun_smoothedEndpointDist_eq_div β haM hMn 0 ω
  have hXdiv (ω : Disorder) : X ω =
      smoothedP2Plane β a N 0 ω / smoothedP2Plane β a n 0 ω := by
    dsimp [X]
    exact profileP2Fun_smoothedEndpointDist_eq_div β (haM.trans hMn) hnN 0 ω
  have hXratio (ω : Disorder) : X ω = P ω / Q ω := by
    have hUm : 0 < smoothedP2Plane β a M 0 ω :=
      Polymer.smoothedP2Plane_pos β a M 0 ω
    have hUn : 0 < smoothedP2Plane β a n 0 ω :=
      Polymer.smoothedP2Plane_pos β a n 0 ω
    calc
      X ω = smoothedP2Plane β a N 0 ω / smoothedP2Plane β a n 0 ω := hXdiv ω
      _ = (smoothedP2Plane β a N 0 ω / smoothedP2Plane β a M 0 ω) /
          (smoothedP2Plane β a n 0 ω / smoothedP2Plane β a M 0 ω) := by
            field_simp [ne_of_gt hUm, ne_of_gt hUn]
      _ = P ω / Q ω := by rw [← hPdiv ω, ← hQdiv ω]
  have hXpos (ω : Disorder) : 0 < X ω := by
    rw [hXratio ω]
    exact div_pos (hPpos ω) (hQpos ω)
  have hrootEq (ω : Disorder) :
      Real.sqrt (Q ω) * Real.sqrt ((P ω)⁻¹) = X ω ^ (-(1 / 2 : ℝ)) := by
    have hratioRoot :
        Real.sqrt (Q ω) * Real.sqrt ((P ω)⁻¹) = Real.sqrt (Q ω / P ω) := by
      calc
        _ = Real.sqrt (Q ω) / Real.sqrt (P ω) := by rw [Real.sqrt_inv, div_eq_mul_inv]
        _ = Real.sqrt (Q ω / P ω) := (Real.sqrt_div' (Q ω) (hPpos ω).le).symm
    rw [hratioRoot, hXratio ω]
    have hrootPower : Real.sqrt (Q ω / P ω) = (P ω / Q ω) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.div_rpow (hQpos ω).le (hPpos ω).le]
      rw [Real.rpow_neg (div_pos (hPpos ω) (hQpos ω)).le]
      rw [Real.div_rpow (hPpos ω).le (hQpos ω).le]
      field_simp
    exact hrootPower
  have hCSbound :
      (∫ ω in G, X ω ^ (-(1 / 2 : ℝ)) ∂disorderLaw) ≤ Real.sqrt D := by
    have hCSint :
        (∫ ω in G, Real.sqrt (Q ω) * Real.sqrt ((P ω)⁻¹) ∂disorderLaw) ≤
          Real.sqrt (∫ ω in G, Q ω ∂disorderLaw) *
            Real.sqrt (∫ ω in G, (P ω)⁻¹ ∂disorderLaw) := by
      simpa using hCS.2
    have hDnonneg : 0 ≤ D := by
      have henergyNonneg : 0 ≤ ∫ ω in G,
          futureEnergy β M N (smoothedEndpointDist β a M 0 ω) ∂disorderLaw :=
        integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
          futureEnergy_nonneg β M N (smoothedEndpointDist β a M 0 ω))
      exact le_trans henergyNonneg hD
    calc
      _ = ∫ ω in G, Real.sqrt (Q ω) * Real.sqrt ((P ω)⁻¹) ∂disorderLaw := by
        have hpast : disorderPast M ≤ (inferInstance : MeasurableSpace Disorder) := by
          rw [← Gaussian.disorderBlock_zero M]
          exact Gaussian.disorderBlock_le 0 M
        exact setIntegral_congr_fun (hpast G hG) (fun ω _ => (hrootEq ω).symm)
      _ ≤ Real.sqrt (∫ ω in G, Q ω ∂disorderLaw) *
          Real.sqrt (∫ ω in G, (P ω)⁻¹ ∂disorderLaw) := hCSint
      _ ≤ Real.sqrt 1 * Real.sqrt D := by
        apply mul_le_mul (Real.sqrt_le_sqrt hQmean) (Real.sqrt_le_sqrt hPInvBound)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt D := by norm_num
  refine ⟨?_, hCSbound⟩
  have hXintG : Integrable (fun ω => X ω ^ (-(1 / 2 : ℝ)))
      (disorderLaw.restrict G) := by
    exact hCS.1.congr (Filter.Eventually.of_forall fun ω => hrootEq ω)
  simpa [IntegrableOn] using hXintG


/-- Split a lower tail over a good event and its complement. -/
theorem profile_measure_lt_exp_neg_le_of_goodSet
    {μ : Measure Disorder} [IsFiniteMeasure μ] (X : Disorder → ℝ)
    (G : Set Disorder) (u B E : ℝ)
    (hXpos : ∀ ω, 0 < X ω) (hXmeas : Measurable X)
    (hXint : IntegrableOn (fun ω => X ω ^ (-(1 / 2 : ℝ))) G μ)
    (hXbound : ∫ ω in G, X ω ^ (-(1 / 2 : ℝ)) ∂μ ≤ B)
    (hGbad : (μ Gᶜ).toReal ≤ E) :
    (μ {ω | X ω < Real.exp (-u)}).toReal ≤ B * Real.exp (-u / 2) + E := by
  let T : Set Disorder := {ω | X ω < Real.exp (-u)}
  have hTmeas : MeasurableSet T := by
    change MeasurableSet {ω | X ω < Real.exp (-u)}
    exact measurableSet_lt hXmeas measurable_const
  have hXint' : Integrable (fun ω => X ω ^ (-(1 / 2 : ℝ))) (μ.restrict G) := by
    simpa [IntegrableOn] using hXint
  have hXbound' : ∫ ω, X ω ^ (-(1 / 2 : ℝ)) ∂(μ.restrict G) ≤ B := by
    simpa using hXbound
  have htail := measure_lt_exp_neg_le_of_integrable_rpow_neg
    (μ := μ.restrict G) X u B hXpos hXint' hXbound'
  have hrestrict : (μ.restrict G) T = μ (T ∩ G) := Measure.restrict_apply hTmeas
  have hsubset : T ⊆ (T ∩ G) ∪ Gᶜ := by
    intro ω hω
    by_cases hωG : ω ∈ G
    · exact Or.inl ⟨hω, hωG⟩
    · exact Or.inr hωG
  have hmeasure : μ T ≤ μ (T ∩ G) + μ Gᶜ :=
    (measure_mono hsubset).trans (measure_union_le (μ := μ) (T ∩ G) Gᶜ)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ (T ∩ G), measure_ne_top μ Gᶜ⟩) hmeasure
  rw [ENNReal.toReal_add (measure_ne_top μ (T ∩ G)) (measure_ne_top μ Gᶜ)] at hreal
  calc
    (μ T).toReal ≤ ((μ (T ∩ G)).toReal + (μ Gᶜ).toReal) := hreal
    _ = ((μ.restrict G) T).toReal + (μ Gᶜ).toReal := by rw [hrestrict]
    _ ≤ B * Real.exp (-u / 2) + E := by
      exact add_le_add htail hGbad

/-- Combine upper and lower tails of a positive random variable. -/
theorem profile_measure_abs_log_lt_le_of_tails
    {μ : Measure Disorder} [IsFiniteMeasure μ] (X : Disorder → ℝ)
    (u A B : ℝ) (hXpos : ∀ ω, 0 < X ω)
    (hpos : (μ {ω | u < Real.log (X ω)}).toReal ≤ A)
    (hneg : (μ {ω | X ω < Real.exp (-u)}).toReal ≤ B) :
    (μ {ω | u < |Real.log (X ω)|}).toReal ≤ A + B := by
  let P : Set Disorder := {ω | u < Real.log (X ω)}
  let Q : Set Disorder := {ω | X ω < Real.exp (-u)}
  have hsubset : {ω | u < |Real.log (X ω)|} ⊆ P ∪ Q := by
    intro ω hω
    by_cases hlog : 0 ≤ Real.log (X ω)
    · left
      simpa [P, abs_of_nonneg hlog] using hω
    · right
      have hlog' : Real.log (X ω) < 0 := lt_of_not_ge hlog
      have hneglog : u < -Real.log (X ω) := by
        change u < |Real.log (X ω)| at hω
        rw [abs_of_neg hlog'] at hω
        exact hω
      have hlogBound : Real.log (X ω) < -u := by linarith
      exact (Real.log_lt_iff_lt_exp (hXpos ω)).mp hlogBound
  have hmeasure : μ {ω | u < |Real.log (X ω)|} ≤ μ P + μ Q :=
    (measure_mono hsubset).trans (measure_union_le (μ := μ) P Q)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ P, measure_ne_top μ Q⟩) hmeasure
  rw [ENNReal.toReal_add (measure_ne_top μ P) (measure_ne_top μ Q)] at hreal
  calc
    (μ {ω | u < |Real.log (X ω)|}).toReal ≤ (μ P).toReal + (μ Q).toReal := hreal
    _ ≤ A + B := add_le_add hpos hneg

/-- A heat entrance at block `h` is separated from the horizon by at most
`K-h` logarithmic blocks, including the entrance at zero. -/
theorem profile_log_horizon_div_blockTime_le {ρ : ℝ} (hρ : 1 < ρ)
    {N h : ℕ} (hN : 1 ≤ N) (hh : h ≤ blockCount N ρ) :
    Real.log ((N : ℝ) / (max (blockTime N ρ h) 1 : ℕ)) ≤
      ((blockCount N ρ - h : ℕ) : ℝ) * Real.log ρ := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hρ0 : 0 < ρ := zero_lt_one.trans hρ
  by_cases hh0 : h = 0
  · subst h
    simpa [blockTime] using log_le_blockCount_mul_log hρ hN
  by_cases hhK : h < blockCount N ρ
  · have ht : (N : ℝ) * ρ ^ ((h : ℝ) - blockCount N ρ) ≤
        (max (blockTime N ρ h) 1 : ℕ) := by
      calc
        _ ≤ (evenCeil ((N : ℝ) * ρ ^ ((h : ℝ) - blockCount N ρ)) : ℝ) :=
          le_evenCeil _
        _ = (blockTime N ρ h : ℝ) := by rw [blockTime, ite_eq_right hh0, ite_eq_left hhK]
        _ ≤ _ := by exact_mod_cast (le_max_left (blockTime N ρ h) 1)
    have hp : 0 < (N : ℝ) * ρ ^ ((h : ℝ) - blockCount N ρ) := by positivity
    have hmax : 0 < (max (blockTime N ρ h) 1 : ℕ) := by omega
    have hmaxR : 0 < ((max (blockTime N ρ h) 1 : ℕ) : ℝ) := by exact_mod_cast hmax
    have hlog := Real.log_le_log hp ht
    rw [Real.log_mul hN0.ne' (Real.rpow_pos_of_pos hρ0 _).ne',
      Real.log_rpow hρ0] at hlog
    rw [Real.log_div hN0.ne' hmaxR.ne', Nat.cast_sub hh]
    linarith only [hlog]
  · have heq : h = blockCount N ρ := by omega
    have ht : blockTime N ρ h = N := by rw [blockTime, ite_eq_right hh0, ite_eq_right hhK]
    rw [ht, max_eq_left hN, div_self hN0.ne', Real.log_one, heq, Nat.sub_self]
    simp

/-- The right logarithmic tail is uniform in the heat entrance. -/
theorem profile_measure_log_gt_le (β : ℝ) {a n N : ℕ} (han : a ≤ n) (hnN : n ≤ N)
    (u : ℝ) :
    (disorderLaw {ω | u < Real.log
      (smoothedP2Plane β a N 0 ω / smoothedP2Plane β a n 0 ω)}).toReal ≤ Real.exp (-u) := by
  classical
  let η := fun ω w => smoothedEndpointDist β a n 0 ω w
  let S := (Polymer.endpoints 0 a).biUnion (fun y => Polymer.endpoints y (n - a))
  have h := measure_log_profileP2Fun_gt_le β hnN η S
    (fun ω w hw => (Smoothing.smoothedEndpointDist_probability β han 0 ω).1 w hw)
    (fun ω w => (Smoothing.smoothedEndpointDist_probability β han 0 ω).2.1 w)
    (fun ω => (Smoothing.smoothedEndpointDist_probability β han 0 ω).2.2)
    (fun w => (Polymer.measurable_smoothedEndpointDist_block β a n han 0 w).mono
      (Gaussian.disorderBlock_mono (Nat.zero_le a) le_rfl) le_rfl) u
  have heq (ω : Disorder) : profileP2Fun β n N (η ω) (fun _ => 1) ω =
      smoothedP2Plane β a N 0 ω / smoothedP2Plane β a n 0 ω :=
    profileP2Fun_smoothedEndpointDist_eq_div β han hnN 0 ω
  simpa only [heq] using h

/-- The adaptive block choice turns a square-root moment and a reciprocal
exceptional probability into the same exponential logarithmic tail. -/
theorem profile_adaptive_tail_arithmetic {C D u : ℝ} (hC : 0 ≤ C) (hD : 1 ≤ D)
    (hu : 0 ≤ u) :
    let k := Nat.ceil (D * Real.exp (u / 3))
    Real.sqrt (C * (k : ℝ)) * Real.exp (-u / 2) ≤
      Real.sqrt (2 * C) * Real.sqrt D * Real.exp (-u / 3) ∧
    C / (k : ℝ) ≤ C * Real.sqrt D * Real.exp (-u / 3) := by
  intro k
  have he : 1 ≤ Real.exp (u / 3) := Real.one_le_exp (by linarith)
  have hDe : 1 ≤ D * Real.exp (u / 3) := by nlinarith only [mul_le_mul hD he (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ D)]
  have hlo : D * Real.exp (u / 3) ≤ (k : ℝ) := Nat.le_ceil _
  have hhi : (k : ℝ) ≤ 2 * D * Real.exp (u / 3) := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ D * Real.exp (u / 3) by positivity)
    change (k : ℝ) < _ at hceil
    linarith only [hceil, hDe]
  have hfactor : Real.sqrt (2 * C * D * Real.exp (u / 3)) * Real.exp (-u / 2) =
      Real.sqrt (2 * C) * Real.sqrt D * Real.exp (-u / 3) := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * C * D),
      Real.sqrt_mul (by positivity : 0 ≤ 2 * C)]
    rw [Real.sqrt_eq_rpow (Real.exp (u / 3)), ← Real.exp_mul]
    have heq : (u / 3) * (1 / 2 : ℝ) + -u / 2 = -u / 3 := by ring
    rw [mul_assoc, ← Real.exp_add, heq]
  constructor
  · calc
      _ ≤ Real.sqrt (2 * C * D * Real.exp (u / 3)) * Real.exp (-u / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        apply Real.sqrt_le_sqrt
        nlinarith only [mul_le_mul_of_nonneg_left hhi hC]
      _ = _ := hfactor
  · have helo : Real.exp (u / 3) ≤ (k : ℝ) :=
      (le_mul_of_one_le_left (Real.exp_nonneg _) hD).trans hlo
    have hrecip : 1 / (k : ℝ) ≤ Real.exp (-u / 3) := by
      calc
        _ ≤ 1 / Real.exp (u / 3) :=
          div_le_div_of_nonneg_left zero_le_one (Real.exp_pos _) helo
        _ = Real.exp (-u / 3) := by rw [one_div, ← Real.exp_neg]; congr 1; ring
    calc
      _ = C * (1 / (k : ℝ)) := by ring
      _ ≤ C * Real.exp (-u / 3) := mul_le_mul_of_nonneg_left hrecip hC
      _ ≤ _ := by
        have hs := Real.one_le_sqrt.mpr hD
        nlinarith only [mul_le_mul_of_nonneg_left hs
          (mul_nonneg hC (Real.exp_nonneg (-u / 3)))]

/-- The adaptive profile logarithmic tail, uniformly in the initial block.
The profile estimates and the heat-start moments are discharged by the library. -/
theorem profile_log_tail_lattice (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ (C : ℝ) (L : ℕ), 0 ≤ C ∧ 1 ≤ L ∧ ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Icc (-A) A, ∀ r j : ℕ, 1 ≤ r → r ≤ j → j + L ≤ blockCount N ρ →
      ∀ u : ℝ, 0 ≤ u →
        (disorderLaw {ω | u < |Real.log
          (smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (r - 1)) N 0 ω /
           smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (r - 1))
             (blockTime N ρ j) 0 ω)|}).toReal ≤
          C * Real.sqrt ((blockCount N ρ - j : ℕ) : ℝ) * Real.exp (-u / 3) := by
  have hPE : ProfileEstimatesBound := fun A => profile_estimates_of
    (fun A => Blocks.openDiscrepancyMass_sq_integral_le A)
    (fun A => Critical2DKPZ.OnePoint.blockGoodSet_compl_and_ratio_bound_of Provider.blockMoments A) A
  obtain ⟨ρ₀, hρ₀, hPEρ₀⟩ := hPE A
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρle
  have hρ : 1 < ρ := hρ₀.trans_le hρle
  have hlogρ : 0 ≤ Real.log ρ := (Real.log_pos hρ).le
  obtain ⟨Cp, ℓ, hPEρ⟩ := hPEρ₀ ρ
  obtain ⟨Cm, hMoment⟩ := OnePoint.smoothedP2Plane_secondMoment_le_log A 1 1 (by norm_num)
  let B := |Cm| * (1 + Real.log ρ)
  let C := 1 + Real.sqrt (2 * |Cp|) + |Cp| + Real.sqrt (2 * B)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, max ℓ 1, hC, le_max_right _ _, ?_⟩
  filter_upwards [hPEρ ρ ⟨hρle, le_rfl⟩, hMoment, blockTime_monotone hρ,
    eventually_ge_atTop 2] with N hp hm ht hN
  intro ϑ hϑ r j hr hrj hj u hu
  let K := blockCount N ρ
  let t := blockTime N ρ
  let β := criticalBeta ϑ N
  let D : ℝ := ((K - j : ℕ) : ℝ)
  let a := t (r - 1)
  let n := t j
  let X := fun ω => smoothedP2Plane β a N 0 ω / smoothedP2Plane β a n 0 ω
  have hjK : j < K := by dsimp [K]; omega
  have hK0 : K ≠ 0 := by omega
  have htK : t K = N := by simp [t, K, blockTime, hK0]
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast (show 1 ≤ K - j by omega)
  have ht' : Monotone t := ht
  have han : a ≤ n := ht' (by omega)
  have hnN : n ≤ N := (ht' hjK.le).trans_eq htK
  have haN : a ≤ N := han.trans hnN
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; positivity
  have hXpos (ω : Disorder) : 0 < X ω :=
    div_pos (Polymer.smoothedP2Plane_pos β a N 0 ω)
      (Polymer.smoothedP2Plane_pos β a n 0 ω)
  have hXmeas : Measurable X :=
    (Polymer.measurable_smoothedP2Plane β a N 0).div
      (Polymer.measurable_smoothedP2Plane β a n 0)
  let k := Nat.ceil (D * Real.exp (u / 3))
  have he : 1 ≤ Real.exp (u / 3) := Real.one_le_exp (by linarith)
  have hDk : D ≤ (k : ℝ) :=
    (le_mul_of_one_le_right (by linarith : 0 ≤ D) he).trans (Nat.le_ceil _)
  have hDknat : K - j ≤ k := by dsimp [D] at hDk; exact_mod_cast hDk
  have hk1 : 1 ≤ k := by have : (1 : ℝ) ≤ (k : ℝ) := hD.trans hDk; exact_mod_cast this
  have hLeft : (disorderLaw {ω | X ω < Real.exp (-u)}).toReal ≤
      (Real.sqrt (2 * |Cp|) + |Cp| + Real.sqrt (2 * B)) *
        Real.sqrt D * Real.exp (-u / 3) := by
    by_cases hrs : r ≤ K - k
    · let s := K - k
      have hkK : k < K := by dsimp [s] at *; omega
      have hs : r ≤ s := hrs
      have hsj : s ≤ j := by dsimp [s]; omega
      have hsℓ : s + ℓ ≤ K := by
        have hℓD : ℓ ≤ K - j := by dsimp [K] at *; omega
        dsimp [s]; omega
      let G := profileGoodSet β t r s
      have hg := hp ϑ hϑ r s hr hs hsℓ
      have hGpast : MeasurableSet[disorderPast (t s)] G :=
        LogNormality.measurableSet_profileGoodSet_past β ht' hr hs
      have hks : ((blockCount N ρ : ℝ) - s) = (k : ℝ) := by
        have h : blockCount N ρ - s = k := by dsimp [s, K] at *; omega
        rw [← Nat.cast_sub (by dsimp [s, K]; omega), h]
      have henergy : ∫ ω in G, futureEnergy β (t s) N
          (smoothedEndpointDist β a (t s) 0 ω) ∂disorderLaw ≤ |Cp| * (k : ℝ) := by
        have hraw := hg.2.2.2.2
        change _ ≤ Cp * ((blockCount N ρ : ℝ) - s) at hraw
        rw [hks] at hraw
        exact hraw.trans (mul_le_mul_of_nonneg_right (le_abs_self Cp) (Nat.cast_nonneg _))
      have hbad : (disorderLaw Gᶜ).toReal ≤ |Cp| / (k : ℝ) := by
        have hraw := hg.1
        change _ ≤ Cp / ((blockCount N ρ : ℝ) - s) at hraw
        rw [hks] at hraw
        exact hraw.trans (div_le_div_of_nonneg_right (le_abs_self Cp) (Nat.cast_nonneg _))
      have hcond := profile_invSqrt_integral_le_of_futureEnergy β hβ
        (ht' (by omega : r - 1 ≤ s)) (ht' hsj) hnN G hGpast (|Cp| * (k : ℝ)) henergy
      have heq (ω : Disorder) :
          profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) (fun _ => 1) ω = X ω :=
        profileP2Fun_smoothedEndpointDist_eq_div β han hnN 0 ω
      have hcond' : IntegrableOn (fun ω => X ω ^ (-(1 / 2 : ℝ))) G disorderLaw ∧
          (∫ ω in G, X ω ^ (-(1 / 2 : ℝ)) ∂disorderLaw) ≤ Real.sqrt (|Cp| * (k : ℝ)) := by
        change IntegrableOn (fun ω =>
          profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) (fun _ => 1) ω ^ (-(1 / 2 : ℝ))) G disorderLaw ∧
          (∫ ω in G, profileP2Fun β n N (smoothedEndpointDist β a n 0 ω) (fun _ => 1) ω ^ (-(1 / 2 : ℝ)) ∂disorderLaw) ≤ _ at hcond
        simpa only [heq] using hcond
      have htail := profile_measure_lt_exp_neg_le_of_goodSet X G u
        (Real.sqrt (|Cp| * (k : ℝ))) (|Cp| / (k : ℝ)) hXpos hXmeas
        hcond'.1 hcond'.2 hbad
      have harith := profile_adaptive_tail_arithmetic (abs_nonneg Cp) hD hu
      calc
        _ ≤ Real.sqrt (|Cp| * (k : ℝ)) * Real.exp (-u / 2) + |Cp| / (k : ℝ) := htail
        _ ≤ (Real.sqrt (2 * |Cp|) + |Cp|) * Real.sqrt D * Real.exp (-u / 3) := by
          nlinarith only [harith.1, harith.2]
        _ ≤ _ := by
          have := mul_nonneg (Real.sqrt_nonneg (2 * B))
            (mul_nonneg (Real.sqrt_nonneg D) (Real.exp_nonneg (-u / 3)))
          nlinarith only [this]
    · have hkr : K - (r - 1) ≤ k := by omega
      have hlog := profile_log_horizon_div_blockTime_le hρ (by omega : 1 ≤ N)
        (show r - 1 ≤ blockCount N ρ by dsimp [K] at *; omega)
      have hlogk : Real.log ((N : ℝ) / (max a 1 : ℕ)) ≤ (k : ℝ) * Real.log ρ :=
        hlog.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hkr) hlogρ)
      have hlog0 : 0 ≤ Real.log ((N : ℝ) / (max a 1 : ℕ)) := by
        apply Real.log_nonneg
        apply (one_le_div (by positivity : 0 < ((max a 1 : ℕ) : ℝ))).mpr
        exact_mod_cast (max_le haN (by omega : 1 ≤ N))
      have hraw := hm ϑ hϑ a N haN (by simp) (by simp)
      have hmoment : (∫ ω, smoothedP2Plane β a N 0 ω ^ 2 ∂disorderLaw) ≤ B * (k : ℝ) := by
        calc
          _ ≤ Cm * (1 + Real.log ((N : ℝ) / (max a 1 : ℕ))) := hraw
          _ ≤ |Cm| * (1 + Real.log ((N : ℝ) / (max a 1 : ℕ))) :=
            mul_le_mul_of_nonneg_right (le_abs_self Cm) (by linarith)
          _ ≤ B * (k : ℝ) := by
            dsimp [B]
            have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
            nlinarith only [mul_le_mul_of_nonneg_left hlogk (abs_nonneg Cm),
              mul_le_mul_of_nonneg_left hkR (abs_nonneg Cm)]
      obtain ⟨hint, hroot⟩ := profile_integral_invSqrt_smoothedRatio_le β hβ (m := a) (n := n) (N := N) 0
      have htail := measure_lt_exp_neg_le_of_integrable_rpow_neg X u
        (Real.sqrt (B * (k : ℝ))) hXpos hint (hroot.trans (Real.sqrt_le_sqrt hmoment))
      have harith := (profile_adaptive_tail_arithmetic hB hD hu).1
      calc
        _ ≤ Real.sqrt (B * (k : ℝ)) * Real.exp (-u / 2) := htail
        _ ≤ Real.sqrt (2 * B) * Real.sqrt D * Real.exp (-u / 3) := harith
        _ ≤ _ := by
          have := mul_nonneg (add_nonneg (Real.sqrt_nonneg (2 * |Cp|)) (abs_nonneg Cp))
            (mul_nonneg (Real.sqrt_nonneg D) (Real.exp_nonneg (-u / 3)))
          nlinarith only [this]
  have hRight := profile_measure_log_gt_le β han hnN u
  have hRight' : Real.exp (-u) ≤ Real.sqrt D * Real.exp (-u / 3) := by
    have heq := Real.exp_le_exp.mpr (show -u ≤ -u / 3 by linarith)
    exact heq.trans (le_mul_of_one_le_left (Real.exp_nonneg _) (Real.one_le_sqrt.mpr hD))
  have htail := profile_measure_abs_log_lt_le_of_tails X u (Real.exp (-u))
    ((Real.sqrt (2 * |Cp|) + |Cp| + Real.sqrt (2 * B)) * Real.sqrt D * Real.exp (-u / 3))
    hXpos hRight hLeft
  change _ ≤ C * Real.sqrt D * Real.exp (-u / 3)
  dsimp [C]
  nlinarith only [htail, hRight']

/-- Logarithmic ratio tails pass to a positive limiting vector through an
open subset of the positive quadrant. -/
theorem profile_log_tail_le_of_tendstoInDistribution
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    {μ : ℕ → Measure Ω'} {P : Measure Ω}
    [∀ N, IsProbabilityMeasure (μ N)] [IsProbabilityMeasure P]
    {X : ℕ → Ω' → Fin 2 → ℝ} {Y : Ω → Fin 2 → ℝ}
    (hd : TendstoInDistribution X atTop Y μ P)
    (hpos : ∀ᵐ ω ∂P, 0 < Y ω 0 ∧ 0 < Y ω 1)
    {u B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᶠ N in atTop,
      ((μ N) {ω | u < |Real.log (X N ω 0 / X N ω 1)|}).toReal ≤ B) :
    (P {ω | u < |Real.log (Y ω 0 / Y ω 1)|}).toReal ≤ B := by
  let G : Set (Fin 2 → ℝ) := {z | 0 < z 0 ∧ 0 < z 1 ∧ u < |Real.log (z 0 / z 1)|}
  have hG : IsOpen G := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hdiv : ContinuousAt (fun v : Fin 2 → ℝ => v 0 / v 1) z :=
      (continuous_apply 0).continuousAt.div (continuous_apply 1).continuousAt (ne_of_gt hz.2.1)
    have hc : ContinuousAt (fun v : Fin 2 → ℝ => |Real.log (v 0 / v 1)|) z :=
      (hdiv.log (ne_of_gt (div_pos hz.1 hz.2.1))).abs
    have hnear := hc.eventually (Ioi_mem_nhds hz.2.2)
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 0)).mem_nhds hz.1,
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz.2.1, hnear] with y h0 h1 hy
    exact ⟨h0, h1, hy⟩
  have hport : (P.map Y) G ≤ liminf (fun N => ((μ N).map (X N)) G) atTop :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hd.tendsto hG
  have happrox : ∀ᶠ N in atTop, ((μ N).map (X N)) G ≤ ENNReal.ofReal B := by
    filter_upwards [hbound] with N hN
    rw [Measure.map_apply_of_aemeasurable (hd.forall_aemeasurable N) hG.measurableSet]
    apply (measure_mono (show X N ⁻¹' G ⊆ {ω | u < |Real.log (X N ω 0 / X N ω 1)|} from
      fun ω hω => hω.2.2)).trans
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal hB] using hN)
  have hlimit : (P.map Y) G ≤ ENNReal.ofReal B :=
    hport.trans (liminf_le_of_frequently_le happrox.frequently)
  rw [Measure.map_apply_of_aemeasurable hd.aemeasurable_limit hG.measurableSet] at hlimit
  have heq : P (Y ⁻¹' G) = P {ω | u < |Real.log (Y ω 0 / Y ω 1)|} := by
    apply measure_congr
    filter_upwards [hpos] with ω hω
    simp only [mem_preimage, mem_ofPred_eq, G, hω.1, hω.2, true_and]
  rw [heq] at hlimit
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlimit).trans_eq
    (ENNReal.toReal_ofReal hB)

/-- Translation leaves the logarithmic tail of a lattice mass ratio unchanged. -/
theorem profile_log_ratio_tail_spatial (β : ℝ) (a n N : ℕ) (x : Site) (u : ℝ) :
    disorderLaw {ω | u < |Real.log (smoothedP2Plane β a N x ω / smoothedP2Plane β a n x ω)|} =
      disorderLaw {ω | u < |Real.log (smoothedP2Plane β a N 0 ω / smoothedP2Plane β a n 0 ω)|} := by
  let F := fun ω => |Real.log (smoothedP2Plane β a N 0 ω / smoothedP2Plane β a n 0 ω)|
  have hF : Measurable F :=
    ((Polymer.measurable_smoothedP2Plane β a N 0).div
      (Polymer.measurable_smoothedP2Plane β a n 0)).log.abs
  have hm := measurePreserving_disorderShift x
  have heq : {ω | u < |Real.log (smoothedP2Plane β a N x ω / smoothedP2Plane β a n x ω)|} =
      (fun ω p => ω (p.1, p.2 + x)) ⁻¹' {ω | u < F ω} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, F, profile_lattice_heatMass_translate β _ _ x ω]
  rw [heq, ← Measure.map_apply hm.measurable (measurableSet_lt measurable_const hF), hm.map_eq]

/-- At a unit horizon the logarithmic profile tail is uniform over all
geometric-grid entrances before the observation time. -/
theorem profile_log_tail_flow_grid (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ (C : ℝ) (L : ℕ), 0 ≤ C ∧ 1 ≤ L ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (ϑ : ℝ), ϑ ∈ Icc (-A) A →
      IsCriticalSHF ϑ P Z → ∀ ka kn : ℕ, kn < ka → L ≤ kn →
      ∀ x : Plane, ∀ u : ℝ, 0 ≤ u →
        (P {ω | u < |Real.log (profileMass Z (ρ ^ (-(ka : ℝ)))
          (ρ ^ (-(kn : ℝ))) 1 x ω)|}).toReal ≤
            C * Real.sqrt kn * Real.exp (-u / 3) := by
  obtain ⟨ρ₀, hρ₀, hLat⟩ := profile_log_tail_lattice A
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρle
  have hρ : 1 < ρ := hρ₀.trans_le hρle
  obtain ⟨C, L, hC, hL, hBound⟩ := hLat ρ hρle
  refine ⟨C, L, hC, hL, ?_⟩
  intro Ω _ P _ Z ϑ hϑ hZ ka kn hna hLn x u hu
  let τ := fun k : ℕ => ρ ^ (-(k : ℝ))
  have hτpos (k : ℕ) : 0 < τ k := Real.rpow_pos_of_pos (by linarith : 0 < ρ) _
  have han : τ ka < τ kn := Real.rpow_lt_rpow_of_exponent_lt hρ
    (neg_lt_neg (show (kn : ℝ) < ka by exact_mod_cast hna))
  have hn1 : τ kn ≤ 1 := by
    simpa [τ] using Real.rpow_le_rpow_of_exponent_le hρ.le (show -(kn : ℝ) ≤ 0 from neg_nonpos.mpr (Nat.cast_nonneg kn))
  let s : Fin 2 → ℝ := fun _ => τ ka
  let t : Fin 2 → ℝ := ![1, τ kn]
  have hparams : ∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < s i := by
    intro i
    fin_cases i
    · exact ⟨(hτpos ka).le, han.trans_le hn1, hτpos ka⟩
    · exact ⟨(hτpos ka).le, han, hτpos ka⟩
  let X := fun (N : ℕ) (ω : Disorder) (i : Fin 2) => profileP2Fun (criticalBeta ϑ N)
    (evenCeil (N * s i)) (evenCeil (N * t i))
    (fun w => srwKernel (evenCeil (N * s i)) (w - latticePoint N x))
    (cellAverage N fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω
  let Y := fun (ω : Ω) (i : Fin 2) => shfPairing Z (s i) (t i)
    (fun y => heatKernel (s i) (y - x)) (fun y => Real.exp ((0 : Plane →ᵇ ℝ) y)) ω
  have hd : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P :=
    profile_heatStart_joint_tendsto ϑ P Z hZ 2 s t s (fun _ => x) 0 hparams
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by omega : ∀ n : ℕ, n ≤ 2 * n) tendsto_id
  have hdEven : TendstoInDistribution (fun n => X (2 * n)) atTop Y (fun _ => disorderLaw) P :=
    ⟨fun n => hd.forall_aemeasurable (2 * n), hd.aemeasurable_limit, hd.tendsto.comp heven⟩
  have hpos : ∀ᵐ ω ∂P, 0 < Y ω 0 ∧ 0 < Y ω 1 := by
    have h0 := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
      (τ ka) 1 (τ ka) x 0 (hτpos ka).le (han.trans_le hn1) (hτpos ka)
    have h1 := SHF.Positivity.isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
      (τ ka) (τ kn) (τ ka) x 0 (hτpos ka).le han (hτpos ka)
    filter_upwards [h0.1, h1.1] with ω h0 h1
    exact ⟨h0, h1⟩
  have hbound : ∀ᶠ n : ℕ in atTop,
      (disorderLaw {ω | u < |Real.log (X (2 * n) ω 0 / X (2 * n) ω 1)|}).toReal ≤
        C * Real.sqrt kn * Real.exp (-u / 3) := by
    have hK := (blockCount_tendsto_atTop hρ).eventually (eventually_gt_atTop ka)
    filter_upwards [heven.eventually (hBound.and hK), eventually_ge_atTop 1] with n hn hn1'
    let N := 2 * n
    let K := blockCount N ρ
    let r := K - ka + 1
    let j := K - kn
    have hNEven : Even N := ⟨n, by dsimp [N]; omega⟩
    have hN : 0 < N := by dsimp [N]; omega
    obtain ⟨hRate, hka⟩ := hn
    change ka < K at hka
    have hclock (k : ℕ) (hk : k ≤ ka) :
        blockTime N ρ (K - k) = evenCeil (N * τ k) :=
      profile_blockTime_from_horizon hNEven (lt_of_le_of_lt hk hka)
    have hRate' := hRate ϑ hϑ r j (by dsimp only [r]; omega)
      (by dsimp [r, j]; omega) (by change j + L ≤ K; dsimp only [j]; omega) u hu
    have hrclock : blockTime N ρ (r - 1) = evenCeil (N * τ ka) := by
      rw [show r - 1 = K - ka by dsimp only [r]; omega]
      exact hclock ka le_rfl
    have hjclock : blockTime N ρ j = evenCeil (N * τ kn) := hclock kn hna.le
    have hratio (ω : Disorder) : X N ω 0 / X N ω 1 =
        smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (r - 1)) N (latticePoint N x) ω /
          smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (r - 1))
            (blockTime N ρ j) (latticePoint N x) ω := by
      dsimp only [X, s, t, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      simp only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero]
      rw [profile_heatStart_approximant_eq_mass ϑ hN (han.trans_le hn1).le,
        profile_heatStart_approximant_eq_mass ϑ hN han.le, mul_one,
        profile_evenCeil_natCast hNEven, hrclock, hjclock]
    change (disorderLaw {ω | u < |Real.log (X N ω 0 / X N ω 1)|}).toReal ≤ _
    simp_rw [hratio]
    rw [profile_log_ratio_tail_spatial]
    have hD : blockCount N ρ - j = kn := by change K - j = kn; dsimp [j]; omega
    change (disorderLaw {ω | u < |Real.log
      (smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (r - 1)) N 0 ω /
       smoothedP2Plane (criticalBeta ϑ N) (blockTime N ρ (r - 1)) (blockTime N ρ j) 0 ω)|}).toReal ≤
      C * Real.sqrt ((blockCount N ρ - j : ℕ) : ℝ) * Real.exp (-u / 3) at hRate'
    simpa only [hD] using hRate' 
  have h := profile_log_tail_le_of_tendstoInDistribution hdEven hpos
    (by positivity : 0 ≤ C * Real.sqrt kn * Real.exp (-u / 3)) hbound
  simpa [Y, s, t, profileMass, τ] using h
/-- A logarithmic tail prefactor gives an additive logarithmic bound on every finite
positive-order moment. -/
theorem profile_eLpNorm_le_of_exp_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hp_top : p ≠ ∞) {B : ℝ} (hB : 1 ≤ B)
    (hTail : ∀ u : ℝ, 0 ≤ u → (μ {ω | u < |f ω|}).toReal ≤ B * Real.exp (-u / 3)) :
    eLpNorm f p μ ≤ ENNReal.ofReal
      (3 * Real.log B + (p.toReal * 3 ^ p.toReal * Real.Gamma p.toReal) ^ (1 / p.toReal)) := by
  let q : ℝ := p.toReal
  have hqpos : 0 < q := by
    dsimp [q]
    exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top
  have hqge : 1 ≤ q := by
    dsimp [q]
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).2 hp
  have hBpos : 0 < B := by linarith
  let a : ℝ := 3 * Real.log B
  have ha : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by norm_num) (Real.log_nonneg hB)
  have hshift : ∀ u : ℝ, 0 ≤ u → (μ {ω | u < max (|f ω| - a) 0}).toReal ≤ Real.exp (-u / 3) := by
    intro u hu
    have hsub : {ω | u < max (|f ω| - a) 0} ⊆ {ω | a + u < |f ω|} := by
      intro ω hω
      change u < max (|f ω| - a) 0 at hω
      change a + u < |f ω|
      by_cases hnonneg : 0 ≤ |f ω| - a
      · rw [max_eq_left hnonneg] at hω
        linarith
      · rw [max_eq_right (le_of_not_ge hnonneg)] at hω
        exact (not_lt_of_ge hu hω).elim
    have htail := hTail (a + u) (by linarith)
    have hfactor : B * Real.exp (-(a + u) / 3) = Real.exp (-u / 3) := by
      calc
        B * Real.exp (-(a + u) / 3) = Real.exp (Real.log B) * Real.exp (-(a + u) / 3) := by
          rw [Real.exp_log hBpos]
        _ = Real.exp (Real.log B + (-(a + u) / 3)) := (Real.exp_add _ _).symm
        _ = Real.exp (-u / 3) := by congr 1; dsimp [a]; ring
    calc
      (μ {ω | u < max (|f ω| - a) 0}).toReal ≤
          (μ {ω | a + u < |f ω|}).toReal := by
            exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono hsub)
      _ ≤ B * Real.exp (-(a + u) / 3) := htail
      _ = Real.exp (-u / 3) := hfactor
  let Y : Ω → ℝ := fun ω => max (|f ω| - a) 0
  have hYmeas : AEStronglyMeasurable Y μ := by
    have hfabs : AEStronglyMeasurable (fun ω => |f ω|) μ := by
      simpa only [Real.norm_eq_abs] using hf.norm
    have hsub : AEStronglyMeasurable (fun ω => |f ω| + -a) μ :=
      hfabs.add aestronglyMeasurable_const
    exact continuous_max.comp_aestronglyMeasurable
      (hsub.prodMk aestronglyMeasurable_const)
  have hYnn : ∀ ω, 0 ≤ Y ω := fun ω => le_max_right _ _
  have hYmoment : ∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ ≤
      ENNReal.ofReal (q * 3 ^ q * Real.Gamma q) := by
    rw [MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul (μ := μ)
      (Filter.Eventually.of_forall hYnn) hYmeas.aemeasurable hqpos]
    have hkernel : IntegrableOn (fun t : ℝ => t ^ (q - 1) * Real.exp (-(t / 3))) (Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := q - 1) (p := 1) (b := 1 / 3) (by linarith) one_pos (by norm_num)
      simpa [Real.rpow_one, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
    have hkernel_nonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t : ℝ => t ^ (q - 1) * Real.exp (-(t / 3))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_nonneg _)
    have hkernel_int := ofReal_integral_eq_lintegral_ofReal hkernel hkernel_nonneg
    have hkernelval : ∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-(t / 3)) =
        3 ^ q * Real.Gamma q := by
      have hval := Real.integral_rpow_mul_exp_neg_mul_Ioi hqpos (by norm_num : (0 : ℝ) < 1 / 3)
      calc
        ∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-(t / 3)) =
            ∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-((1 / 3 : ℝ) * t)) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro t ht
              ring_nf
        _ = (1 / (1 / 3 : ℝ)) ^ q * Real.Gamma q := hval
        _ = 3 ^ q * Real.Gamma q := by norm_num
    have htailEnn : ∀ t : ℝ, 0 < t → μ {ω | t < Y ω} ≤ ENNReal.ofReal (Real.exp (-t / 3)) := by
      intro t ht
      have h := hshift t ht.le
      have hne : μ {ω | t < Y ω} ≠ ∞ := measure_ne_top μ _
      calc
        μ {ω | t < Y ω} = ENNReal.ofReal (μ {ω | t < Y ω}).toReal :=
          (ENNReal.ofReal_toReal hne).symm
        _ ≤ ENNReal.ofReal (Real.exp (-t / 3)) := ENNReal.ofReal_le_ofReal h
    have hlin : ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
        ENNReal.ofReal (∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-(t / 3))) := by
      calc
        ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
            ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(t / 3))) := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              have htail := htailEnn t ht
              calc
                μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
                    ENNReal.ofReal (Real.exp (-t / 3)) * ENNReal.ofReal (t ^ (q - 1)) :=
                      by gcongr
                _ = ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(t / 3))) := by
                  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
                  have hexp : Real.exp (-t / 3) = Real.exp (-(t / 3)) := by
                    congr 1
                    ring_nf
                  rw [hexp, mul_comm]
        _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0, t ^ (q - 1) * Real.exp (-(t / 3))) := by
              rw [← hkernel_int]
    calc
      ENNReal.ofReal q * ∫⁻ t in Ioi (0 : ℝ), μ {ω | t < Y ω} * ENNReal.ofReal (t ^ (q - 1)) ≤
          ENNReal.ofReal q * ENNReal.ofReal (∫ t : ℝ in Ioi 0,
            t ^ (q - 1) * Real.exp (-(t / 3))) := by
              gcongr
      _ = ENNReal.ofReal (q * 3 ^ q * Real.Gamma q) := by
        rw [← ENNReal.ofReal_mul (by linarith), hkernelval]
        ring_nf
  have hYlp : eLpNorm Y p μ ≤ ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top hYmeas]
    have hintegrand : (fun ω => ‖Y ω‖ₑ ^ p.toReal) =
        (fun ω => ENNReal.ofReal (Y ω ^ q)) := by
      funext ω
      simp [q, Real.enorm_eq_ofReal (hYnn ω),
        ENNReal.ofReal_rpow_of_nonneg (hYnn ω) hqpos.le]
    have hqdef : q = p.toReal := rfl
    have hroot := ENNReal.rpow_le_rpow hYmoment (by positivity : 0 ≤ 1 / q)
    calc
      (∫⁻ ω, ‖Y ω‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) =
          (∫⁻ ω, ENNReal.ofReal (Y ω ^ q) ∂μ) ^ (1 / q) := by
            rw [hintegrand, hqdef]
      _ ≤
          ENNReal.ofReal (q * 3 ^ q * Real.Gamma q) ^ (1 / q) := by
            simpa [q] using hroot
      _ = ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
  have hpoint : ∀ ω, |f ω| ≤ a + Y ω := by
    intro ω
    dsimp [Y]
    calc
      |f ω| = a + (|f ω| - a) := by ring
      _ ≤ a + max (|f ω| - a) 0 := by gcongr; exact le_max_left _ _
  have hmajor : eLpNorm f p μ ≤ eLpNorm (fun ω => a + Y ω) p μ :=
    eLpNorm_mono_real hf hpoint
  have hsum : eLpNorm (fun ω => a + Y ω) p μ ≤
      ENNReal.ofReal a + ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
    calc
      eLpNorm (fun ω => a + Y ω) p μ ≤ eLpNorm (fun _ : Ω => a) p μ + eLpNorm Y p μ := by
        change eLpNorm ((fun _ : Ω => a) + Y) p μ ≤ _
        exact eLpNorm_add_le hp
      _ ≤ ENNReal.ofReal a + ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
        apply add_le_add
        · rw [eLpNorm_const' a (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hp_top]
          simp [Real.enorm_eq_ofReal ha]
        · exact hYlp
  calc
    eLpNorm f p μ ≤ eLpNorm (fun ω => a + Y ω) p μ := hmajor
    _ ≤ ENNReal.ofReal a + ENNReal.ofReal ((q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := hsum
    _ = ENNReal.ofReal (3 * Real.log B + (q * 3 ^ q * Real.Gamma q) ^ (1 / q)) := by
      rw [← ENNReal.ofReal_add ha (by positivity)]


/-- Uniform logarithmic tails at exponential horizons, after scaling the
critical parameter to `log c`. -/
theorem profile_log_tail_flow {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      ∃ (C : ℝ) (L : ℕ), 0 ≤ C ∧ 1 ≤ L ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (l : ℝ) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ ka kn : ℕ, kn < ka → L ≤ kn → ∀ x : Plane, ∀ u : ℝ, 0 ≤ u →
        (P {ω | u < |Real.log (profileMass Z (c * Real.exp l * ρ ^ (-(ka : ℝ)))
          (c * Real.exp l * ρ ^ (-(kn : ℝ))) (c * Real.exp l) x ω)|}).toReal ≤
            C * Real.sqrt kn * Real.exp (-u / 3) := by
  obtain ⟨ρ₀, hρ₀, hBound⟩ := profile_log_tail_flow_grid |Real.log c|
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  obtain ⟨C, L, hC, hL, hB⟩ := hBound ρ hρ
  refine ⟨C, L, hC, hL, ?_⟩
  intro Ω _ P _ l Z hZ ka kn hna hLn x u hu
  let H := c * Real.exp l
  have hH : 0 < H := mul_pos hc (Real.exp_pos l)
  let Z' := fun s t ω => ENNReal.ofReal H⁻¹ • (Z (H * s) (H * t) ω).map
    (fun p => ((Real.sqrt H)⁻¹ • p.1, (Real.sqrt H)⁻¹ • p.2))
  have hZ' : IsCriticalSHF (Real.log c) P Z' := isCriticalSHF_profile_horizon_scaled P hc Z hZ
  have h := hB P Z' (Real.log c) ⟨neg_abs_le _, le_abs_self _⟩ hZ'
    ka kn hna hLn ((Real.sqrt H)⁻¹ • x) u hu
  have hdiv (b : ℝ) : H * b / H = b := by field_simp
  have hscale (ω : Ω) :
      profileMass Z' (ρ ^ (-(ka : ℝ))) (ρ ^ (-(kn : ℝ))) 1 ((Real.sqrt H)⁻¹ • x) ω =
      profileMass Z (H * ρ ^ (-(ka : ℝ))) (H * ρ ^ (-(kn : ℝ))) H x ω := by
    simpa only [hdiv, div_self hH.ne'] using profileMass_scaled_eq Z hH
      (H * ρ ^ (-(ka : ℝ))) (H * ρ ^ (-(kn : ℝ))) H x ω
  simpa only [hscale] using h

/-- A square-root scale prefactor gives logarithmic growth of every fixed
finite-order norm, with a constant independent of the random variable. -/
theorem profile_eLpNorm_le_log_scale {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ⊤)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ),
      AEStronglyMeasurable f P → ∀ l : ℝ, Real.exp 1 ≤ l →
      (∀ u : ℝ, 0 ≤ u → (P {ω | u < |f ω|}).toReal ≤ C * Real.sqrt l * Real.exp (-u / 3)) →
      MemLp f p P ∧ eLpNorm f p P ≤ ENNReal.ofReal (Cp * Real.log l) := by
  let R := (p.toReal * 3 ^ p.toReal * Real.Gamma p.toReal) ^ (1 / p.toReal)
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  let Cp := 3 * Real.log (C + 1) + 3 + R
  have hlogC : 0 ≤ Real.log (C + 1) := Real.log_nonneg (by linarith)
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  refine ⟨Cp, hCp, ?_⟩
  intro Ω _ P _ f hf l hl htail
  have hl1 : 1 ≤ l := (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hl
  have hl0 : 0 < l := by linarith
  have hlogl : 1 ≤ Real.log l := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hl
  have hB : 1 ≤ (C + 1) * l := by nlinarith only [hC, hl1]
  have hsqrt : Real.sqrt l ≤ l := by nlinarith only [Real.sq_sqrt hl0.le, hl1, Real.sqrt_nonneg l]
  have htail' (u : ℝ) (hu : 0 ≤ u) :
      (P {ω | u < |f ω|}).toReal ≤ ((C + 1) * l) * Real.exp (-u / 3) := by
    exact (htail u hu).trans (mul_le_mul_of_nonneg_right
      (by nlinarith only [mul_le_mul_of_nonneg_left hsqrt hC, hl0] : C * Real.sqrt l ≤ (C + 1) * l)
      (Real.exp_nonneg _))
  have hnorm := profile_eLpNorm_le_of_exp_tail hf hp hpTop hB htail'
  have hbound : 3 * Real.log ((C + 1) * l) + R ≤ Cp * Real.log l := by
    rw [Real.log_mul (by positivity : C + 1 ≠ 0) hl0.ne']
    dsimp [Cp]
    nlinarith only [mul_le_mul_of_nonneg_left hlogl
      (show 0 ≤ 3 * Real.log (C + 1) + R by positivity)]
  have hnorm' : eLpNorm f p P ≤ ENNReal.ofReal (Cp * Real.log l) :=
    hnorm.trans (ENNReal.ofReal_le_ofReal hbound)
  exact ⟨hnorm'.trans_lt ENNReal.ofReal_lt_top, hnorm'⟩

/-- Uniform logarithmic profile tails at the padded polynomial horizon. -/
theorem profile_log_tail_polynomial_horizon {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ w : ℝ, 0 < w → w < 1 / 2 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ j : ℕ, ∀ x : Plane, ∀ u : ℝ, 0 ≤ u →
        (P {ω | u < |Real.log (profileMass Z (gridEntrance c ρ l j)
          (S c ρ w l) (c * Real.exp l) x ω)|}).toReal ≤
            min 1 (C * Real.sqrt l * Real.exp (-u / 3)) := by
  obtain ⟨ρ₀, hρ₀, hBound⟩ := profile_log_tail_flow hc
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρle w hw hwHalf
  have hρ := hρ₀.trans_le hρle
  have hρ0 := zero_lt_one.trans hρ
  obtain ⟨C, L, hC, hL, hB⟩ := hBound ρ hρle
  obtain ⟨B, hBpos, hUpper⟩ := grid_remaining_le_linear hc hρ hw hwHalf
  refine ⟨C * Real.sqrt B, by positivity, ?_⟩
  filter_upwards [hUpper, eventually_grid_remaining_ge hc hρ hw hwHalf L,
    eventually_gridJ_le_gridIndex hc hρ hw hwHalf, eventually_gt_atTop (1 : ℝ)]
    with l hUpper hLkn hJ hl
  intro Ω _ P _ Z hZ j x u hu
  let kn := gridIndex c ρ l - gridJ w l
  have hJpos := gridJ_pos hw (by linarith : w < 1) hl
  have hna : kn < gridIndex c ρ l + j := by dsimp [kn]; omega
  have h := hB P l Z hZ (gridIndex c ρ l + j) kn hna hLkn x u hu
  have hS : S c ρ w l = c * Real.exp l * ρ ^ (-(kn : ℝ)) := gridHorizon_eq_geometric hρ0 hJ
  rw [← gridEntrance_eq_geometric hρ0 j, ← hS] at h
  apply le_min
  · simpa only [measureReal_def] using (measureReal_le_one (μ := P)
      (s := {ω | u < |Real.log (profileMass Z (gridEntrance c ρ l j) (S c ρ w l) (c * Real.exp l) x ω)|}))
  · apply h.trans
    have hsqrt : Real.sqrt kn ≤ Real.sqrt B * Real.sqrt l := by
      calc
        _ ≤ Real.sqrt (B * l) := Real.sqrt_le_sqrt hUpper
        _ = _ := Real.sqrt_mul hBpos.le l
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg hC (Real.exp_nonneg (-u / 3)))]

/-- Every finite logarithmic moment is bounded by `C_p log l`, uniformly
in earlier entrances; entrance zero in this grid is the delayed ratio `B`. -/
theorem logMoments_profile {c : ℝ} (hc : 0 < c) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ w : ℝ, 0 < w → w < 1 / 2 →
      ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ᶠ l : ℝ in atTop,
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P],
      ∀ (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)), IsCriticalSHF (-l) P Z →
      ∀ j : ℕ, ∀ x : Plane,
        MemLp (fun ω => Real.log (profileMass Z (gridEntrance c ρ l j)
          (S c ρ w l) (c * Real.exp l) x ω)) p P ∧
        eLpNorm (fun ω => Real.log (profileMass Z (gridEntrance c ρ l j)
          (S c ρ w l) (c * Real.exp l) x ω)) p P ≤ ENNReal.ofReal (Cp * Real.log l) := by
  obtain ⟨ρ₀, hρ₀, hTail⟩ := profile_log_tail_polynomial_horizon hc
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρle w hw hwHalf p hp hpTop
  obtain ⟨C, hC, hTail⟩ := hTail ρ hρle w hw hwHalf
  obtain ⟨Cp, hCp, hNorm⟩ := profile_eLpNorm_le_log_scale hp hpTop hC
  refine ⟨Cp, hCp, ?_⟩
  have hρ := hρ₀.trans_le hρle
  have hρ0 := zero_lt_one.trans hρ
  filter_upwards [hTail, eventually_gridJ_le_gridIndex hc hρ hw hwHalf,
    eventually_grid_remaining_ge hc hρ hw hwHalf 1,
    eventually_ge_atTop (Real.exp 1), eventually_gt_atTop (1 : ℝ)]
    with l hTail hJ hkn hlExp hl
  intro Ω _ P _ Z hZ j x
  let kn := gridIndex c ρ l - gridJ w l
  let ka := gridIndex c ρ l + j
  have hna : kn < ka := by
    have := gridJ_pos hw (by linarith : w < 1) hl
    dsimp [kn, ka]; omega
  have hH : 0 < c * Real.exp l := mul_pos hc (Real.exp_pos l)
  have hE := gridEntrance_eq_geometric (c := c) (l := l) hρ0 j
  have hS : S c ρ w l = c * Real.exp l * ρ ^ (-(kn : ℝ)) :=
    gridHorizon_eq_geometric hρ0 hJ
  have ha : 0 < gridEntrance c ρ l j := by rw [hE]; positivity
  have han : gridEntrance c ρ l j < S c ρ w l := by
    rw [hE, hS]
    apply mul_lt_mul_of_pos_left _ hH
    apply Real.rpow_lt_rpow_of_exponent_lt hρ
    exact neg_lt_neg (by exact_mod_cast hna)
  have haH : gridEntrance c ρ l j < c * Real.exp l := by
    rw [hE]
    apply (mul_lt_iff_lt_one_right hH).mpr
    apply Real.rpow_lt_one_of_one_lt_of_neg hρ
    have hka : 0 < ka := by dsimp [kn, ka] at *; omega
    exact neg_neg_of_pos (by exact_mod_cast hka)
  have hf := (aemeasurable_profileMass P Z hZ ha han haH x).log.aestronglyMeasurable
  exact hNorm P _ hf l hlExp (fun u hu => (hTail P Z hZ j x u hu).trans (min_le_right _ _))

/-- Hölder with exponent four bounds the contribution of an exceptional
set by its probability to the power `3/4`. -/
theorem profile_integral_abs_on_set_le_four {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 4 P)
    {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hnorm : eLpNorm Y 4 P ≤ ENNReal.ofReal L)
    (E : Set Ω) (hE : P E ≤ ENNReal.ofReal δ) :
    (∫ ω in E, |Y ω| ∂P) ≤ L * δ ^ (3 / 4 : ℝ) := by
  have hYr := hY.mono_measure (show P.restrict E ≤ P from Measure.restrict_le_self)
  have hI : Integrable Y (P.restrict E) := hYr.integrable (by norm_num)
  have hc := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 4)
    (by norm_num) hYr.aestronglyMeasurable
  norm_num only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div_one, Measure.restrict_apply_univ] at hc
  have hroot : (P E) ^ (3 / 4 : ℝ) ≤ (ENNReal.ofReal δ) ^ (3 / 4 : ℝ) :=
    ENNReal.rpow_le_rpow hE (by norm_num)
  have hc' : eLpNorm Y 1 (P.restrict E) ≤ ENNReal.ofReal (L * δ ^ (3 / 4 : ℝ)) := by
    apply hc.trans
    calc
      _ ≤ ENNReal.ofReal L * (ENNReal.ofReal δ) ^ (3 / 4 : ℝ) :=
        mul_le_mul' ((eLpNorm_mono_measure Y Measure.restrict_le_self).trans hnorm) hroot
      _ = _ := by rw [ENNReal.ofReal_rpow_of_nonneg hδ (by norm_num), ← ENNReal.ofReal_mul hL]
  have heq : ENNReal.ofReal (∫ ω in E, |Y ω| ∂P) = eLpNorm Y 1 (P.restrict E) := by
    rw [eLpNorm_one_eq_lintegral_enorm hYr.aestronglyMeasurable]
    simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_enorm hI
  rw [← heq] at hc'
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc'
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun ω => abs_nonneg (Y ω)),
    ENNReal.toReal_ofReal (mul_nonneg hL (Real.rpow_nonneg hδ _))] using h

/-- The logarithm is Lipschitz above any positive lower cutoff. -/
theorem profile_abs_log_sub_le_div {a b d : ℝ} (hd : 0 < d) (ha : d ≤ a) (hb : d ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / d := by
  have hforward {u v : ℝ} (hu : d ≤ u) (hv : d ≤ v) (huv : u ≤ v) :
      Real.log v - Real.log u ≤ (v - u) / d := by
    have hu0 := hd.trans_le hu
    have hv0 := hd.trans_le hv
    have h := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
    rw [Real.log_div hv0.ne' hu0.ne'] at h
    calc
      _ ≤ (v - u) / u := by convert h using 1; field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (sub_nonneg.mpr huv) hd hu
  rcases le_total b a with hba | hab
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (hd.trans_le hb) hba)),
      abs_of_nonneg (sub_nonneg.mpr hba)]
    exact hforward hb ha hba
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log (hd.trans_le ha) hab)),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    simpa only [neg_sub] using hforward ha hb hab

/-- A nonnegative majorant separates the local Lipschitz comparison from
large local mass differences. -/
def profileLogComparisonError (r a b : ℝ) : ℝ :=
  (2 / r) * min |a - b| (r / 2) +
    if r / 2 < |a - b| then |Real.log a| + |Real.log b| else 0

theorem profileLogComparisonError_nonneg {r : ℝ} (hr : 0 < r) (a b : ℝ) :
    0 ≤ profileLogComparisonError r a b := by
  unfold profileLogComparisonError
  split_ifs <;> positivity

/-- Above the lower cutoff on the delayed ratio, the majorant controls the
absolute logarithmic difference. -/
theorem profile_abs_log_sub_le_error {r a b : ℝ} (hr : 0 < r) (_ha : 0 < a) (hb : r ≤ b) :
    |Real.log a - Real.log b| ≤ profileLogComparisonError r a b := by
  unfold profileLogComparisonError
  split_ifs with hbad
  · have h := abs_sub (Real.log a) (Real.log b)
    have hcap : 0 ≤ (2 / r) * min |a - b| (r / 2) := by positivity
    linarith only [h, hcap]
  · have hdiff : |a - b| ≤ r / 2 := le_of_not_gt hbad
    have ha' : r / 2 ≤ a := by
      have h := neg_abs_le (a - b)
      linarith only [hdiff, hb, h]
    have h := profile_abs_log_sub_le_div (half_pos hr) ha' (by linarith only [hb, hr] : r / 2 ≤ b)
    rw [min_eq_left hdiff, add_zero]
    convert h using 1; ring

/-- A capped mass comparison and fourth logarithmic moments bound the
expectation of the local logarithmic-error majorant. -/
theorem profile_log_error_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A B : Ω → ℝ}
    (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (hLA : MemLp (fun ω => Real.log (A ω)) 4 P)
    (hLB : MemLp (fun ω => Real.log (B ω)) 4 P)
    {r ε L : ℝ} (hr : 0 < r) (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hnA : eLpNorm (fun ω => Real.log (A ω)) 4 P ≤ ENNReal.ofReal L)
    (hnB : eLpNorm (fun ω => Real.log (B ω)) 4 P ≤ ENNReal.ofReal L)
    (hcap : (∫ ω, min |A ω - B ω| (r / 2) ∂P) ≤ ε) :
    Integrable (fun ω => profileLogComparisonError r (A ω) (B ω)) P ∧
      (∫ ω, profileLogComparisonError r (A ω) (B ω) ∂P) ≤
        (2 / r) * ε + 2 * L * (ε / (r / 2)) ^ (3 / 4 : ℝ) := by
  let X := fun ω => min |A ω - B ω| (r / 2)
  let Y := fun ω => |Real.log (A ω)| + |Real.log (B ω)|
  let E := {ω | r / 2 < |A ω - B ω|}
  have hM : 0 < r / 2 := half_pos hr
  have hX0 (ω : Ω) : 0 ≤ X ω := le_min (abs_nonneg _) hM.le
  have hXm : AEStronglyMeasurable X P := ((hA.sub hB).abs.min aemeasurable_const).aestronglyMeasurable
  have hXi : Integrable X P := by
    apply (integrable_const (r / 2)).mono' hXm
    filter_upwards [] with ω
    rw [Real.norm_of_nonneg (hX0 ω)]
    exact min_le_right _ _
  have hE : NullMeasurableSet E P := nullMeasurableSet_lt aemeasurable_const (hA.sub hB).abs
  have hbad : P E ≤ ENNReal.ofReal (ε / (r / 2)) := by
    have hi := hXi.div_const (r / 2)
    have hnn : 0 ≤ᵐ[P] (fun ω => X ω / (r / 2)) :=
      Eventually.of_forall (fun ω => div_nonneg (hX0 ω) hM.le)
    have ht : ∀ ω ∈ E, 1 ≤ X ω / (r / 2) := by
      intro ω hω
      change r / 2 < |A ω - B ω| at hω
      dsimp only [X]
      rw [min_eq_right hω.le, div_self hM.ne']
    have h := hi.measure_le_integral hnn ht
    rw [integral_div] at h
    exact h.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hcap hM.le))
  have hY4 : MemLp Y 4 P := by
    convert hLA.norm.add hLB.norm using 1
  have hYn : eLpNorm Y 4 P ≤ ENNReal.ofReal (2 * L) := by
    have hna : eLpNorm (fun ω => |Real.log (A ω)|) 4 P ≤ ENNReal.ofReal L := by
      have heq : (fun ω => |Real.log (A ω)|) = fun ω => ‖Real.log (A ω)‖ := by
        funext ω; exact (Real.norm_eq_abs _).symm
      rw [heq, eLpNorm_norm _ hLA.aestronglyMeasurable]
      exact hnA
    have hnb : eLpNorm (fun ω => |Real.log (B ω)|) 4 P ≤ ENNReal.ofReal L := by
      have heq : (fun ω => |Real.log (B ω)|) = fun ω => ‖Real.log (B ω)‖ := by
        funext ω; exact (Real.norm_eq_abs _).symm
      rw [heq, eLpNorm_norm _ hLB.aestronglyMeasurable]
      exact hnB
    calc
      _ ≤ _ + _ := eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal L + ENNReal.ofReal L := add_le_add hna hnb
      _ = _ := by rw [← ENNReal.ofReal_add hL hL]; congr 1; ring
  have hYi : Integrable Y P := hY4.integrable (by norm_num)
  have hEY := profile_integral_abs_on_set_le_four P hY4 (by positivity : 0 ≤ 2 * L)
    (div_nonneg hε hM.le) hYn E hbad
  have hY0 (ω : Ω) : 0 ≤ Y ω := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hEY' : (∫ ω in E, Y ω ∂P) ≤ 2 * L * (ε / (r / 2)) ^ (3 / 4 : ℝ) := by
    simpa only [abs_of_nonneg (hY0 _)] using hEY
  have hIi : Integrable (E.indicator Y) P := hYi.indicator₀ hE
  have heq : (fun ω => profileLogComparisonError r (A ω) (B ω)) =
      fun ω => (2 / r) * X ω + E.indicator Y ω := by
    funext ω
    unfold profileLogComparisonError
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_mem hω]
      change _ + (if r / 2 < |A ω - B ω| then _ else _) = _
      rw [ite_eq_left (show r / 2 < |A ω - B ω| from hω)]
    · rw [Set.indicator_of_notMem hω]
      rw [ite_eq_right (show ¬ r / 2 < |A ω - B ω| from hω)]
  rw [heq]
  refine ⟨(hXi.const_mul _).add hIi, ?_⟩
  rw [integral_add (hXi.const_mul _) hIi, integral_const_mul, integral_indicator₀ hE]
  exact add_le_add (mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 2 / r)) hEY'

/-- A deterministic envelope for the scaled logarithmic-comparison error. -/
def profileLogErrorEnvelope (C L l : ℝ) : ℝ :=
  3 * C * l ^ (-(3 / 8 : ℝ)) +
    2 * L * (3 * C) ^ (3 / 4 : ℝ) * Real.log l * l ^ (-(5 / 32 : ℝ))

/-- The cutoff `l^(-5/8)/2` leaves a strictly decaying error after multiplication by `sqrt l`. -/
theorem profile_log_error_scale_bound {C L l : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hl : 1 ≤ l) :
    let r := l ^ (-(5 / 8 : ℝ))
    let ε := C / (l * Real.sqrt l) + C * (r / 2) / l
    Real.sqrt l * ((2 / r) * ε + 2 * (L * Real.log l) * (ε / (r / 2)) ^ (3 / 4 : ℝ)) ≤
      profileLogErrorEnvelope C L l := by
  intro r ε
  have hl0 : 0 < l := by linarith
  have hr : 0 < r := Real.rpow_pos_of_pos hl0 _
  let δ := (2 / r) * ε
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδr : ε / (r / 2) = δ := by dsimp [δ]; ring
  have hden : r * l * Real.sqrt l = l ^ (7 / 8 : ℝ) := by
    change l ^ (-(5 / 8 : ℝ)) * l * Real.sqrt l = _
    calc
      _ = l ^ (-(5 / 8 : ℝ)) * l ^ (1 : ℝ) * l ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = l ^ (-(5 / 8 : ℝ) + 1 + 1 / 2) := by rw [Real.rpow_add hl0, Real.rpow_add hl0]
      _ = _ := by norm_num
  have hδeq : δ = 2 * C * l ^ (-(7 / 8 : ℝ)) + C / l := by
    calc
      _ = 2 * C / (r * l * Real.sqrt l) + C / l := by dsimp only [δ, ε]; field_simp
      _ = _ := by rw [hden, Real.rpow_neg hl0.le]; ring
  have hInv : l⁻¹ ≤ l ^ (-(7 / 8 : ℝ)) := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hl (by norm_num : (-1 : ℝ) ≤ -(7 / 8 : ℝ))
  have hδ : δ ≤ 3 * C * l ^ (-(7 / 8 : ℝ)) := by
    rw [hδeq]
    have h := mul_le_mul_of_nonneg_left hInv hC
    rw [← div_eq_mul_inv] at h
    linarith only [h]
  have hpow : δ ^ (3 / 4 : ℝ) ≤ (3 * C) ^ (3 / 4 : ℝ) * l ^ (-(21 / 32 : ℝ)) := by
    calc
      _ ≤ (3 * C * l ^ (-(7 / 8 : ℝ))) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hδ0 hδ (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by positivity : 0 ≤ 3 * C) (Real.rpow_nonneg hl0.le _),
          ← Real.rpow_mul hl0.le]
        norm_num
  have hid1 : Real.sqrt l * l ^ (-(7 / 8 : ℝ)) = l ^ (-(3 / 8 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hl0]; norm_num
  have hid2 : Real.sqrt l * l ^ (-(21 / 32 : ℝ)) = l ^ (-(5 / 32 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hl0]; norm_num
  rw [hδr]
  change Real.sqrt l * (δ + 2 * (L * Real.log l) * δ ^ (3 / 4 : ℝ)) ≤ _
  calc
    _ ≤ Real.sqrt l * (3 * C * l ^ (-(7 / 8 : ℝ)) +
        2 * (L * Real.log l) * ((3 * C) ^ (3 / 4 : ℝ) * l ^ (-(21 / 32 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (add_le_add hδ (mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (by norm_num) (mul_nonneg hL (Real.log_nonneg hl))))) (Real.sqrt_nonneg _)
    _ = 3 * C * (Real.sqrt l * l ^ (-(7 / 8 : ℝ))) +
        2 * L * (3 * C) ^ (3 / 4 : ℝ) * Real.log l * (Real.sqrt l * l ^ (-(21 / 32 : ℝ))) := by ring
    _ = _ := by rw [hid1, hid2]; rfl

/-- The logarithmic-comparison envelope vanishes at large scales. -/
theorem profileLogErrorEnvelope_tendsto (C L : ℝ) :
    Tendsto (profileLogErrorEnvelope C L) atTop (𝓝 0) := by
  have hpow := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 8)
  have hlog := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 32)).tendsto_div_nhds_zero
  have hlog' : Tendsto (fun l : ℝ => Real.log l * l ^ (-(5 / 32 : ℝ))) atTop (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with l hl
    rw [Real.rpow_neg hl.le]
    ring
  have h := (hpow.const_mul (3 * C)).add (hlog'.const_mul (2 * L * (3 * C) ^ (3 / 4 : ℝ)))
  have h' : Tendsto (fun l : ℝ => 3 * C * l ^ (-(3 / 8 : ℝ)) +
      (2 * L * (3 * C) ^ (3 / 4 : ℝ)) * (Real.log l * l ^ (-(5 / 32 : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using h
  apply h'.congr'
  filter_upwards [] with l
  dsimp only [profileLogErrorEnvelope]
  ring

/-- The logarithmic comparison majorant is a Borel function of the two masses. -/
theorem measurable_profileLogComparisonError (r : ℝ) :
    Measurable (fun p : ℝ × ℝ => profileLogComparisonError r p.1 p.2) := by
  unfold profileLogComparisonError
  have hd : Measurable (fun p : ℝ × ℝ => |p.1 - p.2|) := (measurable_fst.sub measurable_snd).abs
  have hy : Measurable (fun p : ℝ × ℝ => |Real.log p.1| + |Real.log p.2|) :=
    (Real.measurable_log.comp measurable_fst).abs.add (Real.measurable_log.comp measurable_snd).abs
  exact (measurable_const.mul (hd.min measurable_const)).add
    (Measurable.ite (measurableSet_lt measurable_const hd) hy measurable_const)

end Critical2DKPZ.Extensions.GffTangent

end
