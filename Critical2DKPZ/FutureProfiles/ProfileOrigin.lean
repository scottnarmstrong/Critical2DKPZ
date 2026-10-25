/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.OriginComparison
public import Critical2DKPZ.FutureProfiles.SplitInputs
public import Critical2DKPZ.FutureProfiles.WeightedOriginComparison
import Mathlib.Tactic

/-! # The origin profile comparison -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer

private theorem profileP2Fun_sub_eq (β : ℝ) (a b : ℕ) (ν₀ ν₁ f : Site → ℝ)
    (S : Finset Site) (hν₀ : ∀ w ∉ S, ν₀ w = 0) (hν₁ : ∀ w ∉ S, ν₁ w = 0)
    (ω : Disorder) :
    profileP2Fun β a b (ν₀ - ν₁) f ω =
      profileP2Fun β a b ν₀ f ω - profileP2Fun β a b ν₁ f ω := by
  rw [Polymer.profileP2Fun_eq_sum β a b (ν₀ - ν₁) f S
      (fun w hw => by simp [hν₀ w hw, hν₁ w hw]),
    Polymer.profileP2Fun_eq_sum β a b ν₀ f S hν₀,
    Polymer.profileP2Fun_eq_sum β a b ν₁ f S hν₁]
  calc
    ∑ w ∈ S, (ν₀ w - ν₁ w) * (∑' z, pointToPoint β a (b - a) w z ω * f z) =
        ∑ w ∈ S, (ν₀ w * (∑' z, pointToPoint β a (b - a) w z ω * f z) -
          ν₁ w * (∑' z, pointToPoint β a (b - a) w z ω * f z)) := by
            apply Finset.sum_congr rfl
            intro w hw
            ring
    _ = _ := by rw [Finset.sum_sub_distrib]

private theorem weighted_profile_origin_bound
    (β ρ D s L C cE Cball Ctail ctail Rcore R : ℝ) (m n N J : ℕ)
    (S : Finset Site) (U₀ U₁ η : Disorder → Site → ℝ) (G : Set Disorder)
    (f : Site → ℝ) (M : ℝ)
    (hCardBall : ∀ r : ℝ, 1 ≤ r →
      (((Critical2DKPZ.MomentBounds.boxSites ⌈r⌉₊).filter
        fun y => ‖siteToPlane y‖ ≤ r).card : ℝ) ≤ Cball * r ^ 2)
    (hnN : n ≤ N) (hN : 1 ≤ N) (hcE : 0 < cE)
    (hCball : 0 ≤ Cball)
    (hηsupport : ∀ ω y, y ∉ S → η ω y = 0)
    (hηmass : ∀ ω, ∑ y ∈ S, η ω y = 0)
    (hηbound : ∃ B : ℝ, ∀ ω y, |η ω y| ≤ B)
    (hηmeas : ∀ y, Measurable[disorderPast n] (η · y))
    (hU₀support : ∀ ω y, y ∉ S → U₀ ω y = 0)
    (hU₁support : ∀ ω y, y ∉ S → U₁ ω y = 0)
    (hU₀mass : ∀ ω, ∑ y ∈ S, U₀ ω y = 1)
    (hU₁mass : ∀ ω, ∑ y ∈ S, U₁ ω y = 1)
    (hU₀nonneg : ∀ ω y, 0 ≤ U₀ ω y) (hU₁nonneg : ∀ ω y, 0 ≤ U₁ ω y)
    (hU₁eq : ∀ ω y, U₁ ω y = smoothedEndpointDist β m n 0 ω y)
    (hηdiff : ∀ ω y, η ω y = U₀ ω y - U₁ ω y)
    (hG : MeasurableSet[disorderPast n] G)
    (hRootInt : IntegrableOn (fun ω => Real.sqrt (futureEnergy β n N (η ω))) G disorderLaw)
    (hRootBound : ∫ ω in G, Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw ≤ Rcore / J)
    (hEnergy : ∀ ω, cE * (N : ℝ) *
      (∑' y, (finiteWalkConvolution (N - n) S (η ω) y) ^ 2) ≤
        futureEnergy β n N (η ω))
    (hTailInt : Integrable (smoothedEndpointTailMass β m n N R) disorderLaw)
    (hTailBound : ∫ ω, smoothedEndpointTailMass β m n N R ω ∂disorderLaw ≤
      Ctail * Real.exp (-ctail * R ^ 2))
    (hR : 1 ≤ R) (hRdef : R = D * s) (hD : 1 ≤ D)
    (hDtail : 1 ≤ ctail * D ^ 2)
    (hsSq : s ^ 2 = Real.log L) (hsge1 : 1 ≤ s) (hLpos : 0 < L)
    (hρ : 1 < ρ) (hJrecip : 1 / (J : ℝ) ≤ 4 * Real.log ρ / L)
    (hRcore : 0 ≤ Rcore)
    (hCoeff : 16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
      2 * |Ctail| + 4 * Real.log ρ * Rcore ≤ C)
    (hf : ∀ y, |f y| ≤ M) :
    ∫ ω in G, |profileP2Fun β n N (U₀ ω) f ω -
      profileP2Fun β n N (U₁ ω) f ω| ∂disorderLaw ≤ C * M * s / L := by
  have hsnonneg : 0 ≤ s := by linarith [hsge1]
  have hlogLnonneg : 0 ≤ Real.log L := by
    rw [← hsSq]
    positivity
  have hRsq : Real.log L ≤ ctail * R ^ 2 := by
    calc
      Real.log L = 1 * Real.log L := by ring
      _ ≤ (ctail * D ^ 2) * Real.log L :=
        mul_le_mul_of_nonneg_right hDtail hlogLnonneg
      _ = ctail * R ^ 2 := by rw [hRdef, mul_pow, hsSq]; ring
  have htailExp : Real.exp (-ctail * R ^ 2) ≤ 1 / L := by
    calc
      Real.exp (-ctail * R ^ 2) ≤ Real.exp (-Real.log L) :=
        Real.exp_le_exp.mpr (by nlinarith [hRsq])
      _ = 1 / L := by rw [Real.exp_neg, Real.exp_log hLpos]; simp [one_div]
  have hMnonneg : 0 ≤ M := (abs_nonneg (f 0)).trans (hf 0)
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρ
  have htargetFactor : 0 ≤ M * s / L := by positivity
  have hlocalBound := weighted_origin_drift_le β m n N S U₀ U₁ η G f M R
    cE Cball Ctail ctail Rcore J hCardBall hnN hN hcE hCball hηsupport hηbound
    hηmeas hU₁support hU₀mass hU₁mass hU₀nonneg hU₁nonneg hU₁eq hηdiff
    hRootInt hRootBound hEnergy hTailInt hTailBound hR hf
  have hprofileBound := setIntegral_abs_profileP2Fun_weighted_le β hnN η S
    hηsupport hηbound hηmeas hηmass f M hf G hG
  let drift : Disorder → ℝ := fun ω =>
    |∑' y, (finiteWalkConvolution (N - n) S (η ω) y) * f y|
  have hprofileEq (ω : Disorder) :
      profileP2Fun β n N (U₀ ω) f ω - profileP2Fun β n N (U₁ ω) f ω =
        profileP2Fun β n N (η ω) f ω := by
    have hηfun : η ω = U₀ ω - U₁ ω := by
      funext y
      exact hηdiff ω y
    rw [hηfun]
    exact (profileP2Fun_sub_eq β n N (U₀ ω) (U₁ ω) f S
      (hU₀support ω) (hU₁support ω) ω).symm
  have hprofileAEMod :
      (fun ω => |profileP2Fun β n N (U₀ ω) f ω - profileP2Fun β n N (U₁ ω) f ω|) =ᵐ[
        disorderLaw.restrict G] (fun ω => |profileP2Fun β n N (η ω) f ω|) := by
    filter_upwards [] with ω
    rw [hprofileEq ω]
  have hdriftEq : (fun ω =>
      |∑' y, (∑ w ∈ S, η ω w * srwKernel (N - n) (y - w)) * f y|) = drift := by
    funext ω
    apply congrArg abs
    apply tsum_congr
    intro y
    rfl
  have hRootInt' : IntegrableOn
      (fun ω => Real.sqrt (futureEnergy β n N (η ω))) G disorderLaw := hRootInt
  have hDriftInt : IntegrableOn drift G disorderLaw := by
    have hcomp := integrableOn_abs_profileP2Fun_weighted_le β hnN η S
      hηsupport hηbound hηmeas f M hf G
    have hsum := hcomp.2
    have hsumEq : (fun ω => drift ω + M * Real.sqrt (futureEnergy β n N (η ω))) =
        (fun ω => |∑' y, (∑ w ∈ S, η ω w * srwKernel (N - n) (y - w)) * f y| +
          M * Real.sqrt (futureEnergy β n N (η ω))) := by
      funext ω
      rw [← hdriftEq]
    have hsum' : IntegrableOn (fun ω =>
        drift ω + M * Real.sqrt (futureEnergy β n N (η ω))) G disorderLaw := by
      simpa using hsumEq ▸ hsum
    exact (integrable_add_iff_integrable_left' (hRootInt.const_mul M)).1 hsum'
  have hprofileIntegral :
      ∫ ω in G, |profileP2Fun β n N (U₀ ω) f ω - profileP2Fun β n N (U₁ ω) f ω|
        ∂disorderLaw ≤
      ∫ ω in G, drift ω + M * Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw := by
    calc
      _ = ∫ ω in G, |profileP2Fun β n N (η ω) f ω| ∂disorderLaw :=
        integral_congr_ae hprofileAEMod
      _ ≤ _ := by simpa [drift, finiteWalkConvolution] using hprofileBound
  have hsumIntegral :
      ∫ ω in G, drift ω + M * Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw =
        (∫ ω in G, drift ω ∂disorderLaw) +
          M * (∫ ω in G, Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw) := by
    rw [integral_add hDriftInt (hRootInt'.const_mul M), integral_const_mul]
  have hmainBound :
      ∫ ω in G, |profileP2Fun β n N (U₀ ω) f ω - profileP2Fun β n N (U₁ ω) f ω|
        ∂disorderLaw ≤
      2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) +
        |Ctail| * Real.exp (-ctail * R ^ 2)) + M * (Rcore / J) := by
    calc
      _ ≤ ∫ ω in G, drift ω + M * Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw :=
        hprofileIntegral
      _ = _ := hsumIntegral
      _ ≤ 2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) +
          |Ctail| * Real.exp (-ctail * R ^ 2)) + M * (Rcore / J) :=
        add_le_add hlocalBound.2 (mul_le_mul_of_nonneg_left hRootBound hMnonneg)
  have hrootCoeff : M * (Rcore / J) ≤
      (4 * Real.log ρ * Rcore) * M * s / L := by
    have hscale := mul_le_mul_of_nonneg_left hJrecip (mul_nonneg hMnonneg hRcore)
    have hbase : M * Rcore * (1 / (J : ℝ)) ≤
        M * Rcore * (4 * Real.log ρ / L) := hscale
    have hcoef : 0 ≤ (4 * Real.log ρ * Rcore * M) / L := by positivity
    calc
      M * (Rcore / J) = M * Rcore * (1 / (J : ℝ)) := by ring
      _ ≤ M * Rcore * (4 * Real.log ρ / L) := hbase
      _ = ((4 * Real.log ρ * Rcore * M) / L) := by ring
      _ = ((4 * Real.log ρ * Rcore * M) / L) * 1 := by ring
      _ ≤ ((4 * Real.log ρ * Rcore * M) / L) * s :=
        mul_le_mul_of_nonneg_left hsge1 hcoef
      _ = (4 * Real.log ρ * Rcore) * M * s / L := by ring
  have hlocalCoeff :
      2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J)) ≤
        (16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore) *
          M * s / L := by
    have hcoef : 0 ≤ 2 * M * Real.sqrt Cball * D * s / Real.sqrt cE * Rcore := by
      positivity
    calc
      2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J)) =
          (2 * M * Real.sqrt Cball * D * s / Real.sqrt cE * Rcore) *
            (1 / (J : ℝ)) := by rw [hRdef]; ring
      _ ≤ (2 * M * Real.sqrt Cball * D * s / Real.sqrt cE * Rcore) *
          (4 * Real.log ρ / L) := mul_le_mul_of_nonneg_left hJrecip hcoef
      _ = (8 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore) *
          M * s / L := by ring
      _ ≤ (16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore) *
          M * s / L := by
        have hbase : 8 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore ≤
            16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore := by
          have hnonneg : 0 ≤ Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore :=
            by positivity
          calc
            _ = 8 * (Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore) := by ring
            _ ≤ 16 * (Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore) :=
              mul_le_mul_of_nonneg_right (by norm_num) hnonneg
            _ = _ := by ring
        calc
          _ = (8 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore) *
              (M * s / L) := by ring
          _ ≤ (16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore) *
              (M * s / L) := mul_le_mul_of_nonneg_right hbase htargetFactor
          _ = _ := by ring
  have htailCoeff : 2 * M * (|Ctail| * Real.exp (-ctail * R ^ 2)) ≤
      (2 * |Ctail|) * M * s / L := by
    have hinner := mul_le_mul_of_nonneg_left htailExp (abs_nonneg Ctail)
    have hscaled := mul_le_mul_of_nonneg_left hinner (by positivity : 0 ≤ 2 * M)
    have hcoef : 0 ≤ (2 * |Ctail| * M) / L := by positivity
    calc
      2 * M * (|Ctail| * Real.exp (-ctail * R ^ 2)) ≤
          2 * M * (|Ctail| * (1 / L)) := hscaled
      _ = (2 * |Ctail| * M) / L := by ring
      _ = ((2 * |Ctail| * M) / L) * 1 := by ring
      _ ≤ ((2 * |Ctail| * M) / L) * s := mul_le_mul_of_nonneg_left hsge1 hcoef
      _ = (2 * |Ctail|) * M * s / L := by ring
  calc
    _ ≤ 2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J) +
        |Ctail| * Real.exp (-ctail * R ^ 2)) + M * (Rcore / J) := hmainBound
    _ ≤ C * M * s / L := by
      calc
        _ = 2 * M * ((Real.sqrt Cball * R / Real.sqrt cE) * (Rcore / J)) +
            2 * M * (|Ctail| * Real.exp (-ctail * R ^ 2)) + M * (Rcore / J) := by ring
        _ ≤ (16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore) *
              M * s / L + (2 * |Ctail|) * M * s / L +
              (4 * Real.log ρ * Rcore) * M * s / L :=
          add_le_add (add_le_add hlocalCoeff htailCoeff) hrootCoeff
        _ = (16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
              2 * |Ctail| + 4 * Real.log ρ * Rcore) * (M * s / L) := by ring
        _ ≤ C * (M * s / L) := mul_le_mul_of_nonneg_right hCoeff htargetFactor
        _ = C * M * s / L := by ring

private theorem weighted_origin_profile_from_data
    (β ρ D C Cball Ctail ctail cE Rcore : ℝ) (δ L : ℝ)
    (m n N J : ℕ) (S : Finset Site) (U₀ U₁ η : Disorder → Site → ℝ)
    (G : Set Disorder) (hρ : 1 < ρ) (hD : 1 ≤ D)
    (hDtail : 1 ≤ ctail * D ^ 2) (hJrecip : 1 / (J : ℝ) ≤ 4 * Real.log ρ / L)
    (hδlog : 2 < Real.log |Real.log δ|) (hL : L = |Real.log δ|)
    (hLpos : 0 < L)
    (hRcore : 0 ≤ Rcore)
    (hnN : n ≤ N) (hN : 1 ≤ N) (hmn : m ≤ n) (hβ : 0 ≤ β)
    (hcE : 0 < cE) (hCball : 0 ≤ Cball)
    (hCardBall : ∀ r : ℝ, 1 ≤ r →
      (((Critical2DKPZ.MomentBounds.boxSites ⌈r⌉₊).filter
        fun y => ‖siteToPlane y‖ ≤ r).card : ℝ) ≤ Cball * r ^ 2)
    (hηsupport : ∀ ω y, y ∉ S → η ω y = 0)
    (hηmass : ∀ ω, ∑ y ∈ S, η ω y = 0)
    (hηbound : ∃ B : ℝ, ∀ ω y, |η ω y| ≤ B)
    (hηmeas : ∀ y, Measurable[disorderPast n] (η · y))
    (hU₀support : ∀ ω y, y ∉ S → U₀ ω y = 0)
    (hU₁support : ∀ ω y, y ∉ S → U₁ ω y = 0)
    (hU₀mass : ∀ ω, ∑ y ∈ S, U₀ ω y = 1)
    (hU₁mass : ∀ ω, ∑ y ∈ S, U₁ ω y = 1)
    (hU₀nonneg : ∀ ω y, 0 ≤ U₀ ω y) (hU₁nonneg : ∀ ω y, 0 ≤ U₁ ω y)
    (hU₀eq : ∀ ω, U₀ ω = smoothedEndpointDist β 0 n 0 ω)
    (hU₁eq : ∀ ω y, U₁ ω y = smoothedEndpointDist β m n 0 ω y)
    (hηdiff : ∀ ω y, η ω y = U₀ ω y - U₁ ω y)
    (hGmeas : MeasurableSet[disorderPast n] G)
    (hRootInt : IntegrableOn (fun ω => Real.sqrt (futureEnergy β n N (η ω))) G disorderLaw)
    (hRootBound : ∫ ω in G, Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw ≤ Rcore / J)
    (hEnergy : ∀ ω, cE * (N : ℝ) *
      (∑' y, (finiteWalkConvolution (N - n) S (η ω) y) ^ 2) ≤
        futureEnergy β n N (η ω))
    (Minv : ℝ) (hMinv : 0 ≤ Minv)
    (hInvMoment : ∫ ω, (smoothedP2Plane β m n 0 ω)⁻¹ ∂disorderLaw ≤ Minv)
    (cwalk : ℝ) (hcwalk : 1 ≤ cwalk)
    (hwalk : ∀ R : ℝ, 0 ≤ R → ∀ N : ℕ, 1 ≤ N →
      (∑' y : Site, {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator
        (fun _ => (1 : ℝ)) y * srwKernel N y) ≤ cwalk * Real.exp (-R ^ 2 / (8 * cwalk)))
    (hTailEvent : ∀ R : ℝ, 1 ≤ R →
      ∫ ω, ∑' y, {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator
        (fun y => ∑' w, smoothedEndpointDist β m n 0 ω w *
          srwKernel (N - n) (y - w)) y ∂disorderLaw ≤
        Ctail * Real.exp (-ctail * R ^ 2))
    (hCoeff : 16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
      2 * |Ctail| + 4 * Real.log ρ * Rcore ≤ C) :
    ∀ (f : Site → ℝ) (M : ℝ), (∀ y, |f y| ≤ M) →
      ∫ ω in G, |profileP2Fun β n N (endpointDist β n 0 ω) f ω -
        profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) f ω| ∂disorderLaw ≤
          C * M * Real.sqrt (Real.log |Real.log δ|) / L := by
  intro f M hf
  let s : ℝ := Real.sqrt (Real.log |Real.log δ|)
  let R : ℝ := D * s
  have hloglog : 0 < Real.log |Real.log δ| := by linarith [hδlog]
  have hsSq : s ^ 2 = Real.log |Real.log δ| := by
    dsimp [s]
    exact Real.sq_sqrt hloglog.le
  have hsge1 : 1 ≤ s := by
    dsimp [s]
    exact Real.one_le_sqrt.mpr (by linarith [hδlog])
  have hRge1 : 1 ≤ R := by
    dsimp [R]
    exact one_le_mul_of_one_le_of_one_le hD hsge1
  have hEnergyN : ∀ ω, cE * (N : ℝ) *
      (∑' y, (finiteWalkConvolution (N - n) S (η ω) y) ^ 2) ≤
        futureEnergy β n N (η ω) := hEnergy
  have hTailWalk := hwalk R (by linarith) N hN
  have hTailData := integral_smoothedEndpointTailMass_le β hβ m n N hmn hnN R
    cwalk hcwalk hTailWalk Minv hMinv hInvMoment
  have hTailInt : Integrable (smoothedEndpointTailMass β m n N R) disorderLaw :=
    hTailData.1
  have hTailEq (ω : Disorder) :
      (∑' y, {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator
        (fun y => ∑' w, smoothedEndpointDist β m n 0 ω w *
          srwKernel (N - n) (y - w)) y) = smoothedEndpointTailMass β m n N R ω := by
    unfold smoothedEndpointTailMass
    apply tsum_congr
    intro y
    by_cases hy : R * Real.sqrt N < ‖siteToPlane y‖
    · simp [Set.indicator, hy]
    · simp [Set.indicator, hy]
  have hTailBound :
      ∫ ω, smoothedEndpointTailMass β m n N R ω ∂disorderLaw ≤
        Ctail * Real.exp (-ctail * R ^ 2) := by
    calc
      _ = ∫ ω, ∑' y, {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator
          (fun y => ∑' w, smoothedEndpointDist β m n 0 ω w *
            srwKernel (N - n) (y - w)) y ∂disorderLaw := by
        apply integral_congr_ae
        exact ae_of_all disorderLaw fun ω => (hTailEq ω).symm
      _ ≤ Ctail * Real.exp (-ctail * R ^ 2) := hTailEvent R hRge1
  have hCoeff' :
      16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
        2 * |Ctail| + 4 * Real.log ρ * Rcore ≤ C := hCoeff
  have hWeighted := weighted_profile_origin_bound β ρ D s L C cE Cball Ctail ctail
    Rcore R m n N J S U₀ U₁ η G f M hCardBall hnN hN hcE hCball hηsupport
    hηmass hηbound hηmeas hU₀support hU₁support hU₀mass hU₁mass hU₀nonneg hU₁nonneg hU₁eq
    hηdiff hGmeas hRootInt hRootBound hEnergyN hTailInt hTailBound hRge1 rfl
    hD hDtail (by simpa [hL] using hsSq) hsge1 hLpos hρ hJrecip hRcore hCoeff' hf
  have hprofileAEMod :
      (fun ω => |profileP2Fun β n N (endpointDist β n 0 ω) f ω -
        profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) f ω|) =ᵐ[
        disorderLaw.restrict G] (fun ω =>
          |profileP2Fun β n N (U₀ ω) f ω - profileP2Fun β n N (U₁ ω) f ω|) := by
    filter_upwards [] with ω
    have hfirst : endpointDist β n 0 ω = U₀ ω := by
      rw [endpointDist_eq_smoothedEndpointDist_zero β n 0 ω, ← hU₀eq ω]
    have hsecond : smoothedEndpointDist β m n 0 ω = U₁ ω := by
      funext y
      exact (hU₁eq ω y).symm
    rw [hfirst, hsecond]
  have hmainBound :
      ∫ ω in G, |profileP2Fun β n N (endpointDist β n 0 ω) f ω -
        profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) f ω| ∂disorderLaw ≤
      C * M * s / L := by
    calc
      _ = ∫ ω in G, |profileP2Fun β n N (U₀ ω) f ω -
          profileP2Fun β n N (U₁ ω) f ω| ∂disorderLaw :=
        integral_congr_ae hprofileAEMod
      _ ≤ C * M * s / L := hWeighted
  simpa [s] using hmainBound

private theorem origin_square_profile_bounds
    (β ρ Cpe C L : ℝ) (n N J : ℕ) (U₀ U₁ : Disorder → Site → ℝ)
    (S : Finset Site) (G PG₀ PG₁ : Set Disorder)
    (hN : n ≤ N) (hU₀eq : ∀ ω, U₀ ω = smoothedEndpointDist β 0 n 0 ω)
    (hU₀zero : ∀ ω y, y ∉ S → U₀ ω y = 0)
    (hU₁zero : ∀ ω y, y ∉ S → U₁ ω y = 0)
    (hU₀bdd : ∃ B : ℝ, ∀ ω y, |U₀ ω y| ≤ B)
    (hU₁bdd : ∃ B : ℝ, ∀ ω y, |U₁ ω y| ≤ B)
    (hU₀meas : ∀ y, Measurable[disorderPast n] (U₀ · y))
    (hU₁meas : ∀ y, Measurable[disorderPast n] (U₁ · y))
    (hGmeas : MeasurableSet[disorderPast n] G)
    (hPG₀subset : G ⊆ PG₀) (hPG₁subset : G ⊆ PG₁)
    (hU₀energy : ∫ ω in PG₀, futureEnergy β n N (U₀ ω) ∂disorderLaw ≤ |Cpe| * J)
    (hU₁energy : ∫ ω in PG₁, futureEnergy β n N (U₁ ω) ∂disorderLaw ≤ |Cpe| * J)
    (hJupper : (J : ℝ) ≤ L / (2 * Real.log ρ))
    (hCsq : |Cpe| / (2 * Real.log ρ) ≤ C) (hLpos : 0 < L) :
    (∫ ω in G, profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω ^ 2
      ∂disorderLaw ≤ C * L) ∧
    (∫ ω in G, profileP2Fun β n N (U₁ ω) (fun _ => 1) ω ^ 2
      ∂disorderLaw ≤ C * L) := by
  have hU₀energyInt := integrableOn_profileP2Fun_sq_eq β hN U₀ S
    (fun ω y hy => hU₀zero ω y hy) hU₀bdd hU₀meas PG₀
  have hU₁energyInt := integrableOn_profileP2Fun_sq_eq β hN U₁ S
    (fun ω y hy => hU₁zero ω y hy) hU₁bdd hU₁meas PG₁
  have hU₀sqId := setIntegral_profileP2Fun_sq_eq β hN U₀ S
    (fun ω y hy => hU₀zero ω y hy) hU₀bdd hU₀meas G hGmeas
  have hU₁sqId := setIntegral_profileP2Fun_sq_eq β hN U₁ S
    (fun ω y hy => hU₁zero ω y hy) hU₁bdd hU₁meas G hGmeas
  have hU₀energyG : ∫ ω in G, futureEnergy β n N (U₀ ω) ∂disorderLaw ≤
      |Cpe| * (J : ℝ) := by
    calc
      _ ≤ ∫ ω in PG₀, futureEnergy β n N (U₀ ω) ∂disorderLaw :=
        setIntegral_mono_set hU₀energyInt.2
          (Filter.Eventually.of_forall fun ω => futureEnergy_nonneg β n N (U₀ ω))
          (Filter.Eventually.of_forall fun ω hω => hPG₀subset hω)
      _ ≤ _ := hU₀energy
  have hU₁energyG : ∫ ω in G, futureEnergy β n N (U₁ ω) ∂disorderLaw ≤
      |Cpe| * (J : ℝ) := by
    calc
      _ ≤ ∫ ω in PG₁, futureEnergy β n N (U₁ ω) ∂disorderLaw :=
        setIntegral_mono_set hU₁energyInt.2
          (Filter.Eventually.of_forall fun ω => futureEnergy_nonneg β n N (U₁ ω))
          (Filter.Eventually.of_forall fun ω hω => hPG₁subset hω)
      _ ≤ _ := hU₁energy
  have hU₀sq :
      ∫ ω in G, profileP2Fun β n N (U₀ ω) (fun _ => 1) ω ^ 2 ∂disorderLaw ≤
        (|Cpe| / (2 * Real.log ρ)) * L := by
    rw [hU₀sqId]
    exact hU₀energyG.trans (calc
      |Cpe| * (J : ℝ) ≤ |Cpe| * (L / (2 * Real.log ρ)) :=
        mul_le_mul_of_nonneg_left hJupper (abs_nonneg Cpe)
      _ = (|Cpe| / (2 * Real.log ρ)) * L := by ring)
  have hU₁sq :
      ∫ ω in G, profileP2Fun β n N (U₁ ω) (fun _ => 1) ω ^ 2 ∂disorderLaw ≤
        (|Cpe| / (2 * Real.log ρ)) * L := by
    rw [hU₁sqId]
    exact hU₁energyG.trans (calc
      |Cpe| * (J : ℝ) ≤ |Cpe| * (L / (2 * Real.log ρ)) :=
        mul_le_mul_of_nonneg_left hJupper (abs_nonneg Cpe)
      _ = (|Cpe| / (2 * Real.log ρ)) * L := by ring)
  have hU₀sqEndpoint :
      ∫ ω in G, profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω ^ 2
        ∂disorderLaw ≤ C * L := by
    have heq : (fun ω => profileP2Fun β n N (endpointDist β n 0 ω)
        (fun _ => 1) ω ^ 2) =ᵐ[disorderLaw.restrict G]
        fun ω => profileP2Fun β n N (U₀ ω) (fun _ => 1) ω ^ 2 := by
      filter_upwards [] with ω
      rw [endpointDist_eq_smoothedEndpointDist_zero β n 0 ω, ← hU₀eq ω]
    rw [integral_congr_ae heq]
    exact hU₀sq.trans (mul_le_mul_of_nonneg_right hCsq hLpos.le)
  exact ⟨hU₀sqEndpoint, hU₁sq.trans (mul_le_mul_of_nonneg_right hCsq hLpos.le)⟩

private theorem profileOrigin_constant_coefficients
    (ρ D Cball cE Cpe Ctail Rcore C : ℝ) (hρ : 1 < ρ) (hD : 1 ≤ D)
    (hcE : 0 < cE) (hRcore : 0 ≤ Rcore)
    (hC : C = 1 + 32 * Real.log ρ * Rcore + 8 * Real.log ρ * |Cpe| +
      |Cpe| / (2 * Real.log ρ) +
      16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
      2 * |Ctail| + 2) :
    4 * Real.log ρ * Rcore ≤ C ∧
      16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
        2 * |Ctail| + 4 * Real.log ρ * Rcore ≤ C ∧
      |Cpe| / (2 * Real.log ρ) ≤ C := by
  have hlog : 0 < Real.log ρ := Real.log_pos hρ
  have hden : 0 < 2 * Real.log ρ := by positivity
  have hlocal : 0 ≤ 16 * Real.log ρ * D * Real.sqrt Cball / Real.sqrt cE * Rcore := by
    positivity
  have hprofile : 0 ≤ 8 * Real.log ρ * |Cpe| := by positivity
  have hfrac : 0 ≤ |Cpe| / (2 * Real.log ρ) := div_nonneg (abs_nonneg _) hden.le
  have htail : 0 ≤ 2 * |Ctail| := by positivity
  have hmargin : 0 ≤ 28 * Real.log ρ * Rcore := by positivity
  constructor
  · rw [hC]
    nlinarith
  · constructor
    · rw [hC]
      nlinarith
    · rw [hC]
      nlinarith

/-- The discrepancy and profile-energy bounds imply good-event comparison and second-moment bounds for endpoint and smoothed-endpoint partition functions.
The integral statements are nonvacuous by `integrable_randomTerminalProfilePolymer`,
`integrable_sqrt_futureEnergy`,
`integrableOn_profileP2Fun_sq_eq` and `integrableOn_abs_profileP2Fun_weighted_le`. -/
theorem prop_PF_origin_of (hDiscrepancyStringInput : OpenStringBound) (hPE : ProfileEstimatesBound) (A : ℝ) :
    ∃ δ₀ C : ℝ, 0 < δ₀ ∧ δ₀ < 1 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∃ G : Set Disorder,
        MeasurableSet[disorderPast (evenCeil (Real.sqrt δ * N))] G ∧
        (disorderLaw Gᶜ).toReal ≤ C / |Real.log δ| ∧
        ∫ ω in G, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω -
          profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
            (fun _ => 1) ω| ∂disorderLaw ≤ C / |Real.log δ| ∧
        (∫ ω in G, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω ^ 2
            ∂disorderLaw ≤ C * |Real.log δ|) ∧
        (∫ ω in G, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
            (fun _ => 1) ω ^ 2 ∂disorderLaw ≤ C * |Real.log δ|) ∧
        ∀ (f : Site → ℝ) (M : ℝ), (∀ z, |f z| ≤ M) →
          ∫ ω in G, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) f ω -
            profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
              (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
              f ω| ∂disorderLaw ≤ C * M * Real.sqrt (Real.log |Real.log δ|) / |Real.log δ| := by
  classical
  obtain ⟨ρK, θ, hρK, hθ0, hθ1, hDiscrepancyStringInputA⟩ :=
    setIntegral_futureEnergy_openCorrector_le_of hDiscrepancyStringInput A
  obtain ⟨ρPE, hρPE, hPEA⟩ := hPE A
  let ρbase : ℝ := max ρK ρPE
  have hρbase : 1 < ρbase := lt_of_lt_of_le hρK (le_max_left _ _)
  let ρupper : ℝ := ρbase ^ 2
  obtain ⟨Cpe, ell, hPEupper⟩ := hPEA ρupper
  obtain ⟨Copen, hDiscrepancyStringInputUpper⟩ := hDiscrepancyStringInputA ρupper
  obtain ⟨δtail, Ctail, ctail, hδtail, hctail, htail⟩ :=
    integral_smoothedEndpoint_tail_le A
  obtain ⟨cE, hcE, henergy⟩ := futureEnergy_ge_smoothed_sq A
  obtain ⟨Minv, hMinv, hInv⟩ := smoothedEndpoint_inverseMoment_smallDelta A
  obtain ⟨cwalk, hcwalk, hwalk⟩ := exists_srwKernel_tail_le_gaussian_constant
  obtain ⟨Cball, hball⟩ := card_ball_sites_le
  have hCball : 0 ≤ Cball := by
    have h := hball 1 (by norm_num : (1 : ℝ) ≤ 1)
    have hcard : 0 ≤ (((Critical2DKPZ.MomentBounds.boxSites 1).filter
        fun y => ‖siteToPlane y‖ ≤ (1 : ℝ)).card : ℝ) := Nat.cast_nonneg _
    nlinarith
  let δ₀ : ℝ := min (ρbase⁻¹ ^ 2) (min (δtail / 2)
    (min (Real.exp (-Real.exp 2) / 2) (min (1 / 512) (Real.exp
      (-4 * Real.log ρbase * (ell + 2))))))
  have hδ₀pos : 0 < δ₀ := by
    dsimp [δ₀]
    positivity
  have hδ₀lt : δ₀ < 1 := by
    dsimp [δ₀]
    have hρinvpos : 0 < ρbase⁻¹ := by positivity
    have hρinvlt : ρbase⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρbase
    have hρinv : ρbase⁻¹ ^ 2 < 1 := by
      nlinarith [mul_pos (by linarith : 0 < 1 - ρbase⁻¹)
        (by linarith : 0 < 1 + ρbase⁻¹)]
    exact lt_of_le_of_lt (min_le_left _ _) hρinv
  let D : ℝ := max 1 (Real.sqrt (1 / ctail))
  have hD : 1 ≤ D := le_max_left _ _
  have hDtail : 1 ≤ ctail * D ^ 2 := by
    dsimp [D]
    have hc : 0 < ctail := hctail
    by_cases hc1 : 1 ≤ ctail
    · have hDsq : 1 ≤ (max 1 (Real.sqrt (1 / ctail))) ^ 2 := by
        nlinarith [sq_nonneg (max 1 (Real.sqrt (1 / ctail)) - 1)]
      nlinarith
    · have hroot : Real.sqrt (1 / ctail) ≤ max 1 (Real.sqrt (1 / ctail)) :=
        le_max_right _ _
      have hs : Real.sqrt (1 / ctail) ^ 2 = 1 / ctail :=
        Real.sq_sqrt (by positivity)
      have hratio : 1 < 1 / ctail := (one_lt_div hc).2 (lt_of_not_ge hc1)
      have hrootgt : 1 < Real.sqrt (1 / ctail) := by
        by_contra h
        have hrootle : Real.sqrt (1 / ctail) ≤ 1 := le_of_not_gt h
        have hsqle : Real.sqrt (1 / ctail) ^ 2 ≤ 1 ^ 2 :=
          (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).2 hrootle
        rw [hs] at hsqle
        nlinarith
      rw [max_eq_right hrootgt.le]
      rw [hs]
      have hmul : ctail * (1 / ctail) = 1 := by field_simp
      rw [hmul]
  let Rcore : ℝ := 2 * |Cpe| + Real.sqrt |Copen| / (1 - θ) ^ 2
  let C : ℝ := 1 + 32 * Real.log ρbase * Rcore +
      8 * Real.log ρbase * |Cpe| +
      |Cpe| / (2 * Real.log ρbase) +
      16 * Real.log ρbase * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
      2 * |Ctail| + 2
  have hCpos : 0 ≤ C := by
    dsimp [C]
    have hlog : 0 < Real.log ρbase := Real.log_pos hρbase
    have hden : 0 < 1 - θ := by linarith
    have hdenρ : 0 < 2 * Real.log ρbase := by positivity
    dsimp [Rcore]
    positivity
  refine ⟨δ₀, C, hδ₀pos, hδ₀lt, ?_⟩
  intro δ hδ hδsmall
  have hδρ : δ ≤ ρbase⁻¹ ^ 2 := le_trans hδsmall (min_le_left _ _)
  have hδtail' : δ < δtail := by
    have : δ ≤ δtail / 2 := le_trans hδsmall (by simp [δ₀])
    linarith
  have hδexp : δ < Real.exp (-Real.exp 2) := by
    have hhalf : δ ≤ Real.exp (-Real.exp 2) / 2 := by
      exact le_trans hδsmall (by simp [δ₀])
    have hepos : 0 < Real.exp (-Real.exp 2) := Real.exp_pos _
    linarith
  have hδlog : 2 < Real.log |Real.log δ| := by
    have hlog : Real.log δ < -Real.exp 2 :=
      (Real.log_lt_iff_lt_exp hδ).2 hδexp
    have hneg : Real.log δ < 0 := by linarith [Real.exp_pos (2 : ℝ)]
    rw [abs_of_neg hneg]
    have hpos : 0 < |Real.log δ| := by rw [abs_of_neg hneg]; linarith
    have hstep : Real.exp 2 < |Real.log δ| := by
      rw [abs_of_neg hneg]
      linarith
    have hlogstep : 2 < Real.log |Real.log δ| :=
      (Real.lt_log_iff_exp_lt hpos).2 hstep
    simpa [abs_of_neg hneg] using hlogstep
  have hLpos : 0 < |Real.log δ| := by
    have : 1 < |Real.log δ| := by
      have he : 1 < Real.exp 2 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by norm_num)
      have hlog : Real.log δ < -Real.exp 2 := (Real.log_lt_iff_lt_exp hδ).2 hδexp
      rw [abs_of_neg (by linarith [Real.exp_pos (2 : ℝ)])]
      linarith
    linarith
  have hlogδneg : Real.log δ < 0 := by
    have hlog : Real.log δ < -Real.exp 2 := (Real.log_lt_iff_lt_exp hδ).2 hδexp
    linarith [Real.exp_pos (2 : ℝ)]
  have hgrid : gridRatio δ ρbase ∈ Set.Icc ρbase ρupper :=
    gridRatio_mem hρbase hδ hδρ
  let γ : ℝ := gridRatio δ ρbase
  let J : ℕ := gridBlocks δ ρbase
  have hJbounds := gridBlocks_bounds hρbase hδ hδρ
  have hlogbase : 0 < Real.log ρbase := Real.log_pos hρbase
  have hJlower : (|Real.log δ| : ℝ) / (8 * Real.log ρbase) ≤ J := by
    calc
      |Real.log δ| / (8 * Real.log ρbase) ≤
          |Real.log δ| / (4 * Real.log ρbase) := by
        apply div_le_div_of_nonneg_left (abs_nonneg _)
          (mul_pos (by norm_num) hlogbase)
        nlinarith [Real.log_pos hρbase]
      _ ≤ J := by simpa [J] using hJbounds.2.1
  have hJupper : (J : ℝ) ≤ |Real.log δ| / (2 * Real.log ρbase) := by
    simpa [J] using hJbounds.2.2
  have hJell : ell + 2 ≤ J := by
    have hδell : δ ≤ Real.exp (-4 * Real.log ρbase * (ell + 2)) :=
      le_trans hδsmall (by simp [δ₀])
    have hlog : |Real.log δ| ≥ 4 * Real.log ρbase * (ell + 2) := by
      have hlog' := Real.log_le_log hδ hδell
      rw [abs_of_neg hlogδneg]
      rw [Real.log_exp] at hlog'
      linarith
    have hden : 0 < 4 * Real.log ρbase := mul_pos (by norm_num) hlogbase
    have hlow := hJbounds.2.1
    have hreal : (ell + 2 : ℝ) ≤ |Real.log δ| / (4 * Real.log ρbase) := by
      apply (le_div_iff₀ hden).2
      nlinarith [hlog]
    have hlow' : |Real.log δ| / (4 * Real.log ρbase) ≤ J := by
      simpa [J] using hlow
    have hreal' : (ell + 2 : ℝ) ≤ (J : ℝ) := hreal.trans hlow'
    exact_mod_cast hreal'
  have htime := blockTime_gridRatio hρbase hδ hδρ
  have hγgt : 1 < γ := lt_of_lt_of_le hρbase hgrid.1
  have hmon := blockTime_monotone hγgt
  have hδ512 : δ ≤ 1 / 512 := le_trans hδsmall (by simp [δ₀])
  have hNinv := hInv δ hδ (by norm_num at hδ512 ⊢; linarith)
  have hγK : γ ∈ Set.Icc ρK ρupper :=
    ⟨le_trans (le_max_left _ _) hgrid.1, hgrid.2⟩
  have hγPE : γ ∈ Set.Icc ρPE ρupper :=
    ⟨le_trans (le_max_right _ _) hgrid.1, hgrid.2⟩
  have hOpenEvent := hDiscrepancyStringInputUpper γ hγK
  have hPEEvent := hPEupper γ hγPE
  filter_upwards [htime, hmon, hNinv, hOpenEvent, hPEEvent,
      henergy, htail δ hδ hδtail', Filter.eventually_ge_atTop 32]
      with N htimeN hmonN hInvN hOpenN hPEN hEnergyN hTailN hNlarge
  intro ϑ hϑ
  let K : ℕ := blockCount N γ
  let a : ℕ := K - 2 * J
  let b : ℕ := K - J
  have hKgt : 2 * J < K := by simpa [γ, J] using htimeN.1
  have hJpos : 0 < J := by omega
  have hKpos : 0 < K := by omega
  have hba : b = a + J := by dsimp [a, b]; omega
  have hKrel : K = b + J := by dsimp [b]; omega
  have htime0 : blockTime N γ 0 = 0 := by simp [blockTime]
  let t : ℕ → ℕ := blockTime N γ
  have htmono : Monotone t := by simpa [t] using hmonN
  have ht0 : t 0 = 0 := by simpa [t] using htime0
  have htimea : t a = evenCeil (δ * N) := by
    have h := htimeN.2.1
    simpa [a, K, J, γ] using h
  have htimeb : t b = evenCeil (Real.sqrt δ * N) := by
    have h := htimeN.2.2
    simpa [b, K, J, γ] using h
  let m := t a
  let n := t b
  have hmn : m ≤ n := by dsimp [m, n]; exact htmono (by omega)
  have hts : t b ≤ N := by
    have hKtime : t K = N := by
      dsimp [t]
      rw [blockTime]
      have hKzero : K ≠ 0 := ne_of_gt hKpos
      have hKnotlt : ¬ K < blockCount N γ := by dsimp [K]; omega
      simp [hKzero, hKnotlt]
    rw [← hKtime]
    exact htmono (by omega)
  have hJgap : (K : ℝ) - b = J := by
    have hNat : K - b = J := by dsimp [b]; omega
    rw [← Nat.cast_sub (by omega : b ≤ K)]
    exact_mod_cast hNat
  have hlength : b + ell ≤ K := by
    have hNat : b + ell ≤ K := by dsimp [b]; omega
    exact hNat
  have hprofile0 := hPEN ϑ hϑ 1 b (by omega) (by omega) hlength
  have hprofile1 := hPEN ϑ hϑ (a + 1) b (by omega) (by omega) hlength
  have hopen (u : ℕ) (hu : 1 ≤ u) (hus : u ≤ b) :
      ∫ ω in blockGoodSet (criticalBeta ϑ N) t u b,
        futureEnergy (criticalBeta ϑ N) (t b) N
          (openCorrector (criticalBeta ϑ N) t u b ω) ∂disorderLaw ≤
        Copen * θ ^ (2 * (b - u)) / ((K : ℝ) - u) := by
    exact hOpenN ϑ hϑ u b hu hus (by omega)
  have hGridset0 :=
    LogNormality.measurableSet_profileGoodSet_past (criticalBeta ϑ N) htmono
      (by omega : 1 ≤ 1) (by omega : 1 ≤ b)
  have hGridset1 :=
    LogNormality.measurableSet_profileGoodSet_past (criticalBeta ϑ N) htmono
      (by omega : 1 ≤ a + 1) (by omega : a + 1 ≤ b)
  let PG0 := profileGoodSet (criticalBeta ϑ N) t 1 b
  let PG1 := profileGoodSet (criticalBeta ϑ N) t (a + 1) b
  let G := PG0 ∩ PG1
  have hGmeas : MeasurableSet[disorderPast n] G := by
    simpa [G, PG0, PG1, n] using hGridset0.inter hGridset1
  have hG0 : G ⊆ PG0 := Set.inter_subset_left
  have hG1 : G ⊆ PG1 := Set.inter_subset_right
  have hRoot := endpoint_root_comparison_integral_le (criticalBeta ϑ N) t N K a b J
    htmono ht0 (by omega) hKrel hba hts θ Copen Cpe hθ0 hθ1 hopen G
    (by simpa [PG0] using hG0) (by simpa [PG1] using hG1)
    (by simpa [PG0, t, n, ht0] using hprofile0.2.2.2.1)
    (by simpa [PG1, t, m, n] using hprofile1.2.2.2.1)
  rcases hInvN ϑ hϑ with ⟨hNpos, hmnInv, hnN, hInvMoment⟩
  have hrootδ : Real.sqrt δ ≤ 1 / 16 := by
    have hroot512 : Real.sqrt (1 / 512 : ℝ) ≤ 1 / 16 := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).1
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 512)]
      norm_num
    exact (Real.sqrt_le_sqrt hδ512).trans hroot512
  have h4n : 4 * n ≤ N := by
    have hround := Critical2DKPZ.evenCeil_lt_add_two
      (mul_nonneg (Real.sqrt_nonneg δ) (Nat.cast_nonneg N))
    have hnreal : (n : ℝ) < (N : ℝ) / 16 + 2 := by
      have hroundn : (n : ℝ) < Real.sqrt δ * (N : ℝ) + 2 := by
        dsimp [n]
        rw [htimeb]
        exact hround
      have hprod : Real.sqrt δ * (N : ℝ) ≤ (N : ℝ) / 16 := by
        calc
          Real.sqrt δ * (N : ℝ) ≤ (1 / 16) * (N : ℝ) :=
            mul_le_mul_of_nonneg_right hrootδ (Nat.cast_nonneg N)
          _ = (N : ℝ) / 16 := by ring
      exact hroundn.trans_le (add_le_add hprod (le_rfl : (2 : ℝ) ≤ 2))
    have hNreal : 32 ≤ (N : ℝ) := by exact_mod_cast hNlarge
    have h8 : 8 ≤ (N : ℝ) / 4 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
      linarith only [hNreal]
    have hNbound : (N : ℝ) / 4 + 8 ≤ (N : ℝ) := by
      calc
        (N : ℝ) / 4 + 8 ≤ (N : ℝ) / 4 + (N : ℝ) / 4 := add_le_add le_rfl h8
        _ = (N : ℝ) / 2 := by ring
        _ ≤ (N : ℝ) := by
          apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).2
          linarith only [hNreal]
    have hbound : 4 * (n : ℝ) ≤ (N : ℝ) := by
      have hn4 : 4 * (n : ℝ) < 4 * ((N : ℝ) / 16 + 2) :=
        mul_lt_mul_of_pos_left hnreal (by norm_num)
      have hboundLt : 4 * (n : ℝ) < (N : ℝ) := calc
        4 * (n : ℝ) < 4 * ((N : ℝ) / 16 + 2) := hn4
        _ = (N : ℝ) / 4 + 8 := by ring
        _ ≤ (N : ℝ) := hNbound
      exact hboundLt.le
    have hbound' : ((4 * n : ℕ) : ℝ) ≤ (N : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound
    exact (Nat.cast_le (α := ℝ)).mp hbound'
  let β : ℝ := criticalBeta ϑ N
  let U₀ : Disorder → Site → ℝ := smoothedEndpointDist β 0 n 0
  let U₁ : Disorder → Site → ℝ := smoothedEndpointDist β m n 0
  let η : Disorder → Site → ℝ := fun ω y => U₀ ω y - U₁ ω y
  obtain ⟨Sprob, hU₀zero, hU₁zero, hηzero, hU₀mass, hU₁mass,
      hηmass, hηbound⟩ := endpoint_smoothing_difference_probability_data β hmn
  have hηmeas (y : Site) : Measurable[disorderPast n] (η · y) := by
    dsimp [η, U₀, U₁]
    exact measurable_endpoint_smoothing_difference_past β hmn y
  have hηbdd : ∃ B : ℝ, ∀ ω y, |η ω y| ≤ B := ⟨2, hηbound⟩
  have hβnonneg : 0 ≤ β := by dsimp [β, criticalBeta]; positivity
  have hpast0n : Gaussian.disorderBlock 0 n ≤ disorderPast n := by
    rw [← Gaussian.disorderBlock_zero n]
  have hU₀meas (y : Site) : Measurable[disorderPast n] (U₀ · y) := by
    dsimp [U₀]
    exact (Polymer.measurable_smoothedEndpointDist_block β 0 n (Nat.zero_le _) 0 y).mono
      hpast0n le_rfl
  have hU₁meas (y : Site) : Measurable[disorderPast n] (U₁ · y) := by
    dsimp [U₁]
    exact (Polymer.measurable_smoothedEndpointDist_block β m n hmn 0 y).mono
      (Gaussian.disorderBlock_mono (m := m) (n := n) (a := 0) (b := n)
        (Nat.zero_le _) le_rfl) le_rfl
  have hU₀nonneg (ω : Disorder) (y : Site) : 0 ≤ U₀ ω y := by
    change 0 ≤ smoothedEndpointDist β 0 n 0 ω y
    exact Smoothing.smoothedEndpointDist_nonneg β 0 y ω
  have hU₁nonneg (ω : Disorder) (y : Site) : 0 ≤ U₁ ω y := by
    change 0 ≤ smoothedEndpointDist β m n 0 ω y
    exact Smoothing.smoothedEndpointDist_nonneg (β := β) (m := m) (n := n) 0 y ω
  have hU₀bound (ω : Disorder) (y : Site) : |U₀ ω y| ≤ 1 := by
    rw [abs_of_nonneg (hU₀nonneg ω y)]
    by_cases hy : y ∈ Sprob
    · calc
        U₀ ω y ≤ ∑ z ∈ Sprob, U₀ ω z :=
          Finset.single_le_sum (fun z hz => hU₀nonneg ω z) hy
        _ = 1 := hU₀mass ω
    · change smoothedEndpointDist β 0 n 0 ω y ≤ 1
      rw [hU₀zero ω y hy]
      norm_num
  have hU₁bound (ω : Disorder) (y : Site) : |U₁ ω y| ≤ 1 := by
    rw [abs_of_nonneg (hU₁nonneg ω y)]
    by_cases hy : y ∈ Sprob
    · calc
        U₁ ω y ≤ ∑ z ∈ Sprob, U₁ ω z :=
          Finset.single_le_sum (fun z hz => hU₁nonneg ω z) hy
        _ = 1 := hU₁mass ω
    · change smoothedEndpointDist β m n 0 ω y ≤ 1
      rw [hU₁zero ω y hy]
      norm_num
  have hU₀bdd : ∃ B : ℝ, ∀ ω y, |U₀ ω y| ≤ B := ⟨1, hU₀bound⟩
  have hU₁bdd : ∃ B : ℝ, ∀ ω y, |U₁ ω y| ≤ B := ⟨1, hU₁bound⟩
  have hPG0subset : G ⊆ PG0 := by simpa [PG0] using hG0
  have hPG1subset : G ⊆ PG1 := by simpa [PG1] using hG1
  have hprob0 := hprofile0.1
  have hprob1 := hprofile1.1
  have hdenJ : (K : ℝ) - b = (J : ℝ) := by
    have hNat : K - b = J := by dsimp [b]; omega
    rw [← Nat.cast_sub (by omega : b ≤ K)]
    exact_mod_cast hNat
  have hJrealpos : 0 < (J : ℝ) := by exact_mod_cast hJpos
  have hJprob : |Real.log δ| / (4 * Real.log ρbase) ≤ J := by
    simpa [J] using hJbounds.2.1
  have hJrecip : (1 : ℝ) / J ≤ (4 * Real.log ρbase) / |Real.log δ| := by
    apply (div_le_div_iff₀ hJrealpos hLpos).2
    have hJcross : |Real.log δ| ≤ (J : ℝ) * (4 * Real.log ρbase) :=
      (div_le_iff₀ (by positivity : 0 < 4 * Real.log ρbase)).1 hJprob
    calc
      1 * |Real.log δ| ≤ (J : ℝ) * (4 * Real.log ρbase) := by simpa using hJcross
      _ = (4 * Real.log ρbase) * (J : ℝ) := by ring
  have hdenBlock : 0 < (K : ℝ) - b := by rw [hdenJ]; exact hJrealpos
  have hprob0' : (disorderLaw PG0ᶜ).toReal ≤ |Cpe| / J := by
    calc
      (disorderLaw PG0ᶜ).toReal ≤ Cpe / ((K : ℝ) - b) := by
        simpa [PG0, β, t, n, b] using hprob0
      _ ≤ |Cpe| / ((K : ℝ) - b) :=
        div_le_div_of_nonneg_right (le_abs_self Cpe) hdenBlock.le
      _ = |Cpe| / J := by simp [hdenJ]
  have hprob1' : (disorderLaw PG1ᶜ).toReal ≤ |Cpe| / J := by
    calc
      (disorderLaw PG1ᶜ).toReal ≤ Cpe / ((K : ℝ) - b) := by
        simpa [PG1, β, t, m, n, a, b] using hprob1
      _ ≤ |Cpe| / ((K : ℝ) - b) :=
        div_le_div_of_nonneg_right (le_abs_self Cpe) hdenBlock.le
      _ = |Cpe| / J := by simp [hdenJ]
  have hGcompl : (disorderLaw Gᶜ).toReal ≤ 8 * Real.log ρbase * |Cpe| / |Real.log δ| := by
    have hsubset : Gᶜ ⊆ PG0ᶜ ∪ PG1ᶜ := by
      intro ω hω
      change ω ∉ PG0 ∩ PG1 at hω
      by_cases h0 : ω ∈ PG0
      · right
        intro h1
        exact hω ⟨h0, h1⟩
      · exact Or.inl h0
    have hmeasure : disorderLaw Gᶜ ≤ disorderLaw PG0ᶜ + disorderLaw PG1ᶜ :=
      (measure_mono hsubset).trans (measure_union_le PG0ᶜ PG1ᶜ)
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top disorderLaw PG0ᶜ,
        measure_ne_top disorderLaw PG1ᶜ⟩) hmeasure
    rw [ENNReal.toReal_add (measure_ne_top disorderLaw PG0ᶜ)
      (measure_ne_top disorderLaw PG1ᶜ)] at hreal
    calc
      (disorderLaw Gᶜ).toReal ≤ (disorderLaw PG0ᶜ).toReal +
          (disorderLaw PG1ᶜ).toReal := hreal
      _ ≤ |Cpe| / J + |Cpe| / J := add_le_add hprob0' hprob1'
      _ = 2 * |Cpe| * (1 / J) := by ring
      _ ≤ 2 * |Cpe| * ((4 * Real.log ρbase) / |Real.log δ|) :=
        mul_le_mul_of_nonneg_left hJrecip (by positivity)
      _ = 8 * Real.log ρbase * |Cpe| / |Real.log δ| := by ring
  have hCprob : 8 * Real.log ρbase * |Cpe| ≤ C := by
    calc
      8 * Real.log ρbase * |Cpe| ≤
          8 * Real.log ρbase * |Cpe| +
            (1 + 32 * Real.log ρbase * Rcore + |Cpe| / (2 * Real.log ρbase) +
              16 * Real.log ρbase * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
              2 * |Ctail| + 2) := by
        apply le_add_of_nonneg_right
        have hlog : 0 < Real.log ρbase := Real.log_pos hρbase
        positivity
      _ = C := by dsimp [C]; ring
  have hGcompl' : (disorderLaw Gᶜ).toReal ≤ C / |Real.log δ| := by
    exact hGcompl.trans (div_le_div_of_nonneg_right hCprob hLpos.le)
  have hηprofileFlat (ω : Disorder) :
      profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω -
        profileP2Fun β n N (U₁ ω) (fun _ => 1) ω =
      profileP2Fun β n N (η ω) (fun _ => 1) ω := by
    rw [endpointDist_eq_smoothedEndpointDist_zero β n 0 ω]
    change profileP2Fun β n N (smoothedEndpointDist β 0 n 0 ω) (fun _ => 1) ω -
        profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω =
      profileP2Fun β n N
        (smoothedEndpointDist β 0 n 0 ω - smoothedEndpointDist β m n 0 ω)
        (fun _ => 1) ω
    exact (profileP2Fun_sub_eq β n N (smoothedEndpointDist β 0 n 0 ω)
      (smoothedEndpointDist β m n 0 ω) (fun _ => 1) Sprob
      (hU₀zero ω) (hU₁zero ω) ω).symm
  have hnN' : n ≤ N := by simpa [n, htimeb] using hnN
  have hJupper' : (J : ℝ) ≤ |Real.log δ| / (2 * Real.log ρbase) := by
    simpa [J] using hJbounds.2.2
  have hU₀eq (ω : Disorder) : U₀ ω = smoothedEndpointDist β 0 n 0 ω := rfl
  have hU₀energyPG : ∫ ω in PG0, futureEnergy β n N (U₀ ω) ∂disorderLaw ≤
      |Cpe| * (J : ℝ) := by
    calc
      _ ≤ Cpe * ((K : ℝ) - b) := by
        simpa [PG0, U₀, β, t, n, ht0, b] using hprofile0.2.2.2.2
      _ ≤ |Cpe| * (J : ℝ) := by rw [hdenJ]; exact
        mul_le_mul_of_nonneg_right (le_abs_self Cpe) (Nat.cast_nonneg _)
  have hU₁energyPG : ∫ ω in PG1, futureEnergy β n N (U₁ ω) ∂disorderLaw ≤
      |Cpe| * (J : ℝ) := by
    calc
      _ ≤ Cpe * ((K : ℝ) - b) := by
        simpa [PG1, U₁, β, t, n, m, a, b] using hprofile1.2.2.2.2
      _ ≤ |Cpe| * (J : ℝ) := by rw [hdenJ]; exact
        mul_le_mul_of_nonneg_right (le_abs_self Cpe) (Nat.cast_nonneg _)
  have hRcore : 0 ≤ Rcore := by
    dsimp [Rcore]
    have hθden : 0 < 1 - θ := by linarith
    positivity
  have hCoeffs := profileOrigin_constant_coefficients ρbase D Cball cE Cpe Ctail
    Rcore C hρbase hD hcE hRcore rfl
  have hMoments := origin_square_profile_bounds β ρbase Cpe C (|Real.log δ|) n N J
    U₀ U₁ Sprob G PG0 PG1 hnN' hU₀eq
    (fun ω y hy => hU₀zero ω y hy) (fun ω y hy => hU₁zero ω y hy)
    hU₀bdd hU₁bdd hU₀meas hU₁meas hGmeas hPG0subset hPG1subset
    hU₀energyPG hU₁energyPG hJupper' hCoeffs.2.2 hLpos
  have hfirstSq' := hMoments.1
  have hsecondSq' := hMoments.2
  have hflatIntBound := setIntegral_abs_profileP2Fun_le β hnN' η Sprob
    (fun ω y hy => hηzero ω y hy) hηbdd hηmeas G hGmeas
  have hflatEq :
      (fun ω => |profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω -
        profileP2Fun β n N (U₁ ω) (fun _ => 1) ω|) =ᵐ[disorderLaw.restrict G]
      (fun ω => |profileP2Fun β n N (η ω) (fun _ => 1) ω|) := by
    filter_upwards [] with ω
    rw [hηprofileFlat ω]
  have hflatBound :
      ∫ ω in G, |profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω -
        profileP2Fun β n N (U₁ ω) (fun _ => 1) ω| ∂disorderLaw ≤ C / |Real.log δ| := by
    calc
      _ = ∫ ω in G, |profileP2Fun β n N (η ω) (fun _ => 1) ω| ∂disorderLaw :=
        integral_congr_ae hflatEq
      _ ≤ ∫ ω in G, Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw :=
        hflatIntBound
      _ ≤ Rcore / J := by simpa [β, η, U₀, U₁, Rcore] using hRoot.2
      _ ≤ C / |Real.log δ| := by
        calc
          _ = Rcore * (1 / (J : ℝ)) := by ring
          _ ≤ Rcore * (4 * Real.log ρbase / |Real.log δ|) :=
            mul_le_mul_of_nonneg_left hJrecip hRcore
          _ = (4 * Real.log ρbase * Rcore) / |Real.log δ| := by ring
          _ ≤ C / |Real.log δ| := div_le_div_of_nonneg_right hCoeffs.1 hLpos.le
  have hGmeasFinal :
      MeasurableSet[disorderPast (evenCeil (Real.sqrt δ * N))] G := by
    have hnEq : n = evenCeil (Real.sqrt δ * N) := by
      dsimp [n]
      exact htimeb
    rw [← hnEq]
    exact hGmeas
  have hflatBoundFinal :
      ∫ ω in G, |profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
        (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω -
        profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
        (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N))
          (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω| ∂disorderLaw ≤
      C / |Real.log δ| := by simpa [β, n, U₁, m, htimea, htimeb] using hflatBound
  have hfirstSqFinal :
      ∫ ω in G, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
        (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω ^ 2
        ∂disorderLaw ≤ C * |Real.log δ| := by simpa [β, n, htimeb] using hfirstSq'
  have hsecondSqFinal :
      ∫ ω in G, profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
        (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N))
          (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω ^ 2 ∂disorderLaw ≤
      C * |Real.log δ| := by simpa [β, n, U₁, m, htimea, htimeb] using hsecondSq'
  refine ⟨G, hGmeasFinal, hGcompl', hflatBoundFinal, hfirstSqFinal, hsecondSqFinal, ?_⟩
  intro f M hf
  have hEnergyConv (ω : Disorder) : cE * (N : ℝ) *
      (∑' y, (finiteWalkConvolution (N - n) Sprob (η ω) y) ^ 2) ≤
        futureEnergy β n N (η ω) := by
    simpa [β, finiteWalkConvolution] using
      hEnergyN ϑ hϑ n h4n (η ω) Sprob (hηzero ω) (hηmass ω)
  have hRootInt : IntegrableOn
      (fun ω => Real.sqrt (futureEnergy β n N (η ω))) G disorderLaw := by
    simpa [β, η, U₀, U₁] using hRoot.1
  have hRootBound :
      ∫ ω in G, Real.sqrt (futureEnergy β n N (η ω)) ∂disorderLaw ≤ Rcore / J := by
    simpa [β, η, U₀, U₁, Rcore] using hRoot.2
  have hTailEvent (R : ℝ) (hR : 1 ≤ R) :
      ∫ ω, ∑' y, {y : Site | R * Real.sqrt N < ‖siteToPlane y‖}.indicator
        (fun y => ∑' w, smoothedEndpointDist β m n 0 ω w *
          srwKernel (N - n) (y - w)) y ∂disorderLaw ≤
        Ctail * Real.exp (-ctail * R ^ 2) := by
    simpa [β, m, n, t, htimea, htimeb] using hTailN ϑ hϑ R hR
  have hCoeff :
      16 * Real.log ρbase * D * Real.sqrt Cball / Real.sqrt cE * Rcore +
        2 * |Ctail| + 4 * Real.log ρbase * Rcore ≤ C := hCoeffs.2.1
  have hWeighted := weighted_origin_profile_from_data β ρbase D C Cball Ctail ctail
    cE Rcore δ |Real.log δ| m n N J Sprob U₀ U₁ η G hρbase hD hDtail hJrecip
    hδlog rfl hLpos hRcore hnN' hNpos hmn hβnonneg hcE hCball hball
    (fun ω y hy => by simpa [η, U₀, U₁] using hηzero ω y hy)
    (by simpa [η, U₀, U₁] using hηmass) hηbdd hηmeas
    (fun ω y hy => hU₀zero ω y hy) (fun ω y hy => hU₁zero ω y hy)
    hU₀mass hU₁mass hU₀nonneg hU₁nonneg hU₀eq (by intro ω y; rfl)
    (by intro ω y; rfl) hGmeas hRootInt hRootBound hEnergyConv
    Minv hMinv (by simpa [β, m, n, t, htimea, htimeb] using hInvMoment) cwalk hcwalk hwalk
    hTailEvent hCoeff
  simpa [β, m, n, htimea, htimeb] using hWeighted f M hf

end Critical2DKPZ.FutureProfiles

end
