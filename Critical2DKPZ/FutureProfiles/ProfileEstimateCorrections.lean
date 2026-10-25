/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.ProfileEstimateEnergy
public import Critical2DKPZ.FutureProfiles.EnergySeminorm
public import Critical2DKPZ.FutureProfiles.HelperExpansions
public import Critical2DKPZ.FutureProfiles.HelperIdentities
public import Critical2DKPZ.FutureProfiles.OpenCorrectorEnergy
public import Critical2DKPZ.FutureProfiles.SplitBoundInputs
public import Critical2DKPZ.FutureProfiles.WalkBounds
public import Critical2DKPZ.OnePoint.BlockRatioOriginalLawGoodSet
import Mathlib.Tactic

/-! # The block profile estimates -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal
open ProbabilityTheory

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer

/-- On the profile good set, the square root of the future energy of the residual profile
(smoothed endpoint profile minus the simple random walk kernel minus the common correction) is
integrable, and its integral is at most `2 (√(|C₁||C₀|)/(1 − θ) + √(|C₁||Ccommon|)) / (K − s)`. -/
theorem profileResidual_integral_sqrt_le_of
    (β : ℝ) (t : ℕ → ℕ) (N r s K : ℕ) (ht : Monotone t)
    (hr : 1 ≤ r) (hrs : r ≤ s) (hsK : s + 2 ≤ K) (hts : t s ≤ N)
    (θ C₀ C₁ Ccommon : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hRatio : ∀ u : ℕ, r < u → u ≤ s →
      ∫ ω in blockGoodSet β t r (u - 1),
        (blockRatio β t r (u - 1) ω - 1) ^ 2 ∂disorderLaw ≤
          C₁ / ((K : ℝ) - (u - 1)))
    (hOpen : ∀ u : ℕ, r ≤ u → u ≤ s →
      ∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
          C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u))
    (hTotalRatio :
      ∫ ω in blockGoodSet β t r s,
        (blockRatio β t r s ω - 1) ^ 2 ∂disorderLaw ≤ C₁ / ((K : ℝ) - s))
    (hCommonInt : IntegrableOn
      (fun ω => futureEnergy β (t s) N (commonCorrection β t r s ω))
      (blockGoodSet β t r s) disorderLaw)
    (hCommon :
      ∫ ω in blockGoodSet β t r s,
        futureEnergy β (t s) N (commonCorrection β t r s ω) ∂disorderLaw ≤
          Ccommon / ((K : ℝ) - s)) :
    IntegrableOn (fun ω => Real.sqrt (futureEnergy β (t s) N (fun y =>
        smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
          commonCorrection β t r s ω y))) (profileGoodSet β t r s) disorderLaw ∧
    ∫ ω in profileGoodSet β t r s,
      Real.sqrt (futureEnergy β (t s) N (fun y =>
        smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
          commonCorrection β t r s ω y)) ∂disorderLaw ≤
      2 * (Real.sqrt (|C₁| * |C₀|) / (1 - θ) +
        Real.sqrt (|C₁| * |Ccommon|)) / ((K : ℝ) - s) := by
  classical
  let G := blockGoodSet β t r s
  let PG := profileGoodSet β t r s
  let I := Finset.Icc r s
  let S := I.biUnion (fun u => openCorrectorNumeratorSupport t u s)
  let R : Disorder → ℝ := blockRatio β t r s
  let Cprof : Disorder → Site → ℝ := commonCorrection β t r s
  let η : ℕ → Disorder → Site → ℝ := fun u ω y =>
    (blockRatio β t r (u - 1) ω - 1) * openCorrector β t u s ω y
  let Aprof : Disorder → Site → ℝ := fun ω y => ∑ u ∈ I, η u ω y
  let P : Disorder → Site → ℝ := fun ω y =>
    smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y - Cprof ω y
  let Q : Disorder → Site → ℝ := fun ω y =>
    (R ω)⁻¹ * Aprof ω y + ((1 - R ω) / R ω) * Cprof ω y
  let Ecommon : Disorder → ℝ := fun ω => futureEnergy β (t s) N (Cprof ω)
  let Eapprox : Disorder → ℝ := fun ω => futureEnergy β (t s) N (Aprof ω)
  let L : ℝ := (K : ℝ) - s
  have hL : 0 < L := by
    dsimp [L]
    have hn : 0 < K - s := by omega
    rw [← Nat.cast_sub (by omega : s ≤ K)]
    exact_mod_cast hn
  have hRatioMeasBlock : Measurable[Gaussian.disorderBlock (t (r - 1)) (t s)] R := by
    exact measurable_blockRatio_on_block β t ht r s (by omega)
  have hBlockGlobal := Gaussian.disorderBlock_le (t (r - 1)) (t s)
  have hRmeas : Measurable R := hRatioMeasBlock.mono hBlockGlobal le_rfl
  have hGmeasBlock : MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t s)] G :=
    measurable_blockGoodSet_on_block β t ht r s
  have hGmeas : MeasurableSet G := hBlockGlobal G hGmeasBlock
  have hPGmeas : MeasurableSet PG := by
    change MeasurableSet (G ∩ {ω | |R ω - 1| ≤ 1 / 2})
    exact hGmeas.inter (measurableSet_le
      (hRmeas.sub measurable_const).abs measurable_const)
  have hPGsubset : PG ⊆ G := by
    intro ω hω
    exact hω.1
  have hRgood (ω : Disorder) (hω : ω ∈ PG) : |R ω - 1| ≤ 1 / 2 := by
    simpa [PG, profileGoodSet, R] using hω.2
  have hRpos (ω : Disorder) (hω : ω ∈ PG) : 0 < R ω := by
    have h := hRgood ω hω
    have hbound : 1 / 2 ≤ R ω := by
      have h' := abs_le.mp h
      linarith
    linarith
  have hRinv (ω : Disorder) (hω : ω ∈ PG) : |(R ω)⁻¹| ≤ 2 := by
    rw [abs_inv, abs_of_pos (hRpos ω hω), inv_eq_one_div]
    apply (div_le_iff₀ (hRpos ω hω)).2
    have h := hRgood ω hω
    have h' := abs_le.mp h
    linarith
  have hRdefect (ω : Disorder) (hω : ω ∈ PG) :
      |(1 - R ω) / R ω| ≤ 2 * |R ω - 1| := by
    rw [abs_div, abs_of_pos (hRpos ω hω), abs_sub_comm 1 (R ω)]
    apply (div_le_iff₀ (hRpos ω hω)).2
    have h := hRgood ω hω
    rw [abs_le] at h
    nlinarith [abs_nonneg (R ω - 1)]
  have hCcommonMeasPast :=
    measurable_commonCorrection_futureEnergy β t N r s ht hr hrs hts
  have hCcommonMeas : Measurable Ecommon :=
    hCcommonMeasPast.mono (by
      rw [← Gaussian.disorderBlock_zero (t s)]
      exact Gaussian.disorderBlock_le 0 (t s)) le_rfl
  have hCroot := setIntegral_sqrt_le_sqrt Ecommon G hCcommonMeas
    (fun ω => futureEnergy_nonneg β (t s) N (Cprof ω)) hCommonInt
  have hDeltaSqInt : IntegrableOn (fun ω => |R ω - 1| ^ 2) G disorderLaw := by
    simpa [G, R, sq_abs] using OnePoint.integrableOn_blockRatio_sub_one_sq β ht hr hrs
  have hCrootSqInt : IntegrableOn (fun ω => Real.sqrt (Ecommon ω) ^ 2) G disorderLaw := by
    have heq : (fun ω => Real.sqrt (Ecommon ω) ^ 2) =ᵐ[disorderLaw.restrict G] Ecommon := by
      filter_upwards [] with ω
      exact Real.sq_sqrt (futureEnergy_nonneg β (t s) N (Cprof ω))
    exact hCommonInt.congr heq.symm
  have hCauchy := setIntegral_mul_le_sqrt_sq (fun ω => |R ω - 1|)
    (fun ω => Real.sqrt (Ecommon ω)) G (hRmeas.sub measurable_const).abs hCcommonMeas.sqrt
    (fun _ => abs_nonneg _) (fun ω => Real.sqrt_nonneg _)
    hDeltaSqInt hCrootSqInt
  have htotalDelta : ∫ ω in G, |R ω - 1| ^ 2 ∂disorderLaw ≤ |C₁| / L := by
    have h := hTotalRatio
    have hden : 0 < L := hL
    have habs : C₁ / L ≤ |C₁| / L := div_le_div_of_nonneg_right (le_abs_self C₁) hden.le
    simpa [G, R, L] using h.trans habs
  have hcommonAbs : ∫ ω in G, Ecommon ω ∂disorderLaw ≤ |Ccommon| / L := by
    have h := hCommon
    have habs : Ccommon / L ≤ |Ccommon| / L := div_le_div_of_nonneg_right
      (le_abs_self Ccommon) hL.le
    simpa [G, Ecommon, Cprof, L] using h.trans habs
  have hCauchyBound :
      ∫ ω in G, |R ω - 1| * Real.sqrt (Ecommon ω) ∂disorderLaw ≤
        Real.sqrt (|C₁| * |Ccommon|) / L := by
    have hrootEq : ∫ ω in G, Real.sqrt (Ecommon ω) ^ 2 ∂disorderLaw =
        ∫ ω in G, Ecommon ω ∂disorderLaw := by
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        Real.sq_sqrt (futureEnergy_nonneg β (t s) N (Cprof ω)))
    let a := ∫ ω in G, |R ω - 1| ^ 2 ∂disorderLaw
    let b := ∫ ω in G, Real.sqrt (Ecommon ω) ^ 2 ∂disorderLaw
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hb : 0 ≤ b := by dsimp [b]; positivity
    have hprodBound : a * b ≤ (|C₁| * |Ccommon|) / L ^ 2 := by
      dsimp [a, b]
      rw [hrootEq]
      calc
        _ ≤ (|C₁| / L) * (|Ccommon| / L) :=
          mul_le_mul htotalDelta hcommonAbs
            (integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
              futureEnergy_nonneg β (t s) N (Cprof ω)))
            (div_nonneg (abs_nonneg C₁) hL.le)
        _ = _ := by field_simp
    have hQ : 0 ≤ |C₁| * |Ccommon| := by positivity
    have htarget : 0 ≤ Real.sqrt (|C₁| * |Ccommon|) / L := by positivity
    have hcsSq : (Real.sqrt a * Real.sqrt b) ^ 2 ≤
        (Real.sqrt (|C₁| * |Ccommon|) / L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb, div_pow, Real.sq_sqrt hQ]
      exact hprodBound
    have hcs : Real.sqrt a * Real.sqrt b ≤ Real.sqrt (|C₁| * |Ccommon|) / L :=
      (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) htarget).1 hcsSq
    calc
      _ ≤ Real.sqrt a * Real.sqrt b := by simpa [a, b] using hCauchy.2
      _ ≤ _ := hcs
  have hsuppTerm (u : ℕ) (hu : u ∈ I) (ω : Disorder) (y : Site) (hy : y ∉ S) :
      η u ω y = 0 := by
    dsimp [η]
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro hmem
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, hmem⟩)
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu, zero_div, mul_zero]
  have hsumSupport (ω : Disorder) (y : Site) (hy : y ∉ S) : Aprof ω y = 0 := by
    dsimp [Aprof]
    apply Finset.sum_eq_zero
    intro u hu
    exact hsuppTerm u hu ω y hy
  have hcommonSupport (ω : Disorder) (y : Site) (hy : y ∉ S) : Cprof ω y = 0 := by
    dsimp [Cprof, commonCorrection]
    apply Finset.sum_eq_zero
    intro u hu
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro hmem
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, hmem⟩)
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu, zero_div]
  have hηmeas (u : ℕ) (hu : u ∈ I) (y : Site) :
      Measurable[disorderPast (t s)] (η u · y) := by
    dsimp [η]
    have hu' := Finset.mem_Icc.mp hu
    have hOpenMeas : Measurable[disorderPast (t s)]
        (fun ω => openCorrector β t u s ω y) := by
      rw [← Gaussian.disorderBlock_zero (t s)]
      exact (measurable_openCorrector_on_block β t ht u s (by omega) hu'.2 y).mono
        (Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl) le_rfl
    have hRatioMeas : Measurable[disorderPast (t s)]
        (fun ω => blockRatio β t r (u - 1) ω) := by
      by_cases hru : r < u
      · rw [← Gaussian.disorderBlock_zero (t s)]
        exact (measurable_blockRatio_on_block β t ht r (u - 1) (by omega)).mono
          (Gaussian.disorderBlock_mono (Nat.zero_le _) (ht (by omega))) le_rfl
      · have hur : u = r := by omega
        subst u
        have hR : blockRatio β t r (r - 1) = fun _ => 1 := by
          funext ω
          exact blockRatio_empty β t r hr ω
        rw [hR]
        exact measurable_const
    exact (hRatioMeas.sub_const 1).mul hOpenMeas
  have hsumMeas (y : Site) :
      Measurable[disorderPast (t s)] (fun ω => Aprof ω y) := by
    dsimp [Aprof]
    exact Finset.measurable_sum _ fun u hu => hηmeas u hu y
  have hAmeasPast : Measurable[disorderPast (t s)] Eapprox := by
    dsimp [Eapprox, Aprof]
    exact measurable_futureEnergy β hts
      (fun ω y => ∑ u ∈ I, η u ω y) S hsumSupport hsumMeas
  have hAmeas : Measurable Eapprox :=
    hAmeasPast.mono (by
      rw [← Gaussian.disorderBlock_zero (t s)]
      exact Gaussian.disorderBlock_le 0 (t s)) le_rfl
  have htermInt (u : ℕ) (hu : u ∈ I) :
      IntegrableOn (fun ω => futureEnergy β (t s) N (η u ω)) G disorderLaw := by
    have hu' := Finset.mem_Icc.mp hu
    have hRatioU : r < u →
        ∫ ω in blockGoodSet β t r (u - 1),
          (blockRatio β t r (u - 1) ω - 1) ^ 2 ∂disorderLaw ≤
            C₁ / ((K : ℝ) - (u - 1)) := by
      intro hru
      exact hRatio u hru hu'.2
    have hOpenU := hOpen u hu'.1 hu'.2
    exact (ratioFluctuationOpenCorrectorTerm_integral_le β t N r s K u ht hr
      hu'.1 hu'.2 hsK hts C₀ C₁ θ hθ0 hθ1 hRatioU hOpenU).1
  let q : ℕ → ℝ := fun u => θ ^ (s - u)
  have hq (u : ℕ) (hu : u ∈ I) : 0 < q u := by
    dsimp [q]
    exact pow_pos hθ0 _
  have hgeom := sum_Icc_pow_reverse_le_inv_one_sub_of_le
    hθ0.le hθ1 (r := r) (s := s)
  have htermBound (u : ℕ) (hu : u ∈ I) :
      ∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw ≤
        |C₁| * |C₀| * θ ^ (2 * (s - u)) / L ^ 2 := by
    have hu' := Finset.mem_Icc.mp hu
    have hRatioU : r < u →
        ∫ ω in blockGoodSet β t r (u - 1),
          (blockRatio β t r (u - 1) ω - 1) ^ 2 ∂disorderLaw ≤
            C₁ / ((K : ℝ) - (u - 1)) := by
      intro hru
      exact hRatio u hru hu'.2
    have hOpenU := hOpen u hu'.1 hu'.2
    simpa [G, η, L] using
      (ratioFluctuationOpenCorrectorTerm_integral_le β t N r s K u ht hr
        hu'.1 hu'.2 hsK hts C₀ C₁ θ hθ0 hθ1 hRatioU hOpenU).2
  have htermDivBound (u : ℕ) (hu : u ∈ I) :
      (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u ≤
        (|C₁| * |C₀| / L ^ 2) * q u := by
    have hu' := Finset.mem_Icc.mp hu
    have hpow : θ ^ (2 * (s - u)) = q u ^ 2 := by
      dsimp [q]
      rw [show 2 * (s - u) = (s - u) + (s - u) by omega, pow_add]
      ring
    calc
      _ ≤ (|C₁| * |C₀| * θ ^ (2 * (s - u)) / L ^ 2) / q u :=
        div_le_div_of_nonneg_right (htermBound u hu) (hq u hu).le
      _ = (|C₁| * |C₀| / L ^ 2) * q u := by
        rw [hpow]
        field_simp [ne_of_gt (hq u hu), ne_of_gt hL]
  have hweightedSumBound :
      (∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u) ≤
        (|C₁| * |C₀| / L ^ 2) * ∑ u ∈ I, q u := by
    calc
      _ ≤ ∑ u ∈ I, ((|C₁| * |C₀| / L ^ 2) * q u) :=
        Finset.sum_le_sum fun u hu => htermDivBound u hu
      _ = (|C₁| * |C₀| / L ^ 2) * ∑ u ∈ I, q u := by
        rw [Finset.mul_sum]
  have hweightedSumBound' :
      (∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u) ≤
        (|C₁| * |C₀| / L ^ 2) * (1 / (1 - θ)) := by
    calc
      _ ≤ (|C₁| * |C₀| / L ^ 2) * ∑ u ∈ I, q u := hweightedSumBound
      _ ≤ (|C₁| * |C₀| / L ^ 2) * (1 / (1 - θ)) :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hAint := integrableOn_futureEnergy_finset_sum_le_weighted β hts S I G η
    q hsuppTerm hηmeas hq htermInt
  have hweightedSumNonneg : 0 ≤
      ∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u := by
    apply Finset.sum_nonneg
    intro u hu
    apply div_nonneg
    · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
        futureEnergy_nonneg β (t s) N (η u ω))
    · exact (hq u hu).le
  have hgeomNonneg : 0 ≤ 1 / (1 - θ) := by positivity
  have hAenergyBound :
      ∫ ω in G, Eapprox ω ∂disorderLaw ≤
        (Real.sqrt (|C₁| * |C₀|) / ((1 - θ) * L)) ^ 2 := by
    calc
      _ ≤ (∑ u ∈ I, q u) *
          ∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u := by
        simpa [Eapprox] using hAint.2
      _ ≤ (1 / (1 - θ)) *
          ((|C₁| * |C₀| / L ^ 2) * (1 / (1 - θ))) :=
        mul_le_mul hgeom hweightedSumBound' hweightedSumNonneg hgeomNonneg
      _ = (Real.sqrt (|C₁| * |C₀|) / ((1 - θ) * L)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ |C₁| * |C₀|)]
        field_simp [ne_of_gt (sub_pos.mpr hθ1), ne_of_gt hL]
  have hAroot := setIntegral_sqrt_le_sqrt Eapprox G hAmeas
    (fun ω => futureEnergy_nonneg β (t s) N (Aprof ω)) hAint.1
  have hArootBound :
      ∫ ω in G, Real.sqrt (Eapprox ω) ∂disorderLaw ≤
        Real.sqrt (|C₁| * |C₀|) / ((1 - θ) * L) := by
    calc
      _ ≤ Real.sqrt (∫ ω in G, Eapprox ω ∂disorderLaw) := hAroot.2
      _ ≤ Real.sqrt ((Real.sqrt (|C₁| * |C₀|) / ((1 - θ) * L)) ^ 2) :=
        Real.sqrt_le_sqrt hAenergyBound
      _ = _ := by
        rw [Real.sqrt_sq_eq_abs]
        exact abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hPprofile (ω : Disorder) : P ω = Q ω := by
    funext y
    dsimp [P, Q, R, Cprof, Aprof, η]
    exact smoothedEndpointDist_sub_commonCorrection_eq β ht hr hrs ω y
  have hQdecomp (ω : Disorder) : Q ω =
      (R ω)⁻¹ • Aprof ω + ((1 - R ω) / R ω) • Cprof ω := by
    funext y
    simp [Q]
  have hQsupport (ω : Disorder) (y : Site) (hy : y ∉ S) : Q ω y = 0 := by
    dsimp [Q]
    rw [hsumSupport ω y hy, hcommonSupport ω y hy]
    simp
  have hQcoord (y : Site) : Measurable[disorderPast (t s)] (Q · y) := by
    have hRpast : Measurable[disorderPast (t s)] R := by
      rw [← Gaussian.disorderBlock_zero (t s)]
      exact hRatioMeasBlock.mono
        (Gaussian.disorderBlock_mono (Nat.zero_le _) le_rfl) le_rfl
    exact (hRpast.inv.mul (hsumMeas y)).add
      (((measurable_const.sub hRpast).div hRpast).mul
        (measurable_commonCorrection_coordinate β t r s ht hr hrs y))
  have hQenergyPast : Measurable[disorderPast (t s)]
      (fun ω => futureEnergy β (t s) N (Q ω)) :=
    measurable_futureEnergy β hts Q S hQsupport hQcoord
  have hQenergy : Measurable (fun ω => futureEnergy β (t s) N (Q ω)) :=
    hQenergyPast.mono (by
      rw [← Gaussian.disorderBlock_zero (t s)]
      exact Gaussian.disorderBlock_le 0 (t s)) le_rfl
  have hPenergy : Measurable (fun ω => futureEnergy β (t s) N (P ω)) := by
    have hEq : (fun ω => futureEnergy β (t s) N (P ω)) =
        fun ω => futureEnergy β (t s) N (Q ω) := by
      funext ω
      rw [hPprofile ω]
    rw [hEq]
    exact hQenergy
  have hscaleA (ω : Disorder) :
      futureEnergy β (t s) N ((R ω)⁻¹ • Aprof ω) = (R ω)⁻¹ ^ 2 * Eapprox ω := by
    simpa [Eapprox] using futureEnergy_smul β (t s) N ((R ω)⁻¹) (Aprof ω) S
      (fun y hy => hsumSupport ω y hy)
  have hscaleC (ω : Disorder) :
      futureEnergy β (t s) N (((1 - R ω) / R ω) • Cprof ω) =
        ((1 - R ω) / R ω) ^ 2 * Ecommon ω := by
    simpa [Ecommon] using futureEnergy_smul β (t s) N ((1 - R ω) / R ω)
      (Cprof ω) S (fun y hy => hcommonSupport ω y hy)
  have hrootQ (ω : Disorder) :
      Real.sqrt (futureEnergy β (t s) N (Q ω)) ≤
        |(R ω)⁻¹| * Real.sqrt (Eapprox ω) +
          |(1 - R ω) / R ω| * Real.sqrt (Ecommon ω) := by
    rw [hQdecomp ω]
    calc
      _ ≤ Real.sqrt (futureEnergy β (t s) N ((R ω)⁻¹ • Aprof ω)) +
          Real.sqrt (futureEnergy β (t s) N (((1 - R ω) / R ω) • Cprof ω)) :=
        sqrt_futureEnergy_add_le β (t s) N _ _ S
          (fun y hy => by simp [hsumSupport ω y hy])
          (fun y hy => by simp [hcommonSupport ω y hy])
      _ = |(R ω)⁻¹| * Real.sqrt (Eapprox ω) +
          |(1 - R ω) / R ω| * Real.sqrt (Ecommon ω) := by
        rw [hscaleA, hscaleC, Real.sqrt_mul (sq_nonneg ((R ω)⁻¹)),
          Real.sqrt_sq_eq_abs, Real.sqrt_mul (sq_nonneg ((1 - R ω) / R ω)),
          Real.sqrt_sq_eq_abs]
  have hrootPBound (ω : Disorder) (hω : ω ∈ PG) :
      Real.sqrt (futureEnergy β (t s) N (P ω)) ≤
        2 * Real.sqrt (Eapprox ω) +
          2 * (|R ω - 1| * Real.sqrt (Ecommon ω)) := by
    have hApos : 0 ≤ Real.sqrt (Eapprox ω) := Real.sqrt_nonneg _
    have hCpos : 0 ≤ Real.sqrt (Ecommon ω) := Real.sqrt_nonneg _
    calc
      _ = Real.sqrt (futureEnergy β (t s) N (Q ω)) := by rw [hPprofile ω]
      _ ≤ |(R ω)⁻¹| * Real.sqrt (Eapprox ω) +
          |(1 - R ω) / R ω| * Real.sqrt (Ecommon ω) := hrootQ ω
      _ ≤ 2 * Real.sqrt (Eapprox ω) +
          (2 * |R ω - 1|) * Real.sqrt (Ecommon ω) :=
        add_le_add
          (mul_le_mul_of_nonneg_right (hRinv ω hω) hApos)
          (mul_le_mul_of_nonneg_right (hRdefect ω hω) hCpos)
      _ = 2 * Real.sqrt (Eapprox ω) +
          2 * (|R ω - 1| * Real.sqrt (Ecommon ω)) := by ring
  have hArootPG : IntegrableOn (fun ω => Real.sqrt (Eapprox ω)) PG disorderLaw :=
    hAroot.1.mono_set hPGsubset
  have hCauchyPG : IntegrableOn (fun ω => |R ω - 1| * Real.sqrt (Ecommon ω))
      PG disorderLaw := hCauchy.1.mono_set hPGsubset
  have hRhsInt : IntegrableOn (fun ω =>
      2 * Real.sqrt (Eapprox ω) + 2 * (|R ω - 1| * Real.sqrt (Ecommon ω)))
      PG disorderLaw := hArootPG.const_mul 2 |>.add (hCauchyPG.const_mul 2)
  have hProotInt : IntegrableOn (fun ω =>
      Real.sqrt (futureEnergy β (t s) N (P ω))) PG disorderLaw := by
    apply hRhsInt.mono' hPenergy.sqrt.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hPGmeas] with ω hω
    have hRhsNonneg : 0 ≤
        2 * Real.sqrt (Eapprox ω) + 2 * (|R ω - 1| * Real.sqrt (Ecommon ω)) := by
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg hRhsNonneg] using hrootPBound ω hω
  have hProotIntegralBound :
      ∫ ω in PG, Real.sqrt (futureEnergy β (t s) N (P ω)) ∂disorderLaw ≤
        2 * (∫ ω in PG, Real.sqrt (Eapprox ω) ∂disorderLaw) +
          2 * (∫ ω in PG, |R ω - 1| * Real.sqrt (Ecommon ω) ∂disorderLaw) := by
    calc
      _ ≤ ∫ ω in PG,
          2 * Real.sqrt (Eapprox ω) + 2 * (|R ω - 1| * Real.sqrt (Ecommon ω))
          ∂disorderLaw := integral_mono_ae hProotInt hRhsInt (by
            filter_upwards [ae_restrict_mem hPGmeas] with ω hω
            exact hrootPBound ω hω)
      _ = _ := by
        rw [integral_add (hArootPG.const_mul 2) (hCauchyPG.const_mul 2),
          integral_const_mul, integral_const_mul]
  have hArootSubset :
      ∫ ω in PG, Real.sqrt (Eapprox ω) ∂disorderLaw ≤
        ∫ ω in G, Real.sqrt (Eapprox ω) ∂disorderLaw :=
    setIntegral_mono_set hAroot.1
      (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (Eapprox ω))
      (Filter.Eventually.of_forall fun ω hω => hPGsubset hω)
  have hCauchySubset :
      ∫ ω in PG, |R ω - 1| * Real.sqrt (Ecommon ω) ∂disorderLaw ≤
        ∫ ω in G, |R ω - 1| * Real.sqrt (Ecommon ω) ∂disorderLaw :=
    setIntegral_mono_set hCauchy.1
      (Filter.Eventually.of_forall fun ω => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (Filter.Eventually.of_forall fun ω hω => hPGsubset hω)
  refine ⟨hProotInt, ?_⟩
  calc
    _ ≤ 2 * (∫ ω in PG, Real.sqrt (Eapprox ω) ∂disorderLaw) +
          2 * (∫ ω in PG, |R ω - 1| * Real.sqrt (Ecommon ω) ∂disorderLaw) :=
      hProotIntegralBound
    _ ≤ 2 * (∫ ω in G, Real.sqrt (Eapprox ω) ∂disorderLaw) +
          2 * (∫ ω in G, |R ω - 1| * Real.sqrt (Ecommon ω) ∂disorderLaw) :=
      add_le_add (mul_le_mul_of_nonneg_left hArootSubset (by norm_num))
        (mul_le_mul_of_nonneg_left hCauchySubset (by norm_num))
    _ ≤ 2 * (Real.sqrt (|C₁| * |C₀|) / ((1 - θ) * L)) +
          2 * (Real.sqrt (|C₁| * |Ccommon|) / L) :=
      add_le_add (mul_le_mul_of_nonneg_left hArootBound (by norm_num))
        (mul_le_mul_of_nonneg_left hCauchyBound (by norm_num))
    _ = 2 * (Real.sqrt (|C₁| * |C₀|) / (1 - θ) +
          Real.sqrt (|C₁| * |Ccommon|)) / ((K : ℝ) - s) := by
      dsimp [L]
      field_simp [ne_of_gt (sub_pos.mpr hθ1), ne_of_gt hL]

private theorem weightedOpenCorrectorTerm_integral_le
    (β : ℝ) (t : ℕ → ℕ) (N r s K u : ℕ) (ht : Monotone t)
    (hr : 1 ≤ r) (hru : r ≤ u) (hus : u ≤ s) (hsK : s + 2 ≤ K)
    (hts : t s ≤ N) (θ C₀ C₁ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hRatio : r < u →
      ∫ ω in blockGoodSet β t r (u - 1),
        (blockRatio β t r (u - 1) ω - 1) ^ 2 ∂disorderLaw ≤
          C₁ / ((K : ℝ) - (u - 1)))
    (hOpen :
      ∫ ω in blockGoodSet β t u s,
        futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
          C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u)) :
    IntegrableOn (fun ω => futureEnergy β (t s) N (fun y =>
      blockRatio β t r (u - 1) ω * openCorrector β t u s ω y))
      (blockGoodSet β t r s) disorderLaw ∧
    ∫ ω in blockGoodSet β t r s,
      futureEnergy β (t s) N (fun y =>
        blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) ∂disorderLaw ≤
      (2 + 2 * |C₁|) * |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - s) := by
  classical
  let G := blockGoodSet β t r s
  let G₁ := blockGoodSet β t r (u - 1)
  let G₂ := blockGoodSet β t u s
  let R : Disorder → ℝ := fun ω => blockRatio β t r (u - 1) ω
  let E : Disorder → ℝ := fun ω => futureEnergy β (t s) N (openCorrector β t u s ω)
  let F : Disorder → ℝ := Set.indicator G₁ (fun ω => R ω ^ 2)
  let H : Disorder → ℝ := Set.indicator G₂ E
  have hIcc : Finset.Icc r s = Finset.Icc r (u - 1) ∪ Finset.Icc u s := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hG : G = G₁ ∩ G₂ := by
    ext ω
    change (∀ i ∈ Finset.Icc r s, |blockMass β t i ω - 1| ≤ 1 / 2) ↔
      ((∀ i ∈ Finset.Icc r (u - 1), |blockMass β t i ω - 1| ≤ 1 / 2) ∧
        ∀ i ∈ Finset.Icc u s, |blockMass β t i ω - 1| ≤ 1 / 2)
    rw [hIcc]
    constructor
    · intro h
      constructor
      · intro i hi
        exact h i (Finset.mem_union_left _ hi)
      · intro i hi
        exact h i (Finset.mem_union_right _ hi)
    · rintro ⟨h₁, h₂⟩ i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · exact h₁ i hi
      · exact h₂ i hi
  have hG₁meas : MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))] G₁ :=
    measurable_blockGoodSet_on_block β t ht r (u - 1)
  have hG₂meas : MeasurableSet[Gaussian.disorderBlock (t (u - 1)) (t s)] G₂ :=
    measurable_blockGoodSet_on_block β t ht u s
  have hRmeas : Measurable[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))] R := by
    by_cases hurr : u = r
    · subst u
      have hR : R = fun _ => 1 := by
        funext ω
        exact blockRatio_empty β t r hr ω
      rw [hR]
      exact measurable_const
    · have hru' : r < u := lt_of_le_of_ne hru (Ne.symm hurr)
      exact measurable_blockRatio_on_block β t ht r (u - 1) (by omega)
  have hEmeas : Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)] E := by
    exact measurable_futureEnergy_openCorrector_on_block β ht (by omega) hus hts
  have hBlock₁Global := Gaussian.disorderBlock_le (t (r - 1)) (t (u - 1))
  have hBlock₂Global := Gaussian.disorderBlock_le (t (u - 1)) (t s)
  have hG₁global : MeasurableSet G₁ := hBlock₁Global G₁ hG₁meas
  have hG₂global : MeasurableSet G₂ := hBlock₂Global G₂ hG₂meas
  have hRglobal : Measurable R := hRmeas.mono hBlock₁Global le_rfl
  have hEglobal : Measurable E := hEmeas.mono hBlock₂Global le_rfl
  have hFmeas : Measurable[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))] F := by
    change Measurable[Gaussian.disorderBlock (t (r - 1)) (t (u - 1))]
      (Set.indicator G₁ (fun ω => R ω ^ 2))
    exact (hRmeas.pow_const 2).indicator hG₁meas
  have hHmeas : Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)] H := by
    change Measurable[Gaussian.disorderBlock (t (u - 1)) (t s)]
      (Set.indicator G₂ E)
    exact hEmeas.indicator hG₂meas
  have hFglobal : Measurable F := hFmeas.mono hBlock₁Global le_rfl
  have hHglobal : Measurable H := hHmeas.mono hBlock₂Global le_rfl
  have hR2Int : IntegrableOn (fun ω => R ω ^ 2) G₁ disorderLaw := by
    by_cases hurr : u = r
    · subst u
      have hR : R = fun _ => 1 := by
        funext ω
        exact blockRatio_empty β t r hr ω
      rw [hR]
      simp
    · have hru' : r < u := lt_of_le_of_ne hru (Ne.symm hurr)
      have hΔInt := OnePoint.integrableOn_blockRatio_sub_one_sq β ht
        (r := r) (s := u - 1) hr (by omega)
      have hright : IntegrableOn (fun ω => 2 * (R ω - 1) ^ 2 + 2) G₁ disorderLaw := by
        have hΔInt' : IntegrableOn (fun ω => (R ω - 1) ^ 2) G₁ disorderLaw := by
          simpa [G₁, R] using hΔInt
        exact (hΔInt'.const_mul 2).add
          (integrable_const (μ := disorderLaw) (2 : ℝ)).integrableOn
      apply hright.mono' (hRglobal.pow_const 2).aestronglyMeasurable
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (R ω))]
      nlinarith [sq_nonneg (R ω - 2)]
  have hFint : Integrable F disorderLaw := hR2Int.integrable_indicator hG₁global
  have hEintOn : IntegrableOn E G₂ disorderLaw := by
    exact integrableOn_futureEnergy_openCorrector β t N u s ht (by omega) hus hts
  have hHint : Integrable H disorderLaw := hEintOn.integrable_indicator hG₂global
  have hind : IndepFun F H disorderLaw := by
    rw [IndepFun_iff]
    intro X Y hX hY
    exact (Indep_iff _ _ _).1
      (Gaussian.indep_disorderBlock_of_le (m := t (r - 1)) (n := t (u - 1))
        (a := t (u - 1)) (b := t s) le_rfl) X Y
      (hFmeas.comap_le X hX) (hHmeas.comap_le Y hY)
  have hprodInt : Integrable (fun ω => F ω * H ω) disorderLaw :=
    hind.integrable_mul hFint hHint
  have hsupport : ∀ ω y, y ∉ openCorrectorNumeratorSupport t u s →
      openCorrector β t u s ω y = 0 := by
    intro ω y hy
    unfold openCorrector
    rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hy, zero_div]
  have hscale (ω : Disorder) :
      futureEnergy β (t s) N (fun y => R ω * openCorrector β t u s ω y) =
        R ω ^ 2 * E ω := by
    have h := futureEnergy_smul β (t s) N (R ω) (openCorrector β t u s ω)
      (openCorrectorNumeratorSupport t u s) (hsupport ω)
    have hprofile : (fun y => R ω * openCorrector β t u s ω y) =
        R ω • openCorrector β t u s ω := by
      funext y
      rfl
    rw [hprofile]
    exact h
  have hprodEq : (fun ω => F ω * H ω) =
      Set.indicator G (fun ω => futureEnergy β (t s) N (fun y =>
        blockRatio β t r (u - 1) ω * openCorrector β t u s ω y)) := by
    funext ω
    by_cases hω : ω ∈ G
    · have hω12 : ω ∈ G₁ ∩ G₂ := hG ▸ hω
      rcases hω12 with ⟨hω₁, hω₂⟩
      change Set.indicator G₁ (fun ω => R ω ^ 2) ω *
          Set.indicator G₂ E ω =
        Set.indicator G (fun ω => futureEnergy β (t s) N (fun y =>
          blockRatio β t r (u - 1) ω * openCorrector β t u s ω y)) ω
      rw [Set.indicator_of_mem hω₁, Set.indicator_of_mem hω₂,
        Set.indicator_of_mem hω]
      rw [← hscale ω]
    · have hnot : ¬ (ω ∈ G₁ ∧ ω ∈ G₂) := by
        intro hpair
        apply hω
        rw [hG]
        exact hpair
      rcases not_and_or.mp hnot with hω₁ | hω₂
      · simp [F, H, Set.indicator, G, hω, hω₁]
      · simp [F, H, Set.indicator, G, hω, hω₂]
  have hGblock :
      MeasurableSet[Gaussian.disorderBlock (t (r - 1)) (t s)] G :=
    measurable_blockGoodSet_on_block β t ht r s
  have hBlockGGlobal := Gaussian.disorderBlock_le (t (r - 1)) (t s)
  have hGglobal : MeasurableSet G := hBlockGGlobal G hGblock
  have hprodEqAE : (fun ω => F ω * H ω) =ᵐ[disorderLaw]
      Set.indicator G (fun ω => futureEnergy β (t s) N (fun y =>
        blockRatio β t r (u - 1) ω * openCorrector β t u s ω y)) :=
    Filter.Eventually.of_forall fun ω => congrFun hprodEq ω
  have hEqOn : (fun ω => F ω * H ω) =ᵐ[disorderLaw.restrict G]
      (fun ω => futureEnergy β (t s) N (fun y =>
        blockRatio β t r (u - 1) ω * openCorrector β t u s ω y)) := by
    filter_upwards [ae_restrict_mem hGglobal]
      with ω hω
    simpa [hω] using congrFun hprodEq ω
  have htermInt : IntegrableOn (fun ω => futureEnergy β (t s) N (fun y =>
      blockRatio β t r (u - 1) ω * openCorrector β t u s ω y)) G disorderLaw :=
    hprodInt.integrableOn.congr hEqOn
  have htermIntEq :
      ∫ ω in G, futureEnergy β (t s) N (fun y =>
          blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) ∂disorderLaw =
        (∫ ω in G₁, R ω ^ 2 ∂disorderLaw) * (∫ ω in G₂, E ω ∂disorderLaw) := by
    calc
      _ = ∫ ω, F ω * H ω ∂disorderLaw := by
        calc
          _ = ∫ ω, Set.indicator G (fun ω => futureEnergy β (t s) N (fun y =>
                blockRatio β t r (u - 1) ω * openCorrector β t u s ω y)) ω ∂disorderLaw :=
              (integral_indicator hGglobal).symm
          _ = ∫ ω, F ω * H ω ∂disorderLaw := integral_congr_ae hprodEqAE.symm
      _ = (∫ ω, F ω ∂disorderLaw) * ∫ ω, H ω ∂disorderLaw :=
        hind.integral_fun_mul_eq_mul_integral hFglobal.aestronglyMeasurable
          hHglobal.aestronglyMeasurable
      _ = (∫ ω in G₁, R ω ^ 2 ∂disorderLaw) *
          (∫ ω in G₂, E ω ∂disorderLaw) := by
        simpa [F, H] using congrArg₂ (fun x y : ℝ => x * y)
          (integral_indicator hG₁global) (integral_indicator hG₂global)
  let D : ℝ := 2 + 2 * |C₁|
  have hRbound : ∫ ω in G₁, R ω ^ 2 ∂disorderLaw ≤ D := by
    by_cases hurr : u = r
    · subst u
      have hG₁ : G₁ = Set.univ := by
        simp [G₁, blockGoodSet, Finset.Icc_eq_empty_of_lt (show r - 1 < r by omega)]
      have hR : R = fun _ => 1 := by
        funext ω
        exact blockRatio_empty β t r hr ω
      have hI : ∫ ω in G₁, R ω ^ 2 ∂disorderLaw = 1 := by
        simp [G₁, R, hG₁, hR]
      rw [hI]
      dsimp [D]
      nlinarith [abs_nonneg C₁]
    · have hru' : r < u := lt_of_le_of_ne hru (Ne.symm hurr)
      have hDelta := hRatio hru'
      have hden : 0 < (K : ℝ) - (u - 1) := by
        have huCast : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (show 1 ≤ u by omega)
        have hKCast : (u : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show u ≤ K by omega)
        linarith
      have hdenone : 1 ≤ (K : ℝ) - (u - 1) := by
        have huCast : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast (show 1 ≤ u by omega)
        have hKCast : (u : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show u ≤ K by omega)
        linarith
      have hDeltaAbs : ∫ ω in G₁, (R ω - 1) ^ 2 ∂disorderLaw ≤
          |C₁| / ((K : ℝ) - (u - 1)) := by
        exact hDelta.trans (div_le_div_of_nonneg_right (le_abs_self C₁) hden.le)
      have hDeltaBound : ∫ ω in G₁, (R ω - 1) ^ 2 ∂disorderLaw ≤ |C₁| := by
        calc
          _ ≤ |C₁| / ((K : ℝ) - (u - 1)) := hDeltaAbs
          _ ≤ |C₁| := div_le_self (abs_nonneg C₁) hdenone
      have hpoint (ω : Disorder) : R ω ^ 2 ≤ 2 * (R ω - 1) ^ 2 + 2 := by
        nlinarith [sq_nonneg (R ω - 2)]
      have hright : IntegrableOn (fun ω => 2 * (R ω - 1) ^ 2 + 2) G₁ disorderLaw := by
        have hΔInt := OnePoint.integrableOn_blockRatio_sub_one_sq β ht
          (r := r) (s := u - 1) hr (by omega)
        have hΔInt' : IntegrableOn (fun ω => (R ω - 1) ^ 2) G₁ disorderLaw := by
          simpa [G₁, R] using hΔInt
        change Integrable (fun ω => 2 * (R ω - 1) ^ 2 + 2)
          (disorderLaw.restrict G₁)
        change Integrable (fun ω => (R ω - 1) ^ 2) (disorderLaw.restrict G₁) at hΔInt'
        exact (hΔInt'.const_mul 2).add
          (integrable_const (μ := disorderLaw.restrict G₁) (2 : ℝ))
      have hmono := integral_mono_ae hR2Int hright
        (Filter.Eventually.of_forall hpoint)
      calc
        ∫ ω in G₁, R ω ^ 2 ∂disorderLaw ≤
            2 * (∫ ω in G₁, (R ω - 1) ^ 2 ∂disorderLaw) +
              ∫ ω in G₁, (2 : ℝ) ∂disorderLaw := by
                have hΔInt := OnePoint.integrableOn_blockRatio_sub_one_sq β ht
                  (r := r) (s := u - 1) hr (by omega)
                have hconstInt : IntegrableOn (fun _ : Disorder => (2 : ℝ)) G₁ disorderLaw := by
                  change Integrable (fun _ : Disorder => (2 : ℝ))
                    (disorderLaw.restrict G₁)
                  exact integrable_const (μ := disorderLaw.restrict G₁) (2 : ℝ)
                calc
                  _ ≤ ∫ ω in G₁, (2 * (R ω - 1) ^ 2 + 2) ∂disorderLaw := hmono
                  _ = 2 * (∫ ω in G₁, (R ω - 1) ^ 2 ∂disorderLaw) +
                        ∫ ω in G₁, (2 : ℝ) ∂disorderLaw := by
                    rw [integral_add (hΔInt.const_mul 2) hconstInt,
                      integral_const_mul]
        _ ≤ 2 * |C₁| + 2 := by
          have hconst : ∫ ω in G₁, (2 : ℝ) ∂disorderLaw ≤ 2 := by
            calc
              ∫ ω in G₁, (2 : ℝ) ∂disorderLaw ≤
                  ∫ ω, (2 : ℝ) ∂disorderLaw :=
                setIntegral_le_integral (integrable_const (μ := disorderLaw) (2 : ℝ))
                  (Filter.Eventually.of_forall fun ω => by norm_num)
              _ = 2 := by simp
          linarith
        _ = D := by simp [D]; ring
  have hOpenAbs : ∫ ω in G₂, E ω ∂disorderLaw ≤
      |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - s) := by
    have hOpenAbs₁ : ∫ ω in G₂, E ω ∂disorderLaw ≤
        |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := by
      have hden : 0 < (K : ℝ) - u := by
        have hn : 0 < K - u := by omega
        rw [← Nat.cast_sub (by omega : u ≤ K)]
        exact_mod_cast hn
      have hnonneg : 0 ≤ θ ^ (2 * (s - u)) := pow_nonneg hθ0.le _
      exact hOpen.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self C₀) hnonneg) hden.le)
    have hdenS : 0 < (K : ℝ) - s := by
      have hn : 0 < K - s := by omega
      rw [← Nat.cast_sub (by omega : s ≤ K)]
      exact_mod_cast hn
    have hdenLe : (K : ℝ) - s ≤ (K : ℝ) - u := by
      rw [← Nat.cast_sub (by omega : s ≤ K), ← Nat.cast_sub (by omega : u ≤ K)]
      exact_mod_cast Nat.sub_le_sub_left hus K
    calc
      _ ≤ |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := hOpenAbs₁
      _ ≤ |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - s) := by
        apply div_le_div_of_nonneg_left
        · positivity
        · exact hdenS
        · exact hdenLe
  have hprefixNonneg : 0 ≤ ∫ ω in G₁, R ω ^ 2 ∂disorderLaw :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (R ω))
  have hopenNonneg : 0 ≤ ∫ ω in G₂, E ω ∂disorderLaw :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
      futureEnergy_nonneg β (t s) N (openCorrector β t u s ω))
  have hDnonneg : 0 ≤ D := by positivity
  refine ⟨htermInt, ?_⟩
  rw [htermIntEq]
  calc
    (∫ ω in G₁, R ω ^ 2 ∂disorderLaw) *
        (∫ ω in G₂, E ω ∂disorderLaw) ≤ D *
          (|C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - s)) :=
      mul_le_mul hRbound hOpenAbs hopenNonneg hDnonneg
    _ = (2 + 2 * |C₁|) * |C₀| * θ ^ (2 * (s - u)) / ((K : ℝ) - s) := by
      simp [D]
      ring

private theorem weightedCorrection_integral_energy_le_of_terms
    (β : ℝ) (t : ℕ → ℕ) (N r s K : ℕ) (ht : Monotone t)
    (hr : 1 ≤ r) (hsK : s + 2 ≤ K) (hts : t s ≤ N)
    (θ B : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hB : 0 ≤ B)
    (hterm : ∀ u ∈ Finset.Icc r s,
      IntegrableOn (fun ω => futureEnergy β (t s) N (fun y =>
        blockRatio β t r (u - 1) ω * openCorrector β t u s ω y))
        (blockGoodSet β t r s) disorderLaw ∧
      ∫ ω in blockGoodSet β t r s,
        futureEnergy β (t s) N (fun y =>
          blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) ∂disorderLaw ≤
        B * θ ^ (2 * (s - u)) / ((K : ℝ) - s)) :
    IntegrableOn (fun ω => futureEnergy β (t s) N (weightedCorrection β t r s ω))
      (blockGoodSet β t r s) disorderLaw ∧
    ∫ ω in blockGoodSet β t r s,
      futureEnergy β (t s) N (weightedCorrection β t r s ω) ∂disorderLaw ≤
        B / (1 - θ) ^ 2 / ((K : ℝ) - s) := by
  classical
  let I := Finset.Icc r s
  let G := blockGoodSet β t r s
  let A := I.biUnion (fun u => openCorrectorNumeratorSupport t u s)
  let η : ℕ → Disorder → Site → ℝ := fun u ω y =>
    blockRatio β t r (u - 1) ω * openCorrector β t u s ω y
  let q : ℕ → ℝ := fun u => θ ^ (s - u)
  have hsupp (u : ℕ) (hu : u ∈ I) (ω : Disorder) (y : Site) (hy : y ∉ A) :
      η u ω y = 0 := by
    have hyu : y ∉ openCorrectorNumeratorSupport t u s := by
      intro hymem
      exact hy (Finset.mem_biUnion.mpr ⟨u, hu, hymem⟩)
    dsimp [η]
    have hzero : openCorrector β t u s ω y = 0 := by
      unfold openCorrector
      rw [openCorrectorNumerator_eq_zero_of_not_mem_support β t u s ω y hyu, zero_div]
    rw [hzero, mul_zero]
  have hmeas (u : ℕ) (hu : u ∈ I) (y : Site) :
      Measurable[disorderPast (t s)] (η u · y) := by
    have hu' := Finset.mem_Icc.mp hu
    have hRatio : Measurable[disorderPast (t s)]
        (fun ω => blockRatio β t r (u - 1) ω) := by
      by_cases hurr : u = r
      · subst u
        have hR : (fun ω => blockRatio β t r (r - 1) ω) = fun _ => 1 := by
          funext ω
          exact blockRatio_empty β t r hr ω
        rw [hR]
        exact measurable_const
      · have hru : r < u := lt_of_le_of_ne hu'.1 (Ne.symm hurr)
        have hlocal := measurable_blockRatio_on_block β t ht r (u - 1) (by omega)
        have hsub : Gaussian.disorderBlock (t (r - 1)) (t (u - 1)) ≤
            disorderPast (t s) := by
          rw [← Gaussian.disorderBlock_zero (t s)]
          exact Gaussian.disorderBlock_mono (Nat.zero_le _) (ht (by omega))
        exact hlocal.mono hsub le_rfl
    have hOpen : Measurable[disorderPast (t s)]
        (fun ω => openCorrector β t u s ω y) :=
      measurable_openCorrector_on_past β t ht u s (by omega) hu'.2 y
    exact hRatio.mul hOpen
  have hq (u : ℕ) (hu : u ∈ I) : 0 < q u := by
    dsimp [q]
    exact pow_pos hθ0 _
  have hgeom := sum_Icc_pow_reverse_le_inv_one_sub_of_le
    hθ0.le hθ1 (r := r) (s := s)
  have hdenS : 0 < (K : ℝ) - s := by
    have hn : 0 < K - s := by omega
    rw [← Nat.cast_sub (by omega : s ≤ K)]
    exact_mod_cast hn
  have hEi (u : ℕ) (hu : u ∈ I) :
      IntegrableOn (fun ω => futureEnergy β (t s) N (η u ω)) G disorderLaw := by
    simpa [G, η] using (hterm u hu).1
  have hEiDivBound (u : ℕ) (hu : u ∈ I) :
      (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u ≤
        B * q u / ((K : ℝ) - s) := by
    have hden : 0 < (K : ℝ) - s := by
      have hn : 0 < K - s := by omega
      rw [← Nat.cast_sub (by omega : s ≤ K)]
      exact_mod_cast hn
    have hu' := Finset.mem_Icc.mp hu
    calc
      _ ≤ (B * θ ^ (2 * (s - u)) / ((K : ℝ) - s)) / q u :=
        div_le_div_of_nonneg_right (by simpa [G, η] using (hterm u hu).2)
          (hq u hu).le
      _ = B * q u / ((K : ℝ) - s) := by
        dsimp [q]
        have hpow : 2 * (s - u) = (s - u) + (s - u) := by omega
        rw [hpow, pow_add]
        field_simp [ne_of_gt (hq u hu), ne_of_gt hden]
  have hweightedSumBound :
      (∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u) ≤
        (B / ((K : ℝ) - s)) * ∑ u ∈ I, q u := by
    calc
      _ ≤ ∑ u ∈ I, (B * q u / ((K : ℝ) - s)) :=
        Finset.sum_le_sum fun u hu => hEiDivBound u hu
      _ = (B / ((K : ℝ) - s)) * ∑ u ∈ I, q u := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        ring
  have hweightedSumBound' :
      (∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u) ≤
        (B / ((K : ℝ) - s)) * (1 / (1 - θ)) := by
    calc
      _ ≤ (B / ((K : ℝ) - s)) * ∑ u ∈ I, q u := hweightedSumBound
      _ ≤ (B / ((K : ℝ) - s)) * (1 / (1 - θ)) :=
        mul_le_mul_of_nonneg_left hgeom (div_nonneg hB hdenS.le)
  have hsum := integrableOn_futureEnergy_finset_sum_le_weighted β hts A I G η q
    hsupp hmeas hq hEi
  have hsumNonneg : 0 ≤
      ∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u := by
    apply Finset.sum_nonneg
    intro u hu
    apply div_nonneg
    · exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
        futureEnergy_nonneg β (t s) N (η u ω))
    · exact (hq u hu).le
  have hgeomNonneg : 0 ≤ 1 / (1 - θ) := by positivity
  have hbound :
      ∫ ω in G, futureEnergy β (t s) N (fun y => ∑ u ∈ I, η u ω y) ∂disorderLaw ≤
        B / (1 - θ) ^ 2 / ((K : ℝ) - s) := by
    calc
      _ ≤ (∑ u ∈ I, q u) *
          ∑ u ∈ I, (∫ ω in G, futureEnergy β (t s) N (η u ω) ∂disorderLaw) / q u := hsum.2
      _ ≤ (1 / (1 - θ)) *
          ((B / ((K : ℝ) - s)) * (1 / (1 - θ))) :=
        mul_le_mul hgeom hweightedSumBound' hsumNonneg hgeomNonneg
      _ = B / (1 - θ) ^ 2 / ((K : ℝ) - s) := by
        field_simp [ne_of_gt (sub_pos.mpr hθ1), ne_of_gt hdenS]
  have hprofile (ω : Disorder) :
      (fun y => ∑ u ∈ I, η u ω y) = weightedCorrection β t r s ω := by
    funext y
    simp [weightedCorrection, η, I]
  constructor
  · apply hsum.1.congr
    filter_upwards [] with ω
    rw [hprofile ω]
  · calc
      ∫ ω in G, futureEnergy β (t s) N (weightedCorrection β t r s ω) ∂disorderLaw =
          ∫ ω in G, futureEnergy β (t s) N (fun y => ∑ u ∈ I, η u ω y) ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [] with ω
            rw [hprofile ω]
      _ ≤ B / (1 - θ) ^ 2 / ((K : ℝ) - s) := hbound

/-- Uniformly in the parameter `ϑ ∈ [−A, A]`, for large `N` and block indices
`1 ≤ r ≤ s` with `s + 2 ≤ blockCount N ρ`, the future energy of the weighted correction is
integrable on the block good set, and its integral there is at most `C / (blockCount N ρ − s)`. -/
theorem weightedCorrection_integral_energy_le_of (hDiscrepancyStringInput : OpenStringBound)
    (hBlockRatioInput : RatioBoundP) (A : ℝ) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 2 ≤ blockCount N ρ →
          IntegrableOn (fun ω => futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
            (weightedCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω))
            (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s) disorderLaw ∧
          ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
            futureEnergy (criticalBeta ϑ N) (blockTime N ρ s) N
              (weightedCorrection (criticalBeta ϑ N) (blockTime N ρ) r s ω) ∂disorderLaw ≤
            C / ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨ρ₁₂, θ, hρ₁₂, hθ0, hθ1, hDiscrepancyStringInputA⟩ :=
    setIntegral_futureEnergy_openCorrector_le_of hDiscrepancyStringInput A
  obtain ⟨ρ₁₃, hρ₁₃, hBlockRatioInputA⟩ := hBlockRatioInput A
  let ρ₀ := max ρ₁₂ ρ₁₃
  have hρ₀ : 1 < ρ₀ := by
    exact lt_of_lt_of_le hρ₁₂ (le_max_left ρ₁₂ ρ₁₃)
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₂
  obtain ⟨C₀, hDiscrepancyStringInputρ₂⟩ := hDiscrepancyStringInputA ρ₂
  obtain ⟨C₁, hBlockRatioInputρ₂⟩ := hBlockRatioInputA ρ₂
  let B := (2 + 2 * |C₁|) * |C₀|
  let C := B / (1 - θ) ^ 2
  refine ⟨C, ?_⟩
  intro ρ hρ
  have hρ₁₂ρ : ρ₁₂ ≤ ρ := (le_max_left ρ₁₂ ρ₁₃).trans hρ.1
  have hρ₁₃ρ : ρ₁₃ ≤ ρ := (le_max_right ρ₁₂ ρ₁₃).trans hρ.1
  have hρstrict : 1 < ρ := lt_of_lt_of_le hρ₁₂ hρ₁₂ρ
  filter_upwards [hDiscrepancyStringInputρ₂ ρ ⟨hρ₁₂ρ, hρ.2⟩,
      hBlockRatioInputρ₂ ρ ⟨hρ₁₃ρ, hρ.2⟩, blockTime_monotone hρstrict] with
    N hDiscrepancyStringInputN hBlockRatioInputN hmono
  intro ϑ hϑ r s hr hrs hsK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let K := blockCount N ρ
  have htS : t s ≤ N := by
    have hsK' : s ≤ blockCount N ρ := by omega
    have htimeS := hmono hsK'
    have hKpos : 0 < blockCount N ρ := by unfold blockCount; omega
    have hterminal : blockTime N ρ (blockCount N ρ) = N := by
      simp [blockTime, Nat.ne_of_gt hKpos]
    rw [hterminal] at htimeS
    exact htimeS
  have hB : 0 ≤ B := by positivity
  have hterms : ∀ u ∈ Finset.Icc r s,
      IntegrableOn (fun ω => futureEnergy β (t s) N (fun y =>
        blockRatio β t r (u - 1) ω * openCorrector β t u s ω y))
        (blockGoodSet β t r s) disorderLaw ∧
      ∫ ω in blockGoodSet β t r s,
        futureEnergy β (t s) N (fun y =>
          blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) ∂disorderLaw ≤
        B * θ ^ (2 * (s - u)) / ((K : ℝ) - s) := by
    intro u hu
    have hu' := Finset.mem_Icc.mp hu
    have hOpen :
        ∫ ω in blockGoodSet β t u s,
          futureEnergy β (t s) N (openCorrector β t u s ω) ∂disorderLaw ≤
            C₀ * θ ^ (2 * (s - u)) / ((K : ℝ) - u) := by
      exact hDiscrepancyStringInputN ϑ hϑ u s (by omega) hu'.2 (by simpa [K] using hsK)
    have hRatio : r < u →
        ∫ ω in blockGoodSet β t r (u - 1),
          (blockRatio β t r (u - 1) ω - 1) ^ 2 ∂disorderLaw ≤
            C₁ / ((K : ℝ) - (u - 1)) := by
      intro hru
      have huone : 1 ≤ u := by omega
      have hBlockRatioInput := hBlockRatioInputN ϑ hϑ r (u - 1) hr (by omega) (by omega)
      simpa [β, t, K, Nat.cast_sub huone, Nat.cast_one] using hBlockRatioInput.2
    simpa [β, t, B] using weightedOpenCorrectorTerm_integral_le β t N r s K u
      hmono hr hu'.1 hu'.2 (by simpa [K] using hsK) htS θ C₀ C₁ hθ0 hθ1
      hRatio hOpen
  have hweighted := weightedCorrection_integral_energy_le_of_terms β t N r s K hmono
    hr (by simpa [K] using hsK) htS θ B hθ0 hθ1 hB hterms
  refine ⟨?_, ?_⟩
  · simpa [β, t] using hweighted.1
  · simpa [β, t, C, B, K] using hweighted.2


end Critical2DKPZ.FutureProfiles

end
