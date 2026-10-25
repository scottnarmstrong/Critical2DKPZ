/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.LeftTailBounds
public import Critical2DKPZ.FutureProfiles.ConditionalNegativeMoments
public import Critical2DKPZ.FutureProfiles.ProfileEstimateCorrections
public import Critical2DKPZ.FutureProfiles.SplitInputs
public import Critical2DKPZ.FutureProfiles.EndpointTranslation
public import Critical2DKPZ.Blocks.GridAlignment
public import Critical2DKPZ.LogNormality.LatticeInputs
public import Critical2DKPZ.Smoothing.EndpointDistribution
import Mathlib.Tactic

/-! # Adaptive endpoint left tails from profile estimates -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open Critical2DKPZ.OnePoint Critical2DKPZ.Blocks Critical2DKPZ.Collision

namespace Critical2DKPZ.FutureProfiles

/-- Cauchy–Schwarz for the product of square roots of integrable nonnegative functions. -/
theorem integral_sqrt_mul_sqrt_le_of_integrable
    {μ : Measure Disorder} [IsFiniteMeasure μ] (f g : Disorder → ℝ)
    (hfmeas : Measurable f) (hgmeas : Measurable g)
    (hfint : Integrable f μ) (hgint : Integrable g μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω) :
    Integrable (fun ω => Real.sqrt (f ω) * Real.sqrt (g ω)) μ ∧
      (∫ ω, Real.sqrt (f ω) * Real.sqrt (g ω) ∂μ) ≤
        Real.sqrt (∫ ω, f ω ∂μ) * Real.sqrt (∫ ω, g ω ∂μ) := by
  let F : Disorder → ℝ := fun ω => Real.sqrt (f ω)
  let G : Disorder → ℝ := fun ω => Real.sqrt (g ω)
  have hFmeas : Measurable F := Real.continuous_sqrt.measurable.comp hfmeas
  have hGmeas : Measurable G := Real.continuous_sqrt.measurable.comp hgmeas
  have hFsq : Integrable (fun ω => F ω ^ 2) μ := by
    have heq : (fun ω => F ω ^ 2) = f := by
      funext ω
      simp [F, Real.sq_sqrt (hf0 ω)]
    rw [heq]
    exact hfint
  have hGsq : Integrable (fun ω => G ω ^ 2) μ := by
    have heq : (fun ω => G ω ^ 2) = g := by
      funext ω
      simp [G, Real.sq_sqrt (hg0 ω)]
    rw [heq]
    exact hgint
  have hFmem : MemLp F 2 μ :=
    (memLp_two_iff_integrable_sq hFmeas.aestronglyMeasurable).2 hFsq
  have hGmem : MemLp G 2 μ :=
    (memLp_two_iff_integrable_sq hGmeas.aestronglyMeasurable).2 hGsq
  have hFmem' : MemLp F (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hFmem
  have hGmem' : MemLp G (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hGmem
  have hFnonneg : 0 ≤ᵐ[μ] F := Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _
  have hGnonneg : 0 ≤ᵐ[μ] G := Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg _
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    hFnonneg hGnonneg hFmem' hGmem'
  have hprodInt : Integrable (fun ω => F ω * G ω) μ := by
    have hpqENN : ENNReal.HolderTriple
        (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 :=
      Real.HolderConjugate.two_two.ennrealOfReal
    have hprodmem : MemLp (fun ω => G ω * F ω) 1 μ :=
      @MemLp.mul Disorder inferInstance ℝ inferInstance μ
        (ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal (2 : ℝ)) 1 F G hGmem' hFmem' hpqENN
    have hprodInt' : Integrable (fun ω => G ω * F ω) μ := hprodmem.integrable (by norm_num)
    simpa only [mul_comm] using hprodInt'
  have hHolder' :
      ∫ ω, F ω * G ω ∂μ ≤
        Real.sqrt (∫ ω, F ω ^ 2 ∂μ) * Real.sqrt (∫ ω, G ω ^ 2 ∂μ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    convert hHolder using 1
    norm_num
  have hFsqeq : (fun ω => F ω ^ 2) = f := by
    funext ω
    simp [F, Real.sq_sqrt (hf0 ω)]
  have hGsqeq : (fun ω => G ω ^ 2) = g := by
    funext ω
    simp [G, Real.sq_sqrt (hg0 ω)]
  refine ⟨?_, ?_⟩
  · simpa [F, G] using hprodInt
  · simpa only [hFsqeq, hGsqeq, F, G] using hHolder'

private theorem endpointProfile_invSqrt_integral_le_of_futureEnergy
    (β : ℝ) (hβ : 0 ≤ β) {M n N : ℕ} (hMn : M ≤ n) (hnN : n ≤ N)
    (G : Set Disorder) (hG : MeasurableSet[disorderPast M] G) (D : ℝ)
    (hD : ∫ ω in G, futureEnergy β M N
      (smoothedEndpointDist β 0 M 0 ω) ∂disorderLaw ≤ D) :
    IntegrableOn (fun ω =>
      profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω ^ (-(1 / 2 : ℝ)))
        G disorderLaw ∧
    (∫ ω in G,
      profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω ^ (-(1 / 2 : ℝ))
        ∂disorderLaw) ≤ Real.sqrt D := by
  classical
  let S : Finset Site := Polymer.endpoints 0 M
  let η : Disorder → Site → ℝ := fun ω w => smoothedEndpointDist β 0 M 0 ω w
  let P : Disorder → ℝ := fun ω =>
    profileP2Fun β M N (η ω) (fun _ => 1) ω
  let Q : Disorder → ℝ := fun ω =>
    profileP2Fun β M n (η ω) (fun _ => 1) ω
  let X : Disorder → ℝ := fun ω =>
    profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω
  have hST : S = (Polymer.endpoints 0 0).biUnion
      (fun y => Polymer.endpoints y (M - 0)) := by
    ext w
    simp [S, Polymer.endpoints, Polymer.walkPosition_zero]
  have h0M : 0 ≤ M := Nat.zero_le _
  have hηsupp : ∀ ω w, w ∉ S → η ω w = 0 := by
    intro ω w hw
    apply (Smoothing.smoothedEndpointDist_probability β h0M 0 ω).1 w
    rw [← hST]
    exact hw
  have hηnonneg : ∀ ω w, 0 ≤ η ω w := by
    intro ω w
    exact (Smoothing.smoothedEndpointDist_probability β h0M 0 ω).2.1 w
  have hηmass : ∀ ω, ∑ w ∈ S, η ω w = 1 := by
    intro ω
    rw [hST]
    simpa [η] using
      (Smoothing.smoothedEndpointDist_probability β h0M 0 ω).2.2
  have hηmeas (w : Site) : Measurable[disorderPast M] (η · w) := by
    change Measurable[disorderPast M]
      (fun ω => smoothedEndpointDist β 0 M 0 ω w)
    rw [← Gaussian.disorderBlock_zero M]
    exact Polymer.measurable_smoothedEndpointDist_block β 0 M h0M 0 w
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
      smoothedP2Plane β 0 N 0 ω / smoothedP2Plane β 0 M 0 ω := by
    dsimp [P, η]
    exact profileP2Fun_smoothedEndpointDist_eq_div β h0M (Nat.le_trans hMn hnN) 0 ω
  have hQdiv (ω : Disorder) : Q ω =
      smoothedP2Plane β 0 n 0 ω / smoothedP2Plane β 0 M 0 ω := by
    dsimp [Q, η]
    exact profileP2Fun_smoothedEndpointDist_eq_div β h0M hMn 0 ω
  have hXdiv (ω : Disorder) : X ω =
      smoothedP2Plane β 0 N 0 ω / smoothedP2Plane β 0 n 0 ω := by
    dsimp [X]
    rw [endpointDist_eq_smoothedEndpointDist_zero β n 0 ω]
    exact profileP2Fun_smoothedEndpointDist_eq_div β (Nat.zero_le n) hnN 0 ω
  have hXratio (ω : Disorder) : X ω = P ω / Q ω := by
    have hUm : 0 < smoothedP2Plane β 0 M 0 ω :=
      Polymer.smoothedP2Plane_pos β 0 M 0 ω
    have hUn : 0 < smoothedP2Plane β 0 n 0 ω :=
      Polymer.smoothedP2Plane_pos β 0 n 0 ω
    calc
      X ω = smoothedP2Plane β 0 N 0 ω / smoothedP2Plane β 0 n 0 ω := hXdiv ω
      _ = (smoothedP2Plane β 0 N 0 ω / smoothedP2Plane β 0 M 0 ω) /
          (smoothedP2Plane β 0 n 0 ω / smoothedP2Plane β 0 M 0 ω) := by
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
          futureEnergy β M N (smoothedEndpointDist β 0 M 0 ω) ∂disorderLaw :=
        integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω =>
          futureEnergy_nonneg β M N (smoothedEndpointDist β 0 M 0 ω))
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

private theorem measure_lt_exp_neg_le_of_goodSet
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

private theorem measure_abs_log_lt_le_of_tails
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

private theorem sqrt_exp_half (x : ℝ) :
    Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

/-- The profile estimates imply exponential tails for the absolute logarithms of both endpoint partition functions. -/
theorem log_profile_tail_le_of (hPE : ProfileEstimatesBound) (A : ℝ) :
    ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₁ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ u : ℝ, 0 ≤ u →
        (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (endpointDist (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) 0 ω) (fun _ => 1) ω)|}).toReal ≤
          C * Real.sqrt |Real.log δ| * Real.exp (-u / 3) ∧
        (disorderLaw {ω | u < |Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (Real.sqrt δ * N)) N
            (smoothedEndpointDist (criticalBeta ϑ N) (evenCeil (δ * N)) (evenCeil (Real.sqrt δ * N)) 0 ω)
              (fun _ => 1) ω)|}).toReal ≤
          C * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
  obtain ⟨ρ₀, hρ₀, hPEρ₀⟩ := hPE A
  obtain ⟨CPE, ℓ, hPEρ₁⟩ := hPEρ₀ (ρ₀ ^ 2)
  obtain ⟨δsmooth, Csmooth, hδsmooth, hsmoothed⟩ :=
    measure_profileP2Fun_smoothedEndpointDist_lt_le A
  obtain ⟨Ccrude, hcrude⟩ := measure_profileP2Fun_endpointDist_lt_le A
  let δcore : ℝ := min (min (Real.exp (-2)) (ρ₀ ^ (-(2 : ℝ))))
    (Real.exp (-(4 * ((ℓ + 1 : ℕ) : ℝ) * Real.log ρ₀)))
  let δ₁ : ℝ := min δcore δsmooth
  let C : ℝ := 2 + Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
    Real.sqrt 2 * |Ccrude| + |Csmooth|
  have hρ₀pos : 0 < ρ₀ := lt_trans zero_lt_one hρ₀
  have hδcore : 0 < δcore := by
    dsimp [δcore]
    positivity
  have hδ₁pos : 0 < δ₁ := by dsimp [δ₁]; exact lt_min hδcore hδsmooth
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  have hδ1event : ∀ δ : ℝ, 0 < δ → δ < δ₁ →
      δ < Real.exp (-2) ∧ δ < ρ₀ ^ (-(2 : ℝ)) ∧
        δ < Real.exp (-(4 * ((ℓ + 1 : ℕ) : ℝ) * Real.log ρ₀)) ∧ δ < δsmooth := by
    intro δ hδ hδsmall
    have hparts := (lt_min_iff.mp hδsmall)
    have hcore := (lt_min_iff.mp hparts.1)
    have hcore' := (lt_min_iff.mp hcore.1)
    exact ⟨hcore'.1, hcore'.2, hcore.2, hparts.2⟩
  refine ⟨δ₁, C, hδ₁pos, ?_⟩
  intro δ hδ hδsmall
  obtain ⟨hδexp2, hδrpow, hδexpℓ, hδsmooth'⟩ := hδ1event δ hδ hδsmall
  have hlogδlt2 : Real.log δ < -2 := by
    calc
      Real.log δ < Real.log (Real.exp (-2)) := Real.log_lt_log hδ hδexp2
      _ = -2 := Real.log_exp _
  have hδlt1 : δ < 1 := lt_trans hδexp2 (Real.exp_lt_one_iff.mpr (by norm_num))
  have habslog : 1 ≤ |Real.log δ| := by
    rw [abs_of_neg (lt_trans hlogδlt2 (by norm_num))]
    linarith
  have hlogρ : 0 < Real.log ρ₀ := Real.log_pos hρ₀
  have hlogδltℓ : Real.log δ <
      -(4 * ((ℓ + 1 : ℕ) : ℝ) * Real.log ρ₀) := by
    calc
      Real.log δ < Real.log
          (Real.exp (-(4 * ((ℓ + 1 : ℕ) : ℝ) * Real.log ρ₀)) ) :=
        Real.log_lt_log hδ hδexpℓ
      _ = -(4 * ((ℓ + 1 : ℕ) : ℝ) * Real.log ρ₀) := Real.log_exp _
  have hJrealLower : ((ℓ + 1 : ℕ) : ℝ) ≤
      |Real.log δ| / (4 * Real.log ρ₀) := by
    rw [abs_of_neg (lt_trans hlogδlt2 (by norm_num))]
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.log ρ₀)).2
    nlinarith
  have hrpowInv : ρ₀ ^ (-(2 : ℝ)) = ρ₀⁻¹ ^ (2 : ℕ) := by
    rw [Real.rpow_neg hρ₀pos.le]
    rw [inv_pow]
    exact congrArg Inv.inv (Real.rpow_natCast ρ₀ 2)
  have hδρ : δ ≤ ρ₀⁻¹ ^ (2 : ℕ) := by
    rw [← hrpowInv]
    exact hδrpow.le
  let ρ : ℝ := gridRatio δ ρ₀
  let J : ℕ := gridBlocks δ ρ₀
  have hγmem : ρ ∈ Set.Icc ρ₀ (ρ₀ ^ 2) := by
    exact Blocks.gridRatio_mem hρ₀ hδ hδρ
  have hJbounds := Blocks.gridBlocks_bounds hρ₀ hδ hδρ
  have hJpos : 1 ≤ J := by simpa [J] using hJbounds.1
  have hJell : ℓ ≤ J := by
    have hJreal : ((ℓ + 1 : ℕ) : ℝ) ≤ (J : ℝ) := by
      exact le_trans hJrealLower hJbounds.2.1
    have hle : ((ℓ + 1 : ℕ) : ℝ) ≤ (J : ℝ) :=
      hJreal
    exact_mod_cast (show (ℓ : ℝ) ≤ (J : ℝ) by exact le_trans (by norm_num) hle)
  have hγ : 1 < ρ := by exact lt_of_lt_of_le hρ₀ hγmem.1
  have htimeevent := Blocks.blockTime_gridRatio hρ₀ hδ hδρ
  have hPEevent := hPEρ₁ ρ hγmem
  have hsmoothevent := hsmoothed δ hδ hδsmooth'
  have hcrudeevent := hcrude
  have hN2 : ∀ᶠ N : ℕ in atTop, 2 ≤ N := eventually_ge_atTop 2
  have hmonEvent := Blocks.blockTime_monotone hγ
  filter_upwards [htimeevent, hPEevent, hsmoothevent, hcrudeevent, hN2, hmonEvent]
    with N htime hPE_N hsmoothed_N hcrude_N hN2 hmon
  intro ϑ hϑ u hu
  let K : ℕ := blockCount N ρ
  let t : ℕ → ℕ := blockTime N ρ
  let m : ℕ := evenCeil (δ * N)
  let n : ℕ := evenCeil (Real.sqrt δ * N)
  let β : ℝ := criticalBeta ϑ N
  have h2JK : 2 * J < K := by simpa [J, K, ρ] using htime.1
  have hmEq : t (K - 2 * J) = m := by simpa [J, K, ρ, t, m] using htime.2.1
  have hnEq : t (K - J) = n := by simpa [J, K, ρ, t, n] using htime.2.2
  have hKpos : 0 < K := by omega
  have htK : t K = N := by simp [t, K, blockTime, Nat.ne_of_gt hKpos]
  have hmon' : Monotone t := by simpa [t] using hmon
  have hnN : n ≤ N := by
    rw [← hnEq]
    exact (hmon' (Nat.sub_le K J)).trans_eq htK
  have hmn : m ≤ n := by
    rw [← hmEq, ← hnEq]
    exact hmon' (by omega)
  have hβ : 0 ≤ β := by dsimp [β, criticalBeta]; positivity
  let Xend : Disorder → ℝ := fun ω =>
    profileP2Fun β n N (endpointDist β n 0 ω) (fun _ => 1) ω
  let Xsmooth : Disorder → ℝ := fun ω =>
    profileP2Fun β n N (smoothedEndpointDist β m n 0 ω) (fun _ => 1) ω
  have hXendRatio (ω : Disorder) :
      Xend ω = smoothedP2Plane β 0 N 0 ω / smoothedP2Plane β 0 n 0 ω := by
    dsimp [Xend]
    rw [endpointDist_eq_smoothedEndpointDist_zero β n 0 ω]
    exact profileP2Fun_smoothedEndpointDist_eq_div β (Nat.zero_le n) hnN 0 ω
  have hXendPos (ω : Disorder) : 0 < Xend ω := by
    rw [hXendRatio ω]
    exact div_pos (Polymer.smoothedP2Plane_pos β 0 N 0 ω)
      (Polymer.smoothedP2Plane_pos β 0 n 0 ω)
  have hXendMeas : Measurable Xend := by
    have hU : Measurable (fun ω => smoothedP2Plane β 0 N 0 ω) :=
      Polymer.measurable_smoothedP2Plane β 0 N 0
    have hV : Measurable (fun ω => smoothedP2Plane β 0 n 0 ω) :=
      Polymer.measurable_smoothedP2Plane β 0 n 0
    have hratio : Measurable
        (fun ω => smoothedP2Plane β 0 N 0 ω / smoothedP2Plane β 0 n 0 ω) := hU.div hV
    have heq : Xend = fun ω =>
        smoothedP2Plane β 0 N 0 ω / smoothedP2Plane β 0 n 0 ω := by
      funext ω
      exact hXendRatio ω
    rw [heq]
    exact hratio
  have hKmoment := log_le_blockCount_mul_log hγ (by omega : 1 ≤ N)
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlogγnonneg : 0 ≤ Real.log ρ := Real.log_nonneg hγ.le
  have hlogγle : Real.log ρ ≤ 2 * Real.log ρ₀ := by
    calc
      Real.log ρ ≤ Real.log (ρ₀ ^ 2) :=
        Real.log_le_log (lt_trans zero_lt_one hγ) hγmem.2
      _ = 2 * Real.log ρ₀ := by rw [Real.log_pow]; norm_num
  have hJlog : (J : ℝ) * Real.log ρ ≤ |Real.log δ| := by
    calc
      (J : ℝ) * Real.log ρ ≤
          (|Real.log δ| / (2 * Real.log ρ₀)) * (2 * Real.log ρ₀) :=
        mul_le_mul hJbounds.2.2 hlogγle hlogγnonneg (by positivity)
      _ = |Real.log δ| := by field_simp [ne_of_gt hlogρ]
  let k : ℕ := Nat.ceil ((J : ℝ) * Real.exp (u / 3))
  have hJreal : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJpos
  have hexpOne : 1 ≤ Real.exp (u / 3) := Real.one_le_exp (by linarith)
  have hceilLower : (J : ℝ) * Real.exp (u / 3) ≤ (k : ℝ) := by
    exact Nat.le_ceil _
  have hexpK : Real.exp (u / 3) ≤ (k : ℝ) := by
    have hmul : Real.exp (u / 3) ≤ (J : ℝ) * Real.exp (u / 3) := by
      nlinarith [mul_le_mul_of_nonneg_right hJreal (Real.exp_nonneg (u / 3))]
    exact hmul.trans hceilLower
  have hJcastK : (J : ℝ) ≤ (k : ℝ) := by
    calc
      (J : ℝ) ≤ (J : ℝ) * Real.exp (u / 3) := by
        nlinarith [mul_le_mul_of_nonneg_left hexpOne (Nat.cast_nonneg J)]
      _ ≤ (k : ℝ) := hceilLower
  have hJk : J ≤ k := by exact_mod_cast hJcastK
  have hceilUpper : (k : ℝ) < (J : ℝ) * Real.exp (u / 3) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hJexpOne : 1 ≤ (J : ℝ) * Real.exp (u / 3) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (J : ℝ) * Real.exp (u / 3) :=
        mul_le_mul hJreal hexpOne (by norm_num) (by positivity)
  have hkUpper : (k : ℝ) ≤ 2 * (J : ℝ) * Real.exp (u / 3) := by
    calc
      (k : ℝ) ≤ (J : ℝ) * Real.exp (u / 3) + 1 := hceilUpper.le
      _ ≤ 2 * (J : ℝ) * Real.exp (u / 3) := by nlinarith [hJexpOne]
  have hrootLog : 1 ≤ Real.sqrt |Real.log δ| := by
    exact Real.one_le_sqrt.mpr habslog
  have hCgood : 0 ≤ Real.sqrt (|CPE| / Real.log ρ₀) := Real.sqrt_nonneg _
  have hEndLeft : (disorderLaw {ω | Xend ω < Real.exp (-u)}).toReal ≤
      (Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
        Real.sqrt 2 * |Ccrude|) * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
    by_cases hkK : k < K
    · let s : ℕ := K - k
      let G : Set Disorder := profileGoodSet β t 1 s
      have hspos : 1 ≤ s := by dsimp [s]; omega
      have hsupper : s ≤ K - J := by dsimp [s]; omega
      have hℓk : ℓ ≤ k := le_trans hJell hJk
      have hsK : s + ℓ ≤ K := by dsimp [s]; omega
      have hPEdata := hPE_N ϑ hϑ 1 s (by norm_num) hspos hsK
      have hGpast : MeasurableSet[disorderPast (t s)] G := by
        exact Critical2DKPZ.LogNormality.measurableSet_profileGoodSet_past β hmon'
          (r := 1) (s := s) (by norm_num) (by omega)
      have hGfull : MeasurableSet G := by
        have hpast : disorderPast (t s) ≤
            (inferInstance : MeasurableSpace Disorder) := by
          rw [← Gaussian.disorderBlock_zero (t s)]
          exact Gaussian.disorderBlock_le 0 (t s)
        exact hpast G hGpast
      have hMn : t s ≤ n := by
        rw [← hnEq]
        exact hmon hsupper
      have hKsub : blockCount N ρ - s = k := by
        dsimp [K, s]
        omega
      have hKsubReal : (blockCount N ρ : ℝ) - s = (k : ℝ) := by
        rw [← Nat.cast_sub (by omega : s ≤ blockCount N ρ)]
        exact_mod_cast hKsub
      have hPEenergy : ∫ ω in G,
          futureEnergy β (t s) N (smoothedEndpointDist β 0 (t s) 0 ω) ∂disorderLaw ≤
            |CPE| * (k : ℝ) := by
        have hPEenergy' := hPEdata.2.2.2.2
        have hraw : ∫ ω in G,
            futureEnergy β (t s) N (smoothedEndpointDist β 0 (t s) 0 ω)
              ∂disorderLaw ≤ CPE * ((blockCount N ρ : ℝ) - s) := by
          simpa [β, t, G, blockTime] using hPEenergy'
        calc
          _ ≤ CPE * ((blockCount N ρ : ℝ) - s) := hraw
          _ = CPE * (k : ℝ) := by rw [hKsubReal]
          _ ≤ |CPE| * (k : ℝ) :=
            mul_le_mul_of_nonneg_right (le_abs_self CPE) (Nat.cast_nonneg _)
      have hGbad : (disorderLaw Gᶜ).toReal ≤ |CPE| / (k : ℝ) := by
        have hraw : (disorderLaw Gᶜ).toReal ≤ CPE / ((blockCount N ρ : ℝ) - s) :=
          hPEdata.1
        calc
          _ ≤ CPE / (k : ℝ) := by simpa [hKsubReal] using hraw
          _ ≤ |CPE| / (k : ℝ) :=
            div_le_div_of_nonneg_right (le_abs_self CPE) (Nat.cast_nonneg _)
      have hrecip : 1 / (k : ℝ) ≤ Real.exp (-u / 3) := by
        calc
          _ ≤ 1 / Real.exp (u / 3) :=
            div_le_div_of_nonneg_left zero_le_one (Real.exp_pos _) hexpK
          _ = Real.exp (-u / 3) := by
            rw [one_div, ← Real.exp_neg]
            congr 1
            ring
      have hmoment := endpointProfile_invSqrt_integral_le_of_futureEnergy
        β hβ hMn hnN G hGpast (|CPE| * (k : ℝ)) hPEenergy
      have hconditional := measure_lt_exp_neg_le_of_goodSet Xend G u
        (Real.sqrt (|CPE| * (k : ℝ))) (|CPE| / (k : ℝ))
        hXendPos hXendMeas hmoment.1 hmoment.2 hGbad
      have hsqrtUpper : Real.sqrt (|CPE| * (k : ℝ)) ≤
          Real.sqrt (2 * |CPE| * (J : ℝ) * Real.exp (u / 3)) := by
        apply Real.sqrt_le_sqrt
        calc
          |CPE| * (k : ℝ) ≤ |CPE| * (2 * (J : ℝ) * Real.exp (u / 3)) :=
            mul_le_mul_of_nonneg_left hkUpper (abs_nonneg CPE)
          _ = 2 * |CPE| * (J : ℝ) * Real.exp (u / 3) := by ring
      have hfactor :
          Real.sqrt (2 * |CPE| * (J : ℝ) * Real.exp (u / 3)) =
            Real.sqrt (2 * |CPE| * (J : ℝ)) * Real.exp (u / 6) := by
        rw [show 2 * |CPE| * (J : ℝ) * Real.exp (u / 3) =
          (2 * |CPE| * (J : ℝ)) * Real.exp (u / 3) by ring]
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * |CPE| * (J : ℝ))]
        rw [sqrt_exp_half]
        exact congrArg
          (fun x : ℝ => Real.sqrt (2 * |CPE| * (J : ℝ)) * Real.exp x)
          (by ring)
      have hsmallCoeff :
          Real.sqrt (2 * |CPE| * (J : ℝ)) ≤
            Real.sqrt (|CPE| / Real.log ρ₀) * Real.sqrt |Real.log δ| := by
        have hscale : 2 * |CPE| * (J : ℝ) ≤
            (|CPE| / Real.log ρ₀) * |Real.log δ| := by
          calc
            _ = (2 * |CPE|) * (J : ℝ) := by ring
            _ ≤ (2 * |CPE|) * (|Real.log δ| / (2 * Real.log ρ₀)) :=
              mul_le_mul_of_nonneg_left hJbounds.2.2 (by positivity)
            _ = (|CPE| / Real.log ρ₀) * |Real.log δ| := by
              field_simp [ne_of_gt hlogρ]
        calc
          _ ≤ Real.sqrt ((|CPE| / Real.log ρ₀) * |Real.log δ|) :=
            Real.sqrt_le_sqrt hscale
          _ = Real.sqrt (|CPE| / Real.log ρ₀) * Real.sqrt |Real.log δ| :=
            Real.sqrt_mul (by positivity : 0 ≤ |CPE| / Real.log ρ₀) |Real.log δ|
      have hgoodExp : Real.sqrt (|CPE| * (k : ℝ)) * Real.exp (-u / 2) ≤
          Real.sqrt (|CPE| / Real.log ρ₀) * Real.sqrt |Real.log δ| *
            Real.exp (-u / 3) := by
        calc
          _ ≤ (Real.sqrt (2 * |CPE| * (J : ℝ)) * Real.exp (u / 6)) *
              Real.exp (-u / 2) :=
            mul_le_mul_of_nonneg_right (hsqrtUpper.trans_eq hfactor)
              (Real.exp_nonneg _)
          _ = Real.sqrt (2 * |CPE| * (J : ℝ)) * Real.exp (-u / 3) := by
            have hExp : Real.exp (u / 6) * Real.exp (-u / 2) =
                Real.exp (-u / 3) := by
              rw [← Real.exp_add]
              exact congrArg Real.exp (by ring)
            rw [mul_assoc, hExp]
          _ ≤ _ := by
            exact mul_le_mul_of_nonneg_right hsmallCoeff (Real.exp_nonneg _)
      have hbadExp' :
          |CPE| / (k : ℝ) ≤ |CPE| * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
        calc
          _ = |CPE| * (1 / (k : ℝ)) := by ring
          _ ≤ |CPE| * Real.exp (-u / 3) :=
            mul_le_mul_of_nonneg_left hrecip (abs_nonneg CPE)
          _ ≤ _ := by
            calc
              |CPE| * Real.exp (-u / 3) = (|CPE| * 1) * Real.exp (-u / 3) := by ring
              _ ≤ (|CPE| * Real.sqrt |Real.log δ|) * Real.exp (-u / 3) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hrootLog (abs_nonneg CPE))
                  (Real.exp_nonneg _)
              _ = _ := rfl
      have hconditional' :
          (disorderLaw {ω | Xend ω < Real.exp (-u)}).toReal ≤
            (Real.sqrt (|CPE| / Real.log ρ₀) + |CPE|) *
              Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
        calc
          _ ≤ Real.sqrt (|CPE| * (k : ℝ)) * Real.exp (-u / 2) +
              |CPE| / (k : ℝ) := hconditional
          _ ≤ Real.sqrt (|CPE| / Real.log ρ₀) * Real.sqrt |Real.log δ| *
                Real.exp (-u / 3) +
              |CPE| * Real.sqrt |Real.log δ| * Real.exp (-u / 3) :=
            add_le_add hgoodExp hbadExp'
          _ = _ := by ring
      have hcoeff : Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| ≤
          Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| + Real.sqrt 2 * |Ccrude| := by
        exact le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
      have htailCoeff :
          (Real.sqrt (|CPE| / Real.log ρ₀) + |CPE|) *
              Real.sqrt |Real.log δ| * Real.exp (-u / 3) ≤
            (Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| + Real.sqrt 2 * |Ccrude|) *
              Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
        calc
          _ = (Real.sqrt (|CPE| / Real.log ρ₀) + |CPE|) *
                (Real.sqrt |Real.log δ| * Real.exp (-u / 3)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff
            (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _))
          _ = _ := by ring
      exact hconditional'.trans htailCoeff
    · have hkK' : K ≤ k := Nat.le_of_not_gt hkK
      have hKexp : (K : ℝ) * Real.exp (-u / 3) ≤ 2 * (J : ℝ) := by
        have hKceil : (K : ℝ) ≤ (J : ℝ) * Real.exp (u / 3) + 1 :=
          le_trans (by exact_mod_cast hkK') hceilUpper.le
        have hexpSmall : Real.exp (-u / 3) ≤ 1 :=
          (Real.exp_le_one_iff).2 (by linarith)
        calc
          _ ≤ ((J : ℝ) * Real.exp (u / 3) + 1) * Real.exp (-u / 3) :=
            mul_le_mul_of_nonneg_right hKceil (Real.exp_nonneg _)
          _ = (J : ℝ) + Real.exp (-u / 3) := by
            have hexpMul : Real.exp (u / 3) * Real.exp (-u / 3) = 1 := by
              rw [← Real.exp_add, show u / 3 + -u / 3 = 0 by ring, Real.exp_zero]
            calc
              _ = (J : ℝ) * (Real.exp (u / 3) * Real.exp (-u / 3)) +
                  Real.exp (-u / 3) := by ring
              _ = _ := by rw [hexpMul, mul_one]
          _ ≤ (J : ℝ) + 1 := by linarith [hexpSmall]
          _ ≤ 2 * (J : ℝ) := by linarith [hJreal]
      have hlogNscale : Real.log (N : ℝ) * Real.exp (-u / 3) ≤
          2 * |Real.log δ| := by
        calc
          _ ≤ ((K : ℝ) * Real.log ρ) * Real.exp (-u / 3) :=
            mul_le_mul_of_nonneg_right hKmoment (Real.exp_nonneg _)
          _ = ((K : ℝ) * Real.exp (-u / 3)) * Real.log ρ := by ring
          _ ≤ (2 * (J : ℝ)) * Real.log ρ :=
            mul_le_mul_of_nonneg_right hKexp hlogγnonneg
          _ ≤ 2 * |Real.log δ| := by
            calc
              (2 * (J : ℝ)) * Real.log ρ =
                  2 * ((J : ℝ) * Real.log ρ) := by ring
              _ ≤ 2 * |Real.log δ| :=
                mul_le_mul_of_nonneg_left hJlog (by norm_num)
      have hcoarseFactor : Real.sqrt (Real.log (N : ℝ)) * Real.exp (-u / 6) ≤
          Real.sqrt 2 * Real.sqrt |Real.log δ| := by
        have hExpHalf : Real.sqrt (Real.exp (-u / 3)) = Real.exp (-u / 6) := by
          rw [sqrt_exp_half]
          exact congrArg Real.exp (by ring)
        calc
          _ = Real.sqrt (Real.log (N : ℝ)) * Real.sqrt (Real.exp (-u / 3)) := by
            rw [hExpHalf]
          _ = Real.sqrt (Real.log (N : ℝ) * Real.exp (-u / 3)) :=
            (Real.sqrt_mul hlogNnonneg (Real.exp (-u / 3))).symm
          _ ≤ Real.sqrt (2 * |Real.log δ|) := Real.sqrt_le_sqrt hlogNscale
          _ = Real.sqrt 2 * Real.sqrt |Real.log δ| :=
            Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ)) |Real.log δ|
      have hcoarseExp : Real.sqrt (Real.log (N : ℝ)) * Real.exp (-u / 2) ≤
          Real.sqrt 2 * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
        have hsplit : Real.exp (-u / 2) =
            Real.exp (-u / 6) * Real.exp (-u / 3) := by
          rw [← Real.exp_add]
          congr 1
          ring
        calc
          _ = (Real.sqrt (Real.log (N : ℝ)) * Real.exp (-u / 6)) *
              Real.exp (-u / 3) := by rw [hsplit]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoarseFactor (Real.exp_nonneg _)
      have hcrudeTail := hcrude_N ϑ hϑ n hnN u hu
      have hcrudeAbs :
          (disorderLaw {ω | Xend ω < Real.exp (-u)}).toReal ≤
            |Ccrude| * Real.sqrt (Real.log (N : ℝ)) * Real.exp (-u / 2) := by
        have hcoeff : Ccrude * Real.sqrt (Real.log (N : ℝ)) * Real.exp (-u / 2) ≤
            |Ccrude| * Real.sqrt (Real.log (N : ℝ)) * Real.exp (-u / 2) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Ccrude) (Real.sqrt_nonneg _))
            (Real.exp_nonneg _)
        exact hcrudeTail.trans hcoeff
      calc
        _ ≤ |Ccrude| * Real.sqrt (Real.log (N : ℝ)) * Real.exp (-u / 2) := hcrudeAbs
        _ ≤ Real.sqrt 2 * |Ccrude| * Real.sqrt |Real.log δ| *
            Real.exp (-u / 3) := by
              have := mul_le_mul_of_nonneg_left hcoarseExp (abs_nonneg Ccrude)
              simpa [mul_assoc, mul_left_comm, mul_comm] using this
        _ ≤ (Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
            Real.sqrt 2 * |Ccrude|) * Real.sqrt |Real.log δ| *
              Real.exp (-u / 3) := by
            have hcoeff : Real.sqrt 2 * |Ccrude| ≤
                Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| + Real.sqrt 2 * |Ccrude| :=
              le_add_of_nonneg_left (add_nonneg hCgood (abs_nonneg _))
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hcoeff (Real.sqrt_nonneg _))
              (Real.exp_nonneg _)
  let Aend : Finset Site := Polymer.endpoints 0 n
  let ηend : Disorder → Site → ℝ := endpointDist β n 0
  have hendProb (ω : Disorder) := Smoothing.endpointDist_probability β n 0 ω
  have hendSupp : ∀ ω w, w ∉ Aend → ηend ω w = 0 := by
    intro ω w hw
    exact (hendProb ω).1 w (by simpa [Aend] using hw)
  have hendNonneg : ∀ ω w, 0 ≤ ηend ω w := by
    intro ω w
    exact (hendProb ω).2.1 w
  have hendMass : ∀ ω, ∑ w ∈ Aend, ηend ω w = 1 := by
    intro ω
    simpa [Aend, ηend] using (hendProb ω).2.2
  have hendMeas (w : Site) : Measurable[disorderPast n] (ηend · w) := by
    exact Polymer.measurable_endpointDist_past β n 0 w
  have hEndRight : (disorderLaw {ω | u < Real.log (Xend ω)}).toReal ≤
      Real.exp (-u) := by
    simpa [Xend, ηend] using
      (measure_log_profileP2Fun_gt_le β hnN ηend Aend hendSupp hendNonneg
        hendMass hendMeas u)
  have hEndAbs := measure_abs_log_lt_le_of_tails Xend u (Real.exp (-u))
    ((Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
      Real.sqrt 2 * |Ccrude|) * Real.sqrt |Real.log δ| * Real.exp (-u / 3))
    hXendPos hEndRight hEndLeft
  have hEndAbs' : (disorderLaw {ω | u < |Real.log (Xend ω)|}).toReal ≤
      C * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
    have hExpPos : Real.exp (-u) ≤
        Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
      calc
        Real.exp (-u) = Real.exp (-u / 3) * Real.exp (-(2 * u) / 3) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-u / 3) := by
          have hle : Real.exp (-(2 * u) / 3) ≤ 1 :=
            (Real.exp_le_one_iff).2 (by linarith)
          simpa using mul_le_mul_of_nonneg_left hle (Real.exp_nonneg _)
        _ ≤ Real.sqrt |Real.log δ| * Real.exp (-u / 3) :=
          by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hrootLog (Real.exp_nonneg _)
    have hcoeff : Real.exp (-u) +
        ((Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
          Real.sqrt 2 * |Ccrude|) * Real.sqrt |Real.log δ| * Real.exp (-u / 3)) ≤
        C * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
      dsimp [C]
      calc
        _ ≤ Real.sqrt |Real.log δ| * Real.exp (-u / 3) +
            (Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
              Real.sqrt 2 * |Ccrude|) * Real.sqrt |Real.log δ| *
                Real.exp (-u / 3) := add_le_add hExpPos le_rfl
        _ = (1 + Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
            Real.sqrt 2 * |Ccrude|) * Real.sqrt |Real.log δ| *
              Real.exp (-u / 3) := by ring
        _ ≤ _ := by
          have hnonneg : 0 ≤ Real.sqrt |Real.log δ| * Real.exp (-u / 3) :=
            mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
          have hcoef : 1 + Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
              Real.sqrt 2 * |Ccrude| ≤ C := by
            dsimp [C]
            linarith [abs_nonneg Csmooth]
          calc
            _ = (1 + Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
                Real.sqrt 2 * |Ccrude|) *
                  (Real.sqrt |Real.log δ| * Real.exp (-u / 3)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hnonneg
            _ = _ := by ring
    exact hEndAbs.trans hcoeff
  let Asmooth : Finset Site := (Polymer.endpoints 0 m).biUnion
    (fun y => Polymer.endpoints y (n - m))
  let ηsmooth : Disorder → Site → ℝ := smoothedEndpointDist β m n 0
  have hsmoothProb (ω : Disorder) := Smoothing.smoothedEndpointDist_probability β hmn 0 ω
  have hsmoothSupp : ∀ ω w, w ∉ Asmooth → ηsmooth ω w = 0 := by
    intro ω w hw
    exact (hsmoothProb ω).1 w (by simpa [Asmooth, ηsmooth] using hw)
  have hsmoothNonneg : ∀ ω w, 0 ≤ ηsmooth ω w := by
    intro ω w
    exact (hsmoothProb ω).2.1 w
  have hsmoothMass : ∀ ω, ∑ w ∈ Asmooth, ηsmooth ω w = 1 := by
    intro ω
    simpa [Asmooth, ηsmooth] using (hsmoothProb ω).2.2
  have hblockPast : Gaussian.disorderBlock m n ≤ disorderPast n := by
    rw [← Gaussian.disorderBlock_zero n]
    exact Gaussian.disorderBlock_mono (Nat.zero_le m) le_rfl
  have hsmoothMeas (w : Site) :
      Measurable[disorderPast n] (ηsmooth · w) := by
    exact (Polymer.measurable_smoothedEndpointDist_block β m n hmn 0 w).mono
      hblockPast le_rfl
  have hXsmoothPos (ω : Disorder) : 0 < Xsmooth ω :=
    profileP2Fun_pos_of_normalized β n N (ηsmooth ω) Asmooth
      (hsmoothSupp ω) (hsmoothNonneg ω) (hsmoothMass ω) ω
  have hSmoothRight :
      (disorderLaw {ω | u < Real.log (Xsmooth ω)}).toReal ≤ Real.exp (-u) := by
    simpa [Xsmooth, ηsmooth] using
      (measure_log_profileP2Fun_gt_le β hnN ηsmooth Asmooth hsmoothSupp
        hsmoothNonneg hsmoothMass hsmoothMeas u)
  have hSmoothLeft : (disorderLaw {ω | Xsmooth ω < Real.exp (-u)}).toReal ≤
      |Csmooth| * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
    have hraw := hsmoothed_N ϑ hϑ u hu
    have hexp : Real.exp (-u / 2) ≤ Real.exp (-u / 3) :=
      Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ Csmooth * Real.sqrt |Real.log δ| * Real.exp (-u / 2) := by
        simpa [Xsmooth] using hraw
      _ ≤ |Csmooth| * Real.sqrt |Real.log δ| * Real.exp (-u / 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self Csmooth) (Real.sqrt_nonneg _))
          (Real.exp_nonneg _)
      _ ≤ |Csmooth| * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
        exact mul_le_mul_of_nonneg_left hexp (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
  have hSmoothAbs := measure_abs_log_lt_le_of_tails Xsmooth u (Real.exp (-u))
    (|Csmooth| * Real.sqrt |Real.log δ| * Real.exp (-u / 3))
    hXsmoothPos hSmoothRight hSmoothLeft
  have hSmoothAbs' :
      (disorderLaw {ω | u < |Real.log (Xsmooth ω)|}).toReal ≤
        C * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
    have hExpPos : Real.exp (-u) ≤
        Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by
      calc
        Real.exp (-u) = Real.exp (-u / 3) * Real.exp (-(2 * u) / 3) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (-u / 3) := by
          have hle : Real.exp (-(2 * u) / 3) ≤ 1 :=
            (Real.exp_le_one_iff).2 (by linarith)
          simpa using mul_le_mul_of_nonneg_left hle (Real.exp_nonneg _)
        _ ≤ Real.sqrt |Real.log δ| * Real.exp (-u / 3) :=
          by simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hrootLog (Real.exp_nonneg _)
    calc
      _ ≤ Real.exp (-u) +
          |Csmooth| * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := hSmoothAbs
      _ ≤ Real.sqrt |Real.log δ| * Real.exp (-u / 3) +
          |Csmooth| * Real.sqrt |Real.log δ| * Real.exp (-u / 3) :=
        add_le_add hExpPos le_rfl
      _ = (1 + |Csmooth|) * Real.sqrt |Real.log δ| * Real.exp (-u / 3) := by ring
      _ ≤ _ := by
        have hnonneg : 0 ≤ Real.sqrt |Real.log δ| * Real.exp (-u / 3) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _)
        have hcoef : 1 + |Csmooth| ≤ C := by
          dsimp [C]
          have hbase : 0 ≤ Real.sqrt (|CPE| / Real.log ρ₀) + |CPE| +
              Real.sqrt 2 * |Ccrude| :=
            add_nonneg (add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
              (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
          linarith only [hbase]
        calc
          _ = (1 + |Csmooth|) * (Real.sqrt |Real.log δ| * Real.exp (-u / 3)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hnonneg
          _ = _ := by ring
  exact ⟨hEndAbs', hSmoothAbs'⟩

end Critical2DKPZ.FutureProfiles

end
