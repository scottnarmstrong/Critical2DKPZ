/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.Smoothing.ProfileLogL2
public import Critical2DKPZ.Smoothing.ProfileL2Contraction
import Mathlib.Tactic

/-! # L² stability for bounded terminal profiles with random starts -/

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

/-- A bound on the expected future energy controls the inverse first moment of a
past-measurable random probability profile. Integrability is included explicitly. -/
theorem eLpNorm_inv_random_probability_profile_le_of_futureEnergy
    (β : ℝ) (hβ : 0 ≤ β) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hnonneg : ∀ ω w, 0 ≤ η ω w)
    (hmass : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (hmeas : ∀ w, Measurable[disorderPast a] (η · w))
    (_hEnergyInt : Integrable
      (fun ω => FutureProfiles.futureEnergy β a b (η ω)) disorderLaw)
    (Q : ℝ) (_hQ : 0 ≤ Q)
    (hEnergy : (∫ ω, FutureProfiles.futureEnergy β a b (η ω) ∂disorderLaw) ≤ Q) :
    Integrable (fun ω => (profileP2Fun β a b (η ω) (fun _ => 1) ω)⁻¹) disorderLaw ∧
    eLpNorm (fun ω => (profileP2Fun β a b (η ω) (fun _ => 1) ω)⁻¹)
      1 disorderLaw ≤ ENNReal.ofReal Q := by
  classical
  let X : Disorder → ℝ := fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω
  have hpast : disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero a]
    exact Gaussian.disorderBlock_le 0 a
  have hXpos (ω : Disorder) : 0 < X ω := by
    dsimp [X]
    exact Critical2DKPZ.OnePoint.profileP2Fun_pos_of_normalized β a b (η ω) A
      (hsupp ω) (hnonneg ω) (hmass ω) ω
  have hXmeas : Measurable X := by
    change Measurable (Critical2DKPZ.Collision.randomFlatProfilePolymer β a b η)
    exact FutureProfiles.measurable_randomTerminalProfilePolymer β a b A η
      (fun _ => 1) hsupp hmeas
  have hXpow : (fun ω => X ω ^ (-1 : ℝ)) = fun ω => (X ω)⁻¹ := by
    funext ω
    rw [Real.rpow_neg_one]
  have hXinvInt : Integrable (fun ω => (X ω)⁻¹) disorderLaw := by
    rw [← hXpow]
    exact FutureProfiles.integrableOn_rpow_neg_profileP2Fun_pastFrozen β hab η A
      hsupp hnonneg hmass hmeas (p := 1) (by norm_num)
  have hXinvIntegral : (∫ ω, (X ω)⁻¹ ∂disorderLaw) ≤ Q := by
    have hneg := FutureProfiles.setIntegral_rpow_neg_profileP2Fun_le β hβ hab η A
      hsupp hnonneg hmass hmeas Set.univ MeasurableSet.univ (p := 1) (by norm_num)
    have hexp : (1 : ℝ) * (1 + 1) / 2 = 1 := by norm_num
    have hnegPow : (∫ ω, X ω ^ (-1 : ℝ) ∂disorderLaw) ≤
        ∫ ω, FutureProfiles.futureEnergy β a b (η ω) ∂disorderLaw := by
      simpa only [X, MeasureTheory.setIntegral_univ, hexp, Real.rpow_one] using hneg
    have hneg' : (∫ ω, (X ω)⁻¹ ∂disorderLaw) ≤
        ∫ ω, FutureProfiles.futureEnergy β a b (η ω) ∂disorderLaw := by
      simpa only [← hXpow] using hnegPow
    exact hneg'.trans hEnergy
  have hnorm : eLpNorm (fun ω => (X ω)⁻¹) 1 disorderLaw =
      ENNReal.ofReal (∫ ω, (X ω)⁻¹ ∂disorderLaw) := by
    calc
      _ = ∫⁻ ω, ‖(X ω)⁻¹‖ₑ ∂disorderLaw :=
        eLpNorm_one_eq_lintegral_enorm (hXmeas.inv.aestronglyMeasurable)
      _ = ENNReal.ofReal (∫ ω, ‖(X ω)⁻¹‖ ∂disorderLaw) :=
        (ofReal_integral_norm_eq_lintegral_enorm hXinvInt).symm
      _ = ENNReal.ofReal (∫ ω, (X ω)⁻¹ ∂disorderLaw) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hXpos ω).le)]
  refine ⟨?_, ?_⟩
  · simpa only [X] using hXinvInt
  · simpa only [X] using hnorm.trans_le (ENNReal.ofReal_le_ofReal hXinvIntegral)

/-- A bounded positive terminal weight transfers the inverse first-moment bound from a random
past-measurable probability profile's flat polymer to the weighted polymer. Integrability is included. -/
theorem eLpNorm_inv_random_probability_profile_terminal_le_of_futureEnergy
    (β : ℝ) (hβ : 0 ≤ β) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hnonneg : ∀ ω w, 0 ≤ η ω w)
    (hmass : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (hmeas : ∀ w, Measurable[disorderPast a] (η · w))
    (hEnergyInt : Integrable
      (fun ω => FutureProfiles.futureEnergy β a b (η ω)) disorderLaw)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hEnergy : (∫ ω, FutureProfiles.futureEnergy β a b (η ω) ∂disorderLaw) ≤ Q)
    (f : Site → ℝ) (H : ℝ)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ H) :
    Integrable (fun ω => (profileP2Fun β a b (η ω) f ω)⁻¹) disorderLaw ∧
    eLpNorm (fun ω => (profileP2Fun β a b (η ω) f ω)⁻¹) 1 disorderLaw ≤
      ENNReal.ofReal (Real.exp H * Q) := by
  classical
  let X : Disorder → ℝ := fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω
  let Y : Disorder → ℝ := fun ω => profileP2Fun β a b (η ω) f ω
  have hXpos (ω : Disorder) : 0 < X ω := by
    dsimp [X]
    exact Critical2DKPZ.OnePoint.profileP2Fun_pos_of_normalized β a b (η ω) A
      (hsupp ω) (hnonneg ω) (hmass ω) ω
  have hYpos (ω : Disorder) : 0 < Y ω := by
    dsimp [Y]
    exact profileP2Fun_pos_terminal β a b (η ω) f A (hsupp ω) (hnonneg ω)
      (by
        have hsum : 0 < ∑ w ∈ A, η ω w := by rw [hmass ω]; norm_num
        exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hnonneg ω w)).mp hsum)
      (fun z => (hf z).1) ω
  have hXmeas : Measurable X := by
    change Measurable (Critical2DKPZ.Collision.randomFlatProfilePolymer β a b η)
    exact FutureProfiles.measurable_randomTerminalProfilePolymer β a b A η
      (fun _ => 1) hsupp hmeas
  have hYmeas : Measurable Y := by
    change Measurable (Critical2DKPZ.Collision.randomTerminalProfilePolymer β a b η f)
    exact FutureProfiles.measurable_randomTerminalProfilePolymer β a b A η f hsupp hmeas
  have hlog (ω : Disorder) : |Real.log (Y ω) - Real.log (X ω)| ≤ H := by
    dsimp [X, Y]
    exact FutureProfiles.abs_log_profileP2Fun_sub_le β a b (η ω) A (hsupp ω)
      (hnonneg ω) (hmass ω) f H hf ω
  have hpoint (ω : Disorder) : (Y ω)⁻¹ ≤ Real.exp H * (X ω)⁻¹ := by
    have hratioLog : Real.log (X ω) - Real.log (Y ω) ≤ H := by
      have hb := abs_le.mp (hlog ω)
      linarith
    have hratio : X ω / Y ω ≤ Real.exp H := by
      have hexp := Real.exp_le_exp.mpr hratioLog
      rw [Real.exp_sub, Real.exp_log (hXpos ω), Real.exp_log (hYpos ω)] at hexp
      exact hexp
    calc
      (Y ω)⁻¹ = (X ω / Y ω) * (X ω)⁻¹ := by
        field_simp [ne_of_gt (hXpos ω), ne_of_gt (hYpos ω)]
      _ ≤ Real.exp H * (X ω)⁻¹ :=
        mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr (hXpos ω).le)
  have hXinvData := eLpNorm_inv_random_probability_profile_le_of_futureEnergy β hβ hab
    η A hsupp hnonneg hmass hmeas hEnergyInt Q hQ hEnergy
  have hYinv : Integrable (fun ω => (Y ω)⁻¹) disorderLaw := by
    have hmajor : Integrable (fun ω => Real.exp H * (X ω)⁻¹) disorderLaw :=
      hXinvData.1.const_mul (Real.exp H)
    refine hmajor.mono' hYmeas.inv.aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hYpos ω).le)]
    have hmajor0 : 0 ≤ Real.exp H * (X ω)⁻¹ :=
      mul_nonneg (Real.exp_nonneg _) (inv_nonneg.mpr (hXpos ω).le)
    simpa only [abs_of_nonneg hmajor0] using hpoint ω
  have hXinvNorm : eLpNorm (fun ω => (X ω)⁻¹) 1 disorderLaw =
      ENNReal.ofReal (∫ ω, (X ω)⁻¹ ∂disorderLaw) := by
    calc
      _ = ∫⁻ ω, ‖(X ω)⁻¹‖ₑ ∂disorderLaw :=
        eLpNorm_one_eq_lintegral_enorm hXmeas.inv.aestronglyMeasurable
      _ = ENNReal.ofReal (∫ ω, ‖(X ω)⁻¹‖ ∂disorderLaw) :=
        (ofReal_integral_norm_eq_lintegral_enorm hXinvData.1).symm
      _ = ENNReal.ofReal (∫ ω, (X ω)⁻¹ ∂disorderLaw) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hXpos ω).le)]
  have hXinvNormle : eLpNorm (fun ω => (X ω)⁻¹) 1 disorderLaw ≤ ENNReal.ofReal Q := by
    simpa only [X] using hXinvData.2
  have hXrealNorm : ENNReal.ofReal (∫ ω, (X ω)⁻¹ ∂disorderLaw) ≤ ENNReal.ofReal Q := by
    rw [← hXinvNorm]
    exact hXinvNormle
  have hXintegral : (∫ ω, (X ω)⁻¹ ∂disorderLaw) ≤ Q :=
    (ENNReal.ofReal_le_ofReal_iff hQ).mp hXrealNorm
  have hYintegral : (∫ ω, (Y ω)⁻¹ ∂disorderLaw) ≤ Real.exp H * Q := by
    calc
      _ ≤ ∫ ω, Real.exp H * (X ω)⁻¹ ∂disorderLaw :=
        integral_mono hYinv (hXinvData.1.const_mul (Real.exp H)) hpoint
      _ = Real.exp H * ∫ ω, (X ω)⁻¹ ∂disorderLaw := by rw [integral_const_mul]
      _ ≤ Real.exp H * Q :=
        mul_le_mul_of_nonneg_left hXintegral (Real.exp_nonneg _)
  have hnorm : eLpNorm (fun ω => (Y ω)⁻¹) 1 disorderLaw =
      ENNReal.ofReal (∫ ω, (Y ω)⁻¹ ∂disorderLaw) := by
    calc
      _ = ∫⁻ ω, ‖(Y ω)⁻¹‖ₑ ∂disorderLaw :=
        eLpNorm_one_eq_lintegral_enorm hYmeas.inv.aestronglyMeasurable
      _ = ENNReal.ofReal (∫ ω, ‖(Y ω)⁻¹‖ ∂disorderLaw) :=
        (ofReal_integral_norm_eq_lintegral_enorm hYinv).symm
      _ = ENNReal.ofReal (∫ ω, (Y ω)⁻¹ ∂disorderLaw) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hYpos ω).le)]
  exact ⟨hYinv, hnorm.trans_le (ENNReal.ofReal_le_ofReal hYintegral)⟩

/-- The positive profile formed from the coordinatewise absolute difference of two past-measurable
probability laws has second moment bounded by its squared mass plus the first-collision sum times
its coordinate-square mass. Integrability of the profile square is included;
`integrable_pow_pointToPlane` supplies the point-to-plane squares on the right. -/
theorem integral_random_abs_profile_sq_le_coordinate (β : ℝ) {a b : ℕ}
    (hab : a ≤ b) (η ν : Disorder → Site → ℝ) (A : Finset Site)
    (hηA : ∀ ω w, w ∉ A → η ω w = 0)
    (hνA : ∀ ω w, w ∉ A → ν ω w = 0)
    (hη0 : ∀ ω w, 0 ≤ η ω w) (hν0 : ∀ ω w, 0 ≤ ν ω w)
    (hη1 : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (hν1 : ∀ ω, ∑ w ∈ A, ν ω w = 1)
    (hηmeas : ∀ w, Measurable[disorderPast a] (η · w))
    (hνmeas : ∀ w, Measurable[disorderPast a] (ν · w)) :
    let μ : Disorder → Site → ℝ := fun ω w => |η ω w - ν ω w|
    Integrable (fun ω => profileP2Fun β a b (μ ω) (fun _ => 1) ω ^ 2) disorderLaw ∧
    (∫ ω, profileP2Fun β a b (μ ω) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤
      (∫ ω, (∑ w ∈ A, |η ω w - ν ω w|) ^ 2 ∂disorderLaw) +
        (∫ ω, ∑ w ∈ A, (η ω w - ν ω w) ^ 2 ∂disorderLaw) *
          ∑ r ∈ Finset.Icc 1 (b - a),
            Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (b - a - r) 0 ω ^ 2 ∂disorderLaw) := by
  classical
  let μ : Disorder → Site → ℝ := fun ω w => |η ω w - ν ω w|
  let T : Disorder → ℝ := fun ω => ∑ w ∈ A, μ ω w
  let S : Disorder → ℝ := fun ω => ∑ w ∈ A, (η ω w - ν ω w) ^ 2
  let W : Disorder → ℝ := fun ω => profileP2Fun β a b (μ ω) (fun _ => 1) ω
  have hμA (ω : Disorder) (w : Site) (hw : w ∉ A) : μ ω w = 0 := by
    simp [μ, hηA ω w hw, hνA ω w hw]
  have hμ0 (ω : Disorder) (w : Site) : 0 ≤ μ ω w := by
    exact abs_nonneg _
  have hηleOne (ω : Disorder) (w : Site) : η ω w ≤ 1 := by
    by_cases hw : w ∈ A
    · calc
        η ω w ≤ ∑ z ∈ A, η ω z := Finset.single_le_sum (fun z hz => hη0 ω z) hw
        _ = 1 := hη1 ω
    · rw [hηA ω w hw]
      norm_num
  have hνleOne (ω : Disorder) (w : Site) : ν ω w ≤ 1 := by
    by_cases hw : w ∈ A
    · calc
        ν ω w ≤ ∑ z ∈ A, ν ω z := Finset.single_le_sum (fun z hz => hν0 ω z) hw
        _ = 1 := hν1 ω
    · rw [hνA ω w hw]
      norm_num
  have hμleOne (ω : Disorder) (w : Site) : μ ω w ≤ 1 := by
    dsimp [μ]
    rw [abs_le]
    constructor <;> linarith [hη0 ω w, hν0 ω w, hηleOne ω w, hνleOne ω w]
  have hμbound : ∃ C : ℝ, ∀ ω w, |μ ω w| ≤ C := by
    refine ⟨1, ?_⟩
    intro ω w
    rw [abs_of_nonneg (hμ0 ω w)]
    exact hμleOne ω w
  have hμmeas (w : Site) : Measurable[disorderPast a] (μ · w) := by
    dsimp [μ]
    fun_prop
  have hpast : disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero a]
    exact Gaussian.disorderBlock_le 0 a
  have hμmeasFull (w : Site) : Measurable (μ · w) :=
    (hμmeas w).mono hpast le_rfl
  have hTmeas : Measurable T := by
    dsimp [T]
    exact Finset.measurable_sum _ fun w hw => hμmeasFull w
  have hηmeasFull (w : Site) : Measurable (η · w) :=
    (hηmeas w).mono hpast le_rfl
  have hνmeasFull (w : Site) : Measurable (ν · w) :=
    (hνmeas w).mono hpast le_rfl
  have hSmeas : Measurable S := by
    dsimp [S]
    exact Finset.measurable_sum _ fun w hw =>
      ((hηmeasFull w).sub (hνmeasFull w)).pow_const 2
  have hTnonneg (ω : Disorder) : 0 ≤ T ω := by
    dsimp [T]
    positivity
  have hTle (ω : Disorder) : T ω ≤ A.card := by
    dsimp [T]
    calc
      _ ≤ ∑ _w ∈ A, (1 : ℝ) := Finset.sum_le_sum fun w hw => hμleOne ω w
      _ = A.card := by simp
  have hSnonneg (ω : Disorder) : 0 ≤ S ω := by
    dsimp [S]
    positivity
  have hSle (ω : Disorder) : S ω ≤ A.card := by
    dsimp [S]
    calc
      _ ≤ ∑ _w ∈ A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro w hw
        have hdiff : |η ω w - ν ω w| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [hη0 ω w, hν0 ω w, hηleOne ω w, hνleOne ω w]
        calc
          (η ω w - ν ω w) ^ 2 = |η ω w - ν ω w| ^ 2 := by rw [sq_abs]
          _ ≤ 1 := by nlinarith [hdiff, abs_nonneg (η ω w - ν ω w)]
      _ = A.card := by simp
  have hT2int : Integrable (fun ω => T ω ^ 2) disorderLaw := by
    apply Integrable.of_bound (hTmeas.pow_const 2).aestronglyMeasurable ((A.card : ℝ) ^ 2)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (T ω))]
    exact (sq_le_sq₀ (hTnonneg ω) (by positivity)).2 (hTle ω)
  have hSint : Integrable S disorderLaw := by
    apply Integrable.of_bound hSmeas.aestronglyMeasurable (A.card : ℝ)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hSnonneg ω)]
    exact hSle ω
  have hEnergyData := FutureProfiles.integrableOn_profileP2Fun_sq_eq β hab μ A hμA
    hμbound hμmeas Set.univ
  have hWint : Integrable (fun ω => W ω ^ 2) disorderLaw := by
    simpa only [IntegrableOn, Measure.restrict_univ, W] using hEnergyData.1
  have henergyInt : Integrable
      (fun ω => FutureProfiles.futureEnergy β a b (μ ω)) disorderLaw := by
    simpa only [IntegrableOn, Measure.restrict_univ] using hEnergyData.2
  have henergyEq := FutureProfiles.setIntegral_profileP2Fun_sq_eq β hab μ A hμA
    hμbound hμmeas Set.univ MeasurableSet.univ
  have henergyEq' : (∫ ω, W ω ^ 2 ∂disorderLaw) =
      ∫ ω, FutureProfiles.futureEnergy β a b (μ ω) ∂disorderLaw := by
    simpa only [W, MeasureTheory.setIntegral_univ] using henergyEq
  let K : ℝ := ∑ r ∈ Finset.Icc 1 (b - a),
    Polymer.sigmaSq β *
      (∫ ω, pointToPlane β 0 (b - a - r) 0 ω ^ 2 ∂disorderLaw)
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    apply Finset.sum_nonneg
    intro r hr
    have hσ : 0 ≤ Polymer.sigmaSq β := by
      unfold Polymer.sigmaSq
      exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
    exact mul_nonneg hσ (integral_nonneg fun ω => sq_nonneg _)
  have hpointwise (ω : Disorder) :
      FutureProfiles.futureEnergy β a b (μ ω) ≤ T ω ^ 2 + K * S ω := by
    have hfc := Polymer.profile_firstCollision_finset β a (b - a) (μ ω) (μ ω)
      A A (hμA ω) (hμA ω)
    have hfc' : FutureProfiles.futureEnergy β a b (μ ω) - T ω ^ 2 =
        ∑ r ∈ Finset.Icc 1 (b - a), ∑ w ∈ A, ∑ v ∈ A,
          μ ω w * μ ω v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
            (∫ τ, pointToPlane β 0 (b - a - r) 0 τ ^ 2 ∂disorderLaw) := by
      have hmass : (∑ w ∈ A, μ ω w) = T ω := by rfl
      dsimp [FutureProfiles.futureEnergy]
      simpa only [pow_two, Nat.add_sub_of_le hab, hmass] using hfc
    have hcollision (r : ℕ) :
        (∑ w ∈ A, ∑ v ∈ A,
          μ ω w * μ ω v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
            (∫ τ, pointToPlane β 0 (b - a - r) 0 τ ^ 2 ∂disorderLaw)) ≤
          S ω * (Polymer.sigmaSq β *
            (∫ τ, pointToPlane β 0 (b - a - r) 0 τ ^ 2 ∂disorderLaw)) := by
      let c : ℝ := Polymer.sigmaSq β *
        (∫ τ, pointToPlane β 0 (b - a - r) 0 τ ^ 2 ∂disorderLaw)
      have hc : 0 ≤ c := by
        dsimp [c]
        exact mul_nonneg (by
          unfold Polymer.sigmaSq
          exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β)))
          (integral_nonneg fun τ => sq_nonneg _)
      have hquad := finite_kernel_quadratic_le_sq r (μ ω) A
      calc
        _ = (∑ w ∈ A, ∑ v ∈ A,
            μ ω w * μ ω v * srwKernel (2 * r) (v - w)) * c := by
              dsimp [c]
              have hterm (w v : Site) :
                  μ ω w * μ ω v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
                    (∫ τ, pointToPlane β 0 (b - a - r) 0 τ ^ 2 ∂disorderLaw) =
                  (μ ω w * μ ω v * srwKernel (2 * r) (v - w)) * c := by
                dsimp [c]
                ring
              calc
                _ = ∑ w ∈ A, ∑ v ∈ A,
                    (μ ω w * μ ω v * srwKernel (2 * r) (v - w)) * c := by
                      apply Finset.sum_congr rfl
                      intro w hw
                      apply Finset.sum_congr rfl
                      intro v hv
                      exact hterm w v
                _ = (∑ w ∈ A, ∑ v ∈ A,
                    μ ω w * μ ω v * srwKernel (2 * r) (v - w)) * c := by
                      symm
                      rw [Finset.sum_mul]
                      apply Finset.sum_congr rfl
                      intro w hw
                      rw [Finset.sum_mul]
        _ ≤ (∑ w ∈ A, μ ω w ^ 2) * c := mul_le_mul_of_nonneg_right hquad hc
        _ = S ω * (Polymer.sigmaSq β *
            (∫ τ, pointToPlane β 0 (b - a - r) 0 τ ^ 2 ∂disorderLaw)) := by
              dsimp [c]
              simp only [S, μ, sq_abs]
    have htotal :
        (∑ r ∈ Finset.Icc 1 (b - a), ∑ w ∈ A, ∑ v ∈ A,
          μ ω w * μ ω v * srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
            (∫ τ, pointToPlane β 0 (b - a - r) 0 τ ^ 2 ∂disorderLaw)) ≤ K * S ω := by
      calc
        _ ≤ ∑ r ∈ Finset.Icc 1 (b - a), S ω *
            (Polymer.sigmaSq β *
              (∫ τ, pointToPlane β 0 (b - a - r) 0 τ ^ 2 ∂disorderLaw)) :=
                Finset.sum_le_sum fun r hr => hcollision r
        _ = K * S ω := by
              dsimp [K]
              rw [← Finset.mul_sum]
              ring
    have h := hfc'
    linarith
  have hmajorInt : Integrable (fun ω => T ω ^ 2 + K * S ω) disorderLaw :=
    hT2int.add (hSint.const_mul K)
  have henergyBound := integral_mono henergyInt hmajorInt hpointwise
  refine ⟨hWint, ?_⟩
  rw [henergyEq']
  have hfinal :
      (∫ ω, FutureProfiles.futureEnergy β a b (μ ω) ∂disorderLaw) ≤
        (∫ ω, T ω ^ 2 ∂disorderLaw) +
          (∫ ω, S ω ∂disorderLaw) * K := by
    calc
    _ ≤ ∫ ω, (T ω ^ 2 + K * S ω) ∂disorderLaw := henergyBound
    _ = (∫ ω, T ω ^ 2 ∂disorderLaw) +
        (∫ ω, S ω ∂disorderLaw) * K := by
          rw [integral_add hT2int (hSint.const_mul K), integral_const_mul]
          ring
  simpa [T, S, K, μ] using hfinal

/-- A bounded terminal profile inherits coordinate-square control for two past-measurable
probability laws. The positive absolute-difference profile supplies a pointwise majorant. The point-to-plane squares are integrable by
`integrable_pow_pointToPlane`. -/
theorem integral_random_probability_profile_difference_sq_le_terminal_of_coord_sq
    (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η ν : Disorder → Site → ℝ) (A : Finset Site)
    (hηA : ∀ ω w, w ∉ A → η ω w = 0)
    (hνA : ∀ ω w, w ∉ A → ν ω w = 0)
    (hη0 : ∀ ω w, 0 ≤ η ω w) (hν0 : ∀ ω w, 0 ≤ ν ω w)
    (hη1 : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (hν1 : ∀ ω, ∑ w ∈ A, ν ω w = 1)
    (hηmeas : ∀ w, Measurable[disorderPast a] (η · w))
    (hνmeas : ∀ w, Measurable[disorderPast a] (ν · w))
    (f : Site → ℝ) (F : ℝ) (hF : 0 ≤ F) (hf : ∀ z, |f z| ≤ F) :
    Integrable (fun ω => (profileP2Fun β a b (η ω) f ω -
      profileP2Fun β a b (ν ω) f ω) ^ 2) disorderLaw ∧
    (∫ ω, (profileP2Fun β a b (η ω) f ω -
      profileP2Fun β a b (ν ω) f ω) ^ 2 ∂disorderLaw) ≤
      F ^ 2 * ((∫ ω, (∑ w ∈ A, |η ω w - ν ω w|) ^ 2 ∂disorderLaw) +
        (∫ ω, ∑ w ∈ A, (η ω w - ν ω w) ^ 2 ∂disorderLaw) *
          ∑ r ∈ Finset.Icc 1 (b - a),
            Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (b - a - r) 0 ω ^ 2 ∂disorderLaw)) := by
  classical
  let μ : Disorder → Site → ℝ := fun ω w => |η ω w - ν ω w|
  let W : Disorder → ℝ := fun ω => profileP2Fun β a b (μ ω) (fun _ => 1) ω
  let D : Disorder → ℝ := fun ω =>
    profileP2Fun β a b (η ω) f ω - profileP2Fun β a b (ν ω) f ω
  have hμA (ω : Disorder) (w : Site) (hw : w ∉ A) : μ ω w = 0 := by
    simp [μ, hηA ω w hw, hνA ω w hw]
  have hμ0 (ω : Disorder) (w : Site) : 0 ≤ μ ω w := abs_nonneg _
  have hμmeas (w : Site) : Measurable[disorderPast a] (μ · w) := by
    dsimp [μ]
    fun_prop
  have hμbound : ∃ C : ℝ, ∀ ω w, |μ ω w| ≤ C := by
    refine ⟨2, ?_⟩
    intro ω w
    dsimp [μ]
    rw [abs_abs]
    have hηle : η ω w ≤ 1 := by
      by_cases hw : w ∈ A
      · exact (Finset.single_le_sum (fun z hz => hη0 ω z) hw).trans_eq (hη1 ω)
      · rw [hηA ω w hw]
        norm_num
    have hνle : ν ω w ≤ 1 := by
      by_cases hw : w ∈ A
      · exact (Finset.single_le_sum (fun z hz => hν0 ω z) hw).trans_eq (hν1 ω)
      · rw [hνA ω w hw]
        norm_num
    calc
      |η ω w - ν ω w| ≤ |η ω w| + |ν ω w| := abs_sub _ _
      _ ≤ 2 := by
        rw [abs_of_nonneg (hη0 ω w), abs_of_nonneg (hν0 ω w)]
        linarith
  have hμmeasFull (w : Site) : Measurable (μ · w) := by
    have hpast : disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
      rw [← Gaussian.disorderBlock_zero a]
      exact Gaussian.disorderBlock_le 0 a
    exact (hμmeas w).mono hpast le_rfl
  have hWdata := integral_random_abs_profile_sq_le_coordinate β hab η ν A
    hηA hνA hη0 hν0 hη1 hν1 hηmeas hνmeas
  have hWint : Integrable (fun ω => W ω ^ 2) disorderLaw := by
    simpa only [W, μ] using hWdata.1
  have hηbound : ∃ B : ℝ, ∀ ω w, |η ω w| ≤ B := by
    refine ⟨1, ?_⟩
    intro ω w
    rw [abs_of_nonneg (hη0 ω w)]
    by_cases hw : w ∈ A
    · exact (Finset.single_le_sum (fun z hz => hη0 ω z) hw).trans_eq (hη1 ω)
    · rw [hηA ω w hw]
      norm_num
  have hνbound : ∃ B : ℝ, ∀ ω w, |ν ω w| ≤ B := by
    refine ⟨1, ?_⟩
    intro ω w
    rw [abs_of_nonneg (hν0 ω w)]
    by_cases hw : w ∈ A
    · exact (Finset.single_le_sum (fun z hz => hν0 ω z) hw).trans_eq (hν1 ω)
    · rw [hνA ω w hw]
      norm_num
  have hηmem : MemLp (fun ω => profileP2Fun β a b (η ω) f ω) 2 disorderLaw := by
    change MemLp (Critical2DKPZ.Collision.randomTerminalProfilePolymer β a b η f) 2 disorderLaw
    exact FutureProfiles.memLp_randomTerminalProfilePolymer β a b A η f hηA hηbound
      hηmeas F hf 2 (by norm_num)
  have hνmem : MemLp (fun ω => profileP2Fun β a b (ν ω) f ω) 2 disorderLaw := by
    change MemLp (Critical2DKPZ.Collision.randomTerminalProfilePolymer β a b ν f) 2 disorderLaw
    exact FutureProfiles.memLp_randomTerminalProfilePolymer β a b A ν f hνA hνbound
      hνmeas F hf 2 (by norm_num)
  have hDmem : MemLp D 2 disorderLaw := by
    dsimp [D]
    exact hηmem.sub hνmem
  have hDint : Integrable (fun ω => D ω ^ 2) disorderLaw := by
    have h := hDmem.integrable_norm_pow'
    simpa only [D, Pi.sub_apply, Real.norm_eq_abs, sq_abs] using h
  have hpointwise (ω : Disorder) : D ω ^ 2 ≤ F ^ 2 * W ω ^ 2 := by
    have hrepr : D ω =
        ∑ w ∈ A, (η ω w - ν ω w) *
          (∑' z, pointToPoint β a (b - a) w z ω * f z) := by
      dsimp [D]
      rw [show b = a + (b - a) by omega]
      rw [Polymer.profileP2Fun_eq_sum β a (a + (b - a)) (η ω) f A (hηA ω),
        Polymer.profileP2Fun_eq_sum β a (a + (b - a)) (ν ω) f A (hνA ω)]
      simp only [Nat.add_sub_of_le hab]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      ring
    have hmajor : |D ω| ≤ F * W ω := by
      rw [hrepr]
      calc
        _ ≤ ∑ w ∈ A,
            |(η ω w - ν ω w) *
              (∑' z, pointToPoint β a (b - a) w z ω * f z)| :=
                Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ w ∈ A, μ ω w * (F * pointToPlane β a (b - a) w ω) := by
              apply Finset.sum_le_sum
              intro w hw
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left
                (Polymer.terminalProfile_abs_le β a (b - a) w f F hf ω)
                (abs_nonneg _)
        _ = F * W ω := by
              have hWflat : W ω =
                  ∑ w ∈ A, μ ω w * pointToPlane β a (b - a) w ω := by
                dsimp [W]
                simpa only [Nat.add_sub_of_le hab] using
                  Polymer.profileP2Fun_flat_eq_sum β a (b - a) (μ ω) A (hμA ω) ω
              calc
                _ = ∑ w ∈ A, F * (μ ω w * pointToPlane β a (b - a) w ω) := by
                      apply Finset.sum_congr rfl
                      intro w hw
                      ring
                _ = F * ∑ w ∈ A, μ ω w * pointToPlane β a (b - a) w ω := by
                      rw [← Finset.mul_sum]
                _ = F * W ω := by rw [← hWflat]
    have hWnonneg (ω : Disorder) : 0 ≤ W ω := by
      have hWflat : W ω =
          ∑ w ∈ A, μ ω w * pointToPlane β a (b - a) w ω := by
        dsimp [W]
        simpa only [Nat.add_sub_of_le hab] using
          Polymer.profileP2Fun_flat_eq_sum β a (b - a) (μ ω) A (hμA ω) ω
      rw [hWflat]
      apply Finset.sum_nonneg
      intro w hw
      exact mul_nonneg (hμ0 ω w) (Polymer.pointToPlane_pos β a (b - a) w ω).le
    have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hF (hWnonneg ω))).2 hmajor
    simpa only [sq_abs, mul_pow] using hsq
  have hmajorInt : Integrable (fun ω => F ^ 2 * W ω ^ 2) disorderLaw :=
    hWint.const_mul (F ^ 2)
  have hbound := integral_mono hDint hmajorInt hpointwise
  refine ⟨hDint, ?_⟩
  calc
    _ ≤ F ^ 2 * (∫ ω, W ω ^ 2 ∂disorderLaw) := by
          simpa only [integral_const_mul] using hbound
    _ ≤ F ^ 2 * ((∫ ω, (∑ w ∈ A, |η ω w - ν ω w|) ^ 2 ∂disorderLaw) +
          (∫ ω, ∑ w ∈ A, (η ω w - ν ω w) ^ 2 ∂disorderLaw) *
            ∑ r ∈ Finset.Icc 1 (b - a),
              Polymer.sigmaSq β *
                (∫ ω, pointToPlane β 0 (b - a - r) 0 ω ^ 2 ∂disorderLaw)) := by
          exact mul_le_mul_of_nonneg_left hWdata.2 (sq_nonneg F)


end Critical2DKPZ.Smoothing

end
