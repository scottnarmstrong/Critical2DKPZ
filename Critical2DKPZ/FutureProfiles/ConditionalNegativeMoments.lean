/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.ConditionalMoments
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Mathlib.Tactic

/-! # Conditional negative moments of past-measurable profiles -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Collision
open Critical2DKPZ.Polymer
open Critical2DKPZ.OnePoint

/-- Negative powers of a partition function with a finite normalized past measurable nonnegative initial profile are integrable. -/
theorem integrableOn_rpow_neg_profileP2Fun_pastFrozen (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hnn : ∀ ω w, 0 ≤ η ω w) (hmass : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (hmeas : ∀ w, Measurable[disorderPast a] (η · w)) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-p)) disorderLaw := by
  classical
  have hA : A.Nonempty := by
    by_contra hA
    have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have h := hmass (fun _ => 0)
    simp [hAempty] at h
  let X : Disorder → ℝ := fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω
  have hXpos (ω : Disorder) : 0 < X ω := by
    dsimp [X]
    exact profileP2Fun_pos_of_normalized β a b (η ω) A (hsupp ω) (hnn ω) (hmass ω) ω
  let Z : Site → Disorder → ℝ := fun w ω => pointToPlane β a (b - a) w ω
  have hterm (w : Site) :
      Integrable (fun ω => Z w ω ^ (-p)) disorderLaw := by
    let ν : Site → ℝ := fun z => if z = w then 1 else 0
    have hνsupp : ∀ z ∉ ({w} : Finset Site), ν z = 0 := by
      intro z hz
      simp [ν, Finset.mem_singleton] at hz ⊢
      exact hz
    have hνnonneg : ∀ z, 0 ≤ ν z := by
      intro z
      by_cases hz : z = w <;> simp [ν, hz]
    have hνmass : ∑ z ∈ ({w} : Finset Site), ν z = 1 := by simp [ν]
    have hνint := integrable_rpow_profileP2Fun β a b ν {w} hνsupp hνnonneg hνmass (-p)
    have hνeq (ω : Disorder) :
        profileP2Fun β a b ν (fun _ => 1) ω = Z w ω := by
      rw [profileP2Fun_eq_sum β a b ν (fun _ => 1) {w} hνsupp]
      simp [ν, Z, tsum_pointToPoint]
    have hEq :
        (fun ω => profileP2Fun β a b ν (fun _ => 1) ω ^ (-p)) =
          fun ω => Z w ω ^ (-p) := by
      funext ω
      rw [hνeq]
    rw [← hEq]
    exact hνint
  let H : Disorder → ℝ := fun ω => ∑ w ∈ A, Z w ω ^ (-p)
  have hHint : Integrable H disorderLaw := by
    dsimp [H]
    exact integrable_finsetSum _ fun w hw => hterm w
  have hHnonneg (ω : Disorder) : 0 ≤ H ω := by
    dsimp [H]
    exact Finset.sum_nonneg fun w hw => Real.rpow_nonneg
      (Polymer.pointToPlane_pos β a (b - a) w ω).le _
  have hXmeas : Measurable X := by
    change Measurable (randomFlatProfilePolymer β a b η)
    exact measurable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hmeas
  have hpowMeas : Measurable (fun ω => X ω ^ (-p)) := by
    have heq : (fun ω => X ω ^ (-p)) =
        fun ω => Real.exp (-p * Real.log (X ω)) := by
      funext ω
      rw [Real.rpow_def_of_pos (hXpos ω)]
      congr 1
      ring
    rw [heq]
    exact Real.measurable_exp.comp (measurable_const.mul hXmeas.log)
  have hbound (ω : Disorder) : X ω ^ (-p) ≤ H ω := by
    let z : Site → ℝ := fun w => Z w ω
    let m : ℝ := (A.image z).min' (Finset.image_nonempty.mpr hA)
    have hminMember : ∃ w ∈ A, z w = m := by
      rcases Finset.mem_image.mp
          (Finset.min'_mem (A.image z) (Finset.image_nonempty.mpr hA)) with
        ⟨w, hw, hzw⟩
      exact ⟨w, hw, hzw⟩
    obtain ⟨w₀, hw₀, hzw₀⟩ := hminMember
    have hmpos : 0 < m := by
      rw [← hzw₀]
      exact Polymer.pointToPlane_pos β a (b - a) w₀ ω
    have hminle (w : Site) (hw : w ∈ A) : m ≤ z w :=
      Finset.min'_le _ _ (Finset.mem_image_of_mem z hw)
    have hsumX : X ω = ∑ w ∈ A, η ω w * z w := by
      dsimp [X, z, Z]
      simpa only [Nat.add_sub_of_le hab] using
        Polymer.profileP2Fun_flat_eq_sum β a (b - a) (η ω) A (hsupp ω) ω
    have hmleX : m ≤ X ω := by
      rw [hsumX]
      calc
        m = (∑ w ∈ A, η ω w) * m := by rw [hmass ω]; ring
        _ = ∑ w ∈ A, η ω w * m := by rw [Finset.sum_mul]
        _ ≤ ∑ w ∈ A, η ω w * z w :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hminle w hw) (hnn ω w)
    have hrpow : X ω ^ (-p) ≤ m ^ (-p) :=
      Real.rpow_le_rpow_of_nonpos hmpos hmleX (by linarith)
    have hminSum : m ^ (-p) ≤ ∑ w ∈ A, z w ^ (-p) := by
      rw [← hzw₀]
      exact Finset.single_le_sum (fun v hv => Real.rpow_nonneg
        (Polymer.pointToPlane_pos β a (b - a) v ω).le _) hw₀
    exact hrpow.trans hminSum
  have hboundNorm (ω : Disorder) : ‖X ω ^ (-p)‖ ≤ H ω := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hXpos ω).le _)]
    exact hbound ω
  exact hHint.mono' hpowMeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hboundNorm)

/-- For a past-measurable probability profile, the conditional negative moment of order `p ≥ 0` is bounded by the conditional future-energy moment of order `p * (p + 1) / 2`.

The profile's negative-power integrability on `disorderLaw` is given by
`integrableOn_rpow_neg_profileP2Fun_pastFrozen`. -/
theorem setIntegral_rpow_neg_profileP2Fun_le (β : ℝ) (hβ : 0 ≤ β) {a b : ℕ}
    (hab : a ≤ b) (η : Disorder → Site → ℝ) (A : Finset Site)
    (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hnn : ∀ ω w, 0 ≤ η ω w) (hmass : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (hmeas : ∀ w, Measurable[disorderPast a] (η · w)) (G : Set Disorder)
    (hG : MeasurableSet[disorderPast a] G) {p : ℝ} (hp : 0 ≤ p) :
    ∫ ω in G, profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-p) ∂disorderLaw ≤
      ∫ ω in G, futureEnergy β a b (η ω) ^ (p * (p + 1) / 2) ∂disorderLaw := by
  classical
  have hbdd : ∃ M : ℝ, ∀ ω w, |η ω w| ≤ M := by
    refine ⟨1, fun ω w => ?_⟩
    rw [abs_of_nonneg (hnn ω w)]
    by_cases hw : w ∈ A
    · exact Finset.single_le_sum (fun v hv => hnn ω v) hw |>.trans_eq (hmass ω)
    · rw [hsupp ω w hw]
      norm_num
  have hpast : disorderPast a ≤ (inferInstance : MeasurableSpace Disorder) := by
    rw [← Gaussian.disorderBlock_zero a]
    exact Gaussian.disorderBlock_le 0 a
  let X : Disorder → ℝ := fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-p)
  have hXint : Integrable X disorderLaw := by
    change Integrable (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-p)) disorderLaw
    exact integrableOn_rpow_neg_profileP2Fun_pastFrozen β hab η A hsupp hnn hmass hmeas hp
  have hXmeas : Measurable X := by
    dsimp [X]
    have hZmeas : Measurable (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω) := by
      change Measurable (randomFlatProfilePolymer β a b η)
      exact measurable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp hmeas
    have hZpos (ω : Disorder) :
        0 < profileP2Fun β a b (η ω) (fun _ => 1) ω :=
      profileP2Fun_pos_of_normalized β a b (η ω) A (hsupp ω) (hnn ω) (hmass ω) ω
    have heq : (fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω ^ (-p)) =
        fun ω => Real.exp (-p * Real.log (profileP2Fun β a b (η ω) (fun _ => 1) ω)) := by
      funext ω
      rw [Real.rpow_def_of_pos (hZpos ω)]
      congr 1
      ring
    rw [heq]
    exact Real.measurable_exp.comp (measurable_const.mul hZmeas.log)
  let Y : Disorder → ℝ := fun ω => futureEnergy β a b (η ω) ^ (p * (p + 1) / 2)
  have hq : 0 ≤ p * (p + 1) / 2 := by positivity
  have hYmeas : Measurable Y := by
    dsimp [Y]
    have hEmeas : Measurable (fun ω => futureEnergy β a b (η ω)) :=
      (measurable_futureEnergy β hab η A hsupp hmeas).mono hpast le_rfl
    exact (Real.continuous_rpow_const hq).measurable.comp
      hEmeas
  have hEbound : ∃ B : ℝ, ∀ ω, 0 ≤ futureEnergy β a b (η ω) ∧
      futureEnergy β a b (η ω) ≤ B := by
    let B : ℝ := 1 + ∑ w ∈ A, ∑ v ∈ A, |pairMoment β (b - a) w v|
    refine ⟨B, fun ω => ?_⟩
    constructor
    · exact futureEnergy_nonneg β a b (η ω)
    · have hηle (w : Site) : η ω w ≤ 1 := by
        by_cases hw : w ∈ A
        · exact Finset.single_le_sum (fun v hv => hnn ω v) hw |>.trans_eq (hmass ω)
        · rw [hsupp ω w hw]
          norm_num
      have hcoef (w v : Site) :
          |η ω w * η ω v * pairMoment β (b - a) w v| ≤
            |pairMoment β (b - a) w v| := by
        have hw : |η ω w| ≤ 1 := by rw [abs_of_nonneg (hnn ω w)]; exact hηle w
        have hv : |η ω v| ≤ 1 := by rw [abs_of_nonneg (hnn ω v)]; exact hηle v
        rw [abs_mul, abs_mul]
        calc
          |η ω w| * |η ω v| * |pairMoment β (b - a) w v| ≤
              1 * 1 * |pairMoment β (b - a) w v| := by gcongr
          _ = |pairMoment β (b - a) w v| := by ring
      have hsumEq := futureEnergy_eq_pairMoment_sum β hab (η ω) A (hsupp ω)
      have habs : |futureEnergy β a b (η ω)| ≤
          ∑ w ∈ A, ∑ v ∈ A, |pairMoment β (b - a) w v| := by
        rw [hsumEq]
        calc
          |∑ w ∈ A, ∑ v ∈ A,
              η ω w * η ω v * pairMoment β (b - a) w v| ≤
            ∑ w ∈ A, |∑ v ∈ A,
              η ω w * η ω v * pairMoment β (b - a) w v| :=
                Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ w ∈ A, ∑ v ∈ A,
              |η ω w * η ω v * pairMoment β (b - a) w v| :=
                Finset.sum_le_sum fun w hw => Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ w ∈ A, ∑ v ∈ A, |pairMoment β (b - a) w v| := by
                apply Finset.sum_le_sum
                intro w hw
                apply Finset.sum_le_sum
                intro v hv
                exact hcoef w v
      have hE := futureEnergy_nonneg β a b (η ω)
      dsimp [B]
      rw [abs_of_nonneg hE] at habs
      linarith
  obtain ⟨B, hB⟩ := hEbound
  have hYbound : ∀ ω, ‖Y ω‖ ≤ (1 + B) ^ (p * (p + 1) / 2) := by
    intro ω
    have hE := hB ω
    have hEB : futureEnergy β a b (η ω) ≤ 1 + B :=
      hE.2.trans (by linarith : B ≤ 1 + B)
    have hPow := Real.rpow_le_rpow hE.1 hEB hq
    dsimp [Y]
    rw [abs_of_nonneg (Real.rpow_nonneg hE.1 _)]
    exact hPow
  have hYint : Integrable Y disorderLaw := by
    refine (integrable_const ((1 + B) ^ (p * (p + 1) / 2))).mono'
      hYmeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    exact hYbound ω
  have hCE := Gaussian.condExp_disorderBlock_ae_eq 0 a hXmeas hXint
  rw [Gaussian.disorderBlock_zero] at hCE
  have hfiber (ω : Disorder) :
      ∫ ξ, X (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) ∂disorderLaw ≤ Y ω := by
    have hresample (ξ : Disorder) :
        profileP2Fun β a b
            (η (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ)) (fun _ => 1)
            (Gaussian.resample (Gaussian.timeBlock 0 a) ω ξ) =
          profileP2Fun β a b (η ω) (fun _ => 1) ξ := by
      rw [profileP2Fun_resamplePast β a b A η hsupp hmeas ω ξ]
      symm
      simpa only [Nat.add_sub_of_le hab] using
        Polymer.profileP2Fun_flat_eq_sum β a (b - a) (η ω) A (hsupp ω) ξ
    have hProfileInverseMomentInput := integral_rpow_neg_profileP2Fun_le hβ a b (η ω) A (hsupp ω)
      (hnn ω) (hmass ω) hp
    calc
      _ = ∫ ξ, profileP2Fun β a b (η ω) (fun _ => 1) ξ ^ (-p) ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        simpa [X] using congrArg (fun z : ℝ => z ^ (-p)) (hresample ξ)
      _ ≤ futureEnergy β a b (η ω) ^ (p * (p + 1) / 2) := by
        simpa only [futureEnergy] using hProfileInverseMomentInput
  have hCEbound :
      (fun ω => disorderLaw[X | disorderPast a] ω) ≤ᵐ[disorderLaw] Y := by
    filter_upwards [hCE] with ω hω
    rw [hω]
    exact hfiber ω
  calc
    ∫ ω in G, X ω ∂disorderLaw =
        ∫ ω in G, disorderLaw[X | disorderPast a] ω ∂disorderLaw := by
          exact (setIntegral_condExp hpast hXint hG).symm
    _ ≤ ∫ ω in G, Y ω ∂disorderLaw :=
      integral_mono_ae (integrable_condExp.integrableOn) hYint.integrableOn
        (ae_restrict_of_ae hCEbound)

end Critical2DKPZ.FutureProfiles

end
