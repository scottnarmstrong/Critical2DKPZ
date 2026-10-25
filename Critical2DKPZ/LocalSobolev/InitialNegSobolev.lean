/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.FlatNegSobolev
public import Critical2DKPZ.Analysis.Sobolev.FunctionBound
import Mathlib.Tactic

/-! # Initial profile contribution to negative Sobolev moments -/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.LocalSobolev

private theorem locallyIntegrable_of_ae_bound {f : Plane → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hbound : ∀ᵐ x ∂volume, ‖f x‖ ≤ M) : LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  rw [IntegrableOn]
  have hKfinite : volume K < ⊤ := hK.measure_lt_top
  have hconstant : Integrable (fun _ : Plane => M) (volume.restrict K) := by
    exact (integrableOn_const_iff (μ := volume) (s := K) (C := M)).2
      (Or.inr hKfinite)
  refine hconstant.mono' hf.restrict ?_
  filter_upwards [ae_restrict_of_ae hbound] with x hx
  exact hx

/-- Uniform negative Sobolev moment bound for a bounded initial profile. -/
theorem kpzRegularized_negSobolev_moment_le_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    {t : ℝ} (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) {a : ℝ} (ha : 0 < a) (χ : TestFn) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ < t / 2 →
      ∫⁻ ω, localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => kpzRegularized P Z t δ h₀ x ω) volume ⊤) χ ∂P ≤
        ENNReal.ofReal C := by
  obtain ⟨Cflat, hflat⟩ := kpzRegularized_flat_negSobolev_moment_le_of
    hVD ϑ P Z hZ hHeatStartLogInput hsym ht ha χ
  let C₀ : ℝ := max 0 Cflat
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; exact le_max_left _ _
  let M : ℝ := ‖h₀‖
  have hχsq : Integrable (fun x : Plane => (χ x) ^ 2) volume := by
    have hprod : HasCompactSupport (fun x : Plane => χ x * χ x) := by
      exact χ.hasCompactSupport.mul_left
    have hcont : Continuous (fun x : Plane => χ x * χ x) := χ.continuous.mul χ.continuous
    simpa only [pow_two] using
      (hcont.integrable_of_hasCompactSupport (μ := volume) hprod)
  let qχ : ℝ := ∫ x : Plane, (χ x) ^ 2
  have hqχ : 0 ≤ qχ := by
    dsimp [qχ]
    exact integral_nonneg fun x => sq_nonneg (χ x)
  have hqχenn : ∫⁻ x : Plane, ENNReal.ofReal ((χ x) ^ 2) = ENNReal.ofReal qχ := by
    dsimp [qχ]
    exact (ofReal_integral_eq_lintegral_ofReal hχsq
      (Filter.Eventually.of_forall fun x => sq_nonneg (χ x))).symm
  let Bχ : ℝ := M ^ 2 * qχ
  have hBχ : 0 ≤ Bχ := by dsimp [Bχ]; positivity
  let K : ℝ≥0∞ := ENNReal.ofReal Bχ
  have hKtop : K < ⊤ := by dsimp [K]; exact ENNReal.ofReal_lt_top
  have hconstantBound : ENNReal.ofReal Cflat ≤ ENNReal.ofReal C₀ := by
    apply ENNReal.ofReal_le_ofReal
    dsimp [C₀]
    exact le_max_right _ _
  refine ⟨2 * (C₀ + Bχ), ?_⟩
  intro δ hδ hδhalf
  have hδt : δ < t := by linarith
  obtain ⟨Y, hYmeas, hYeq, hYloc⟩ :=
    kpzRegularized_flat_locallyIntegrable_version_of ϑ P Z hZ hsym hδ hδt
  have hXhmeas := kpzRegularized_joint_aestronglyMeasurable_of_initial
    ϑ P Z hZ hδ hδt h₀
  have hX0meas := kpzRegularized_joint_aestronglyMeasurable_of_initial
    ϑ P Z hZ hδ hδt (0 : Plane →ᵇ ℝ)
  let Xh : Ω × Plane → ℝ := fun q => kpzRegularized P Z t δ h₀ q.2 q.1
  let X0 : Ω × Plane → ℝ := fun q => kpzRegularized P Z t δ 0 q.2 q.1
  let D : Ω × Plane → ℝ := fun q => Xh q - X0 q
  have hXh : AEStronglyMeasurable Xh (P.prod volume) := by
    simpa only [Xh] using hXhmeas
  have hX0 : AEStronglyMeasurable X0 (P.prod volume) := by
    simpa only [X0] using hX0meas
  have hD : AEStronglyMeasurable D (P.prod volume) := by
    exact hXh.sub hX0
  let Dswap : Plane × Ω → ℝ := fun q => D (q.2, q.1)
  have hDswap : AEStronglyMeasurable Dswap (volume.prod P) := by
    simpa only [Dswap, Function.comp_def, Prod.swap] using
      hD.comp_measurePreserving
        (Measure.measurePreserving_swap (μ := volume) (ν := P))
  let E : Set ℝ := {r | |r| > M}
  let Bad : Set (Plane × Ω) := Dswap ⁻¹' E
  have hE : MeasurableSet E := by
    dsimp [E]
    exact (isOpen_lt continuous_const continuous_abs).measurableSet
  have hBadMeas : NullMeasurableSet Bad (volume.prod P) := by
    exact hDswap.aemeasurable.nullMeasurableSet_preimage hE
  have hBadSlice (x : Plane) : P ((fun ω => (x, ω)) ⁻¹' Bad) = 0 := by
    have hAvoid : ∀ᵐ ω ∂P, |Dswap (x, ω)| ≤ M := by
      filter_upwards [kpzRegularized_shift_bound_ae ϑ P Z hZ hsym hδ hδt h₀ x]
        with ω hω
      simpa [Dswap, D, Xh, X0] using hω
    have hAvoidZero : P {ω | ¬ |Dswap (x, ω)| ≤ M} = 0 := (ae_iff).1 hAvoid
    simpa [Bad, E, not_le] using hAvoidZero
  have hBadZero : (volume.prod P) Bad = 0 := by
    rw [Measure.prod_apply₀ hBadMeas]
    calc
      _ = ∫⁻ x : Plane, (0 : ℝ≥0∞) ∂volume := by
        apply lintegral_congr
        intro x
        exact hBadSlice x
      _ = 0 := by simp
  have hDswapBound : ∀ᵐ q : Plane × Ω ∂volume.prod P, |Dswap q| ≤ M := by
    rw [ae_iff]
    simpa [Bad, E, not_le] using hBadZero
  have hDbound : ∀ᵐ q : Ω × Plane ∂P.prod volume, |D q| ≤ M := by
    have h := (Measure.measurePreserving_swap (μ := P) (ν := volume)).quasiMeasurePreserving.ae
      hDswapBound
    simpa only [Dswap, Prod.swap] using h
  have hDsectionBound : ∀ᵐ ω ∂P, ∀ᵐ x ∂volume, |D (ω, x)| ≤ M :=
    Measure.ae_ae_of_ae_prod hDbound
  let Dm : Ω × Plane → ℝ := hD.aemeasurable.mk D
  have hDmeas : Measurable Dm := hD.aemeasurable.measurable_mk
  have hDeq : D =ᵐ[P.prod volume] Dm :=
    hD.aemeasurable.ae_eq_mk
  have hDsectionMeas : ∀ᵐ ω ∂P, AEStronglyMeasurable (fun x => D (ω, x)) volume := by
    filter_upwards [Measure.ae_ae_of_ae_prod hDeq] with ω hω
    have hm : Measurable (fun x : Plane => Dm (ω, x)) :=
      hDmeas.comp (measurable_const.prodMk measurable_id)
    have hω' : (fun x : Plane => Dm (ω, x)) =ᵐ[volume] (fun x => D (ω, x)) :=
      hω.mono fun x hx => hx.symm
    exact hm.aestronglyMeasurable.congr hω'
  have hDloc : ∀ᵐ ω ∂P, LocallyIntegrable (fun x => D (ω, x)) volume := by
    filter_upwards [hDsectionMeas, hDsectionBound] with ω hωmeas hωbound
    have hωbound' : ∀ᵐ x ∂volume, ‖D (ω, x)‖ ≤ M := by
      filter_upwards [hωbound] with x hx
      simpa [Real.norm_eq_abs] using hx
    exact locallyIntegrable_of_ae_bound hωmeas hωbound'
  have hFlatLoc : ∀ᵐ ω ∂P, LocallyIntegrable (fun x => X0 (ω, x)) volume := by
    filter_upwards [Measure.ae_ae_of_ae_prod hYeq] with ω hω
    have hEq : (fun x => Y (ω, x)) =ᵐ[volume] (fun x => X0 (ω, x)) := by
      filter_upwards [hω] with x hx
      simpa [X0] using hx
    exact (hYloc ω).congr hEq
  have hXhLoc : ∀ᵐ ω ∂P, LocallyIntegrable (fun x => Xh (ω, x)) volume := by
    filter_upwards [hFlatLoc, hDloc] with ω hω0 hωD
    have hsum : (fun x => X0 (ω, x)) + (fun x => D (ω, x)) =ᵐ[volume]
        (fun x => Xh (ω, x)) := by
      filter_upwards [] with x
      simp [D, Xh, X0]
    exact ((hω0.add hωD).congr hsum)
  have hDenergyPoint (ω : Ω) (hω : ∀ᵐ x ∂volume, |D (ω, x)| ≤ M)
      (hωloc : LocallyIntegrable (fun x => D (ω, x)) volume) :
      localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => D (ω, x)) volume ⊤) χ ≤ K := by
    apply (localNegSobolevSq_ofFun_le_lintegral ha.le hωloc χ).trans
    dsimp [K, Bχ, qχ]
    have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
    calc
      _ ≤ ∫⁻ x : Plane, ENNReal.ofReal (M ^ 2 * (χ x) ^ 2) := by
        apply lintegral_mono_ae
        filter_upwards [hω] with x hx
        apply ENNReal.ofReal_le_ofReal
        have hDsquare : (D (ω, x)) ^ 2 ≤ M ^ 2 := by
          have habs : |D (ω, x)| ≤ M := hx
          exact sq_le_sq' (abs_le.mp habs).1 (abs_le.mp habs).2
        calc
          (χ x * D (ω, x)) ^ 2 = (χ x) ^ 2 * (D (ω, x)) ^ 2 := by ring
          _ ≤ (χ x) ^ 2 * M ^ 2 := by gcongr
          _ = M ^ 2 * (χ x) ^ 2 := by ring
      _ = ENNReal.ofReal (M ^ 2) * ∫⁻ x : Plane, ENNReal.ofReal ((χ x) ^ 2) := by
        simp_rw [ENNReal.ofReal_mul hM2]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (∫ x : Plane, (χ x) ^ 2) := by
        rw [hqχenn]
      _ = ENNReal.ofReal (M ^ 2 * ∫ x : Plane, (χ x) ^ 2) := by
        rw [ENNReal.ofReal_mul hM2]
  have hDenergy : ∀ᵐ ω ∂P,
      localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => D (ω, x)) volume ⊤) χ ≤ K := by
    filter_upwards [hDsectionBound, hDloc] with ω hωbound hωloc
    exact hDenergyPoint ω hωbound hωloc
  have hpoint : ∀ᵐ ω ∂P,
      localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => Xh (ω, x)) volume ⊤) χ ≤
        2 * (K + localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ) := by
    filter_upwards [hFlatLoc, hDloc, hDenergy] with ω hω0 hωD hωE
    have hsplit : Distribution.ofFun ⊤ (fun x => Xh (ω, x)) volume ⊤ =
        Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤ +
          Distribution.ofFun ⊤ (fun x => D (ω, x)) volume ⊤ := by
      have hfun : (fun x => Xh (ω, x)) =
          (fun x => X0 (ω, x)) + (fun x => D (ω, x)) := by
        funext x
        simp [D, Xh, X0]
      rw [hfun, Distribution.ofFun_add (hω0.locallyIntegrableOn ⊤)
        (hωD.locallyIntegrableOn ⊤)]
    rw [hsplit]
    let E0 := localNegSobolevENorm a
      (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ
    let ED := localNegSobolevENorm a
      (Distribution.ofFun ⊤ (fun x => D (ω, x)) volume ⊤) χ
    have htri : localNegSobolevENorm a
        (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤ +
          Distribution.ofFun ⊤ (fun x => D (ω, x)) volume ⊤) χ ≤ E0 + ED := by
      exact localNegSobolevENorm_add_le a _ _ χ
    have hpow : (E0 + ED) ^ (2 : ℝ) ≤
        2 * (E0 ^ (2 : ℝ) + ED ^ (2 : ℝ)) := by
      have h := ENNReal.rpow_add_le_mul_rpow_add_rpow E0 ED
        (p := (2 : ℝ)) (by norm_num)
      rw [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h
      simpa only [ENNReal.rpow_two] using h
    have hE0sq : E0 ^ (2 : ℝ) =
        localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ := by
      dsimp [E0]
      rw [ENNReal.rpow_two, localNegSobolevENorm_sq]
    have hEDsq : ED ^ (2 : ℝ) =
        localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => D (ω, x)) volume ⊤) χ := by
      dsimp [ED]
      rw [ENNReal.rpow_two, localNegSobolevENorm_sq]
    calc
      _ = localNegSobolevENorm a
          (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤ +
            Distribution.ofFun ⊤ (fun x => D (ω, x)) volume ⊤) χ ^ 2 :=
        (localNegSobolevENorm_sq a _ χ).symm
      _ ≤ (E0 + ED) ^ (2 : ℝ) := by
        simpa only [ENNReal.rpow_two] using
          (ENNReal.rpow_le_rpow htri (by norm_num : (0 : ℝ) ≤ 2))
      _ ≤ 2 * (E0 ^ (2 : ℝ) + ED ^ (2 : ℝ)) := hpow
      _ ≤ 2 * (localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ + K) := by
        rw [hE0sq, hEDsq]
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hωE) bot_le
      _ = 2 * (K + localNegSobolevSq a
          (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ) := by
        congr 1
        exact add_comm _ _
  have hflatX0 : ∫⁻ ω, localNegSobolevSq a
      (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ ∂P ≤ ENNReal.ofReal C₀ := by
    simpa [X0] using (hflat δ hδ hδhalf).trans hconstantBound
  calc
    _ ≤ ∫⁻ ω, 2 * (K + localNegSobolevSq a
        (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ) ∂P :=
      lintegral_mono_ae hpoint
    _ = 2 * (K + ∫⁻ ω, localNegSobolevSq a
        (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ ∂P) := by
      rw [lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        lintegral_add_left (measurable_const : Measurable (fun _ : Ω => K))]
      simp
    _ ≤ 2 * (K + ENNReal.ofReal C₀) := by
      apply mul_le_mul_of_nonneg_left _ bot_le
      calc
        K + ∫⁻ ω, localNegSobolevSq a
            (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ ∂P =
          (∫⁻ ω, localNegSobolevSq a
              (Distribution.ofFun ⊤ (fun x => X0 (ω, x)) volume ⊤) χ ∂P) + K :=
            add_comm _ _
        _ ≤ ENNReal.ofReal C₀ + K := by
          simpa [add_comm] using add_le_add_right hflatX0 K
        _ = K + ENNReal.ofReal C₀ := add_comm _ _
    _ = ENNReal.ofReal (2 * (C₀ + Bχ)) := by
      calc
        _ = 2 * (ENNReal.ofReal Bχ + ENNReal.ofReal C₀) := by rfl
        _ = 2 * ENNReal.ofReal (Bχ + C₀) := by
          rw [← ENNReal.ofReal_add hBχ hC₀]
        _ = ENNReal.ofReal (2 * (Bχ + C₀)) := by
          have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
          rw [htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ = _ := by congr 1; ring

end Critical2DKPZ.LocalSobolev

end
