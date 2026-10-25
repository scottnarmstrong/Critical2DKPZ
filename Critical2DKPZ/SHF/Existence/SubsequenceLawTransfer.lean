/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.FiniteDimensionalLaws
import Critical2DKPZ.RandomMeasure.GeneralRandom

/-! # Transfer of subsequential limits -/

@[expose] public section

open MeasureTheory Filter
open scoped CompactlySupported Topology
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Existence

private def signedCompactTestIntegral {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (f : C_c(X, ℝ)) (μ : Measure X) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal -
    (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal

private theorem measurable_signedCompactTestIntegral {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (f : C_c(X, ℝ)) :
    Measurable (signedCompactTestIntegral f : Measure X → ℝ) := by
  have hp : Measurable (fun μ : Measure X => ∫⁻ x, ENNReal.ofReal (f x) ∂μ) :=
    Measure.measurable_lintegral f.continuous.measurable.ennreal_ofReal
  have hn : Measurable (fun μ : Measure X => ∫⁻ x, ENNReal.ofReal (-f x) ∂μ) :=
    Measure.measurable_lintegral f.continuous.measurable.neg.ennreal_ofReal
  exact hp.ennreal_toReal.sub hn.ennreal_toReal

private theorem signedCompactTestIntegral_eq_integral {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [LocallyCompactSpace X] [T2Space X]
    (μ : Measure X) (hμ : IsLocallyFiniteMeasure μ) (f : C_c(X, ℝ)) :
    signedCompactTestIntegral f μ = ∫ x, f x ∂μ := by
  have hfc : IsFiniteMeasureOnCompacts μ :=
    @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure X _ _ _ hμ
  have hf : Integrable f μ :=
    @Continuous.integrable_of_hasCompactSupport X ℝ _ _ _ μ _ f hfc f.continuous f.hasCompactSupport
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf).symm

private def pairAndFirstMarginalTestIntegrals {k : ℕ} (φ : Fin k → C_c(Plane × Plane, ℝ))
    (χ : Fin k → C_c(Plane, ℝ)) :
    (Fin k → Measure (Plane × Plane)) → Fin k → ℝ × ℝ := fun m i =>
      (signedCompactTestIntegral (φ i) (m i),
       signedCompactTestIntegral (χ i) (Measure.map Prod.fst (m i)))

private theorem measurable_pairAndFirstMarginalTestIntegrals {k : ℕ}
    (φ : Fin k → C_c(Plane × Plane, ℝ)) (χ : Fin k → C_c(Plane, ℝ)) :
    Measurable (pairAndFirstMarginalTestIntegrals φ χ) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_signedCompactTestIntegral (φ i)).comp (measurable_pi_apply i) |>.prodMk
    ((measurable_signedCompactTestIntegral (χ i)).comp
      ((Measure.measurable_map Prod.fst measurable_fst).comp (measurable_pi_apply i)))

/-- Being a subsequential polymer limit depends only on its finite-dimensional
laws, provided the new process is measurable. -/
theorem isPolymerSubseqLimit_of_fdd_eq {ϑ : ℝ} {D : Set ℝ} {ψ : ℕ → ℕ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    (hm : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω)) :
    IsPolymerSubseqLimit ϑ D ψ P' Z' := by
  have hlocalTarget : ∀ s ∈ D, ∀ t ∈ D, s < t →
      ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' s t ω) ∧
        IsLocallyFiniteMeasure (Measure.map Prod.fst (Z' s t ω)) := by
    intro s hs t ht hst
    have hlocal := hZ.1 s hs t ht hst
    have hsourceMeas : Measurable (Z s t) := hlocal.1
    have htargetMeas : Measurable (Z' s t) := hm s hs t ht hst
    have hsourceFlatMeas : Measurable (fun ω => Measure.map Prod.fst (Z s t ω)) :=
      (Measure.measurable_map Prod.fst measurable_fst).comp hsourceMeas
    have htargetFlatMeas : Measurable (fun ω => Measure.map Prod.fst (Z' s t ω)) :=
      (Measure.measurable_map Prod.fst measurable_fst).comp htargetMeas
    have hsourceLaw : P.map (Z s t) = P'.map (Z' s t) := by
      let ev : (Fin 1 → Measure (Plane × Plane)) → Measure (Plane × Plane) := fun q => q 0
      have hev : Measurable ev := measurable_pi_apply (0 : Fin 1)
      have hsourceVec : Measurable (fun ω : Ω => fun _ : Fin 1 => Z s t ω) := by
        apply measurable_pi_iff.mpr
        intro i
        exact hsourceMeas
      have htargetVec : Measurable (fun ω : Ω' => fun _ : Fin 1 => Z' s t ω) := by
        apply measurable_pi_iff.mpr
        intro i
        exact htargetMeas
      have hsingle := hfdd 1 (fun _ => s) (fun _ => t) (fun _ => ⟨hs, ht, hst⟩)
      calc
        P.map (Z s t) = (P.map (fun ω i => Z s t ω)).map ev := by
          rw [Measure.map_map hev hsourceVec]
          rfl
        _ = (P'.map (fun ω i => Z' s t ω)).map ev := by rw [hsingle]
        _ = P'.map (Z' s t) := by
          rw [Measure.map_map hev htargetVec]
          rfl
    have hpairSet : MeasurableSet {μ : Measure (Plane × Plane) | IsLocallyFiniteMeasure μ} :=
      Critical2DKPZ.RandomMeasure.measurableSet_isLocallyFiniteMeasure
        (Critical2DKPZ.RandomMeasure.vagueCompactExhaustion (Plane × Plane))
        (fun μ => μ) measurable_id
    have hflatSet : MeasurableSet {μ : Measure Plane | IsLocallyFiniteMeasure μ} :=
      Critical2DKPZ.RandomMeasure.measurableSet_isLocallyFiniteMeasure
        (Critical2DKPZ.RandomMeasure.vagueCompactExhaustion Plane)
        (fun μ => μ) measurable_id
    have hpairLaw : ∀ᵐ μ ∂P.map (Z s t), IsLocallyFiniteMeasure μ :=
      (MeasureTheory.ae_map_iff hsourceMeas.aemeasurable hpairSet).2
        (hlocal.2.mono fun ω hw => hw.1)
    have hflatLaw : ∀ᵐ μ ∂P.map (fun ω => Measure.map Prod.fst (Z s t ω)),
        IsLocallyFiniteMeasure μ :=
      (MeasureTheory.ae_map_iff hsourceFlatMeas.aemeasurable hflatSet).2
        (hlocal.2.mono fun ω hw => hw.2)
    have hsourceFlatLaw : P.map (fun ω => Measure.map Prod.fst (Z s t ω)) =
        P'.map (fun ω => Measure.map Prod.fst (Z' s t ω)) := by
          calc
            P.map (fun ω => Measure.map Prod.fst (Z s t ω)) =
                (P.map (Z s t)).map (fun μ => Measure.map Prod.fst μ) := by
                  rw [Measure.map_map (Measure.measurable_map Prod.fst measurable_fst)
                    hsourceMeas]
                  rfl
            _ = (P'.map (Z' s t)).map (fun μ => Measure.map Prod.fst μ) := by rw [hsourceLaw]
            _ = P'.map (fun ω => Measure.map Prod.fst (Z' s t ω)) := by
                  rw [Measure.map_map (Measure.measurable_map Prod.fst measurable_fst)
                    htargetMeas]
                  rfl
    rw [hsourceLaw] at hpairLaw
    rw [hsourceFlatLaw] at hflatLaw
    have hpairTarget : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' s t ω) :=
      (MeasureTheory.ae_map_iff htargetMeas.aemeasurable hpairSet).1 hpairLaw
    have hflatTarget : ∀ᵐ ω ∂P',
        IsLocallyFiniteMeasure (Measure.map Prod.fst (Z' s t ω)) :=
      (MeasureTheory.ae_map_iff htargetFlatMeas.aemeasurable hflatSet).1 hflatLaw
    exact hpairTarget.and hflatTarget
  constructor
  · intro s hs t ht hst
    exact ⟨hm s hs t ht hst, hlocalTarget s hs t ht hst⟩
  · intro k s t hTimes φ χ
    let sourceReadout : ℕ → Disorder → Fin k → ℝ × ℝ := fun n ω i =>
      ((∫ p, φ i p ∂polymerMeasure ϑ (ψ n) (s i) (t i) ω),
       ∫ x, χ i x ∂((polymerMeasure ϑ (ψ n) (s i) (t i) ω).map Prod.fst))
    let sourceLimitReadout : Ω → Fin k → ℝ × ℝ := fun ω i =>
      ((∫ p, φ i p ∂Z (s i) (t i) ω),
       ∫ x, χ i x ∂((Z (s i) (t i) ω).map Prod.fst))
    let targetLimitReadout : Ω' → Fin k → ℝ × ℝ := fun ω i =>
      ((∫ p, φ i p ∂Z' (s i) (t i) ω),
       ∫ x, χ i x ∂((Z' (s i) (t i) ω).map Prod.fst))
    let sourceLimitAux : Ω → Fin k → ℝ × ℝ := fun ω =>
      pairAndFirstMarginalTestIntegrals φ χ (fun i => Z (s i) (t i) ω)
    let targetLimitAux : Ω' → Fin k → ℝ × ℝ := fun ω =>
      pairAndFirstMarginalTestIntegrals φ χ (fun i => Z' (s i) (t i) ω)
    have hlocalSource : ∀ᵐ ω ∂P, ∀ i : Fin k,
        IsLocallyFiniteMeasure (Z (s i) (t i) ω) ∧
          IsLocallyFiniteMeasure (Measure.map Prod.fst (Z (s i) (t i) ω)) :=
      ae_all_iff.mpr fun i => (hZ.1 (s i) (hTimes i).1 (t i) (hTimes i).2.1
        (hTimes i).2.2).2
    have hlocalTarget : ∀ᵐ ω ∂P', ∀ i : Fin k,
        IsLocallyFiniteMeasure (Z' (s i) (t i) ω) ∧
          IsLocallyFiniteMeasure (Measure.map Prod.fst (Z' (s i) (t i) ω)) :=
      ae_all_iff.mpr fun i => hlocalTarget (s i) (hTimes i).1 (t i) (hTimes i).2.1
        (hTimes i).2.2
    have hsourceAuxEq : sourceLimitAux =ᵐ[P] sourceLimitReadout := by
      filter_upwards [hlocalSource] with ω hω
      funext i
      exact Prod.ext
        (signedCompactTestIntegral_eq_integral (Z (s i) (t i) ω) (hω i).1 (φ i))
        (signedCompactTestIntegral_eq_integral (Measure.map Prod.fst (Z (s i) (t i) ω))
          (hω i).2 (χ i))
    have htargetAuxEq : targetLimitAux =ᵐ[P'] targetLimitReadout := by
      filter_upwards [hlocalTarget] with ω hω
      funext i
      exact Prod.ext
        (signedCompactTestIntegral_eq_integral (Z' (s i) (t i) ω) (hω i).1 (φ i))
        (signedCompactTestIntegral_eq_integral (Measure.map Prod.fst (Z' (s i) (t i) ω))
          (hω i).2 (χ i))
    have hZvec : Measurable (fun ω i => Z (s i) (t i) ω) := by
      apply measurable_pi_iff.mpr
      intro i
      exact (hZ.1 (s i) (hTimes i).1 (t i) (hTimes i).2.1 (hTimes i).2.2).1
    have hZ'vec : Measurable (fun ω i => Z' (s i) (t i) ω) := by
      apply measurable_pi_iff.mpr
      intro i
      exact hm (s i) (hTimes i).1 (t i) (hTimes i).2.1 (hTimes i).2.2
    have hauxLaw : P.map sourceLimitAux = P'.map targetLimitAux := by
      have hfinite := hfdd k s t hTimes
      have hreadmeas := measurable_pairAndFirstMarginalTestIntegrals φ χ
      calc
        P.map sourceLimitAux = (P.map (fun ω i => Z (s i) (t i) ω)).map
            (pairAndFirstMarginalTestIntegrals φ χ) := by
              rw [Measure.map_map hreadmeas hZvec]
              rfl
        _ = (P'.map (fun ω i => Z' (s i) (t i) ω)).map
            (pairAndFirstMarginalTestIntegrals φ χ) := by rw [hfinite]
        _ = P'.map targetLimitAux := by
              rw [Measure.map_map hreadmeas hZ'vec]
              rfl
    have hlimitLaw : P.map sourceLimitReadout = P'.map targetLimitReadout := by
      calc
        P.map sourceLimitReadout = P.map sourceLimitAux := Measure.map_congr hsourceAuxEq.symm
        _ = P'.map targetLimitAux := hauxLaw
        _ = P'.map targetLimitReadout := Measure.map_congr htargetAuxEq
    have htargetAuxMeas : Measurable targetLimitAux :=
      (measurable_pairAndFirstMarginalTestIntegrals φ χ).comp hZ'vec
    have htargetReadoutMeas : AEMeasurable targetLimitReadout P' :=
      htargetAuxMeas.aemeasurable.congr htargetAuxEq
    have hsourceDist := hZ.2 k s t hTimes φ χ
    refine ⟨hsourceDist.forall_aemeasurable, htargetReadoutMeas, ?_⟩
    have hprobEq :
        (⟨P.map sourceLimitReadout, inferInstance⟩ : ProbabilityMeasure (Fin k → ℝ × ℝ)) =
          ⟨P'.map targetLimitReadout, inferInstance⟩ := by
      apply Subtype.ext
      exact hlimitLaw
    rw [← hprobEq]
    exact hsourceDist.tendsto

end Critical2DKPZ.SHF.Existence

end
