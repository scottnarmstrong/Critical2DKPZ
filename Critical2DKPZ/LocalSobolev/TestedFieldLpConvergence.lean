/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.DistributionValuedLimits
import Critical2DKPZ.JointConvergence.ThmToyJointConvergence

/-! Reversal transfers scalar Lᵖ convergence to the forward regularized KPZ field. -/

@[expose] public section

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.LocalSobolev

/-- At each admissible width, the forward and reversed regularization errors have the same `Lᵖ` seminorm. The two-width reversal law identifies the limiting error distributions. -/
private theorem kpzRegularized_pairing_eLpNorm_eq_of_process
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (hHmeas : ∀ t, 0 < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ φ : TestFn,
      Measurable[shfSigma Z] fun ω => H t h₀ ω φ)
    (T : ℝ)
    (X : ℝ → (Plane →ᵇ ℝ) → TestFn → Ω → ℝ)
    (hXmeas : ∀ u (h₀ : Plane →ᵇ ℝ) (φ : TestFn), 0 ≤ u → u < T →
      Measurable[shfSigma Z] (X u h₀ φ))
    (hXLp : ∀ u (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞),
      0 ≤ u → u < T → 1 ≤ p → p ≠ ⊤ →
        Tendsto (fun δ => eLpNorm
          (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω) -
            X u h₀ φ ω) p P)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    {t δ : ℝ} (ht : 0 < t) (htT : t < T) (hδ : 0 < δ) (hδt : δ < t)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) (p : ℝ≥0∞) (hp : 1 ≤ p) (hpTop : p ≠ ⊤) :
    eLpNorm (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) -
      H t h₀ ω φ) p P =
    eLpNorm (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z (T - t) T δ h₀ x ω) -
      X (T - t) h₀ φ ω) p P := by
  let u : ℝ := T - t
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have huT : u < T := by dsimp [u]; linarith
  let fwd : ℝ → Ω → ℝ := fun η ω =>
    if hη : 0 < η ∧ η < t then
      ∫ x, φ x * kpzRegularized P Z t η h₀ x ω
    else 0
  let rev : ℝ → Ω → ℝ := fun η ω =>
    if hη : 0 < η ∧ η < t then
      ∫ x, φ x * kpzRegularizedReversed P Z u T η h₀ x ω
    else 0
  have hSigma : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [shfSigma]
    apply iSup_le
    intro s
    apply iSup_le
    intro u
    apply iSup_le
    intro hsu
    exact (hZ.1 s u hsu.1 hsu.2).comap_le
  have hηvalid : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < η ∧ η < t := by
    have hpos : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < η := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact hη
    have hlt : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0), η < t := by
      have hnhds : ∀ᶠ η : ℝ in 𝓝 (0 : ℝ), η < t := Iio_mem_nhds ht
      exact hnhds.filter_mono nhdsWithin_le_nhds
    exact hpos.and hlt
  have hfwdRep (η : ℝ) (hη : 0 < η) (hηt : η < t) :
      AEMeasurable (fun ω => ∫ x, φ x * kpzRegularized P Z t η h₀ x ω) P := by
    obtain ⟨g, hg, hgeq⟩ := exists_shfSigma_measurable_kpzRegularized_integral
      ϑ P Z hZ hη hηt h₀ φ
    exact (hg.mono hSigma le_rfl).aemeasurable.congr hgeq
  have hrevRep (η : ℝ) (hη : 0 < η) (hηt : η < t) :
      AEMeasurable (fun ω => ∫ x, φ x * kpzRegularizedReversed P Z u T η h₀ x ω) P := by
    obtain ⟨g, hg, hgeq⟩ :=
      Critical2DKPZ.JointConvergence.exists_shfSigma_measurable_kpzRegularizedReversed_integral
        ϑ P Z hZ u T η hu hη (by dsimp [u]; linarith) h₀ φ
    exact (hg.mono hSigma le_rfl).aemeasurable.congr hgeq
  have hfwdAEMeas (η : ℝ) : AEMeasurable (fwd η) P := by
    by_cases hη : 0 < η ∧ η < t
    · exact (hfwdRep η hη.1 hη.2).congr
        (Filter.Eventually.of_forall fun ω => by simp [fwd, hη])
    · have hzero : fwd η = fun _ : Ω => (0 : ℝ) := by
        funext ω
        simp [fwd, hη]
      rw [hzero]
      exact measurable_const.aemeasurable
  have hrevAEMeas (η : ℝ) : AEMeasurable (rev η) P := by
    by_cases hη : 0 < η ∧ η < t
    · exact (hrevRep η hη.1 hη.2).congr
        (Filter.Eventually.of_forall fun ω => by simp [rev, hη])
    · have hzero : rev η = fun _ : Ω => (0 : ℝ) := by
        funext ω
        simp [rev, hη]
      rw [hzero]
      exact measurable_const.aemeasurable
  have hHmeasFull (u : ℝ) (hu : 0 < u) (ψ : TestFn) :
      AEMeasurable (fun ω => H u h₀ ω ψ) P :=
    ((hHmeas u hu h₀ ψ).mono hSigma le_rfl).aemeasurable
  have hXmeasFull (v : ℝ) (hv : 0 ≤ v) (hvT : v < T) (ψ : TestFn) :
      AEMeasurable (fun ω => X v h₀ ψ ω) P :=
    ((hXmeas v h₀ ψ hv hvT).mono hSigma le_rfl).aemeasurable
  have hfwdTMeasure : TendstoInMeasure P fwd (nhdsWithin 0 (Set.Ioi 0))
      (fun ω => H t h₀ ω φ) := by
    have hEq : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0), (fwd η) =ᵐ[P]
        (fun ω => ∫ x, φ x * kpzRegularized P Z t η h₀ x ω) := by
      filter_upwards [hηvalid] with η hη
      simp [fwd, hη.1, hη.2]
    have hEq' : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (fun ω => ∫ x, φ x * kpzRegularized P Z t η h₀ x ω) =ᵐ[P] fwd η :=
      hEq.mono fun η hη => hη.symm
    exact (hH t ht h₀ φ).congr' hEq' EventuallyEq.rfl
  have hfwdDiffMeasure : TendstoInMeasure P
      (fun η ω => fwd η ω - H t h₀ ω φ) (nhdsWithin 0 (Set.Ioi 0)) (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm] at hfwdTMeasure ⊢
    simpa using hfwdTMeasure
  have hrevRawMeasure : TendstoInMeasure P
      (fun η ω => ∫ x, φ x * kpzRegularizedReversed P Z u T η h₀ x ω)
      (nhdsWithin 0 (Set.Ioi 0)) (fun ω => X u h₀ φ ω) :=
    tendstoInMeasure_of_tendsto_eLpNorm
      (lt_of_lt_of_le zero_lt_one hp).ne'
      (hXLp u h₀ φ p hu huT hp hpTop)
  have hrevTMeasure : TendstoInMeasure P rev (nhdsWithin 0 (Set.Ioi 0))
      (fun ω => X u h₀ φ ω) := by
    have hEq : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0), (rev η) =ᵐ[P]
        (fun ω => ∫ x, φ x * kpzRegularizedReversed P Z u T η h₀ x ω) := by
      filter_upwards [hηvalid] with η hη
      simp [rev, hη.1, hη.2]
    have hEq' : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (fun ω => ∫ x, φ x * kpzRegularizedReversed P Z u T η h₀ x ω) =ᵐ[P] rev η :=
      hEq.mono fun η hη => hη.symm
    exact hrevRawMeasure.congr' hEq' EventuallyEq.rfl
  have hrevDiffMeasure : TendstoInMeasure P
      (fun η ω => rev η ω - X u h₀ φ ω) (nhdsWithin 0 (Set.Ioi 0)) (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm] at hrevTMeasure ⊢
    simpa using hrevTMeasure
  have hfirstFwd : AEMeasurable
      (fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) P :=
    hfwdRep δ hδ hδt
  have hfirstRev : AEMeasurable
      (fun ω => ∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω) P :=
    hrevRep δ hδ hδt
  have hforwardPair : TendstoInDistribution
      (fun η ω => ((∫ x, φ x * kpzRegularized P Z t δ h₀ x ω), fwd η ω))
      (nhdsWithin 0 (Set.Ioi 0))
      (fun ω => ((∫ x, φ x * kpzRegularized P Z t δ h₀ x ω), H t h₀ ω φ))
      (fun _ => P) P := by
    let A : Ω → ℝ := fun ω => ∫ x, φ x * kpzRegularized P Z t δ h₀ x ω
    let B : Ω → ℝ := fun ω => H t h₀ ω φ
    have hbase : AEMeasurable (fun ω => (A ω, B ω)) P :=
      hfirstFwd.prodMk (hHmeasFull t ht φ)
    have htriple := (tendstoInDistribution_const hbase).prodMk_of_tendstoInMeasure_const
      (fun _ ω => (A ω, B ω))
      (fun η ω => fwd η ω - B ω)
      (fun ω => (A ω, B ω))
      hfwdDiffMeasure (fun η => (hfwdAEMeas η).sub (hHmeasFull t ht φ))
    have hmap := htriple.continuous_comp
      (g := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2 + q.2)) (by fun_prop)
    simpa [A, B, Function.comp_def, sub_add_cancel] using hmap
  have hreversePair : TendstoInDistribution
      (fun η ω => ((∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω), rev η ω))
      (nhdsWithin 0 (Set.Ioi 0))
      (fun ω => ((∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω), X u h₀ φ ω))
      (fun _ => P) P := by
    let A : Ω → ℝ := fun ω =>
      ∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω
    let B : Ω → ℝ := fun ω => X u h₀ φ ω
    have hbase : AEMeasurable (fun ω => (A ω, B ω)) P :=
      hfirstRev.prodMk (hXmeasFull u hu huT φ)
    have htriple := (tendstoInDistribution_const hbase).prodMk_of_tendstoInMeasure_const
      (fun _ ω => (A ω, B ω))
      (fun η ω => rev η ω - B ω)
      (fun ω => (A ω, B ω))
      hrevDiffMeasure (fun η => (hrevAEMeas η).sub (hXmeasFull u hu huT φ))
    have hmap := htriple.continuous_comp
      (g := fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2 + q.2)) (by fun_prop)
    simpa [A, B, Function.comp_def, sub_add_cancel] using hmap
  let vF (η : ℝ) (ω : Ω) (i : Fin 2) : ℝ :=
    ∫ x, φ x * kpzRegularized P Z t (if i = 0 then δ else η) h₀ x ω
  let vR (η : ℝ) (ω : Ω) (i : Fin 2) : ℝ :=
    ∫ x, φ x * kpzRegularizedReversed P Z u T (if i = 0 then δ else η) h₀ x ω
  let pairF (η : ℝ) (ω : Ω) : ℝ × ℝ :=
    (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω,
      ∫ x, φ x * kpzRegularized P Z t η h₀ x ω)
  let pairR (η : ℝ) (ω : Ω) : ℝ × ℝ :=
    (∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω,
      ∫ x, φ x * kpzRegularizedReversed P Z u T η h₀ x ω)
  have hvFAEMeas (η : ℝ) (hη : 0 < η) (hηt : η < t) :
      AEMeasurable (vF η) P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    fin_cases i
    · simpa [vF] using hfirstFwd
    · simpa [vF] using hfwdRep η hη hηt
  have hvRAEMeas (η : ℝ) (hη : 0 < η) (hηt : η < t) :
      AEMeasurable (vR η) P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    fin_cases i
    · simpa [vR] using hfirstRev
    · simpa [vR] using hrevRep η hη hηt
  have hlawPairEventually : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0),
      P.map (pairF η) = P.map (pairR η) := by
    filter_upwards [hηvalid] with η hη
    let δvec : Fin 2 → ℝ := fun i => if i = 0 then δ else η
    have htimes : ∀ i : Fin 2, 0 < δvec i ∧ δvec i < t ∧ t ≤ T := by
      intro i
      fin_cases i
      · simp [δvec, hδ, hδt]
        exact le_of_lt htT
      · simp [δvec, hη.1, hη.2]
        exact le_of_lt htT
    have hvec := Critical2DKPZ.JointConvergence.kpzRegularized_reverse_law_of
      ϑ P Z hZ T (shfReversal_measureLaw_of ϑ P Z hZ T) 2 (fun _ => t) δvec
      (fun _ => h₀) (fun _ => φ) htimes
    let e : (Fin 2 → ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.finTwoArrow
    have hvF : AEMeasurable (vF η) P := hvFAEMeas η hη.1 hη.2
    have hvR : AEMeasurable (vR η) P := hvRAEMeas η hη.1 hη.2
    have hmapF : P.map (pairF η) = (P.map (vF η)).map e := by
      have hcomp : (fun ω => e (vF η ω)) = pairF η := by
        funext ω
        apply Prod.ext <;> simp [e, vF, pairF]
      calc
        P.map (pairF η) = P.map (fun ω => e (vF η ω)) := by
          exact Measure.map_congr
            (Eventually.of_forall fun ω => (congrFun hcomp ω).symm)
        _ = (P.map (vF η)).map e :=
          (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hvF).symm
    have hmapR : P.map (pairR η) = (P.map (vR η)).map e := by
      have hcomp : (fun ω => e (vR η ω)) = pairR η := by
        funext ω
        apply Prod.ext <;> simp [e, vR, pairR]
      calc
        P.map (pairR η) = P.map (fun ω => e (vR η ω)) := by
          exact Measure.map_congr
            (Eventually.of_forall fun ω => (congrFun hcomp ω).symm)
        _ = (P.map (vR η)).map e :=
          (AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hvR).symm
    have hvec' := congrArg (Measure.map e) hvec
    have htimeEq : T - t = u := rfl
    have hvec'' : (P.map (vF η)).map e = (P.map (vR η)).map e := by
      simpa [vF, vR, δvec, htimeEq] using hvec'
    calc
      P.map (pairF η) = (P.map (vF η)).map e := hmapF
      _ = (P.map (vR η)).map e := hvec''
      _ = P.map (pairR η) := hmapR.symm
  have hpairLimitLaw : P.map (fun ω =>
      ((∫ x, φ x * kpzRegularized P Z t δ h₀ x ω), H t h₀ ω φ)) =
      P.map (fun ω =>
        ((∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω), X u h₀ φ ω)) := by
    let μF : ℝ → ProbabilityMeasure (ℝ × ℝ) := fun η => ⟨P.map (pairF η), inferInstance⟩
    let μR : ℝ → ProbabilityMeasure (ℝ × ℝ) := fun η => ⟨P.map (pairR η), inferInstance⟩
    let μFfromTID : ℝ → ProbabilityMeasure (ℝ × ℝ) := fun η =>
      ⟨P.map (fun ω => ((∫ x, φ x * kpzRegularized P Z t δ h₀ x ω), fwd η ω)),
        inferInstance⟩
    let μRfromTID : ℝ → ProbabilityMeasure (ℝ × ℝ) := fun η =>
      ⟨P.map (fun ω =>
        ((∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω), rev η ω)),
        inferInstance⟩
    have hμF : μF =ᶠ[nhdsWithin 0 (Set.Ioi 0)] μFfromTID := by
      filter_upwards [hηvalid] with η hη
      apply Subtype.ext
      apply Measure.map_congr
      filter_upwards [] with ω
      simp [pairF, fwd, hη.1, hη.2]
    have hμR : μR =ᶠ[nhdsWithin 0 (Set.Ioi 0)] μRfromTID := by
      filter_upwards [hηvalid] with η hη
      apply Subtype.ext
      apply Measure.map_congr
      filter_upwards [] with ω
      simp [pairR, rev, hη.1, hη.2]
    have hFconv : Tendsto μF (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ⟨P.map (fun ω =>
          ((∫ x, φ x * kpzRegularized P Z t δ h₀ x ω), H t h₀ ω φ)), inferInstance⟩) := by
      exact (hforwardPair.tendsto.congr' hμF.symm)
    have hRconv : Tendsto μR (nhdsWithin 0 (Set.Ioi 0))
        (𝓝 ⟨P.map (fun ω =>
          ((∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω), X u h₀ φ ω)), inferInstance⟩) := by
      exact (hreversePair.tendsto.congr' hμR.symm)
    have hEq : μF =ᶠ[nhdsWithin 0 (Set.Ioi 0)] μR := by
      filter_upwards [hlawPairEventually] with η hη
      apply Subtype.ext
      exact hη
    have hFconv' := hFconv.congr' hEq
    have hlim := tendsto_nhds_unique hFconv' hRconv
    exact congrArg Subtype.val hlim
  have hdiffLaw : P.map (fun ω =>
      (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ) =
      P.map (fun ω =>
        (∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω) - X u h₀ φ ω) := by
    let sub : ℝ × ℝ → ℝ := fun z => z.1 - z.2
    let f : Ω → ℝ := fun ω =>
      (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ
    let r : Ω → ℝ := fun ω =>
      (∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω) - X u h₀ φ ω
    have hf : AEMeasurable f P := hfirstFwd.sub (hHmeasFull t ht φ)
    have hr : AEMeasurable r P := hfirstRev.sub (hXmeasFull u hu huT φ)
    have hsubMeas : Measurable sub := by fun_prop
    have hleft : P.map f = (Measure.map sub (P.map fun ω =>
        ((∫ x, φ x * kpzRegularized P Z t δ h₀ x ω), H t h₀ ω φ))) := by
      symm
      rw [AEMeasurable.map_map_of_aemeasurable hsubMeas.aemeasurable
        (hfirstFwd.prodMk (hHmeasFull t ht φ))]
      rfl
    have hright : P.map r = (Measure.map sub (P.map fun ω =>
        ((∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω), X u h₀ φ ω))) := by
      symm
      rw [AEMeasurable.map_map_of_aemeasurable hsubMeas.aemeasurable
        (hfirstRev.prodMk (hXmeasFull u hu huT φ))]
      rfl
    change P.map f = P.map r
    calc
      P.map f = Measure.map sub (P.map fun ω =>
          ((∫ x, φ x * kpzRegularized P Z t δ h₀ x ω), H t h₀ ω φ)) := hleft
      _ = Measure.map sub (P.map fun ω =>
          ((∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω), X u h₀ φ ω)) :=
        congrArg (Measure.map sub) hpairLimitLaw
      _ = P.map r := hright.symm
  let f : Ω → ℝ := fun ω =>
    (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ
  let r : Ω → ℝ := fun ω =>
    (∫ x, φ x * kpzRegularizedReversed P Z u T δ h₀ x ω) - X u h₀ φ ω
  have hf : AEMeasurable f P := hfirstFwd.sub (hHmeasFull t ht φ)
  have hr : AEMeasurable r P := hfirstRev.sub (hXmeasFull u hu huT φ)
  have hFNorm : eLpNorm f p P = eLpNorm id p (P.map f) := by
    symm
    rw [eLpNorm_map_measure (p := p) measurable_id.aestronglyMeasurable hf]
    simp [f]
  have hRNorm : eLpNorm r p P = eLpNorm id p (P.map r) := by
    symm
    rw [eLpNorm_map_measure (p := p) measurable_id.aestronglyMeasurable hr]
    simp [r]
  have hNormEq : eLpNorm f p P = eLpNorm r p P := by
    calc
      eLpNorm f p P = eLpNorm id p (P.map f) := hFNorm
      _ = eLpNorm id p (P.map r) := by rw [hdiffLaw]
      _ = eLpNorm r p P := hRNorm.symm
  exact hNormEq

/-- Test pairings of the forward regularized field converge to the critical process in every finite Lᵖ space with p ≥ 1. -/
theorem kpzRegularized_pairing_tendsto_eLpNorm_of_process
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hC12 : ToyJointAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (hHmeas : ∀ t, 0 < t → ∀ h₀ : Plane →ᵇ ℝ, ∀ φ : TestFn,
      Measurable[shfSigma Z] fun ω => H t h₀ ω φ)
    {t : ℝ} (ht : 0 < t) (h₀ : Plane →ᵇ ℝ) (φ : TestFn)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hpTop : p ≠ ⊤) :
    Tendsto (fun δ : ℝ => eLpNorm
      (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ) p P)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  let T : ℝ := 2 * t
  have hT : 0 < T := by dsimp [T]; positivity
  have htT : t < T := by dsimp [T]; linarith
  obtain ⟨X, hXmeas, _hXbound, hXLp, _hXLattice, _hXlaw⟩ := hC12 T hT
  have hδvalid : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ ∧ δ < t := by
    have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < δ := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact hδ
    have hlt : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), δ < t := by
      have hnhds : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), δ < t := Iio_mem_nhds ht
      exact hnhds.filter_mono nhdsWithin_le_nhds
    exact hpos.and hlt
  have hnormEq : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      eLpNorm
        (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ) p P =
      eLpNorm
        (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z (T - t) T δ h₀ x ω) -
          X (T - t) h₀ φ ω) p P := by
    filter_upwards [hδvalid] with δ hδ
    exact kpzRegularized_pairing_eLpNorm_eq_of_process
      ϑ P Z hZ H hH hHmeas T X hXmeas hXLp ht htT hδ.1 hδ.2 h₀ φ p hp hpTop
  have hu : 0 ≤ T - t := by linarith
  have huT : T - t < T := by linarith
  have hnormEq' : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
      eLpNorm
        (fun ω => (∫ x, φ x * kpzRegularizedReversed P Z (T - t) T δ h₀ x ω) -
          X (T - t) h₀ φ ω) p P =
      eLpNorm
        (fun ω => (∫ x, φ x * kpzRegularized P Z t δ h₀ x ω) - H t h₀ ω φ) p P :=
    hnormEq.mono fun δ hδ => hδ.symm
  exact (hXLp (T - t) h₀ φ p hu huT hp hpTop).congr' hnormEq'

end Critical2DKPZ.LocalSobolev

end
