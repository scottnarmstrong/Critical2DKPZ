/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.FiniteScaleBlocks
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Critical2DKPZ.RandomMeasure.GeneralDetermination

/-! # Independence on consecutive time intervals in polymer limits

Compact-test convergence transfers the independence of polymer measures on consecutive time intervals to their limiting random measures. -/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory TopologicalSpace
open scoped CompactlySupported Topology

set_option linter.style.haveILetI false

noncomputable section

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit

/-- At each allowed time pair, the limiting random pair measure is measurable and almost surely locally finite. -/
theorem polymerSubseqLimit_measurable_locallyFinite
    (ϑ : ℝ) (D : Set ℝ) (ψ : ℕ → ℕ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) :
    ∀ s ∈ D, ∀ t ∈ D, s < t →
      Measurable (Z s t) ∧ ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z s t ω) := by
  intro s hs t ht hst
  refine ⟨(hZ.1 s hs t ht hst).1, ?_⟩
  exact (hZ.1 s hs t ht hst).2.mono fun _ hω => hω.1

private theorem polymerPairing_tendstoInDistribution_of_processLaw_tendsto
    (ϑ : ℝ) (D : Set ℝ) (hD : D.Countable) (η : ℕ → ℕ) (m : ℕ)
    (s t : Fin m → ℝ) (hTimes : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i)
    (φ : Fin m → C_c(Plane × Plane, ℝ))
    (Q : ProbabilityMeasure (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure))
    (hweak :
      letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
        RandomMeasure.vagueTopology (Plane × Plane)
      letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
        RandomMeasure.polishSpace_positiveRadonMeasure_planePair
      letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
        ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
      letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
        ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
      letI : Countable D := hD.to_subtype
      letI : Countable (PolymerPairIndex D) := inferInstance
      letI : TopologicalSpace
        (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := Pi.topologicalSpace
      letI : PolishSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) :=
        RandomMeasure.vagueCountableProductPolishSpace
      letI : BorelSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
      letI : OpensMeasurableSpace
        (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
      Tendsto (fun n => polymerRadonProcessLaw ϑ (η n) D) atTop (𝓝 Q)) :
    TendstoInDistribution
      (fun n (ω : Disorder) i =>
        ∫ p, φ i p ∂polymerMeasure ϑ (η n) (s i) (t i) ω)
      atTop
      (fun (q : PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) i =>
        RandomMeasure.vaguePairing
          (q ⟨(⟨s i, (hTimes i).1⟩, ⟨t i, (hTimes i).2.1⟩), (hTimes i).2.2⟩) (φ i))
      (fun _ => disorderLaw) (Q : Measure _) := by
  classical
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : Countable D := hD.to_subtype
  letI : Countable (PolymerPairIndex D) := inferInstance
  letI : TopologicalSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) :=
    Pi.topologicalSpace
  letI : PolishSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) :=
    RandomMeasure.vagueCountableProductPolishSpace
  letI : MeasurableSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  letI : BorelSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  let ind : Fin m → PolymerPairIndex D := fun i =>
    ⟨(⟨s i, (hTimes i).1⟩, ⟨t i, (hTimes i).2.1⟩), (hTimes i).2.2⟩
  let F : (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) → Fin m → ℝ :=
    fun q i => RandomMeasure.vaguePairing (q (ind i)) (φ i)
  have hFcont : Continuous F := by
    apply continuous_pi
    intro i
    exact (RandomMeasure.continuous_vaguePairing (φ i)).comp
      (continuous_apply (ind i))
  have hFmeas : Measurable F := hFcont.measurable
  have hproc (N : ℕ) : Measurable (polymerRadonProcess ϑ N D) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_polymerRadonMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ)
  have hsourceEq (n : ℕ) :
      (fun (ω : Disorder) i =>
        ∫ p, φ i p ∂polymerMeasure ϑ (η n) (s i) (t i) ω) =
      fun ω => F (polymerRadonProcess ϑ (η n) D ω) := by
    funext ω i
    simp [F, ind, polymerRadonProcess, polymerRadonMeasure,
      RandomMeasure.vaguePairing]
  have hsource (n : ℕ) : AEMeasurable
      (fun (ω : Disorder) i =>
        ∫ p, φ i p ∂polymerMeasure ϑ (η n) (s i) (t i) ω) disorderLaw := by
    rw [hsourceEq n]
    exact (hFmeas.comp (hproc (η n))).aemeasurable
  have hmap (n : ℕ) :
      polymerDisorderProbability.map
        (fun (ω : Disorder) i =>
          ∫ p, φ i p ∂polymerMeasure ϑ (η n) (s i) (t i) ω) =
        (polymerRadonProcessLaw ϑ (η n) D).map F := by
    apply Subtype.ext
    calc
      Measure.map (fun (ω : Disorder) i =>
          ∫ p, φ i p ∂polymerMeasure ϑ (η n) (s i) (t i) ω) disorderLaw =
        Measure.map (fun ω => F (polymerRadonProcess ϑ (η n) D ω)) disorderLaw := by
          apply Measure.map_congr
          exact Filter.Eventually.of_forall fun ω => congrFun (hsourceEq n) ω
      _ = Measure.map F
          (Measure.map (polymerRadonProcess ϑ (η n) D) disorderLaw) :=
            (Measure.map_map hFmeas (hproc (η n))).symm
      _ = (Measure.map F (polymerRadonProcessLaw ϑ (η n) D : Measure _)) := rfl
  have hlimit : Tendsto (fun n => (polymerRadonProcessLaw ϑ (η n) D).map F)
      atTop (𝓝 (Q.map F)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => polymerRadonProcessLaw ϑ (η n) D) Q hweak hFcont
  refine ⟨hsource, hFmeas.aemeasurable, ?_⟩
  exact Tendsto.congr' (Filter.Eventually.of_forall fun n => (hmap n).symm) hlimit

/-- In a polymer subsequential limit, the random measures on consecutive time intervals are jointly independent. -/
theorem iIndepFun_polymerSubseqLimit_consecutive
    (ϑ : ℝ) (D : Set ℝ) (hD : D.Countable)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z)
    (k : ℕ) (t : Fin (k + 1) → ℝ) (ht : StrictMono t) (htD : ∀ i, t i ∈ D) :
    iIndepFun (fun i : Fin k => Z (t i.castSucc) (t i.succ)) P := by
  classical
  letI : TopologicalSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.vagueTopology (Plane × Plane)
  letI : PolishSpace RandomMeasure.PlanePairRadonMeasure :=
    RandomMeasure.polishSpace_positiveRadonMeasure_planePair
  letI : BorelSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.symm⟩
  letI : OpensMeasurableSpace RandomMeasure.PlanePairRadonMeasure :=
    ⟨RandomMeasure.borel_positiveRadonMeasure_eq_comap.le⟩
  letI : Countable D := hD.to_subtype
  letI : Countable (D × D) := inferInstance
  letI : Countable (PolymerPairIndex D) := inferInstance
  letI : TopologicalSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) :=
    Pi.topologicalSpace
  letI : PolishSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) :=
    RandomMeasure.vagueCountableProductPolishSpace
  letI : MeasurableSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  letI : BorelSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  letI : TopologicalSpace (Fin k → RandomMeasure.PlanePairRadonMeasure) := Pi.topologicalSpace
  letI : PolishSpace (Fin k → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  letI : MeasurableSpace (Fin k → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  letI : BorelSpace (Fin k → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  letI : OpensMeasurableSpace (Fin k → RandomMeasure.PlanePairRadonMeasure) := inferInstance
  let idx : Fin k → PolymerPairIndex D := fun i =>
    ⟨(⟨t i.castSucc, htD i.castSucc⟩, ⟨t i.succ, htD i.succ⟩),
      ht i.castSucc_lt_succ⟩
  obtain ⟨ξ, hξ, _, Q, hweak⟩ :=
    exists_subseq_tendsto_polymerRadonProcessLaw ϑ D hD ψ hψ
  let η : ℕ → ℕ := ψ ∘ ξ
  have hweak' : Tendsto (fun n => polymerRadonProcessLaw ϑ (η n) D)
      atTop (𝓝 Q) := by
    exact hweak
  let E : (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) →
      (Fin k → RandomMeasure.PlanePairRadonMeasure) := fun q i => q (idx i)
  have hEcont : Continuous E := by
    apply continuous_pi
    intro i
    exact continuous_apply (idx i)
  let L : ℕ → ProbabilityMeasure (Fin k → RandomMeasure.PlanePairRadonMeasure) :=
    fun n => (polymerRadonProcessLaw ϑ (η n) D).map E
  have hLweak : Tendsto L atTop (𝓝 (Q.map E)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => polymerRadonProcessLaw ϑ (η n) D) Q hweak' hEcont
  let M : ℕ → Fin k → ProbabilityMeasure RandomMeasure.PlanePairRadonMeasure :=
    fun n i => (polymerRadonProcessLaw ϑ (η n) D).map (fun q => q (idx i))
  let Mlim : Fin k → ProbabilityMeasure RandomMeasure.PlanePairRadonMeasure :=
    fun i => Q.map (fun q => q (idx i))
  have hMcoord (i : Fin k) : Tendsto (fun n => M n i) atTop (𝓝 (Mlim i)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => polymerRadonProcessLaw ϑ (η n) D) Q hweak'
      (continuous_apply (idx i))
  have hM : Tendsto M atTop (𝓝 Mlim) := tendsto_pi_nhds.2 hMcoord
  have hMpi : Tendsto (fun n => ProbabilityMeasure.pi (M n)) atTop
      (𝓝 (ProbabilityMeasure.pi Mlim)) :=
    (ProbabilityMeasure.continuous_pi).continuousAt.tendsto.comp hM
  have hproc (N : ℕ) : Measurable (polymerRadonProcess ϑ N D) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_polymerRadonMeasure ϑ N (i.1.1 : ℝ) (i.1.2 : ℝ)
  have hfiniteInd (n : ℕ) : iIndepFun (fun i : Fin k =>
      polymerRadonMeasure ϑ (η n) (t i.castSucc) (t i.succ)) disorderLaw :=
    iIndepFun_polymerRadonMeasure_consecutive ϑ (η n) k t ht
  have hcoordMeas (n : ℕ) (i : Fin k) : Measurable
      (fun ω => polymerRadonMeasure ϑ (η n) (t i.castSucc) (t i.succ) ω) := by
    let a := evenCeil ((η n : ℝ) * t i.castSucc)
    let b := evenCeil ((η n : ℝ) * t i.succ)
    have hab : a ≤ b := evenCeil_mono
      (mul_le_mul_of_nonneg_left (ht i.castSucc_lt_succ).le (by positivity))
    have hsum : a + (b - a) = b := Nat.add_sub_of_le hab
    have hb : Measurable[Gaussian.disorderBlock a b]
        (fun ω => polymerRadonMeasure ϑ (η n) (t i.castSucc) (t i.succ) ω) := by
      rw [← hsum]
      exact measurable_polymerRadonMeasure_disorderBlock ϑ (η n)
        (t i.castSucc) (t i.succ) a (b - a) rfl rfl
    exact hb.mono (Gaussian.disorderBlock_le a b) le_rfl
  have hfiniteLaw (n : ℕ) : L n = ProbabilityMeasure.pi (M n) := by
    apply Subtype.ext
    have hPi := (hfiniteInd n).map_fun_eq_pi_map
      (fun i => (hcoordMeas n i).aemeasurable)
    have hseq : Measure.map (fun ω : Disorder => fun i : Fin k =>
        polymerRadonMeasure ϑ (η n) (t i.castSucc) (t i.succ) ω) disorderLaw =
        Measure.map E (polymerRadonProcessLaw ϑ (η n) D : Measure _) := by
      calc
        Measure.map (fun ω : Disorder => fun i : Fin k =>
            polymerRadonMeasure ϑ (η n) (t i.castSucc) (t i.succ) ω) disorderLaw =
          Measure.map (fun ω => E (polymerRadonProcess ϑ (η n) D ω)) disorderLaw := by
            apply Measure.map_congr
            exact Filter.Eventually.of_forall fun ω => by
              funext i
              rfl
        _ = Measure.map E
            (Measure.map (polymerRadonProcess ϑ (η n) D) disorderLaw) :=
              (Measure.map_map hEcont.measurable (hproc (η n))).symm
        _ = Measure.map E (polymerRadonProcessLaw ϑ (η n) D : Measure _) := rfl
    have hMarg (i : Fin k) :
        polymerDisorderProbability.map
          (fun ω => polymerRadonMeasure ϑ (η n) (t i.castSucc) (t i.succ) ω) = M n i := by
      apply Subtype.ext
      calc
        Measure.map (fun ω => polymerRadonMeasure ϑ (η n)
            (t i.castSucc) (t i.succ) ω) disorderLaw =
          Measure.map (fun q : PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure =>
            q (idx i)) (Measure.map (polymerRadonProcess ϑ (η n) D) disorderLaw) := by
              rw [Measure.map_map (measurable_pi_apply (idx i)) (hproc (η n))]
              apply Measure.map_congr
              exact Filter.Eventually.of_forall fun ω => rfl
        _ = M n i := rfl
    change Measure.map E (polymerRadonProcessLaw ϑ (η n) D : Measure _) =
      (ProbabilityMeasure.pi (M n) : Measure _)
    calc
      Measure.map E (polymerRadonProcessLaw ϑ (η n) D : Measure _) =
          Measure.map (fun ω : Disorder => fun i : Fin k =>
            polymerRadonMeasure ϑ (η n) (t i.castSucc) (t i.succ) ω) disorderLaw := hseq.symm
      _ = Measure.pi (fun i => Measure.map (fun ω => polymerRadonMeasure ϑ (η n)
            (t i.castSucc) (t i.succ) ω) disorderLaw) := hPi
      _ = (ProbabilityMeasure.pi (M n) : Measure _) := by
          rw [ProbabilityMeasure.toMeasure_pi]
          congr 1
          funext i
          exact congrArg Subtype.val (hMarg i)
  have hjointLimit : Q.map E = ProbabilityMeasure.pi Mlim := by
    apply tendsto_nhds_unique
      (Tendsto.congr' (Filter.Eventually.of_forall fun n => hfiniteLaw n) hLweak)
      hMpi
  have hQind : iIndepFun (fun i : Fin k => fun q : PolymerPairIndex D →
      RandomMeasure.PlanePairRadonMeasure => q (idx i)) (Q : Measure _) := by
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (measurable_pi_apply (idx i)).aemeasurable)).2
    exact congrArg Subtype.val hjointLimit
  let Z' : Fin k → (PolymerPairIndex D → RandomMeasure.PlanePairRadonMeasure) →
      Measure (Plane × Plane) := fun i q => (q (idx i)).1
  have hZ'meas (i : Fin k) : Measurable (Z' i) := by
    exact measurable_subtype_coe.comp (measurable_pi_apply (idx i))
  have hZ'lf : ∀ᵐ q ∂(Q : Measure _), ∀ i, IsLocallyFiniteMeasure (Z' i q) := by
    filter_upwards [] with q i
    exact (q (idx i)).2
  have hZmeas (i : Fin k) : Measurable (Z (t i.castSucc) (t i.succ)) :=
    (hZ.1 (t i.castSucc) (htD i.castSucc) (t i.succ) (htD i.succ)
      (ht i.castSucc_lt_succ)).1
  have hZlf : ∀ᵐ ω ∂P, ∀ i : Fin k, IsLocallyFiniteMeasure
      (Z (t i.castSucc) (t i.succ) ω) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [(hZ.1 (t i.castSucc) (htD i.castSucc) (t i.succ) (htD i.succ)
      (ht i.castSucc_lt_succ)).2] with ω hω
    exact hω.1
  have hpairLaws : ∀ (m : ℕ) (f : Fin m → Fin k × C_c(Plane × Plane, ℝ)),
      P.map (fun ω j => ∫ p, (f j).2 p ∂
        (Z (t (f j).1.castSucc) (t (f j).1.succ) ω)) =
      (Q : Measure _).map (fun q j => ∫ p, (f j).2 p ∂(Z' (f j).1 q)) := by
    intro m f
    let s : Fin m → ℝ := fun j => t (f j).1.castSucc
    let u : Fin m → ℝ := fun j => t (f j).1.succ
    let hTimes : ∀ j, s j ∈ D ∧ u j ∈ D ∧ s j < u j := by
      intro j
      exact ⟨htD _, htD _, ht (f j).1.castSucc_lt_succ⟩
    let φ : Fin m → C_c(Plane × Plane, ℝ) := fun j => (f j).2
    have hZconv := hZ.2 m s u hTimes φ (fun _ => 0)
    let project : (Fin m → ℝ × ℝ) → Fin m → ℝ := fun x j => (x j).1
    have hproject : Continuous project := by fun_prop
    have hZpair := hZconv.continuous_comp hproject
    have hZsub : TendstoInDistribution
        (fun n (ω : Disorder) j =>
          ∫ p, φ j p ∂polymerMeasure ϑ (η n) (s j) (u j) ω)
        atTop
        (fun ω j => ∫ p, φ j p ∂Z (s j) (u j) ω)
        (fun _ => disorderLaw) P := by
      refine ⟨fun n => hZpair.forall_aemeasurable (ξ n), hZpair.aemeasurable_limit, ?_⟩
      exact hZpair.tendsto.comp hξ.tendsto_atTop
    have hQpair := polymerPairing_tendstoInDistribution_of_processLaw_tendsto
      ϑ D hD η m s u hTimes φ Q hweak'
    have hunique := MeasureTheory.tendstoInDistribution_unique
      _ hZsub hQpair
    simpa [s, u, hTimes, φ, Z', RandomMeasure.vaguePairing] using hunique
  have hlaw := RandomMeasure.map_eq_of_pairing_laws P (Q : Measure _) k
    (fun i => Z (t i.castSucc) (t i.succ)) Z'
    hZmeas hZ'meas hZlf hZ'lf hpairLaws
  have hZae (i : Fin k) : AEMeasurable
      (fun ω => Z (t i.castSucc) (t i.succ) ω) P := (hZmeas i).aemeasurable
  have hZ'ae (i : Fin k) : AEMeasurable (Z' i) Q := (hZ'meas i).aemeasurable
  have hZ'rawInd : iIndepFun Z' Q := hQind.comp
    (fun _ μ => (μ.1 : Measure (Plane × Plane))) (fun _ => measurable_subtype_coe)
  have hZ'pi := (iIndepFun_iff_map_fun_eq_pi_map hZ'ae).mp hZ'rawInd
  have hmarg (i : Fin k) : P.map (fun ω => Z (t i.castSucc) (t i.succ) ω) =
      Q.map (Z' i) := by
    have hvecZ : Measurable (fun ω (i : Fin k) => Z (t i.castSucc) (t i.succ) ω) :=
      measurable_pi_iff.mpr hZmeas
    have hleft : P.map (fun ω => Z (t i.castSucc) (t i.succ) ω) =
        Measure.map (fun v : Fin k → Measure (Plane × Plane) => v i)
          (P.map (fun ω j => Z (t j.castSucc) (t j.succ) ω)) := by
      rw [Measure.map_map (measurable_pi_apply i) hvecZ]
      rfl
    have hright : Q.map (Z' i) =
        Measure.map (fun v : Fin k → Measure (Plane × Plane) => v i)
          ((Q : Measure _).map (fun q (j : Fin k) => Z' j q)) := by
      rw [Measure.map_map (measurable_pi_apply i) (measurable_pi_iff.mpr hZ'meas)]
      rfl
    rw [hleft, hright]
    exact congrArg (Measure.map (fun v : Fin k → Measure (Plane × Plane) => v i)) hlaw
  apply (iIndepFun_iff_map_fun_eq_pi_map hZae).2
  calc
    P.map (fun ω i => Z (t i.castSucc) (t i.succ) ω) =
        (Q : Measure _).map (fun q i => Z' i q) := hlaw
    _ = Measure.pi (fun i => Q.map (Z' i)) := hZ'pi
    _ = Measure.pi (fun i => P.map (fun ω => Z (t i.castSucc) (t i.succ) ω)) := by
      congr 1
      funext i
      exact (hmarg i).symm

end Critical2DKPZ.SHF.Flow

end
