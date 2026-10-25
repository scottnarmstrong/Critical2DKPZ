/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralProduct
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! For a locally compact second-countable Hausdorff space, probability laws on countable products of its vague measure space are determined by all finite joint compact-test laws. -/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped Topology

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.RandomMeasure

/-- Sets depending on finitely many coordinates in a countable real product. -/
def finiteRealCylinder {ι : Type*} : Set (Set (ι → ℝ)) :=
  {A | ∃ s : Finset ι, ∃ U : ι → Set ℝ,
    (∀ i ∈ s, MeasurableSet (U i)) ∧ A = Set.pi (s : Set ι) U}

/-- Finite-coordinate cylinders form a π-system. -/
theorem finiteRealCylinder_isPiSystem {ι : Type*} :
    IsPiSystem (finiteRealCylinder (ι := ι)) := by
  classical
  rintro A ⟨s, U, hU, rfl⟩ B ⟨t, V, hV, rfl⟩ _
  let W : ι → Set ℝ := fun i =>
    (if i ∈ s then U i else Set.univ) ∩ (if i ∈ t then V i else Set.univ)
  refine ⟨s ∪ t, W, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with his | hit
    · by_cases hit : i ∈ t
      · simpa [W, his, hit] using (hU i his).inter (hV i hit)
      · simpa [W, his, hit] using hU i his
    · by_cases his : i ∈ s
      · simpa [W, his, hit] using (hU i his).inter (hV i hit)
      · simpa [W, his, hit] using hV i hit
  · ext x
    change (x ∈ Set.pi (s : Set ι) U ∧ x ∈ Set.pi (t : Set ι) V) ↔
      x ∈ Set.pi ((s ∪ t : Finset ι) : Set ι) W
    constructor
    · rintro ⟨hxs, hxt⟩ i hi
      rcases Finset.mem_union.mp hi with his | hit
      · have hleft : x i ∈ (if i ∈ s then U i else Set.univ) := by
          have hxs' : x i ∈ U i := hxs i (by simpa using his)
          simpa [his] using hxs'
        have hright : x i ∈ (if i ∈ t then V i else Set.univ) := by
          by_cases hit : i ∈ t
          · simpa [hit] using hxt i hit
          · simp [hit]
        exact ⟨hleft, hright⟩
      · have hright : x i ∈ (if i ∈ t then V i else Set.univ) := by
          have hxt' : x i ∈ V i := hxt i (by simpa using hit)
          simpa [hit] using hxt'
        have hleft : x i ∈ (if i ∈ s then U i else Set.univ) := by
          by_cases his : i ∈ s
          · simpa [his] using hxs i his
          · simp [his]
        exact ⟨hleft, hright⟩
    · intro hx
      constructor
      · intro i hi
        have hi' : i ∈ s := by simpa using hi
        have hmem := hx i (Finset.mem_union.mpr (Or.inl hi'))
        have hleft : x i ∈ (if i ∈ s then U i else Set.univ) := hmem.1
        simpa [hi'] using hleft
      · intro i hi
        have hi' : i ∈ t := by simpa using hi
        have hmem := hx i (Finset.mem_union.mpr (Or.inr hi'))
        have hright : x i ∈ (if i ∈ t then V i else Set.univ) := hmem.2
        simpa [hi'] using hright

/-- Finite-coordinate cylinders generate the product Borel σ-algebra on a
countable real product. -/
theorem finiteRealCylinder_generateFrom {ι : Type*} [Countable ι] :
    MeasurableSpace.generateFrom (finiteRealCylinder (ι := ι)) =
      (MeasurableSpace.pi : MeasurableSpace (ι → ℝ)) := by
  classical
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro A ⟨s, U, hU, rfl⟩
    exact MeasurableSet.pi (Finite.countable (Finset.finite_toSet s)) hU
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_mono
    rintro A ⟨i, B, hB, rfl⟩
    refine ⟨{i}, fun j => if j = i then B else Set.univ, ?_, ?_⟩
    · intro j hj
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      simpa using hB
    · ext x
      simp

/-- A law on a countable real product is determined by all its finite
coordinate marginal laws. -/
theorem measure_eq_of_finiteCoordinateLaws {ι : Type*} [Countable ι]
    (μ ν : Measure (ι → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ s : Finset ι,
      Measure.map (fun x : ι → ℝ => fun i : s => x i.1) μ =
        Measure.map (fun x : ι → ℝ => fun i : s => x i.1) ν) :
    μ = ν := by
  classical
  apply ext_of_generate_finite (finiteRealCylinder (ι := ι))
    finiteRealCylinder_generateFrom.symm finiteRealCylinder_isPiSystem
  · intro A hA
    rcases hA with ⟨s, U, hU, rfl⟩
    let B : Set (s → ℝ) := Set.pi Set.univ fun i => U i.1
    have hB : MeasurableSet B := by
      exact MeasurableSet.univ_pi fun i => hU i i.2
    have hmaps := congrArg (fun m : Measure (s → ℝ) => m B) (h s)
    rw [Measure.map_apply (by fun_prop) hB, Measure.map_apply (by fun_prop) hB] at hmaps
    have hpre : (fun x : ι → ℝ => fun i : s => x i.1) ⁻¹' B =
        Set.pi (s : Set ι) U := by
      ext x
      simp [B, Set.mem_pi]
    rw [hpre] at hmaps
    exact hmaps
  · have htotal := congrArg
      (fun m : Measure ((∅ : Finset ι) → ℝ) => m Set.univ) (h ∅)
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ,
      Measure.map_apply (by fun_prop) MeasurableSet.univ] at htotal
    simpa using htotal

/-- The countable compact-test family at each coordinate of a product of
positive Radon measure spaces. -/
def vagueProductReadout {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ι → PositiveRadonMeasure X) : ι → ((ℕ × ℕ) ⊕ ℕ → ℝ) :=
  fun i => countableVagueReadout K (μ i)

/-- The flattened coordinate family of countable compact-test pairings. -/
@[expose]
def vagueProductReadoutFlat {ι X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (μ : ι → PositiveRadonMeasure X) :
    (ι × ((ℕ × ℕ) ⊕ ℕ)) → ℝ :=
  fun p => countableVagueReadout K (μ p.1) p.2

/-- Every finite family of compact-test integrals is continuous on the countable product of vague measure spaces. -/
theorem continuous_finite_vagueProductReadoutFlat {ι X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (s : Finset (ι × ((ℕ × ℕ) ⊕ ℕ))) :
    Continuous (fun μ : ι → PositiveRadonMeasure X =>
      fun p : s => vagueProductReadoutFlat K μ p.1) := by
  apply continuous_pi
  intro p
  change Continuous (fun μ : ι → PositiveRadonMeasure X =>
    vaguePairing (μ p.1.1) (countableVagueTest K p.1.2))
  exact (continuous_vaguePairing (countableVagueTest K p.1.2)).comp
    (continuous_apply p.1.1)

/-- Borel sets on a countable product of vague measure spaces are generated by
the countable family of compact-test pairings. -/
theorem measurableSpace_eq_comap_vagueProductReadout {ι X : Type*} [Countable ι]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    (inferInstance : MeasurableSpace (ι → PositiveRadonMeasure X)) =
      MeasurableSpace.comap (vagueProductReadout K)
        (MeasurableSpace.pi : MeasurableSpace
          (ι → ((ℕ × ℕ) ⊕ ℕ → ℝ))) := by
  classical
  rw [MeasurableSpace.pi, MeasurableSpace.comap_process_pi]
  apply iSup_congr
  intro i
  have hreadout : @borel (PositiveRadonMeasure X) (vagueTopology X) =
      MeasurableSpace.comap (countableVagueReadout K)
        (MeasurableSpace.pi : MeasurableSpace ((ℕ × ℕ) ⊕ ℕ → ℝ)) :=
    vague_borel_eq_countableReadout K
  have htestSpace : (inferInstance : MeasurableSpace ((ℕ × ℕ) ⊕ ℕ → ℝ)) =
      @borel _ inferInstance := BorelSpace.measurable_eq
  change MeasurableSpace.comap (fun μ : ι → PositiveRadonMeasure X => μ i)
      (MeasurableSpace.comap Subtype.val inferInstance) = _
  rw [eval_eq_vague_borel]
  change MeasurableSpace.comap (fun μ : ι → PositiveRadonMeasure X => μ i)
      (@borel (PositiveRadonMeasure X) (vagueTopology X)) =
    MeasurableSpace.comap
      (fun μ : ι → PositiveRadonMeasure X => countableVagueReadout K (μ i))
      (MeasurableSpace.pi : MeasurableSpace ((ℕ × ℕ) ⊕ ℕ → ℝ))
  calc
    _ = MeasurableSpace.comap (fun μ : ι → PositiveRadonMeasure X => μ i)
        (MeasurableSpace.comap (countableVagueReadout K)
          (MeasurableSpace.pi : MeasurableSpace ((ℕ × ℕ) ⊕ ℕ → ℝ))) := by
      rw [← hreadout]
    _ = MeasurableSpace.comap
        (fun μ : ι → PositiveRadonMeasure X => countableVagueReadout K (μ i))
        (MeasurableSpace.pi : MeasurableSpace ((ℕ × ℕ) ⊕ ℕ → ℝ)) := by
      rw [MeasurableSpace.comap_comp]
      rfl

/-- The flattened compact-test coordinates also generate the Borel σ-algebra
of the countable product. -/
theorem measurableSpace_eq_comap_vagueProductReadoutFlat {ι X : Type*} [Countable ι]
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) :
    (inferInstance : MeasurableSpace (ι → PositiveRadonMeasure X)) =
      MeasurableSpace.comap (vagueProductReadoutFlat K)
        (MeasurableSpace.pi : MeasurableSpace
          (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ)) := by
  let e : MeasurableEquiv (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ)
      (ι → ((ℕ × ℕ) ⊕ ℕ → ℝ)) := MeasurableEquiv.curry ι ((ℕ × ℕ) ⊕ ℕ) ℝ
  have hfun : vagueProductReadout K = e ∘ vagueProductReadoutFlat K := by
    funext μ
    funext i
    funext j
    rfl
  rw [measurableSpace_eq_comap_vagueProductReadout K, hfun,
    ← MeasurableSpace.comap_comp]
  rw [e.measurableEmbedding.comap_eq]

/-- A law on a finite or countable product of vague measure spaces is
determined by the finite joint laws of the countable compact-test family. -/
theorem probabilityMeasure_eq_of_finite_vagueProductReadoutLaws {ι X : Type*}
    [Countable ι] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X)
    (P Q : ProbabilityMeasure (ι → PositiveRadonMeasure X))
    (h : ∀ s : Finset (ι × ((ℕ × ℕ) ⊕ ℕ)),
      Measure.map (fun μ : ι → PositiveRadonMeasure X =>
        fun p : s => vagueProductReadoutFlat K μ p.1) (P : Measure _) =
      Measure.map (fun μ : ι → PositiveRadonMeasure X =>
        fun p : s => vagueProductReadoutFlat K μ p.1) (Q : Measure _)) :
    P = Q := by
  classical
  let F : (ι → PositiveRadonMeasure X) →
      (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ) := vagueProductReadoutFlat K
  have hF : Measurable F := by
    rw [measurable_pi_iff]
    intro p
    exact (measurable_vaguePairing_eval (countableVagueTest K p.2)).comp
      (measurable_pi_apply p.1)
  let PF : Measure (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ) :=
    (P : Measure (ι → PositiveRadonMeasure X)).map F
  let QF : Measure (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ) :=
    (Q : Measure (ι → PositiveRadonMeasure X)).map F
  have hfinite : ∀ s : Finset (ι × ((ℕ × ℕ) ⊕ ℕ)),
      Measure.map (fun y : (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ) => fun p : s => y p.1)
          PF =
      Measure.map (fun y : (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ) => fun p : s => y p.1)
          QF := by
    intro s
    let g : (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ) → (s → ℝ) := fun y p => y p.1
    have hg : Measurable g := by fun_prop
    let G : (ι → PositiveRadonMeasure X) → (s → ℝ) := fun μ p => F μ p.1
    have hG : Measure.map G (P : Measure _) = Measure.map G (Q : Measure _) := by
      simpa [G, F] using h s
    change Measure.map g PF = Measure.map g QF
    calc
      Measure.map g PF = Measure.map G (P : Measure _) := by
        change Measure.map g ((P : Measure _).map F) = _
        rw [Measure.map_map hg hF]
        rfl
      _ = Measure.map G (Q : Measure _) := hG
      _ = Measure.map g QF := by
        change _ = Measure.map g ((Q : Measure _).map F)
        rw [Measure.map_map hg hF]
        rfl
  have hPFQF : PF = QF :=
    measure_eq_of_finiteCoordinateLaws PF QF hfinite
  have hPmeas : (MeasurableSpace.pi : MeasurableSpace
      (ι → PositiveRadonMeasure X)) =
        MeasurableSpace.comap F
          (MeasurableSpace.pi : MeasurableSpace
            (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ)) := by
    simpa [F] using measurableSpace_eq_comap_vagueProductReadoutFlat K
  apply Subtype.ext
  apply Measure.ext
  intro A hA
  change MeasurableSet[(MeasurableSpace.pi : MeasurableSpace
    (ι → PositiveRadonMeasure X))] A at hA
  rw [hPmeas] at hA
  rcases MeasurableSpace.measurableSet_comap.mp hA with ⟨B, hB, rfl⟩
  have hmap := congrArg
    (fun m : Measure (ι × ((ℕ × ℕ) ⊕ ℕ) → ℝ) => m B) hPFQF
  rw [Measure.map_apply hF hB, Measure.map_apply hF hB] at hmap
  exact hmap

/-- For a tight sequence of probability laws on a countable product of vague measure spaces, convergence of all finite joint compact-test laws to those under `Q` implies weak convergence to `Q`. -/
theorem tendsto_probabilityMeasure_of_tight_vagueProductReadoutLaws
    {ι X : Type*} [Countable ι] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X)
    (P : ℕ → ProbabilityMeasure (ι → PositiveRadonMeasure X))
    (Q : ProbabilityMeasure (ι → PositiveRadonMeasure X))
    (hP : IsTightMeasureSet (Set.range fun n : ℕ =>
      (P n : Measure (ι → PositiveRadonMeasure X))))
    (hread : ∀ s : Finset (ι × ((ℕ × ℕ) ⊕ ℕ)),
      Tendsto
        (fun n => (P n).map (fun μ : ι → PositiveRadonMeasure X =>
          fun p : s => vagueProductReadoutFlat K μ p.1)) atTop
        (𝓝 (Q.map (fun μ : ι → PositiveRadonMeasure X =>
          fun p : s => vagueProductReadoutFlat K μ p.1)))) :
    Tendsto P atTop (𝓝 Q) := by
  classical
  letI : PolishSpace (ι → PositiveRadonMeasure X) :=
    vagueCountableProductPolishSpace
  letI : BorelSpace (ι → PositiveRadonMeasure X) := inferInstance
  letI : OpensMeasurableSpace (ι → PositiveRadonMeasure X) := inferInstance
  letI : IsCompletelyMetrizableSpace (ι → PositiveRadonMeasure X) := inferInstance
  letI : PseudoMetrizableSpace (ι → PositiveRadonMeasure X) := inferInstance
  letI : SeparableSpace (ι → PositiveRadonMeasure X) := inferInstance
  letI : MetrizableSpace (ProbabilityMeasure (ι → PositiveRadonMeasure X)) := inferInstance
  have hTight : IsTightMeasureSet
      ((fun μ : ProbabilityMeasure (ι → PositiveRadonMeasure X) =>
          (μ : Measure (ι → PositiveRadonMeasure X))) '' Set.range P) := by
    have hset :
        ((fun μ : ProbabilityMeasure (ι → PositiveRadonMeasure X) =>
            (μ : Measure (ι → PositiveRadonMeasure X))) '' Set.range P) =
          Set.range fun n : ℕ => (P n : Measure (ι → PositiveRadonMeasure X)) := by
      ext μ
      simp
    rw [hset]
    exact hP
  have hcompact := _root_.isCompact_closure_of_isTightMeasureSet hTight
  have hmem : ∀ᶠ n : ℕ in atTop, P n ∈ closure (Set.range P) := by
    filter_upwards [] with n
    exact subset_closure ⟨n, rfl⟩
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt
    (l := atTop) (f := P) (y := Q) hmem
  intro R hR hcluster
  obtain ⟨φ, hφ, hlim⟩ := hcluster.tendsto_subseq
  have hlaws : ∀ s : Finset (ι × ((ℕ × ℕ) ⊕ ℕ)),
      Measure.map (fun μ : ι → PositiveRadonMeasure X =>
        fun p : s => vagueProductReadoutFlat K μ p.1) (R : Measure _) =
      Measure.map (fun μ : ι → PositiveRadonMeasure X =>
        fun p : s => vagueProductReadoutFlat K μ p.1) (Q : Measure _) := by
    intro s
    let F : (ι → PositiveRadonMeasure X) → (s → ℝ) := fun μ p =>
      vagueProductReadoutFlat K μ p.1
    have hF : Continuous F := continuous_finite_vagueProductReadoutFlat K s
    have hclusterMap : Tendsto (fun n => (P (φ n)).map F) atTop
        (𝓝 (R.map F)) :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n => P (φ n)) R hlim hF
    have hgivenMap : Tendsto (fun n => (P (φ n)).map F) atTop
        (𝓝 (Q.map F)) := (hread s).comp hφ.tendsto_atTop
    have hmap : (R.map F : Measure (s → ℝ)) = (Q.map F : Measure (s → ℝ)) := by
      have hprob : R.map F = Q.map F := tendsto_nhds_unique hclusterMap hgivenMap
      exact congrArg Subtype.val hprob
    simpa only [ProbabilityMeasure.toMeasure_map] using hmap
  exact probabilityMeasure_eq_of_finite_vagueProductReadoutLaws K R Q hlaws

/-- Weak convergence of laws on a product of vague measure spaces implies convergence of every finite joint law of compact-test integrals. -/
theorem tendsto_finite_vagueProductReadoutLaws_of_tendsto
    {ι X : Type*} [Countable ι] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X)
    (P : ℕ → ProbabilityMeasure (ι → PositiveRadonMeasure X))
    (Q : ProbabilityMeasure (ι → PositiveRadonMeasure X))
    (hP : Tendsto P atTop (𝓝 Q)) :
    ∀ s : Finset (ι × ((ℕ × ℕ) ⊕ ℕ)),
      Tendsto
        (fun n => (P n).map (fun μ : ι → PositiveRadonMeasure X =>
          fun p : s => vagueProductReadoutFlat K μ p.1)) atTop
        (𝓝 (Q.map (fun μ : ι → PositiveRadonMeasure X =>
          fun p : s => vagueProductReadoutFlat K μ p.1))) := by
  intro s
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous P Q hP
    (continuous_finite_vagueProductReadoutFlat K s)

/-- For a tight sequence, weak convergence of laws on a product of vague measure spaces is equivalent to convergence of all finite joint compact-test laws. -/
theorem tendsto_probabilityMeasure_iff_finite_vagueProductReadoutLaws
    {ι X : Type*} [Countable ι] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (K : CompactExhaustion X)
    (P : ℕ → ProbabilityMeasure (ι → PositiveRadonMeasure X))
    (Q : ProbabilityMeasure (ι → PositiveRadonMeasure X))
    (hTight : IsTightMeasureSet (Set.range fun n : ℕ =>
      (P n : Measure (ι → PositiveRadonMeasure X)))) :
    Tendsto P atTop (𝓝 Q) ↔
      ∀ s : Finset (ι × ((ℕ × ℕ) ⊕ ℕ)),
        Tendsto
          (fun n => (P n).map (fun μ : ι → PositiveRadonMeasure X =>
            fun p : s => vagueProductReadoutFlat K μ p.1)) atTop
          (𝓝 (Q.map (fun μ : ι → PositiveRadonMeasure X =>
            fun p : s => vagueProductReadoutFlat K μ p.1))) := by
  constructor
  · exact tendsto_finite_vagueProductReadoutLaws_of_tendsto K P Q
  · exact tendsto_probabilityMeasure_of_tight_vagueProductReadoutLaws K P Q hTight

end Critical2DKPZ.RandomMeasure

end
