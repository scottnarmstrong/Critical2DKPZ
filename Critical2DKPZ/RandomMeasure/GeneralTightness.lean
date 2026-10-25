/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.RandomMeasure.GeneralPolish
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! On a locally compact second-countable Hausdorff space, uniform expected-mass bounds on a compact exhaustion imply tightness of laws on the vague space of positive locally finite measures. -/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology

noncomputable section

set_option linter.style.haveILetI false

namespace Critical2DKPZ.RandomMeasure

/-- The mass of a compact exhaustion window, as a function on vague measure
space. -/
@[expose] def vagueCompactWindowMass {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (K : CompactExhaustion X) (k : ℕ) : PositiveRadonMeasure X → ℝ≥0∞ :=
  fun μ => μ.measure (K k)


/-- Compact-window mass is Borel measurable for the vague topology. -/
theorem measurable_vagueCompactWindowMass {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X) (k : ℕ) :
    Measurable (vagueCompactWindowMass K k) := by
  change @Measurable (PositiveRadonMeasure X) ℝ≥0∞
    (MeasurableSpace.comap Subtype.val inferInstance) inferInstance _
  exact (Measure.measurable_coe ((K.isCompact k).isClosed.measurableSet)).comp
    measurable_subtype_coe

/-- Markov's inequality for a compact-window mass evaluation. -/
theorem measure_ge_vagueCompactWindowMass_le {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (P : ProbabilityMeasure (PositiveRadonMeasure X))
    {k : ℕ} {R : ℝ≥0∞} (hR0 : R ≠ 0) (hRtop : R ≠ ∞) :
    (P : Measure (PositiveRadonMeasure X))
        {μ | R ≤ vagueCompactWindowMass K k μ} ≤
      (∫⁻ μ, vagueCompactWindowMass K k μ ∂(P : Measure _)) / R := by
  exact MeasureTheory.meas_ge_le_lintegral_div
    (μ := (P : Measure (PositiveRadonMeasure X)))
    (measurable_vagueCompactWindowMass K k).aemeasurable hR0 hRtop

/-- Uniform finite expected masses on a compact exhaustion imply tightness of
a family of probability laws on the vague measure space. -/
theorem isTightMeasureSet_of_uniform_expected_compact_mass {X : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : CompactExhaustion X)
    (S : Set (ProbabilityMeasure (PositiveRadonMeasure X)))
    (hExp : ∀ k : ℕ, ∃ M : ℝ≥0∞, M < ∞ ∧
      ∀ P ∈ S, (∫⁻ μ, vagueCompactWindowMass K k μ ∂(P : Measure _)) ≤ M) :
    IsTightMeasureSet
      {((P : ProbabilityMeasure (PositiveRadonMeasure X)) :
        Measure (PositiveRadonMeasure X)) | P ∈ S} := by
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  let δ : ℝ≥0∞ := min ε 1
  have hδpos : 0 < δ := lt_min hε zero_lt_one
  have hδtop : δ < ∞ := lt_of_le_of_lt (min_le_right _ _) (by simp)
  have hδε : δ ≤ ε := min_le_left _ _
  choose M hMtop hMbound using hExp
  let w : ℕ → ℝ≥0∞ := fun k => δ * (1 / 2 : ℝ≥0∞) ^ (k + 1)
  have hwpos (k : ℕ) : 0 < w k := by
    dsimp [w]
    exact ENNReal.mul_pos hδpos.ne' (pow_ne_zero _ (by norm_num))
  have hwtop (k : ℕ) : w k < ∞ := by
    dsimp [w]
    apply ENNReal.mul_lt_top hδtop
    finiteness
  have hwne (k : ℕ) : w k ≠ 0 := (hwpos k).ne'
  have hwne_top (k : ℕ) : w k ≠ ∞ := (hwtop k).ne
  let R : ℕ → ℝ≥0∞ := fun k => M k / w k + 1
  have hRpos (k : ℕ) : 0 < R k := by
    dsimp [R]
    exact zero_lt_one.trans_le (le_add_of_nonneg_left (by positivity))
  have hRtop (k : ℕ) : R k < ∞ := by
    dsimp [R]
    rw [ENNReal.add_lt_top]
    exact ⟨ENNReal.div_lt_top (hMtop k).ne (hwne k), by simp⟩
  have hMtail (k : ℕ) : M k / R k ≤ w k := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (hRpos k).ne')
      (Or.inl (hRtop k).ne)]
    dsimp [R]
    have hcancel : M k / w k * w k = M k :=
      ENNReal.div_mul_cancel (hwne k) (hwne_top k)
    calc
      M k = M k / w k * w k := hcancel.symm
      _ ≤ (M k / w k + 1) * w k := by
        gcongr
        exact le_add_of_nonneg_right (by norm_num)
      _ = w k * (M k / w k + 1) := mul_comm _ _
  let A : Set (PositiveRadonMeasure X) :=
    {μ | ∀ k, vagueCompactWindowMass K k μ ≤ R k}
  have hcompact : IsCompact (closure A) := by
    rw [isCompact_vagueClosure_iff_localMassBound K]
    intro k
    refine ⟨(R k).toReal, fun μ hμ => ?_⟩
    have hle := hμ k
    change μ.measure (K k) ≤ R k at hle
    simpa only [Measure.real_def] using ENNReal.toReal_mono (hRtop k).ne hle
  have hbad (P : ProbabilityMeasure (PositiveRadonMeasure X)) (hP : P ∈ S) :
      (P : Measure (PositiveRadonMeasure X)) (Aᶜ) ≤ δ := by
    have hbadEq : Aᶜ = ⋃ k, {μ | R k < vagueCompactWindowMass K k μ} := by
      ext μ
      simp only [A, mem_compl_iff, mem_ofPred_eq, mem_iUnion, not_forall]
      simp only [not_le]
    calc
      (P : Measure (PositiveRadonMeasure X)) (Aᶜ) =
          (P : Measure (PositiveRadonMeasure X))
            (⋃ k, {μ | R k < vagueCompactWindowMass K k μ}) := by rw [hbadEq]
      _ ≤ ∑' k, (P : Measure (PositiveRadonMeasure X))
          {μ | R k < vagueCompactWindowMass K k μ} := measure_iUnion_le _
      _ ≤ ∑' k, w k := by
        apply ENNReal.tsum_le_tsum
        intro k
        calc
          (P : Measure (PositiveRadonMeasure X))
              {μ | R k < vagueCompactWindowMass K k μ} ≤
              (P : Measure (PositiveRadonMeasure X))
                {μ | R k ≤ vagueCompactWindowMass K k μ} :=
            measure_mono (by
              intro μ hμ
              change R k < vagueCompactWindowMass K k μ at hμ
              exact hμ.le)
          _ ≤ (∫⁻ μ, vagueCompactWindowMass K k μ ∂(P : Measure _)) / R k :=
            measure_ge_vagueCompactWindowMass_le K P (hRpos k).ne' (hRtop k).ne
          _ ≤ M k / R k := ENNReal.div_le_div_right (hMbound k P hP) _
          _ ≤ w k := hMtail k
      _ = δ := by
        rw [ENNReal.tsum_mul_left]
        have hgeom : (∑' k : ℕ, (1 / 2 : ℝ≥0∞) ^ (k + 1)) = 1 := by
          simp_rw [one_div]
          rw [ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two, inv_inv]
          have htwo0 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
          have htwotop : (2 : ℝ≥0∞) ≠ ∞ := by simp
          exact ENNReal.inv_mul_cancel htwo0 htwotop
        rw [hgeom, mul_one]
  refine ⟨closure A, hcompact, ?_⟩
  rintro P ⟨Q, hQ, rfl⟩
  have hsub : (closure A)ᶜ ⊆ Aᶜ := by
    intro μ hμ hA
    exact hμ (subset_closure hA)
  calc
    (Q : Measure (PositiveRadonMeasure X)) ((closure A)ᶜ) ≤ (Q : Measure _) (Aᶜ) :=
      measure_mono hsub
    _ ≤ δ := hbad Q hQ
    _ ≤ ε := hδε

end Critical2DKPZ.RandomMeasure

end
