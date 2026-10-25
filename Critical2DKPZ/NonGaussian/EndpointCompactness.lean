/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Critical2DKPZ.RandomMeasure.Compactness

/-! # Vague compactness for subprobability measures on the plane -/

@[expose] public section

open MeasureTheory Filter TopologicalSpace
open scoped CompactlySupported Topology

set_option linter.style.haveILetI false

namespace Critical2DKPZ.NonGaussian

/-- A sequence of measures on the plane with mass at most one has a vaguely
convergent subsequence whose limit also has mass at most one. -/
theorem exists_subseq_vague_tendsto (m : ℕ → Measure Plane)
    (hm : ∀ n, m n Set.univ ≤ 1) :
    ∃ (μ : Measure Plane) (φ : ℕ → ℕ), StrictMono φ ∧ IsFiniteMeasure μ ∧ μ Set.univ ≤ 1 ∧
      ∀ f : C_c(Plane, ℝ),
        Tendsto (fun n => ∫ y, f y ∂(m (φ n))) atTop
          (𝓝 (∫ y, f y ∂μ)) := by
  classical
  let K : CompactExhaustion Plane := RandomMeasure.vagueCompactExhaustion Plane
  have hfinite (n : ℕ) : IsFiniteMeasure (m n) := by
    refine ⟨?_⟩
    exact (hm n).trans_lt ENNReal.one_lt_top
  let mRadon : ℕ → RandomMeasure.PositiveRadonMeasure Plane := fun n => by
    letI : IsFiniteMeasure (m n) := hfinite n
    exact ⟨m n, inferInstance⟩
  have hmass (k : ℕ) : ∃ C : ℝ, ∀ n : ℕ,
      (mRadon n).measure.real (K k) ≤ C := by
    refine ⟨1, fun n => ?_⟩
    have hle : m n (K k) ≤ ENNReal.ofReal 1 := by
      exact (measure_mono (Set.subset_univ _)).trans (by simpa using hm n)
    have hreal : (m n (K k)).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal (by norm_num) hle
    simpa only [Measure.real_def] using hreal
  obtain ⟨φ, hφ, ν, hν⟩ :=
    RandomMeasure.exists_strictMono_subseq_vague_tendsto_of_localMassBound K mRadon hmass
  have hpair (f : C_c(Plane, ℝ)) :
      Tendsto (fun n => ∫ y, f y ∂(mRadon (φ n)).measure) atTop
        (𝓝 (∫ y, f y ∂ν.measure)) := by
    have h := (RandomMeasure.tendsto_vague_iff_forall_test
      (fun n => mRadon (φ n)) ν).mp hν f
    simpa only [RandomMeasure.vaguePairing] using h
  have hcutoff (k : ℕ) :
      ∫ y, RandomMeasure.vagueMassTest K k y ∂ν.measure ≤ 1 := by
    apply le_of_tendsto (hpair (RandomMeasure.vagueMassTest K k))
    filter_upwards [] with n
    let μn : RandomMeasure.PositiveRadonMeasure Plane := mRadon (φ n)
    have hpoint : ∀ y, RandomMeasure.vagueMassTest K k y ≤ 1 :=
      (RandomMeasure.vagueMassTest_spec K k).2.1
    have hi : Integrable (fun y : Plane => RandomMeasure.vagueMassTest K k y) μn.measure :=
      RandomMeasure.integrable_vagueTest μn (RandomMeasure.vagueMassTest K k)
    have hone : Integrable (fun _ : Plane => (1 : ℝ)) μn.measure := integrable_const 1
    have hmassReal : μn.measure.real Set.univ ≤ 1 := by
      have hle : μn.measure Set.univ ≤ ENNReal.ofReal 1 := by
        simpa [μn, RandomMeasure.PositiveRadonMeasure.measure, mRadon,
          ENNReal.ofReal_one] using hm (φ n)
      have hreal := ENNReal.toReal_le_of_le_ofReal (by norm_num) hle
      simpa only [Measure.real_def] using hreal
    calc
      ∫ y, RandomMeasure.vagueMassTest K k y ∂μn.measure ≤
          ∫ y, (1 : ℝ) ∂μn.measure :=
        integral_mono hi hone (fun y => hpoint y)
      _ = μn.measure.real Set.univ := by simp [Measure.real_def]
      _ ≤ 1 := hmassReal
  have hwindow (k : ℕ) : ν.measure (K k) ≤ ENNReal.ofReal 1 := by
    letI : IsLocallyFiniteMeasure ν.measure := ν.2
    have hreal : ν.measure.real (K k) ≤ 1 :=
      (RandomMeasure.vague_window_mass_le_test K ν k).trans (hcutoff k)
    have htop : ν.measure (K k) ≠ ⊤ := (K.isCompact k).measure_ne_top
    rw [Measure.real_def] at hreal
    rw [← ENNReal.ofReal_toReal htop]
    exact ENNReal.ofReal_le_ofReal hreal
  have hcover : (⋃ k, K k) = Set.univ := K.iUnion_eq
  have hKmono : Monotone (fun k => K k) := fun i j hij => K.subset hij
  have hmassUniv : ν.measure Set.univ ≤ ENNReal.ofReal 1 := by
    rw [← hcover, hKmono.measure_iUnion]
    exact iSup_le fun k => hwindow k
  have hfinν : IsFiniteMeasure ν.measure := ⟨(hmassUniv.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨ν.measure, φ, hφ, hfinν, ?_, ?_⟩
  · simpa only [ENNReal.ofReal_one] using hmassUniv
  · intro f
    exact hpair f

end Critical2DKPZ.NonGaussian

end
