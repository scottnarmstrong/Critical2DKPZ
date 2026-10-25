/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Transporting probability limits through a common input law

Measurable error events depend only on the input law. Thus probability
convergence to a measurable input function transfers between two realizations
of that law. Uniqueness identifies any other limit on the second realization.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Probability convergence of measurable real observables transfers across equality of input laws. -/
theorem tendstoInMeasure_comp_of_map_eq {Ω Ω' S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    (P : Measure Ω) (P' : Measure Ω') (X : Ω → S) (Y : Ω' → S)
    (hX : Measurable X) (hY : Measurable Y) (hLaw : P.map X = P'.map Y)
    (v : ℕ → S → ℝ) (hv : ∀ n, Measurable (v n)) (F : S → ℝ) (hF : Measurable F)
    (hconv : TendstoInMeasure P (fun n ω => v n (X ω)) atTop (F ∘ X)) :
    TendstoInMeasure P' (fun n ω => v n (Y ω)) atTop (F ∘ Y) := by
  rw [tendstoInMeasure_iff_dist] at hconv ⊢
  intro ε hε
  have hEvent (n : ℕ) :
      P {ω | ε ≤ dist (v n (X ω)) (F (X ω))} = P' {ω | ε ≤ dist (v n (Y ω)) (F (Y ω))} := by
    have hm : MeasurableSet {x | ε ≤ dist (v n x) (F x)} := measurableSet_le measurable_const ((hv n).dist hF)
    have h := congrArg (fun μ : Measure S => μ {x | ε ≤ dist (v n x) (F x)}) hLaw
    simpa only [Measure.map_apply hX hm, Measure.map_apply hY hm, Set.preimage_ofPred_eq] using h
  exact (hconv ε hε).congr hEvent

/-- A measurable input factor recovered on one realization also identifies a probability limit on any realization of the same input law. -/
theorem ae_eq_factor_of_map_eq_of_limits {Ω Ω' S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S]
    (P : Measure Ω) (P' : Measure Ω') (X : Ω → S) (Y : Ω' → S)
    (hX : Measurable X) (hY : Measurable Y) (hLaw : P.map X = P'.map Y)
    (v : ℕ → S → ℝ) (hv : ∀ n, Measurable (v n)) (φ : S → ℝ) (hφ : Measurable φ)
    (F : Ω → ℝ) (G : Ω' → ℝ) (hF : F =ᵐ[P] φ ∘ X)
    (hconvF : TendstoInMeasure P (fun n ω => v n (X ω)) atTop F)
    (hconvG : TendstoInMeasure P' (fun n ω => v n (Y ω)) atTop G) :
    G =ᵐ[P'] φ ∘ Y := by
  have hconvφ := tendstoInMeasure_comp_of_map_eq P P' X Y hX hY hLaw v hv φ hφ
    (hconvF.congr_right hF)
  exact tendstoInMeasure_ae_unique hconvG hconvφ

/-- Joint laws of approximation and target transport convergence in probability between realizations. -/
theorem tendstoInMeasure_of_pair_law_eq {Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) (P' : Measure Ω') (X : ℕ → Ω → E) (Y : Ω → E)
    (X' : ℕ → Ω' → E) (Y' : Ω' → E)
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hX' : ∀ n, AEMeasurable (X' n) P') (hY' : AEMeasurable Y' P')
    (hLaw : ∀ n, P.map (fun ω => (X n ω, Y ω)) = P'.map (fun ω => (X' n ω, Y' ω)))
    (hconv : TendstoInMeasure P' X' atTop Y') : TendstoInMeasure P X atTop Y := by
  rw [tendstoInMeasure_iff_dist] at hconv ⊢
  intro ε hε
  have hm : MeasurableSet {p : E × E | ε ≤ dist p.1 p.2} :=
    measurableSet_le measurable_const (measurable_fst.dist measurable_snd)
  have hEvent (n : ℕ) : P {ω | ε ≤ dist (X n ω) (Y ω)} = P' {ω | ε ≤ dist (X' n ω) (Y' ω)} := by
    have h := congrArg (fun ν : Measure (E × E) => ν {p | ε ≤ dist p.1 p.2}) (hLaw n)
    simpa only [Measure.map_apply_of_aemeasurable ((hX n).prodMk hY) hm,
      Measure.map_apply_of_aemeasurable ((hX' n).prodMk hY') hm, Set.preimage_ofPred_eq] using h
  exact (hconv ε hε).congr (fun n => (hEvent n).symm)

end Critical2DKPZ.SHF.Tsai

end
