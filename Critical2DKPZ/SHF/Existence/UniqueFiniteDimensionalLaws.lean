/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Existence.FiniteDimensionalLaws

/-! # Uniqueness of finite-dimensional laws -/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported Topology
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai

noncomputable section

namespace Critical2DKPZ.SHF.Existence

universe u v

/-- Approximate-flow estimates and dense-time uniqueness identify the joint compact and flat-marginal laws of any two
subsequential polymer limits on the same dense set. -/
theorem isPolymerSubseqLimit_fdd_eq_of (ϑ : ℝ) (hDenseSubseqLimitsInput : SubseqLimitsAreDense.{u} ϑ)
    (hDenseSubseqLimitsInput' : SubseqLimitsAreDense.{v} ϑ)
    (hT : DenseSHFUnique.{u, v} (ϑ - Real.eulerMascheroniConstant))
    (B : ℝ) (hB : 0 < B) (D : Set ℝ) (hD : D.Countable)
    (hDB : D ⊆ Set.Icc 0 B) (hdense : Set.Icc 0 B ⊆ closure D)
    {ψ ψ' : ℕ → ℕ} (hψ : StrictMono ψ) (hψ' : StrictMono ψ')
    {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω)
    (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    (hZ : IsPolymerSubseqLimit ϑ D ψ P Z) (hZ' : IsPolymerSubseqLimit ϑ D ψ' P' Z')
    (k : ℕ) (s t : Fin k → ℝ)
    (hst : ∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) :
    P.map (fun ω i => (Z (s i) (t i) ω, (Z (s i) (t i) ω).map Prod.fst)) =
      P'.map (fun ω i => (Z' (s i) (t i) ω, (Z' (s i) (t i) ω).map Prod.fst)) := by
  let hDense : IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P Z :=
    hDenseSubseqLimitsInput D hD (fun x hx => (hDB hx).1) ψ hψ P Z hZ
  let hDense' : IsDenseSHF (ϑ - Real.eulerMascheroniConstant) D P' Z' :=
    hDenseSubseqLimitsInput' D hD (fun x hx => (hDB hx).1) ψ' hψ' P' Z' hZ'
  have hlaw := hT B hB D hDB hdense P P' Z Z' hDense hDense' k s t hst
  let G : (Fin k → Measure (Plane × Plane)) →
      Fin k → Measure (Plane × Plane) × Measure Plane := fun m i =>
        (m i, Measure.map Prod.fst (m i))
  have hG : Measurable G := by
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply i).prodMk
      ((Measure.measurable_map Prod.fst measurable_fst).comp (measurable_pi_apply i))
  have hZvec : Measurable (fun ω i => Z (s i) (t i) ω) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hDense.1 (s i) (hst i).1 (t i) (hst i).2.1 (hst i).2.2).1
  have hZ'vec : Measurable (fun ω i => Z' (s i) (t i) ω) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hDense'.1 (s i) (hst i).1 (t i) (hst i).2.1 (hst i).2.2).1
  calc
    P.map (fun ω i => (Z (s i) (t i) ω, (Z (s i) (t i) ω).map Prod.fst)) =
        (P.map (fun ω i => Z (s i) (t i) ω)).map G := by
          rw [Measure.map_map hG hZvec]
          rfl
    _ = (P'.map (fun ω i => Z' (s i) (t i) ω)).map G := by rw [hlaw]
    _ = P'.map (fun ω i => (Z' (s i) (t i) ω, (Z' (s i) (t i) ω).map Prod.fst)) := by
          rw [Measure.map_map hG hZ'vec]
          rfl


end Critical2DKPZ.SHF.Existence

end
