/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.ClosedCarrier
public import Critical2DKPZ.Analysis.Sobolev.ExpectedHeatEnergy
public import Critical2DKPZ.Definitions.LocNegSobolevTopBorelSpace
public import Critical2DKPZ.Definitions.ToLocNegSobolevTuple
public import Mathlib.Topology.Bases

/-! Distributions with finite local negative Sobolev energy carry the topology induced by the extended-energy space and its Borel sigma algebra. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.Analysis.Sobolev

/-- Distributions with finite local negative Sobolev energy of order `s`. -/
abbrev LocNegSobolevCarrier (s : ℝ) :=
  {T : Critical2DKPZ.LocNegSobolevTop s //
    Critical2DKPZ.MemLocalNegSobolev s T.toDistr}




/-- On a second-countable finite-energy carrier, testwise measurability implies measurability of a distribution family. -/
theorem measurable_locNegSobolevCarrier_of_testwise
    {Ω : Type*} [MeasurableSpace Ω] {s : ℝ} (T : Ω → Critical2DKPZ.Distr)
    (hT : ∀ φ : Critical2DKPZ.TestFn, Measurable fun ω => T ω φ)
    [SecondCountableTopology (LocNegSobolevCarrier s)]
    (hmem : ∀ ω, Critical2DKPZ.MemLocalNegSobolev s (T ω)) :
    Measurable fun ω => (⟨T ω, hmem ω⟩ : LocNegSobolevCarrier s) := by
  let f : Ω → LocNegSobolevCarrier s := fun ω => ⟨T ω, hmem ω⟩
  apply measurable_of_isOpen
  intro U hU
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  rw [← hVU]
  have hpre (V : Set (Critical2DKPZ.LocNegSobolevTop s))
      (hV : IsOpen V) :
      MeasurableSet (f ⁻¹' (Subtype.val ⁻¹' V)) := by
    induction hV with
    | basic V hgen =>
        change ∃ (U : Critical2DKPZ.Distr) (χ : Critical2DKPZ.TestFn)
          (ε : ℝ≥0∞), 0 < ε ∧
            V = {S : Critical2DKPZ.LocNegSobolevTop s |
              Critical2DKPZ.localNegSobolevSq s (S.toDistr - U) χ < ε} at hgen
        obtain ⟨U, χ, ε, hε, rfl⟩ := hgen
        have henergy : Measurable fun ω =>
            Critical2DKPZ.localNegSobolevSq s (T ω - U) χ := by
          apply Critical2DKPZ.measurable_localNegSobolevSq
          intro φ
          exact (hT φ).sub_const (U φ)
        change MeasurableSet {ω |
          Critical2DKPZ.localNegSobolevSq s (T ω - U) χ < ε}
        exact measurableSet_lt henergy measurable_const
    | univ => simp
    | inter _ _ _ _ hV hW => exact hV.inter hW
    | sUnion S hS ih =>
        let W : (↑S) → Set (LocNegSobolevCarrier s) :=
          fun V => Subtype.val ⁻¹' (V.1)
        have hW : ∀ V, IsOpen (W V) := fun V => isOpen_induced (hS V.1 V.2)
        obtain ⟨A, hAcnt, hAeq⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
        have hcount : MeasurableSet (⋃ V : A, f ⁻¹' W V.1) :=
          @MeasurableSet.iUnion Ω A inferInstance hAcnt.to_subtype _
            (fun V => ih V.1.1 V.1.2)
        have hcover : (⋃ V : A, W V.1) = Subtype.val ⁻¹' (⋃₀ S) := by
          calc
            (⋃ V : A, W V.1) = ⋃ V ∈ A, W V := by
              ext x
              simp
            _ = ⋃ V : (↑S), W V := hAeq
            _ = Subtype.val ⁻¹' (⋃₀ S) := by
              ext x
              simp [W]
        have hpreEq : f ⁻¹' (Subtype.val ⁻¹' (⋃₀ S)) =
            ⋃ V : A, f ⁻¹' W V.1 := by
          rw [← hcover]
          simp only [Set.preimage_iUnion]
        rw [hpreEq]
        exact hcount
  exact hpre V hV


/-- The coordinatewise inclusion of finite-energy distributions into the ambient distribution space. -/
def locNegSobolevCarrierTupleToFrozen (s : ℝ) {k : ℕ}
    (T : Fin k → LocNegSobolevCarrier s) :
    Critical2DKPZ.LocNegSobolevTuple s k := fun i => (T i).1

/-- The inclusion of a finite-energy tuple into the product local Sobolev space is continuous. -/
theorem continuous_locNegSobolevCarrierTupleToFrozen (s : ℝ) {k : ℕ} :
    Continuous (locNegSobolevCarrierTupleToFrozen s (k := k)) := by
  apply continuous_pi
  intro i
  exact continuous_subtype_val.comp (continuous_apply i)




end Critical2DKPZ.Analysis.Sobolev

end
