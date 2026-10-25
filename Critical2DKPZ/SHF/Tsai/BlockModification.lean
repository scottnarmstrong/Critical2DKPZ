/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockMoments
public import Critical2DKPZ.SHF.Tsai.ChainMeasurability
public import Critical2DKPZ.RandomMeasure.GeneralRandom

/-! # Locally finite modifications of moment blocks

The stochastic axioms give local finiteness almost surely. The canonical
random-measure modification makes it hold everywhere, retaining the moments,
independence and each finite endpoint chain almost surely.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.RandomMeasure

namespace Critical2DKPZ.SHF.Tsai

/-- Measurable almost-sure modifications preserve the complete block moment predicate. -/
theorem HasDeltaBoseMoments.congr {θ τ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B B' : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B)
    (hm : Measurable B') (heq : B =ᵐ[P] B') : HasDeltaBoseMoments θ τ P B' := by
  refine ⟨hm, ?_, ?_⟩
  · filter_upwards [hB.2.1, heq] with ω hω hωeq
    rw [← hωeq]
    exact hω
  · intro n hn1 hn g g' hg hg'
    obtain ⟨hI, hint, hmoment⟩ := hB.2.2 n hn1 hn g g' hg hg'
    have hprod : (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂B ω) =ᵐ[P]
        fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂B' ω := by
      filter_upwards [heq] with ω hω
      rw [hω]
    refine ⟨?_, hint.congr hprod, (integral_congr_ae hprod).symm.trans hmoment⟩
    filter_upwards [hI, heq] with ω hω hωeq
    rw [← hωeq]
    exact hω

/-- The canonical everywhere locally finite modification retains all delta-Bose moments. -/
theorem HasDeltaBoseMoments.locallyFiniteMeasureModification {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {B : Ω → Measure (Plane × Plane)}
    (hB : HasDeltaBoseMoments θ τ P B) (K : CompactExhaustion (Plane × Plane)) :
    HasDeltaBoseMoments θ τ P (RandomMeasure.locallyFiniteMeasureModification K B) := by
  have hm : Measurable (RandomMeasure.locallyFiniteMeasureModification K B) := by
    classical
    exact Measurable.ite (measurableSet_locallyFiniteEvent K B hB.1) hB.1 measurable_const
  have heq : RandomMeasure.locallyFiniteMeasureModification K B =ᵐ[P] B :=
    ae_eq_radonValuedModification K P B hB.2.1
  exact hB.congr hm heq.symm

/-- Almost-sure blockwise equality gives almost-sure equality of the literal finite chains. -/
theorem chainProduct_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (K : ℕ)
    (B B' : ℕ → Ω → Measure (Plane × Plane)) (heq : ∀ k ≤ K, B k =ᵐ[P] B' k)
    (w : ℕ → Plane → ℝ) :
    (fun ω => chainProduct (fun k => B k ω) w K) =ᵐ[P]
      fun ω => chainProduct (fun k => B' k ω) w K := by
  have hprefix : ∀ᵐ ω ∂P, ∀ k ≤ K, B k ω = B' k ω :=
    ae_all_iff.2 fun k => ae_all_iff.2 fun hk => heq k hk
  filter_upwards [hprefix] with ω hω
  exact chainProduct_congr_prefix K _ _ hω w


end Critical2DKPZ.SHF.Tsai

end
