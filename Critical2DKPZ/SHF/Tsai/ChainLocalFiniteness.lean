/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainAbsoluteMoments

/-! # Almost-sure local finiteness of finite mollified chains

Compact exhaustion sets lie in products of their compact endpoint projections.
Indicator tests of those projections are in `L²`; their finite positive first
moments make each covering rectangle finite almost surely. The canonical
compact-exhaustion criterion then gives local finiteness of the actual chain.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Finite chains with applicable connectors are locally finite almost surely. -/
theorem ae_locallyFinite_chainProduct {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K : ℕ) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (chainProduct (fun k => B k ω) (fun k => w k ℓ) K) := by
  classical
  let E := CompactExhaustion.choice (Plane × Plane)
  have hsmall (j : ℕ) : ∀ᵐ ω ∂P,
      chainProduct (fun k => B k ω) (fun k => w k ℓ) K (E j) < ⊤ := by
    let A := Prod.fst '' E j
    let D := Prod.snd '' E j
    have hAc : IsCompact A := (E.isCompact j).image continuous_fst
    have hDc : IsCompact D := (E.isCompact j).image continuous_snd
    have hAm : MeasurableSet A := hAc.isClosed.measurableSet
    have hDm : MeasurableSet D := hDc.isClosed.measurableSet
    let g : Plane → ℝ := A.indicator (fun _ => 1)
    let g' : Plane → ℝ := D.indicator (fun _ => 1)
    have hgm : Measurable g := measurable_const.indicator hAm
    have hg'm : Measurable g' := measurable_const.indicator hDm
    have hg : MemLp g 2 := memLp_indicator_const 2 hAm 1 (Or.inr hAc.measure_lt_top.ne)
    have hg' : MemLp g' 2 := memLp_indicator_const 2 hDm 1 (Or.inr hDc.measure_lt_top.ne)
    have htest (μ : Measure (Plane × Plane)) :
        (∫⁻ p, ENNReal.ofReal |g p.1| * ENNReal.ofReal |g' p.2| ∂μ) = μ (A ×ˢ D) := by
      rw [← lintegral_indicator_one (hAm.prod hDm)]
      apply lintegral_congr
      intro p
      by_cases ha : p.1 ∈ A <;> by_cases hd : p.2 ∈ D <;>
        simp [g, g', Set.indicator, ha, hd]
    have hfinite := lintegral_prod_abs_chainPairings_lt_top K τ hτ B hB hind
      (n := 1) (by norm_num) (by norm_num) (fun _ => w) (fun _ => hw) ℓ
      (fun _ => g) (fun _ => g') (fun _ => hgm) (fun _ => hg'm) (fun _ => hg) (fun _ => hg')
    simp only [Fin.prod_univ_one] at hfinite
    simp_rw [htest] at hfinite
    have hm : AEMeasurable (fun ω => chainProduct (fun k => B k ω) (fun k => w k ℓ) K (A ×ˢ D)) P :=
      (Measure.measurable_coe (hAm.prod hDm)).comp_aemeasurable
        (aemeasurable_chainProduct P K B (fun k hk => (hB k hk).1)
          (fun k hk => (hB k hk).2.1) _ (fun k => ((hw k).2.1 ℓ).measurable))
    filter_upwards [ae_lt_top' hm hfinite.ne] with ω hω
    apply lt_of_le_of_lt (measure_mono ?_) hω
    intro p hp
    exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  filter_upwards [ae_all_iff.2 hsmall] with ω hω
  exact (RandomMeasure.locallyFinite_iff_finite_compactExhaustion E _).2 hω

end Critical2DKPZ.SHF.Tsai

end
