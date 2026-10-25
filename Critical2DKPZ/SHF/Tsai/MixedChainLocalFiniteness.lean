/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedChainAbsoluteMoments
public import Critical2DKPZ.SHF.Tsai.ChainPairingMeasurability

/-! # Local finiteness after one heat-block replacement

Finite first absolute moments control endpoint rectangles containing each
compact exhaustion set. Their masses are finite almost surely, which gives
local finiteness of the literal heat-replaced chain.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A fixed deterministic heat replacement preserves measurability of a locally finite random chain. -/
theorem aemeasurable_chainProduct_update_heat {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (K j : ℕ) (τ : ℝ) (B : ℕ → Ω → Measure (Plane × Plane))
    (hBm : ∀ k ≤ K, Measurable (B k))
    (hBlf : ∀ k ≤ K, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (B k ω))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k)) :
    AEMeasurable (fun ω => chainProduct (Function.update (fun k => B k ω) j (heatBlock τ)) w K) P := by
  classical
  let C (k : ℕ) (ω : Ω) := Function.update (fun k => B k ω) j (heatBlock τ) k
  have hCm (k) (hk : k ≤ K) : Measurable (C k) := by
    by_cases hkj : k = j
    · subst k
      simpa only [C, Function.update_self] using
        (measurable_const : Measurable (fun _ : Ω => heatBlock τ))
    · simpa only [C, Function.update_of_ne hkj] using hBm k hk
  have hClf (k) (hk : k ≤ K) : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (C k ω) := by
    by_cases hkj : k = j
    · subst k
      filter_upwards with ω
      simpa only [C, Function.update_self] using locallyFinite_heatBlock τ
    · simpa only [C, Function.update_of_ne hkj] using hBlf k hk
  exact aemeasurable_chainProduct P K C hCm hClf w hw

/-- Replacing one time block by its heat mean preserves almost-sure local finiteness of the chain. -/
theorem ae_locallyFinite_chainProduct_update_heat {θ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (K j : ℕ) (hj : j ≤ K) (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k)
    (B : ℕ → Ω → Measure (Plane × Plane)) (hB : ∀ k ≤ K, HasDeltaBoseMoments θ (τ k) P (B k))
    (hind : iIndepFun (fun k : Fin (K + 1) => B k) P)
    (w : ℕ → ℕ → Plane → ℝ) (hw : ∀ k, IsL2ApplicableMollifier (w k)) (ℓ : ℕ) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K) := by
  classical
  let E := CompactExhaustion.choice (Plane × Plane)
  have hsmall (R : ℕ) : ∀ᵐ ω ∂P,
      chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K (E R) < ⊤ := by
    let A := Prod.fst '' E R
    let D := Prod.snd '' E R
    have hAc : IsCompact A := (E.isCompact R).image continuous_fst
    have hDc : IsCompact D := (E.isCompact R).image continuous_snd
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
    have hfinite := lintegral_prod_abs_mixedChainPairings_lt_top K j hj τ hτ B hB hind
      (n := 1) (by norm_num) (by norm_num) ∅ (fun _ => w) (fun _ => hw) ℓ
      (fun _ => g) (fun _ => g') (fun _ => hgm) (fun _ => hg'm) (fun _ => hg) (fun _ => hg')
    simp only [Fin.prod_univ_one, Finset.notMem_empty, ite_false] at hfinite
    simp_rw [htest] at hfinite
    have hm : AEMeasurable (fun ω => chainProduct (Function.update (fun k => B k ω) j (heatBlock (τ j))) (fun k => w k ℓ) K (A ×ˢ D)) P :=
      (Measure.measurable_coe (hAm.prod hDm)).comp_aemeasurable
        (aemeasurable_chainProduct_update_heat P K j (τ j) B
          (fun k hk => (hB k hk).1) (fun k hk => (hB k hk).2.1)
          _ (fun k => ((hw k).2.1 ℓ).measurable))
    filter_upwards [ae_lt_top' hm hfinite.ne] with ω hω
    apply lt_of_le_of_lt (measure_mono ?_) hω
    intro p hp
    exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
  filter_upwards [ae_all_iff.2 hsmall] with ω hω
  exact (RandomMeasure.locallyFinite_iff_finite_compactExhaustion E _).2 hω

end Critical2DKPZ.SHF.Tsai

end
