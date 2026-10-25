/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralData

/-! # Passing finite-family laws to countable suprema -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Identical laws pass through almost sure limits, including extended-real limits. -/
theorem identDistrib_of_ae_tendsto {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] [HasOuterApproxClosed E] {f g : ℕ → Ω → E} {F G : Ω → E}
    (hid : ∀ n, IdentDistrib (f n) (g n) P P)
    (hf : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (F ω)))
    (hg : ∀ᵐ ω ∂P, Tendsto (fun n => g n ω) atTop (𝓝 (G ω)))
    (hF : AEMeasurable F P) (hG : AEMeasurable G P) : IdentDistrib F G P P := by
  have hfl := tendstoInDistribution_of_ae_tendsto
    (fun n => (hid n).aemeasurable_fst) hF hf
  have hgl := tendstoInDistribution_of_ae_tendsto
    (fun n => (hid n).aemeasurable_snd) hG hg
  have hfg : TendstoInDistribution f atTop G (fun _ => P) P := by
    refine ⟨fun n => (hid n).aemeasurable_fst, hG, ?_⟩
    exact hgl.tendsto.congr' (Eventually.of_forall fun n => Subtype.ext (hid n).map_eq.symm)
  exact ⟨hF, hG, tendstoInDistribution_unique f hfl hfg⟩

/-- Finite maxima along a surjective enumeration converge to the full supremum. -/
theorem tendsto_fin_iSup {ι : Type*} (e : ℕ → ι) (he : Function.Surjective e)
    (f : ι → ℝ≥0∞) :
    Tendsto (fun n => ⨆ i : Fin n, f (e i)) atTop (𝓝 (⨆ i, f i)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨i, hi⟩ := lt_iSup_iff.mp ha
    obtain ⟨k, hk⟩ := he i
    refine eventually_atTop.mpr ⟨k + 1, fun n hn => ?_⟩
    have hkn : k < n := by omega
    exact hi.trans_le (le_iSup_of_le (⟨k, hkn⟩ : Fin n) (by simpa only [hk] using (le_rfl : f i ≤ f i)))
  · intro a ha
    exact Eventually.of_forall fun n => (iSup_le fun i : Fin n => le_iSup f (e i)).trans_lt ha

/-- Equality of finite-family laws determines the law of a countable supremum. -/
theorem identDistrib_iSup_of_enumeration {ι : Type*} [Countable ι]
    (e : ℕ → ι) (he : Function.Surjective e) (f g : ι → Ω → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hid : ∀ (n : ℕ) (i : Fin n → ι),
      IdentDistrib (fun ω j => f (i j) ω) (fun ω j => g (i j) ω) P P) :
    IdentDistrib (fun ω => ⨆ i, f i ω) (fun ω => ⨆ i, g i ω) P P := by
  have hfinite (n : ℕ) : IdentDistrib (fun ω => ⨆ j : Fin n, f (e j) ω)
      (fun ω => ⨆ j : Fin n, g (e j) ω) P P :=
    (hid n (fun j => e j)).comp (Measurable.iSup fun j => measurable_pi_apply j)
  exact identDistrib_of_ae_tendsto hfinite
    (Eventually.of_forall fun ω => tendsto_fin_iSup e he (fun i => f i ω))
    (Eventually.of_forall fun ω => tendsto_fin_iSup e he (fun i => g i ω))
    (Measurable.iSup hf).aemeasurable (Measurable.iSup hg).aemeasurable

/-- Equality of finite-family laws determines a nonempty countable supremum. -/
theorem identDistrib_iSup {ι : Type*} [Countable ι] [Nonempty ι]
    (f g : ι → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hid : ∀ (n : ℕ) (i : Fin n → ι),
      IdentDistrib (fun ω j => f (i j) ω) (fun ω j => g (i j) ω) P P) :
    IdentDistrib (fun ω => ⨆ i, f i ω) (fun ω => ⨆ i, g i ω) P P := by
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  exact identDistrib_iSup_of_enumeration e he f g hf hg hid

end Critical2DKPZ.Extensions.ScaleLimit

end
