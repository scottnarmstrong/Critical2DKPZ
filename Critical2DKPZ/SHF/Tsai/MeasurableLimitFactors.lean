/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! # Measurable factors of limits in measure

A limit in measure of measurable functions of a common input is almost everywhere a measurable
function of that input. A measurable embedding into countably many real coordinates gives the
same conclusion for limits valued in the embedded space.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- A real limit in measure of measurable functions of a common input is almost everywhere a measurable function of that input. -/
theorem exists_measurable_factor_of_tendstoInMeasure {Ω S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] (P : Measure Ω)
    (X : Ω → S) (F : Ω → ℝ) (v : ℕ → S → ℝ) (hv : ∀ n, Measurable (v n))
    (hconv : TendstoInMeasure P (fun n ω => v n (X ω)) atTop F) :
    ∃ φ : S → ℝ, Measurable φ ∧ F =ᵐ[P] φ ∘ X := by
  obtain ⟨ns, _hns, hAE⟩ := hconv.exists_seq_tendsto_ae
  let φ (x : S) := limUnder atTop (fun n => v (ns n) x)
  have hφ : StronglyMeasurable φ := StronglyMeasurable.limUnder (fun n => (hv (ns n)).stronglyMeasurable)
  refine ⟨φ, hφ.measurable, ?_⟩
  filter_upwards [hAE] with ω hω
  exact hω.limUnder_eq.symm

/-- A measurable embedding into countably many real coordinates recovers a measurable factor from coordinatewise limits in measure. -/
theorem exists_measurable_factor_of_coordinate_limits {Ω S E ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace E] [Nonempty E] [Countable ι]
    (P : Measure Ω) (X : Ω → S) (F : Ω → E) (e : E → ι → ℝ) (he : MeasurableEmbedding e)
    (v : ι → ℕ → S → ℝ) (hv : ∀ i n, Measurable (v i n))
    (hconv : ∀ i, TendstoInMeasure P (fun n ω => v i n (X ω)) atTop (fun ω => e (F ω) i)) :
    ∃ φ : S → E, Measurable φ ∧ F =ᵐ[P] φ ∘ X := by
  classical
  choose f hfm hfAE using fun i =>
    exists_measurable_factor_of_tendstoInMeasure P X (fun ω => e (F ω) i) (v i) (hv i) (hconv i)
  let Φ (x : S) (i : ι) := f i x
  have hΦ : Measurable Φ := Measurable.of_eval hfm
  refine ⟨he.invFun ∘ Φ, he.measurable_invFun.comp hΦ, ?_⟩
  filter_upwards [ae_all_iff.2 hfAE] with ω hω
  have hread : Φ (X ω) = e (F ω) := by
    funext i
    exact (hω i).symm
  change F ω = he.invFun (Φ (X ω))
  rw [hread, he.leftInverse_invFun]

end Critical2DKPZ.SHF.Tsai

end
