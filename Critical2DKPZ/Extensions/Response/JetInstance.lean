/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.JetLimit
import Mathlib.Tactic

/-! # Compact jet limits for the positive smoothing filter

This module isolates the filter instances and the application of the
finite-difference Cauchy criterion and global measurable jet completeness.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Positive smoothing parameters tending down to zero, in the positive-real parameter space. -/
def responseScaleFilter : Filter (Set.Ioi (0 : ℝ)) :=
  Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi (0 : ℝ)))

instance responseScaleFilter_neBot : NeBot responseScaleFilter := by
  unfold responseScaleFilter
  exact (inferInstance : NeBot (𝓝[>] (0 : ℝ))).comap_of_range_mem
    (by simpa only [Subtype.range_coe] using self_mem_nhdsWithin)

instance responseScaleFilter_isCountablyGenerated : IsCountablyGenerated responseScaleFilter := by
  unfold responseScaleFilter
  infer_instance

/-- Inclusion of positive smoothing parameters tends to zero. -/
theorem tendsto_val_responseScaleFilter :
    Tendsto (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) responseScaleFilter (𝓝 0) :=
  tendsto_comap.mono_right nhdsWithin_le_nhds

/-- Every positive threshold eventually bounds the smoothing parameter. -/
theorem eventually_lt_responseScaleFilter (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : Set.Ioi (0 : ℝ) in responseScaleFilter, (r : ℝ) < ε :=
  tendsto_val_responseScaleFilter.eventually (Iio_mem_nhds hε)

/-- Convergence in `Lᵖ` implies Cauchyness along the product parameter filter. -/
theorem eLpNorm_cauchy_of_tendsto {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter ι) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : ι → Ω → ℝ) (g : Ω → ℝ)
    (hf : Tendsto (fun i => eLpNorm (f i - g) p P) l (𝓝 0)) :
    Tendsto (fun ij : ι × ι => eLpNorm (fun ω => f ij.1 ω - f ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0) := by
  have hsum := (hf.comp tendsto_fst).add (hf.comp tendsto_snd)
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun ij => ?_)
  have heq : (fun ω => f ij.1 ω - f ij.2 ω) = (f ij.1 - g) + -(f ij.2 - g) := by
    ext ω
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
    abel
  rw [heq]
  exact (eLpNorm_add_le hp).trans_eq (by rw [eLpNorm_neg]; rfl)

/-- Pointwise `Lᵖ` Cauchyness of a measurable bounded jet family gives one
measurable global limit with compact-uniform convergence for all finite exponents. -/
theorem exists_jet_limit_instance {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter ι) [NeBot l] [IsCountablyGenerated l]
    (J : ι → Ω → C(ℝ, Fin 3 → ℝ)) (A M B : ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hJm : ∀ i, Measurable (J i)) (hJd : ∀ i ω, JetData A M B (J i ω))
    (hpt : ∀ (q : ℝ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      ∀ ε > (0 : ℝ), ∃ s ∈ l, ∀ i ∈ s, ∀ j ∈ s,
        eLpNorm (fun ω => J i ω q 0 - J j ω q 0) p P < ENNReal.ofReal ε) :
    ∃ R : Ω → C(ℝ, Fin 3 → ℝ), Measurable R ∧
      ∀ a b : ℝ, a ≤ b → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
        MemLp (fun ω => restrictJet a b (R ω)) p P ∧
        Tendsto (fun i => eLpNorm (fun ω => restrictJet a b (J i ω) - restrictJet a b (R ω)) p P)
          l (𝓝 0) := by
  have hJdAE (i : ι) : ∀ᵐ ω ∂P, JetData A M B (J i ω) := Eventually.of_forall (hJd i)
  exact exists_jet_limit P l J A M B hA hM hB hJm hJdAE
    (jet_cauchy_Lp P l J A M B hA hM hB hJm hJdAE hpt)

end Critical2DKPZ.Extensions.Response
