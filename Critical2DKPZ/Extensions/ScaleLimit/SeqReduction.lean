/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Probability.CramerWold
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# Distributional convergence along positive real indices

Sequence reduction, Cramér–Wold, and invariance under equality of laws for
the real parameter used in the scale limit.
-/

public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

section Topological

variable {E Ω Ω' Ω'' : Type*} [TopologicalSpace E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MeasurableSpace Ω'']
  {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure Ω'} [IsProbabilityMeasure μ]
  {Q : Measure Ω''} [IsProbabilityMeasure Q]

/-- Positive-real distributional convergence can be tested on every divergent sequence. -/
theorem tendstoInDistribution_atTop_iff_forall_seq
    {X : Set.Ioi (0 : ℝ) → Ω → E} {Z : Ω' → E}
    (hX : ∀ L, AEMeasurable (X L) P) (hZ : AEMeasurable Z μ) :
    TendstoInDistribution X atTop Z (fun _ => P) μ ↔
      ∀ u : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (u n : ℝ)) atTop atTop →
        TendstoInDistribution (fun n => X (u n)) atTop Z (fun _ => P) μ := by
  constructor
  · intro h u hu
    exact ⟨fun n => hX (u n), hZ, h.tendsto.comp (tendsto_Ioi_atTop.mpr hu)⟩
  · intro h
    refine ⟨hX, hZ, tendsto_iff_seq_tendsto.mpr ?_⟩
    intro u hu
    exact (h u (tendsto_Ioi_atTop.mp hu)).tendsto

/-- Distributional convergence depends only on the laws, with measurability explicit. -/
theorem tendstoInDistribution_congr_of_map_eq
    {ι : Type*} {l : Filter ι} {X : ι → Ω → E} {Y : ι → Ω'' → E}
    {Z : Ω' → E} (hX : ∀ i, AEMeasurable (X i) P)
    (hY : ∀ i, AEMeasurable (Y i) Q) (hZ : AEMeasurable Z μ)
    (hmap : ∀ i, P.map (X i) = Q.map (Y i)) :
    TendstoInDistribution X l Z (fun _ => P) μ ↔
      TendstoInDistribution Y l Z (fun _ => Q) μ := by
  have hlaw : (fun i => (⟨P.map (X i), inferInstance⟩ : ProbabilityMeasure E)) =
      fun i => (⟨Q.map (Y i), inferInstance⟩ : ProbabilityMeasure E) := by
    funext i
    exact Subtype.ext (hmap i)
  constructor
  · intro h
    exact ⟨hY, hZ, hlaw ▸ h.tendsto⟩
  · intro h
    exact ⟨hX, hZ, hlaw.symm ▸ h.tendsto⟩

end Topological

section Inner

variable {E Ω Ω' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure Ω'} [IsProbabilityMeasure μ]

/-- Cramér–Wold for the positive-real scale parameter. -/
theorem tendstoInDistribution_atTop_iff_inner
    {X : Set.Ioi (0 : ℝ) → Ω → E} {Z : Ω' → E}
    (hX : ∀ L, AEMeasurable (X L) P) (hZ : AEMeasurable Z μ) :
    TendstoInDistribution X atTop Z (fun _ => P) μ ↔
      ∀ v : E, TendstoInDistribution (fun L ω => inner ℝ (X L ω) v)
        atTop (fun ω => inner ℝ (Z ω) v) (fun _ => P) μ := by
  constructor
  · intro h v
    exact h.continuous_comp (continuous_id.inner continuous_const)
  · intro h
    apply (tendstoInDistribution_atTop_iff_forall_seq hX hZ).mpr
    intro u hu
    apply (tendstoInDistribution_iff_tendstoInDistribution_inner hZ
      (fun n => hX (u n))).mpr
    intro v
    exact (tendstoInDistribution_atTop_iff_forall_seq
      (fun L => (h v).forall_aemeasurable L)
      (h v).aemeasurable_limit).mp (h v) u hu

end Inner

section Pi

variable {I Ω Ω' : Type*} [Fintype I]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure Ω'} [IsProbabilityMeasure μ]

/-- Cramér–Wold for finite coordinate families, with their product topology. -/
theorem tendstoInDistribution_atTop_iff_sum
    {X : Set.Ioi (0 : ℝ) → Ω → I → ℝ} {Z : Ω' → I → ℝ}
    (hX : ∀ L, AEMeasurable (X L) P) (hZ : AEMeasurable Z μ) :
    TendstoInDistribution X atTop Z (fun _ => P) μ ↔
      ∀ v : I → ℝ, TendstoInDistribution (fun L ω => ∑ i, X L ω i * v i)
        atTop (fun ω => ∑ i, Z ω i * v i) (fun _ => P) μ := by
  let : MeasurableSpace (EuclideanSpace ℝ I) := borel _
  let : BorelSpace (EuclideanSpace ℝ I) := ⟨rfl⟩
  let e : (I → ℝ) → EuclideanSpace ℝ I := WithLp.toLp 2
  have he : Continuous e := PiLp.continuous_toLp 2 _
  have hback : Continuous (WithLp.ofLp : EuclideanSpace ℝ I → I → ℝ) :=
    PiLp.continuous_ofLp 2 _
  constructor
  · intro h v
    have hv := ((tendstoInDistribution_atTop_iff_inner
      (fun L => he.measurable.comp_aemeasurable (hX L))
      (he.measurable.comp_aemeasurable hZ)).mp (h.continuous_comp he)) (e v)
    simpa only [Function.comp_apply, e, PiLp.inner_apply, RCLike.inner_apply,
      conj_trivial, WithLp.ofLp_toLp, mul_comm] using hv
  · intro h
    have hinner : TendstoInDistribution (fun L => e ∘ X L) atTop (e ∘ Z)
        (fun _ => P) μ := by
      apply (tendstoInDistribution_atTop_iff_inner
        (fun L => he.measurable.comp_aemeasurable (hX L))
        (he.measurable.comp_aemeasurable hZ)).mpr
      intro v
      simpa only [Function.comp_apply, e, PiLp.inner_apply, RCLike.inner_apply,
        conj_trivial, WithLp.ofLp_toLp, mul_comm] using h (WithLp.ofLp v)
    exact hinner.continuous_comp hback

end Pi

end Critical2DKPZ.Extensions.ScaleLimit
