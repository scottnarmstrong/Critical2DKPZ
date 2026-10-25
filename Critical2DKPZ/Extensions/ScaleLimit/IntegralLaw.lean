/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.StationaryLaw
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Passing finite-family laws through integration

Approximate a pair of `L¹`-valued functions by simple functions with values
in their joint range. Each approximating integral is a finite linear
combination of evaluations, and equality in law is closed under `L¹` limits.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The pairs of `L¹` random variables with equal laws form a closed set. -/
theorem isClosed_identDistrib_L1 :
    IsClosed {p : Lp E 1 P × Lp E 1 P |
      IdentDistrib (p.1 : Ω → E) (p.2 : Ω → E) P P} := by
  apply IsSeqClosed.isClosed
  intro s p hs hsp
  have hf : Tendsto (fun n => (s n).1) atTop (𝓝 p.1) :=
    continuous_fst.continuousAt.tendsto.comp hsp
  have hg : Tendsto (fun n => (s n).2) atTop (𝓝 p.2) :=
    continuous_snd.continuousAt.tendsto.comp hsp
  exact identDistrib_of_tendstoInMeasure hs
    (tendstoInMeasure_of_tendsto_Lp hf) (tendstoInMeasure_of_tendsto_Lp hg)
    (Lp.aestronglyMeasurable p.1).aemeasurable (Lp.aestronglyMeasurable p.2).aemeasurable

omit [IsProbabilityMeasure P] [CompleteSpace E] in
/-- Finite-dimensional laws determine laws of finite linear combinations. -/
theorem identDistrib_L1_linearCombination {ι : Type*} [Fintype ι]
    (F G : ι → Lp E 1 P) (c : ι → ℝ)
    (hid : IdentDistrib (fun ω i => F i ω) (fun ω i => G i ω) P P) :
    IdentDistrib ((∑ i, c i • F i : Lp E 1 P) : Ω → E)
      ((∑ i, c i • G i : Lp E 1 P) : Ω → E) P P := by
  classical
  have hm : Measurable (fun z : ι → E => ∑ i, c i • z i) := by fun_prop
  have hh := hid.comp hm
  have hae (H : ι → Lp E 1 P) :
      ((∑ i, c i • H i : Lp E 1 P) : Ω → E) =ᵐ[P] fun ω => ∑ i, c i • H i ω := by
    apply (Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • H i)).trans
    filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (H i))] with ω hω
    exact Finset.sum_congr rfl (fun i _ => hω i)
  exact (IdentDistrib.of_ae_eq (Lp.aestronglyMeasurable _).aemeasurable (hae F)).trans
    (hh.trans (IdentDistrib.of_ae_eq (Lp.aestronglyMeasurable _).aemeasurable (hae G)).symm)

omit [IsProbabilityMeasure P] [NormedSpace ℝ E] [CompleteSpace E]
  [BorelSpace E] [SecondCountableTopology E] in
/-- Finite-family laws indexed by `Fin` can be used on any finite index type. -/
theorem identDistrib_L1_family {α : Type*} (F G : α → Lp E 1 P)
    (hid : ∀ (n : ℕ) (y : Fin n → α),
      IdentDistrib (fun ω i => F (y i) ω) (fun ω i => G (y i) ω) P P)
    {ι : Type*} [Fintype ι] (y : ι → α) :
    IdentDistrib (fun ω i => F (y i) ω) (fun ω i => G (y i) ω) P P := by
  let e := Fintype.equivFin ι
  have hh := (hid (Fintype.card ι) (fun i => y (e.symm i))).comp
    (show Measurable (fun z : Fin (Fintype.card ι) → E => fun i => z (e i)) by fun_prop)
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using hh

/-- Integrating `L¹`-valued fields preserves identical finite-family laws. -/
theorem identDistrib_integral_L1 {α : Type*} [MeasurableSpace α] [Nonempty α]
    (μ : Measure α) [IsFiniteMeasure μ] (F G : α → Lp E 1 P)
    (hF : StronglyMeasurable F) (hG : StronglyMeasurable G)
    (hFi : Integrable F μ) (hGi : Integrable G μ)
    (hid : ∀ (n : ℕ) (y : Fin n → α),
      IdentDistrib (fun ω i => F (y i) ω) (fun ω i => G (y i) ω) P P) :
    IdentDistrib ((∫ y, F y ∂μ : Lp E 1 P) : Ω → E)
      ((∫ y, G y ∂μ : Lp E 1 P) : Ω → E) P P := by
  classical
  borelize (Lp E 1 P × Lp E 1 P)
  let H : α → Lp E 1 P × Lp E 1 P := fun y => (F y, G y)
  have hH : StronglyMeasurable H := hF.prodMk hG
  have hHi : Integrable H μ := hFi.prodMk hGi
  let y₀ : α := Classical.ofNonempty
  have h₀ : H y₀ ∈ range H := mem_range_self _
  let : TopologicalSpace.SeparableSpace (range H) := hH.isSeparable_range.separableSpace
  let S := SimpleFunc.approxOn H hH.measurable (range H) (H y₀) h₀
  have ht : Tendsto (fun n => (S n).integral μ) atTop (𝓝 (∫ y, H y ∂μ)) :=
    tendsto_integral_approxOn_of_measurable hHi hH.measurable
      (Eventually.of_forall fun y => subset_closure (mem_range_self y)) h₀ (integrable_const _)
  have he (n : ℕ) : IdentDistrib (((S n).integral μ).1 : Ω → E)
      (((S n).integral μ).2 : Ω → E) P P := by
    have hex (b : (S n).range) : ∃ y : α, H y = b.1 := by
      obtain ⟨a, ha⟩ := (S n).mem_range.mp b.2
      have hb := SimpleFunc.approxOn_mem hH.measurable h₀ n a
      change (S n) a ∈ range H at hb
      rwa [ha] at hb
    choose y hy using hex
    let c (b : (S n).range) : ℝ := μ.real ((S n) ⁻¹' {b.1})
    have heq : (S n).integral μ = ∑ b : (S n).range, c b • H (y b) := by
      rw [SimpleFunc.integral_eq, ← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro b _
      rw [hy b]
    have hh := identDistrib_L1_linearCombination (fun b => F (y b))
      (fun b => G (y b)) c (identDistrib_L1_family F G hid y)
    simpa only [heq, H, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd] using hh
  have hh := isClosed_identDistrib_L1.mem_of_tendsto ht (Eventually.of_forall he)
  rwa [integral_pair hFi hGi] at hh

end Critical2DKPZ.Extensions.ScaleLimit

end
