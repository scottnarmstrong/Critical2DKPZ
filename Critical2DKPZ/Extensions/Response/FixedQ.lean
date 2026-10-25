/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Critical2DKPZ.Extensions.Response.FixedQLimit
public import Critical2DKPZ.Extensions.Response.CutoffJets
public import Critical2DKPZ.Extensions.Response.JetInstance
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

/-! # Bounded convergence in measure for response evaluations

The generic result is stated for arbitrary nonbottom countably generated filters.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.Response

/-- An almost surely uniformly bounded family is uniformly integrable at every
finite exponent at least one. -/
theorem unifIntegrable_of_ae_bound {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : ι → Ω → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) P) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ i, ∀ᵐ ω ∂P, |f i ω| ≤ K) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    UnifIntegrable f p P := by
  apply unifIntegrable_of hp hp' hf
  intro ε _hε
  let C : ℝ≥0 := ⟨K + 1, by linarith⟩
  have hCK : K < (C : ℝ) := lt_add_of_pos_right K zero_lt_one
  refine ⟨C, fun i => ?_⟩
  have hcut : ({ω | C ≤ ‖f i ω‖₊}.indicator (f i)) =ᵐ[P] fun _ => 0 := by
    filter_upwards [hb i] with ω hω
    have hnot : ω ∉ {ω | C ≤ ‖f i ω‖₊} := by
      intro hmem
      have hh : (C : ℝ) ≤ ‖f i ω‖ := by exact_mod_cast hmem
      have hh' : ‖f i ω‖ ≤ K := hω
      linarith only [hh, hh', hCK]
    exact Set.indicator_of_notMem hnot _
  rw [eLpNorm_congr_ae hcut]
  change eLpNorm (0 : Ω → ℝ) p P ≤ ε
  rw [eLpNorm_zero]
  exact bot_le

/-- A bounded family converging in measure has the same bound at its limit and
converges in every finite `Lᵖ`, along any countably generated nonbottom filter. -/
theorem tendsto_eLpNorm_of_tendstoInMeasure_of_bounded {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter ι) [NeBot l] [IsCountablyGenerated l]
    {f : ι → Ω → ℝ} {g : Ω → ℝ} {K : ℝ}
    (hf : ∀ i, AEStronglyMeasurable (f i) P)
    (hb : ∀ i, ∀ᵐ ω ∂P, |f i ω| ≤ K) (hconv : TendstoInMeasure P f l g)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    (∀ᵐ ω ∂P, |g ω| ≤ K) ∧ MemLp g p P ∧
      Tendsto (fun i => eLpNorm (f i - g) p P) l (𝓝 0) := by
  obtain ⟨ns, _hns, hlim⟩ := hconv.exists_seq_tendsto_ae'
  have hK : 0 ≤ K := by
    obtain ⟨ω, hω⟩ := (hb (ns 0)).exists
    exact (abs_nonneg _).trans hω
  have hgb : ∀ᵐ ω ∂P, |g ω| ≤ K := by
    filter_upwards [hlim, ae_all_iff.mpr (fun n => hb (ns n))] with ω hω hbω
    exact le_of_tendsto hω.abs (Eventually.of_forall hbω)
  have hgm : AEStronglyMeasurable g P := TendstoInMeasure.aestronglyMeasurable hf hconv
  have hg : MemLp g p P := MemLp.of_bound hgm K hgb
  have hmem (i : ι) : MemLp (f i) p P := MemLp.of_bound (hf i) K (hb i)
  refine ⟨hgb, hg, ?_⟩
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro u hu
  have hUI := unifIntegrable_of_ae_bound P (fun n => f (u n)) (fun n => hf (u n)) K hK
    (fun n => hb (u n)) p hp hp'
  exact (tendstoInMeasure_iff_tendsto_Lp_finite hp hp' (fun n => hmem (u n)) hg).mp
    ⟨hconv.comp hu, hUI⟩

/-- Fixed-parameter convergence in probability upgrades to convergence in
every finite `Lᵖ`; the same deterministic bound holds for the limiting field difference. -/
theorem fixed_q_Lp (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h v : Plane →ᵇ ℝ) (ψ : TestFn) (q : ℝ)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
    (∀ᵐ ω ∂P, |H t (h + q • v) ω ψ - H t h ω ψ| ≤ (∫ x, |ψ x|) * ‖v‖ * |q|) ∧
    MemLp (fun ω => H t (h + q • v) ω ψ - H t h ω ψ) p P ∧
    Tendsto (fun r : Set.Ioi (0 : ℝ) => eLpNorm
      (fun ω => responseCutoff Z t r h v ψ ω q - (H t (h + q • v) ω ψ - H t h ω ψ)) p P)
      responseScaleFilter (𝓝 0) := by
  have hconv := (responseCutoff_tendstoInMeasure ϑ P Z hZ H hH t ht h v ψ q).comp
    (show Tendsto (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) responseScaleFilter (𝓝[>] 0) from tendsto_comap)
  exact tendsto_eLpNorm_of_tendstoInMeasure_of_bounded P responseScaleFilter
    (f := fun r ω => responseCutoff Z t r h v ψ ω q)
    (fun r => (aemeasurable_responseCutoff ϑ P Z hZ ht r.property h v ψ q).aestronglyMeasurable)
    (fun r => (responseCutoff_bounds ϑ P Z hZ t r ht r.property h v ψ).mono
      (fun _ hω => (hω q).1)) hconv hp hp'

end Critical2DKPZ.Extensions.Response
