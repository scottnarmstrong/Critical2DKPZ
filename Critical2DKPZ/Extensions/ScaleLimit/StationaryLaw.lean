/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralData
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.Sequences

/-! # Stationary laws and continuity in mean

Finite-family stationarity implies one-point stationarity. Together with
continuity in probability and integrability, the latter gives continuity into
`L¹` by uniform integrability. Equality in law is closed under convergence in
probability, as required when passing from finite sums to ball averages.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Equality of laws is preserved when both sequences converge in probability. -/
theorem identDistrib_of_tendstoInMeasure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f g : ℕ → Ω → E} {F G : Ω → E}
    (hid : ∀ n, IdentDistrib (f n) (g n) P P)
    (hf : TendstoInMeasure P f atTop F) (hg : TendstoInMeasure P g atTop G)
    (hF : AEMeasurable F P) (hG : AEMeasurable G P) : IdentDistrib F G P P := by
  have hfl := hf.tendstoInDistribution_of_aemeasurable
    (fun n => (hid n).aemeasurable_fst) hF
  have hgl := hg.tendstoInDistribution_of_aemeasurable
    (fun n => (hid n).aemeasurable_snd) hG
  have hfg : TendstoInDistribution f atTop G (fun _ => P) P := by
    refine ⟨fun n => (hid n).aemeasurable_fst, hG, ?_⟩
    exact hgl.tendsto.congr' (Eventually.of_forall fun n => Subtype.ext (hid n).map_eq.symm)
  exact ⟨hF, hG, tendstoInDistribution_unique f hfl hfg⟩

omit [IsProbabilityMeasure P] in
/-- Projection of finite-family stationarity to a single spatial point. -/
theorem identDistrib_eval_zero {g : Plane → Ω → ℝ}
    (hstat : ∀ (n : ℕ) (y : Fin n → Plane) (z : Plane),
      IdentDistrib (fun ω i => g (y i + z) ω) (fun ω i => g (y i) ω) P P)
    (y : Plane) : IdentDistrib (g y) (g 0) P P := by
  have h := (hstat 1 (fun _ => 0) y).comp (measurable_pi_apply (0 : Fin 1))
  simpa only [Function.comp_def, zero_add] using h

/-- A sequence with a fixed integrable law that converges in probability
converges in mean. -/
theorem tendsto_eLpNorm_one_of_identDistrib {f : ℕ → Ω → ℝ} {g : Ω → ℝ}
    (hid : ∀ n, IdentDistrib (f n) g P P) (hg : Integrable g P)
    (hfg : TendstoInMeasure P f atTop g) :
    Tendsto (fun n => eLpNorm (f n - g) 1 P) atTop (𝓝 0) := by
  have hmem : ∀ n, MemLp (f n) 1 P :=
    fun n => (hid n).memLp_iff.mpr (memLp_one_iff_integrable.mpr hg)
  have hui := ProbabilityTheory.MemLp.uniformIntegrable_of_identDistrib (le_refl 1) (by norm_num) (hmem 0)
    (fun n => (hid n).trans (hid 0).symm)
  exact tendsto_Lp_finite_of_tendstoInMeasure (le_refl 1) (by norm_num)
    (fun n => (hmem n).aestronglyMeasurable) (memLp_one_iff_integrable.mpr hg)
    hui.unifIntegrable hfg

/-- The `L¹` class of an integrable field with stationary one-point laws. -/
@[expose] def stationaryL1 {g : Plane → Ω → ℝ}
    (hstat : ∀ y, IdentDistrib (g y) (g 0) P P) (hint : Integrable (g 0) P)
    (y : Plane) : Lp ℝ 1 P :=
  ((hstat y).memLp_iff.mpr (memLp_one_iff_integrable.mpr hint)).toLp (g y)

omit [IsProbabilityMeasure P] in
/-- The representative of the `L¹` class agrees almost everywhere with the field. -/
theorem stationaryL1_ae_eq {g : Plane → Ω → ℝ}
    (hstat : ∀ y, IdentDistrib (g y) (g 0) P P) (hint : Integrable (g 0) P)
    (y : Plane) : (stationaryL1 hstat hint y : Ω → ℝ) =ᵐ[P] g y :=
  MemLp.coeFn_toLp _

/-- Continuity in probability upgrades to continuity in `L¹` for a field with
one-point stationary, integrable laws. -/
theorem continuous_stationaryL1 {g : Plane → Ω → ℝ}
    (hstat : ∀ y, IdentDistrib (g y) (g 0) P P) (hint : Integrable (g 0) P)
    (hcont : ∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀)) :
    Continuous (stationaryL1 hstat hint) := by
  apply SeqContinuous.continuous
  intro s y hsy
  rw [tendsto_iff_edist_tendsto_0]
  have hy : Integrable (g y) P := (hstat y).integrable_iff.mpr hint
  have hh := tendsto_eLpNorm_one_of_identDistrib
    (fun n => (hstat (s n)).trans (hstat y).symm) hy ((hcont y).comp hsy)
  simpa only [stationaryL1, Function.comp_apply, Lp.edist_toLp_toLp] using hh

end Critical2DKPZ.Extensions.ScaleLimit

end
