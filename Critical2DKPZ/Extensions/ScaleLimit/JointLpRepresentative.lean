/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # Jointly measurable representatives of continuous random fields

Countable spatial approximations with summable `L²` errors give a measurable
pointwise limit. Identification is for each fixed spatial point, as required
for a version of a stochastic process.
-/

public section
noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A continuous `L²`-valued planar map has a jointly measurable version. -/
theorem exists_jointlyMeasurable_Lp_version {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Plane → Lp ℝ 2 P) (hf : Continuous f) :
    ∃ F : Plane → Ω → ℝ, Measurable (Function.uncurry F) ∧
      ∀ y, F y =ᵐ[P] (f y : Ω → ℝ) := by
  classical
  let ε : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hsum : Summable ε := summable_geometric_of_abs_lt_one (by norm_num)
  have hex (k : ℕ) (y : Plane) : ∃ m : ℕ, dist (f (denseSeq Plane m)) (f y) < ε k :=
    (denseRange_denseSeq Plane).exists_mem_open
      (isOpen_lt (hf.dist continuous_const) continuous_const) ⟨y, by simpa using hε k⟩
  let N (k : ℕ) (y : Plane) : ℕ := Nat.find (hex k y)
  have hNm (k : ℕ) : Measurable (N k) := measurable_find (hex k)
    (fun m => (isOpen_lt (continuous_const.dist hf) continuous_const).measurableSet)
  let G (k : ℕ) (p : Plane × Ω) : ℝ := f (denseSeq Plane (N k p.1)) p.2
  have hGm (k : ℕ) : Measurable (G k) := by
    have hm : Measurable (fun p : ℕ × Ω => f (denseSeq Plane p.1) p.2) :=
      measurable_from_prod_countable_right (fun m => (Lp.stronglyMeasurable (f (denseSeq Plane m))).measurable)
    exact hm.comp ((hNm k).comp measurable_fst |>.prodMk measurable_snd)
  let F (y : Plane) (ω : Ω) : ℝ := limUnder atTop (fun k => G k (y, ω))
  refine ⟨F, (StronglyMeasurable.limUnder (fun k => (hGm k).stronglyMeasurable)).measurable, ?_⟩
  intro y
  have hbound (k : ℕ) : eLpNorm (fun ω => G k (y, ω) - f y ω) 1 P ≤ ENNReal.ofReal (ε k) := by
    apply (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    change eLpNorm ((f (denseSeq Plane (N k y)) : Ω → ℝ) - (f y : Ω → ℝ)) 2 P ≤ _
    rw [← eLpNorm_congr_ae (Lp.coeFn_sub (f (denseSeq Plane (N k y))) (f y)), ← Lp.enorm_def]
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact (show ‖f (denseSeq Plane (N k y)) - f y‖ < ε k by
      simpa only [N, dist_eq_norm] using Nat.find_spec (hex k y)).le
  have hsumE : (∑' k, eLpNorm (fun ω => G k (y, ω) - f y ω) 1 P) ≠ ∞ := by
    apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top : ENNReal.ofReal (∑' k, ε k) ≠ ∞)
    rw [ENNReal.ofReal_tsum_of_nonneg (fun k => (hε k).le) hsum]
    exact ENNReal.tsum_le_tsum hbound
  have hae : ∀ᵐ ω ∂P, Summable (fun k => ‖G k (y, ω) - f y ω‖) :=
    summable_norm_of_tsum_eLpNorm_ne_top le_rfl hsumE
  filter_upwards [hae] with ω hω
  have hz : Tendsto (fun k => G k (y, ω) - f y ω) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hω.tendsto_atTop_zero
  have hlim : Tendsto (fun k => G k (y, ω)) atTop (𝓝 (f y ω)) := by
    simpa only [sub_add_cancel, zero_add] using hz.add_const (f y ω)
  exact hlim.limUnder_eq

end Critical2DKPZ.Extensions.ScaleLimit
