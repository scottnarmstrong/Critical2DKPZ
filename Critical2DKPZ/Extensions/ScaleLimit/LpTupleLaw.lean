/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.StationaryLaw
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Passing finite-family laws through coordinatewise L² limits -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Assemble finitely many scalar L² classes into a vector class. -/
@[expose] def lpTuple (v : ι → Lp ℝ 2 P) : Lp (ι → ℝ) 2 P :=
  ∑ i, (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLp (v i)

omit [IsProbabilityMeasure P] in
/-- The vector class represents the tuple of the scalar representatives. -/
theorem lpTuple_coe (v : ι → Lp ℝ 2 P) :
    (lpTuple v : Ω → ι → ℝ) =ᵐ[P] fun ω i => v i ω := by
  have hs := Lp.coeFn_fun_finsetSum (Finset.univ : Finset ι)
    (fun i => (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLp (v i))
  have hi : ∀ᵐ ω ∂P, ∀ i, (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLp
      (v i) ω = ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i (v i ω) :=
    ae_all_iff.mpr fun i => ContinuousLinearMap.coeFn_compLp _ _
  filter_upwards [hs, hi] with ω hω hi
  rw [show lpTuple v ω = _ from hω]
  simp_rw [hi]
  ext j
  simp [ContinuousLinearMap.single_apply, Finset.sum_apply, Pi.single_apply]

omit [IsProbabilityMeasure P] in
/-- Coordinatewise L² limits yield convergence in probability of the complete finite tuple. -/
theorem tendstoInMeasure_lpTuple {v : ℕ → ι → Lp ℝ 2 P} {w : ι → Lp ℝ 2 P}
    (h : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (w i))) :
    TendstoInMeasure P (fun n ω i => v n i ω) atTop (fun ω i => w i ω) := by
  have ht : Tendsto (fun n => lpTuple (v n)) atTop (𝓝 (lpTuple w)) := by
    apply tendsto_finsetSum
    intro i _
    exact ((ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i).compLpL 2 P).continuous.continuousAt.tendsto.comp (h i)
  exact (tendstoInMeasure_of_tendsto_Lp ht).congr (fun n => lpTuple_coe (v n)) (lpTuple_coe w)

/-- Equality of finite-family laws survives coordinatewise L² convergence. -/
theorem identDistrib_lpTuple_limit {v u : ℕ → ι → Lp ℝ 2 P} {w q : ι → Lp ℝ 2 P}
    (hid : ∀ n, IdentDistrib (fun ω i => v n i ω) (fun ω i => u n i ω) P P)
    (hv : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (w i)))
    (hu : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (q i))) :
    IdentDistrib (fun ω i => w i ω) (fun ω i => q i ω) P P := by
  exact identDistrib_of_tendstoInMeasure hid (tendstoInMeasure_lpTuple hv)
    (tendstoInMeasure_lpTuple hu)
    (aemeasurable_pi_iff.mpr fun i => (Lp.stronglyMeasurable (w i)).aemeasurable)
    (aemeasurable_pi_iff.mpr fun i => (Lp.stronglyMeasurable (q i)).aemeasurable)

end Critical2DKPZ.Extensions.ScaleLimit
