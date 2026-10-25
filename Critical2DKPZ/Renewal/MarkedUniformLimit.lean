/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.MarkedLimit
public import Critical2DKPZ.Renewal.LocalBounds
import Critical2DKPZ.Renewal.MonotoneUniform

/-!
# Locally uniform marked renewal convergence

The marked profile is increasing in the critical parameter and in time. Joint
continuity of the scalar density upgrades its pointwise limit to uniform convergence
on every compact set of critical parameters and strictly positive times.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Uniformity

namespace Critical2DKPZ.Renewal

/-- The marked cumulative renewal profile on the macroscopic time scale. -/
def criticalMarkedProfile (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  markedRenewalFunction (fun r => criticalSigmaSq p.1 N * returnWeight r)
    ⌊((N : ℝ) + 1) * p.2⌋₊ / (Real.log N) ^ 2

/-- The marked limiting density is continuous at positive times. -/
theorem continuousAt_markedDensity {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt (fun q : ℝ × ℝ => q.2 * DeltaBose.scalarDensity
      (q.1 - Real.eulerMascheroniConstant) q.2) p := by
  have hc : ContinuousAt (fun q : ℝ × ℝ => DeltaBose.scalarDensity q.1 q.2)
      (p.1 - Real.eulerMascheroniConstant, p.2) :=
    DeltaBose.continuousOn_scalarDensity.continuousAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds
        (show (0 : ℝ) < (p.1 - Real.eulerMascheroniConstant, p.2).2 from hp))
  have hcomp : ContinuousAt
      (fun q : ℝ × ℝ => DeltaBose.scalarDensity
        (q.1 - Real.eulerMascheroniConstant) q.2) p :=
    hc.comp₂ (continuous_fst.sub continuous_const).continuousAt continuous_snd.continuousAt
  exact continuous_snd.continuousAt.mul hcomp

/-- Marked critical renewal profiles converge along jointly moving parameters and times. -/
theorem tendsto_joint_criticalMarkedProfile {p : ℝ × ℝ} (hp : 0 < p.2) :
    Tendsto (fun z : ℕ × (ℝ × ℝ) => criticalMarkedProfile z.1 z.2)
      (atTop ×ˢ nhds p)
      (nhds (p.2 * DeltaBose.scalarDensity (p.1 - Real.eulerMascheroniConstant) p.2)) := by
  let K : Set (ℝ × ℝ) := Icc (p.1 - 1) (p.1 + 1) ×ˢ Icc (p.2 / 2) (p.2 + 1)
  have hK : K ∈ nhds p := by
    rw [nhds_prod_eq]
    exact Filter.mem_prod_iff.mpr ⟨_, Icc_mem_nhds (by linarith) (by linarith),
      _, Icc_mem_nhds (by linarith only [hp]) (by linarith), fun _ h => h⟩
  apply tendsto_joint_of_eventually_monotone hK _ _ (continuousAt_markedDensity hp)
  · filter_upwards [criticalSigmaSq_eventually_pos (p.1 - 1), eventually_ge_atTop 2] with N hσ hN
    intro x hx y hy hxy
    have hwx : ∀ r, 0 ≤ criticalSigmaSq x.1 N * returnWeight r := fun r =>
      mul_nonneg ((hσ.le).trans (criticalSigmaSq_mono_parameter hN hx.1.1)) (srwKernel_nonneg _ _)
    have hxyw : ∀ r, criticalSigmaSq x.1 N * returnWeight r ≤
        criticalSigmaSq y.1 N * returnWeight r := fun r =>
      mul_le_mul_of_nonneg_right (criticalSigmaSq_mono_parameter hN hxy.1) (srwKernel_nonneg _ _)
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply (markedRenewalFunction_mono_kernel hwx hxyw _).trans
    apply markedRenewalFunction_mono_time
      (fun r => mul_nonneg ((hσ.le).trans (criticalSigmaSq_mono_parameter hN hy.1.1))
        (srwKernel_nonneg _ _))
    exact Nat.floor_mono (mul_le_mul_of_nonneg_left hxy.2 (by positivity))
  · intro q hq
    exact tendsto_markedCriticalRenewalFunction q.1
      ((half_pos hp).trans_le hq.2.1)



end Critical2DKPZ.Renewal

end
