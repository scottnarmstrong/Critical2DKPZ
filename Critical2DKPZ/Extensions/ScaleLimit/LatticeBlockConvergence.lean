/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.LatticeMassConvergence
public import Critical2DKPZ.Extensions.ScaleLimit.LatticeBlockClock
public import Critical2DKPZ.Definitions.SmoothedP2Plane
import Critical2DKPZ.NonGaussian.HeatStartWalkLaw
import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! # Joint convergence of a fixed finite family of reversed geometric blocks

The reversed block indices are held fixed while the even lattice size grows.
This is the lattice-to-flow identification used before any block index tends
to infinity.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- With smoothing time equal to initial time, the walk profile is the literal
smoothed point-to-plane mass. Parity removes the cell-averaged terminal. -/
theorem latticeHeatMass_eq_smoothed (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    {s t : ℝ} (hst : s ≤ t) (x : Plane) (ω : Disorder) :
    latticeHeatMass ϑ N s t s x ω =
      smoothedP2Plane (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * t))
        (latticePoint N x) ω := by
  have hab := evenCeil_mono (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N))
  have hflat := NonGaussian.heatStartWalkProfile_cellAverage_one_eq (criticalBeta ϑ N)
    hN hab (evenCeil_even (N * s)) ((evenCeil_even (N * t)).tsub (evenCeil_even (N * s))) x ω
  exact hflat.trans (Polymer.profileP2Fun_srw_flat _ _ _ _ _)

/-- Lattice mass over the interval with fixed reversed endpoints `a > b`, on an
even lattice size. The definition is meaningful also at the initial sizes. -/
def latticeGeometricMass (ϑ ρ : ℝ) (N a b : ℕ) (ω : Disorder) : ℝ :=
  smoothedP2Plane (criticalBeta ϑ (2 * N))
    (blockTime (2 * N) ρ (blockCount (2 * N) ρ - a))
    (blockTime (2 * N) ρ (blockCount (2 * N) ρ - b)) 0 ω

/-- Every fixed finite family of geometric lattice masses converges jointly to
the masses of the given flow, including intervals terminating at time one. -/
theorem latticeGeometricMass_joint_tendsto (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {ρ : ℝ} (hρ : 1 < ρ) (k : ℕ) (a b : Fin k → ℕ) (hab : ∀ i, b i < a i) :
    TendstoInDistribution (fun N ω i => latticeGeometricMass ϑ ρ N (a i) (b i) ω)
      atTop (fun ω i => shfPairing Z (tau ρ (a i)) (tau ρ (b i))
        (fun y => heatKernel (tau ρ (a i)) y) (fun _ => 1) ω) (fun _ => disorderLaw) P := by
  have hp (i : Fin k) : 0 ≤ tau ρ (a i) ∧ tau ρ (a i) < tau ρ (b i) ∧ 0 < tau ρ (a i) :=
    ⟨(tau_pos hρ _).le, strictAnti_tau hρ (hab i), tau_pos hρ _⟩
  have hdist := latticeHeatMass_joint_tendsto ϑ P Z hZ k
    (fun i => tau ρ (a i)) (fun i => tau ρ (b i)) (fun i => tau ρ (a i)) (fun _ => 0) hp
  have h2 : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
    tendsto_atTop_mono (f := fun N : ℕ => N) (fun N => by omega) tendsto_id
  have hdistEven : TendstoInDistribution
      (fun N ω i => latticeHeatMass ϑ (2 * N) (tau ρ (a i)) (tau ρ (b i)) (tau ρ (a i)) 0 ω)
      atTop (fun ω i => shfPairing Z (tau ρ (a i)) (tau ρ (b i))
        (fun y => heatKernel (tau ρ (a i)) y) (fun _ => 1) ω) (fun _ => disorderLaw) P := by
    refine ⟨fun N => hdist.forall_aemeasurable (2 * N), ?_, ?_⟩
    · simpa only [sub_zero] using hdist.aemeasurable_limit
    · convert! hdist.tendsto.comp h2 using 1
      simp only [sub_zero]
  have hclock : ∀ᶠ N : ℕ in atTop, ∀ i : Fin k,
      blockTime (2 * N) ρ (blockCount (2 * N) ρ - a i) = evenCeil ((2 * N : ℕ) * tau ρ (a i)) ∧
      blockTime (2 * N) ρ (blockCount (2 * N) ρ - b i) = evenCeil ((2 * N : ℕ) * tau ρ (b i)) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (eventually_blockTime_reverse_eq hρ (a i)).and (eventually_blockTime_reverse_eq hρ (b i))
  refine ⟨fun N => aemeasurable_pi_iff.mpr (fun i =>
    (Polymer.measurable_smoothedP2Plane _ _ _ _).aemeasurable), hdistEven.aemeasurable_limit, ?_⟩
  apply Tendsto.congr' ?_ hdistEven.tendsto
  filter_upwards [hclock, eventually_ge_atTop 1] with N hN hN1
  apply Subtype.ext
  apply Measure.map_congr
  filter_upwards [] with ω
  funext i
  dsimp [latticeGeometricMass]
  rw [(hN i).1, (hN i).2]
  have heq := latticeHeatMass_eq_smoothed ϑ (by omega : 0 < 2 * N) (hp i).2.1.le 0 ω
  have hzero : latticePoint (2 * N) (0 : Plane) = 0 := by simp [latticePoint, nearestEven]
  simpa only [hzero] using heq

end Critical2DKPZ.Extensions.ScaleLimit
