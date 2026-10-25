/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureConvergence
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureJoint
public import Critical2DKPZ.SHF.Moments.SinglePairWordCompact
import Mathlib.Tactic

/-! # Phase-correct sampling of the complete two-particle future -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- Sample a collision location in the phase appropriate to a remaining
walk duration. The parity correction disappears at diffusive scale. -/
def pairTwoFutureSampleSite (N r : ℕ) (w : Plane) : Site :=
  latticePoint N (w - latticeRepresentative N (entranceParityShift r)) + entranceParityShift r

/-- The sampled future site has the required terminal parity. -/
theorem pairTwoFutureSampleSite_phase (N r : ℕ) (w : Plane) :
    Even (pairTwoFutureSampleSite N r w 0 + pairTwoFutureSampleSite N r w 1 + (r : ℤ)) := by
  have hp := entranceParityShift_phase r (a := 0) (by change Even ((0 : ℤ) + 0); simp)
  have he := latticePoint_mem_evenLattice N (w - latticeRepresentative N (entranceParityShift r))
  change Even (latticePoint N (w - latticeRepresentative N (entranceParityShift r)) 0 +
    latticePoint N (w - latticeRepresentative N (entranceParityShift r)) 1) at he
  have h := he.add hp
  convert h using 1
  simp only [pairTwoFutureSampleSite, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, sub_zero]
  ring

private theorem tendsto_cellSample_moving (wN : ℕ → Plane) (w : Plane)
    (hw : Tendsto wN atTop (𝓝 w)) :
    Tendsto (fun N => cellSample N (wN N)) atTop (𝓝 w) := by
  apply hw.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (eventually_gt_atTop 0 |>.mono fun N hN => ?_) tendsto_lattice_mesh
  simpa only [dist_comm] using dist_cellSample_le hN (wN N)

/-- Sampling arbitrary moving collision locations preserves their limit,
regardless of the microscopic remaining-time parity. -/
theorem tendsto_pairTwoFutureSampleSite (rN : ℕ → ℕ) (wN : ℕ → Plane) (w : Plane)
    (hw : Tendsto wN atTop (𝓝 w)) :
    Tendsto (fun N => latticeRepresentative N (pairTwoFutureSampleSite N (rN N) (wN N)))
      atTop (𝓝 w) := by
  have hδ := tendsto_entranceParityShift_along rN
  have harg : Tendsto (fun N => wN N - latticeRepresentative N (entranceParityShift (rN N)))
      atTop (𝓝 w) := by simpa only [sub_zero] using hw.sub hδ
  have hs := tendsto_cellSample_moving _ w harg
  have h := hs.add hδ
  simpa only [pairTwoFutureSampleSite, latticeRepresentative_add, cellSample, add_zero] using h

/-- The future test sampled at macroscopic collision time and location. -/
def pairTwoFutureSampleProfile (ϑ : ℝ) (N L : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (p : ℝ × Plane) : ℝ :=
  let r := L - Nat.floor ((N : ℝ) * p.1)
  (N : ℝ)^2 * pairTwoFutureTestedTail (criticalSigmaSq ϑ N) N r 0 φ x
    (pairTwoFutureSampleSite N r p.2)

/-- The remaining microscopic duration has the expected moving diffusive limit. -/
theorem tendsto_remaining_floor (L : ℕ → ℕ) {T u : ℝ}
    (hL : Tendsto (fun N => (L N : ℝ) / N) atTop (𝓝 T))
    (uN : ℕ → ℝ) (huN : Tendsto uN atTop (𝓝 u)) (hu : 0 < u) (huT : u < T) :
    Tendsto (fun N => ((L N - Nat.floor ((N : ℝ) * uN N) : ℕ) : ℝ) / N)
      atTop (𝓝 (T - u)) := by
  have hf := tendsto_floor_scaled_moving id tendsto_id uN huN hu
  have hgap := (hL.sub hf).eventually (Ioi_mem_nhds (sub_pos.mpr huT))
  apply (hL.sub hf).congr'
  filter_upwards [hgap, eventually_gt_atTop 0] with N hgapN hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlt : (Nat.floor ((N : ℝ) * uN N) : ℝ) < L N := by
    exact (div_lt_div_iff_of_pos_right hNr).mp (sub_pos.mp hgapN)
  have hle : Nat.floor ((N : ℝ) * uN N) ≤ L N := by exact_mod_cast hlt.le
  rw [Nat.cast_sub hle, sub_div]
  rfl



end Critical2DKPZ.SHF.Moments
