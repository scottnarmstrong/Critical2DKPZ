/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceScaling
public import Critical2DKPZ.SHF.Moments.EntranceRiemann
public import Critical2DKPZ.SHF.Moments.Dictionary
public import Critical2DKPZ.SHF.Moments.FirstMoment
import Mathlib.Tactic

/-! # Off-diagonal short-time collision entrance bounds -/

public section

open Filter
open MeasureTheory
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- The integral of a bounded spatial test against a heat-pair is controlled by the
two-center heat kernel. -/
theorem abs_heatKernelPairProfileIntegral_le_heatKernel
    {a b : Plane} (F : ℝ × Plane → ℝ) (M : ℝ)
    (hFbound : ∀ u x, |F (u, x)| ≤ M) (hFcont : Continuous F)
    {u : ℝ} (hu : 0 < u) :
    |heatKernelPairProfileIntegral u a b F| ≤ M * heatKernel (2 * u) (b - a) := by
  let center : Plane := (1 / 2 : ℝ) • (a + b)
  let pair : Plane → ℝ := fun x => heatKernel u (x - a) * heatKernel u (x - b)
  have hshift : Integrable (fun x : Plane => heatKernel (u / 2) (x - center)) := by
    have hmp : MeasurePreserving (fun x : Plane => x - center)
        (volume : Measure Plane) volume := by
      simpa only [sub_eq_add_neg] using
        (MeasureTheory.measurePreserving_add_right (volume : Measure Plane) (-center))
    exact hmp.integrable_comp_of_integrable
      (Critical2DKPZ.integrable_heatKernel (div_pos hu (by norm_num)))
  have hfactorInt : Integrable (fun x : Plane =>
      heatKernel (2 * u) (b - a) * heatKernel (u / 2) (x - center)) :=
    hshift.const_mul (heatKernel (2 * u) (b - a))
  have hpairInt : Integrable pair := by
    apply hfactorInt.congr
    filter_upwards [] with x
    exact (heatKernel_product_center_factorization hu a b x).symm
  have hFslice : Continuous (fun x : Plane => F (u, x)) :=
    hFcont.comp (continuous_const.prodMk continuous_id)
  have hFmeas : AEStronglyMeasurable (fun x : Plane => F (u, x)) :=
    hFslice.aestronglyMeasurable
  have hFprod : Integrable (fun x : Plane => F (u, x) * pair x) := by
    apply hpairInt.bdd_mul (c := M) hFmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs]
    exact hFbound u x
  have hpairNonneg : ∀ x, 0 ≤ pair x := by
    intro x
    exact mul_nonneg (heatKernel_nonneg hu.le _) (heatKernel_nonneg hu.le _)
  have hpairIntegral : (∫ x : Plane, pair x) = heatKernel (2 * u) (b - a) := by
    dsimp [pair]
    rw [show (fun x : Plane => heatKernel u (x - a) * heatKernel u (x - b)) =
        (fun x => heatKernel (2 * u) (b - a) * heatKernel (u / 2)
          (x - (1 / 2 : ℝ) • (a + b))) from by
            funext x
            exact heatKernel_product_center_factorization hu a b x]
    rw [integral_const_mul,
      Critical2DKPZ.integral_heatKernel_sub (div_pos hu (by norm_num))]
    ring
  unfold heatKernelPairProfileIntegral
  change |∫ x : Plane, F (u, x) * pair x| ≤ _
  calc
    _ = ‖∫ x : Plane, F (u, x) * pair x‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ x : Plane, ‖F (u, x) * pair x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : Plane, M * pair x := by
      apply integral_mono hFprod.norm (hpairInt.const_mul M)
      intro x
      change |F (u, x) * pair x| ≤ M * pair x
      rw [abs_mul, abs_of_nonneg (hpairNonneg x)]
      exact mul_le_mul_of_nonneg_right (hFbound u x) (hpairNonneg x)
    _ = M * heatKernel (2 * u) (b - a) := by
      rw [integral_const_mul, hpairIntegral]


/-- Separated limiting starting centers give an `O(ε + 1/N)` short-strip bound. The bound constant is uniform over tests bounded by `M`, while the scale threshold may depend on the test, `ε` and the starting sequences. -/
theorem eventually_collisionEntrance_offDiagonal_short_strip_bound
    {a b : Plane} (hab : a ≠ b) (aSite bSite : ℕ → Site)
    (ha : Tendsto (fun N => latticeRepresentative N (aSite N)) atTop (𝓝 a))
    (hb : Tendsto (fun N => latticeRepresentative N (bSite N)) atTop (𝓝 b))
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ × Plane → ℝ), (∀ p, |F p| ≤ M) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
        |collisionEntrance N 0 (evenCeil ((N : ℝ) * ε))
            (aSite N) (bSite N) F| ≤
          (2 * M * C / (‖b - a‖ / 2) ^ 2) * (ε + 3 / (N : ℝ)) := by
  obtain ⟨C, hC, hstrip⟩ := collisionEntrance_scaled_short_strip_bound
  have hgap : Tendsto
      (fun N => latticeRepresentative N (bSite N - aSite N)) atTop (𝓝 (b - a)) := by
    simpa only [latticeRepresentative_sub] using hb.sub ha
  let d : ℝ := ‖b - a‖ / 2
  have hd : 0 < d := by
    dsimp [d]
    exact half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hab)))
  have hseparated : ∀ᶠ N : ℕ in atTop,
      d ≤ ‖latticeRepresentative N (bSite N - aSite N)‖ := by
    have hclose : ∀ᶠ N : ℕ in atTop,
        ‖latticeRepresentative N (bSite N - aSite N) - (b - a)‖ < d := by
      exact (Metric.tendsto_nhds.mp hgap) d hd
    filter_upwards [hclose] with N hclose
    have hnorm := norm_le_norm_sub_add (b - a)
      (latticeRepresentative N (bSite N - aSite N))
    have hclose' :
        ‖(b - a) - latticeRepresentative N (bSite N - aSite N)‖ <
          ‖b - a‖ / 2 := by
      simpa only [norm_sub_rev, d] using hclose
    change ‖b - a‖ / 2 ≤ ‖latticeRepresentative N (bSite N - aSite N)‖
    linarith
  refine ⟨C, hC, fun F hF ε hε => ?_⟩
  filter_upwards [eventually_gt_atTop 0, hseparated] with N hN hsep
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let ε' : ℝ := ε + 2 / (N : ℝ)
  have hε' : 0 < ε' := by dsimp [ε']; positivity
  have hceil := (Critical2DKPZ.evenCeil_lt_add_two
    (mul_nonneg (Nat.cast_nonneg N) hε.le)).le
  have hK : (evenCeil ((N : ℝ) * ε) : ℝ) ≤ ε' * (N : ℝ) := by
    calc
      (evenCeil ((N : ℝ) * ε) : ℝ) ≤ (N : ℝ) * ε + 2 := by
        simpa [mul_comm] using hceil
      _ = ε' * (N : ℝ) := by
        dsimp [ε']
        field_simp [hNr.ne']
  have hmain := hstrip N (evenCeil ((N : ℝ) * ε)) hN
    (aSite N) (bSite N) F M d ε' hM hd hF hK hsep
  have htime : ε' + 1 / (N : ℝ) = ε + 3 / (N : ℝ) := by
    dsimp [ε']
    ring
  simpa only [d, htime] using hmain

end Critical2DKPZ.SHF.Moments

end
