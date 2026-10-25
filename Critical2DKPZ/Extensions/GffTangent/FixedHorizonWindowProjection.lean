/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonBlocks
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonParity
import Critical2DKPZ.Extensions.GffTangent.FlowMartingale
import Critical2DKPZ.Blocks.BlockResampling
import Critical2DKPZ.SHF.Flow.SlabProjection

/-! # Conditional projections onto a linear-time polymer window -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- Annealing the complement of a window removes all disorder before its left
endpoint while retaining the free entrance walk. -/
theorem integral_pointToPlane_resample_window (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (x : Site) (ω : Disorder) :
    (∫ η, pointToPlane β 0 b x
      (Gaussian.resample (Gaussian.timeBlock a b) ω η) ∂disorderLaw) =
      smoothedP2Plane β a b x ω := by
  classical
  let E := Polymer.endpoints x a
  have hfirst (y : Site) (η : Disorder) : pointToPoint β 0 a x y
      (Gaussian.resample (Gaussian.timeBlock a b) ω η) = pointToPoint β 0 a x y η := by
    apply SHF.Flow.blockMeasurable_resample_outside (a := 0) (b := a) (c := a) (d := b)
    · exact Set.disjoint_left.mpr fun k hk hk' => (not_lt_of_ge hk.2) hk'.1
    · have hm := Polymer.measurable_pointToPoint_block β 0 a x y
      change Measurable[Gaussian.disorderBlock 0 (0 + a)] (pointToPoint β 0 a x y) at hm
      rw [Nat.zero_add] at hm
      exact hm
  have hlast (y : Site) (η : Disorder) : pointToPlane β a (b - a) y
      (Gaussian.resample (Gaussian.timeBlock a b) ω η) = pointToPlane β a (b - a) y ω := by
    apply Blocks.blockMeasurable_resample_keep
    convert Polymer.measurable_pointToPlane_block β a (b - a) y using 1
    rw [Nat.add_sub_of_le hab]
  have he (η : Disorder) : pointToPlane β 0 b x
      (Gaussian.resample (Gaussian.timeBlock a b) ω η) =
      ∑ y ∈ E, pointToPoint β 0 a x y η * pointToPlane β a (b - a) y ω := by
    have hc := Polymer.pointToPlane_chapmanKolmogorov β 0 a (b - a) x
      (Gaussian.resample (Gaussian.timeBlock a b) ω η)
    rw [Nat.add_sub_of_le hab, Nat.zero_add] at hc
    rw [hc]
    simp_rw [hfirst, hlast]
    exact tsum_eq_sum (s := E) fun y hy => by
      rw [Polymer.pointToPoint_eq_zero_of_not_mem β 0 a x y η hy, zero_mul]
  calc
    _ = ∫ η, ∑ y ∈ E, pointToPoint β 0 a x y η * pointToPlane β a (b - a) y ω ∂disorderLaw :=
      integral_congr_ae (Eventually.of_forall he)
    _ = ∑ y ∈ E, srwKernel a (y - x) * pointToPlane β a (b - a) y ω := by
      rw [integral_finsetSum E (fun y _ => (Polymer.integrable_pointToPoint β 0 a x y).mul_const _)]
      simp only [integral_mul_const, Polymer.integral_pointToPoint]
    _ = _ := (Polymer.smoothedP2Plane_eq_sum β a b x ω).symm

/-- The source window variable is the conditional projection of the full
point-to-plane mass at the right endpoint. -/
theorem condExp_pointToPlane_window_endpoint (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (x : Site) :
    disorderLaw[pointToPlane β 0 b x | Gaussian.disorderBlock a b] =ᵐ[disorderLaw]
      freeEntranceWindowMass β a b x := by
  have hh := Gaussian.condExp_disorderBlock_ae_eq a b
    (Polymer.measurable_pointToPlane β 0 b x) (Polymer.integrable_pointToPlane β 0 b x)
  filter_upwards [hh] with ω hω
  rw [hω, integral_pointToPlane_resample_window β hab,
    freeEntranceWindowMass_eq_smoothedP2Plane]

/-- The same window is the conditional projection of any longer polymer.
The tower property first anneals the future of the right endpoint. -/
theorem condExp_pointToPlane_window (β : ℝ) {a b N : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    (x : Site) :
    disorderLaw[pointToPlane β 0 N x | Gaussian.disorderBlock a b] =ᵐ[disorderLaw]
      freeEntranceWindowMass β a b x := by
  have hle : Gaussian.disorderBlock a b ≤ Gaussian.disorderBlock 0 b :=
    Gaussian.disorderBlock_mono (Nat.zero_le a) le_rfl
  have htower := condExp_condExp_of_le (μ := disorderLaw) (f := pointToPlane β 0 N x)
    hle (Gaussian.disorderBlock_le 0 b)
  exact htower.symm.trans ((condExp_congr_ae (m := Gaussian.disorderBlock a b)
    (condExp_pointToPlane_ae_eq β hbN x)).trans (condExp_pointToPlane_window_endpoint β hab x))

/-- Conditional projections commute with the finite signed spatial average,
including its exact deterministic centering and normalization. -/
theorem condExp_finiteEntranceFluctuation_window (β c : ℝ) {a b N : ℕ}
    (hab : a ≤ b) (hbN : b ≤ N) (S : Finset Site) (ν : Site → ℝ) :
    disorderLaw[finiteEntranceFluctuation β c 0 N S ν | Gaussian.disorderBlock a b] =ᵐ[disorderLaw]
      latticeWindowFluctuation β c a b S ν := by
  let m := Gaussian.disorderBlock a b
  let F : Site → Disorder → ℝ := fun w ω => (c * ν w) * (pointToPlane β 0 N w ω - 1)
  let G : Site → Disorder → ℝ := fun w ω => (c * ν w) * (freeEntranceWindowMass β a b w ω - 1)
  have hFi (w : Site) : Integrable (F w) disorderLaw := by
    simpa only [F, Pi.sub_apply] using
      ((Polymer.integrable_pointToPlane β 0 N w).sub (integrable_const 1)).const_mul (c * ν w)
  have hsum := condExp_finsetSum (μ := disorderLaw) (m := m) (s := S) (fun w _ => hFi w)
  have hterm (w : Site) : disorderLaw[F w | m] =ᵐ[disorderLaw] G w := by
    have hs := condExp_smul (μ := disorderLaw) (c := c * ν w)
      (f := fun ω => pointToPlane β 0 N w ω - 1) m
    have hd := condExp_sub (Polymer.integrable_pointToPlane β 0 N w) (integrable_const (1 : ℝ)) m
    have hp := condExp_pointToPlane_window β hab hbN w
    filter_upwards [hs, hd, hp] with ω hsω hdω hpω
    change disorderLaw[(c * ν w) • (fun ω => pointToPlane β 0 N w ω - 1) | m] ω = _
    rw [hsω]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show disorderLaw[(fun ω => pointToPlane β 0 N w ω - 1) | m] ω =
      disorderLaw[pointToPlane β 0 N w | m] ω - disorderLaw[(fun _ => (1 : ℝ)) | m] ω from hdω,
      hpω, condExp_const (Gaussian.disorderBlock_le a b) (1 : ℝ)]
  have hterms := eventuallyEq_sum (s := S) fun w _ => hterm w
  have hF : (∑ w ∈ S, F w) = finiteEntranceFluctuation β c 0 N S ν := by
    funext ω
    simp only [F, Finset.sum_apply, finiteEntranceFluctuation, Finset.mul_sum, mul_assoc]
  have hG : (∑ w ∈ S, G w) = latticeWindowFluctuation β c a b S ν := by
    funext ω
    simp only [G, Finset.sum_apply, latticeWindowFluctuation, Finset.mul_sum, mul_assoc]
  rw [hF] at hsum
  rw [hG] at hterms
  exact hsum.trans hterms

end Critical2DKPZ.Extensions.GffTangent
