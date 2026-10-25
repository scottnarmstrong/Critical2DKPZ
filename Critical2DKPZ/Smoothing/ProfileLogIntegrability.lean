/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.PolymerCalculus.PathAssociation
public import Critical2DKPZ.Smoothing.Measurability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-! # Square integrability of logarithms with bounded terminal weights -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.Smoothing

/-- A bounded positive terminal weight changes a finite normalized profile logarithm by a bounded
amount, so the weighted logarithm inherits square integrability from the flat finite path mass. -/
theorem memLp_log_profileP2Fun_of_bounded_terminal (β : ℝ) (a b : ℕ)
    (ν : Site → ℝ) (A : Finset Site) (hνA : ∀ w ∉ A, ν w = 0)
    (hν0 : ∀ w, 0 ≤ ν w) (hν1 : ∑ w ∈ A, ν w = 1)
    (f : Site → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ z, 0 < f z ∧ |Real.log (f z)| ≤ L) :
    MemLp (fun ω => Real.log (profileP2Fun β a b ν f ω)) 2 disorderLaw := by
  classical
  let Starts := {w // w ∈ A}
  let start : Starts → Site := fun w => w.1
  let coeff : Starts × (Fin (b - a) → Fin 4) → ℝ := fun p =>
    ν p.1.1 * ((4 : ℝ)⁻¹ ^ (b - a))
  have hνpos : ∃ w ∈ A, 0 < ν w := by
    have hsum : 0 < ∑ w ∈ A, ν w := by rw [hν1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun w hw => hν0 w)).mp hsum
  have hcoeff0 : ∀ p, 0 ≤ coeff p := by
    intro p
    dsimp [coeff]
    exact mul_nonneg (hν0 p.1.1) (by positivity)
  have hcoeffpos : ∃ p, 0 < coeff p := by
    obtain ⟨w, hwA, hw⟩ := hνpos
    refine ⟨(⟨w, hwA⟩, fun _ => 0), ?_⟩
    dsimp [coeff]
    exact mul_pos hw (by positivity)
  have hflat : MemLp
      (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)) 2 disorderLaw := by
    have hpath := PolymerCalculus.memLp_log_finitePathMass β a (b - a) start
      hcoeff0 hcoeffpos 2
    have heq (ω : Disorder) : profileP2Fun β a b ν (fun _ => 1) ω =
        PolymerCalculus.finitePathMass β a (b - a) start coeff ω := by
      simpa only [start, coeff, Starts] using
        OnePoint.profileP2Fun_eq_finitePathMass β a b ν A hνA ω
    have hfun : (fun ω => Real.log (profileP2Fun β a b ν (fun _ => 1) ω)) =
        fun ω => Real.log (PolymerCalculus.finitePathMass β a (b - a) start coeff ω) := by
      funext ω
      rw [heq]
    rw [hfun]
    exact hpath
  let D : Disorder → ℝ := fun ω =>
    Real.log (profileP2Fun β a b ν f ω) -
      Real.log (profileP2Fun β a b ν (fun _ => 1) ω)
  have hFmeas : Measurable (fun ω => profileP2Fun β a b ν f ω) :=
    measurable_profileP2Fun_param β a b f (fun _ => measurable_const) measurable_id
  have hFlatMeas : Measurable
      (fun ω => profileP2Fun β a b ν (fun _ => 1) ω) :=
    measurable_profileP2Fun_param β a b (fun _ => 1)
      (fun _ => measurable_const) measurable_id
  have hDmeas : Measurable D := by
    dsimp [D]
    exact hFmeas.log.sub hFlatMeas.log
  have hDbound : ∀ ω, |D ω| ≤ L := by
    intro ω
    exact FutureProfiles.abs_log_profileP2Fun_sub_le β a b ν A hνA hν0 hν1 f L hf ω
  have hDmem : MemLp D 2 disorderLaw := by
    apply (memLp_two_iff_integrable_sq hDmeas.aestronglyMeasurable).2
    refine Integrable.of_bound (hDmeas.pow_const 2).aestronglyMeasurable (L ^ 2) ?_
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (D ω))]
      have hsq := (sq_le_sq₀ (abs_nonneg (D ω)) hL).2 (hDbound ω)
      simpa only [sq_abs] using hsq
  have hlog : (fun ω => Real.log (profileP2Fun β a b ν f ω)) =
      fun ω => D ω + Real.log (profileP2Fun β a b ν (fun _ => 1) ω) := by
    funext ω
    dsimp [D]
    ring
  rw [hlog]
  exact hDmem.add hflat

end Critical2DKPZ.Smoothing

end
