/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.Tightness
public import Critical2DKPZ.Polymer.Locality
public import Critical2DKPZ.PolymerCalculus.Clocks
public import Critical2DKPZ.Definitions.RescaledP2P
import Mathlib.MeasureTheory.Measure.Prod

/-! # Finite-scale independence of polymer measures on consecutive slabs

Each finite-scale polymer measure is measurable with respect to the disorder
coordinates in its time slab. Successive slabs therefore give independent
measure-valued random variables.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal CompactlySupported Topology

set_option linter.style.haveILetI false

noncomputable section

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Limit

/-- A polymer measure is measurable using only the disorder in its time slab.
The endpoint clock is `a + n`, matching the path kernel in `rescaledP2P`. -/
theorem measurable_polymerMeasure_disorderBlock (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (a n : ℕ)
    (ha : a = evenCeil ((N : ℝ) * s))
    (hn : n = evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) :
    Measurable[Gaussian.disorderBlock a (a + n)] (polymerMeasure ϑ N s t) := by
  classical
  letI : MeasurableSpace Disorder := Gaussian.disorderBlock a (a + n)
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hptp (wz : Site × Site) :
      Measurable (fun ω : Disorder =>
        pointToPoint (criticalBeta ϑ N) a n wz.1 wz.2 ω) := by
    exact Polymer.measurable_pointToPoint_block (criticalBeta ϑ N) a n wz.1 wz.2
  have hptp' : Measurable (fun q : (Site × Site) × Disorder =>
      pointToPoint (criticalBeta ϑ N) a n q.1.1 q.1.2 q.2) :=
    measurable_from_prod_countable_right hptp
  have hsites : Measurable (fun q : (Plane × Plane) × Disorder =>
      ((latticePoint N q.1.1, latticePoint N q.1.2), q.2)) :=
    ((((measurable_latticePoint N).comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_latticePoint N).comp (measurable_snd.comp measurable_fst))).prodMk
        measurable_snd)
  have hpair : Measurable (fun q : (Plane × Plane) × Disorder =>
      rescaledP2P ϑ N s t q.1 q.2) := by
    have hcomp := hptp'.comp hsites
    have hn' : n = evenCeil ((N : ℝ) * t) - a := by rw [ha]; exact hn
    simp only [rescaledP2P]
    rw [← ha, ← hn']
    exact hcomp.const_mul ((N : ℝ) / 4)
  have hres : Measurable (fun q : Disorder × (Plane × Plane) =>
      rescaledP2P ϑ N s t q.2 q.1) := measurable_swap_iff.mpr hpair
  have hset : MeasurableSet {q : Disorder × (Plane × Plane) | q.2 ∈ A} :=
    hA.preimage measurable_snd
  have hdens : Measurable (fun q : Disorder × (Plane × Plane) =>
      if q.2 ∈ A then ENNReal.ofReal (rescaledP2P ϑ N s t q.2 q.1) else 0) :=
    Measurable.ite hset (ENNReal.measurable_ofReal.comp hres) measurable_const
  have hlin : Measurable (fun ω : Disorder => ∫⁻ p : Plane × Plane,
      (if p ∈ A then ENNReal.ofReal (rescaledP2P ϑ N s t p ω) else 0)) :=
    hdens.lintegral_prod_right' (ν := (volume : Measure (Plane × Plane)))
  have hEq : (fun ω : Disorder => polymerMeasure ϑ N s t ω A) =
      fun ω => ∫⁻ p : Plane × Plane,
        (if p ∈ A then ENNReal.ofReal (rescaledP2P ϑ N s t p ω) else 0) := by
    funext ω
    simp only [polymerMeasure, withDensity_apply _ hA]
    rw [← lintegral_indicator hA]
    rfl
  rw [hEq]
  exact hlin

/-- The Radon-valued polymer measure is measurable with respect to its slab
disorder. -/
theorem measurable_polymerRadonMeasure_disorderBlock (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (a n : ℕ)
    (ha : a = evenCeil ((N : ℝ) * s))
    (hn : n = evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) :
    Measurable[Gaussian.disorderBlock a (a + n)] (polymerRadonMeasure ϑ N s t) := by
  letI : MeasurableSpace Disorder := Gaussian.disorderBlock a (a + n)
  exact (measurable_polymerMeasure_disorderBlock ϑ N s t a n ha hn).subtype_mk
    (h := fun ω => isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω)

/-- At every finite scale, polymer Radon measures on successive clock slabs
are jointly independent. -/
theorem iIndepFun_polymerRadonMeasure_consecutive (ϑ : ℝ) (N k : ℕ)
    (t : Fin (k + 1) → ℝ) (ht : StrictMono t) :
    iIndepFun (fun i : Fin k =>
      polymerRadonMeasure ϑ N (t i.castSucc) (t i.succ)) disorderLaw := by
  classical
  let a : Fin k → ℕ := fun i => evenCeil ((N : ℝ) * t i.castSucc)
  let b : Fin k → ℕ := fun i => evenCeil ((N : ℝ) * t i.succ)
  have hab : ∀ i, a i ≤ b i := by
    intro i
    apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left (ht i.castSucc_lt_succ).le (by positivity)
  have hdisj : Pairwise (fun i j : Fin k =>
      Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases hxi with ⟨hxi₁, hxi₂⟩
    rcases hxj with ⟨hxj₁, hxj₂⟩
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hij' | hij'
    · have hidx : i.succ ≤ j.castSucc := Fin.le_def.mpr (by
        simpa only [Fin.val_succ, Fin.val_castSucc] using
          (Nat.succ_le_of_lt hij'))
      have hclock : b i ≤ a j := evenCeil_mono
        (mul_le_mul_of_nonneg_left (ht.monotone hidx) (by positivity))
      exact (not_le_of_gt (lt_of_le_of_lt hclock hxj₁)) hxi₂
    · have hidx : j.succ ≤ i.castSucc := Fin.le_def.mpr (by
        simpa only [Fin.val_succ, Fin.val_castSucc] using
          (Nat.succ_le_of_lt hij'))
      have hclock : b j ≤ a i := evenCeil_mono
        (mul_le_mul_of_nonneg_left (ht.monotone hidx) (by positivity))
      exact (not_le_of_gt (lt_of_le_of_lt hclock hxi₁)) hxj₂
  have hm : ∀ i, Measurable[Gaussian.disorderBlock (a i) (b i)]
      (fun ω => polymerRadonMeasure ϑ N (t i.castSucc) (t i.succ) ω) := by
    intro i
    have hsum : a i + (b i - a i) = b i := Nat.add_sub_of_le (hab i)
    have hblock := measurable_polymerRadonMeasure_disorderBlock ϑ N
      (t i.castSucc) (t i.succ) (a i) (b i - a i) rfl (by rfl)
    have hblock' : Measurable[Gaussian.disorderBlock (a i) (b i)]
        (fun ω => polymerRadonMeasure ϑ N (t i.castSucc) (t i.succ) ω) := by
      rw [← hsum]
      exact hblock
    exact hblock'
  rw [iIndepFun_iff]
  intro S sets hsets
  exact (iIndep_iff _ _).1 (Gaussian.iIndep_disorderBlock a b hdisj) S
    (fun i hi => (hm i).comap_le (sets i) (hsets i hi))

end Critical2DKPZ.SHF.Flow

end
