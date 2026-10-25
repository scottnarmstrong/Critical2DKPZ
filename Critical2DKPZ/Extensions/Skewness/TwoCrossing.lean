/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Skewness.CenteredMoments
public import Mathlib.Analysis.Convex.Continuous
import Critical2DKPZ.EhrhardType.NormalCDF
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Finite crossing endpoints from the two matched moments -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped ENNReal

namespace Critical2DKPZ.Extensions.Skewness

/-- A finite convex representative and its residual are continuous everywhere. -/
theorem continuous_residual {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h) :
    Continuous (residual h) :=
  ((continuousOn_univ.mp (hc.continuousOn isOpen_univ)).sub continuous_const).sub
    (continuous_const.mul continuous_id)

/-- Subtracting the matching affine function preserves convexity. -/
theorem convexOn_residual {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h) :
    ConvexOn ℝ univ (residual h) :=
  (hc.sub (concaveOn_const (mean h) convex_univ)).sub
    ((concaveOn_id convex_univ).smul (stddev_nonneg h))

/-- A continuous, nonzero residual of mean zero takes both signs. -/
theorem residual_changes_sign {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h)
    (hL3 : MemLp h 3 (gaussianReal 0 1)) (hne : ∃ x, residual h x ≠ 0) :
    (∃ x, residual h x < 0) ∧ ∃ x, 0 < residual h x := by
  have := EhrhardType.isOpenPosMeasure_gaussianReal 0 (v := 1) one_ne_zero
  have hr := continuous_residual hc
  obtain ⟨hi, _, hz, _⟩ := orthogonality h hL3
  obtain ⟨x, hx⟩ := hne
  constructor
  · by_contra hn
    have hnn : 0 ≤ residual h := fun y => le_of_not_gt (fun hy => hn ⟨y, hy⟩)
    have hp := integral_pos_of_integrable_nonneg_nonzero hr hi hnn hx
    rw [hz] at hp
    exact hp.false
  · by_contra hn
    have hnn : 0 ≤ fun y => -residual h y := fun y =>
      neg_nonneg.mpr (le_of_not_gt (fun hy => hn ⟨y, hy⟩))
    have hp := integral_pos_of_integrable_nonneg_nonzero hr.neg hi.neg hnn (neg_ne_zero.mpr hx)
    change 0 < ∫ x, -residual h x ∂gaussianReal 0 1 at hp
    rw [integral_neg, hz, neg_zero] at hp
    exact hp.false

/-- A signed product with a strictly increasing companion cannot have zero mean
unless the continuous residual is identically zero. -/
theorem eq_zero_of_signed_companion {r w : ℝ → ℝ} (hr : Continuous r)
    (hw : StrictMono w) (c : ℝ)
    (hi : Integrable (fun x => r x * (w x - w c)) (gaussianReal 0 1))
    (hz : (∫ x, r x * (w x - w c) ∂gaussianReal 0 1) = 0)
    (hsign : (∀ x, 0 ≤ r x * (w x - w c)) ∨ (∀ x, r x * (w x - w c) ≤ 0)) :
    ∀ x, r x = 0 := by
  have := EhrhardType.isOpenPosMeasure_gaussianReal 0 (v := 1) one_ne_zero
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hp : (fun x => r x * (w x - w c)) =ᵐ[gaussianReal 0 1] 0 := by
    rcases hsign with hs | hs
    · exact (integral_eq_zero_iff_of_nonneg hs hi).mp hz
    · have hn : (fun x => -(r x * (w x - w c))) =ᵐ[gaussianReal 0 1] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => neg_nonneg.mpr (hs x)) hi.neg).mp
          (by rw [integral_neg, hz, neg_zero])
      filter_upwards [hn] with x hx using neg_eq_zero.mp hx
  have heq : r =ᵐ[gaussianReal 0 1] 0 := by
    filter_upwards [hp, (gaussianReal 0 1).ae_ne c] with x hx hxc
    exact (mul_eq_zero.mp hx).resolve_right (sub_ne_zero.mpr (hw.injective.ne hxc))
  exact congrFun (eq_of_ae_eq heq hr continuous_const)

/-- A nonempty open order-connected subset of the line has no member at a finite
infimum or supremum. -/
theorem strict_csInf_csSup_of_mem {S : Set ℝ} (ho : IsOpen S)
    (hlo : BddBelow S) (hhi : BddAbove S) {x : ℝ} (hx : x ∈ S) :
    sInf S < x ∧ x < sSup S := by
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ho.mem_nhds hx)
  have hleft : (a + x) / 2 ∈ S := hsub ⟨by linarith only [hab.1], by linarith only [hab.1, hab.2]⟩
  have hright : (x + b) / 2 ∈ S := hsub ⟨by linarith only [hab.1, hab.2], by linarith only [hab.2]⟩
  exact ⟨(csInf_le hlo hleft).trans_lt (by linarith only [hab.1]),
    lt_of_lt_of_le (by linarith only [hab.2]) (le_csSup hhi hright)⟩

/-- The residual's negative set has finite endpoints. The proof excludes both rays
by the two cancellations, following Step 2 of the note's crossing lemma. -/
theorem residual_negative_bounded {h : ℝ → ℝ} (hm : Monotone h)
    (hc : ConvexOn ℝ univ h) (hL3 : MemLp h 3 (gaussianReal 0 1))
    (hσ : 0 < stddev h) (hne : ∃ x, residual h x ≠ 0) :
    BddBelow {x | residual h x < 0} ∧ BddAbove {x | residual h x < 0} := by
  let S : Set ℝ := {x | residual h x < 0}
  let w : ℝ → ℝ := fun x => h x - mean h + stddev h * x
  have hw : StrictMono w := fun x y hxy =>
    add_lt_add_of_le_of_lt (sub_le_sub_right (hm hxy.le) _) (mul_lt_mul_of_pos_left hxy hσ)
  have ho : IsOpen S := isOpen_lt (continuous_residual hc) continuous_const
  have hconn : S.OrdConnected := by
    have hs := (convexOn_residual hc).convex_lt 0
    simpa only [mem_univ, true_and, ofPred_mem_eq] using hs.ordConnected
  obtain ⟨hS, hpos⟩ := residual_changes_sign hc hL3 hne
  obtain ⟨hi, hj, hz, hp⟩ := orthogonality h hL3
  have hshift : ∀ c, Integrable (fun x => residual h x * (w x - w c)) (gaussianReal 0 1) ∧
      (∫ x, residual h x * (w x - w c) ∂gaussianReal 0 1) = 0 := by
    intro c
    have hf : (fun x => residual h x * (w x - w c)) =
        (fun x => residual h x * w x - residual h x * w c) := by funext x; ring
    rw [hf]
    refine ⟨hj.sub (hi.mul_const _), ?_⟩
    rw [integral_sub hj (hi.mul_const _), integral_mul_const, hz, hp, zero_mul, sub_zero]
  have hnotboth : BddBelow S ∨ BddAbove S := by
    by_contra hn
    have hlo : ¬ BddBelow S := fun ht => hn (Or.inl ht)
    have hhi : ¬ BddAbove S := fun ht => hn (Or.inr ht)
    obtain ⟨t, ht⟩ := hpos
    obtain ⟨a, ha, hat⟩ := not_bddBelow_iff.mp hlo t
    obtain ⟨b, hb, htb⟩ := not_bddAbove_iff.mp hhi t
    exact (hconn.out ha hb ⟨hat.le, htb.le⟩).not_gt ht
  have hUpper : BddBelow S → BddAbove S := by
    intro hlo
    by_contra hhi
    have hzall := eq_zero_of_signed_companion (continuous_residual hc) hw (sInf S)
      (hshift _).1 (hshift _).2 (Or.inr (by
        intro x
        rcases lt_trichotomy x (sInf S) with hx | hx | hx
        · have hr : 0 ≤ residual h x := le_of_not_gt (fun hneg => hx.not_ge (csInf_le hlo hneg))
          exact mul_nonpos_of_nonneg_of_nonpos hr (sub_nonpos.mpr (hw.monotone hx.le))
        · rw [hx, sub_self, mul_zero]
        · obtain ⟨a, ha, hax⟩ := (csInf_lt_iff hlo hS).mp hx
          obtain ⟨b, hb, hxb⟩ := not_bddAbove_iff.mp hhi x
          have hr : residual h x < 0 := hconn.out ha hb ⟨hax.le, hxb.le⟩
          exact mul_nonpos_of_nonpos_of_nonneg hr.le (sub_nonneg.mpr (hw.monotone hx.le))))
    obtain ⟨x, hx⟩ := hne
    exact hx (hzall x)
  have hLower : BddAbove S → BddBelow S := by
    intro hhi
    by_contra hlo
    have hzall := eq_zero_of_signed_companion (continuous_residual hc) hw (sSup S)
      (hshift _).1 (hshift _).2 (Or.inl (by
        intro x
        rcases lt_trichotomy x (sSup S) with hx | hx | hx
        · obtain ⟨a, ha, hax⟩ := not_bddBelow_iff.mp hlo x
          obtain ⟨b, hb, hxb⟩ := (lt_csSup_iff hhi hS).mp hx
          have hr : residual h x < 0 := hconn.out ha hb ⟨hax.le, hxb.le⟩
          exact mul_nonneg_of_nonpos_of_nonpos hr.le (sub_nonpos.mpr (hw.monotone hx.le))
        · rw [hx, sub_self, mul_zero]
        · have hr : 0 ≤ residual h x := le_of_not_gt (fun hneg => hx.not_ge (le_csSup hhi hneg))
          exact mul_nonneg hr (sub_nonneg.mpr (hw.monotone hx.le))))
    obtain ⟨x, hx⟩ := hne
    exact hx (hzall x)
  rcases hnotboth with hlo | hhi
  · exact ⟨hlo, hUpper hlo⟩
  · exact ⟨hLower hhi, hhi⟩

/-- The two finite crossing points, including the boundary equalities. -/
theorem two_crossing {h : ℝ → ℝ} (hmono : Monotone h)
    (hconv : ConvexOn ℝ univ h) (hL3 : MemLp h 3 (gaussianReal 0 1))
    (hσ : 0 < stddev h) (hρ : ∃ x, residual h x ≠ 0) :
    ∃ x₁ x₂ : ℝ, x₁ < x₂ ∧
      (∀ x, residual h x < 0 ↔ x ∈ Ioo x₁ x₂) ∧
      residual h x₁ = 0 ∧ residual h x₂ = 0 := by
  let S : Set ℝ := {x | residual h x < 0}
  obtain ⟨hlo, hhi⟩ := residual_negative_bounded hmono hconv hL3 hσ hρ
  have hcont := continuous_residual hconv
  have ho : IsOpen S := isOpen_lt hcont continuous_const
  have hconn : S.OrdConnected := by
    have hs := (convexOn_residual hconv).convex_lt 0
    simpa only [mem_univ, true_and, ofPred_mem_eq] using hs.ordConnected
  obtain ⟨hne, _⟩ := residual_changes_sign hconv hL3 hρ
  obtain ⟨x, hx⟩ := hne
  have hab := strict_csInf_csSup_of_mem ho hlo hhi hx
  have hiff : ∀ x, residual h x < 0 ↔ x ∈ Ioo (sInf S) (sSup S) := by
    intro y
    constructor
    · exact strict_csInf_csSup_of_mem ho hlo hhi
    · intro hy
      obtain ⟨a, ha, hay⟩ := (csInf_lt_iff hlo ⟨x, hx⟩).mp hy.1
      obtain ⟨b, hb, hyb⟩ := (lt_csSup_iff hhi ⟨x, hx⟩).mp hy.2
      exact hconn.out ha hb ⟨hay.le, hyb.le⟩
  have hclosed : IsClosed {x | residual h x ≤ 0} := isClosed_le hcont continuous_const
  have hsub : closure S ⊆ {x | residual h x ≤ 0} :=
    closure_minimal (fun _ (hx : residual h _ < 0) => hx.le) hclosed
  refine ⟨sInf S, sSup S, hab.1.trans hab.2, hiff, ?_, ?_⟩
  · apply le_antisymm (hsub (csInf_mem_closure ⟨x, hx⟩ hlo))
    exact le_of_not_gt (fun ht => (hiff _).mp ht |>.1 |>.false)
  · apply le_antisymm (hsub (csSup_mem_closure ⟨x, hx⟩ hhi))
    exact le_of_not_gt (fun ht => (hiff _).mp ht |>.2 |>.false)

end Critical2DKPZ.Extensions.Skewness
