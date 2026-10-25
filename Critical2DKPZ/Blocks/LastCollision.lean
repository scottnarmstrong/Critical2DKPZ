/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.LastNoise
import Critical2DKPZ.Blocks.PredictableIsometry
import Mathlib.Tactic

/-! # The diagonal last-collision identity with arbitrary terminal data -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Blocks


/-- The spatial last-collision identity for a pair of terminal profiles. -/
theorem terminalProfile_mul_integral_lastCollision (β : ℝ) (a n : ℕ)
    (w : Site) (f g : Site → ℝ) :
    (∫ ω, (∑' z, pointToPoint β a n w z ω * f z) *
      (∑' z, pointToPoint β a n w z ω * g z) ∂disorderLaw) =
      Collision.terminalWalkMean n w f * Collision.terminalWalkMean n w g +
        ∑ r : Fin n, ∑' x,
          Collision.spatialRenewal (Polymer.sigmaSq β) (r.val + 1) (x - w) *
            (Collision.terminalWalkMean (n - (r.val + 1)) x f *
              Collision.terminalWalkMean (n - (r.val + 1)) x g) := by
  classical
  let J : Finset (Σ _ : Fin n, Site) :=
    Finset.univ.sigma (fun r => Polymer.endpoints w (r.val + 1))
  let time : (Σ _ : Fin n, Site) → ℕ := fun p => a + p.1.val
  let site : (Σ _ : Fin n, Site) → Site := fun p => p.2
  let F : (Site → ℝ) → (Σ _ : Fin n, Site) → Disorder → ℝ := fun h p ω =>
    preTerminalKernel β a p.1.val w p.2 ω *
      Collision.terminalWalkMean (n - (p.1.val + 1)) p.2 h
  have hinj : Set.InjOn (fun p => (time p, site p)) J := by
    rintro ⟨r, x⟩ _ ⟨s, y⟩ _ h
    have hrs : r = s := Fin.ext (Nat.add_left_cancel (congrArg Prod.fst h))
    have hxy : x = y := congrArg Prod.snd h
    cases hrs
    cases hxy
    rfl
  have hm (h : Site → ℝ) (p) (_ : p ∈ J) :
      Measurable[Gaussian.disorderBlock 0 (time p)] (F h p) := by
    have hp := (measurable_preTerminalKernel_block β a p.1.val w p.2).mono
      (Gaussian.disorderBlock_mono (Nat.zero_le a) le_rfl) le_rfl
    exact hp.mul measurable_const
  have hF (h : Site → ℝ) (p) (_ : p ∈ J) : MemLp (F h p) 4 disorderLaw :=
    (memLp_preTerminalKernel β a p.1.val w p.2 4 (by norm_num)).mul_const _
  have hexp (h : Site → ℝ) (ω : Disorder) :
      (∑' z, pointToPoint β a n w z ω * h z) =
      Collision.terminalWalkMean n w h +
        ∑ p ∈ J, F h p ω * Polymer.xi β (time p + 1, site p) ω := by
    rw [terminalProfile_lastNoise]
    congr 1
    simp only [J, Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r _
    unfold lastNoiseTerm
    rw [tsum_eq_sum (s := Polymer.endpoints w (r.val + 1))]
    · apply Finset.sum_congr rfl
      intro x _
      dsimp only [F, time, site]
      ring
    · intro x hx
      rw [preTerminalKernel_eq_zero_of_not_mem β a r.val w x ω hx,
        zero_mul, zero_mul]
  calc
    _ = ∫ ω, (Collision.terminalWalkMean n w f +
        ∑ p ∈ J, F f p ω * Polymer.xi β (time p + 1, site p) ω) *
        (Collision.terminalWalkMean n w g +
        ∑ p ∈ J, F g p ω * Polymer.xi β (time p + 1, site p) ω) ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => congrArg₂ (· * ·) (hexp f ω) (hexp g ω)
    _ = Collision.terminalWalkMean n w f * Collision.terminalWalkMean n w g +
        ∑ p ∈ J, Polymer.sigmaSq β * (∫ ω, F f p ω * F g p ω ∂disorderLaw) :=
      integral_const_add_finset_predictable_mul β (Collision.terminalWalkMean n w f)
        (Collision.terminalWalkMean n w g) J time site (F f) (F g) hinj (hm f) (hm g) (hF f) (hF g)
    _ = _ := by
      congr 1
      simp only [J, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro r _
      have hterm (x : Site) :
          Polymer.sigmaSq β * (∫ ω, F f ⟨r, x⟩ ω * F g ⟨r, x⟩ ω ∂disorderLaw) =
          Collision.spatialRenewal (Polymer.sigmaSq β) (r.val + 1) (x - w) *
            (Collision.terminalWalkMean (n - (r.val + 1)) x f *
              Collision.terminalWalkMean (n - (r.val + 1)) x g) := by
        have heq (ω : Disorder) : F f ⟨r, x⟩ ω * F g ⟨r, x⟩ ω =
            preTerminalKernel β a r.val w x ω ^ 2 *
              (Collision.terminalWalkMean (n - (r.val + 1)) x f *
                Collision.terminalWalkMean (n - (r.val + 1)) x g) := by dsimp only [F]; ring
        simp_rw [heq]
        rw [integral_mul_const, ← mul_assoc, sigmaSq_mul_preTerminalKernel_sq_integral]
      simp_rw [hterm]
      symm
      apply tsum_eq_sum
      intro x hx
      have hzero : Collision.spatialRenewal (Polymer.sigmaSq β) (r.val + 1) (x - w) = 0 := by
        rw [← sigmaSq_mul_preTerminalKernel_sq_integral β a r.val w x]
        simp only [preTerminalKernel_eq_zero_of_not_mem β a r.val w x _ hx,
          zero_pow (by omega : 2 ≠ 0), integral_zero, mul_zero]
      rw [hzero, zero_mul]

/-- Grouping the nonempty chaos by its last collision gives the spatial renewal profile. -/
theorem terminalProfile_sq_integral_lastCollision (β : ℝ) (a n : ℕ)
    (w : Site) (f : Site → ℝ) :
    (∫ ω, (∑' z, pointToPoint β a n w z ω * f z) ^ 2 ∂disorderLaw) =
      Collision.terminalWalkMean n w f ^ 2 +
        ∑ r : Fin n, ∑' x,
          Collision.spatialRenewal (Polymer.sigmaSq β) (r.val + 1) (x - w) *
            Collision.terminalWalkMean (n - (r.val + 1)) x f ^ 2 := by
  simpa only [pow_two] using terminalProfile_mul_integral_lastCollision β a n w f f

/-- The same last-collision identity with the empty chaos included as the zero-gap atom. -/
theorem terminalProfile_sq_integral_lastCollision_zeroIncluded (β : ℝ) (a n : ℕ)
    (w : Site) (f : Site → ℝ) :
    (∫ ω, (∑' z, pointToPoint β a n w z ω * f z) ^ 2 ∂disorderLaw) =
      ∑ r : Fin (n + 1), ∑' x,
        Collision.spatialRenewal (Polymer.sigmaSq β) r.val (x - w) *
          Collision.terminalWalkMean (n - r.val) x f ^ 2 := by
  rw [terminalProfile_sq_integral_lastCollision, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, Collision.spatialRenewal_zero, sub_eq_zero,
    ite_mul, one_mul, zero_mul, tsum_ite_eq, Nat.sub_zero]


end Critical2DKPZ.Blocks
