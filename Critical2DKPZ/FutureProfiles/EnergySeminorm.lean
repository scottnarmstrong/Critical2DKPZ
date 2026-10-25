/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.FreezingPast
public import Critical2DKPZ.Polymer.Profiles
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # The future-energy square root is an L² seminorm -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.FutureProfiles

private theorem eLpNorm_profile_sqrt (β : ℝ) (a b : ℕ) (η : Site → ℝ)
    (A : Finset Site) (hη : ∀ w ∉ A, η w = 0) :
    (eLpNorm (profileP2Fun β a b η (fun _ => 1)) 2 disorderLaw).toReal =
      Real.sqrt (futureEnergy β a b η) := by
  let F : Disorder → ℝ := fun ω => profileP2Fun β a b η (fun _ => 1) ω
  have hF : MemLp F 2 disorderLaw := by
    dsimp [F]
    exact Polymer.memLp_profileP2Fun_finset β a b η (fun _ => 1) A hη 2 (by norm_num)
  have hnormPow :
      (∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂disorderLaw) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ =
        (eLpNorm F 2 disorderLaw).toReal := by
    rw [hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have hnonneg : 0 ≤
        (∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂disorderLaw) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := by positivity
    exact (ENNReal.toReal_ofReal hnonneg).symm
  have henergy :
      futureEnergy β a b η = ∫ ω, ‖F ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂disorderLaw := by
    simp [futureEnergy, F, ENNReal.toReal_ofNat, Real.norm_eq_abs, sq_abs]
  rw [← hnormPow, ← henergy, Real.sqrt_eq_rpow]
  congr 1
  norm_num [ENNReal.toReal_ofNat]

/-- The square root of the future energy satisfies the triangle inequality for finite profiles. -/
theorem sqrt_futureEnergy_add_le (β : ℝ) (a b : ℕ) (η η' : Site → ℝ) (A : Finset Site)
    (hη : ∀ w ∉ A, η w = 0) (hη' : ∀ w ∉ A, η' w = 0) :
    Real.sqrt (futureEnergy β a b (η + η')) ≤
      Real.sqrt (futureEnergy β a b η) + Real.sqrt (futureEnergy β a b η') := by
  have hsumSupp : ∀ w ∉ A, (η + η') w = 0 := by
    intro w hw
    simp [hη w hw, hη' w hw]
  have hlin (ω : Disorder) :
      profileP2Fun β a b (η + η') (fun _ => 1) ω =
        profileP2Fun β a b η (fun _ => 1) ω + profileP2Fun β a b η' (fun _ => 1) ω := by
    rw [Polymer.profileP2Fun_eq_sum β a b (η + η') (fun _ => 1) A hsumSupp ω,
      Polymer.profileP2Fun_eq_sum β a b η (fun _ => 1) A hη ω,
      Polymer.profileP2Fun_eq_sum β a b η' (fun _ => 1) A hη' ω]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    simp only [Pi.add_apply]
    change (η w + η' w) *
        (∑' z, pointToPoint β a (b - a) w z ω * (1 : ℝ)) =
      η w * (∑' z, pointToPoint β a (b - a) w z ω * (1 : ℝ)) +
        η' w * (∑' z, pointToPoint β a (b - a) w z ω * (1 : ℝ))
    ring
  have hFplus :
      profileP2Fun β a b (η + η') (fun _ => 1) =
        profileP2Fun β a b η (fun _ => 1) +
          profileP2Fun β a b η' (fun _ => 1) := by
    funext ω
    exact hlin ω
  rw [← eLpNorm_profile_sqrt β a b (η + η') A hsumSupp,
    ← eLpNorm_profile_sqrt β a b η A hη,
    ← eLpNorm_profile_sqrt β a b η' A hη']
  rw [hFplus]
  have htri := eLpNorm_add_le (f := fun ω => profileP2Fun β a b η (fun _ => 1) ω)
    (g := fun ω => profileP2Fun β a b η' (fun _ => 1) ω)
    (p := (2 : ℝ≥0∞)) (μ := disorderLaw) (by norm_num)
  have hηMem : MemLp (profileP2Fun β a b η (fun _ => 1)) 2 disorderLaw :=
    Polymer.memLp_profileP2Fun_finset β a b η (fun _ => 1) A hη 2 (by norm_num)
  have hη'Mem : MemLp (profileP2Fun β a b η' (fun _ => 1)) 2 disorderLaw :=
    Polymer.memLp_profileP2Fun_finset β a b η' (fun _ => 1) A hη' 2 (by norm_num)
  have htriReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hηMem.eLpNorm_ne_top, hη'Mem.eLpNorm_ne_top⟩) htri
  rw [ENNReal.toReal_add hηMem.eLpNorm_ne_top hη'Mem.eLpNorm_ne_top] at htriReal
  exact htriReal

end Critical2DKPZ.FutureProfiles

end
