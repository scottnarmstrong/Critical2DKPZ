/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Gaussian.DisorderLaws
public import Critical2DKPZ.Polymer.Profiles

/-! # A common forward time shift of the Gaussian environment -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.Smoothing

/-- Drop the first `d` time slices, keeping one shared environment for every observable. -/
def shiftEnvironment (d : ℕ) (ω : Disorder) : Disorder := fun p => ω (d + p.1, p.2)

/-- The time-shifted disorder map is measurable. -/
theorem measurable_shiftEnvironment (d : ℕ) : Measurable (shiftEnvironment d) :=
  measurable_pi_iff.mpr fun p => Gaussian.measurable_disorder_eval (d + p.1, p.2)

/-- Injective reindexing preserves the product standard-Gaussian disorder law. -/
theorem measurePreserving_shiftEnvironment (d : ℕ) :
    MeasurePreserving (shiftEnvironment d) disorderLaw disorderLaw := by
  have hinj : Function.Injective (fun p : ℕ × Site => (d + p.1, p.2)) := by
    intro p q h
    have ht := congrArg Prod.fst h
    have hx := congrArg Prod.snd h
    exact Prod.ext (by simpa only [Nat.add_left_cancel_iff] using ht) hx
  refine ⟨measurable_shiftEnvironment d, ?_⟩
  change disorderLaw.map (fun ω p => ω (d + p.1, p.2)) = disorderLaw
  have hm : ∀ p : ℕ × Site, AEMeasurable (fun ω : Disorder => ω (d + p.1, p.2)) disorderLaw :=
    fun p => (Gaussian.measurable_disorder_eval (d + p.1, p.2)).aemeasurable
  have he := (Gaussian.iIndepFun_disorder_eval.precomp hinj).map_fun_eq_infinitePi_map₀' hm
  calc
    _ = Measure.infinitePi (fun p : ℕ × Site =>
        disorderLaw.map (fun ω : Disorder => ω (d + p.1, p.2))) := he
    _ = disorderLaw := by
      have hcoord (p : ℕ × Site) : disorderLaw.map (fun ω : Disorder => ω (d + p.1, p.2)) =
          gaussianReal 0 1 := (Gaussian.hasLaw_disorder_eval (d + p.1, p.2)).map_eq
      have hfun : (fun p : ℕ × Site => disorderLaw.map (fun ω : Disorder => ω (d + p.1, p.2))) =
          (fun _ : ℕ × Site => gaussianReal 0 1) := funext hcoord
      rw [hfun]
      rfl

/-- Expectations of measurable observables are invariant under the common shift. -/
theorem integral_shiftEnvironment (d : ℕ) {F : Disorder → ℝ} (hF : Measurable F) :
    (∫ ω, F (shiftEnvironment d ω) ∂disorderLaw) = ∫ ω, F ω ∂disorderLaw := by
  have h := integral_map (μ := disorderLaw) (measurable_shiftEnvironment d).aemeasurable hF.aestronglyMeasurable
  rw [(measurePreserving_shiftEnvironment d).map_eq] at h
  exact h.symm

/-- The path energy after a common time shift is exactly the original path energy. -/
theorem pathWeight_timeShift (β : ℝ) (d a : ℕ) (w : Site) {n : ℕ}
    (s : Fin n → Fin 4) (ω : Disorder) :
    Polymer.pathWeight β (d + a) w s ω = Polymer.pathWeight β a w s (shiftEnvironment d ω) := by
  simp only [Polymer.pathWeight, shiftEnvironment, Nat.add_assoc]

/-- Shifting the disorder clock identifies the corresponding point-to-point partition functions. -/
theorem pointToPoint_timeShift (β : ℝ) (d a n : ℕ) (w z : Site) (ω : Disorder) :
    pointToPoint β (d + a) n w z ω = pointToPoint β a n w z (shiftEnvironment d ω) := by
  simp only [Polymer.pointToPoint_eq_sum, pathWeight_timeShift]

/-- Shifting the disorder clock identifies the corresponding profile-tested partition functions. -/
theorem profileP2Fun_timeShift (β : ℝ) (d a b : ℕ) (ν f : Site → ℝ) (ω : Disorder) :
    profileP2Fun β (d + a) (d + b) ν f ω = profileP2Fun β a b ν f (shiftEnvironment d ω) := by
  simp only [profileP2Fun, Nat.add_sub_add_left, pointToPoint_timeShift]

/-- Subtract the same initial clock from both endpoints of a profile pairing. -/
theorem profileP2Fun_timeShift_sub (β : ℝ) {d a b : ℕ} (hda : d ≤ a) (hdb : d ≤ b)
    (ν f : Site → ℝ) (ω : Disorder) :
    profileP2Fun β a b ν f ω = profileP2Fun β (a - d) (b - d) ν f (shiftEnvironment d ω) := by
  have h := profileP2Fun_timeShift β d (a - d) (b - d) ν f ω
  simpa only [Nat.add_sub_of_le hda, Nat.add_sub_of_le hdb] using h

end Critical2DKPZ.Smoothing

end
