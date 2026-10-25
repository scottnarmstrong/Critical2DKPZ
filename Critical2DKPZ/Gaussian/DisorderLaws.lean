/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
public import Critical2DKPZ.Gaussian.Poincare
public import Mathlib.Probability.Independence.InfinitePi

/-! The product disorder law has Gaussian coordinate marginals and spatial symmetries. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.Gaussian

/-- Every disorder coordinate is measurable in the product sigma-field. -/
theorem measurable_disorder_eval (p : ℕ × Site) :
    Measurable (fun ω : Disorder => ω p) := measurable_pi_apply p

/-- Every disorder coordinate has the standard normal law, including measurability. -/
theorem hasLaw_disorder_eval (p : ℕ × Site) :
    HasLaw (fun ω : Disorder => ω p) (gaussianReal 0 1) disorderLaw where
  aemeasurable := (measurable_disorder_eval p).aemeasurable
  map_eq := Measure.infinitePi_map_eval (fun _ => gaussianReal 0 1) p

/-- The entire coordinate family is independent. -/
theorem iIndepFun_disorder_eval :
    iIndepFun (fun p (ω : Disorder) => ω p) disorderLaw :=
  iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)


/-- Reindexing a disorder sample by a permutation. -/
def reindexDisorder (e : (ℕ × Site) ≃ (ℕ × Site)) (ω : Disorder) : Disorder :=
  fun p => ω (e p)

/-- All permutations of the index set preserve the disorder law. -/
theorem measurePreserving_reindexDisorder (e : (ℕ × Site) ≃ (ℕ × Site)) :
    MeasurePreserving (reindexDisorder e) disorderLaw disorderLaw where
  measurable := measurable_pi_iff.mpr fun p => measurable_disorder_eval (e p)
  map_eq := by
    have he : (Equiv.piCongrLeft (fun _ : ℕ × Site => ℝ) e.symm : Disorder → Disorder) =
        reindexDisorder e := by
      funext ω p
      simp only [Equiv.piCongrLeft_apply_eq_cast, Equiv.symm_symm, cast_eq, reindexDisorder]
    rw [← he]
    exact Measure.infinitePi_map_piCongrLeft (fun _ : ℕ × Site => gaussianReal 0 1) e.symm

/-- Spatial translation of space-time indices, with time fixed. -/
def spatialTranslation (w : Site) : (ℕ × Site) ≃ (ℕ × Site) where
  toFun p := (p.1, p.2 + w)
  invFun p := (p.1, p.2 - w)
  left_inv p := by
    apply Prod.ext
    · rfl
    funext i
    exact add_sub_cancel_right (p.2 i) (w i)
  right_inv p := by
    apply Prod.ext
    · rfl
    funext i
    exact sub_add_cancel (p.2 i) (w i)

/-- The disorder law is spatially translation invariant. -/
theorem measurePreserving_disorder_translation (w : Site) :
    MeasurePreserving (fun ω : Disorder => fun p => ω (p.1, p.2 + w))
      disorderLaw disorderLaw :=
  measurePreserving_reindexDisorder (spatialTranslation w)

end Critical2DKPZ.Gaussian

end
