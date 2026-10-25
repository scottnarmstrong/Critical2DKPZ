/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.IdentDistrib
import Mathlib.Tactic

/-! # Reindexing finite-dimensional real laws -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Laws supplied for every `Fin k` family determine the law on any finite
index type. Measurability is explicit on both sides. -/
theorem map_fintype_eq_of_fin_laws {Ω Ω' I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I]
    (P : Measure Ω) (Q : Measure Ω') (X : Ω → I → ℝ) (Y : Ω' → I → ℝ)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (hLaw : ∀ k : ℕ, ∀ f : Fin k → I,
      P.map (fun ω j => X ω (f j)) = Q.map (fun ω j => Y ω (f j))) :
    P.map X = Q.map Y := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let g : (Fin (Fintype.card I) → ℝ) → I → ℝ := fun v i => v (e.symm i)
  have hg : Measurable g := by fun_prop
  have hXm : AEMeasurable (fun ω j => X ω (e j)) P :=
    aemeasurable_pi_iff.mpr fun j => (aemeasurable_pi_iff.mp hX) (e j)
  have hYm : AEMeasurable (fun ω j => Y ω (e j)) Q :=
    aemeasurable_pi_iff.mpr fun j => (aemeasurable_pi_iff.mp hY) (e j)
  have hx : (P.map (fun ω j => X ω (e j))).map g = P.map X := by
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hXm]
    congr 1
    funext ω i
    simp only [Function.comp_def, g, Equiv.apply_symm_apply]
  have hy : (Q.map (fun ω j => Y ω (e j))).map g = Q.map Y := by
    rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hYm]
    congr 1
    funext ω i
    simp only [Function.comp_def, g, Equiv.apply_symm_apply]
  exact hx.symm.trans ((congrArg (fun μ : Measure (Fin (Fintype.card I) → ℝ) => μ.map g)
    (hLaw (Fintype.card I) e)).trans hy)

/-- Dividing every coordinate by the same deterministic scalar preserves a law identity. -/
theorem map_div_family_eq {Ω Ω' I : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype I]
    (P : Measure Ω) (Q : Measure Ω') (X : Ω → I → ℝ) (Y : Ω' → I → ℝ)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y Q)
    (hLaw : P.map X = Q.map Y) (c : ℝ) :
    P.map (fun ω i => X ω i / c) = Q.map (fun ω i => Y ω i / c) := by
  have h : ProbabilityTheory.IdentDistrib X Y P Q := ⟨hX, hY, hLaw⟩
  have hg : Measurable (fun v : I → ℝ => fun i => v i / c) := by fun_prop
  simpa only [Function.comp_def] using (h.comp hg).map_eq

end Critical2DKPZ.Extensions.ScaleLimit
