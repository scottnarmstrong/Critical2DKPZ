/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabTensorTests
public import Critical2DKPZ.SHF.Tsai.Defs
public import Critical2DKPZ.SHF.Tsai.BlockTupleMeasures

/-! # Coordinate grouping for two independent replica blocks -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

/-- Reorder four replica endpoint pairs into two blocks of two replica configurations. -/
def slabSeparatedArrayEquiv :
    (Fin 2 → Configuration 2 × Configuration 2) ≃ (Fin 4 → Plane × Plane) where
  toFun z := ![
    ((z 0).1 0, (z 0).2 0), ((z 0).1 1, (z 0).2 1),
    ((z 1).1 0, (z 1).2 0), ((z 1).1 1, (z 1).2 1)]
  invFun q := ![
    ((![(q 0).1, (q 1).1] : Configuration 2), ![(q 0).2, (q 1).2]),
    ((![(q 2).1, (q 3).1] : Configuration 2), ![(q 2).2, (q 3).2])]
  left_inv z := by
    funext b
    fin_cases b
    · apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · funext i
        fin_cases i <;> rfl
    · apply Prod.ext
      · funext i
        fin_cases i <;> rfl
      · funext i
        fin_cases i <;> rfl
  right_inv q := by
    funext i
    fin_cases i <;> rfl

/-- The coordinate reordering is a homeomorphism. -/
def slabSeparatedArrayHomeomorph :
    (Fin 2 → Configuration 2 × Configuration 2) ≃ₜ (Fin 4 → Plane × Plane) := by
  refine ⟨slabSeparatedArrayEquiv, ?_, ?_⟩ <;> fun_prop

/-- Pulling a compact test back through the two-block coordinate reordering preserves compact support. -/
def slabSeparatedGroupedTest (F : C_c((Fin 4 → Plane × Plane), ℝ)) :
    C_c((Fin 2 → Configuration 2 × Configuration 2), ℝ) := by
  let e := slabSeparatedArrayHomeomorph
  let f : (Fin 2 → Configuration 2 × Configuration 2) → ℝ := fun z => F (e z)
  have hf : Continuous f := F.continuous.comp e.continuous
  refine ⟨⟨f, hf⟩, ?_⟩
  apply HasCompactSupport.of_support_subset_isCompact (F.hasCompactSupport.image e.symm.continuous)
  intro z hz
  refine ⟨e z, subset_tsupport _ hz, ?_⟩
  simp [e]

@[simp] theorem slabSeparatedGroupedTest_apply
    (F : C_c((Fin 4 → Plane × Plane), ℝ))
    (z : Fin 2 → Configuration 2 × Configuration 2) :
    slabSeparatedGroupedTest F z = F (slabSeparatedArrayHomeomorph z) := rfl

end Critical2DKPZ.SHF.Flow

end
