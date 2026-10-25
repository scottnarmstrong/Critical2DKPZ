/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.PositiveChainBlockTests
import Critical2DKPZ.SHF.Tsai.ProductMeasureKernels
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-! # Measurability of the endpoint test obtained by isolating a chain block

A finite product kernel represents the remaining path coordinates. The
signed path integrand is jointly measurable, so kernel integration makes
the isolated endpoint test measurable in both the outer sample and endpoints.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The isolated block test is jointly measurable for measurable locally finite outer blocks. -/
theorem measurable_positiveChainBlockTest {Ω : Type*} [MeasurableSpace Ω] (K : ℕ)
    (j : Fin (K + 1)) (B : ℕ → Ω → Measure (Plane × Plane))
    (hB : ∀ k ≤ K, Measurable (B k))
    (hlf : ∀ ω, ∀ k ≤ K, IsLocallyFiniteMeasure (B k ω))
    (w : ℕ → Plane → ℝ) (hw : ∀ k, Measurable (w k))
    (F : Plane × Plane → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun q : Ω × (Plane × Plane) => positiveChainBlockTest K j (fun k => B k q.1) w F q.2) := by
  let κ (i : Fin K) : Kernel (Ω × (Plane × Plane)) (Plane × Plane) :=
    ⟨fun q => B (j.succAbove i) q.1,
      (hB (j.succAbove i) (Nat.le_of_lt_succ (j.succAbove i).is_lt)).comp measurable_fst⟩
  have hκ (i) : IsSFiniteKernel (κ i) := by
    apply isSFiniteKernel_of_locallyFinite
    intro q
    exact hlf q.1 _ (Nat.le_of_lt_succ (j.succAbove i).is_lt)
  have hsf (i) (q : Ω × (Plane × Plane)) : SigmaFinite (κ i q) := by
    let : IsLocallyFiniteMeasure (B (j.succAbove i) q.1) :=
      hlf q.1 _ (Nat.le_of_lt_succ (j.succAbove i).is_lt)
    change SigmaFinite (B (j.succAbove i) q.1)
    infer_instance
  obtain ⟨η, hη, hηeq⟩ := exists_piMeasureKernel K κ hκ hsf
  let : IsSFiniteKernel η := hη
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (K + 1) => Plane × Plane) j
  let J := chainPathTest K w F
  have hJ : Measurable J := measurable_chainPathTest K hw hF
  let Ψ (q : (Ω × (Plane × Plane)) × (Fin K → Plane × Plane)) := J (e.symm (q.1.2, q.2))
  have hΨ : Measurable Ψ :=
    Measurable.comp (g := J) (f := fun q : (Ω × (Plane × Plane)) × (Fin K → Plane × Plane) =>
      e.symm (q.1.2, q.2)) hJ
      (e.symm.measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  have hm := hΨ.lintegral_kernel_prod_right' (κ := η)
  have heq : (fun q : Ω × (Plane × Plane) => ∫⁻ p, Ψ (q, p) ∂η q) =
      fun q => positiveChainBlockTest K j (fun k => B k q.1) w F q.2 := by
    funext q
    rw [hηeq q]
    rfl
  rw [heq] at hm
  exact hm

end Critical2DKPZ.SHF.Tsai

end
