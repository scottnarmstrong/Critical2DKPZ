/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelOperator

/-! # Symmetry of bounded configuration-kernel operators

Endpoint symmetry of the literal positive kernel passes to the bounded L²
operator by product-variable exchange in its absolutely integrable form.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A symmetric positive kernel gives the symmetric bounded L² operator pairing. -/
theorem inner_configurationKernelOperator_symm {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hQ : FormBound volume volume K c) (hSymm : ∀ x y, K x y = K y x)
    (F G : Lp ℝ 2 (volume : Measure (Configuration n))) :
    ⟪configurationKernelOperator hK hc hQ F, G⟫_ℝ =
      ⟪F, configurationKernelOperator hK hc hQ G⟫_ℝ := by
  calc
    _ = ∫ q : Configuration n × Configuration n,
        G q.1 * (K q.1 q.2).toReal * F q.2 ∂volume.prod volume :=
      inner_configurationKernelOperator hK hc hQ G F
    _ = ∫ q : Configuration n × Configuration n,
        G q.2 * (K q.2 q.1).toReal * F q.1 ∂volume.prod volume :=
      integral_prod_swap (fun q : Configuration n × Configuration n =>
        G q.2 * (K q.2 q.1).toReal * F q.1)
    _ = ∫ q : Configuration n × Configuration n,
        F q.1 * (K q.1 q.2).toReal * G q.2 ∂volume.prod volume := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      change G q.2 * (K q.2 q.1).toReal * F q.1 = F q.1 * (K q.1 q.2).toReal * G q.2
      rw [hSymm q.2 q.1]
      ring
    _ = ⟪configurationKernelOperator hK hc hQ G, F⟫_ℝ :=
      (inner_configurationKernelOperator hK hc hQ F G).symm
    _ = _ := real_inner_comm _ _

end Critical2DKPZ.SHF.Tsai

end
