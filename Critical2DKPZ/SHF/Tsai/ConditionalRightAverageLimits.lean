/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.FiberwiseProbabilityLimits
public import Critical2DKPZ.SHF.Tsai.WeightedBlockTests
public import Critical2DKPZ.SHF.Tsai.ProductTensorAverages

/-! # Appending an independent block at a fixed connector

Convergence in probability on deterministic `L²` endpoint tests is preserved by appending
an independent block through a fixed mollifier and conditioning on that block.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Convergence of inner tensor tests passes to products with an independent right block at a fixed connector. -/
theorem tendstoInMeasure_smoothedProduct_right_of_tensor_limits {θ τ : ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (C : ℕ → Ω → Measure (Plane × Plane)) (D : Ω → Measure (Plane × Plane))
    (hClf : ∀ n, ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (C n ω))
    (hDlf : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (D ω))
    (A : Ω' → Measure (Plane × Plane)) (hA : HasDeltaBoseMoments θ τ P' A) (hτ : 0 < τ)
    (w : Plane → ℝ) (hw : ∀ x, 0 ≤ w x) (hwm : Measurable w) (hw2 : MemLp w 2)
    (g g' : C_c(Plane, ℝ))
    (hconv : ∀ f : Plane → ℝ, MemLp f 2 →
      TendstoInMeasure P (fun n ω => ∫ p, g p.1 * f p.2 ∂C n ω) atTop
        (fun ω => ∫ p, g p.1 * f p.2 ∂D ω))
    (hXm : ∀ n, AEStronglyMeasurable (fun q : Ω' × Ω => ∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure (C n q.2) w (A q.1)) (P'.prod P))
    (hYm : AEStronglyMeasurable (fun q : Ω' × Ω => ∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure (D q.2) w (A q.1)) (P'.prod P))
    (hXI : ∀ n, ∀ᵐ q : Ω' × Ω ∂P'.prod P, Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (smoothedProductMeasure (C n q.2) w (A q.1)))
    (hYI : ∀ᵐ q : Ω' × Ω ∂P'.prod P, Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (smoothedProductMeasure (D q.2) w (A q.1))) :
    TendstoInMeasure (P'.prod P) (fun n q => ∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure (C n q.2) w (A q.1)) atTop
        (fun q => ∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure (D q.2) w (A q.1)) := by
  have hXRows : ∀ᵐ a ∂P', ∀ n, ∀ᵐ ω ∂P,
      Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
        (smoothedProductMeasure (C n ω) w (A a)) :=
    ae_all_iff.2 fun n => Measure.ae_ae_of_ae_prod (hXI n)
  have hYRows : ∀ᵐ a ∂P', ∀ᵐ ω ∂P,
      Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
        (smoothedProductMeasure (D ω) w (A a)) := Measure.ae_ae_of_ae_prod hYI
  have htests : ∀ᵐ a ∂P', MemLp (fun y => ∫ p, w (y - p.1) * g' p.2 ∂A a) 2 :=
    (hA.ae_memLp_weighted_right_test hτ g' w hwm hw2).mono (fun _ h => h.1)
  apply tendstoInMeasure_prod_of_fiberwise_ae P P' _ _ hXm hYm
  filter_upwards [hA.2.1, htests, hXRows, hYRows] with a ha htest hXa hYa
  let : IsLocallyFiniteMeasure (A a) := ha
  let f (y : Plane) := ∫ p, w (y - p.1) * g' p.2 ∂A a
  have hleft (n : ℕ) : (fun ω => ∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure (C n ω) w (A a)) =ᵐ[P]
      fun ω => ∫ p, g p.1 * f p.2 ∂C n ω := by
    filter_upwards [hXa n, hClf n] with ω hω hLF
    let : IsLocallyFiniteMeasure (C n ω) := hLF
    exact (integral_smoothedProduct_tensor_eq_right_average (C n ω) (A a) w hw hwm g g'
      g.continuous.measurable g'.continuous.measurable hω).2
  have hright : (fun ω => ∫ p, g p.1 * g' p.2 ∂smoothedProductMeasure (D ω) w (A a)) =ᵐ[P]
      fun ω => ∫ p, g p.1 * f p.2 ∂D ω := by
    filter_upwards [hYa, hDlf] with ω hω hLF
    let : IsLocallyFiniteMeasure (D ω) := hLF
    exact (integral_smoothedProduct_tensor_eq_right_average (D ω) (A a) w hw hwm g g'
      g.continuous.measurable g'.continuous.measurable hω).2
  exact (hconv f htest).congr (fun n => (hleft n).symm) hright.symm

end Critical2DKPZ.SHF.Tsai

end
