/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TaylorRemainderIntegration
import Mathlib.MeasureTheory.Integral.Prod

/-! # Taylor replacement after conditioning on the outer blocks

At each outer sample the base point is fixed. Matching integrable cubic
coordinate moments then bounds the conditional nonlinear expectation.
Fubini and the global fourth moments integrate that bound, retaining the
exact factor `1/24` and both nonlinear integrability clauses.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Conditional cubic moment matching gives the integrated fourth-order replacement estimate. -/
theorem abs_integral_conditional_add_sub_le {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {m : ℕ}
    (A : Ω' → Fin m → ℝ) (hAm : AEStronglyMeasurable A P')
    (X Y : Ω' × Ω → Fin m → ℝ)
    (hXm : AEStronglyMeasurable X (P'.prod P)) (hYm : AEStronglyMeasurable Y (P'.prod P))
    (hX4 : Integrable (fun ω => ∑ i, X ω i ^ 4) (P'.prod P))
    (hY4 : Integrable (fun ω => ∑ i, Y ω i ^ 4) (P'.prod P))
    (hmatch : ∀ᵐ a ∂P', ∀ k ≤ 3, ∀ q : Fin k → Fin m,
      Integrable (fun ω => ∏ i, X (a, ω) (q i)) P ∧
      Integrable (fun ω => ∏ i, Y (a, ω) (q i)) P ∧
      (∫ ω, ∏ i, X (a, ω) (q i) ∂P) = ∫ ω, ∏ i, Y (a, ω) (q i) ∂P)
    (H : (Fin m → ℝ) → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hH0 : ∀ z, ‖H z‖ ≤ CH) (hCH : ∀ z, ‖iteratedFDeriv ℝ 4 H z‖ ≤ CH) :
    Integrable (fun ω => H (A ω.1 + X ω)) (P'.prod P) ∧
    Integrable (fun ω => H (A ω.1 + Y ω)) (P'.prod P) ∧
    |(∫ ω, H (A ω.1 + X ω) ∂P'.prod P) - ∫ ω, H (A ω.1 + Y ω) ∂P'.prod P| ≤
      CH / 24 * ((∫ ω, ∑ i, X ω i ^ 4 ∂P'.prod P) + ∫ ω, ∑ i, Y ω i ^ 4 ∂P'.prod P) := by
  let F (ω : Ω' × Ω) := H (A ω.1 + X ω)
  let G (ω : Ω' × Ω) := H (A ω.1 + Y ω)
  have hFm : AEStronglyMeasurable F (P'.prod P) :=
    hH.continuous.comp_aestronglyMeasurable (hAm.comp_fst.add hXm)
  have hGm : AEStronglyMeasurable G (P'.prod P) :=
    hH.continuous.comp_aestronglyMeasurable (hAm.comp_fst.add hYm)
  have hFI : Integrable F (P'.prod P) :=
    Integrable.of_bound hFm CH (Filter.Eventually.of_forall (fun ω => hH0 _))
  have hGI : Integrable G (P'.prod P) :=
    Integrable.of_bound hGm CH (Filter.Eventually.of_forall (fun ω => hH0 _))
  let Δ (a : Ω') := (∫ ω, F (a, ω) ∂P) - ∫ ω, G (a, ω) ∂P
  let FX (a : Ω') := ∫ ω, ∑ i, X (a, ω) i ^ 4 ∂P
  let FY (a : Ω') := ∫ ω, ∑ i, Y (a, ω) i ^ 4 ∂P
  have hΔI : Integrable Δ P' := hFI.integral_prod_left.sub hGI.integral_prod_left
  have hdomI : Integrable (fun a => CH / 24 * (FX a + FY a)) P' :=
    (hX4.integral_prod_left.add hY4.integral_prod_left).const_mul _
  have hpoint : ∀ᵐ a ∂P', |Δ a| ≤ CH / 24 * (FX a + FY a) := by
    filter_upwards [hmatch, hXm.prodMk_left, hYm.prodMk_left,
      hX4.prod_right_ae, hY4.prod_right_ae] with a ha hXa hYa hXIa hYIa
    have h := abs_integral_add_sub_le_of_cubic_coordinate_moments P P
      (fun ω => X (a, ω)) (fun ω => Y (a, ω)) hXa hYa hXIa hYIa
      (fun k hk q => (ha k hk q).1) (fun k hk q => (ha k hk q).2.1)
      (fun k hk q => (ha k hk q).2.2) H hH CH hCH (A a)
    exact h.2.2
  have hbound := (abs_integral_le_integral_abs (f := Δ)).trans
    (integral_mono_ae hΔI.abs hdomI hpoint)
  rw [integral_const_mul, integral_add hX4.integral_prod_left hY4.integral_prod_left] at hbound
  have hglobal : (∫ ω, F ω ∂P'.prod P) - (∫ ω, G ω ∂P'.prod P) = ∫ a, Δ a ∂P' := by
    rw [integral_prod _ hFI, integral_prod _ hGI]
    exact (integral_sub hFI.integral_prod_left hGI.integral_prod_left).symm
  refine ⟨hFI, hGI, ?_⟩
  change |(∫ ω, F ω ∂P'.prod P) - (∫ ω, G ω ∂P'.prod P)| ≤ _
  rw [hglobal]
  exact hbound.trans_eq (by rw [integral_prod _ hX4, integral_prod _ hY4])

end Critical2DKPZ.SHF.Tsai

end
