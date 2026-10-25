/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.CovarianceLimit
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic

/-! # Covariance and spatial integration -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.CovarianceKernel

private theorem abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  nlinarith [sq_nonneg (|x| - 1 / 2), sq_abs x]

/-- Integrability of a test-weighted field from a uniform pointwise second-moment bound. -/
theorem integrable_test_weighted_field_of_uniform_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] [IsProbabilityMeasure P]
    (X : Ω → Plane → ℝ) (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXmem : ∀ x, MemLp (fun ω => X ω x) 2 P) (B : ℝ)
    (hXsq : ∀ x, Integrable (fun ω => X ω x ^ 2) P ∧
      (∫ ω, X ω x ^ 2 ∂P) ≤ B)
    (f : Plane → ℝ) (hf : Measurable f) (hfAbs : Integrable (fun x => |f x|) volume) :
    Integrable (fun p : Ω × Plane => f p.2 * X p.1 p.2) (P.prod volume) := by
  let F : Ω × Plane → ℝ := fun p => f p.2 * X p.1 p.2
  have hF : Measurable F := by
    dsimp [F]
    exact (hf.comp measurable_snd).mul hX
  have hFsections (x : Plane) : Integrable (fun ω => F (ω, x)) P := by
    have hxi : Integrable (fun ω => X ω x) P := (hXmem x).integrable (by norm_num)
    simpa [F] using hxi.const_mul (f x)
  have hXabsInt (x : Plane) : Integrable (fun ω => |X ω x|) P := by
    have hmajor : Integrable (fun ω => X ω x ^ 2 + 1) P :=
      (hXsq x).1.add (integrable_const 1)
    have hmeas : AEStronglyMeasurable (fun ω => |X ω x|) P := by
      exact ((hX.comp (measurable_id.prodMk measurable_const)).abs).aestronglyMeasurable
    refine hmajor.mono' hmeas ?_
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_abs] using abs_le_sq_add_one (X ω x)
  have hXabsBound (x : Plane) : (∫ ω, |X ω x| ∂P) ≤ B + 1 := by
    calc
      _ ≤ ∫ ω, X ω x ^ 2 + 1 ∂P := by
        apply integral_mono (hXabsInt x) ((hXsq x).1.add (integrable_const 1))
        intro ω
        exact abs_le_sq_add_one (X ω x)
      _ = (∫ ω, X ω x ^ 2 ∂P) + 1 := by
        rw [integral_add ((hXsq x).1) (integrable_const 1)]
        simp
      _ ≤ B + 1 := add_le_add (hXsq x).2 le_rfl
  have hFnormStrong : StronglyMeasurable (fun p : Ω × Plane => ‖F p‖) := hF.norm.stronglyMeasurable
  have hFavgStrong : StronglyMeasurable (fun x : Plane => ∫ ω, ‖F (ω, x)‖ ∂P) := by
    simpa only [Function.uncurry_apply_pair] using hFnormStrong.integral_prod_left'
  have hFavgInt : Integrable (fun x : Plane => ∫ ω, ‖F (ω, x)‖ ∂P) volume := by
    have hmajor : Integrable (fun x : Plane => |f x| * (B + 1)) volume := by
      simpa [mul_comm] using hfAbs.const_mul (B + 1)
    refine hmajor.mono' hFavgStrong.aestronglyMeasurable ?_
    filter_upwards [] with x
    calc
      ‖∫ ω, ‖F (ω, x)‖ ∂P‖ = ∫ ω, |f x| * |X ω x| ∂P := by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        apply integral_congr_ae
        filter_upwards [] with ω
        simp [F, Real.norm_eq_abs]
      _ = |f x| * ∫ ω, |X ω x| ∂P := by
        rw [integral_const_mul]
      _ ≤ |f x| * (B + 1) := mul_le_mul_of_nonneg_left (hXabsBound x) (abs_nonneg _)
  apply (integrable_prod_iff' hF.aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall hFsections, hFavgInt⟩

/-- The two weighted point fields form an integrable product on probability space times the
two-point spatial space. The second-moment integral bound is included in the hypotheses. -/
private theorem integrable_test_pair_product_of_uniform_secondMoment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] [IsProbabilityMeasure P]
    (X : Ω → Plane → ℝ) (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXmem : ∀ x, MemLp (fun ω => X ω x) 2 P) (B : ℝ)
    (hXsq : ∀ x, Integrable (fun ω => X ω x ^ 2) P ∧
      (∫ ω, X ω x ^ 2 ∂P) ≤ B)
    (f g : Plane → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfAbs : Integrable (fun x => |f x|) volume)
    (hgAbs : Integrable (fun x => |g x|) volume) :
    Integrable (fun p : Ω × (Plane × Plane) =>
      (f p.2.1 * X p.1 p.2.1) * (g p.2.2 * X p.1 p.2.2))
      (P.prod (volume.prod volume)) := by
  let F : Ω × (Plane × Plane) → ℝ := fun p =>
    (f p.2.1 * X p.1 p.2.1) * (g p.2.2 * X p.1 p.2.2)
  have hπ₁ : QuasiMeasurePreserving
      (fun p : Ω × (Plane × Plane) => (p.1, p.2.1))
      (P.prod (volume.prod volume)) (P.prod volume) := by
    change QuasiMeasurePreserving (Prod.map id Prod.fst)
      (P.prod (volume.prod volume)) (P.prod volume)
    exact QuasiMeasurePreserving.prodMap (QuasiMeasurePreserving.id P)
      (quasiMeasurePreserving_fst (μ := volume) (ν := volume))
  have hπ₂ : QuasiMeasurePreserving
      (fun p : Ω × (Plane × Plane) => (p.1, p.2.2))
      (P.prod (volume.prod volume)) (P.prod volume) := by
    change QuasiMeasurePreserving (Prod.map id Prod.snd)
      (P.prod (volume.prod volume)) (P.prod volume)
    exact QuasiMeasurePreserving.prodMap (QuasiMeasurePreserving.id P)
      (quasiMeasurePreserving_snd (μ := volume) (ν := volume))
  have hF : AEStronglyMeasurable F (P.prod (volume.prod volume)) := by
    dsimp [F]
    exact (((hf.comp measurable_snd.fst).aestronglyMeasurable.mul
      (hX.aestronglyMeasurable.comp_quasiMeasurePreserving hπ₁)).mul
      ((hg.comp measurable_snd.snd).aestronglyMeasurable.mul
        (hX.aestronglyMeasurable.comp_quasiMeasurePreserving hπ₂)))
  have hsection (x y : Plane) : Integrable (fun ω =>
      (f x * X ω x) * (g y * X ω y)) P := by
    have hholder : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) 1 := Real.HolderConjugate.two_two.ennrealOfReal
    have hleft : MemLp (fun ω => f x * X ω x) (ENNReal.ofReal (2 : ℝ)) P := by
      simpa [mul_comm] using (hXmem x).const_mul (f x)
    have hright : MemLp (fun ω => g y * X ω y) (ENNReal.ofReal (2 : ℝ)) P := by
      simpa [mul_comm] using (hXmem y).const_mul (g y)
    have hprod : MemLp (fun ω => (f x * X ω x) * (g y * X ω y)) 1 P := by
      simpa only [ENNReal.ofReal_ofNat, mul_comm] using hleft.fun_mul hright
    exact hprod.integrable (by norm_num)
  have hmeanNormAEStrong : AEStronglyMeasurable (fun p : Plane × Plane =>
      ∫ ω, ‖F (ω, p)‖ ∂P) (volume.prod volume) := by
    exact hF.norm.prod_swap.integral_prod_right'
  have hmeanNormBound (x y : Plane) :
      (∫ ω, ‖F (ω, (x, y))‖ ∂P) ≤ |f x| * |g y| * (2 * B) := by
    have hprodInt : Integrable (fun ω => X ω x * X ω y) P := by
      have hholder : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
          (ENNReal.ofReal (2 : ℝ)) 1 := Real.HolderConjugate.two_two.ennrealOfReal
      have hleft : MemLp (fun ω => X ω x) (ENNReal.ofReal (2 : ℝ)) P := by
        simpa using hXmem x
      have hright : MemLp (fun ω => X ω y) (ENNReal.ofReal (2 : ℝ)) P := by
        simpa using hXmem y
      have hprod : MemLp (fun ω => X ω x * X ω y) 1 P := by
        simpa only [ENNReal.ofReal_ofNat] using hleft.fun_mul hright
      exact hprod.integrable (by norm_num)
    have hmajor : Integrable (fun ω => X ω x ^ 2 + X ω y ^ 2) P :=
      (hXsq x).1.add (hXsq y).1
    have hpt (ω : Ω) : |X ω x * X ω y| ≤ X ω x ^ 2 + X ω y ^ 2 := by
      rw [abs_mul]
      have h := sq_nonneg (|X ω x| - |X ω y|)
      nlinarith [sq_abs (X ω x), sq_abs (X ω y)]
    have habs : (∫ ω, |X ω x * X ω y| ∂P) ≤ 2 * B := by
      calc
        _ ≤ ∫ ω, X ω x ^ 2 + X ω y ^ 2 ∂P :=
          integral_mono hprodInt.abs hmajor hpt
        _ = (∫ ω, X ω x ^ 2 ∂P) + ∫ ω, X ω y ^ 2 ∂P :=
          integral_add (hXsq x).1 (hXsq y).1
        _ ≤ B + B := add_le_add (hXsq x).2 (hXsq y).2
        _ = 2 * B := by ring
    calc
      ∫ ω, ‖F (ω, (x, y))‖ ∂P =
          ∫ ω, |f x| * |g y| * |X ω x * X ω y| ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp only [F, Real.norm_eq_abs, abs_mul]
        ring
      _ = |f x| * |g y| * ∫ ω, |X ω x * X ω y| ∂P := by
        rw [integral_const_mul]
      _ ≤ |f x| * |g y| * (2 * B) := by
        exact mul_le_mul_of_nonneg_left habs
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hbound : Integrable (fun p : Plane × Plane =>
      |f p.1| * |g p.2| * (2 * B)) (volume.prod volume) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hfAbs.mul_prod hgAbs).const_mul (2 * B)
  have hmeanNormInt : Integrable (fun p : Plane × Plane =>
      ∫ ω, ‖F (ω, p)‖ ∂P) (volume.prod volume) := by
    refine hbound.mono' hmeanNormAEStrong ?_
    filter_upwards [] with p
    have hnonneg : 0 ≤ ∫ ω, ‖F (ω, p)‖ ∂P := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    exact hmeanNormBound p.1 p.2
  exact (integrable_prod_iff' hF).2
    ⟨Filter.Eventually.of_forall (fun p => hsection p.1 p.2), hmeanNormInt⟩

/-- A jointly measurable field with a uniform pointwise second moment has the expected covariance
formula after testing in space. The right-hand test-kernel integral is asserted integrable. -/
theorem covariance_test_integral_eq_of
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] [IsProbabilityMeasure P]
    (X : Ω → Plane → ℝ) (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hXmem : ∀ x, MemLp (fun ω => X ω x) 2 P) (B : ℝ)
    (hXsq : ∀ x, Integrable (fun ω => X ω x ^ 2) P ∧
      (∫ ω, X ω x ^ 2 ∂P) ≤ B)
    (hzero : ∀ x, (∫ ω, X ω x ∂P) = 0)
    (f g : Plane → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfAbs : Integrable (fun x => |f x|) volume)
    (hgAbs : Integrable (fun x => |g x|) volume) :
    MemLp (fun ω => ∫ x, f x * X ω x) 2 P ∧
      MemLp (fun ω => ∫ x, g x * X ω x) 2 P ∧
      Integrable (fun p : Plane × Plane =>
        f p.1 * g p.2 * cov[fun ω => X ω p.1, fun ω => X ω p.2; P]) (volume.prod volume) ∧
      cov[fun ω => ∫ x, f x * X ω x, fun ω => ∫ x, g x * X ω x; P] =
        ∫ p : Plane × Plane,
          f p.1 * g p.2 * cov[fun ω => X ω p.1, fun ω => X ω p.2; P] := by
  let F : Ω × Plane → ℝ := fun p => f p.2 * X p.1 p.2
  let G : Ω × Plane → ℝ := fun p => g p.2 * X p.1 p.2
  let IF : Ω → ℝ := fun ω => ∫ x, F (ω, x) ∂volume
  let IG : Ω → ℝ := fun ω => ∫ x, G (ω, x) ∂volume
  have hFint := integrable_test_weighted_field_of_uniform_secondMoment P X hX hXmem B hXsq
    f hf hfAbs
  have hGint := integrable_test_weighted_field_of_uniform_secondMoment P X hX hXmem B hXsq
    g hg hgAbs
  have hFFint := integrable_test_pair_product_of_uniform_secondMoment P X hX hXmem B hXsq
    f f hf hf hfAbs hfAbs
  have hFGint := integrable_test_pair_product_of_uniform_secondMoment P X hX hXmem B hXsq
    f g hf hg hfAbs hgAbs
  have hGGint := integrable_test_pair_product_of_uniform_secondMoment P X hX hXmem B hXsq
    g g hg hg hgAbs hgAbs
  have hFsection : ∀ᵐ ω ∂P, Integrable (fun x => F (ω, x)) volume :=
    hFint.prod_right_ae
  have hGsection : ∀ᵐ ω ∂P, Integrable (fun x => G (ω, x)) volume :=
    hGint.prod_right_ae
  have hIFstrong : AEStronglyMeasurable IF P := by
    simpa only [IF, Function.uncurry_apply_pair] using hFint.aestronglyMeasurable.integral_prod_right'
  have hIGstrong : AEStronglyMeasurable IG P := by
    simpa only [IG, Function.uncurry_apply_pair] using hGint.aestronglyMeasurable.integral_prod_right'
  have hIFint : Integrable IF P := by simpa only [IF] using hFint.integral_prod_left
  have hIGint : Integrable IG P := by simpa only [IG] using hGint.integral_prod_left
  have hIFzero : (∫ ω, IF ω ∂P) = 0 := by
    calc
      _ = ∫ p : Ω × Plane, F p ∂(P.prod volume) := (integral_prod _ hFint).symm
      _ = ∫ x, ∫ ω, F (ω, x) ∂P ∂volume := integral_prod_symm F hFint
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [] with x
        change (∫ ω, f x * X ω x ∂P) = 0
        rw [integral_const_mul, hzero x, mul_zero]
  have hIGzero : (∫ ω, IG ω ∂P) = 0 := by
    calc
      _ = ∫ p : Ω × Plane, G p ∂(P.prod volume) := (integral_prod _ hGint).symm
      _ = ∫ x, ∫ ω, G (ω, x) ∂P ∂volume := integral_prod_symm G hGint
      _ = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [] with x
        change (∫ ω, g x * X ω x ∂P) = 0
        rw [integral_const_mul, hzero x, mul_zero]
  have hFMem : MemLp IF 2 P := by
    have hFFavg : Integrable (fun ω => ∫ p : Plane × Plane,
        (f p.1 * X ω p.1) * (f p.2 * X ω p.2) ∂(volume.prod volume)) P := by
      simpa only [F, Function.uncurry_apply_pair] using hFFint.integral_prod_left
    have hFFsection : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        (f p.1 * X ω p.1) * (f p.2 * X ω p.2)) (volume.prod volume) :=
      hFFint.prod_right_ae
    have hsq : Integrable (fun ω => IF ω ^ 2) P := by
      refine hFFavg.congr ?_
      filter_upwards [hFsection, hFFsection] with ω hω hpair
      have heq : IF ω ^ 2 = ∫ p : Plane × Plane,
          (f p.1 * X ω p.1) * (f p.2 * X ω p.2) ∂(volume.prod volume) := by
        rw [pow_two]
        exact (integral_prod_mul (μ := volume) (ν := volume)
          (fun x => f x * X ω x) (fun x => f x * X ω x)).symm
      exact heq.symm
    exact (memLp_two_iff_integrable_sq hIFstrong).2 hsq
  have hGMem : MemLp IG 2 P := by
    have hGGavg : Integrable (fun ω => ∫ p : Plane × Plane,
        (g p.1 * X ω p.1) * (g p.2 * X ω p.2) ∂(volume.prod volume)) P := by
      simpa only [G, Function.uncurry_apply_pair] using hGGint.integral_prod_left
    have hGGsection : ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        (g p.1 * X ω p.1) * (g p.2 * X ω p.2)) (volume.prod volume) :=
      hGGint.prod_right_ae
    have hsq : Integrable (fun ω => IG ω ^ 2) P := by
      refine hGGavg.congr ?_
      filter_upwards [hGsection, hGGsection] with ω hω hpair
      have heq : IG ω ^ 2 = ∫ p : Plane × Plane,
          (g p.1 * X ω p.1) * (g p.2 * X ω p.2) ∂(volume.prod volume) := by
        rw [pow_two]
        exact (integral_prod_mul (μ := volume) (ν := volume)
          (fun x => g x * X ω x) (fun x => g x * X ω x)).symm
      exact heq.symm
    exact (memLp_two_iff_integrable_sq hIGstrong).2 hsq
  have hcrossMem : MemLp (fun ω => IF ω * IG ω) 1 P := by
    have hholder : ENNReal.HolderTriple (ENNReal.ofReal (2 : ℝ))
        (ENNReal.ofReal (2 : ℝ)) 1 := Real.HolderConjugate.two_two.ennrealOfReal
    change MemLp (IF * IG) 1 P
    simpa only [ENNReal.ofReal_ofNat] using hFMem.mul hGMem
  have hcross : Integrable (fun ω => IF ω * IG ω) P := hcrossMem.integrable (by norm_num)
  have hAint := hFGint.integral_prod_right
  have hcrossEq : (∫ ω, IF ω * IG ω ∂P) =
      ∫ p : Plane × Plane, ∫ ω,
        (f p.1 * X ω p.1) * (g p.2 * X ω p.2) ∂P ∂(volume.prod volume) := by
    calc
      _ = ∫ ω, ∫ p : Plane × Plane,
          (f p.1 * X ω p.1) * (g p.2 * X ω p.2) ∂(volume.prod volume) ∂P := by
        apply integral_congr_ae
        filter_upwards [hFsection, hGsection, hFGint.prod_right_ae] with ω hfw hgw hp
        have heq : IF ω * IG ω = ∫ p : Plane × Plane,
            (f p.1 * X ω p.1) * (g p.2 * X ω p.2) ∂(volume.prod volume) := by
          exact (integral_prod_mul (μ := volume) (ν := volume)
            (fun x => f x * X ω x) (fun y => g y * X ω y)).symm
        exact heq
      _ = ∫ p : Plane × Plane, ∫ ω,
          (f p.1 * X ω p.1) * (g p.2 * X ω p.2) ∂P ∂(volume.prod volume) :=
        integral_integral_swap hFGint
  have hpoint (p : Plane × Plane) :
      (∫ ω, (f p.1 * X ω p.1) * (g p.2 * X ω p.2) ∂P) =
        f p.1 * g p.2 * cov[fun ω => X ω p.1, fun ω => X ω p.2; P] := by
    have hcov := covariance_eq_sub (hXmem p.1) (hXmem p.2)
    rw [hcov, hzero p.1, hzero p.2]
    simp only [mul_zero, sub_zero, Pi.mul_apply]
    rw [show (fun ω => (f p.1 * X ω p.1) * (g p.2 * X ω p.2)) =
        fun ω => (f p.1 * g p.2) * (X ω p.1 * X ω p.2) by
      funext ω
      ring,
      integral_const_mul]
  have hcovsqInt : Integrable (fun p : Plane × Plane =>
      f p.1 * g p.2 * cov[fun ω => X ω p.1, fun ω => X ω p.2; P])
      (volume.prod volume) := by
    refine hAint.congr ?_
    filter_upwards [] with p
    simpa only [Function.uncurry_apply_pair] using hpoint p
  have hEq : cov[IF, IG; P] =
      ∫ p : Plane × Plane,
        f p.1 * g p.2 * cov[fun ω => X ω p.1, fun ω => X ω p.2; P] := by
    rw [covariance_eq_sub hFMem hGMem, hIFzero, hIGzero, mul_zero, sub_zero]
    change (∫ ω, IF ω * IG ω ∂P) = _
    rw [hcrossEq]
    exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
  refine ⟨?_, ?_, hcovsqInt, ?_⟩
  · simpa only [F, IF] using hFMem
  · simpa only [G, IG] using hGMem
  · simpa only [F, G, IF, IG] using hEq

end Critical2DKPZ.CovarianceKernel

end
