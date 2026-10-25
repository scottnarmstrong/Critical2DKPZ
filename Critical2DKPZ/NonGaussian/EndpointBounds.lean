/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointOne
public import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Uniform bounds for centered endpoint perturbations -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.JointConvergence Critical2DKPZ.SHF.Positivity
open Critical2DKPZ.LocalSobolev
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- For `0 < c ≤ f ≤ C` and a nonnegative spatial test of integral one, the separately centered
log fields for terminals `f` and `1` differ almost surely by at most `log (C/c)`; see KPZ (9.5). -/
theorem avgLogField_sub_le_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (_hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (ψ : TestFn)
    (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (f : Plane →ᵇ ℝ) {c C : ℝ} (hc : 0 < c)
    (hf : ∀ y, c ≤ f y ∧ f y ≤ C) :
    ∀ᵐ ω ∂P, |avgLogField P Z r t ψ f ω -
      avgLogField P Z r t ψ (fun _ => 1) ω| ≤ Real.log (C / c) := by
  let one : Plane →ᵇ ℝ := 1
  let K : Plane → Plane → ℝ := fun x y => heatKernel r (y - x)
  let Gf : Plane × Ω → ℝ := fun q => Real.log
    (shfPairing Z r t (fun y => K q.1 y) f q.2)
  let G1 : Plane × Ω → ℝ := fun q => Real.log
    (shfPairing Z r t (fun y => K q.1 y) (fun _ => (1 : ℝ)) q.2)
  let D : Plane × Ω → ℝ := fun q => Gf q - G1 q
  let mf : Plane → ℝ := fun x => ∫ ω, Gf (x, ω) ∂P
  let m1 : Plane → ℝ := fun x => ∫ ω, G1 (x, ω) ∂P
  let J : Plane × Ω → ℝ := fun q => ψ q.1 *
    ((Gf q - mf q.1) - (G1 q - m1 q.1))
  have hcC : c ≤ C := (hf 0).1.trans (hf 0).2
  have hC : 0 < C := hc.trans_le hcC
  have hlogcC : Real.log c ≤ Real.log C := Real.log_le_log hc hcC
  have hwidth : 0 ≤ Real.log C - Real.log c := sub_nonneg.mpr hlogcC
  have hwidthEq : Real.log C - Real.log c = Real.log (C / c) := by
    rw [Real.log_div hC.ne' hc.ne']
  have hlogf_cont : Continuous (fun y => Real.log (f y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le hc (hf y).1))).comp
      f.continuous.continuousAt
  let B : ℝ := max |Real.log c| |Real.log C|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlogf_bound (y : Plane) : |Real.log (f y)| ≤ B := by
    have hlow : Real.log c ≤ Real.log (f y) := Real.log_le_log hc (hf y).1
    have hupp : Real.log (f y) ≤ Real.log C :=
      Real.log_le_log (hc.trans_le (hf y).1) (hf y).2
    apply abs_le.mpr
    constructor
    · calc
        -B ≤ -|Real.log c| := by dsimp [B]; exact neg_le_neg (le_max_left _ _)
        _ ≤ Real.log c := neg_abs_le _
        _ ≤ Real.log (f y) := hlow
    · calc
        Real.log (f y) ≤ Real.log C := hupp
        _ ≤ B := le_trans (le_abs_self _) (le_max_right _ _)
  let h₀ : Plane →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.log (f y), hlogf_cont⟩ (2 * B) (by
      intro x y
      rw [Real.dist_eq]
      calc
        |Real.log (f x) - Real.log (f y)| ≤
            |Real.log (f x)| + |Real.log (f y)| := abs_sub _ _
        _ ≤ B + B := add_le_add (hlogf_bound x) (hlogf_bound y)
        _ = 2 * B := by ring)
  have h₀eq (y : Plane) : h₀ y = Real.log (f y) := by
    simp [h₀, BoundedContinuousFunction.mkOfBound_coe]
  have hexp₀ (y : Plane) : Real.exp (h₀ y) = f y := by
    rw [h₀eq]
    exact Real.exp_log (lt_of_lt_of_le hc (hf y).1)
  let μ : Ω → Measure (Plane × Plane) := Z r t
  have hμ : Measurable μ := hZ.1 r t hr.le hrt
  have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [(hZ.2.1 r t hr.le hrt).mono (fun ω hω => hω.1)] with ω hω
    exact hω
  have hgfnn : ∀ y, 0 ≤ f y := fun y =>
    le_of_lt (hc.trans_le (hf y).1)
  have hGf : AEMeasurable Gf (volume.prod P) := by
    exact aemeasurable_log_heatPairing_joint P μ hμ hlocal r hr
      f (f.continuous.measurable) hgfnn
  have hG1 : AEMeasurable G1 (volume.prod P) := by
    exact aemeasurable_log_heatPairing_joint P μ hμ hlocal r hr
      one (by fun_prop) (by intro y; norm_num)
  have hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane)
      (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2 ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P := by
    intro s t δ hs hst hδ x g
    exact isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  have hjoint := isCriticalSHF_heat_bounded_pairing_joint ϑ P Z hZ
  have hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P := by
    intro s t δ x h₀ hs hst hδ
    rcases hsym.2.2.2.2.2.2 s t δ x h₀ hs hst hδ with ⟨hp, hm, _⟩
    exact ⟨hp, hm⟩
  obtain ⟨Mf, hMf, hSqf₀⟩ := shf_heatStartLogField_square_bound
    ϑ P Z hZ hpair hjoint hpos t h₀ (s := r) (δ := r) hr.le hrt hr
  obtain ⟨M1, hM1, hSq1₀⟩ := shf_heatStartLogField_square_bound
    ϑ P Z hZ hpair hjoint hpos t (0 : Plane →ᵇ ℝ) (s := r) (δ := r) hr.le hrt hr
  have hSqf (x : Plane) : Integrable (fun ω => |Gf (x, ω)| ^ 2) P ∧
      ∫ ω, |Gf (x, ω)| ^ 2 ∂P ≤ Mf := by
    simpa [Gf, K, hexp₀] using hSqf₀ x
  have hSq1 (x : Plane) : Integrable (fun ω => |G1 (x, ω)| ^ 2) P ∧
      ∫ ω, |G1 (x, ω)| ^ 2 ∂P ≤ M1 := by
    simpa [G1, K, Real.exp_zero] using hSq1₀ x
  have hsecf (x : Plane) : AEStronglyMeasurable (fun ω => Gf (x, ω)) P := by
    have h := hsym.2.2.2.2.2.2 r t r x h₀ hr.le hrt hr
    have he (y : Plane) : Real.exp (h₀ y) = f y := hexp₀ y
    simpa [Gf, K, he] using h.2.1.aestronglyMeasurable
  have hsec1 (x : Plane) : AEStronglyMeasurable (fun ω => G1 (x, ω)) P := by
    have h := hsym.2.2.2.2.2.2 r t r x (0 : Plane →ᵇ ℝ) hr.le hrt hr
    simpa [G1, K, Real.exp_zero] using h.2.1.aestronglyMeasurable
  have hmemf (x : Plane) : MemLp (fun ω => Gf (x, ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq (hsecf x)).2
    simpa [sq_abs] using (hSqf x).1
  have hmem1 (x : Plane) : MemLp (fun ω => G1 (x, ω)) 2 P := by
    apply (memLp_two_iff_integrable_sq (hsec1 x)).2
    simpa [sq_abs] using (hSq1 x).1
  have hDint (x : Plane) : Integrable (fun ω => D (x, ω)) P := by
    exact (hmemf x).integrable (by norm_num) |>.sub ((hmem1 x).integrable (by norm_num))
  have hDrange (x : Plane) : ∀ᵐ ω ∂P,
      Real.log c ≤ D (x, ω) ∧ D (x, ω) ≤ Real.log C := by
    let A : Ω → ℝ := fun ω => shfPairing Z r t
      (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ)) ω
    let B : Ω → ℝ := fun ω => shfPairing Z r t
      (fun y => heatKernel r (y - x)) f ω
    have hp1 := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hr.le hrt hr x one
    have hpf := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hr.le hrt hr x f
    have hApos : ∀ᵐ ω ∂P, 0 < A ω := by
      have h := hsym.2.2.2.2.2.2 r t r x (0 : Plane →ᵇ ℝ) hr.le hrt hr
      simpa [A, Real.exp_zero] using h.1
    filter_upwards [hp1.1, hpf.1, hApos] with ω hI1 hIf hAp
    have hpointL (p : Plane × Plane) :
        c * (heatKernel r (p.1 - x) * one p.2) ≤
          heatKernel r (p.1 - x) * f p.2 := by
      simpa [one, mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left (hf p.2).1
        (heatKernel_nonneg hr.le (p.1 - x))
    have hpointU (p : Plane × Plane) :
        heatKernel r (p.1 - x) * f p.2 ≤
          C * (heatKernel r (p.1 - x) * one p.2) := by
      have hh := mul_le_mul_of_nonneg_left (hf p.2).2
        (heatKernel_nonneg hr.le (p.1 - x))
      simpa [one, mul_assoc, mul_left_comm, mul_comm] using hh
    have hlow : c * A ω ≤ B ω := by
      dsimp [A, B, shfPairing]
      calc
        c * ∫ p, heatKernel r (p.1 - x) * one p.2 ∂Z r t ω =
            ∫ p, c * (heatKernel r (p.1 - x) * one p.2) ∂Z r t ω := by
              rw [integral_const_mul]
        _ ≤ ∫ p, heatKernel r (p.1 - x) * f p.2 ∂Z r t ω :=
          integral_mono_ae (hI1.const_mul c) hIf (Filter.Eventually.of_forall hpointL)
    have hhigh : B ω ≤ C * A ω := by
      dsimp [A, B, shfPairing]
      calc
        ∫ p, heatKernel r (p.1 - x) * f p.2 ∂Z r t ω ≤
            ∫ p, C * (heatKernel r (p.1 - x) * one p.2) ∂Z r t ω :=
          integral_mono_ae hIf (hI1.const_mul C) (Filter.Eventually.of_forall hpointU)
        _ = C * ∫ p, heatKernel r (p.1 - x) * one p.2 ∂Z r t ω := by
          rw [integral_const_mul]
    have hlogL : Real.log (c * A ω) ≤ Real.log (B ω) :=
      Real.log_le_log (mul_pos hc hAp) hlow
    have hlogU : Real.log (B ω) ≤ Real.log (C * A ω) :=
      Real.log_le_log ((mul_pos hc hAp).trans_le hlow) hhigh
    have hlogc : Real.log (c * A ω) = Real.log c + Real.log (A ω) :=
      Real.log_mul hc.ne' hAp.ne'
    have hlogC : Real.log (C * A ω) = Real.log C + Real.log (A ω) :=
      Real.log_mul hC.ne' hAp.ne'
    constructor
    · change Real.log c ≤ Real.log (B ω) - Real.log (A ω)
      rw [hlogc] at hlogL
      linarith
    · change Real.log (B ω) - Real.log (A ω) ≤ Real.log C
      rw [hlogC] at hlogU
      linarith
  have hDcenter (x : Plane) : ∀ᵐ ω ∂P,
      |D (x, ω) - ∫ ω', D (x, ω') ∂P| ≤ Real.log C - Real.log c := by
    have hmeanL : Real.log c ≤ ∫ ω, D (x, ω) ∂P := by
      calc
        Real.log c = ∫ _ω : Ω, Real.log c ∂P := by simp
        _ ≤ ∫ ω, D (x, ω) ∂P := integral_mono_ae (integrable_const _)
          (hDint x) (hDrange x |>.mono fun ω hω => hω.1)
    have hmeanU : ∫ ω, D (x, ω) ∂P ≤ Real.log C := by
      calc
        ∫ ω, D (x, ω) ∂P ≤ ∫ _ω : Ω, Real.log C ∂P := integral_mono_ae
          (hDint x) (integrable_const _) (hDrange x |>.mono fun ω hω => hω.2)
        _ = Real.log C := by simp
    filter_upwards [hDrange x] with ω hω
    rw [show (∫ ω', D (x, ω') ∂P) = ∫ ω', D (x, ω') ∂P from rfl]
    rw [abs_le]
    constructor <;> linarith
  have hprodF := integrable_test_mul_joint P hGf hsecf hMf hSqf ψ
  have hprod1 := integrable_test_mul_joint P hG1 hsec1 hM1 hSq1 ψ
  have hmeanFInt : Integrable (fun x => ψ x * mf x) volume := by
    have hEq : (fun x => ∫ ω, ψ x * Gf (x, ω) ∂P) = fun x => ψ x * mf x := by
      funext x
      rw [integral_const_mul]
    exact (Integrable.integral_prod_left hprodF).congr
      (Filter.Eventually.of_forall fun x => congrFun hEq x)
  have hmean1Int : Integrable (fun x => ψ x * m1 x) volume := by
    have hEq : (fun x => ∫ ω, ψ x * G1 (x, ω) ∂P) = fun x => ψ x * m1 x := by
      funext x
      rw [integral_const_mul]
    exact (Integrable.integral_prod_left hprod1).congr
      (Filter.Eventually.of_forall fun x => congrFun hEq x)
  have hmeanF : AEMeasurable (fun x => ψ x * mf x) volume := hmeanFInt.aemeasurable
  have hmean1 : AEMeasurable (fun x => ψ x * m1 x) volume := hmean1Int.aemeasurable
  have hcenterProdF : Integrable (fun q : Plane × Ω => ψ q.1 * mf q.1)
      (volume.prod P) := by
    simpa only using hmeanFInt.comp_fst P
  have hcenterProd1 : Integrable (fun q : Plane × Ω => ψ q.1 * m1 q.1)
      (volume.prod P) := by
    simpa only using hmean1Int.comp_fst P
  have hFcentInt : Integrable (fun q : Plane × Ω => ψ q.1 * (Gf q - mf q.1))
      (volume.prod P) := by
    have hEqf : (fun q : Plane × Ω => ψ q.1 * (Gf q - mf q.1)) =
        (fun q => ψ q.1 * Gf q) - (fun q => ψ q.1 * mf q.1) := by
      funext q
      change ψ q.1 * (Gf q - mf q.1) =
        ψ q.1 * Gf q - ψ q.1 * mf q.1
      ring
    rw [hEqf]
    exact hprodF.sub hcenterProdF
  have h1centInt : Integrable (fun q : Plane × Ω => ψ q.1 * (G1 q - m1 q.1))
      (volume.prod P) := by
    have hEq1 : (fun q : Plane × Ω => ψ q.1 * (G1 q - m1 q.1)) =
        (fun q => ψ q.1 * G1 q) - (fun q => ψ q.1 * m1 q.1) := by
      funext q
      change ψ q.1 * (G1 q - m1 q.1) =
        ψ q.1 * G1 q - ψ q.1 * m1 q.1
      ring
    rw [hEq1]
    exact hprod1.sub hcenterProd1
  have hJint : Integrable J (volume.prod P) := by
    have hJEq : J = (fun q => ψ q.1 * (Gf q - mf q.1)) -
        (fun q => ψ q.1 * (G1 q - m1 q.1)) := by
      funext q
      simp [J]
      ring_nf
    rw [hJEq]
    exact hFcentInt.sub h1centInt
  have hJboundSection (x : Plane) : ∀ᵐ ω ∂P, |J (x, ω)| ≤ ψ x * (Real.log C - Real.log c) := by
    filter_upwards [hDcenter x] with ω hω
    have hψx := hψ x
    have hDidentity : J (x, ω) = ψ x *
        (D (x, ω) - ∫ ω', D (x, ω') ∂P) := by
      have hgfint : Integrable (fun ω => Gf (x, ω)) P :=
        (hmemf x).integrable (by norm_num)
      have h1int : Integrable (fun ω => G1 (x, ω)) P :=
        (hmem1 x).integrable (by norm_num)
      have hmean : mf x - m1 x = ∫ ω', D (x, ω') ∂P := by
        dsimp [mf, m1, D]
        rw [integral_sub hgfint h1int]
      change ψ x * (Gf (x, ω) - mf x - (G1 (x, ω) - m1 x)) =
        ψ x * ((Gf (x, ω) - G1 (x, ω)) - ∫ ω', D (x, ω') ∂P)
      nlinarith [hmean]
    rw [hDidentity, abs_mul, abs_of_nonneg hψx]
    exact mul_le_mul_of_nonneg_left hω hψx
  have hJrep : J =ᵐ[volume.prod P] (hJint.aestronglyMeasurable.mk J) :=
    hJint.aestronglyMeasurable.ae_eq_mk
  let Jm : Plane × Ω → ℝ := hJint.aestronglyMeasurable.mk J
  have hJm : Measurable Jm := hJint.aestronglyMeasurable.measurable_mk
  have hJset : MeasurableSet {q : Plane × Ω |
      |Jm q| ≤ ψ q.1 * (Real.log C - Real.log c)} := by
    exact measurableSet_le hJm.abs
      ((ψ.continuous.measurable.comp measurable_fst).mul_const
        (Real.log C - Real.log c))
  have hJboundProd : ∀ᵐ q : Plane × Ω ∂(volume.prod P),
      |Jm q| ≤ ψ q.1 * (Real.log C - Real.log c) := by
    rw [Measure.ae_prod_iff_ae_ae hJset]
    have hJsections : ∀ᵐ x ∂volume,
        (fun ω => J (x, ω)) =ᵐ[P] fun ω => Jm (x, ω) :=
      Measure.ae_ae_of_ae_prod hJrep
    filter_upwards [hJsections] with x hEq
    filter_upwards [hJboundSection x, hEq] with ω hB hEqω
    simpa [hEqω] using hB
  have hJboundSwap : ∀ᵐ q : Ω × Plane ∂(P.prod volume),
      |J (q.2, q.1)| ≤ ψ q.2 * (Real.log C - Real.log c) := by
    have hJmSwap := (Measure.measurePreserving_swap (μ := P) (ν := volume)).quasiMeasurePreserving.ae_eq_comp hJrep
    have hboundSwap : ∀ᵐ q : Ω × Plane ∂(P.prod volume),
        |Jm (q.2, q.1)| ≤ ψ q.2 * (Real.log C - Real.log c) := by
      exact (Measure.measurePreserving_swap (μ := P) (ν := volume)).quasiMeasurePreserving.ae hJboundProd
    filter_upwards [hJmSwap, hboundSwap] with q hEq hB
    have hEq' : J (q.2, q.1) = Jm (q.2, q.1) := by
      simpa [Function.comp_def, Prod.swap] using hEq
    rw [hEq']
    exact hB
  have hJsections : ∀ᵐ ω ∂P, ∀ᵐ x ∂volume,
      |J (x, ω)| ≤ ψ x * (Real.log C - Real.log c) :=
    Measure.ae_ae_of_ae_prod hJboundSwap
  have hJω : ∀ᵐ ω ∂P, Integrable (fun x => J (x, ω)) volume := by
    exact (integrable_prod_iff hJint.swap.aestronglyMeasurable).1 hJint.swap |>.1
  have hfc : ∀ᵐ ω ∂P,
      Integrable (fun x => ψ x * (Gf (x, ω) - mf x)) volume :=
    (integrable_prod_iff' hFcentInt.aestronglyMeasurable).1 hFcentInt |>.1
  have h1c : ∀ᵐ ω ∂P,
      Integrable (fun x => ψ x * (G1 (x, ω) - m1 x)) volume :=
    (integrable_prod_iff' h1centInt.aestronglyMeasurable).1 h1centInt |>.1
  have havgEq : avgLogField P Z r t ψ f -
      avgLogField P Z r t ψ (fun _ => 1) =ᵐ[P]
      fun ω => ∫ x, J (x, ω) ∂volume := by
    filter_upwards [hfc, h1c] with ω hfcω h1cω
    have hEqf (ω : Ω) : avgLogField P Z r t ψ f ω =
        ∫ x, ψ x * (Gf (x, ω) - mf x) ∂volume := by
      unfold avgLogField
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => rfl
    have hEq1 (ω : Ω) : avgLogField P Z r t ψ (fun _ => 1) ω =
        ∫ x, ψ x * (G1 (x, ω) - m1 x) ∂volume := by
      unfold avgLogField
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => rfl
    change avgLogField P Z r t ψ f ω -
      avgLogField P Z r t ψ (fun _ => 1) ω = ∫ x, J (x, ω) ∂volume
    rw [hEqf ω, hEq1 ω, ← integral_sub hfcω h1cω]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [J]
      ring
  have hboundIntegral (ω : Ω) (hω : ∀ᵐ x ∂volume,
      |J (x, ω)| ≤ ψ x * (Real.log C - Real.log c))
      (hJω : Integrable (fun x => J (x, ω)) volume) :
      |∫ x, J (x, ω) ∂volume| ≤ Real.log C - Real.log c := by
    have hψInt : Integrable (fun x : Plane => ψ x) volume :=
      ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    have hdom : Integrable (fun x => ψ x * (Real.log C - Real.log c)) volume :=
      hψInt.mul_const _
    have hnonneg : 0 ≤ᵐ[volume] fun x => ψ x * (Real.log C - Real.log c) :=
      Filter.Eventually.of_forall fun x => mul_nonneg (hψ x) hwidth
    have habs : ∀ᵐ x ∂volume,
        |J (x, ω)| ≤ ψ x * (Real.log C - Real.log c) := hω
    calc
      |∫ x, J (x, ω) ∂volume| = ‖∫ x, J (x, ω) ∂volume‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ∫ x, ‖J (x, ω)‖ ∂volume := norm_integral_le_integral_norm _
      _ = ∫ x, |J (x, ω)| ∂volume := by simp only [Real.norm_eq_abs]
      _ ≤ ∫ x, ψ x * (Real.log C - Real.log c) ∂volume :=
        integral_mono_ae hJω.norm hdom habs
      _ = Real.log C - Real.log c := by
        rw [integral_mul_const]
        simp [hψ₁]
  filter_upwards [hJsections, havgEq, hJω] with ω hω heq hint
  change |(avgLogField P Z r t ψ f -
    avgLogField P Z r t ψ (fun _ => 1)) ω| ≤ Real.log (C / c)
  rw [heq]
  have hbound := hboundIntegral ω hω hint
  simpa only [hwidthEq] using hbound

end Critical2DKPZ.NonGaussian

end
