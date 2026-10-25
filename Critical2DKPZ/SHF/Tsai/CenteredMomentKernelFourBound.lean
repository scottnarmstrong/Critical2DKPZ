/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelForms
public import Critical2DKPZ.SHF.Tsai.WeightedFormBoundIntegral
public import Critical2DKPZ.SHF.Tsai.CenteredCoveringIdentity
public import Critical2DKPZ.SHF.Tsai.HeadIntegratedBounds
public import Critical2DKPZ.SHF.Tsai.TailKernelBound
public import Critical2DKPZ.SHF.Tsai.WordFactorization
import Mathlib.Tactic

/-! # Real bilinear forms from weighted positive kernel bounds -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Transfer real-valued integrability across an almost-everywhere equality. -/
theorem integrable_real_congr_of_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable f μ) (h : f =ᵐ[μ] g) : Integrable g μ :=
  hf.congr h

/-- A finite weighted positive form bound controls the corresponding real
bilinear integral. -/
theorem weightedFormBound_real_form_bound {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞}
    {w : Configuration n → ℝ} {p : ℝ} (hp : 0 < p)
    (hKm : Measurable (Function.uncurry K))
    (hKneTop : ∀ᵐ xy : Configuration n × Configuration n ∂(volume.prod volume),
      K xy.1 xy.2 ≠ ⊤)
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hForm : WeightedFormBound volume volume w w p p K c)
    (hw : Measurable w) (F G : Configuration n → ℝ)
    (hF : MemLp (fun x => F x * Real.exp (w x)) (ENNReal.ofReal p))
    (hG : MemLp (fun y => G y * Real.exp (w y)) (ENNReal.ofReal p)) :
    Integrable (fun xy : Configuration n × Configuration n =>
      F xy.1 * (K xy.1 xy.2).toReal * G xy.2) (volume.prod volume) ∧
    |∫ xy : Configuration n × Configuration n,
      F xy.1 * (K xy.1 xy.2).toReal * G xy.2 ∂(volume.prod volume)| ≤
      c.toReal * (eLpNorm (fun x => F x * Real.exp (w x)) (ENNReal.ofReal p)).toReal *
        (eLpNorm (fun y => G y * Real.exp (w y)) (ENNReal.ofReal p)).toReal := by
  let u : Configuration n → ℝ≥0∞ := fun x => ENNReal.ofReal |F x|
  let v : Configuration n → ℝ≥0∞ := fun y => ENNReal.ofReal |G y|
  let H : Configuration n × Configuration n → ℝ :=
    fun xy => F xy.1 * (K xy.1 xy.2).toReal * G xy.2
  let NF : ℝ≥0∞ := eLpNorm (fun x => F x * Real.exp (w x)) (ENNReal.ofReal p) volume
  let NG : ℝ≥0∞ := eLpNorm (fun y => G y * Real.exp (w y)) (ENNReal.ofReal p) volume
  have hp0 : 0 < p := hp
  have hpz : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp0)
  have hKreal : Measurable (fun xy : Configuration n × Configuration n =>
      (K xy.1 xy.2).toReal) := hKm.ennreal_toReal
  have hFreal : AEStronglyMeasurable F volume := by
    have hmul := hF.aestronglyMeasurable.mul
      ((hw.neg.exp).aestronglyMeasurable)
    have heq : (fun x : Configuration n =>
        (F x * Real.exp (w x)) * Real.exp (-w x)) =ᵐ[volume] F := by
      filter_upwards [] with x
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    exact hmul.congr heq
  have hGreal : AEStronglyMeasurable G volume := by
    have hmul := hG.aestronglyMeasurable.mul
      ((hw.neg.exp).aestronglyMeasurable)
    have heq : (fun y : Configuration n =>
        (G y * Real.exp (w y)) * Real.exp (-w y)) =ᵐ[volume] G := by
      filter_upwards [] with y
      rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    exact hmul.congr heq
  have huA : AEMeasurable u volume := by
    simpa only [u, Real.enorm_eq_ofReal_abs] using hFreal.aemeasurable.enorm
  have hvA : AEMeasurable v volume := by
    simpa only [v, Real.enorm_eq_ofReal_abs] using hGreal.aemeasurable.enorm
  let um : Configuration n → ℝ≥0∞ := huA.mk u
  let vm : Configuration n → ℝ≥0∞ := hvA.mk v
  have hu : u =ᵐ[volume] um := huA.ae_eq_mk
  have hv : v =ᵐ[volume] vm := hvA.ae_eq_mk
  have hum : Measurable um := huA.measurable_mk
  have hvm : Measurable vm := hvA.measurable_mk
  have hH : AEStronglyMeasurable H (volume.prod volume) := by
    exact ((hFreal.comp_fst.mul hKreal.aestronglyMeasurable).mul hGreal.comp_snd)
  have hpoint (xy : Configuration n × Configuration n)
      (hfinite : K xy.1 xy.2 ≠ ⊤) :
      ENNReal.ofReal |H xy| = (K xy.1 xy.2 * v xy.2) * u xy.1 := by
    have hk : 0 ≤ (K xy.1 xy.2).toReal := ENNReal.toReal_nonneg
    calc
      ENNReal.ofReal |H xy| =
          ENNReal.ofReal (|F xy.1| * (K xy.1 xy.2).toReal * |G xy.2|) := by
            simp only [H, abs_mul, abs_of_nonneg hk]
      _ = (ENNReal.ofReal |F xy.1| * ENNReal.ofReal (K xy.1 xy.2).toReal) *
          ENNReal.ofReal |G xy.2| := by
            rw [ENNReal.ofReal_mul
              (mul_nonneg (abs_nonneg _) ENNReal.toReal_nonneg),
              ENNReal.ofReal_mul (abs_nonneg _)]
      _ = (K xy.1 xy.2 * v xy.2) * u xy.1 := by
            rw [ENNReal.ofReal_toReal hfinite]
            simp [u, v, mul_comm, mul_left_comm]
  have hRootF :
      (∫⁻ x : Configuration n,
        (u x * ENNReal.ofReal (Real.exp (w x))) ^ p) ^ (1 / p : ℝ) =
        eLpNorm (fun x => F x * Real.exp (w x)) (ENNReal.ofReal p) volume := by
    symm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpz ENNReal.ofReal_ne_top
      hF.aestronglyMeasurable]
    have hnorm (x : Configuration n) :
        ‖F x * Real.exp (w x)‖ₑ = u x * ENNReal.ofReal (Real.exp (w x)) := by
      rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        abs_of_pos (Real.exp_pos _)]
    simp only [ENNReal.toReal_ofReal hp0.le]
    simp_rw [hnorm]
  have hRootG :
      (∫⁻ y : Configuration n,
        (v y * ENNReal.ofReal (Real.exp (w y))) ^ p) ^ (1 / p : ℝ) =
        eLpNorm (fun y => G y * Real.exp (w y)) (ENNReal.ofReal p) volume := by
    symm
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpz ENNReal.ofReal_ne_top
      hG.aestronglyMeasurable]
    have hnorm (y : Configuration n) :
        ‖G y * Real.exp (w y)‖ₑ = v y * ENNReal.ofReal (Real.exp (w y)) := by
      rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        abs_of_pos (Real.exp_pos _)]
    simp only [ENNReal.toReal_ofReal hp0.le]
    simp_rw [hnorm]
  have hpositiveRaw :
      (∫⁻ x : Configuration n, u x *
        (∫⁻ y : Configuration n, K x y * v y ∂volume) ∂volume) ≤
        c * (∫⁻ y : Configuration n,
          (v y * ENNReal.ofReal (Real.exp (w y))) ^ p ∂volume) ^ (1 / p : ℝ) *
          (∫⁻ x : Configuration n,
            (u x * ENNReal.ofReal (Real.exp (w x))) ^ p ∂volume) ^ (1 / p : ℝ) := by
    have hVweighted :
        (∫⁻ y : Configuration n,
          (vm y * ENNReal.ofReal (Real.exp (w y))) ^ p ∂volume) =
        ∫⁻ y : Configuration n,
          (v y * ENNReal.ofReal (Real.exp (w y))) ^ p ∂volume := by
      apply lintegral_congr_ae
      exact hv.mono fun y hy => by
        change (vm y * ENNReal.ofReal (Real.exp (w y))) ^ p =
          (v y * ENNReal.ofReal (Real.exp (w y))) ^ p
        rw [hy]
    have hUweighted :
        (∫⁻ x : Configuration n,
          (um x * ENNReal.ofReal (Real.exp (w x))) ^ p ∂volume) =
        ∫⁻ x : Configuration n,
          (u x * ENNReal.ofReal (Real.exp (w x))) ^ p ∂volume := by
      apply lintegral_congr_ae
      exact hu.mono fun x hx => by
        change (um x * ENNReal.ofReal (Real.exp (w x))) ^ p =
          (u x * ENNReal.ofReal (Real.exp (w x))) ^ p
        rw [hx]
    have hActionEq (x : Configuration n) :
        (∫⁻ y : Configuration n, K x y * v y ∂volume) =
          ∫⁻ y : Configuration n, K x y * vm y ∂volume := by
      apply lintegral_congr_ae
      exact hv.mono fun y hy => by
        change K x y * v y = K x y * vm y
        rw [hy]
    calc
      _ = ∫⁻ x : Configuration n, um x *
          (∫⁻ y : Configuration n, K x y * vm y ∂volume) ∂volume := by
            apply lintegral_congr_ae
            exact hu.mono fun x hx => by
              change u x * (∫⁻ y, K x y * v y ∂volume) =
                um x * (∫⁻ y, K x y * vm y ∂volume)
              rw [hx, hActionEq x]
      _ ≤ c *
          (∫⁻ y : Configuration n,
            (vm y * ENNReal.ofReal (Real.exp (w y))) ^ p ∂volume) ^ (1 / p : ℝ) *
          (∫⁻ x : Configuration n,
            (um x * ENNReal.ofReal (Real.exp (w x))) ^ p ∂volume) ^ (1 / p : ℝ) :=
              hForm vm um hvm hum
      _ = _ := by rw [hVweighted, hUweighted]
  have hpositive :
      (∫⁻ x : Configuration n, u x *
        (∫⁻ y : Configuration n, K x y * v y ∂volume) ∂volume) ≤
        c * NG * NF := by
    calc
      _ ≤ c * (∫⁻ y : Configuration n,
            (v y * ENNReal.ofReal (Real.exp (w y))) ^ p ∂volume) ^ (1 / p : ℝ) *
          (∫⁻ x : Configuration n,
            (u x * ENNReal.ofReal (Real.exp (w x))) ^ p ∂volume) ^ (1 / p : ℝ) :=
              hpositiveRaw
      _ = _ := by rw [hRootG, hRootF]
  have hrowAEMeas (x : Configuration n) :
      AEMeasurable (fun y : Configuration n => K x y * v y) volume :=
    ((hKm.comp (measurable_const.prodMk measurable_id)).aemeasurable).mul
      hvA
  have hAbsEq :
      (∫⁻ xy : Configuration n × Configuration n,
        ENNReal.ofReal |H xy| ∂(volume.prod volume)) =
      ∫⁻ xy : Configuration n × Configuration n,
        (K xy.1 xy.2 * v xy.2) * u xy.1 ∂(volume.prod volume) := by
    apply lintegral_congr_ae
    filter_upwards [hKneTop] with xy hfinite
    exact hpoint xy hfinite
  have hProductMeas : AEMeasurable
      (fun xy : Configuration n × Configuration n =>
        (K xy.1 xy.2 * v xy.2) * u xy.1) (volume.prod volume) :=
    ((hKm.aemeasurable.mul (hvA.comp_snd)).mul (huA.comp_fst))
  have hAbsolute :
      (∫⁻ xy : Configuration n × Configuration n,
        ENNReal.ofReal |H xy| ∂(volume.prod volume)) ≤
      c * NG * NF := by
    rw [hAbsEq, lintegral_prod _ hProductMeas]
    calc
      (∫⁻ x : Configuration n,
          ∫⁻ y : Configuration n, (K x y * v y) * u x ∂volume ∂volume) =
        ∫⁻ x : Configuration n,
          (∫⁻ y : Configuration n, K x y * v y ∂volume) * u x ∂volume := by
            apply lintegral_congr
            intro x
            exact lintegral_mul_const'' (u x) (hrowAEMeas x)
      _ = ∫⁻ x : Configuration n, u x *
          (∫⁻ y : Configuration n, K x y * v y ∂volume) ∂volume := by
            apply lintegral_congr
            intro x
            ac_rfl
      _ ≤ _ := hpositive
  have hHabs_integrable : Integrable (fun xy : Configuration n × Configuration n => |H xy|)
      (volume.prod volume) := by
    have hnormIntegral :
        (∫⁻ xy : Configuration n × Configuration n,
          ENNReal.ofReal ‖H xy‖ ∂(volume.prod volume)) ≤
        c * NG * NF := by
      simpa only [Real.norm_eq_abs] using hAbsolute
    have hcprod :
        c * NG * NF ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top hc hG.eLpNorm_ne_top) hF.eLpNorm_ne_top
    have hnormIntegrable : Integrable (fun xy : Configuration n × Configuration n => ‖H xy‖)
        (volume.prod volume) :=
      (lintegral_ofReal_ne_top_iff_integrable hH.norm
        (Filter.Eventually.of_forall fun xy => norm_nonneg (H xy))).1 <|
          ne_top_of_le_ne_top hcprod hnormIntegral
    simpa only [Real.norm_eq_abs] using hnormIntegrable
  have hHint : Integrable H (volume.prod volume) := by
    apply (integrable_norm_iff hH).mp
    simpa only [Real.norm_eq_abs] using hHabs_integrable
  refine ⟨hHint, ?_⟩
  have hreal : ENNReal.ofReal |∫ xy, H xy ∂(volume.prod volume)| ≤
      c * NF * NG := by
    calc
      ENNReal.ofReal |∫ xy, H xy ∂(volume.prod volume)| =
          ENNReal.ofReal ‖∫ xy, H xy ∂(volume.prod volume)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ENNReal.ofReal (∫ xy, ‖H xy‖ ∂(volume.prod volume)) :=
            ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm H)
      _ = ∫⁻ xy, ‖H xy‖ₑ ∂(volume.prod volume) := ofReal_integral_norm_eq_lintegral_enorm hHint
      _ = ∫⁻ xy, ENNReal.ofReal |H xy| ∂(volume.prod volume) := by
            apply lintegral_congr_ae
            filter_upwards [] with xy
            rw [Real.enorm_eq_ofReal_abs]
      _ ≤ c * NG * NF := hAbsolute
      _ = _ := by ac_rfl
  have hProductTop :
      c * NF * NG ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hc hF.eLpNorm_ne_top) hG.eLpNorm_ne_top
  have hreal' : |∫ xy, H xy ∂(volume.prod volume)| ≤
      (c * NF * NG).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hProductTop).1 hreal
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at hreal'
  simpa only [H, mul_assoc] using hreal'


/-- Joint measurability of the head kernel in time and both spatial endpoints. -/
theorem measurable_headKernel_joint {n : ℕ} (θ : ℝ) (α β : CollisionPair n) :
    Measurable (fun q : ℝ × Configuration n × FusedConfiguration β =>
      headKernel θ α β q.1 q.2.1 q.2.2) := by
  have hP : Measurable (causalKernel (freeTimeKernel id (collisionEmbedding α))) :=
    measurable_causalKernel
      (measurable_freeTimeKernel measurable_id (measurable_collisionEmbedding α))
  have hJ : Measurable (causalKernel (collisionTimeKernel α θ)) :=
    measurable_causalKernel (measurable_collisionTimeKernel α θ)
  have hS : Measurable (causalKernel
      (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β))) :=
    measurable_causalKernel
      (measurable_freeTimeKernel (measurable_collisionEmbedding α)
        (measurable_collisionEmbedding β))
  have hJS : Measurable (timeKernelComp volume
      (causalKernel (collisionTimeKernel α θ))
      (causalKernel (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)))) :=
    measurable_timeKernelComp volume hJ hS
  have hHead : Measurable (headTimeKernel θ α β) := by
    change Measurable (timeKernelComp volume
      (causalKernel (freeTimeKernel id (collisionEmbedding α)))
      (timeKernelComp volume
        (causalKernel (collisionTimeKernel α θ))
        (causalKernel (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)))))
    exact measurable_timeKernelComp volume hP hJS
  have hmap : Measurable
      (fun q : ℝ × Configuration n × FusedConfiguration β => (q.1, q.2.1, q.2.2)) := by
    fun_prop
  have heq : (fun q : ℝ × Configuration n × FusedConfiguration β =>
      headKernel θ α β q.1 q.2.1 q.2.2) =
      fun q => headTimeKernel θ α β (q.1, q.2.1, q.2.2) := by
    funext q
    exact headKernel_eq_headTimeKernel θ α β q.1 q.2.1 q.2.2
  rw [heq]
  exact hHead.comp hmap

/-- Joint measurability of the resummed tail in time and both endpoints. -/
theorem measurable_tailKernel_joint {n : ℕ} (θ : ℝ) (β : CollisionPair n) :
    Measurable (fun q : ℝ × FusedConfiguration β × Configuration n =>
      tailKernel θ β q.1 q.2.1 q.2.2) := by
  classical
  change Measurable (fun q : ℝ × FusedConfiguration β × Configuration n =>
    ∑' m : ℕ, ∑ w : CollisionWord n m,
      if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
        tailWordKernel θ β (List.ofFn w.1) q.1 q.2.1 q.2.2 else 0)
  apply Measurable.tsum
  intro m
  apply Finset.measurable_sum
  intro w hw
  by_cases hfirst : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
  · let word := List.ofFn w.1
    have hJ : Measurable (causalKernel (collisionTimeKernel β θ)) :=
      measurable_causalKernel (measurable_collisionTimeKernel β θ)
    have hR : Measurable (causalKernel
        (pathTimeKernel θ word (collisionEmbedding β) id)) :=
      measurable_causalKernel
        (measurable_pathTimeKernel θ word (measurable_collisionEmbedding β) measurable_id)
    have hWord : Measurable (tailWordTimeKernel θ β word) := by
      change Measurable (timeKernelComp volume
        (causalKernel (collisionTimeKernel β θ))
        (causalKernel (pathTimeKernel θ word (collisionEmbedding β) id)))
      exact measurable_timeKernelComp volume hJ hR
    have heq : (fun q : ℝ × FusedConfiguration β × Configuration n =>
        if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
          tailWordKernel θ β word q.1 q.2.1 q.2.2 else 0) =
        fun q => tailWordTimeKernel θ β word (q.1, q.2.1, q.2.2) := by
      funext q
      simp only [ite_eq_left hfirst]
      exact tailWordKernel_eq_tailWordTimeKernel θ β word q.1 q.2.1 q.2.2
    rw [heq]
    exact hWord.comp (by fun_prop)
  · have heq : (fun q : ℝ × FusedConfiguration β × Configuration n =>
        if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
          tailWordKernel θ β (List.ofFn w.1) q.1 q.2.1 q.2.2 else 0) =
        fun _ => 0 := by
      funext q
      simp only [ite_eq_right hfirst]
    rw [heq]
    exact measurable_const

/-- Joint measurability of the positive covering kernel in its endpoints. -/
theorem measurable_coveringKernel_four (θ t : ℝ) :
    Measurable (Function.uncurry (fun x y : Configuration 4 => coveringKernel 4 θ t x y)) := by
  classical
  unfold coveringKernel
  apply Measurable.tsum
  intro m
  apply Finset.measurable_sum
  intro w hw
  by_cases hcover : wordSupport w.1 = Finset.univ
  · have hmap : Measurable
        (fun xy : Configuration 4 × Configuration 4 => ((θ, t), xy.1, xy.2)) := by
      fun_prop
    simp only [ite_eq_left hcover]
    have hdiag := (measurable_diagramKernel (List.ofFn w.1)).comp hmap
    convert hdiag using 1
    funext xy
    rfl
  · simp [hcover]


/-- Uniform weighted bound for the positive four-particle covering kernel. -/
theorem weightedFormBound_coveringKernel_four (θ T : ℝ) {p : ℝ≥0∞}
    (hp : 2 < p) (hp' : p ≠ ⊤) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ T →
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configL1Norm x)
        (fun y : Configuration 4 => a * configL1Norm y) p.toReal p.toReal
        (coveringKernel 4 θ t)
        (ENNReal.ofReal (C * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)))) := by
  classical
  let r : ℝ := p.toReal
  have hr : 2 < r :=
    (ENNReal.toReal_lt_toReal (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hp').mpr hp
  have hr0 : 0 < r := lt_trans (by norm_num) hr
  have htwoDiv : 2 / r < 1 := (div_lt_iff₀ hr0).2 (by linarith)
  have honeDiv : 1 / r < 1 := (div_lt_iff₀ hr0).2 (by linarith)
  let b : ℝ := 1 / 2 - 2 / r
  let b' : ℝ := -1 / r
  have hb : -1 < b := by dsimp [b]; linarith
  have hb' : -1 < b' := by
    have hneg : -1 / r = -(1 / r) := by ring
    dsimp [b']
    rw [hneg]
    linarith [honeDiv]
  let e : ℝ := b + b' + 1
  have he : e = (3 / 2 : ℝ) * (1 - 2 / r) := by
    dsimp [e, b, b']
    ring
  have hb1 : 0 < b + 1 := by linarith
  have hb'1 : 0 < b' + 1 := by linarith
  have hb2 : 0 < b + b' + 2 := by linarith
  let betaFactor : ℝ :=
    Real.Gamma (b + 1) * Real.Gamma (b' + 1) / Real.Gamma (b + b' + 2)
  have hBetaFactor : 0 < betaFactor := by
    dsimp [betaFactor]
    positivity
  let headConst : CollisionPair 4 → CollisionPair 4 → ℝ :=
    fun α β => if h : α = β then 0 else
      Classical.choose (weightedFormBound_headKernel θ T hr ha α β h)
  have hHeadSpec (α β : CollisionPair 4) (hneq : α ≠ β) :
      0 < headConst α β ∧ ∀ s : ℝ, 0 < s → s ≤ T →
        WeightedFormBound volume volume
          (fun x : Configuration 4 => a * configurationOneNorm x)
          (fun _ : FusedConfiguration β => 0) 2 r
          (headKernel θ α β s) (ENNReal.ofReal (headConst α β * s ^ b)) := by
    dsimp [headConst]
    rw [dite_eq_right hneq]
    simpa [b] using
      Classical.choose_spec (weightedFormBound_headKernel θ T hr ha α β hneq)
  let tailConst : CollisionPair 4 → ℝ :=
    fun β => Classical.choose (weightedFormBound_tailKernel θ T hr ha β)
  have hTailSpec (β : CollisionPair 4) :
      0 < tailConst β ∧ ∀ s : ℝ, 0 < s → s ≤ T →
        WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
          (fun y : Configuration 4 => a * configurationOneNorm y) r 2
          (tailKernel θ β s) (ENNReal.ofReal (tailConst β * s ^ b')) := by
    simpa [tailConst, b'] using
      Classical.choose_spec (weightedFormBound_tailKernel θ T hr ha β)
  let PairScale (α β : CollisionPair 4) : ℝ :=
    if α = β then 0 else headConst α β * tailConst β * betaFactor
  let C : ℝ := ∑ α : CollisionPair 4, ∑ β : CollisionPair 4, PairScale α β
  have hC : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro α hα
    apply Finset.sum_nonneg
    intro β hβ
    by_cases h : α = β
    · simp [PairScale, h]
    · simp only [PairScale, ite_eq_right h]
      exact mul_nonneg (mul_nonneg (hHeadSpec α β h).1.le (hTailSpec β).1.le)
        hBetaFactor.le
  refine ⟨C, hC, ?_⟩
  intro t ht htT
  let PairIntegral (α β : CollisionPair 4) (x y : Configuration 4) : ℝ≥0∞ :=
    ∫⁻ s in Set.Ioo (0 : ℝ) t, ∫⁻ z : FusedConfiguration β,
      headKernel θ α β s x z * tailKernel θ β (t - s) z y
  let PairKernel (α β : CollisionPair 4) (x y : Configuration 4) : ℝ≥0∞ :=
    if α = β then 0 else PairIntegral α β x y
  let PairCoeff (α β : CollisionPair 4) : ℝ≥0∞ :=
    ENNReal.ofReal (PairScale α β * t ^ e)
  have hPairIntegralMeas (α β : CollisionPair 4) :
      Measurable (Function.uncurry (PairIntegral α β)) := by
    let InnerIntegrand :
        ((Configuration 4 × Configuration 4) × ℝ) × FusedConfiguration β → ℝ≥0∞ :=
      fun q => headKernel θ α β q.1.2 q.1.1.1 q.2 *
        tailKernel θ β (t - q.1.2) q.2 q.1.1.2
    let Inner : (Configuration 4 × Configuration 4) × ℝ → ℝ≥0∞ :=
      fun q => ∫⁻ z : FusedConfiguration β, InnerIntegrand (q, z) ∂volume
    have hHeadMap : Measurable
        (fun q : ((Configuration 4 × Configuration 4) × ℝ) × FusedConfiguration β =>
          (q.1.2, q.1.1.1, q.2)) := by fun_prop
    have hTailMap : Measurable
        (fun q : ((Configuration 4 × Configuration 4) × ℝ) × FusedConfiguration β =>
          (t - q.1.2, q.2, q.1.1.2)) := by fun_prop
    have hHeadIntegrand : Measurable (fun q :
        ((Configuration 4 × Configuration 4) × ℝ) × FusedConfiguration β =>
          headKernel θ α β q.1.2 q.1.1.1 q.2) := by
      exact (measurable_headKernel_joint θ α β).comp hHeadMap
    have hTailIntegrand : Measurable (fun q :
        ((Configuration 4 × Configuration 4) × ℝ) × FusedConfiguration β =>
          tailKernel θ β (t - q.1.2) q.2 q.1.1.2) := by
      convert (measurable_tailKernel_joint θ β).comp hTailMap using 1
      funext q
      rfl
    have hIntegrand : Measurable InnerIntegrand := by
      change Measurable (fun q :
        ((Configuration 4 × Configuration 4) × ℝ) × FusedConfiguration β =>
          headKernel θ α β q.1.2 q.1.1.1 q.2 *
            tailKernel θ β (t - q.1.2) q.2 q.1.1.2)
      exact hHeadIntegrand.mul hTailIntegrand
    have hInner : Measurable Inner := by
      change Measurable (fun q : (Configuration 4 × Configuration 4) × ℝ =>
        ∫⁻ z : FusedConfiguration β, InnerIntegrand (q, z) ∂volume)
      exact hIntegrand.lintegral_prod_right'
    change Measurable (fun xy : Configuration 4 × Configuration 4 =>
      ∫⁻ s in Set.Ioo (0 : ℝ) t, Inner (xy, s))
    exact hInner.lintegral_prod_right'
  have hPairMeas (α β : CollisionPair 4) :
      Measurable (Function.uncurry (PairKernel α β)) := by
    by_cases h : α = β
    · subst β
      have hzero : Function.uncurry (PairKernel α α) =
          fun _ : Configuration 4 × Configuration 4 => (0 : ℝ≥0∞) := by
        funext xy
        change (if α = α then 0 else PairIntegral α α xy.1 xy.2) = 0
        simp
      rw [hzero]
      exact measurable_const
    · simp only [PairKernel, ite_eq_right h]
      exact hPairIntegralMeas α β
  have hPairBound (α β : CollisionPair 4) :
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun y : Configuration 4 => a * configurationOneNorm y) r r
        (PairKernel α β) (PairCoeff α β) := by
    by_cases hneq : α = β
    · subst β
      simp [PairKernel, PairCoeff, PairScale, WeightedFormBound]
    · obtain ⟨hcH, hH⟩ := hHeadSpec α β hneq
      obtain ⟨hcT, hT⟩ := hTailSpec β
      have hheadMeas : Measurable
          (fun q : ℝ × Configuration 4 × FusedConfiguration β =>
            headKernel θ α β q.1 q.2.1 q.2.2) :=
        measurable_headKernel_joint θ α β
      have htailMeas : Measurable
          (fun q : ℝ × FusedConfiguration β × Configuration 4 =>
            tailKernel θ β q.1 q.2.1 q.2.2) :=
        measurable_tailKernel_joint θ β
      have hcomp := WeightedFormBound.lintegral_comp_beta
        (μ := volume) (ν := volume) (ρ := volume)
        (wX := fun x : Configuration 4 => a * configurationOneNorm x)
        (wZ := fun y : Configuration 4 => a * configurationOneNorm y)
        (p := r) (p' := r)
        (H := fun s x z => headKernel θ α β s x z)
        (L := fun s z y => tailKernel θ β s z y)
        t (headConst α β) (tailConst β) b b' ht hcH hcT hb hb'
        hheadMeas htailMeas
        (by
          intro s hs
          have hs' : 0 < s := hs.1
          have hsT : s ≤ T := (le_of_lt hs.2).trans htT
          exact hH s hs' hsT)
        (by
          intro s hs
          have hs' : 0 < s := hs.1
          have hsT : s ≤ T := (le_of_lt hs.2).trans htT
          exact hT s hs' hsT)
      have hWFB : WeightedFormBound volume volume
          (fun x : Configuration 4 => a * configurationOneNorm x)
          (fun y : Configuration 4 => a * configurationOneNorm y) r r
          (PairIntegral α β)
          (ENNReal.ofReal (headConst α β * tailConst β * t ^ (b + b' + 1) *
            (Real.Gamma (b + 1) * Real.Gamma (b' + 1) /
              Real.Gamma (b + b' + 2)))) := by
        simpa [PairIntegral, spatialKernelComp] using hcomp.2
      have hcoeff :
          PairCoeff α β =
            ENNReal.ofReal (headConst α β * tailConst β * t ^ (b + b' + 1) *
              (Real.Gamma (b + 1) * Real.Gamma (b' + 1) /
                Real.Gamma (b + b' + 2))) := by
        dsimp [PairCoeff, PairScale]
        simp only [ite_eq_right hneq]
        congr 1
        dsimp [e, betaFactor]
        ring
      simpa only [PairKernel, ite_eq_right hneq, hcoeff] using hWFB
  have hBetaBound (α : CollisionPair 4) :
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun y : Configuration 4 => a * configurationOneNorm y) r r
        (fun x y => ∑' β : CollisionPair 4, PairKernel α β x y)
        (∑' β : CollisionPair 4, PairCoeff α β) :=
    WeightedFormBound.tsum (fun β => hPairMeas α β) (fun β => hPairBound α β)
  have hBetaMeas (α : CollisionPair 4) :
      Measurable (Function.uncurry
        (fun x y => ∑' β : CollisionPair 4, PairKernel α β x y)) :=
    Measurable.tsum (fun β => hPairMeas α β)
  have hAllBound :
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun y : Configuration 4 => a * configurationOneNorm y) r r
        (fun x y => ∑' α : CollisionPair 4, ∑' β : CollisionPair 4,
          PairKernel α β x y)
        (∑' α : CollisionPair 4, ∑' β : CollisionPair 4, PairCoeff α β) :=
    WeightedFormBound.tsum hBetaMeas (fun α => hBetaBound α)
  have hLongEq (x y : Configuration 4) :
      longWordKernel 4 θ t x y =
        ∑' α : CollisionPair 4, ∑' β : CollisionPair 4, PairKernel α β x y := by
    rw [longWordKernel_eq_sum_head_tail θ ht]
    simp only [PairKernel, PairIntegral, tsum_fintype]
  have htimeNonneg : 0 ≤ t ^ e := Real.rpow_nonneg ht.le _
  have hCoeffSum :
      (∑' α : CollisionPair 4, ∑' β : CollisionPair 4, PairCoeff α β) =
        ENNReal.ofReal (C * t ^ e) := by
    simp only [tsum_fintype, PairCoeff]
    calc
      (∑ α : CollisionPair 4, ∑ β : CollisionPair 4,
          ENNReal.ofReal (PairScale α β * t ^ e)) =
        ∑ α : CollisionPair 4,
          ENNReal.ofReal (∑ β : CollisionPair 4, PairScale α β * t ^ e) := by
            apply Finset.sum_congr rfl
            intro α hα
            rw [← ENNReal.ofReal_sum_of_nonneg (fun β hβ =>
              mul_nonneg
                (by
                  by_cases h : α = β
                  · simp [PairScale, h]
                  · simp [PairScale, h]
                    exact mul_nonneg (mul_nonneg (hHeadSpec α β h).1.le
                      (hTailSpec β).1.le) hBetaFactor.le)
                htimeNonneg)]
      _ = ENNReal.ofReal
          (∑ α : CollisionPair 4, ∑ β : CollisionPair 4,
            PairScale α β * t ^ e) := by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun α hα =>
              Finset.sum_nonneg fun β hβ =>
                mul_nonneg
                  (by
                    by_cases h : α = β
                    · simp [PairScale, h]
                    · simp [PairScale, h]
                      exact mul_nonneg (mul_nonneg (hHeadSpec α β h).1.le
                        (hTailSpec β).1.le) hBetaFactor.le)
                  htimeNonneg)]
      _ = ENNReal.ofReal (C * t ^ e) := by
            congr 1
            simp [C, Finset.sum_mul]
  have hLongForm :
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun y : Configuration 4 => a * configurationOneNorm y) r r
        (longWordKernel 4 θ t) (ENNReal.ofReal (C * t ^ e)) := by
    have hsum : (fun x y => ∑' α : CollisionPair 4, ∑' β : CollisionPair 4,
        PairKernel α β x y) = longWordKernel 4 θ t := by
      funext x y
      exact (hLongEq x y).symm
    rw [← hsum, ← hCoeffSum]
    exact hAllBound
  have hCoverForm :
      WeightedFormBound volume volume
        (fun x : Configuration 4 => a * configurationOneNorm x)
        (fun y : Configuration 4 => a * configurationOneNorm y) r r
        (coveringKernel 4 θ t) (ENNReal.ofReal (C * t ^ e)) :=
    hLongForm.mono
      (fun x y => coveringKernel_four_le_longWordKernel θ t x y)
      le_rfl
  have hCovMeas : Measurable (Function.uncurry
      (fun x y : Configuration 4 => coveringKernel 4 θ t x y)) :=
    measurable_coveringKernel_four θ t
  simpa only [he] using hCoverForm

/-- Convert a covering-kernel form bound into the exact centered-kernel
integral estimate. -/
theorem centeredMomentKernel_four_le_of_coveringForm (θ : ℝ) {p : ℝ≥0∞}
    (hp : 2 < p) (hp' : p ≠ ⊤) {a : ℝ} (t C : ℝ) (hC : 0 ≤ C)
    (ht : 0 < t)
    (hCoverForm : WeightedFormBound volume volume
      (fun x : Configuration 4 => a * configL1Norm x)
      (fun y : Configuration 4 => a * configL1Norm y) p.toReal p.toReal
      (coveringKernel 4 θ t)
      (ENNReal.ofReal (C * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)))) )
    (F G : Configuration 4 → ℝ)
    (hF : MemLp (fun x => F x * Real.exp (a * configL1Norm x)) p)
    (hG : MemLp (fun y => G y * Real.exp (a * configL1Norm y)) p) :
    Integrable (fun xy : Configuration 4 × Configuration 4 =>
      F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2) ∧
      |∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2| ≤
        C * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
          (eLpNorm (fun x => F x * Real.exp (a * configL1Norm x)) p).toReal *
          (eLpNorm (fun y => G y * Real.exp (a * configL1Norm y)) p).toReal := by
  classical
  have hr : 2 < p.toReal :=
    (ENNReal.toReal_lt_toReal (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hp').mpr hp
  have hpReal : 0 < p.toReal := lt_trans (by norm_num) hr
  have hw : Measurable (fun x : Configuration 4 => a * configL1Norm x) :=
    measurable_const.mul (measurable_configurationOneNorm (n := 4))
  have hcenteredAE := centeredMomentKernel_eq_coveringKernel
    (by decide : 1 ≤ 4) (by decide : 4 ≤ 4) θ ht
  have hcenteredAEVol : ∀ᵐ xy : Configuration 4 × Configuration 4 ∂volume,
      coveringKernel 4 θ t xy.1 xy.2 ≠ ⊤ ∧
        centeredMomentKernel 4 θ t xy.1 xy.2 =
          (coveringKernel 4 θ t xy.1 xy.2).toReal := by
    change ∀ᵐ xy : Configuration 4 × Configuration 4 ∂(volume.prod volume), _
    exact hcenteredAE
  have hKneTop : ∀ᵐ xy : Configuration 4 × Configuration 4 ∂(volume.prod volume),
      coveringKernel 4 θ t xy.1 xy.2 ≠ ⊤ := hcenteredAE.mono fun xy hxy => hxy.1
  have hformreal := weightedFormBound_real_form_bound
    (n := 4) (K := coveringKernel 4 θ t) (w := fun x => a * configL1Norm x)
    (p := p.toReal) hpReal (measurable_coveringKernel_four θ t) hKneTop
    ENNReal.ofReal_ne_top hCoverForm hw F G
    (by simpa only [ENNReal.ofReal_toReal hp'] using hF)
    (by simpa only [ENNReal.ofReal_toReal hp'] using hG)
  rcases hformreal with ⟨hint, hbound⟩
  have hBoundNonneg : 0 ≤ C * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) :=
    mul_nonneg hC (Real.rpow_nonneg ht.le _)
  have hrealBound := hbound
  rw [ENNReal.toReal_ofReal hBoundNonneg] at hrealBound
  have hRealF : eLpNorm (fun x => F x * Real.exp (a * configL1Norm x)) p =
      eLpNorm (fun x => F x * Real.exp (a * configL1Norm x)) (ENNReal.ofReal p.toReal) := by
    rw [ENNReal.ofReal_toReal hp']
  have hRealG : eLpNorm (fun y => G y * Real.exp (a * configL1Norm y)) p =
      eLpNorm (fun y => G y * Real.exp (a * configL1Norm y)) (ENNReal.ofReal p.toReal) := by
    rw [ENNReal.ofReal_toReal hp']
  rw [← hRealF, ← hRealG] at hrealBound
  let centeredIntegrand : Configuration 4 × Configuration 4 → ℝ :=
    fun xy => F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2
  let coveringIntegrand : Configuration 4 × Configuration 4 → ℝ :=
    fun xy => F xy.1 * (coveringKernel 4 θ t xy.1 xy.2).toReal * G xy.2
  have hIntEq :
      centeredIntegrand =ᵐ[volume] coveringIntegrand := by
    filter_upwards [hcenteredAEVol] with xy hxy
    dsimp [centeredIntegrand, coveringIntegrand]
    rw [hxy.2]
  have hintVol : Integrable
      coveringIntegrand volume := by
    change Integrable _ (volume.prod volume)
    exact hint
  have hintCentered : Integrable
      centeredIntegrand := integrable_real_congr_of_ae
        (f := coveringIntegrand) (g := centeredIntegrand) hintVol hIntEq.symm
  have hrealBoundVol :
      |∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * (coveringKernel 4 θ t xy.1 xy.2).toReal * G xy.2| ≤
        C * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
          (eLpNorm (fun x => F x * Real.exp (a * configL1Norm x)) p).toReal *
          (eLpNorm (fun y => G y * Real.exp (a * configL1Norm y)) p).toReal := by
    change |∫ xy : Configuration 4 × Configuration 4,
        F xy.1 * (coveringKernel 4 θ t xy.1 xy.2).toReal * G xy.2 ∂(volume.prod volume)| ≤ _
    exact hrealBound
  refine ⟨hintCentered, ?_⟩
  have hEqInt :
      |∫ xy : Configuration 4 × Configuration 4, centeredIntegrand xy| =
        |∫ xy : Configuration 4 × Configuration 4, coveringIntegrand xy| := by
    congr 1
    exact integral_congr_ae hIntEq
  rw [hEqInt]
  exact hrealBoundVol

/-- On bounded positive-time intervals, the four-particle centered-kernel form is absolutely integrable and bounded by `C t^{(3/2)(1 - 2/p)}` times the two exponentially weighted `Lᵖ` norms, for `2 < p < ∞`. -/
theorem centeredMomentKernel_four_le (θ : ℝ) {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤)
    {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ∃ c : ℝ, ∀ t : ℝ, 0 < t → t ≤ T → ∀ F G : Configuration 4 → ℝ,
      MemLp (fun x => F x * Real.exp (a * configL1Norm x)) p →
      MemLp (fun y => G y * Real.exp (a * configL1Norm y)) p →
      Integrable (fun xy : Configuration 4 × Configuration 4 =>
        F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2) ∧
      |∫ xy : Configuration 4 × Configuration 4,
          F xy.1 * centeredMomentKernel 4 θ t xy.1 xy.2 * G xy.2| ≤
        c * t ^ ((3 / 2 : ℝ) * (1 - 2 / p.toReal)) *
          (eLpNorm (fun x => F x * Real.exp (a * configL1Norm x)) p).toReal *
          (eLpNorm (fun y => G y * Real.exp (a * configL1Norm y)) p).toReal := by
  obtain ⟨C, hC, hcover⟩ := weightedFormBound_coveringKernel_four θ T hp hp' ha
  refine ⟨C, fun t ht htT F G hF hG => ?_⟩
  exact centeredMomentKernel_four_le_of_coveringForm θ hp hp' t C hC ht
    (hcover t ht htT) F G hF hG

end Critical2DKPZ.SHF.Tsai

end
