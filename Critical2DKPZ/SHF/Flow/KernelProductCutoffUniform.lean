/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.KernelProductCutoffTail
public import Critical2DKPZ.SHF.Flow.SlabProductsIdentities
public import Critical2DKPZ.SHF.Tsai.Defs
public import Critical2DKPZ.SHF.Tsai.Cutoff
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.SHF.Limit.LocalFinite
import Mathlib.Tactic

/-! # Uniform Gaussian cutoff tails for polymer kernel products -/

@[expose] public section

open MeasureTheory
open Filter
open scoped Topology
open scoped CompactlySupported
open Critical2DKPZ.SHF.Tsai
open Critical2DKPZ.SHF.Limit

noncomputable section

namespace Critical2DKPZ.SHF.Flow

private theorem measurable_polymerKernelProductPairing
    (ϑ : ℝ) (N : ℕ) (s t t' u : ℝ) (Φ : C_c(Plane × Plane, ℝ))
    (κ : Plane → Plane → ℝ) (hκm : Measurable fun p : Plane × Plane => κ p.1 p.2)
    (C M : ℝ) (hM : 0 ≤ M)
    (hΦ : ∀ p, |Φ p| ≤ M) (hκ : ∀ x y, |κ x y| ≤ C) :
    Measurable (fun ω => kernelProductPairing (polymerMeasure ϑ N s t ω) κ
      (polymerMeasure ϑ N t' u ω) Φ) := by
  classical
  by_cases hN : N = 0
  · subst N
    simp [polymerMeasure_zero_at_zero]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let SxSet : Set Site := latticePoint N '' (Prod.fst '' tsupport Φ)
    let SzSet : Set Site := latticePoint N '' (Prod.snd '' tsupport Φ)
    have hSxFin : SxSet.Finite :=
      finite_latticePoint_image_of_bounded (N := N)
        (Φ.hasCompactSupport.image continuous_fst).isBounded
    have hSzFin : SzSet.Finite :=
      finite_latticePoint_image_of_bounded (N := N)
        (Φ.hasCompactSupport.image continuous_snd).isBounded
    let Sx : Finset Site := hSxFin.toFinset
    let Sz : Finset Site := hSzFin.toFinset
    let n₁ := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
    let n₂ := evenCeil ((N : ℝ) * u) - evenCeil ((N : ℝ) * t')
    let W : Finset Site := Sx.biUnion fun x => Polymer.endpoints x n₁
    let Y : Finset Site := Sz.biUnion fun z => Polymer.endpoints z n₂
    let Q : Finset ((Site × Site) × (Site × Site)) :=
      (Sx.product W).product (Y.product Sz)
    let F : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
      Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1
    let G : ((Site × Site) × (Site × Site)) → Disorder → ℝ := fun q ω =>
      ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * s)) n₁ q.1.1 q.1.2 ω) *
      ((N : ℝ) / 4 * pointToPoint (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * t')) n₂ q.2.1 q.2.2 ω)
    have houter : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
        (q.1.1, q.2.2)) := by fun_prop
    have hmiddle : Measurable (fun q : (Plane × Plane) × (Plane × Plane) =>
        (q.1.2, q.2.1)) := by fun_prop
    have hFm : Measurable F := by
      dsimp [F]
      exact (Φ.measurable.comp houter).mul (hκm.comp hmiddle)
    have hFbound (q : (Plane × Plane) × (Plane × Plane)) : ‖F q‖ ≤ M * C := by
      dsimp [F]
      rw [abs_mul]
      exact mul_le_mul (hΦ _) (hκ _ _) (abs_nonneg _) hM
    have hzero (q : (Site × Site) × (Site × Site)) (ω : Disorder) (hq : q ∉ Q)
        (p : (Plane × Plane) × (Plane × Plane))
        (hp : p ∈ (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2)) : F p * G q ω = 0 := by
      have hparts : q.1.1 ∉ Sx ∨ q.1.2 ∉ W ∨ q.2.1 ∉ Y ∨ q.2.2 ∉ Sz := by
        by_contra h
        push Not at h
        exact hq (Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨h.1, h.2.1⟩,
            Finset.mem_product.mpr ⟨h.2.2.1, h.2.2.2⟩⟩)
      rcases hp with ⟨⟨hp₁, hp₂⟩, ⟨hp₃, hp₄⟩⟩
      have hq₁ : latticePoint N p.1.1 = q.1.1 := (mem_cell_iff N q.1.1 p.1.1).mp hp₁
      have hq₂ : latticePoint N p.1.2 = q.1.2 := (mem_cell_iff N q.1.2 p.1.2).mp hp₂
      have hq₃ : latticePoint N p.2.1 = q.2.1 := (mem_cell_iff N q.2.1 p.2.1).mp hp₃
      have hq₄ : latticePoint N p.2.2 = q.2.2 := (mem_cell_iff N q.2.2 p.2.2).mp hp₄
      have hΦzeroX (hx : q.1.1 ∉ Sx) : Φ (p.1.1, p.2.2) = 0 := by
          by_contra hne
          have hsupport := subset_tsupport Φ (Function.mem_support.mpr hne)
          apply hx
          exact hSxFin.mem_toFinset.mpr
            ⟨p.1.1, ⟨(p.1.1, p.2.2), hsupport, rfl⟩, hq₁⟩
      have hΦzeroZ (hz : q.2.2 ∉ Sz) : Φ (p.1.1, p.2.2) = 0 := by
          by_contra hne
          have hsupport := subset_tsupport Φ (Function.mem_support.mpr hne)
          apply hz
          exact hSzFin.mem_toFinset.mpr
            ⟨p.2.2, ⟨(p.1.1, p.2.2), hsupport, rfl⟩, hq₄⟩
      rcases hparts with hx | hw | hy | hz
      · simp [F, G, hΦzeroX hx]
      · by_cases hx : q.1.1 ∈ Sx
        · have hptp : pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s)) n₁ q.1.1 q.1.2 ω = 0 := by
            apply Polymer.pointToPoint_eq_zero_of_not_mem
            intro hreach
            have hendpoint : q.1.2 ∈ Polymer.endpoints q.1.1 n₁ := hreach
            exact hw (Finset.mem_biUnion.mpr ⟨q.1.1, hx,
              by simpa [n₁] using hendpoint⟩)
          simp [G, hptp]
        · simp [F, G, hΦzeroX hx]
      · by_cases hz : q.2.2 ∈ Sz
        · have hptp : pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * t')) n₂ q.2.1 q.2.2 ω = 0 := by
            apply Polymer.pointToPoint_eq_zero_of_not_mem
            intro hreach
            have hendpoint := mem_endpoints_reverse hreach
            exact hy (Finset.mem_biUnion.mpr ⟨q.2.2, hz,
              by simpa [n₂] using hendpoint⟩)
          simp [G, hptp]
        · simp [F, G, hΦzeroZ hz]
      · simp [F, G, hΦzeroZ hz]
    have hsum (ω : Disorder) :
        kernelProductPairing (polymerMeasure ϑ N s t ω) κ
          (polymerMeasure ϑ N t' u ω) Φ =
        ∑ q ∈ Q, (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2), F p) * G q ω := by
      rw [kernelProductPairing_polymer_eq_densityIntegral]
      let Gω : ((Site × Site) × (Site × Site)) → ℝ := fun q => G q ω
      have hexp := integral_finiteLatticeFourStep_test_eq_cellSum N hNpos F hFm
        (M * C) hFbound Gω Q (fun q hq p hp => hzero q ω hq p hp)
      calc
        _ = ∫ p : (Plane × Plane) × (Plane × Plane),
            F p * Gω ((latticePoint N p.1.1, latticePoint N p.1.2),
              (latticePoint N p.2.1, latticePoint N p.2.2)) := by
                apply integral_congr_ae
                filter_upwards [] with p
                simp only [F, G, Gω, rescaledP2P, n₁, n₂]
                ring
        _ = _ := hexp
        _ = _ := by simp [Gω]
    rw [show (fun ω => kernelProductPairing (polymerMeasure ϑ N s t ω) κ
        (polymerMeasure ϑ N t' u ω) Φ) =
        fun ω => ∑ q ∈ Q, (∫ p in (cell N q.1.1 ×ˢ cell N q.1.2) ×ˢ
          (cell N q.2.1 ×ˢ cell N q.2.2), F p) * G q ω by
          funext ω; exact hsum ω]
    apply Q.measurable_fun_sum
    intro q hq
    exact measurable_const.mul
      ((measurable_const.mul (Polymer.measurable_pointToPoint (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * s)) n₁ q.1.1 q.1.2)).mul
       (measurable_const.mul (Polymer.measurable_pointToPoint (criticalBeta ϑ N)
        (evenCeil ((N : ℝ) * t')) n₂ q.2.1 q.2.2)))

private theorem eventually_secondCompact_mass_sixth_integrable_le
    (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (Bset : Set Plane) (hBset : IsCompact Bset) (R : ℝ) (hR : 0 ≤ R)
    (hBbox : ∀ y ∈ Bset, ‖y‖ ≤ R) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω =>
        ((polymerMeasure ϑ N s t ω ((Set.univ : Set Plane) ×ˢ Bset)).toReal) ^ 6)
        disorderLaw ∧
      ∫ ω,
        ((polymerMeasure ϑ N s t ω ((Set.univ : Set Plane) ×ˢ Bset)).toReal) ^ 6
          ∂disorderLaw ≤ C := by
  obtain ⟨Cflat, hflat⟩ := eventually_secondCutoff_sixth_integrable_le
    ϑ hs hst R hR
  let C := max Cflat 0
  refine ⟨C, ?_⟩
  filter_upwards [hflat] with N hflatN
  let S : Set (Plane × Plane) := (Set.univ : Set Plane) ×ˢ Bset
  let Y : Disorder → ℝ := fun ω => (polymerMeasure ϑ N s t ω S).toReal
  let Z : Disorder → ℝ := fun ω =>
    ∫ y, polymerTailCutoff R hR y
      ∂((polymerMeasure ϑ N s t ω).map Prod.snd)
  have hYm : Measurable Y := by
    dsimp [Y, S]
    exact measurable_polymerMeasure_real_mass ϑ N s t _
      (MeasurableSet.univ.prod hBset.measurableSet)
  have hYnonneg (ω : Disorder) : 0 ≤ Y ω := by
    exact ENNReal.toReal_nonneg
  have hZnonneg (ω : Disorder) : 0 ≤ Z ω :=
    integral_nonneg fun y => polymerTailCutoff_nonneg R hR y
  have hYleZ (ω : Disorder) : Y ω ≤ Z ω := by
    dsimp [Y, Z, S]
    have h := polymerMeasure_compact_second_mass_le_flatCutoff
      ϑ N s t ω Bset hBset R hR hBbox
    have hfun : (fun y : Plane => |polymerTailCutoff R hR y|) =
        fun y => polymerTailCutoff R hR y := by
      funext y
      exact abs_of_nonneg (polymerTailCutoff_nonneg R hR y)
    rw [hfun] at h
    exact h
  have hZ6 : Integrable (fun ω => Z ω ^ 6) disorderLaw := by
    dsimp [Z]
    exact hflatN.1
  have hY6 : Integrable (fun ω => Y ω ^ 6) disorderLaw := by
    apply hZ6.mono' (hYm.pow_const 6).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hYnonneg ω) 6)]
    exact pow_le_pow_left₀ (hYnonneg ω) (hYleZ ω) 6
  have hmoment : ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ C := by
    calc
      _ ≤ ∫ ω, Z ω ^ 6 ∂disorderLaw :=
        integral_mono_ae hY6 hZ6 (Filter.Eventually.of_forall fun ω =>
          pow_le_pow_left₀ (hYnonneg ω) (hYleZ ω) 6)
      _ ≤ Cflat := hflatN.2
      _ ≤ max Cflat 0 := le_max_left _ _
  refine ⟨?_, ?_⟩
  · simpa [Y, S] using hY6
  · simpa [Y, S] using hmoment

private theorem exp_truncated_tail_identity (a R : ℝ) :
    Real.exp (a * R ^ 2 / 96) ^ 3 * Real.exp (-a * R ^ 2 / 16) =
      Real.exp (-a * R ^ 2 / 32) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

private theorem exp_truncated_moment_identity (a R : ℝ) :
    (Real.exp (a * R ^ 2 / 96))⁻¹ ^ 2 = Real.exp (-a * R ^ 2 / 48) := by
  rw [inv_pow, ← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  ring

private theorem exp_gaussian_square_identity (c R : ℝ) :
    Real.exp (-c * (R / 2) ^ 2) ^ 2 = Real.exp (-c * R ^ 2 / 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private theorem neg_scaled_nonneg_le {a d k x : ℝ} (_hk : 0 < k)
    (hd : d ≤ a / k) (hx : 0 ≤ x) : -a * x / k ≤ -d * x := by
  have hmul := mul_le_mul_of_nonneg_right hd hx
  calc
    -a * x / k = -(a / k * x) := by ring
    _ ≤ -(d * x) := neg_le_neg hmul
    _ = -d * x := by ring

/-- A Gaussian connector bound makes the cutoff error small in mean square as the cutoff radius grows; square integrability follows from `memLp_kernelProductPairing_two` and `memLp_kernelProductCutoffPairing_two`. -/
theorem kernelProduct_cutoff_tail (ϑ : ℝ) {s t t' u : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (htt' : t ≤ t') (ht'u : t' < u) (Φ : C_c(Plane × Plane, ℝ))
    (κ : ℕ → Plane → Plane → ℝ)
    (hκm : ∀ N, Measurable fun q : Plane × Plane => κ N q.1 q.2)
    (hκ : ∃ C c : ℝ, 0 < c ∧ ∀ N w y,
      |κ N w y| ≤ C * Real.exp (-c * ‖w - y‖ ^ 2)) :
    ∀ ε > 0, ∃ R₀ : ℝ, ∀ R ≥ R₀, ∀ᶠ N : ℕ in atTop,
      ∫ ω, (kernelProductPairing (polymerMeasure ϑ N s t ω) (κ N)
          (polymerMeasure ϑ N t' u ω) Φ -
        ∫ q, Φ (q.1.1, q.2.2) * κ N q.1.2 q.2.1 *
          ballCutoff R q.1.2 * ballCutoff R q.2.1
          ∂((polymerMeasure ϑ N s t ω).prod
            (polymerMeasure ϑ N t' u ω))) ^ 2 ∂disorderLaw ≤ ε := by
  classical
  intro ε hε
  obtain ⟨Cκ, c, hc, hκbound⟩ := hκ
  have hCκ : 0 ≤ Cκ := by
    by_contra hC
    have hCneg : Cκ < 0 := lt_of_not_ge hC
    have h00 := hκbound 0 (0 : Plane) 0
    have h00' : |κ 0 0 0| ≤ Cκ := by simpa using h00
    have habs : 0 ≤ |κ 0 0 0| := abs_nonneg _
    linarith
  have hκle (N : ℕ) (x y : Plane) : |κ N x y| ≤ Cκ := by
    calc
      |κ N x y| ≤ Cκ * Real.exp (-c * ‖x - y‖ ^ 2) := hκbound N x y
      _ ≤ Cκ := by
        calc
          Cκ * Real.exp (-c * ‖x - y‖ ^ 2) ≤ Cκ * 1 := by
            apply mul_le_mul_of_nonneg_left _ hCκ
            apply Real.exp_le_one_iff.mpr
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _)
          _ = Cκ := by ring
  obtain ⟨CΦ, hΦnorm⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  let M := max CΦ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hΦ (p : Plane × Plane) : |Φ p| ≤ M := by
    calc
      |Φ p| = ‖Φ p‖ := (Real.norm_eq_abs _).symm
      _ ≤ CΦ := hΦnorm p
      _ ≤ M := le_max_left _ _
  let A : Set Plane := Prod.fst '' tsupport Φ
  let B : Set Plane := Prod.snd '' tsupport Φ
  have hA : IsCompact A := Φ.hasCompactSupport.image continuous_fst
  have hB : IsCompact B := Φ.hasCompactSupport.image continuous_snd
  obtain ⟨RA, hRA⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hA.isBounded
  obtain ⟨RB, hRB⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hB.isBounded
  let BA := max RA 0
  let BB := max RB 0
  have hBA : 0 ≤ BA := le_max_right _ _
  have hBB : 0 ≤ BB := le_max_right _ _
  have hAbox : ∀ x ∈ A, ‖x‖ ≤ BA := by
    intro x hx
    have hxball := hRA hx
    have hxnorm : ‖x‖ ≤ RA := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hxball
    exact hxnorm.trans (le_max_left _ _)
  have hBbox : ∀ y ∈ B, ‖y‖ ≤ BB := by
    intro y hy
    have hyball := hRB hy
    have hynorm : ‖y‖ ≤ RB := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hyball
    exact hynorm.trans (le_max_left _ _)
  have houter : ∀ p, Φ p ≠ 0 → p.1 ∈ A ∧ p.2 ∈ B := by
    intro p hp
    have hpK : p ∈ tsupport Φ := subset_tsupport Φ (Function.mem_support.mpr hp)
    exact ⟨⟨p, hpK, rfl⟩, ⟨p, hpK, rfl⟩⟩
  obtain ⟨Ctail, a, hCtail, ha, htail⟩ :=
    eventually_expected_polymerMeasure_pair_tail_le
      ϑ hs hst A hA.measurableSet BA hBA hAbox
  obtain ⟨CXraw, hXevent⟩ := eventually_firstCompact_mass_sixth_integrable_le
    ϑ hs hst A hA BA hBA hAbox
  have ht'0 : 0 ≤ t' := by
    exact (le_trans hs hst.le).trans htt'
  obtain ⟨CYraw, hYevent⟩ := eventually_secondCompact_mass_sixth_integrable_le
    ϑ ht'0 ht'u B hB BB hBB hBbox
  let CX := max CXraw 0
  let CY := max CYraw 0
  have hCX : 0 ≤ CX := le_max_right _ _
  have hCY : 0 ≤ CY := le_max_right _ _
  let baseR := 2 * (BA + 8)
  let tailConst := Ctail * Real.exp (a * BA ^ 2) * (4 * Real.pi / a) *
    (volume A).toReal
  have htailConst : 0 ≤ tailConst := by
    dsimp [tailConst]
    positivity
  let decayConst := Ctail * Real.exp (a * BA ^ 2) * (4 * Real.pi / a) *
    (volume A).toReal
  have hdecayConst : 0 ≤ decayConst := by
    dsimp [decayConst]
    positivity
  let d := min (a / 32) (min (a / 48) (c / 2))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  let massConst := 1 + CX + CY + (1 + CX + CX + CY)
  have hmassConst : 0 ≤ massConst := by positivity
  let coeff := 2 * (M * Cκ) ^ 2
  have hcoeff : 0 ≤ coeff := by positivity
  let finalConst := coeff * (decayConst + CX + CY + massConst)
  have hfinalConst : 0 ≤ finalConst := by
    apply mul_nonneg hcoeff
    positivity
  have hdecay : Tendsto (fun R : ℝ => finalConst * Real.exp (-d * R ^ 2))
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun R : ℝ => R ^ 2) atTop atTop :=
      tendsto_pow_atTop (by norm_num : 2 ≠ 0)
    have harg : Tendsto (fun R : ℝ => -d * R ^ 2) atTop atBot := by
      have h := hpow.const_mul_atTop_of_neg (neg_lt_zero.mpr hd)
      exact h
    have hexp : Tendsto (fun R : ℝ => Real.exp (-d * R ^ 2)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp harg
    simpa using tendsto_const_nhds.mul hexp
  have hsmall : ∀ᶠ R : ℝ in atTop,
      finalConst * Real.exp (-d * R ^ 2) ≤ ε := by
    filter_upwards [hdecay.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)] with R hR
    have hdist : |finalConst * Real.exp (-d * R ^ 2)| < ε := by
      simpa only [Real.dist_eq, sub_zero] using hR
    rw [abs_of_nonneg (mul_nonneg hfinalConst (Real.exp_nonneg _))] at hdist
    exact hdist.le
  obtain ⟨Rε, hRε⟩ := Filter.eventually_atTop.1 hsmall
  refine ⟨max baseR Rε, ?_⟩
  intro R hR
  have hRbase : baseR ≤ R := (le_max_left _ _).trans hR
  have hReps : Rε ≤ R := (le_max_right _ _).trans hR
  have hRnonneg : 0 ≤ R := by dsimp [baseR] at hRbase; linarith [hBA]
  have hhalf : BA + 8 ≤ R / 2 := by dsimp [baseR] at hRbase; linarith
  have hFbound : finalConst * Real.exp (-d * R ^ 2) ≤ ε := hRε R hReps
  filter_upwards [hXevent, hYevent, htail (R / 2) hhalf] with N hXN hYN hTN
  let leftSet : Set (Plane × Plane) := A ×ˢ (Set.univ : Set Plane)
  let rightSet : Set (Plane × Plane) := (Set.univ : Set Plane) ×ˢ B
  let strictTail : Set (Plane × Plane) :=
    A ×ˢ {y : Plane | R / 2 < ‖y‖}
  have hstrictMeas : MeasurableSet strictTail := by
    exact hA.measurableSet.prod
      (isOpen_lt continuous_const continuous_norm).measurableSet
  let X : Disorder → ℝ := fun ω =>
    (polymerMeasure ϑ N s t ω leftSet).toReal
  let Y : Disorder → ℝ := fun ω =>
    (polymerMeasure ϑ N t' u ω rightSet).toReal
  let T : Disorder → ℝ := fun ω =>
    (polymerMeasure ϑ N s t ω strictTail).toReal
  have hXm : Measurable X := by
    dsimp [X, leftSet]
    exact measurable_polymerMeasure_real_mass ϑ N s t _
      (hA.measurableSet.prod MeasurableSet.univ)
  have hYm : Measurable Y := by
    dsimp [Y, rightSet]
    exact measurable_polymerMeasure_real_mass ϑ N t' u _
      (MeasurableSet.univ.prod hB.measurableSet)
  have hTm : Measurable T := by
    dsimp [T, strictTail]
    exact measurable_polymerMeasure_real_mass ϑ N s t _ hstrictMeas
  have hXnonneg (ω : Disorder) : 0 ≤ X ω := ENNReal.toReal_nonneg
  have hYnonneg (ω : Disorder) : 0 ≤ Y ω := ENNReal.toReal_nonneg
  have hTnonneg (ω : Disorder) : 0 ≤ T ω := ENNReal.toReal_nonneg
  have hXfinite (ω : Disorder) : polymerMeasure ϑ N s t ω leftSet < ⊤ := by
    exact polymerMeasure_finite_first_compact ϑ N s t ω A hA
  have hYfinite (ω : Disorder) : polymerMeasure ϑ N t' u ω rightSet < ⊤ := by
    exact polymerMeasure_finite_second_compact ϑ N t' u ω B hB
  have hTfinite (ω : Disorder) : polymerMeasure ϑ N s t ω strictTail < ⊤ := by
    apply lt_of_le_of_lt (measure_mono ?_) (hXfinite ω)
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  have hTleX (ω : Disorder) : T ω ≤ X ω := by
    dsimp [T, X]
    apply ENNReal.toReal_mono (hXfinite ω).ne
    exact measure_mono (by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      exact ⟨hx, Set.mem_univ _⟩)
  have hX6 : Integrable (fun ω => X ω ^ 6) disorderLaw := by
    simpa [X, leftSet] using hXN.1
  have hY6 : Integrable (fun ω => Y ω ^ 6) disorderLaw := by
    simpa [Y, rightSet] using hYN.1
  have hXmoment : ∫ ω, X ω ^ 6 ∂disorderLaw ≤ CX := by
    have hraw : ∫ ω, X ω ^ 6 ∂disorderLaw ≤ CXraw := by
      simpa [X, leftSet] using hXN.2
    exact hraw.trans (le_max_left _ _)
  have hYmoment : ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ CY := by
    have hraw : ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ CYraw := by
      simpa [Y, rightSet] using hYN.2
    exact hraw.trans (le_max_left _ _)
  have hXint : Integrable X disorderLaw := by
    have hX6norm : Integrable (fun ω => ‖X ω‖ ^ 6) disorderLaw := by
      apply hX6.congr
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hXnonneg ω)]
    have h := integrable_norm_pow_of_le hXm.aestronglyMeasurable
      (by norm_num : 1 ≤ 6) hX6norm
    have hfun : (fun ω => ‖X ω‖ ^ 1) = X := by
      funext ω
      rw [pow_one, Real.norm_eq_abs, abs_of_nonneg (hXnonneg ω)]
    rw [hfun] at h
    exact h
  have hYint : Integrable Y disorderLaw := by
    have hY6norm : Integrable (fun ω => ‖Y ω‖ ^ 6) disorderLaw := by
      apply hY6.congr
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnonneg ω)]
    have h := integrable_norm_pow_of_le hYm.aestronglyMeasurable
      (by norm_num : 1 ≤ 6) hY6norm
    have hfun : (fun ω => ‖Y ω‖ ^ 1) = Y := by
      funext ω
      rw [pow_one, Real.norm_eq_abs, abs_of_nonneg (hYnonneg ω)]
    rw [hfun] at h
    exact h
  have hTint : Integrable T disorderLaw := by
    apply hXint.mono' hTm.aestronglyMeasurable
    filter_upwards [] with ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hTnonneg ω),
      abs_of_nonneg (hXnonneg ω)] using hTleX ω
  have hTailStrict :
      ∫⁻ ω, polymerMeasure ϑ N s t ω strictTail ∂disorderLaw ≤
        ENNReal.ofReal (Ctail * Real.exp (a * BA ^ 2)) *
          ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * (R / 2) ^ 2 / 4)) *
            volume A := by
    calc
      _ ≤ ∫⁻ ω, polymerMeasure ϑ N s t ω
          (A ×ˢ {y : Plane | R / 2 ≤ ‖y‖}) ∂disorderLaw := by
            apply lintegral_mono
            intro ω
            apply measure_mono
            intro p hp
            rcases p with ⟨x, y⟩
            change x ∈ A ∧ R / 2 < ‖y‖ at hp
            change x ∈ A ∧ R / 2 ≤ ‖y‖
            exact ⟨hp.1, le_of_lt hp.2⟩
      _ ≤ _ := hTN
  let tailE : ENNReal :=
    ENNReal.ofReal (Ctail * Real.exp (a * BA ^ 2)) *
      ENNReal.ofReal ((4 * Real.pi / a) * Real.exp (-a * (R / 2) ^ 2 / 4)) *
        volume A
  have htailEtop : tailE < ⊤ := by
    dsimp [tailE]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      hA.measure_lt_top
  have hTmean : ∫ ω, T ω ∂disorderLaw ≤ tailE.toReal := by
    have htailmeas : Measurable fun ω => polymerMeasure ϑ N s t ω strictTail :=
      (Measure.measurable_coe hstrictMeas).comp (measurable_polymerMeasure ϑ N s t)
    have htailfiniteAE : ∀ᵐ ω ∂disorderLaw,
        polymerMeasure ϑ N s t ω strictTail < ⊤ :=
      Filter.Eventually.of_forall hTfinite
    have htoReal := integral_toReal htailmeas.aemeasurable htailfiniteAE
    calc
      _ = (∫⁻ ω, polymerMeasure ϑ N s t ω strictTail ∂disorderLaw).toReal := by
        exact htoReal
      _ ≤ tailE.toReal := ENNReal.toReal_mono htailEtop.ne hTailStrict
  have htailMeanBound : ∫ ω, T ω ∂disorderLaw ≤
      decayConst * Real.exp (-a * R ^ 2 / 16) := by
    have hreal : tailE.toReal = decayConst * Real.exp (-a * R ^ 2 / 16) := by
      dsimp [tailE, decayConst]
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
      rw [show -a * (R / 2) ^ 2 / 4 = -a * R ^ 2 / 16 by ring]
      ring
    rw [hreal] at hTmean
    exact hTmean
  let L : ℝ := Real.exp (a * R ^ 2 / 96)
  have hL : 0 < L := Real.exp_pos _
  have hmassSq : Integrable (fun ω => (T ω * Y ω) ^ 2) disorderLaw ∧
      ∫ ω, (T ω * Y ω) ^ 2 ∂disorderLaw ≤
        L ^ 3 * ∫ ω, T ω ∂disorderLaw +
          L⁻¹ ^ 2 * (∫ ω, X ω ^ 6 ∂disorderLaw + ∫ ω, Y ω ^ 6 ∂disorderLaw) := by
    exact integral_mul_sq_le_two_sixth_truncation disorderLaw X Y T Y L hL
      hXm hYm hTm hYm
      (Filter.Eventually.of_forall hXnonneg) (Filter.Eventually.of_forall hYnonneg)
      (Filter.Eventually.of_forall hTnonneg) (Filter.Eventually.of_forall hYnonneg)
      (Filter.Eventually.of_forall hTleX) (Filter.Eventually.of_forall fun _ => le_rfl)
      hTint hX6 hY6
  have hxySq : Integrable (fun ω => (X ω * Y ω) ^ 2) disorderLaw ∧
      ∫ ω, (X ω * Y ω) ^ 2 ∂disorderLaw ≤
        ∫ ω, X ω ∂disorderLaw +
          (∫ ω, X ω ^ 6 ∂disorderLaw + ∫ ω, Y ω ^ 6 ∂disorderLaw) := by
    simpa only [one_pow, inv_one, one_mul] using
      (integral_mul_sq_le_two_sixth_truncation disorderLaw X Y X Y 1
        one_pos hXm hYm hXm hYm
        (Filter.Eventually.of_forall hXnonneg) (Filter.Eventually.of_forall hYnonneg)
        (Filter.Eventually.of_forall hXnonneg) (Filter.Eventually.of_forall hYnonneg)
        (Filter.Eventually.of_forall fun _ => le_rfl)
        (Filter.Eventually.of_forall fun _ => le_rfl) hXint hX6 hY6)
  have hXmean : ∫ ω, X ω ∂disorderLaw ≤ 1 + CX := by
    have hsum : Integrable (fun ω => 1 + X ω ^ 6) disorderLaw :=
      (integrable_const 1).add hX6
    have hpoint (ω : Disorder) : X ω ≤ 1 + X ω ^ 6 := by
      have h := hXnonneg ω
      by_cases hle : X ω ≤ 1
      · linarith [pow_nonneg h 6]
      · have hone : 1 ≤ X ω := le_of_not_ge hle
        have hpow : 1 ≤ X ω ^ 5 := one_le_pow₀ hone
        have hXle : X ω ≤ X ω ^ 6 := by
          calc
            X ω = X ω * 1 := by ring
            _ ≤ X ω * X ω ^ 5 := mul_le_mul_of_nonneg_left hpow h
            _ = X ω ^ 6 := by ring
        linarith
    calc
      _ ≤ ∫ ω, (1 + X ω ^ 6) ∂disorderLaw :=
        integral_mono_ae hXint hsum (Filter.Eventually.of_forall hpoint)
      _ = 1 + ∫ ω, X ω ^ 6 ∂disorderLaw := by
        rw [integral_add (integrable_const 1) hX6]
        simp
      _ ≤ 1 + CX := by linarith
  have hxyMoment : ∫ ω, (X ω * Y ω) ^ 2 ∂disorderLaw ≤ massConst := by
    calc
      _ ≤ ∫ ω, X ω ∂disorderLaw +
          (∫ ω, X ω ^ 6 ∂disorderLaw + ∫ ω, Y ω ^ 6 ∂disorderLaw) := hxySq.2
      _ ≤ 1 + CX + (CX + CY) := by
          exact add_le_add hXmean (add_le_add hXmoment hYmoment)
      _ ≤ massConst := by dsimp [massConst]; linarith [hCX, hCY]

  let κcut (n : ℕ) (x y : Plane) : ℝ :=
    κ n x y * ballCutoff R x * ballCutoff R y
  have hκcutMeas (n : ℕ) :
      Measurable (fun p : Plane × Plane => κcut n p.1 p.2) := by
    have hm := (hκm n).mul
      (((continuous_ballCutoff R).measurable.comp measurable_fst).mul
        ((continuous_ballCutoff R).measurable.comp measurable_snd))
    have heq :
        (fun p : Plane × Plane => κ n p.1 p.2 * ballCutoff R p.1 * ballCutoff R p.2) =
          fun p => κ n p.1 p.2 * (ballCutoff R p.1 * ballCutoff R p.2) := by
      funext p
      ring
    dsimp [κcut]
    rw [heq]
    exact hm
  have hcutAbs (x : Plane) : |ballCutoff R x| ≤ 1 := by
    rw [abs_of_nonneg (ballCutoff_mem_Icc R x).1]
    exact (ballCutoff_mem_Icc R x).2
  have hκcutBound (n : ℕ) (x y : Plane) : |κcut n x y| ≤ Cκ := by
    dsimp [κcut]
    rw [abs_mul, abs_mul]
    calc
      |κ n x y| * |ballCutoff R x| * |ballCutoff R y| ≤
          |κ n x y| * 1 * |ballCutoff R y| := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_left (hcutAbs x) (abs_nonneg _)
            · exact abs_nonneg _
      _ ≤ |κ n x y| * 1 * 1 := by
            exact mul_le_mul_of_nonneg_left (hcutAbs y) (by positivity)
      _ = |κ n x y| := by ring
      _ ≤ Cκ := hκle n x y
  have hpairMeas (n : ℕ) :
      Measurable (fun ω => kernelProductPairing
        (polymerMeasure ϑ N s t ω) (κ n) (polymerMeasure ϑ N t' u ω) Φ) :=
    measurable_polymerKernelProductPairing ϑ N s t t' u Φ (κ n) (hκm n)
      Cκ M hM hΦ (hκle n)
  have hpairCutMeas (n : ℕ) :
      Measurable (fun ω => kernelProductPairing
        (polymerMeasure ϑ N s t ω) (κcut n) (polymerMeasure ϑ N t' u ω) Φ) :=
    measurable_polymerKernelProductPairing ϑ N s t t' u Φ (κcut n) (hκcutMeas n)
      Cκ M hM hΦ (hκcutBound n)
  let E : Disorder → ℝ := fun ω =>
    kernelProductPairing (polymerMeasure ϑ N s t ω) (κ N)
      (polymerMeasure ϑ N t' u ω) Φ -
    kernelProductPairing (polymerMeasure ϑ N s t ω) (κcut N)
      (polymerMeasure ϑ N t' u ω) Φ
  have hEm : Measurable E := (hpairMeas N).sub (hpairCutMeas N)
  have hcutPairing (μ ν : Measure (Plane × Plane)) :
      (∫ q, Φ (q.1.1, q.2.2) * κ N q.1.2 q.2.1 *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂(μ.prod ν)) =
      kernelProductPairing μ (κcut N) ν Φ := by
    rw [kernelProductPairing]
    apply integral_congr_ae
    filter_upwards [] with q
    dsimp [κcut]
    ring
  have hEtarget (ω : Disorder) : E ω =
      kernelProductPairing (polymerMeasure ϑ N s t ω) (κ N)
          (polymerMeasure ϑ N t' u ω) Φ -
        ∫ q, Φ (q.1.1, q.2.2) * κ N q.1.2 q.2.1 *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂
            ((polymerMeasure ϑ N s t ω).prod (polymerMeasure ϑ N t' u ω)) := by
    dsimp [E]
    rw [hcutPairing (polymerMeasure ϑ N s t ω) (polymerMeasure ϑ N t' u ω)]
  have hEintegrandMeas : Measurable (fun ω => E ω ^ 2) := hEm.pow_const 2

  have htailErrorBound (ω : Disorder) : E ω ^ 2 ≤
      coeff * (T ω * Y ω) ^ 2 +
        coeff * (Real.exp (-c * (R / 2) ^ 2) * X ω * Y ω) ^ 2 := by
    let μ₀ := polymerMeasure ϑ N s t ω
    let ν₀ := polymerMeasure ϑ N t' u ω
    let μ := μ₀.restrict leftSet
    let ν := ν₀.restrict rightSet
    have hμfinite : IsFiniteMeasure μ := ⟨by
      rw [Measure.restrict_apply_univ]
      simpa [μ, μ₀, leftSet] using hXfinite ω⟩
    have hνfinite : IsFiniteMeasure ν := ⟨by
      rw [Measure.restrict_apply_univ]
      simpa [ν, ν₀, rightSet] using hYfinite ω⟩
    have hμtail : μ.real (kernelProductSecondTail (R / 2)) = T ω := by
      change (μ (kernelProductSecondTail (R / 2))).toReal = T ω
      have htailMeas : MeasurableSet (kernelProductSecondTail (R / 2)) := by
        change MeasurableSet {p : Plane × Plane | R / 2 < ‖p.2‖}
        exact (isOpen_lt continuous_const
          (continuous_norm.comp continuous_snd)).measurableSet
      rw [Measure.restrict_apply htailMeas]
      have hsets : kernelProductSecondTail (R / 2) ∩ leftSet = strictTail := by
        ext p
        rcases p with ⟨x, y⟩
        simp [kernelProductSecondTail, leftSet, strictTail, and_comm]
      rw [hsets]

    have hμall : μ.real Set.univ = X ω := by
      change (μ Set.univ).toReal = X ω
      rw [Measure.restrict_apply_univ]
    have hνall : ν.real Set.univ = Y ω := by
      change (ν Set.univ).toReal = Y ω
      rw [Measure.restrict_apply_univ]
    have hμ₀SFinite : SFinite μ₀ := by
      change SFinite ((volume : Measure (Plane × Plane)).withDensity fun p =>
        ENNReal.ofReal (rescaledP2P ϑ N s t p ω))
      have hvol : SFinite (volume : Measure (Plane × Plane)) := by infer_instance
      infer_instance
    have hν₀SFinite : SFinite ν₀ := by
      change SFinite ((volume : Measure (Plane × Plane)).withDensity fun p =>
        ENNReal.ofReal (rescaledP2P ϑ N t' u p ω))
      have hvol : SFinite (volume : Measure (Plane × Plane)) := by infer_instance
      infer_instance
    have hpairRestrict :
        kernelProductPairing μ₀ (κ N) ν₀ Φ =
          kernelProductPairing μ (κ N) ν Φ :=
      @kernelProductPairing_restrict_outer_support μ₀ ν₀ (κ N) Φ A B
        hμ₀SFinite hν₀SFinite hA.measurableSet hB.measurableSet houter
    have hpairCutRestrict :
        kernelProductPairing μ₀ (κcut N) ν₀ Φ =
          kernelProductPairing μ (κcut N) ν Φ :=
      @kernelProductPairing_restrict_outer_support μ₀ ν₀ (κcut N) Φ A B
        hμ₀SFinite hν₀SFinite hA.measurableSet hB.measurableSet houter
    have hErestrict : E ω =
        kernelProductPairing μ (κ N) ν Φ -
          kernelProductPairing μ (κcut N) ν Φ := by
      change kernelProductPairing μ₀ (κ N) ν₀ Φ -
          kernelProductPairing μ₀ (κcut N) ν₀ Φ = _
      rw [hpairRestrict, hpairCutRestrict]
    have hdet := @sq_kernelProductPairing_cutoff_error_le_leftTail_add_gaussian
      μ ν hμfinite hνfinite (κ N) (hκm N) Cκ c hCκ hc (hκbound N) Φ M hM hΦ R hRnonneg
    rw [hμtail, hνall, hμall] at hdet
    rw [hcutPairing μ ν] at hdet
    rw [hErestrict]
    simpa [coeff] using hdet

  let G : Disorder → ℝ := fun ω =>
    coeff * (T ω * Y ω) ^ 2 +
      (coeff * Real.exp (-c * (R / 2) ^ 2) ^ 2) * (X ω * Y ω) ^ 2
  have hGfirst : Integrable (fun ω => coeff * (T ω * Y ω) ^ 2) disorderLaw := by
    exact hmassSq.1.const_mul coeff
  have hGsecond : Integrable (fun ω =>
      (coeff * Real.exp (-c * (R / 2) ^ 2) ^ 2) * (X ω * Y ω) ^ 2) disorderLaw := by
    have hbase := hxySq.1.const_mul (coeff * Real.exp (-c * (R / 2) ^ 2) ^ 2)
    exact hbase
  have hGint : Integrable G disorderLaw := by
    dsimp [G]
    exact hGfirst.add hGsecond
  have hE2int : Integrable (fun ω => E ω ^ 2) disorderLaw := by
    apply hGint.mono' hEintegrandMeas.aestronglyMeasurable
    filter_upwards [] with ω
    change ‖E ω ^ 2‖ ≤ G ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (E ω))]
    calc
      E ω ^ 2 ≤ coeff * (T ω * Y ω) ^ 2 +
          coeff * (Real.exp (-c * (R / 2) ^ 2) * X ω * Y ω) ^ 2 := htailErrorBound ω
      _ = G ω := by dsimp [G]; ring
  have hGintegral : ∫ ω, G ω ∂disorderLaw =
      coeff * ∫ ω, (T ω * Y ω) ^ 2 ∂disorderLaw +
        (coeff * Real.exp (-c * (R / 2) ^ 2) ^ 2) *
          ∫ ω, (X ω * Y ω) ^ 2 ∂disorderLaw := by
    dsimp [G]
    rw [integral_add hGfirst hGsecond, integral_const_mul, integral_const_mul]
  have hmomentSum : ∫ ω, X ω ^ 6 ∂disorderLaw +
      ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ CX + CY := add_le_add hXmoment hYmoment
  have htailProductSmall : L ^ 3 * ∫ ω, T ω ∂disorderLaw ≤
      decayConst * Real.exp (-d * R ^ 2) := by
    calc
      _ ≤ L ^ 3 * (decayConst * Real.exp (-a * R ^ 2 / 16)) :=
        mul_le_mul_of_nonneg_left htailMeanBound (by positivity)
      _ = decayConst * Real.exp (-a * R ^ 2 / 32) := by
        calc
          _ = decayConst * (Real.exp (a * R ^ 2 / 96) ^ 3 *
                Real.exp (-a * R ^ 2 / 16)) := by dsimp [L]; ring
          _ = _ := by rw [exp_truncated_tail_identity]
      _ ≤ decayConst * Real.exp (-d * R ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hdecayConst
        apply Real.exp_le_exp.mpr
        have hd' : d ≤ a / 32 := min_le_left _ _
        exact neg_scaled_nonneg_le (by norm_num) hd' (sq_nonneg R)
  have hmomentProductSmall : L⁻¹ ^ 2 *
      (∫ ω, X ω ^ 6 ∂disorderLaw + ∫ ω, Y ω ^ 6 ∂disorderLaw) ≤
        (CX + CY) * Real.exp (-d * R ^ 2) := by
    calc
      _ = Real.exp (-a * R ^ 2 / 48) *
          (∫ ω, X ω ^ 6 ∂disorderLaw + ∫ ω, Y ω ^ 6 ∂disorderLaw) := by
            dsimp [L]
            rw [exp_truncated_moment_identity]
      _ ≤ Real.exp (-d * R ^ 2) * (CX + CY) := by
            apply mul_le_mul
            · apply Real.exp_le_exp.mpr
              have hd' : d ≤ a / 48 := (min_le_right _ _).trans (min_le_left _ _)
              exact neg_scaled_nonneg_le (by norm_num) hd' (sq_nonneg R)
            · exact hmomentSum
            · exact add_nonneg (integral_nonneg
                (fun ω => pow_nonneg (hXnonneg ω) 6))
                (integral_nonneg (fun ω => pow_nonneg (hYnonneg ω) 6))
            · exact Real.exp_nonneg _
      _ = (CX + CY) * Real.exp (-d * R ^ 2) := by ring
  have hgaussianCoeffSmall :
      coeff * Real.exp (-c * (R / 2) ^ 2) ^ 2 * massConst ≤
        coeff * massConst * Real.exp (-d * R ^ 2) := by
    rw [exp_gaussian_square_identity]
    calc
      coeff * Real.exp (-c * R ^ 2 / 2) * massConst =
          (coeff * massConst) * Real.exp (-c * R ^ 2 / 2) := by ring
      _ ≤ (coeff * massConst) * Real.exp (-d * R ^ 2) := by
            apply mul_le_mul_of_nonneg_left
            · apply Real.exp_le_exp.mpr
              have hd' : d ≤ c / 2 := (min_le_right _ _).trans (min_le_right _ _)
              exact neg_scaled_nonneg_le (by norm_num) hd' (sq_nonneg R)
            · exact mul_nonneg hcoeff hmassConst
      _ = coeff * massConst * Real.exp (-d * R ^ 2) := by ring
  have hGbound : ∫ ω, G ω ∂disorderLaw ≤
      finalConst * Real.exp (-d * R ^ 2) := by
    rw [hGintegral]
    calc
      _ ≤ coeff * (L ^ 3 * ∫ ω, T ω ∂disorderLaw +
            L⁻¹ ^ 2 * (∫ ω, X ω ^ 6 ∂disorderLaw +
              ∫ ω, Y ω ^ 6 ∂disorderLaw)) +
          coeff * Real.exp (-c * (R / 2) ^ 2) ^ 2 * massConst := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hmassSq.2 hcoeff
            · exact mul_le_mul_of_nonneg_left hxyMoment
                (mul_nonneg hcoeff (sq_nonneg (Real.exp (-c * (R / 2) ^ 2))))
      _ ≤ coeff * ((decayConst + CX + CY) * Real.exp (-d * R ^ 2)) +
          coeff * massConst * Real.exp (-d * R ^ 2) := by
            apply add_le_add
            · apply mul_le_mul_of_nonneg_left
              · calc
                  _ ≤ decayConst * Real.exp (-d * R ^ 2) +
                      (CX + CY) * Real.exp (-d * R ^ 2) :=
                        add_le_add htailProductSmall hmomentProductSmall
                  _ = (decayConst + CX + CY) * Real.exp (-d * R ^ 2) := by ring
              · exact hcoeff
            · exact hgaussianCoeffSmall
      _ = finalConst * Real.exp (-d * R ^ 2) := by
            dsimp [finalConst]
            ring
  have hfinal : ∫ ω, E ω ^ 2 ∂disorderLaw ≤ ε := by
    calc
      _ ≤ ∫ ω, G ω ∂disorderLaw :=
        integral_mono_ae hE2int hGint (Filter.Eventually.of_forall fun ω => by
          calc
            E ω ^ 2 ≤ coeff * (T ω * Y ω) ^ 2 +
                coeff * (Real.exp (-c * (R / 2) ^ 2) * X ω * Y ω) ^ 2 :=
                  htailErrorBound ω
            _ = G ω := by dsimp [G]; ring)
      _ ≤ finalConst * Real.exp (-d * R ^ 2) := hGbound
      _ ≤ ε := hFbound
  simpa only [hEtarget] using hfinal

end Critical2DKPZ.SHF.Flow

end
