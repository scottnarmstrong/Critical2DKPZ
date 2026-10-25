/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Provider.ShfSymmetries
public import Critical2DKPZ.Extensions.GffTangent.LinearCovariance
import Critical2DKPZ.SHF.Flow.TerminalProfileAnnealing
import Critical2DKPZ.Polymer.Series
import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
import Critical2DKPZ.SHF.Flow.FiniteScaleBlocks
import Critical2DKPZ.JointConvergence.MomentConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Time shifts of linear stochastic-heat-flow pairings

The Bochner integral of a measurable real function is a measurable function of
the integrating measure, including on the nonintegrable locus where the
Bochner integral is definitionally zero.  This permits finite-dimensional SHF
measure laws to be pushed forward by arbitrary Borel tensor pairings.
-/

public noncomputable section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction CompactlySupported

namespace Critical2DKPZ.Extensions.GffTangent

/-- Integrating a measurable real function is measurable as a function of the
measure.  On measures where the function is not integrable, both the Bochner
integral and the displayed measurable representative are zero. -/
theorem measurable_integral_measure_real {X : Type*} [MeasurableSpace X]
    {H : X → ℝ} (hH : Measurable H) :
    Measurable (fun μ : Measure X => ∫ x, H x ∂μ) := by
  have hp : Measurable (fun μ : Measure X => ∫⁻ x, ENNReal.ofReal (H x) ∂μ) :=
    Measure.measurable_lintegral hH.ennreal_ofReal
  have hn : Measurable (fun μ : Measure X => ∫⁻ x, ENNReal.ofReal (-H x) ∂μ) :=
    Measure.measurable_lintegral hH.neg.ennreal_ofReal
  have ha : Measurable (fun μ : Measure X => ∫⁻ x, ENNReal.ofReal |H x| ∂μ) := by
    exact Measure.measurable_lintegral hH.norm.ennreal_ofReal
  let J : Measure X → ℝ := fun μ =>
    if (∫⁻ x, ENNReal.ofReal |H x| ∂μ) < ⊤ then
      (∫⁻ x, ENNReal.ofReal (H x) ∂μ).toReal -
        (∫⁻ x, ENNReal.ofReal (-H x) ∂μ).toReal
    else 0
  have hJ : Measurable J := by
    exact Measurable.ite (measurableSet_lt ha measurable_const)
      (hp.ennreal_toReal.sub hn.ennreal_toReal) measurable_const
  have heq : (fun μ : Measure X => ∫ x, H x ∂μ) = J := by
    funext μ
    by_cases hi : Integrable H μ
    · have hfin : (∫⁻ x, ENNReal.ofReal |H x| ∂μ) < ⊤ := by
        simpa only [Real.enorm_eq_ofReal_abs] using
          (hasFiniteIntegral_iff_enorm.mp hi.hasFiniteIntegral)
      rw [show J μ = (∫⁻ x, ENNReal.ofReal (H x) ∂μ).toReal -
          (∫⁻ x, ENNReal.ofReal (-H x) ∂μ).toReal by simp only [J, ite_eq_left hfin]]
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi
    · have hfin : ¬ (∫⁻ x, ENNReal.ofReal |H x| ∂μ) < ⊤ := by
        intro hlt
        apply hi
        refine ⟨hH.aestronglyMeasurable, ?_⟩
        exact hasFiniteIntegral_iff_enorm.mpr (by
          simpa only [Real.enorm_eq_ofReal_abs] using hlt)
      rw [integral_undef hi]
      simp only [J, ite_eq_right hfin]
  rw [heq]
  exact hJ

/-- The joint law of finitely many Borel SHF pairings is invariant when all
time intervals are translated by the same nonnegative amount. -/
theorem law_shfPairing_timeShift (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {k : ℕ} (s t : Fin k → ℝ) (hst : ∀ i, 0 ≤ s i ∧ s i < t i)
    (u : ℝ) (hu : 0 ≤ u) (f g : Fin k → Plane → ℝ)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
    P.map (fun ω i => shfPairing Z (s i + u) (t i + u) (f i) (g i) ω) =
      P.map (fun ω i => shfPairing Z (s i) (t i) (f i) (g i) ω) := by
  let Zu : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun a b ω => Z (a + u) (b + u) ω
  have hZu : IsCriticalSHF ϑ P Zu := by
    simpa only [Zu] using (Provider.shf_symmetries ϑ P Z hZ).2.2.1 u hu
  have hlaw := SHF.Symmetries.isCriticalSHF_fdd_eq ϑ P P Z Zu hZ hZu k s t hst
  let Φ : (Fin k → Measure (Plane × Plane)) → Fin k → ℝ := fun μ i =>
    ∫ p, f i p.1 * g i p.2 ∂(μ i)
  have hΦ : Measurable Φ := by
    apply Measurable.of_eval
    intro i
    have hfg : Measurable (fun p : Plane × Plane => f i p.1 * g i p.2) :=
      ((hf i).comp measurable_fst).mul ((hg i).comp measurable_snd)
    exact (measurable_integral_measure_real hfg).comp (measurable_pi_apply i)
  have hZvec : Measurable (fun ω i => Z (s i) (t i) ω) := by
    apply Measurable.of_eval
    intro i
    exact hZ.1 (s i) (t i) (hst i).1 (hst i).2
  have hZuvec : Measurable (fun ω i => Zu (s i) (t i) ω) := by
    apply Measurable.of_eval
    intro i
    exact hZu.1 (s i) (t i) (hst i).1 (hst i).2
  have hpush := congrArg
    (fun μ : Measure (Fin k → Measure (Plane × Plane)) => μ.map Φ) hlaw
  rw [Measure.map_map hΦ hZvec, Measure.map_map hΦ hZuvec] at hpush
  simpa only [Function.comp_def, Φ, Zu, shfPairing] using hpush.symm

/-- Annealing all disorder after an arbitrary deterministic time slice turns a
point-to-plane partition function into its value at that slice. -/
theorem integral_pointToPlane_resample_after (β : ℝ) {m n : ℕ} (hmn : m ≤ n)
    (x : Site) (ω : Disorder) :
    (∫ η, pointToPlane β 0 n x
      (Gaussian.resample (Gaussian.timeBlock 0 m) ω η) ∂disorderLaw) =
      pointToPlane β 0 m x ω := by
  classical
  let E : Finset Site := Polymer.endpoints x m
  have hsplit : m + (n - m) = n := Nat.add_sub_of_le hmn
  have hfirst (y : Site) (η : Disorder) :
      pointToPoint β 0 m x y
          (Gaussian.resample (Gaussian.timeBlock 0 m) ω η) =
        pointToPoint β 0 m x y ω := by
    apply Blocks.blockMeasurable_resample_keep
    have h := Polymer.measurable_pointToPoint_block β 0 m x y
    change Measurable[Gaussian.disorderBlock 0 (0 + m)] (pointToPoint β 0 m x y) at h
    rw [Nat.zero_add] at h
    exact h
  have hlater (y : Site) (η : Disorder) :
      pointToPlane β m (n - m) y
          (Gaussian.resample (Gaussian.timeBlock 0 m) ω η) =
        pointToPlane β m (n - m) y η := by
    apply SHF.Flow.blockMeasurable_resample_outside
      (a := m) (b := n) (c := 0) (d := m)
    · exact Set.disjoint_left.mpr fun i hi hj => by
        simp only [Set.mem_Ioc] at hi hj
        omega
    · convert Polymer.measurable_pointToPlane_block β m (n - m) y using 1
      rw [Nat.add_sub_of_le hmn]
  have hfactor (η : Disorder) :
      pointToPlane β 0 n x
          (Gaussian.resample (Gaussian.timeBlock 0 m) ω η) =
        ∑' y, pointToPoint β 0 m x y ω *
          pointToPlane β m (n - m) y η := by
    rw [← hsplit, Polymer.pointToPlane_chapmanKolmogorov]
    simp only [Nat.zero_add, Nat.add_sub_cancel_left]
    apply tsum_congr
    intro y
    rw [hfirst y η, hlater y η]
  have hzero (y : Site) (hy : y ∉ E) :
      pointToPoint β 0 m x y ω = 0 :=
    Polymer.pointToPoint_eq_zero_of_not_mem β 0 m x y ω (by simpa [E] using hy)
  have hsum (η : Disorder) :
      (∑' y, pointToPoint β 0 m x y ω *
        pointToPlane β m (n - m) y η) =
      ∑ y ∈ E, pointToPoint β 0 m x y ω *
        pointToPlane β m (n - m) y η := by
    rw [tsum_eq_sum (s := E)]
    intro y hy
    rw [hzero y hy, zero_mul]
  have hint (y : Site) : Integrable
      (fun η => pointToPoint β 0 m x y ω *
        pointToPlane β m (n - m) y η) disorderLaw :=
    (Polymer.integrable_pointToPlane β m (n - m) y).const_mul _
  calc
    _ = ∫ η, ∑ y ∈ E, pointToPoint β 0 m x y ω *
          pointToPlane β m (n - m) y η ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun η => (hfactor η).trans (hsum η)
    _ = ∑ y ∈ E, pointToPoint β 0 m x y ω := by
      rw [integral_finsetSum E (fun y _ => hint y)]
      apply Finset.sum_congr rfl
      intro y hy
      rw [integral_const_mul, Polymer.integral_pointToPlane, mul_one]
    _ = pointToPlane β 0 m x ω := by
      rw [← Polymer.tsum_pointToPoint]
      symm
      exact tsum_eq_sum (s := E) fun y hy => by rw [hzero y hy]

/-- The arbitrary-split point-to-plane martingale identity as a conditional
expectation with respect to the past disorder block. -/
theorem condExp_pointToPlane_ae_eq (β : ℝ) {m n : ℕ} (hmn : m ≤ n) (x : Site) :
    disorderLaw[pointToPlane β 0 n x | Gaussian.disorderBlock 0 m]
      =ᵐ[disorderLaw] pointToPlane β 0 m x := by
  have h := Gaussian.condExp_disorderBlock_ae_eq 0 m
    (Polymer.measurable_pointToPlane β 0 n x)
    (Polymer.integrable_pointToPlane β 0 n x)
  filter_upwards [h] with ω hω
  rw [hω]
  exact integral_pointToPlane_resample_after β hmn x ω



/-- Conditional expectation commutes with an absolutely summable spatial mixture
of point-to-plane partition functions. -/
theorem condExp_tsum_weightedPointToPlane_ae_eq (β : ℝ) {m n : ℕ}
    (hmn : m ≤ n) (a : Site → ℝ) (ha : Summable a) :
    disorderLaw[(fun ω => ∑' x, a x * pointToPlane β 0 n x ω) |
        Gaussian.disorderBlock 0 m] =ᵐ[disorderLaw]
      fun ω => ∑' x, a x * pointToPlane β 0 m x ω := by
  let fn : Site → Disorder → ℝ := fun x ω => a x * pointToPlane β 0 n x ω
  have hfn (x : Site) : AEStronglyMeasurable (fn x) disorderLaw :=
    ((Polymer.integrable_pointToPlane β 0 n x).const_mul (a x)).aestronglyMeasurable
  have hnorm :
      (∑' x : Site, eLpNorm (fn x) 1 disorderLaw) ≠ ⊤ := by
    simpa only [fn, Nat.sub_zero, mul_one, Polymer.tsum_pointToPoint] using
      Polymer.profile_term_norms_ne_top β 0 n a (fun _ => 1) ha.norm
        1 zero_le_one (fun _ => by norm_num) 1 (by norm_num)
  have hlin :
      (∑' x : Site, ∫⁻ ω, ‖fn x ω‖ₑ ∂disorderLaw) ≠ ⊤ := by
    have heach (x : Site) :
        eLpNorm (fn x) 1 disorderLaw = ∫⁻ ω, ‖fn x ω‖ₑ ∂disorderLaw := by
      rw [eLpNorm_one_eq_lintegral_enorm (hfn x)]
    simpa only [heach] using hnorm
  have hsum := condExp_tsum (μ := disorderLaw)
    (m := Gaussian.disorderBlock 0 m) hfn hlin
  have hterm (x : Site) :
      disorderLaw[fn x | Gaussian.disorderBlock 0 m] =ᵐ[disorderLaw]
        fun ω => a x * pointToPlane β 0 m x ω := by
    have hsmul := condExp_smul (μ := disorderLaw) (c := a x)
      (f := fun ω => pointToPlane β 0 n x ω)
      (Gaussian.disorderBlock 0 m)
    filter_upwards [hsmul, condExp_pointToPlane_ae_eq β hmn x] with ω h₁ h₂
    simpa only [fn, Pi.smul_def, smul_eq_mul] using h₁.trans (congrArg (fun z => a x * z) h₂)
  have hterms : ∀ᵐ ω ∂disorderLaw, ∀ x,
      disorderLaw[fn x | Gaussian.disorderBlock 0 m] ω =
        a x * pointToPlane β 0 m x ω := ae_all_iff.2 hterm
  filter_upwards [hsum, hterms] with ω hω hωterm
  rw [hω]
  apply tsum_congr
  exact hωterm

/-- A summable signed point-to-plane increment is orthogonal to every bounded past
observable. -/
theorem integral_mul_tsum_weightedPointToPlane_increment_eq_zero (β : ℝ)
    {m n : ℕ} (hmn : m ≤ n) (a : Site → ℝ)
    (ha : Summable (fun x => |a x|))
    (G : Disorder → ℝ)
    (hG : AEStronglyMeasurable[Gaussian.disorderBlock 0 m] G disorderLaw)
    (C : ℝ) (hC : ∀ᵐ ω ∂disorderLaw, ‖G ω‖ ≤ C) :
    (∫ ω, G ω *
      ((∑' x, a x * pointToPlane β 0 n x ω) -
       ∑' x, a x * pointToPlane β 0 m x ω) ∂disorderLaw) = 0 := by
  let X : Disorder → ℝ := fun ω => ∑' x, a x * pointToPlane β 0 n x ω
  let Y : Disorder → ℝ := fun ω => ∑' x, a x * pointToPlane β 0 m x ω
  have ha' : Summable a := ha.of_norm
  have hXI : Integrable X disorderLaw := by
    apply memLp_one_iff_integrable.mp
    exact Polymer.memLp_tsum_of_norm 1 le_rfl
      (fun x ω => a x * pointToPlane β 0 n x ω)
      (fun x => (Polymer.memLp_pointToPlane β 0 n x 1 (by simp)).const_mul _)
      (by
        simpa only [Nat.sub_zero, mul_one, Polymer.tsum_pointToPoint] using
          Polymer.profile_term_norms_ne_top β 0 n a (fun _ => 1) ha
            1 zero_le_one (fun _ => by norm_num) 1 (by norm_num))
  have hGI : Integrable (fun ω => G ω * X ω) disorderLaw := by
    have h := hXI.bdd_mul (c := C) (hG.mono (Gaussian.disorderBlock_le 0 m)) hC
    exact h
  have hCE : disorderLaw[X | Gaussian.disorderBlock 0 m] =ᵐ[disorderLaw] Y := by
    simpa only [X, Y] using
      condExp_tsum_weightedPointToPlane_ae_eq β hmn a ha'
  have hpull := condExp_mul_of_aestronglyMeasurable_left hG hGI hXI
  have hprod :
      (fun ω => G ω * disorderLaw[X | Gaussian.disorderBlock 0 m] ω) =ᵐ[disorderLaw]
        fun ω => G ω * Y ω := by
    filter_upwards [hCE] with ω hω
    rw [hω]
  have hGY : Integrable (fun ω => G ω * Y ω) disorderLaw :=
    integrable_condExp.congr (hpull.trans hprod)
  have heq : (∫ ω, G ω * X ω ∂disorderLaw) =
      ∫ ω, G ω * Y ω ∂disorderLaw := by
    calc
      _ = ∫ ω, disorderLaw[(fun η => G η * X η) |
          Gaussian.disorderBlock 0 m] ω ∂disorderLaw :=
        (integral_condExp (μ := disorderLaw)
          (m := Gaussian.disorderBlock 0 m)
          (f := fun η => G η * X η) (Gaussian.disorderBlock_le 0 m)).symm
      _ = _ := integral_congr_ae (hpull.trans hprod)
  calc
    _ = ∫ ω, G ω * X ω - G ω * Y ω ∂disorderLaw := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact mul_sub _ _ _
    _ = (∫ ω, G ω * X ω ∂disorderLaw) -
        ∫ ω, G ω * Y ω ∂disorderLaw := integral_sub hGI hGY
    _ = 0 := by rw [heq, sub_self]


/-- Symmetric clipping of the identity. -/
@[expose] noncomputable def clippedIdentity (R : ℝ) (hR : 0 ≤ R) : (Fin 1 → ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun z => max (-R) (min R (z 0)), by fun_prop⟩ (2 * R) (by
      intro z w
      rw [Real.dist_eq]
      have hb (q : Fin 1 → ℝ) : |max (-R) (min R (q 0))| ≤ R := by
        apply abs_le.mpr
        exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
      calc
        |max (-R) (min R (z 0)) - max (-R) (min R (w 0))|
            ≤ |max (-R) (min R (z 0))| + |max (-R) (min R (w 0))| := abs_sub _ _
        _ ≤ R + R := add_le_add (hb z) (hb w)
        _ = 2 * R := by ring)


/-- Compact flat pairings inherit the uniform square bound of a positive
heat-start pairing. -/
theorem polymer_compact_flat_pairing_sq_integral_bounded
    (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (f : C_c(Plane, ℝ)) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω =>
        (∫ x : Plane, f x * rescaledP2Plane ϑ N s t x ω) ^ 2)
        disorderLaw ∧
      (∫ ω, (∫ x : Plane,
        f x * rescaledP2Plane ϑ N s t x ω) ^ 2 ∂disorderLaw) ≤ C := by
  let q : Plane → ℝ := fun x => f x / heatKernel 1 x
  have hqcont : Continuous q := by
    exact f.continuous.div (continuous_heatKernel 1)
      (fun x => (heatKernel_pos zero_lt_one x).ne')
  have hqsupp : HasCompactSupport q := by
    simpa only [q, div_eq_mul_inv, Pi.mul_def] using
      (f.hasCompactSupport.mul_right (f' := fun x => (heatKernel 1 x)⁻¹))
  obtain ⟨A, hA⟩ := hqsupp.exists_bound_of_continuous hqcont
  have hAnonneg : 0 ≤ A := by
    exact le_trans (norm_nonneg (q 0)) (hA 0)
  have hfdom (x : Plane) : |f x| ≤ A * heatKernel 1 x := by
    have hq := hA x
    rw [Real.norm_eq_abs] at hq
    have hk := heatKernel_pos zero_lt_one x
    have heq : f x = q x * heatKernel 1 x := by
      dsimp only [q]
      field_simp [hk.ne']
    rw [heq, abs_mul, abs_of_pos hk]
    exact mul_le_mul_of_nonneg_right hq hk.le

  obtain ⟨K, hK⟩ := SHF.Positivity.polymer_heat_pairing_sq_integral_bounded
    ϑ hs hst zero_lt_one (0 : Plane)
  refine ⟨A ^ 2 * max K 0, ?_⟩
  filter_upwards [hK, eventually_ge_atTop 1] with N hheat hN
  let X : Disorder → ℝ := fun ω => ∫ x : Plane,
    f x * rescaledP2Plane ϑ N s t x ω
  let Y : Disorder → ℝ := fun ω => ∫ p,
    heatKernel 1 (p.1 - 0) ∂(SHF.Limit.polymerMeasure ϑ N s t ω)
  let Q : Disorder → ℝ := fun ω => ∫ x : Plane,
    heatKernel 1 x * rescaledP2Plane ϑ N s t x ω

  have hfint : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hprodF := SHF.Limit.integrable_flatPairingProduct ϑ N s t hfint
  have hprodQ := SHF.Limit.integrable_flatPairingProduct ϑ N s t
    (integrable_heatKernel zero_lt_one)
  have hslicesF : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun x : Plane =>
        f x * rescaledP2Plane ϑ N s t x ω) :=
    hprodF.swap.prod_right_ae
  have hslicesQ : ∀ᵐ ω ∂disorderLaw,
      Integrable (fun x : Plane =>
        heatKernel 1 x * rescaledP2Plane ϑ N s t x ω) :=
    hprodQ.swap.prod_right_ae
  have hYQ : Y =ᵐ[disorderLaw] Q := by
    filter_upwards [] with ω
    dsimp only [Y, Q]
    calc
      _ = ∫ y, heatKernel 1 (y - 0)
          ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) :=
        (integral_map measurable_fst.aemeasurable
          (((continuous_heatKernel 1).comp
            (continuous_id.sub continuous_const)).aestronglyMeasurable)).symm
      _ = _ := by
        rw [SHF.Limit.integral_map_fst_polymerMeasure ϑ hN s t ω]
        simp only [sub_zero]

  have hXY : ∀ᵐ ω ∂disorderLaw, |X ω| ≤ A * Y ω := by
    filter_upwards [hslicesF, hslicesQ, hYQ] with ω hFi hQi hYQi
    have hpoint : ∀ x : Plane,
        |f x * rescaledP2Plane ϑ N s t x ω| ≤
          A * (heatKernel 1 x * rescaledP2Plane ϑ N s t x ω) := by
      intro x
      rw [abs_mul, abs_of_nonneg
        (SHF.Limit.rescaledP2Plane_nonneg ϑ N s t x ω)]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hfdom x)
        (SHF.Limit.rescaledP2Plane_nonneg ϑ N s t x ω)
    have habs : |X ω| ≤ ∫ x : Plane,
        |f x * rescaledP2Plane ϑ N s t x ω| := by
      exact abs_integral_le_integral_abs
    calc
      |X ω| ≤ ∫ x : Plane,
          |f x * rescaledP2Plane ϑ N s t x ω| := habs
      _ ≤ ∫ x : Plane,
          A * (heatKernel 1 x * rescaledP2Plane ϑ N s t x ω) :=
        integral_mono hFi.norm (hQi.const_mul A) hpoint
      _ = A * Q ω := integral_const_mul _ _
      _ = A * Y ω := by rw [hYQi]

  have hsq : ∀ᵐ ω ∂disorderLaw, X ω ^ 2 ≤ A ^ 2 * Y ω ^ 2 := by
    filter_upwards [hXY] with ω hω
    have hYnonneg : 0 ≤ Y ω := by
      dsimp only [Y]
      exact integral_nonneg fun _ => heatKernel_nonneg zero_le_one _
    have hXabs : |X ω| ≤ |A * Y ω| := by
      rwa [abs_of_nonneg (mul_nonneg hAnonneg hYnonneg)]
    have hh := (sq_le_sq₀ (abs_nonneg (X ω)) (abs_nonneg (A * Y ω))).mpr hXabs
    simpa only [sq_abs, mul_pow] using hh
  have hXmeas : AEStronglyMeasurable X disorderLaw := by
    simpa only [X] using
      (SHF.Limit.aemeasurable_rescaledP2Plane_pairing ϑ N s t f).aestronglyMeasurable
  have hXsq : Integrable (fun ω => X ω ^ 2) disorderLaw := by
    apply (hheat.1.const_mul (A ^ 2)).mono' (hXmeas.pow 2)
    filter_upwards [hsq] with ω hω
    change ‖X ω ^ 2‖ ≤ A ^ 2 * Y ω ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hω
  constructor
  · simpa only [X] using hXsq
  · change (∫ ω, X ω ^ 2 ∂disorderLaw) ≤ _
    calc
      (∫ ω, X ω ^ 2 ∂disorderLaw) ≤
          ∫ ω, A ^ 2 * Y ω ^ 2 ∂disorderLaw :=
        integral_mono_ae hXsq (hheat.1.const_mul (A ^ 2)) hsq
      _ = A ^ 2 * ∫ ω, Y ω ^ 2 ∂disorderLaw := integral_const_mul _ _
      _ ≤ A ^ 2 * max K 0 :=
        mul_le_mul_of_nonneg_left (hheat.2.trans (le_max_left _ _)) (sq_nonneg A)

theorem integral_latticeStep_mul_eq_tsum_cell
    (N : ℕ) (f : Plane → ℝ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (G : Site → ℝ) :
    (∫ x : Plane, f x * G (latticePoint N x)) =
      ∑' z : Site, (∫ x in cell N z, f x) * G z := by
  classical
  let K : Set Plane := tsupport f
  have hK : IsCompact K := hfs
  let S : Set Site := latticePoint N '' K
  have hS : S.Finite := SHF.Limit.finite_latticePoint_image_of_bounded hK.isBounded
  let V : Set ℝ := (fun z : Site => |G z|) '' S
  have hV : V.Finite := hS.image _
  obtain ⟨B, hB⟩ := hV.bddAbove
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  have hprodMeas : Measurable (fun x : Plane => f x * G (latticePoint N x)) :=
    hf.measurable.mul ((measurable_of_countable G).comp (measurable_latticePoint N))
  have hbound (x : Plane) :
      ‖f x * G (latticePoint N x)‖ ≤ C * ‖f x‖ := by
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hxK : x ∈ K := subset_closure (Function.mem_support.mpr hfx)
      have hzS : latticePoint N x ∈ S := ⟨x, hxK, rfl⟩
      have hvalue : |G (latticePoint N x)| ≤ B := hB ⟨latticePoint N x, hzS, rfl⟩
      calc
        ‖f x * G (latticePoint N x)‖ = ‖f x‖ * |G (latticePoint N x)| := by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
        _ ≤ ‖f x‖ * C := mul_le_mul_of_nonneg_left (hvalue.trans (le_max_left _ _)) (norm_nonneg _)
        _ = C * ‖f x‖ := by ring
  have hprod : Integrable (fun x : Plane => f x * G (latticePoint N x)) := by
    apply ((hf.integrable_of_hasCompactSupport hfs).norm.const_mul C).mono'
      hprodMeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall hbound
  have hcover : (⋃ z : Site, cell N z) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨latticePoint N x, mem_cell_latticePoint N x⟩
  have hi := integral_iUnion (measurableSet_cell N) (pairwise_disjoint_cell N)
    hprod.integrableOn
  rw [hcover, setIntegral_univ] at hi
  rw [hi]
  apply tsum_congr
  intro z
  rw [setIntegral_congr_fun (measurableSet_cell N z) (fun x hx => ?_), integral_mul_const]
  rw [mem_cell_iff] at hx
  rw [hx]


/-- The compact flat coordinates in the defining SHF joint convergence law. -/
theorem isCriticalSHF_compact_fst_pairings_tendsto
    {ϑ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {k : ℕ} (s t : Fin k → ℝ) (ht : ∀ i, 0 ≤ s i ∧ s i < t i)
    (ψ : Fin k → C_c(Plane, ℝ)) :
    TendstoInDistribution
      (fun N ω i => ∫ x, ψ i x * rescaledP2Plane ϑ N (s i) (t i) x ω)
      atTop (fun ω i => shfPairing Z (s i) (t i) (ψ i) (fun _ => 1) ω)
      (fun _ => disorderLaw) P := by
  have h := hZ.2.2 k s t ht (fun _ => 0) ψ
  have hp := h.continuous_comp
    (g := fun v : Fin k → ℝ × ℝ => fun i => (v i).2) (by fun_prop)
  have hmap (ω : Ω) (i : Fin k) :
      (∫ x, ψ i x ∂((Z (s i) (t i) ω).map Prod.fst)) =
        shfPairing Z (s i) (t i) (ψ i) (fun _ => 1) ω := by
    simp only [shfPairing, mul_one]
    exact integral_map measurable_fst.aemeasurable (ψ i).continuous.aestronglyMeasurable
  simpa only [Function.comp_def, hmap] using hp

/-- Exact cell decomposition of a compact flat lattice pairing. -/
theorem integral_compact_rescaledP2Plane_eq_tsum
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (f : C_c(Plane, ℝ)) (ω : Disorder) :
    (∫ x, f x * rescaledP2Plane ϑ N s t x ω) =
      ∑' w : Site, (∫ x in cell N w, f x) *
        pointToPlane (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) w ω := by
  exact integral_latticeStep_mul_eq_tsum_cell N f f.continuous f.hasCompactSupport
    (fun w => pointToPlane (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) w ω)

/-- The cell masses of a compact entrance test are absolutely summable. -/
theorem summable_abs_integral_cell_compact (N : ℕ) (f : C_c(Plane, ℝ)) :
    Summable (fun w : Site => |∫ x in cell N w, f x|) := by
  classical
  have hS : (latticePoint N '' tsupport f).Finite :=
    SHF.Limit.finite_latticePoint_image_of_bounded f.hasCompactSupport.isBounded
  have hz (w : Site) (hw : w ∉ latticePoint N '' tsupport f) :
      (∫ x in cell N w, f x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem (measurableSet_cell N w)] with x hx
    by_contra hfx
    exact hw ⟨x, subset_closure (Function.mem_support.mpr hfx), (mem_cell_iff N w x).mp hx⟩
  apply summable_of_hasFiniteSupport
  apply hS.subset
  intro w hw
  by_contra hn
  exact hw (by
    change |∫ x in cell N w, f x| = 0
    rw [hz w hn, abs_zero])


/-- Compact entrance masses satisfy the weak martingale identity against
bounded continuous functions of finitely many past compact flat masses. -/
theorem integral_boundedContinuous_mul_compactMass_increment_eq_zero
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t T : ℝ} (ht : 0 < t) (htT : t < T)
    {k : ℕ} (s₀ u₀ : Fin k → ℝ) (ψ : Fin k → C_c(Plane, ℝ))
    (htimes : ∀ i, 0 ≤ s₀ i ∧ s₀ i < u₀ i ∧ u₀ i ≤ t)
    (f : C_c(Plane, ℝ)) (Φ : (Fin k → ℝ) →ᵇ ℝ) :
    (∫ ω, Φ (fun i => shfPairing Z (s₀ i) (u₀ i) (ψ i) (fun _ => 1) ω) *
      (shfPairing Z 0 T f (fun _ => 1) ω -
       shfPairing Z 0 t f (fun _ => 1) ω) ∂P) = 0 := by
  classical
  let ss : Fin (k + 2) → ℝ := Fin.append s₀ ![0, 0]
  let tt : Fin (k + 2) → ℝ := Fin.append u₀ ![t, T]
  let ff : Fin (k + 2) → C_c(Plane, ℝ) := Fin.append ψ ![f, f]
  have hall : ∀ i, 0 ≤ ss i ∧ ss i < tt i := by
    intro i
    refine Fin.addCases (m := k) (n := 2) (fun j => ?_) (fun j => ?_) i
    · simpa only [ss, tt, Fin.append_left] using ⟨(htimes j).1, (htimes j).2.1⟩
    · fin_cases j
      · simpa [ss, tt] using (show 0 ≤ (0 : ℝ) ∧ 0 < t from ⟨le_rfl, ht⟩)
      · simpa [ss, tt] using (show 0 ≤ (0 : ℝ) ∧ 0 < T from ⟨le_rfl, ht.trans htT⟩)
  let X : ℕ → Disorder → Fin (k + 2) → ℝ := fun N ω i =>
    ∫ x, ff i x * rescaledP2Plane ϑ N (ss i) (tt i) x ω
  let Y : Ω → Fin (k + 2) → ℝ := fun ω i =>
    shfPairing Z (ss i) (tt i) (ff i) (fun _ => 1) ω
  have hjoint : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P := by
    exact isCriticalSHF_compact_fst_pairings_tendsto P Z hZ ss tt hall ff
  let F : (Fin (k + 2) → ℝ) → ℝ := fun z =>
    Φ (fun i => z (Fin.castAdd 2 i)) *
      (z (Fin.natAdd k 1) - z (Fin.natAdd k 0))
  have hF : Continuous F := by
    exact (Φ.continuous.comp (continuous_pi fun i => continuous_apply (Fin.castAdd 2 i))).mul
      ((continuous_apply (Fin.natAdd k 1)).sub
        (continuous_apply (Fin.natAdd k 0)))
  have hdist : TendstoInDistribution (fun N ω => F (X N ω)) atTop
      (fun ω => F (Y ω)) (fun _ => disorderLaw) P := hjoint.continuous_comp hF

  let Mt : ℕ → Disorder → ℝ := fun N ω => X N ω (Fin.natAdd k 0)
  let MT : ℕ → Disorder → ℝ := fun N ω => X N ω (Fin.natAdd k 1)
  obtain ⟨Ct, hCt⟩ := polymer_compact_flat_pairing_sq_integral_bounded
    ϑ (s := 0) (t := t) (by norm_num) ht f
  obtain ⟨CT, hCT⟩ := polymer_compact_flat_pairing_sq_integral_bounded
    ϑ (s := 0) (t := T) (by norm_num) (ht.trans htT) f
  have hMt (N : ℕ) (ω : Disorder) : Mt N ω =
      ∫ x, f x * rescaledP2Plane ϑ N 0 t x ω := by
    simp only [Mt, X, ss, tt, ff, Fin.append_right, Matrix.cons_val_zero]
  have hMT (N : ℕ) (ω : Disorder) : MT N ω =
      ∫ x, f x * rescaledP2Plane ϑ N 0 T x ω := by
    simp only [MT, X, ss, tt, ff, Fin.append_right,
      Matrix.cons_val_one, Matrix.cons_val_zero]
  have hCt' : ∀ᶠ N in atTop, Integrable (fun ω => Mt N ω ^ 2) disorderLaw ∧
      (∫ ω, Mt N ω ^ 2 ∂disorderLaw) ≤ Ct := by
    simpa only [hMt] using hCt
  have hCT' : ∀ᶠ N in atTop, Integrable (fun ω => MT N ω ^ 2) disorderLaw ∧
      (∫ ω, MT N ω ^ 2 ∂disorderLaw) ≤ CT := by
    simpa only [hMT] using hCT
  let C : ℝ := ‖Φ‖ ^ 2 * (2 * (max CT 0 + max Ct 0))
  have hpow (N : ℕ) (ω : Disorder) :
      |F (X N ω)| ^ (2 : ℝ) = (F (X N ω)) ^ 2 := by
    rw [Real.rpow_two, sq_abs]
  have hbound_point (N : ℕ) (ω : Disorder) :
      (F (X N ω)) ^ 2 ≤ ‖Φ‖ ^ 2 *
        (2 * (MT N ω ^ 2 + Mt N ω ^ 2)) := by
    have hΦ : |Φ (fun i => X N ω (Fin.castAdd 2 i))| ≤ ‖Φ‖ := by
      simpa only [Real.norm_eq_abs] using Φ.norm_coe_le_norm (fun i => X N ω (Fin.castAdd 2 i))
    have hsub : (MT N ω - Mt N ω) ^ 2 ≤
        2 * (MT N ω ^ 2 + Mt N ω ^ 2) := by nlinarith [sq_nonneg (MT N ω + Mt N ω)]
    dsimp only [F, MT, Mt]
    rw [mul_pow]
    exact mul_le_mul (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hΦ)
      hsub (sq_nonneg _) (sq_nonneg _)
  have hmoment : ∀ᶠ N in atTop,
      ∫ ω, |F (X N ω)| ^ (2 : ℝ) ∂disorderLaw ≤ C := by
    filter_upwards [hCt', hCT'] with N hNt hNT
    rw [integral_congr_ae (Filter.Eventually.of_forall (hpow N))]
    calc
      _ ≤ ∫ ω, ‖Φ‖ ^ 2 * (2 * (MT N ω ^ 2 + Mt N ω ^ 2))
          ∂disorderLaw := integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)
            ((hNT.1.add hNt.1).const_mul 2 |>.const_mul (‖Φ‖ ^ 2))
            (Filter.Eventually.of_forall (hbound_point N))
      _ = ‖Φ‖ ^ 2 * (2 *
          ((∫ ω, MT N ω ^ 2 ∂disorderLaw) +
           ∫ ω, Mt N ω ^ 2 ∂disorderLaw)) := by
            rw [integral_const_mul, integral_const_mul, integral_add hNT.1 hNt.1]
      _ ≤ C := by
        dsimp only [C]
        gcongr
        · exact hNT.2.trans (le_max_left _ _)
        · exact hNt.2.trans (le_max_left _ _)
  have hint : ∀ᶠ N in atTop,
      Integrable (fun ω => |F (X N ω)| ^ (2 : ℝ)) disorderLaw := by
    filter_upwards [hCt', hCT'] with N hNt hNT
    rw [show (fun ω => |F (X N ω)| ^ (2 : ℝ)) =
        fun ω => F (X N ω) ^ 2 by funext ω; exact hpow N ω]
    apply Integrable.mono' ((hNT.1.add hNt.1).const_mul 2 |>.const_mul (‖Φ‖ ^ 2))
      ((hdist.forall_aemeasurable N).aestronglyMeasurable.pow 2)
    filter_upwards [] with ω
    change ‖F (X N ω) ^ 2‖ ≤ ‖Φ‖ ^ 2 * (2 * (MT N ω ^ 2 + Mt N ω ^ 2))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound_point N ω
  have hmean := JointConvergence.tendsto_integral_of_tendstoInDistribution
    hdist (by norm_num : (1 : ℝ) < 2) hmoment hint

  have hlattice : ∀ᶠ N in atTop, (∫ ω, F (X N ω) ∂disorderLaw) = 0 := by
    filter_upwards [] with N
    let m := evenCeil ((N : ℝ) * t)
    let n := evenCeil ((N : ℝ) * T)
    have hmn : m ≤ n := evenCeil_mono
      (mul_le_mul_of_nonneg_left htT.le (Nat.cast_nonneg N))
    let a : Site → ℝ := fun w => ∫ x in cell N w, f x
    have ha : Summable (fun w => |a w|) := summable_abs_integral_cell_compact N f
    let G : Disorder → ℝ := fun ω => Φ (fun i => X N ω (Fin.castAdd 2 i))
    have hGb : ∀ ω, ‖G ω‖ ≤ ‖Φ‖ := fun ω => Φ.norm_coe_le_norm _
    have hGm : AEStronglyMeasurable[Gaussian.disorderBlock 0 m] G disorderLaw := by
      have hvec : Measurable[Gaussian.disorderBlock 0 m]
          (fun ω : Disorder => fun i : Fin k => X N ω (Fin.castAdd 2 i)) := by
        let : MeasurableSpace Disorder := Gaussian.disorderBlock 0 m
        apply Measurable.of_eval
        intro i
        let ai := evenCeil ((N : ℝ) * s₀ i)
        let bi := evenCeil ((N : ℝ) * u₀ i)
        let ν : Site → ℝ := fun w => ∫ x in cell N w, ψ i x
        have hab : ai ≤ bi := evenCeil_mono
          (mul_le_mul_of_nonneg_left (htimes i).2.1.le (Nat.cast_nonneg N))
        have hbm : bi ≤ m := evenCeil_mono
          (mul_le_mul_of_nonneg_left (htimes i).2.2 (Nat.cast_nonneg N))
        have hmP := Polymer.measurable_profileP2Fun_block (criticalBeta ϑ N) ai bi hab ν (fun _ => 1)
        have hblock : Gaussian.disorderBlock ai bi ≤ Gaussian.disorderBlock 0 m :=
          Gaussian.disorderBlock_mono (Nat.zero_le ai) hbm
        have hmP' := hmP.mono hblock le_rfl
        have heq : (fun ω => X N ω (Fin.castAdd 2 i)) =
            profileP2Fun (criticalBeta ϑ N) ai bi ν (fun _ => 1) := by
          funext ω
          simp only [X, ss, tt, ff, Fin.append_left]
          rw [integral_compact_rescaledP2Plane_eq_tsum]
          simp only [profileP2Fun, mul_one, Polymer.tsum_pointToPoint, ai, bi, ν]
        rw [heq]
        exact hmP'
      exact (Φ.continuous.measurable.comp hvec).aestronglyMeasurable
    have hzero := integral_mul_tsum_weightedPointToPlane_increment_eq_zero
      (criticalBeta ϑ N) hmn a ha G hGm ‖Φ‖ (Filter.Eventually.of_forall hGb)
    have hrepT (ω : Disorder) : MT N ω =
        ∑' w, a w * pointToPlane (criticalBeta ϑ N) 0 n w ω := by
      rw [hMT, integral_compact_rescaledP2Plane_eq_tsum]
      simp only [mul_zero, evenCeil_zero, Nat.sub_zero, a, n]
    have hrept (ω : Disorder) : Mt N ω =
        ∑' w, a w * pointToPlane (criticalBeta ϑ N) 0 m w ω := by
      rw [hMt, integral_compact_rescaledP2Plane_eq_tsum]
      simp only [mul_zero, evenCeil_zero, Nat.sub_zero, a, m]
    calc
      _ = ∫ ω, G ω * ((∑' w, a w * pointToPlane (criticalBeta ϑ N) 0 n w ω) -
          ∑' w, a w * pointToPlane (criticalBeta ϑ N) 0 m w ω) ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        change G ω * (MT N ω - Mt N ω) = _
        rw [hrepT, hrept]
      _ = 0 := hzero
  have hzeroT : Tendsto (fun N => ∫ ω, F (X N ω) ∂disorderLaw)
      atTop (𝓝 0) := tendsto_const_nhds.congr' (hlattice.mono fun _ h => h.symm)
  have hlim : (∫ ω, F (Y ω) ∂P) = 0 := tendsto_nhds_unique hmean hzeroT
  simpa only [F, Y, ss, tt, ff, Fin.append_left, Fin.append_right,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hlim


/-- Compact flat entrance masses have the martingale cross moment. -/
theorem integral_compactMass_mul_eq_integral_sq
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t T : ℝ} (ht : 0 < t) (htT : t < T) (f : C_c(Plane, ℝ)) :
    (∫ ω, shfPairing Z 0 T f (fun _ => 1) ω *
      shfPairing Z 0 t f (fun _ => 1) ω ∂P) =
    ∫ ω, shfPairing Z 0 t f (fun _ => 1) ω ^ 2 ∂P := by
  let Xt : Ω → ℝ := shfPairing Z 0 t f (fun _ => 1)
  let XT : Ω → ℝ := shfPairing Z 0 T f (fun _ => 1)
  have hf : Measurable (f : Plane → ℝ) := f.continuous.measurable
  have hf1 : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨Cf, hCf⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hfbd : ∀ y, |f y| ≤ Cf := by simpa only [Real.norm_eq_abs] using hCf
  have hXt2 : MemLp Xt 2 P := by
    exact memLp_two_shfPairing_one (-ϑ) P Z (by simpa only [neg_neg] using hZ)
      (a := 0) (T := t) (by norm_num) ht hf hf1 hfbd
  have hXT2 : MemLp XT 2 P := by
    exact memLp_two_shfPairing_one (-ϑ) P Z (by simpa only [neg_neg] using hZ)
      (a := 0) (T := T) (by norm_num) (ht.trans htT) hf hf1 hfbd
  have hdiff2 : MemLp (fun ω => XT ω - Xt ω) 2 P := hXT2.sub hXt2
  have hdomI : Integrable (fun ω => |Xt ω * (XT ω - Xt ω)|) P := by
    exact (MemLp.integrable_mul (p := 2) (q := 2) hXt2 hdiff2).abs
  have hclip (R : ℕ) :
      (∫ ω, (clippedIdentity R (Nat.cast_nonneg R)) (fun _ => Xt ω) *
        (XT ω - Xt ω) ∂P) = 0 := by
    have h := integral_boundedContinuous_mul_compactMass_increment_eq_zero
      ϑ P Z hZ ht htT
      (k := 1) (fun _ => 0) (fun _ => t) (fun _ => f)
      (fun _ => ⟨by norm_num, ht, le_rfl⟩) f
      (clippedIdentity R (Nat.cast_nonneg R))
    exact h
  have hlim : Tendsto (fun R : ℕ =>
      ∫ ω, (clippedIdentity R (Nat.cast_nonneg R)) (fun _ => Xt ω) *
        (XT ω - Xt ω) ∂P) atTop
      (𝓝 (∫ ω, Xt ω * (XT ω - Xt ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun ω => |Xt ω * (XT ω - Xt ω)|)
    · intro R
      have hvec : AEMeasurable (fun ω => fun _ : Fin 1 => Xt ω) P :=
        aemeasurable_pi_iff.mpr fun _ => hXt2.aestronglyMeasurable.aemeasurable
      have hclipm : AEStronglyMeasurable
          (fun ω => (clippedIdentity R (Nat.cast_nonneg R)) (fun _ => Xt ω)) P :=
        ((clippedIdentity R (Nat.cast_nonneg R)).continuous.measurable.comp_aemeasurable
          hvec).aestronglyMeasurable
      exact hclipm.mul (hXT2.aestronglyMeasurable.sub hXt2.aestronglyMeasurable)
    · exact hdomI
    · intro R
      filter_upwards [] with ω
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have hclipabs :
          |max (-(R : ℝ)) (min (R : ℝ) (Xt ω))| ≤ |Xt ω| := by
        by_cases hleft : Xt ω ≤ -(R : ℝ)
        · have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
          have hmin : min (R : ℝ) (Xt ω) = Xt ω :=
            min_eq_right (hleft.trans (by linarith))
          have hmax : max (-(R : ℝ)) (Xt ω) = -(R : ℝ) := max_eq_left hleft
          rw [hmin, hmax, abs_neg, abs_of_nonneg hR0,
            abs_of_nonpos (hleft.trans (by linarith))]
          linarith
        · by_cases hright : (R : ℝ) ≤ Xt ω
          · have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
            have hmin : min (R : ℝ) (Xt ω) = R := min_eq_left hright
            have hmax : max (-(R : ℝ)) R = R := max_eq_right (by linarith)
            rw [hmin, hmax, abs_of_nonneg hR0,
              abs_of_nonneg (hR0.trans hright)]
            exact hright
          · have hmin : min (R : ℝ) (Xt ω) = Xt ω :=
              min_eq_right (le_of_not_ge hright)
            have hmax : max (-(R : ℝ)) (Xt ω) = Xt ω :=
              max_eq_right (le_of_not_ge hleft)
            rw [hmin, hmax]
      simpa only [clippedIdentity, BoundedContinuousFunction.mkOfBound_coe,
        ContinuousMap.coe_mk, Fin.isValue] using hclipabs
    · filter_upwards [] with ω
      have heq : ∀ᶠ R : ℕ in atTop,
          (clippedIdentity R (Nat.cast_nonneg R)) (fun _ => Xt ω) = Xt ω := by
        obtain ⟨R, hR⟩ := exists_nat_gt |Xt ω|
        filter_upwards [eventually_ge_atTop R] with n hn
        have habs : |Xt ω| ≤ (n : ℝ) := by
          exact le_trans hR.le (by exact_mod_cast hn)
        simp only [clippedIdentity, BoundedContinuousFunction.mkOfBound_coe, ContinuousMap.coe_mk, Fin.isValue]
        rw [min_eq_right (le_of_abs_le habs), max_eq_right (neg_le_of_abs_le habs)]
      exact tendsto_const_nhds.congr' (heq.mono fun R hR => by
        change Xt ω * (XT ω - Xt ω) =
          (clippedIdentity R (Nat.cast_nonneg R)) (fun _ => Xt ω) * (XT ω - Xt ω)
        rw [hR])
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hz : (∫ ω, Xt ω * (XT ω - Xt ω) ∂P) = 0 :=
    tendsto_nhds_unique hlim (hzero.congr' (Filter.Eventually.of_forall fun R => (hclip R).symm))
  have hprodI : Integrable (fun ω => Xt ω * XT ω) P :=
    MemLp.integrable_mul (p := 2) (q := 2) hXt2 hXT2
  have hsqI : Integrable (fun ω => Xt ω ^ 2) P := hXt2.integrable_sq
  have hexpand : (∫ ω, Xt ω * (XT ω - Xt ω) ∂P) =
      (∫ ω, Xt ω * XT ω ∂P) - ∫ ω, Xt ω ^ 2 ∂P := by
    rw [show (fun ω => Xt ω * (XT ω - Xt ω)) =
      fun ω => Xt ω * XT ω - Xt ω ^ 2 by funext ω; ring,
      integral_sub hprodI hsqI]
  rw [hexpand] at hz
  have := sub_eq_zero.mp hz
  simpa only [Xt, XT, mul_comm] using this


/-- The square of a compact flat-mass increment is the variance difference. -/
theorem variance_increment
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {t T : ℝ} (ht : 0 < t) (htT : t < T) (f : C_c(Plane, ℝ)) :
    (∫ ω, (shfPairing Z 0 T f (fun _ => 1) ω -
      shfPairing Z 0 t f (fun _ => 1) ω) ^ 2 ∂P) =
      ProbabilityTheory.variance (shfPairing Z 0 T f (fun _ => 1)) P -
      ProbabilityTheory.variance (shfPairing Z 0 t f (fun _ => 1)) P := by
  let XT := shfPairing Z 0 T f (fun _ => 1)
  let Xt := shfPairing Z 0 t f (fun _ => 1)
  have hf : Measurable (f : Plane → ℝ) := f.continuous.measurable
  have hf1 : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hfbd : ∀ y, |f y| ≤ C := by simpa only [Real.norm_eq_abs] using hC
  have hXT : MemLp XT 2 P := memLp_two_shfPairing_one (-ϑ) P Z
    (by simpa only [neg_neg] using hZ) (by norm_num) (ht.trans htT) hf hf1 hfbd
  have hXt : MemLp Xt 2 P := memLp_two_shfPairing_one (-ϑ) P Z
    (by simpa only [neg_neg] using hZ) (by norm_num) ht hf hf1 hfbd
  have hXTmean : (∫ ω, XT ω ∂P) = ∫ x, f x :=
    integral_shfPairing_one ϑ P Z hZ (by norm_num) (ht.trans htT) hf hf1
  have hXtmean : (∫ ω, Xt ω ∂P) = ∫ x, f x :=
    integral_shfPairing_one ϑ P Z hZ (by norm_num) ht hf hf1
  have hcross : (∫ ω, XT ω * Xt ω ∂P) = ∫ ω, Xt ω ^ 2 ∂P :=
    integral_compactMass_mul_eq_integral_sq ϑ P Z hZ ht htT f
  have hpoly : (fun ω => (XT ω - Xt ω) ^ 2) =
      (fun ω => XT ω ^ 2 - XT ω * Xt ω - XT ω * Xt ω + Xt ω ^ 2) := by
    funext ω
    ring
  change (∫ ω, (XT ω - Xt ω) ^ 2 ∂P) =
    ProbabilityTheory.variance XT P - ProbabilityTheory.variance Xt P
  rw [ProbabilityTheory.variance_eq_sub hXT, ProbabilityTheory.variance_eq_sub hXt]
  simp only [Pi.pow_apply]
  have hA : Integrable (fun ω => XT ω ^ 2) P := hXT.integrable_sq
  have hB : Integrable (fun ω => XT ω * Xt ω) P := hXT.integrable_mul hXt
  have hD : Integrable (fun ω => Xt ω ^ 2) P := hXt.integrable_sq
  rw [hXTmean, hXtmean, hpoly, integral_sub_sub_add hA hB hB hD, hcross]
  ring

end Critical2DKPZ.Extensions.GffTangent

end
