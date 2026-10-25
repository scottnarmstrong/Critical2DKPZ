/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.CramerWold
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic

/-!
# Sequential criteria for convergence in distribution

The sequential characterization requires measurability assumptions, even for
the bottom filter: the sequential condition is then vacuous, whereas
`TendstoInDistribution` still requires measurability. A two-point example
shows why these assumptions are necessary.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology Matrix

namespace Critical2DKPZ.Extensions.GffTangent

/-- Sequential characterization with the random-variable measurability
premises explicit, including for the bottom filter. -/
theorem tendstoInDistribution_iff_forall_seq {ι Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ι → Ω → E} {Z : Ω' → E} {F : Filter ι} [F.IsCountablyGenerated]
    (hX : ∀ i, AEMeasurable (X i) P) (hZ : AEMeasurable Z P') :
    TendstoInDistribution X F Z (fun _ => P) P' ↔
      ∀ u : ℕ → ι, Tendsto u atTop F →
        TendstoInDistribution (fun n => X (u n)) atTop Z (fun _ => P) P' := by
  constructor
  · intro h u hu
    exact ⟨fun n => hX (u n), hZ, h.tendsto.comp hu⟩
  · intro h
    refine ⟨hX, hZ, Filter.tendsto_iff_seq_tendsto.mpr ?_⟩
    intro u hu
    exact (h u hu).tendsto




/-- A finite annealed absolute mass supplies samplewise and annealed
integrability of a real random-measure integral. -/
theorem integrable_randomMeasure_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {B : Ω → Measure X} (hB : Measurable B) {H : X → ℝ} (hH : Measurable H)
    (hfin : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal |H x| ∂(B ω) ∂P) < ⊤) :
    (∀ᵐ ω ∂P, Integrable H (B ω)) ∧ Integrable (fun ω => ∫ x, H x ∂(B ω)) P := by
  have hAbs : Measurable (fun x => |H x|) := by
    simpa only [Real.norm_eq_abs] using hH.norm
  have hm := (Measure.measurable_lintegral hAbs.ennreal_ofReal).comp hB
  change Measurable (fun ω => ∫⁻ x, ENNReal.ofReal |H x| ∂(B ω)) at hm
  have hfi : ∀ᵐ ω ∂P, Integrable H (B ω) := by
    filter_upwards [ae_lt_top hm hfin.ne] with ω hω
    refine ⟨hH.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    simpa only [Real.enorm_eq_ofReal_abs] using hω
  have hp := (Measure.measurable_lintegral hH.ennreal_ofReal).comp hB
  change Measurable (fun ω => ∫⁻ x, ENNReal.ofReal (H x) ∂(B ω)) at hp
  have hn := (Measure.measurable_lintegral hH.neg.ennreal_ofReal).comp hB
  change Measurable (fun ω => ∫⁻ x, ENNReal.ofReal (-H x) ∂(B ω)) at hn
  have he : (fun ω => (∫⁻ x, ENNReal.ofReal (H x) ∂(B ω)).toReal -
      (∫⁻ x, ENNReal.ofReal (-H x) ∂(B ω)).toReal) =ᵐ[P]
        (fun ω => ∫ x, H x ∂(B ω)) := by
    filter_upwards [hfi] with ω hω
    exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω).symm
  have hmeas := (hp.ennreal_toReal.sub hn.ennreal_toReal).aemeasurable.congr he
  refine ⟨hfi, (integrable_toReal_of_lintegral_ne_top hm.aemeasurable hfin.ne).mono'
    hmeas.aestronglyMeasurable ?_⟩
  filter_upwards with ω
  rw [← integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => abs_nonneg (H x)) hAbs.aestronglyMeasurable]
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := B ω) H

/-- Positive and negative annealed masses evaluate the signed expectation.
The finite absolute-mass premise is discharged by moment formulas at use sites. -/
theorem integral_randomMeasure_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {B : Ω → Measure X} (hB : Measurable B) {H : X → ℝ} (hH : Measurable H)
    (hfin : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal |H x| ∂(B ω) ∂P) < ⊤) :
    (∫ ω, ∫ x, H x ∂(B ω) ∂P) =
      (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (H x) ∂(B ω) ∂P).toReal -
        (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (-H x) ∂(B ω) ∂P).toReal := by
  have hfi := (integrable_randomMeasure_integral hB hH hfin).1
  have hp := (Measure.measurable_lintegral hH.ennreal_ofReal).comp hB
  change Measurable (fun ω => ∫⁻ x, ENNReal.ofReal (H x) ∂(B ω)) at hp
  have hn := (Measure.measurable_lintegral hH.neg.ennreal_ofReal).comp hB
  change Measurable (fun ω => ∫⁻ x, ENNReal.ofReal (-H x) ∂(B ω)) at hn
  have hpfin : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (H x) ∂(B ω) ∂P) < ⊤ := by
    apply lt_of_le_of_lt _ hfin
    apply lintegral_mono
    intro ω
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hnfin : (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (-H x) ∂(B ω) ∂P) < ⊤ := by
    apply lt_of_le_of_lt _ hfin
    apply lintegral_mono
    intro ω
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (neg_le_abs _)
  calc
    _ = ∫ ω, ((∫⁻ x, ENNReal.ofReal (H x) ∂(B ω)).toReal -
          (∫⁻ x, ENNReal.ofReal (-H x) ∂(B ω)).toReal) ∂P := by
      apply integral_congr_ae
      filter_upwards [hfi] with ω hω
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω
    _ = _ := by
      rw [integral_sub (integrable_toReal_of_lintegral_ne_top hp.aemeasurable hpfin.ne)
        (integrable_toReal_of_lintegral_ne_top hn.aemeasurable hnfin.ne),
        integral_toReal hp.aemeasurable (ae_lt_top hp hpfin.ne),
        integral_toReal hn.aemeasurable (ae_lt_top hn hnfin.ne)]

/-- Cramér--Wold along an arbitrary countably generated filter.  The explicit
measurability premises also cover the bottom-filter boundary case. -/
theorem tendstoInDistribution_iff_inner {ι Ω Ω' E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : ι → Ω → E} {Z : Ω' → E} {F : Filter ι} [F.IsCountablyGenerated]
    (hX : ∀ i, AEMeasurable (X i) P) (hZ : AEMeasurable Z P') :
    TendstoInDistribution X F Z (fun _ => P) P' ↔
      ∀ t : E, TendstoInDistribution (fun i ω => inner ℝ (X i ω) t) F
        (fun ω => inner ℝ (Z ω) t) (fun _ => P) P' := by
  constructor
  · intro h t
    exact h.continuous_comp (continuous_id.inner continuous_const)
  · intro h
    apply (tendstoInDistribution_iff_forall_seq hX hZ).mpr
    intro u hu
    apply (tendstoInDistribution_iff_tendstoInDistribution_inner hZ
      (fun n => hX (u n))).mpr
    intro t
    exact (tendstoInDistribution_iff_forall_seq
      (fun i => (h t).forall_aemeasurable i)
      (h t).aemeasurable_limit).mp (h t) u hu

/-- Positive-semidefinite covariance matrices converging entrywise give weak
convergence of the corresponding centered multivariate Gaussian laws. -/
theorem tendstoInDistribution_gaussian_of_cov_tendsto
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (S : ℕ → Matrix κ κ ℝ) (S' : Matrix κ κ ℝ)
    (hS : Tendsto S atTop (𝓝 S'))
    (hSpos : ∀ n, (S n).PosSemidef) (hS'pos : S'.PosSemidef) :
    TendstoInDistribution (fun _ : ℕ => id) atTop id
      (fun n => ProbabilityTheory.multivariateGaussian 0 (S n))
      (ProbabilityTheory.multivariateGaussian 0 S') := by
  apply TendstoInDistribution.of_tendsto_charFun
    (fun _ => measurable_id.aemeasurable) measurable_id.aemeasurable
  intro x
  have hentry (i j : κ) : Tendsto (fun n => S n i j) atTop (𝓝 (S' i j)) :=
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hS i) j
  have hquad : Tendsto (fun n => x ⬝ᵥ S n *ᵥ x) atTop (𝓝 (x ⬝ᵥ S' *ᵥ x)) := by
    simp only [dotProduct, Matrix.mulVec]
    apply tendsto_finsetSum
    intro i hi
    apply Tendsto.mul tendsto_const_nhds
    apply tendsto_finsetSum
    intro j hj
    exact (hentry i j).mul tendsto_const_nhds
  have hexp : Tendsto (fun n => Complex.exp (-((x ⬝ᵥ S n *ᵥ x : ℝ) : ℂ) / 2)) atTop
      (𝓝 (Complex.exp (-((x ⬝ᵥ S' *ᵥ x : ℝ) : ℂ) / 2))) := by
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    exact ((RCLike.continuous_ofReal (K := ℂ)).continuousAt.tendsto.comp hquad).neg.div_const 2
  simp only [Measure.map_id]
  simp_rw [ProbabilityTheory.charFun_multivariateGaussian (hSpos _) x,
    ProbabilityTheory.charFun_multivariateGaussian hS'pos x]
  simpa only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, neg_div] using hexp



set_option backward.isDefEq.respectTransparency.types false in
/-- Converging together with the iterated probability-tail condition stated in its directly usable
form: for large approximation index `k`, the approximation is uniformly good eventually along
`F`. -/
theorem tendstoInDistribution_of_converging_together_tail_varying
    {ι Ω Ω' ΩLimit E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace ΩLimit]
    [SeminormedAddCommGroup E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : ℕ → Measure Ω'} [∀ k, IsProbabilityMeasure (P' k)]
    {PLimit : Measure ΩLimit} [IsProbabilityMeasure PLimit]
    {F : Filter ι} [F.IsCountablyGenerated] [F.NeBot]
    {X : ι → ℕ → Ω → E} {Y : ℕ → Ω' → E} {YLimit : ΩLimit → E} {W : ι → Ω → E}
    (hX : ∀ i k, AEMeasurable (X i k) P) (_hY : ∀ k, AEMeasurable (Y k) (P' k))
    (hYLimit : AEMeasurable YLimit PLimit) (hW : ∀ i, AEMeasurable (W i) P)
    (hXY : ∀ k, TendstoInDistribution (fun i => X i k) F (Y k) (fun _ => P) (P' k))
    (hYlim : TendstoInDistribution Y atTop YLimit P' PLimit)
    (hclose : ∀ ε > 0, ∀ δ > 0, ∀ᶠ k : ℕ in atTop, ∀ᶠ i in F,
      P.real {ω | ε < ‖X i k ω - W i ω‖} < δ) :
    TendstoInDistribution W F YLimit (fun _ => P) PLimit := by
  rcases isEmpty_or_nonempty E with hE | hE
  · simp
  let x₀ : E := hE.some
  refine ⟨hW, hYLimit, ?_⟩
  rw [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro f hf_bounded hf_lip
  obtain ⟨M, hMbound⟩ := hf_bounded
  obtain ⟨L, hLlip⟩ := hf_lip
  have hM : 0 ≤ M := by
    have := hMbound x₀ x₀
    simpa only [dist_self] using this
  have h_int (Q : Measure Ω) [IsProbabilityMeasure Q] (Z : Ω → E)
      (hZ : AEMeasurable Z Q) : Integrable (fun ω => f (Z ω)) Q := by
    apply Integrable.of_bound
      (hLlip.continuous.measurable.comp_aemeasurable hZ).aestronglyMeasurable
      (‖f x₀‖ + M)
    filter_upwards with ω
    have hb := hMbound (Z ω) x₀
    rw [← sub_le_iff_le_add']
    exact (abs_sub_abs_le_abs_sub (f (Z ω)) (f x₀)).trans hb
  have h_perturb (i : ι) (k : ℕ) (r : ℝ) (hr : 0 < r) :
      |(∫ z, f z ∂P.map (W i)) - ∫ z, f z ∂P.map (X i k)| ≤
        L * r + M * P.real {ω | r ≤ ‖W i ω - X i k ω‖} := by
    have h_int_W := h_int P (W i) (hW i)
    have h_int_X := h_int P (X i k) (hX i k)
    have h_int_sub : Integrable (fun ω => ‖f (W i ω) - f (X i k ω)‖) P := by
      exact (h_int_W.sub h_int_X).norm
    rw [integral_map (hW i) hLlip.continuous.aestronglyMeasurable,
      integral_map (hX i k) hLlip.continuous.aestronglyMeasurable,
      ← integral_sub h_int_W h_int_X, ← Real.norm_eq_abs]
    calc
      ‖∫ ω, f (W i ω) - f (X i k ω) ∂P‖
          ≤ ∫ ω, ‖f (W i ω) - f (X i k ω)‖ ∂P :=
        norm_integral_le_integral_norm _
      _ = ∫ ω in {ω | ‖W i ω - X i k ω‖ < r},
              ‖f (W i ω) - f (X i k ω)‖ ∂P
            + ∫ ω in {ω | r ≤ ‖W i ω - X i k ω‖},
              ‖f (W i ω) - f (X i k ω)‖ ∂P := by
        symm
        simp_rw [← not_lt]
        apply integral_add_compl₀
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact h_int_sub
      _ ≤ ∫ _ in {ω | ‖W i ω - X i k ω‖ < r}, L * r ∂P
            + ∫ _ in {ω | r ≤ ‖W i ω - X i k ω‖}, M ∂P := by
        gcongr ?_ + ?_
        · apply setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const
          · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
          · intro ω hω
            exact hLlip.norm_sub_le_of_le hω.le
        · apply setIntegral_mono h_int_sub.integrableOn integrableOn_const
          intro ω
          change ‖f (W i ω) - f (X i k ω)‖ ≤ M
          simpa only [Real.norm_eq_abs, Real.dist_eq] using hMbound (W i ω) (X i k ω)
      _ = L * r * P.real {ω | ‖W i ω - X i k ω‖ < r}
            + M * P.real {ω | r ≤ ‖W i ω - X i k ω‖} := by
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
          Set.univ_inter, smul_eq_mul]
        ring
      _ ≤ L * r + M * P.real {ω | r ≤ ‖W i ω - X i k ω‖} := by
        exact add_le_add
          (mul_le_of_le_one_right (by positivity) measureReal_le_one) le_rfl
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  intro η hη
  let r : ℝ := η / (6 * ((L : ℝ) + 1))
  let δ : ℝ := η / (6 * (M + 1))
  have hr : 0 < r := by positivity
  have hδ : 0 < δ := by positivity
  have hYtest : Tendsto (fun k => ∫ z, f z ∂(P' k).map (Y k)) atTop
      (𝓝 (∫ z, f z ∂PLimit.map YLimit)) := by
    have ht := hYlim.tendsto
    rw [tendsto_iff_forall_lipschitz_integral_tendsto] at ht
    exact ht f ⟨M, hMbound⟩ ⟨L, hLlip⟩
  have hYevent : ∀ᶠ k : ℕ in atTop,
      |(∫ z, f z ∂(P' k).map (Y k)) - ∫ z, f z ∂PLimit.map YLimit| < η / 3 := by
    simpa only [Real.dist_eq] using hYtest.eventually (Metric.ball_mem_nhds _ (by positivity))
  have hcloseK := hclose (r / 2) (by positivity) δ hδ
  obtain ⟨k, hkY, hkclose⟩ := (hYevent.and hcloseK).exists
  have hXtest : Tendsto (fun i => ∫ z, f z ∂P.map (X i k)) F
      (𝓝 (∫ z, f z ∂(P' k).map (Y k))) := by
    have ht := (hXY k).tendsto
    rw [tendsto_iff_forall_lipschitz_integral_tendsto] at ht
    exact ht f ⟨M, hMbound⟩ ⟨L, hLlip⟩
  have hXevent : ∀ᶠ i in F,
      |(∫ z, f z ∂P.map (X i k)) - ∫ z, f z ∂(P' k).map (Y k)| < η / 3 := by
    simpa only [Real.dist_eq] using hXtest.eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [hXevent, hkclose] with i hiX hiclose
  have hbad : P.real {ω | r ≤ ‖W i ω - X i k ω‖} < δ := by
    apply lt_of_le_of_lt (measureReal_mono ?_) hiclose
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [norm_sub_rev]
    exact lt_of_lt_of_le (half_lt_self hr) hω
  have hWX := h_perturb i k r hr
  have hsmall : L * r + M * P.real {ω | r ≤ ‖W i ω - X i k ω‖} < η / 3 := by
    apply lt_of_le_of_lt
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbad.le hM)) ?_
    have hLfrac : (L : ℝ) / ((L : ℝ) + 1) < 1 :=
      (div_lt_one (by positivity)).mpr (by linarith)
    have hMfrac : M / (M + 1) < 1 :=
      (div_lt_one (by linarith)).mpr (by linarith)
    have hLterm : (L : ℝ) * r < η / 6 := by
      calc
        (L : ℝ) * r = (η / 6) * ((L : ℝ) / ((L : ℝ) + 1)) := by
          dsimp only [r]
          field_simp [show (L : ℝ) + 1 ≠ 0 by positivity]
        _ < (η / 6) * 1 := mul_lt_mul_of_pos_left hLfrac (by positivity)
        _ = η / 6 := mul_one _
    have hMterm : M * δ < η / 6 := by
      calc
        M * δ = (η / 6) * (M / (M + 1)) := by
          dsimp only [δ]
          field_simp [show M + 1 ≠ 0 by linarith]
        _ < (η / 6) * 1 := mul_lt_mul_of_pos_left hMfrac (by positivity)
        _ = η / 6 := mul_one _
    linarith
  have hWXsmall := hWX.trans_lt hsmall
  calc
    |(∫ z, f z ∂P.map (W i)) - ∫ z, f z ∂PLimit.map YLimit|
        ≤ |(∫ z, f z ∂P.map (W i)) - ∫ z, f z ∂P.map (X i k)|
          + |(∫ z, f z ∂P.map (X i k)) - ∫ z, f z ∂(P' k).map (Y k)|
          + |(∫ z, f z ∂(P' k).map (Y k)) - ∫ z, f z ∂PLimit.map YLimit| := by
            linarith [abs_sub_le (∫ z, f z ∂P.map (W i))
              (∫ z, f z ∂P.map (X i k)) (∫ z, f z ∂PLimit.map YLimit),
              abs_sub_le (∫ z, f z ∂P.map (X i k))
                (∫ z, f z ∂(P' k).map (Y k)) (∫ z, f z ∂PLimit.map YLimit)]
    _ < η := by linarith




/-- An eventually dominating family of second-moment bounds with vanishing
iterated limit implies the probability-tail hypothesis used by the
converging-together theorem. -/
theorem probability_tail_eventually_of_sq_moment_le_tendsto
    {ι Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filter ι}
    (X : ι → ℕ → Ω → E) (W : ι → Ω → E)
    (a : ι → ℕ → ℝ) (b : ℕ → ℝ)
    (hInt : ∀ k, ∀ᶠ i in F,
      Integrable (fun ω => ‖X i k ω - W i ω‖ ^ 2) P)
    (hle : ∀ k, ∀ᶠ i in F,
      (∫ ω, ‖X i k ω - W i ω‖ ^ 2 ∂P) ≤ a i k)
    (hmom : ∀ k, Tendsto (fun i => a i k) F (𝓝 (b k)))
    (hb : Tendsto b atTop (𝓝 0)) :
    ∀ ε > 0, ∀ δ > 0, ∀ᶠ k : ℕ in atTop, ∀ᶠ i in F,
      P.real {ω | ε < ‖X i k ω - W i ω‖} < δ := by
  intro ε hε δ hδ
  let c : ℝ := δ * ε ^ 2
  have hc : 0 < c := mul_pos hδ (sq_pos_of_pos hε)
  have hb_event : ∀ᶠ k : ℕ in atTop, |b k| < c / 2 := by
    have he := hb.eventually (Metric.ball_mem_nhds (0 : ℝ) (half_pos hc))
    simpa only [Real.dist_eq, sub_zero] using he
  filter_upwards [hb_event] with k hbk
  have ha_event : ∀ᶠ i in F, |a i k - b k| < c / 2 := by
    have he := (hmom k).eventually (Metric.ball_mem_nhds (b k) (half_pos hc))
    simpa only [Real.dist_eq] using he
  filter_upwards [hInt k, hle k, ha_event] with i hi hmean_le hai
  let g : Ω → ℝ := fun ω => ‖X i k ω - W i ω‖ ^ 2
  have hg_nonneg : 0 ≤ᵐ[P] g :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  have ha_lt : a i k < c := by
    have hb_upper : b k < c / 2 :=
      lt_of_le_of_lt (le_abs_self _) hbk
    have hdiff_upper : a i k - b k < c / 2 :=
      lt_of_le_of_lt (le_abs_self _) hai
    linarith
  have hmean_lt : (∫ ω, g ω ∂P) < c := by
    exact hmean_le.trans_lt ha_lt
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hg_nonneg hi (ε ^ 2)
  have hsubset : {ω | ε < ‖X i k ω - W i ω‖} ⊆
      {ω | ε ^ 2 ≤ g ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    dsimp only [g]
    exact (sq_lt_sq₀ hε.le (norm_nonneg _)).mpr hω |>.le
  have hmeasure :
      ε ^ 2 * P.real {ω | ε < ‖X i k ω - W i ω‖} < c := by
    exact (mul_le_mul_of_nonneg_left (measureReal_mono hsubset)
      (sq_nonneg ε) |>.trans hmarkov).trans_lt hmean_lt
  have heps2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  apply lt_of_mul_lt_mul_left (a := ε ^ 2) ?_ heps2.le
  simpa only [c, mul_comm] using hmeasure

end Critical2DKPZ.Extensions.GffTangent
