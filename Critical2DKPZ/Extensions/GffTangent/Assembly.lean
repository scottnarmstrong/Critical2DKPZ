/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.Reduction
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Critical2DKPZ.Extensions.GffTangent.FiniteGaussian
public import Critical2DKPZ.Extensions.GffTangent.LinearClt
import Critical2DKPZ.Extensions.GffTangent.LinearCovariance
import Critical2DKPZ.Extensions.GffTangent.FixedHorizonMollifiedClt
import Critical2DKPZ.Extensions.GffTangent.Uv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Critical2DKPZ.Provider.CriticalKPZInvariance

/-! # Measurability and normalization for the microscopic Gaussian limit -/

public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.GffTangent

universe u

/-- The vector in the microscopic GFF limit is a.e. measurable for
every positive width and for every associated version of the KPZ field. -/
theorem microscopic_vector_aemeasurable (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (ε : ℝ) (x : Plane) (n : ℕ) (f : Fin n → TestFn) :
    AEMeasurable (fun ω => WithLp.toLp 2 (fun i : Fin n =>
      Real.sqrt (Real.log ε⁻¹) * H t 0 ω ((f i).dilate ε x))) P := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp_aemeasurable
  apply aemeasurable_pi_iff.mpr
  intro i
  exact ((Critical2DKPZ.Provider.criticalKPZ_invariance.{u, u} ϑ P Z hZ H hH n
    (fun _ => t) (fun _ => ht) (fun j => (f j).dilate ε x)).1 i).const_mul _

/-- The microscopic parameter diverges as the spatial width tends to zero. -/
theorem microscopicParameter_tendsto (ϑ : ℝ) :
    Tendsto (microscopicParameter ϑ) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hm : Tendsto (fun ε : ℝ => 2 * Real.log ε⁻¹) (𝓝[>] 0) atTop :=
    hlog.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  change Tendsto (fun ε : ℝ => 2 * Real.log ε⁻¹ - ϑ) (𝓝[>] 0) atTop
  simpa only [sub_eq_add_neg] using
    tendsto_atTop_add_const_right (𝓝[>] (0 : ℝ)) (-ϑ) hm

/-- The double scale clock and the microscopic logarithm have asymptotically
equal square-root normalizations. -/
theorem microscopic_normalization_tendsto (ϑ : ℝ) :
    Tendsto (fun ε : ℝ => Real.sqrt (Real.log ε⁻¹) /
      Real.sqrt (microscopicParameter ϑ ε / 2)) (𝓝[>] 0) (𝓝 1) := by
  have hlog : Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hsmall : Tendsto (fun ε : ℝ => (ϑ / 2) / Real.log ε⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hr : Tendsto (fun ε : ℝ => (microscopicParameter ϑ ε / 2) / Real.log ε⁻¹)
      (𝓝[>] 0) (𝓝 1) := by
    have ht : Tendsto (fun ε : ℝ => 1 - (ϑ / 2) / Real.log ε⁻¹) (𝓝[>] 0) (𝓝 1) := by
      simpa only [sub_zero] using (tendsto_const_nhds.sub hsmall)
    apply ht.congr'
    filter_upwards [hlog.eventually_gt_atTop 0] with ε hε
    have halg (v : ℝ) (hv : v ≠ 0) : 1 - (ϑ / 2) / v = ((2 * v - ϑ) / 2) / v := by
      field_simp
    exact halg _ hε.ne'
  have hs : Tendsto (fun ε : ℝ =>
      (Real.sqrt ((microscopicParameter ϑ ε / 2) / Real.log ε⁻¹))⁻¹)
      (𝓝[>] 0) (𝓝 1) := by
    simpa only [Real.sqrt_one, inv_one] using hr.sqrt.inv₀ (by norm_num : Real.sqrt 1 ≠ 0)
  apply hs.congr'
  filter_upwards [(microscopicParameter_tendsto ϑ).eventually_gt_atTop 0] with ε hε
  rw [Real.sqrt_div (by positivity : 0 ≤ microscopicParameter ϑ ε / 2), inv_div]

private theorem aemeasurable_delayed_heatSmoothPairing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {l a T δ : ℝ} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF (-l) P Z) (ha : 0 ≤ a) (haT : a < T)
    (hδ : 0 ≤ δ) (f : TestFn) :
    AEMeasurable (shfPairing Z a T (heatSmooth' δ f) (fun _ => 1)) P := by
  have hfi : Integrable (f : Plane → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hm : Measurable (heatSmooth' δ f) := by
    unfold heatSmooth'
    split_ifs
    · exact f.continuous.measurable
    · exact measurable_heatSmooth_testFn f δ
  have hi : Integrable (heatSmooth' δ f) := by
    unfold heatSmooth'
    split_ifs with he
    · exact hfi
    · exact integrable_heatSmooth hfi (lt_of_le_of_ne hδ (Ne.symm he))
  exact (integrable_shfPairing_one (-l) P Z hZ ha haT hm hi).2.aemeasurable

/-- Assembly after UV removal/localisation: a delayed mollified linear field
with eventually valid interval inherits the moving-horizon CLT, and an
`o_P(1)` approximation inherits its limit.  `max (S-m) 1` supplies an honest
positive horizon at every index. -/
theorem target_gff_of_uv
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : Fin n → TestFn) (hf : ∀ i, (∫ x, f i x) = 0)
    (m S : ℝ → ℝ)
    (hm : ∀ l, 0 ≤ m l)
    (hm0 : Tendsto m atTop (𝓝 0))
    (horder : ∀ᶠ l in atTop, m l < S l)
    (hS : Tendsto S atTop atTop)
    (hlogS : Tendsto (fun l => Real.log (S l) / l) atTop (𝓝 0))
    (K : ℝ → Ω → EuclideanSpace ℝ (Fin n))
    (hKmeas : ∀ l, AEMeasurable (K l) P)
    (hclose : TendstoInMeasure P
      (fun l ω => K l ω - (if m l < S l then
        WithLp.toLp 2 (fun i => Real.sqrt (l / 2) *
          shfPairing (Z l) (m l) (S l) (heatSmooth' (m l) (f i)) (fun _ => 1) ω)
        else 0))
      atTop (fun _ => 0))
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : IsFiniteGffLaw f ν) :
    TendstoInDistribution K atTop id (fun _ => P) ν := by
  let T : ℝ → ℝ := fun l => max (S l - m l) 1
  let W : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun l ω =>
    WithLp.toLp 2 (fun i => Real.sqrt (l / 2) *
      shfPairing (Z l) 0 (T l) (heatSmooth' (m l) (f i)) (fun _ => 1) ω)
  let D : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun l ω =>
    if m l < S l then WithLp.toLp 2 (fun i => Real.sqrt (l / 2) *
      shfPairing (Z l) (m l) (S l) (heatSmooth' (m l) (f i)) (fun _ => 1) ω)
    else 0
  have hTpos : ∀ l, 0 < T l := fun l => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hT_event : T =ᶠ[atTop] fun l => S l - m l := by
    filter_upwards [horder, hS.eventually_gt_atTop 2,
      hm0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with l hml hSl hmlt
    have : 1 ≤ S l - m l := by linarith
    exact max_eq_left this
  have hTtop : Tendsto T atTop atTop := by
    apply tendsto_atTop_mono' atTop _
      (tendsto_atTop_add_const_right atTop (-1) hS)
    filter_upwards [hm0.eventually (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with l hml
    dsimp only [T]
    exact (sub_le_sub_left hml.le (S l)).trans (le_max_left _ _)
  have hlogT : Tendsto (fun l => Real.log (T l) / l) atTop (𝓝 0) := by
    apply Tendsto.congr' (hT_event.mono fun l hl => by rw [hl])
    have hratio : Tendsto (fun l => (S l - m l) / S l) atTop (𝓝 1) := by
      have hsInv : Tendsto (fun l => (S l)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hS
      have hmdiv : Tendsto (fun l => m l / S l) atTop (𝓝 0) := by
        simpa only [div_eq_mul_inv, zero_mul] using hm0.mul hsInv
      have ht : Tendsto (fun l => 1 - m l / S l) atTop (𝓝 1) := by
        simpa only [sub_zero] using tendsto_const_nhds.sub hmdiv
      apply ht.congr'
      filter_upwards [hS.eventually_gt_atTop 0] with l hl
      rw [sub_div, div_self hl.ne']
    have hlogratio : Tendsto (fun l => Real.log ((S l - m l) / S l)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.log_one] using (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hratio
    have hdecomp : ∀ᶠ l in atTop,
        Real.log (S l - m l) / l =
          Real.log (S l) / l + Real.log ((S l - m l) / S l) / l := by
      filter_upwards [horder, hS.eventually_gt_atTop 0] with l hml hSl
      rw [Real.log_div (sub_pos.mpr hml).ne' hSl.ne']
      ring
    apply Tendsto.congr' (hdecomp.mono fun _ h => h.symm)
    have hsecond : Tendsto (fun l => Real.log ((S l - m l) / S l) / l)
        atTop (𝓝 0) := by
      simpa only [id_eq, zero_div] using hlogratio.div_atTop tendsto_id
    simpa only [add_zero] using hlogS.add hsecond
  have hW : TendstoInDistribution W atTop id (fun _ => P) ν := by
    exact tendstoInDistribution_sqrt_half_shfPairing_mollified
      P Z hZ f hf T hTpos hTtop hlogT m hm hm0 ν hν
  have hDmeas : ∀ l, AEMeasurable (D l) P := by
    intro l
    by_cases hlt : m l < S l
    · simp only [D, ite_eq_left hlt]
      apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp_aemeasurable
      apply aemeasurable_pi_iff.mpr
      intro i
      exact (aemeasurable_delayed_heatSmoothPairing P (Z l) (hZ l)
        (hm l) hlt (hm l) (f i)).const_mul _
    · simp only [D, ite_eq_right hlt]
      exact aemeasurable_const
  have hDWlaw : ∀ᶠ l in atTop, P.map (D l) = P.map (W l) := by
    filter_upwards [horder, hT_event] with l hml hTl
    let U : Ω → Fin n → ℝ := fun ω i =>
      shfPairing (Z l) (m l) (S l) (heatSmooth' (m l) (f i)) (fun _ => 1) ω
    let V : Ω → Fin n → ℝ := fun ω i =>
      shfPairing (Z l) 0 (S l - m l) (heatSmooth' (m l) (f i)) (fun _ => 1) ω
    let scale : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := fun v =>
      WithLp.toLp 2 (fun i => Real.sqrt (l / 2) * v i)
    have hU : AEMeasurable U P := aemeasurable_pi_iff.mpr fun i =>
      aemeasurable_delayed_heatSmoothPairing P (Z l) (hZ l) (hm l) hml (hm l) (f i)
    have hV : AEMeasurable V P := aemeasurable_pi_iff.mpr fun i =>
      aemeasurable_delayed_heatSmoothPairing P (Z l) (hZ l) le_rfl (sub_pos.mpr hml) (hm l) (f i)
    have hg (i : Fin n) : Measurable (heatSmooth' (m l) (f i)) := by
      unfold heatSmooth'
      split_ifs
      · exact (f i).continuous.measurable
      · exact measurable_heatSmooth_testFn (f i) (m l)
    have hscale : Measurable scale := by fun_prop
    have hlaw := law_timeShift_vector (-l) P (Z l) (hZ l)
      (hm l) hml n (fun i => heatSmooth' (m l) (f i))
      hg
    change P.map U = P.map V at hlaw
    simp only [D, ite_eq_left hml, W, hTl]
    calc
      P.map (scale ∘ U) = (P.map U).map scale :=
        (hscale.aemeasurable.map_map_of_aemeasurable hU).symm
      _ = (P.map V).map scale := congrArg (fun μ : Measure (Fin n → ℝ) => μ.map scale) hlaw
      _ = P.map (scale ∘ V) := hscale.aemeasurable.map_map_of_aemeasurable hV
  have hD : TendstoInDistribution D atTop id (fun _ => P) ν := by
    refine ⟨hDmeas, hW.aemeasurable_limit, ?_⟩
    apply hW.tendsto.congr'
    filter_upwards [hDWlaw] with l hlaw
    exact ProbabilityMeasure.toMeasure_injective hlaw.symm
  exact tendstoInDistribution_of_tendstoInMeasure_sub K id hD (by simpa only [D, Pi.sub_def, Pi.zero_def] using hclose) hKmeas

private theorem tendstoInMeasure_fin_toLp
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {k : ℕ}
    {U : ℝ → Ω → Fin k → ℝ}
    (hU : ∀ i, TendstoInMeasure P (fun l ω => U l ω i) atTop (fun _ => 0)) :
    TendstoInMeasure P (fun l ω => WithLp.toLp 2 (U l ω)) atTop (fun _ => 0) := by
  rcases k with _ | k
  · rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have he (l : ℝ) (ω : Ω) : WithLp.toLp 2 (U l ω) = 0 := Subsingleton.elim _ _
    simp only [he, sub_self, norm_zero, not_le.mpr hε, Set.ofPred_false, measure_empty]
    exact tendsto_const_nhds
  · apply (tendstoInMeasure_iff_norm).2
    intro ε hε
    let d := ε / (k + 1 : ℝ)
    have hd : 0 < d := div_pos hε (by positivity)
    have hbound (l : ℝ) :
        P {ω | ε ≤ ‖WithLp.toLp 2 (U l ω) - 0‖} ≤
          ∑ i, P {ω | d ≤ ‖U l ω i - 0‖} := by
      calc
        _ ≤ P (⋃ i, {ω | d ≤ ‖U l ω i - 0‖}) := by
          apply measure_mono
          intro ω hω
          by_contra hn
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hn
          have hv : WithLp.toLp 2 (U l ω) =
              ∑ i, PiLp.single 2 i (U l ω i) := by
            ext j
            simp
          have hsum : ‖WithLp.toLp 2 (U l ω)‖ ≤ ∑ i, ‖U l ω i‖ := by
            rw [hv]
            exact (norm_sum_le _ _).trans_eq (by simp)
          have hlt : (∑ i, ‖U l ω i‖) < ε := by
            calc
              _ < ∑ _i : Fin (k+1), d := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
                (fun i _ => by simpa only [sub_zero] using hn i)
              _ = ε := by simp [d]; field_simp
          exact (not_lt_of_ge (by simpa only [Set.mem_ofPred_eq, sub_zero] using hω)) (hsum.trans_lt hlt)
        _ ≤ _ := measure_iUnion_fintype_le _ _
    have hs : Tendsto (fun l => ∑ i, P {ω | d ≤ ‖U l ω i - 0‖}) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using
        (tendsto_finsetSum Finset.univ (fun i _ =>
          (tendstoInMeasure_iff_norm.mp (hU i)) d hd))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs
      (fun _ => zero_le) hbound

private theorem TendstoInMeasure.const_mul_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ → Ω → ℝ}
    (hX : TendstoInMeasure P X atTop (fun _ => 0)) (c : ℝ) :
    TendstoInMeasure P (fun l ω => c * X l ω) atTop (fun _ => 0) := by
  by_cases hc : c = 0
  · subst c
    apply (tendstoInMeasure_iff_norm).2
    intro ε hε
    simp only [zero_mul, sub_zero, norm_zero, not_le.mpr hε, Set.ofPred_false, measure_empty]
    exact tendsto_const_nhds
  · apply (tendstoInMeasure_iff_norm).2
    intro ε hε
    have hcabs : 0 < |c| := abs_pos.mpr hc
    have h := (tendstoInMeasure_iff_norm.mp hX) (ε / |c|) (div_pos hε hcabs)
    apply h.congr'
    filter_upwards [] with l
    congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, sub_zero, norm_mul, Real.norm_eq_abs]
    simpa only [mul_comm] using (div_le_iff₀ hcabs : ε / |c| ≤ |X l ω| ↔ ε ≤ |X l ω| * |c|)

/-- The large-horizon GFF limit for every family of critical stochastic heat flows. -/
theorem target_gff {c : ℝ} (hc : 0 < c)
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : ∀ l, IsCriticalSHF (-l) P (Z l))
    (f : Fin n → TestFn) (hf : ∀ i, (∫ x, f i x) = 0)
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : IsFiniteGffLaw f ν) :
    TendstoInDistribution (fun l ω => WithLp.toLp 2 (fun i =>
      Real.sqrt (l / 2) * kField (-l) P (Z l) (hZ l)
        (c * Real.exp l) (mul_pos hc (Real.exp_pos l)) (f i) ω))
      atTop id (fun _ => P) (ν : Measure _) := by
  obtain ⟨ρ₀, qS, qM, hρ₀, hqS, hqS2, hqM, hqM2, huv⟩ := prop_uv hc
  let ρ := ρ₀
  have hρ : 1 < ρ := hρ₀
  let m := uvCoarseEntrance c ρ qM
  let S := gridHorizon c ρ qS
  let K : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun l ω => WithLp.toLp 2 (fun i =>
    Real.sqrt (l / 2) * kField (-l) P (Z l) (hZ l)
      (c * Real.exp l) (mul_pos hc (Real.exp_pos l)) (f i) ω)
  have hm : ∀ l, 0 ≤ m l := fun l => (uvCoarseEntrance_bounds hc hρ qM l).1.le
  have hm0 : Tendsto m atTop (𝓝 0) := uvCoarseEntrance_tendsto_zero hc hρ qM
  have horder : ∀ᶠ l in atTop, m l < S l := by
    filter_upwards [uvScales_horizon_order hc hρ hqS hqS2] with l hord
    exact (uvCoarseEntrance_bounds hc hρ qM l).2.trans_lt
      (hord.2.2.1.trans hord.2.2.2.1)
  have hS : Tendsto S atTop atTop := uvHorizon_tendsto_atTop hc hρ hqS hqS2
  have hlogS : Tendsto (fun l => Real.log (S l) / l) atTop (𝓝 0) :=
    uvHorizon_log_div_tendsto_zero hc hρ hqS hqS2
  have hKmeas (l : ℝ) : AEMeasurable (K l) P := by
    apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp_aemeasurable
    exact aemeasurable_pi_iff.mpr fun i =>
      (kField_aemeasurable (-l) P (Z l) (hZ l) (c*Real.exp l)
        (mul_pos hc (Real.exp_pos l)) (f i)).const_mul _
  have hcoord (i : Fin n) := (huv ρ le_rfl hρ P Z hZ (f i) (hf i)).2
  let B : ℝ → Ω → Fin n → ℝ := fun l ω i =>
    Real.sqrt (l / 2) * (kField (-l) P (Z l) (hZ l) (c * Real.exp l)
      (mul_pos hc (Real.exp_pos l)) (f i) ω -
      shfPairing (Z l) (m l) (S l) (heatSmooth' (m l) (f i)) (fun _ => 1) ω)
  have hscalar (i : Fin n) : TendstoInMeasure P (fun l ω => B l ω i) atTop (fun _ => 0) := by
    have hi := TendstoInMeasure.const_mul_zero (hcoord i) (Real.sqrt 2)⁻¹
    apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hi
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with l hl
    filter_upwards [] with ω
    dsimp only [B, m, S]
    rw [Real.sqrt_div hl]
    ring
  have hclose : TendstoInMeasure P
      (fun l ω => K l ω - (if m l < S l then WithLp.toLp 2 (fun i =>
        Real.sqrt (l/2) * shfPairing (Z l) (m l) (S l)
          (heatSmooth' (m l) (f i)) (fun _ => 1) ω) else 0))
      atTop (fun _ => 0) := by
    have hv := tendstoInMeasure_fin_toLp hscalar
    apply TendstoInMeasure.congr' ?_ EventuallyEq.rfl hv
    filter_upwards [horder] with l hml
    filter_upwards [] with ω
    ext i
    simp only [K, ite_eq_left hml, B, PiLp.sub_apply]
    ring
  exact target_gff_of_uv P Z hZ f hf m S hm hm0 horder hS hlogS K hKmeas hclose ν hν


end Critical2DKPZ.Extensions.GffTangent
