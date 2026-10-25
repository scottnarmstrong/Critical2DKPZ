/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.ProfileTruncation
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.Polymer.Series
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-! # Negative moments for summable polymer profiles -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Critical2DKPZ.SHF.Positivity

/-- Finite-polymer Gaussian calculus for summable nonnegative start profiles, by finite truncations and Fatou. -/
theorem integral_rpow_neg_profileP2Fun_le_of_summable {β : ℝ} (hβ : 0 ≤ β)
    (a b : ℕ) (ν : Site → ℝ) (hν0 : ∀ w, 0 ≤ ν w) (hν : Summable ν)
    (hν1 : ∑' w, ν w = 1) {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun ω => profileP2Fun β a b ν (fun _ => 1) ω ^ (-p)) disorderLaw ∧
    ∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ^ (-p) ∂disorderLaw ≤
      (∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ^ 2 ∂disorderLaw) ^ (p * (p + 1) / 2) := by
  classical
  let F : Disorder → ℝ := profileP2Fun β a b ν (fun _ => 1)
  let φ (k : ℕ) : Site → ℝ :=
    (↑(MomentBounds.boxSites k) : Set Site).indicator ν
  let m (k : ℕ) : ℝ := ∑ w ∈ MomentBounds.boxSites k, ν w
  let η (k : ℕ) : Site → ℝ := fun w => φ k w / m k
  let Fk (k : ℕ) : Disorder → ℝ := profileP2Fun β a b (φ k) (fun _ => 1)
  let Qk (k : ℕ) : Disorder → ℝ := profileP2Fun β a b (η k) (fun _ => 1)
  have hνabs : Summable (fun w => |ν w|) := by
    simpa only [abs_of_nonneg (hν0 _)] using hν
  have htrunc := profileP2Fun_box_truncation β a b ν hν0 hν
  have hm_tendsto : Tendsto m atTop (𝓝 1) := by
    simpa only [m, hν1] using htrunc.1
  have hm_pos : ∀ᶠ k : ℕ in atTop, 0 < m k := by
    filter_upwards [hm_tendsto.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with k hk
    exact hk
  obtain ⟨k₀, hk₀⟩ := (eventually_atTop.mp hm_pos)
  have hm_pos_all (k : ℕ) : 0 < m (k + k₀) := hk₀ (k + k₀) (by omega)
  have hm_tendsto' : Tendsto (fun k : ℕ => m (k + k₀)) atTop (𝓝 1) := by
    exact hm_tendsto.comp (tendsto_add_atTop_nat k₀)
  have hFn_tendsto : ∀ᵐ ω ∂disorderLaw,
      Tendsto (fun k : ℕ => Fk (k + k₀) ω) atTop (𝓝 (F ω)) := by
    filter_upwards [htrunc.2.1] with ω hω
    exact hω.comp (tendsto_add_atTop_nat k₀)
  have hFn_le (k : ℕ) : ∀ᵐ ω ∂disorderLaw, Fk (k + k₀) ω ≤ F ω :=
    htrunc.2.2 (k + k₀)
  have hηsupp (k : ℕ) : ∀ w ∉ MomentBounds.boxSites (k + k₀), η (k + k₀) w = 0 := by
    intro w hw
    simp [η, φ, hw]
  have hηnonneg (k : ℕ) : ∀ w, 0 ≤ η (k + k₀) w := by
    intro w
    apply div_nonneg _ (le_of_lt (hm_pos_all k))
    by_cases hw : w ∈ MomentBounds.boxSites (k + k₀)
    · have hφ : φ (k + k₀) w = ν w := by simp [φ, hw]
      rw [hφ]
      exact hν0 w
    · have hφ : φ (k + k₀) w = 0 := by simp [φ, hw]
      rw [hφ]
  have hφmass (n : ℕ) :
      (∑ w ∈ MomentBounds.boxSites n, φ n w) = m n := by
    dsimp [m]
    apply Finset.sum_congr rfl
    intro w hw
    dsimp [φ]
    exact Set.indicator_of_mem (Finset.mem_coe.mpr hw) ν
  have hηmass (k : ℕ) :
      ∑ w ∈ MomentBounds.boxSites (k + k₀), η (k + k₀) w = 1 := by
    rw [show (∑ w ∈ MomentBounds.boxSites (k + k₀), η (k + k₀) w) =
      (∑ w ∈ MomentBounds.boxSites (k + k₀), φ (k + k₀) w) / m (k + k₀) by
        simp [η, Finset.sum_div]]
    rw [hφmass]
    exact div_self (ne_of_gt (hm_pos_all k))
  have hQpos (k : ℕ) (ω : Disorder) : 0 < Qk (k + k₀) ω := by
    dsimp [Qk]
    exact OnePoint.profileP2Fun_pos_of_normalized β a b (η (k + k₀))
      (MomentBounds.boxSites (k + k₀)) (hηsupp k) (hηnonneg k) (hηmass k) ω
  have hscale (k : ℕ) (hmk : 0 < m (k + k₀)) (ω : Disorder) :
      Fk (k + k₀) ω = m (k + k₀) * Qk (k + k₀) ω := by
    dsimp [Fk, Qk]
    unfold profileP2Fun
    calc
      _ = ∑' w, (m (k + k₀) * η (k + k₀) w) *
          ∑' z, pointToPoint β a (b - a) w z ω * (1 : ℝ) := by
            apply tsum_congr
            intro w
            congr 2
            dsimp [η]
            field_simp [ne_of_gt hmk]
      _ = ∑' w, m (k + k₀) *
          (η (k + k₀) w * ∑' z, pointToPoint β a (b - a) w z ω * (1 : ℝ)) := by
            apply tsum_congr
            intro w
            ring
      _ = m (k + k₀) * Qk (k + k₀) ω := by
            change (∑' w, m (k + k₀) *
              (η (k + k₀) w * ∑' z, pointToPoint β a (b - a) w z ω * (1 : ℝ))) =
              m (k + k₀) * (∑' w, η (k + k₀) w *
                ∑' z, pointToPoint β a (b - a) w z ω * (1 : ℝ))
            rw [← tsum_mul_left]
  have hFpos : ∀ᵐ ω ∂disorderLaw, 0 < F ω := by
    filter_upwards [hFn_le 0] with ω hle
    have hpos := hQpos 0 ω
    have hscale0 := hscale 0 (hm_pos_all 0) ω
    have hle' : Fk k₀ ω ≤ F ω := by simpa only [Nat.zero_add] using hle
    have hFnpos : 0 < Fk k₀ ω := by
      calc
        0 < m k₀ * Qk k₀ ω := by simpa only [Nat.zero_add] using mul_pos (hm_pos_all 0) hpos
        _ = Fk k₀ ω := by simpa only [Nat.zero_add] using hscale0.symm
    exact hFnpos.trans_le hle'
  have hFmeas : Measurable F := by
    dsimp [F]
    exact Polymer.measurable_profileP2Fun β a b ν (fun _ => 1)
  have hFmem : MemLp F 2 disorderLaw := by
    dsimp [F]
    exact Polymer.memLp_profileP2Fun_summable β a b ν (fun _ => 1) hνabs
      1 (by norm_num) (by intro z; norm_num) 2 (by norm_num)
  have hF2 : Integrable (fun ω => F ω ^ 2) disorderLaw := by
    have h := hFmem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  let M : ℝ := ∫ ω, F ω ^ 2 ∂disorderLaw
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg fun ω => sq_nonneg (F ω)
  have hFpow_meas : AEMeasurable (fun ω => F ω ^ (-p)) disorderLaw := by
    have hEq : (fun ω => F ω ^ (-p)) =ᵐ[disorderLaw]
        fun ω => Real.exp (-p * Real.log (F ω)) := by
      filter_upwards [hFpos] with ω hω
      rw [Real.rpow_def_of_pos hω]
      congr 1
      ring
    apply (aemeasurable_congr hEq).2
    exact (Real.measurable_exp.comp (measurable_const.mul hFmeas.log)).aemeasurable
  have hFnegInt : Integrable (fun ω => F ω ^ (-p)) disorderLaw := by
    have hdom : ∀ᵐ ω ∂disorderLaw,
        ‖F ω ^ (-p)‖ ≤ Fk (k₀) ω ^ (-p) := by
      filter_upwards [hFpos, hFn_le 0] with ω hFω hle
      have hle0 : Fk k₀ ω ≤ F ω := by simpa only [Nat.zero_add] using hle
      have hFnpos : 0 < Fk k₀ ω := by
        have hscale0 := hscale 0 (hm_pos_all 0) ω
        calc
          0 < m k₀ * Qk k₀ ω := by
            simpa only [Nat.zero_add] using mul_pos (hm_pos_all 0) (hQpos 0 ω)
          _ = Fk k₀ ω := by simpa only [Nat.zero_add] using hscale0.symm
      have hpow : F ω ^ (-p) ≤ Fk k₀ ω ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos hFnpos hle0 (neg_nonpos.mpr hp)
      calc
        ‖F ω ^ (-p)‖ = F ω ^ (-p) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hFω.le _)]
        _ ≤ Fk k₀ ω ^ (-p) := hpow
    have hQint : Integrable (fun ω => Qk k₀ ω ^ (-p)) disorderLaw := by
      dsimp [Qk]
      exact OnePoint.integrable_rpow_profileP2Fun β a b (η k₀)
        (MomentBounds.boxSites k₀)
        (by simpa only [Nat.zero_add] using hηsupp 0)
        (by simpa only [Nat.zero_add] using hηnonneg 0)
        (by simpa only [Nat.zero_add] using hηmass 0) (-p)
    have hscalePow : (fun ω => Fk k₀ ω ^ (-p)) =ᵐ[disorderLaw]
        fun ω => (m k₀) ^ (-p) * Qk k₀ ω ^ (-p) := by
      filter_upwards [] with ω
      have hscale0 : Fk k₀ ω = m k₀ * Qk k₀ ω := by
        simpa only [Nat.zero_add] using hscale 0 (hm_pos_all 0) ω
      have hm0 : 0 < m k₀ := by simpa only [Nat.zero_add] using hm_pos_all 0
      calc
        Fk k₀ ω ^ (-p) = (m k₀ * Qk k₀ ω) ^ (-p) := by rw [hscale0]
        _ = m k₀ ^ (-p) * Qk k₀ ω ^ (-p) :=
          Real.mul_rpow (le_of_lt hm0) (by simpa only [Nat.zero_add] using (hQpos 0 ω).le)
    have hFnInt : Integrable (fun ω => Fk k₀ ω ^ (-p)) disorderLaw := by
      exact (hQint.const_mul _).congr hscalePow.symm
    exact hFnInt.mono' hFpow_meas.aestronglyMeasurable hdom
  have hQnegInt (k : ℕ) : Integrable (fun ω => Qk (k + k₀) ω ^ (-p)) disorderLaw := by
    dsimp [Qk]
    exact OnePoint.integrable_rpow_profileP2Fun β a b (η (k + k₀))
      (MomentBounds.boxSites (k + k₀)) (hηsupp k) (hηnonneg k) (hηmass k) (-p)
  have hQtwoInt (k : ℕ) : Integrable (fun ω => Qk (k + k₀) ω ^ 2) disorderLaw := by
    have h := OnePoint.integrable_rpow_profileP2Fun β a b (η (k + k₀))
      (MomentBounds.boxSites (k + k₀)) (hηsupp k) (hηnonneg k) (hηmass k) 2
    have h' : Integrable (fun ω => Qk (k + k₀) ω ^ (2 : ℝ)) disorderLaw := by
      simpa only [Qk] using h
    have hEq : (fun ω => Qk (k + k₀) ω ^ (2 : ℝ)) =
        fun ω => Qk (k + k₀) ω ^ 2 := by
      funext ω
      exact Real.rpow_natCast _ 2
    exact h'.congr (Filter.Eventually.of_forall fun ω => congrFun hEq ω)
  have hQsquare_bound (k : ℕ) :
      ∫ ω, Qk (k + k₀) ω ^ 2 ∂disorderLaw ≤ M / (m (k + k₀)) ^ 2 := by
    have hFbound : ∀ᵐ ω ∂disorderLaw,
        Qk (k + k₀) ω ≤ F ω / m (k + k₀) := by
      filter_upwards [hFn_le k] with ω hle
      rw [hscale k (hm_pos_all k) ω] at hle
      exact (le_div_iff₀ (hm_pos_all k)).2 (by linarith)
    have hFnonneg : 0 ≤ᵐ[disorderLaw] fun ω => F ω / m (k + k₀) := by
      filter_upwards [hFpos] with ω hω
      exact div_nonneg hω.le (le_of_lt (hm_pos_all k))
    have hsq : ∀ᵐ ω ∂disorderLaw,
        Qk (k + k₀) ω ^ 2 ≤ (F ω / m (k + k₀)) ^ 2 := by
      filter_upwards [hFbound, hFnonneg] with ω hle hnonneg
      exact (sq_le_sq₀ (hQpos k ω).le hnonneg).2 hle
    have hFscaledInt : Integrable (fun ω => (F ω / m (k + k₀)) ^ 2) disorderLaw := by
      have hEq : (fun ω => (F ω / m (k + k₀)) ^ 2) =
          fun ω => (m (k + k₀))⁻¹ ^ 2 * F ω ^ 2 := by
        funext ω
        field_simp [ne_of_gt (hm_pos_all k)]
      rw [hEq]
      exact hF2.const_mul _
    have hsqEq (ω : Disorder) : (F ω / m (k + k₀)) ^ 2 =
        (m (k + k₀))⁻¹ ^ 2 * F ω ^ 2 := by
      field_simp [ne_of_gt (hm_pos_all k)]
    calc
      _ ≤ ∫ ω, (F ω / m (k + k₀)) ^ 2 ∂disorderLaw :=
        integral_mono_ae (hQtwoInt k) hFscaledInt hsq
      _ = (m (k + k₀))⁻¹ ^ 2 * M := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hsqEq), integral_const_mul]
      _ = M / (m (k + k₀)) ^ 2 := by
        dsimp [M]
        field_simp [ne_of_gt (hm_pos_all k)]
  have he : 0 ≤ p * (p + 1) / 2 := by positivity
  have hProfileInverseMomentInput (k : ℕ) :
      ∫ ω, Qk (k + k₀) ω ^ (-p) ∂disorderLaw ≤
        (∫ ω, Qk (k + k₀) ω ^ 2 ∂disorderLaw) ^ (p * (p + 1) / 2) := by
    simpa only [Qk] using OnePoint.integral_rpow_neg_profileP2Fun_le hβ a b
      (η (k + k₀)) (MomentBounds.boxSites (k + k₀)) (hηsupp k) (hηnonneg k)
      (hηmass k) hp
  have hQbound (k : ℕ) :
      ∫ ω, Qk (k + k₀) ω ^ (-p) ∂disorderLaw ≤
        (M / (m (k + k₀)) ^ 2) ^ (p * (p + 1) / 2) := by
    exact (hProfileInverseMomentInput k).trans (Real.rpow_le_rpow
      (integral_nonneg fun ω => sq_nonneg (Qk (k + k₀) ω))
      (hQsquare_bound k) he)
  have hbase_tendsto :
      Tendsto (fun k : ℕ => M / (m (k + k₀)) ^ 2) atTop (𝓝 M) := by
    have hcont : ContinuousAt (fun r : ℝ => M / r ^ 2) 1 := by
      have hden : (1 : ℝ) ^ 2 ≠ 0 := by norm_num
      fun_prop
    have hfun : (fun k : ℕ => M / (m (k + k₀)) ^ 2) =
        (fun r : ℝ => M / r ^ 2) ∘ (fun k : ℕ => m (k + k₀)) := by
      funext k
      rfl
    have h := hcont.tendsto.comp hm_tendsto'
    rw [hfun]
    simpa using h
  have hbound_tendsto :
      Tendsto (fun k : ℕ => (M / (m (k + k₀)) ^ 2) ^ (p * (p + 1) / 2))
        atTop (𝓝 (M ^ (p * (p + 1) / 2))) := by
    exact (Real.continuousAt_rpow_const M (p * (p + 1) / 2) (Or.inr he)).tendsto.comp
      hbase_tendsto
  have hfatou :
      ∫⁻ ω, ENNReal.ofReal (F ω ^ (-p)) ∂disorderLaw ≤
        liminf (fun k : ℕ => ∫⁻ ω,
          ENNReal.ofReal (Qk (k + k₀) ω ^ (-p)) ∂disorderLaw) atTop := by
    have hmeas (k : ℕ) : AEMeasurable
        (fun ω => ENNReal.ofReal (Qk (k + k₀) ω ^ (-p))) disorderLaw := by
      exact (hQnegInt k).aemeasurable.ennreal_ofReal
    calc
      _ = ∫⁻ ω, liminf (fun k : ℕ =>
          ENNReal.ofReal (Qk (k + k₀) ω ^ (-p))) atTop ∂disorderLaw := by
        apply lintegral_congr_ae
        filter_upwards [hFpos, hFn_tendsto] with ω hFposω hFnω
        have hmn : Tendsto (fun k : ℕ => m (k + k₀)) atTop (𝓝 1) := hm_tendsto'
        have hQlimit : Tendsto (fun k : ℕ => Qk (k + k₀) ω) atTop (𝓝 (F ω)) := by
          have hEq : (fun k : ℕ => Qk (k + k₀) ω) =ᶠ[atTop]
              fun k => Fk (k + k₀) ω / m (k + k₀) := by
            filter_upwards [Filter.Eventually.of_forall hm_pos_all] with k hmk
            rw [hscale k (hm_pos_all k) ω]
            field_simp [ne_of_gt hmk]
          have hdiv := hFnω.div hmn (by norm_num : (1 : ℝ) ≠ 0)
          have hdiv' : Tendsto (fun k : ℕ => Fk (k + k₀) ω / m (k + k₀)) atTop
              (𝓝 (F ω)) := by
                convert hdiv using 1
                norm_num
          exact hdiv'.congr' hEq.symm
        have hQpower : Tendsto (fun k : ℕ => Qk (k + k₀) ω ^ (-p)) atTop
            (𝓝 (F ω ^ (-p))) := by
          by_cases hp0 : p = 0
          · subst p
            have hconst : (fun k : ℕ => Qk (k + k₀) ω ^ (-(0 : ℝ))) = fun _ => 1 := by
              funext k
              simp
            rw [hconst]
            simp
          · have hcont : ContinuousAt (fun x : ℝ => x ^ (-p)) (F ω) :=
              Real.continuousAt_rpow_const (F ω) (-p) (Or.inl (ne_of_gt hFposω))
            exact hcont.tendsto.comp hQlimit
        have hENN : Tendsto (fun k : ℕ => ENNReal.ofReal
            (Qk (k + k₀) ω ^ (-p))) atTop
            (𝓝 (ENNReal.ofReal (F ω ^ (-p)))) := by
          exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hQpower
        exact hENN.liminf_eq.symm
      _ ≤ liminf (fun k : ℕ => ∫⁻ ω,
          ENNReal.ofReal (Qk (k + k₀) ω ^ (-p)) ∂disorderLaw) atTop :=
        lintegral_liminf_le' hmeas
  have hQlin (k : ℕ) : ∫⁻ ω, ENNReal.ofReal (Qk (k + k₀) ω ^ (-p)) ∂disorderLaw =
      ENNReal.ofReal (∫ ω, Qk (k + k₀) ω ^ (-p) ∂disorderLaw) := by
    symm
    apply ofReal_integral_eq_lintegral_ofReal (hQnegInt k)
    filter_upwards [] with ω
    exact Real.rpow_nonneg (hQpos k ω).le _
  have hQlin_bound (k : ℕ) :
      ∫⁻ ω, ENNReal.ofReal (Qk (k + k₀) ω ^ (-p)) ∂disorderLaw ≤
        ENNReal.ofReal ((M / (m (k + k₀)) ^ 2) ^ (p * (p + 1) / 2)) := by
    rw [hQlin k]
    exact ENNReal.ofReal_le_ofReal (hQbound k)
  have hliminf_bound :
      liminf (fun k : ℕ => ∫⁻ ω,
        ENNReal.ofReal (Qk (k + k₀) ω ^ (-p)) ∂disorderLaw) atTop ≤
        ENNReal.ofReal (M ^ (p * (p + 1) / 2)) := by
    calc
      _ ≤ liminf (fun k : ℕ => ENNReal.ofReal
          ((M / (m (k + k₀)) ^ 2) ^ (p * (p + 1) / 2))) atTop :=
        liminf_le_liminf (Eventually.of_forall hQlin_bound)
      _ = _ := by
        have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbound_tendsto
        exact ht.liminf_eq
  have hFlin : ∫⁻ ω, ENNReal.ofReal (F ω ^ (-p)) ∂disorderLaw =
      ENNReal.ofReal (∫ ω, F ω ^ (-p) ∂disorderLaw) := by
    symm
    apply ofReal_integral_eq_lintegral_ofReal hFnegInt
    filter_upwards [hFpos] with ω hω
    exact Real.rpow_nonneg hω.le _
  have hfinal := hfatou.trans hliminf_bound
  rw [hFlin] at hfinal
  constructor
  · simpa only [F] using hFnegInt
  · dsimp [F, M] at hfinal ⊢
    exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hMnonneg _)).mp hfinal

end Critical2DKPZ.SHF.Positivity

end
