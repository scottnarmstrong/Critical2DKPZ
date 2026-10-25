/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Definitions.RestrictJet
public import Critical2DKPZ.Extensions.Response.FiniteDifference
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
# Compact uniform estimates for random jets

Finite nets reduce compact uniform control of equicontinuous scalar functions to
finitely many evaluations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Critical2DKPZ.Extensions.Response

/-- The deterministic bounds and derivative identities of a response jet. -/
def JetData (A M B : ℝ) (f : C(ℝ, Fin 3 → ℝ)) : Prop :=
  (∀ q, HasDerivAt (fun u => f u 0) (f q 1) q) ∧
  (∀ q, HasDerivAt (fun u => f u 1) (f q 2) q) ∧
  (∀ q q', |f q 2 - f q' 2| ≤ B * |q - q'|) ∧
  (∀ q, |f q 0| ≤ A * M * |q| ∧ |f q 1| ≤ A * M ∧ |f q 2| ≤ A * M ^ 2)


/-- Vector-valued version of the finite-net bound, with a sum over evaluations. -/
theorem finite_mesh_norm_le_sum {X E : Type*} [MetricSpace X] [CompactSpace X]
    [NormedAddCommGroup E] (f g : C(X, E)) (L η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hf : ∀ x y, ‖f x - f y‖ ≤ L * dist x y)
    (hg : ∀ x y, ‖g x - g y‖ ≤ L * dist x y)
    (mesh : Finset X) (hnet : ∀ x, ∃ y ∈ mesh, dist x y ≤ η) :
    ‖f - g‖ ≤ (∑ y ∈ mesh, ‖f y - g y‖) + 2 * L * η := by
  apply (ContinuousMap.norm_le (f - g) (by positivity)).mpr
  intro x
  obtain ⟨y, hy, hxy⟩ := hnet x
  have hfx := (hf x y).trans (mul_le_mul_of_nonneg_left hxy hL)
  have hgx := (hg x y).trans (mul_le_mul_of_nonneg_left hxy hL)
  have hyfg := Finset.single_le_sum (fun z (_ : z ∈ mesh) => norm_nonneg (f z - g z)) hy
  have ha := norm_add_le (f x - f y) (f y - g y)
  have hb := norm_sub_le (f x - f y + (f y - g y)) (g x - g y)
  have hid : f x - f y + (f y - g y) - (g x - g y) = f x - g x := by abel
  rw [hid] at hb
  change ‖f x - g x‖ ≤ _
  linarith only [hfx, hgx, hyfg, ha, hb]

/-- Restricting a measurable random continuous jet to a compact interval preserves
measurability. -/
theorem measurable_restrictJet {Ω : Type*} [MeasurableSpace Ω]
    (J : Ω → C(ℝ, Fin 3 → ℝ)) (hJ : Measurable J) (a b : ℝ) :
    Measurable (fun ω => restrictJet a b (J ω)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro q
  exact (ContinuousMap.measurable_eval (q : ℝ)).comp hJ

/-- The first component of a jet is uniformly Lipschitz. -/
theorem JetData.lipschitz_zero {A M B : ℝ} {f : C(ℝ, Fin 3 → ℝ)}
    (hf : JetData A M B f) (x y : ℝ) :
    |f x 0 - f y 0| ≤ A * M * |x - y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (fun q _ => (hf.1 q).hasDerivWithinAt)
    (fun q _ => show ‖f q 1‖ ≤ A * M from (hf.2.2.2 q).2.1)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- The derivative component of a jet is uniformly Lipschitz. -/
theorem JetData.lipschitz_one {A M B : ℝ} {f : C(ℝ, Fin 3 → ℝ)}
    (hf : JetData A M B f) (x y : ℝ) :
    |f x 1 - f y 1| ≤ A * M ^ 2 * |x - y| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (fun q _ => (hf.2.1 q).hasDerivWithinAt)
    (fun q _ => show ‖f q 2‖ ≤ A * M ^ 2 from (hf.2.2.2 q).2.2)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ y) (Set.mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- A common Lipschitz bound for all three coordinates of a deterministic jet. -/
theorem JetData.lipschitz {A M B : ℝ} {f : C(ℝ, Fin 3 → ℝ)}
    (hf : JetData A M B f) (hA : 0 ≤ A) (hM : 0 ≤ M) (hB : 0 ≤ B) (x y : ℝ) :
    ‖f x - f y‖ ≤ (A * M + A * M ^ 2 + B) * |x - y| := by
  have h0 : 0 ≤ A * M * |x - y| := by positivity
  have h1 : 0 ≤ A * M ^ 2 * |x - y| := by positivity
  have h2 : 0 ≤ B * |x - y| := by positivity
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  fin_cases k
  · change |f x 0 - f y 0| ≤ _
    exact (hf.lipschitz_zero x y).trans (by nlinarith only [h1, h2])
  · change |f x 1 - f y 1| ≤ _
    exact (hf.lipschitz_one x y).trans (by nlinarith only [h0, h2])
  · change |f x 2 - f y 2| ≤ _
    exact (hf.2.2.1 x y).trans (by nlinarith only [h0, h1])

/-- A symmetric eventual estimate is equivalent to convergence to zero along the
product filter. The real thresholds are convenient for applications in `Lᵖ`. -/
theorem tendsto_zero_prod_iff {ι : Type*} (l : Filter ι) (F : ι → ι → ℝ≥0∞) :
    Tendsto (fun ij : ι × ι => F ij.1 ij.2) (l ×ˢ l) (𝓝 0) ↔
      ∀ ε > (0 : ℝ), ∃ s ∈ l, ∀ i ∈ s, ∀ j ∈ s, F i j < ENNReal.ofReal ε := by
  constructor
  · intro h ε hε
    have he := h.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hε))
    obtain ⟨s, hs, t, ht, hst⟩ := Filter.eventually_prod_iff.mp he
    exact ⟨{i | s i ∧ t i}, inter_mem hs ht, fun i hi j hj => hst hi.1 hj.2⟩
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    obtain ⟨s, hs, hss⟩ := h δ (by exact_mod_cast hδ)
    apply Filter.eventually_prod_iff.mpr
    refine ⟨(· ∈ s), hs, (· ∈ s), hs, ?_⟩
    intro i hi j hj
    exact (hss i hi j hj).le.trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hδε.le)

/-- A finite-net estimate in `Lᵖ`, with the spatial supremum inside the random norm. -/
theorem eLpNorm_le_sum_evaluations_add {Ω X E : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompactSpace X] [NormedAddCommGroup E]
    (P : Measure Ω) [IsProbabilityMeasure P] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (F G : Ω → C(X, E)) (hF : AEStronglyMeasurable F P) (hG : AEStronglyMeasurable G P)
    (L η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hf : ∀ᵐ ω ∂P, ∀ x y, ‖F ω x - F ω y‖ ≤ L * dist x y)
    (hg : ∀ᵐ ω ∂P, ∀ x y, ‖G ω x - G ω y‖ ≤ L * dist x y)
    (mesh : Finset X) (hnet : ∀ x, ∃ y ∈ mesh, dist x y ≤ η) :
    eLpNorm (fun ω => F ω - G ω) p P ≤
      (∑ x ∈ mesh, eLpNorm (fun ω => F ω x - G ω x) p P) + ENNReal.ofReal (2 * L * η) := by
  let H : Ω → ℝ := fun ω => ∑ x ∈ mesh, ‖F ω x - G ω x‖
  have hmono : eLpNorm (fun ω => F ω - G ω) p P ≤
      eLpNorm (fun ω => H ω + 2 * L * η) p P := by
    apply eLpNorm_mono_ae_real (hF.sub hG)
    filter_upwards [hf, hg] with ω hωf hωg
    exact finite_mesh_norm_le_sum (F ω) (G ω) L η hL hη hωf hωg mesh hnet
  have hc : eLpNorm (fun _ : Ω => 2 * L * η) p P = ENNReal.ofReal (2 * L * η) := by
    rw [eLpNorm_const _ (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) (NeZero.ne P)]
    simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (by positivity : 0 ≤ 2 * L * η)]
  have hsum : eLpNorm H p P ≤ ∑ x ∈ mesh, eLpNorm (fun ω => F ω x - G ω x) p P := by
    have hh := eLpNorm_sum_le (μ := P) (s := mesh)
      (f := fun x ω => ‖F ω x - G ω x‖) hp
    have he (x : X) : AEStronglyMeasurable (fun ω => F ω x - G ω x) P :=
      ((continuous_eval_const x).comp_aestronglyMeasurable hF).sub
        ((continuous_eval_const x).comp_aestronglyMeasurable hG)
    have heq : (∑ x ∈ mesh, fun ω => ‖F ω x - G ω x‖) = H := by
      ext ω
      simp only [H, Finset.sum_apply]
    rw [heq] at hh
    simpa only [eLpNorm_norm _ (he _)] using hh
  calc
    _ ≤ eLpNorm (fun ω => H ω + 2 * L * η) p P := hmono
    _ ≤ eLpNorm H p P + eLpNorm (fun _ : Ω => 2 * L * η) p P := eLpNorm_add_le hp
    _ ≤ _ := by rw [hc]; exact add_le_add hsum le_rfl

/-- Uniform Lipschitz control upgrades evaluationwise `Lᵖ` Cauchyness to Cauchyness
in the compact continuous-function norm. -/
theorem uniform_cauchy_Lp_of_eval {Ω X E ι : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompactSpace X] [NormedAddCommGroup E]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter ι)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (F : ι → Ω → C(X, E))
    (hF : ∀ i, AEStronglyMeasurable (F i) P) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ i, ∀ᵐ ω ∂P, ∀ x y, ‖F i ω x - F i ω y‖ ≤ L * dist x y)
    (hpt : ∀ x, Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => F ij.1 ω x - F ij.2 ω x) p P) (l ×ˢ l) (𝓝 0)) :
    Tendsto (fun ij : ι × ι => eLpNorm (fun ω => F ij.1 ω - F ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0) := by
  apply (tendsto_zero_prod_iff l (fun i j => eLpNorm (fun ω => F i ω - F j ω) p P)).mpr
  intro ε hε
  obtain ⟨η, hη, hηerr⟩ := exists_pos_mul_lt (half_pos hε) (2 * L)
  obtain ⟨t, _, ht, hcover⟩ := finite_cover_balls_of_compact
    (isCompact_univ : IsCompact (Set.univ : Set X)) hη
  let mesh := ht.toFinset
  have hnet : ∀ x : X, ∃ y ∈ mesh, dist x y ≤ η := by
    intro x
    obtain ⟨y, hyt, hxy⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ x))
    exact ⟨y, ht.mem_toFinset.mpr hyt, (Metric.mem_ball.mp hxy).le⟩
  have hsum : Tendsto (fun ij : ι × ι => ∑ x ∈ mesh,
      eLpNorm (fun ω => F ij.1 ω x - F ij.2 ω x) p P) (l ×ˢ l) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum mesh (fun x _ => hpt x)
  have hevent := hsum.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hε)))
  obtain ⟨s, hs, u, hu, hsu⟩ := Filter.eventually_prod_iff.mp hevent
  refine ⟨{i | s i ∧ u i}, inter_mem hs hu, ?_⟩
  intro i hi j hj
  calc
    _ ≤ (∑ x ∈ mesh, eLpNorm (fun ω => F i ω x - F j ω x) p P) +
        ENNReal.ofReal (2 * L * η) :=
      eLpNorm_le_sum_evaluations_add P p hp (F i) (F j) (hF i) (hF j)
        L η hL hη.le (hLip i) (hLip j) mesh hnet
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add (hsu hi.1 hj.2)
        ((ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mpr hηerr)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      ring

/-- `Lᵖ` Cauchyness is stable under addition. -/
theorem tendsto_eLpNorm_sub_zero_add {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) (l : Filter ι) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (F G : ι → Ω → E)
    (hF : Tendsto (fun ij : ι × ι => eLpNorm (fun ω => F ij.1 ω - F ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0))
    (hG : Tendsto (fun ij : ι × ι => eLpNorm (fun ω => G ij.1 ω - G ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0)) :
    Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => (F ij.1 ω + G ij.1 ω) - (F ij.2 ω + G ij.2 ω)) p P)
      (l ×ˢ l) (𝓝 0) := by
  have hh := hF.add hG
  simp only [add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => bot_le) (fun ij => ?_)
  have heq : (fun ω => (F ij.1 ω + G ij.1 ω) - (F ij.2 ω + G ij.2 ω)) =
      (fun ω => F ij.1 ω - F ij.2 ω) + (fun ω => G ij.1 ω - G ij.2 ω) := by
    ext ω
    simp only [Pi.add_apply]
    abel
  rw [heq]
  exact eLpNorm_add_le hp

/-- `Lᵖ` Cauchyness is stable under multiplication by a fixed real scalar. -/
theorem tendsto_eLpNorm_sub_zero_smul {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω) (l : Filter ι) (p : ℝ≥0∞)
    (F : ι → Ω → E) (c : ℝ)
    (hF : Tendsto (fun ij : ι × ι => eLpNorm (fun ω => F ij.1 ω - F ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0)) :
    Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => c • F ij.1 ω - c • F ij.2 ω) p P) (l ×ˢ l) (𝓝 0) := by
  have hh := ENNReal.Tendsto.const_mul (a := ‖c‖ₑ) hF (Or.inr enorm_ne_top)
  simp only [mul_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ => bot_le) (fun ij => ?_)
  have heq : (fun ω => c • F ij.1 ω - c • F ij.2 ω) =
      c • (fun ω => F ij.1 ω - F ij.2 ω) := by
    ext ω
    simp only [Pi.smul_apply, smul_sub]
  rw [heq]
  exact eLpNorm_const_smul_le

open scoped ContDiff in
/-- Continuous jets satisfying `JetData` have a continuously twice differentiable
zeroth component. -/
theorem JetData.contDiff_zero {A M B : ℝ} {f : C(ℝ, Fin 3 → ℝ)}
    (hf : JetData A M B f) : ContDiff ℝ 2 (fun q => f q 0) := by
  have h0 : deriv (fun q => f q 0) = fun q => f q 1 := funext (fun q => (hf.1 q).deriv)
  have h1 : deriv (fun q => f q 1) = fun q => f q 2 := funext (fun q => (hf.2.1 q).deriv)
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiff_succ_iff_deriv, h0]
  refine ⟨fun q => (hf.1 q).differentiableAt, ?_, ?_⟩
  · intro h
    cases h
  · rw [contDiff_one_iff_deriv, h1]
    exact ⟨fun q => (hf.2.1 q).differentiableAt, (continuous_apply 2).comp f.continuous⟩

/-- The first forward difference approximates the derivative component of a jet. -/
theorem JetData.first_difference_error {A M B : ℝ} {f : C(ℝ, Fin 3 → ℝ)}
    (hf : JetData A M B f) (q ε : ℝ) (hε : 0 < ε) :
    |(f (q + ε) 0 - f q 0) / ε - f q 1| ≤ A * M ^ 2 * ε / 2 := by
  have h0 : deriv (fun q => f q 0) = fun q => f q 1 := funext (fun q => (hf.1 q).deriv)
  have h1 : iteratedDeriv 2 (fun q => f q 0) = fun q => f q 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, h0]
    exact funext (fun q => (hf.2.1 q).deriv)
  have hh := first_difference_error_le (fun q => f q 0) q ε (A * M ^ 2) hε hf.contDiff_zero
    (fun y _ => by rw [h1]; exact (hf.2.2.2 y).2.2)
  rw [h0] at hh
  have heq : (f (q + ε) 0 - f q 0) / ε - f q 1 =
      (f (q + ε) 0 - f q 0 - ε * f q 1) / ε := by field_simp
  rw [heq, abs_div, abs_of_pos hε]
  apply (div_le_iff₀ hε).mpr
  nlinarith only [hh]

/-- The second forward difference approximates the second component of a jet. -/
theorem JetData.second_difference_error {A M B : ℝ} {f : C(ℝ, Fin 3 → ℝ)}
    (hf : JetData A M B f) (q ε : ℝ) (hε : 0 < ε) :
    |(f (q + 2 * ε) 0 - 2 * f (q + ε) 0 + f q 0) / ε ^ 2 - f q 2| ≤ B * ε :=
  second_diff_quotient_error_le _ _ _ q ε B hε hf.1 hf.2.1 (fun y _ => hf.2.2.1 y q)

/-- `Lᵖ` Cauchyness is stable under subtraction. -/
theorem tendsto_eLpNorm_sub_zero_sub {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω) (l : Filter ι)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (F G : ι → Ω → E)
    (hF : Tendsto (fun ij : ι × ι => eLpNorm (fun ω => F ij.1 ω - F ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0))
    (hG : Tendsto (fun ij : ι × ι => eLpNorm (fun ω => G ij.1 ω - G ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0)) :
    Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => (F ij.1 ω - G ij.1 ω) - (F ij.2 ω - G ij.2 ω)) p P)
      (l ×ˢ l) (𝓝 0) := by
  have hneg := tendsto_eLpNorm_sub_zero_smul P l p G (-1) hG
  simpa only [neg_one_smul, sub_eq_add_neg] using
    tendsto_eLpNorm_sub_zero_add P l p hp F (fun i ω => (-1 : ℝ) • G i ω) hF hneg

/-- Uniformly accurate `Lᵖ`-Cauchy approximations imply `Lᵖ` Cauchyness. -/
theorem tendsto_eLpNorm_sub_zero_of_approx {Ω ι E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (P : Measure Ω) [IsProbabilityMeasure P]
    (l : Filter ι) (p : ℝ≥0∞) (hp : 1 ≤ p) (F : ι → Ω → E)
    (hF : ∀ i, AEStronglyMeasurable (F i) P)
    (happrox : ∀ δ > (0 : ℝ), ∃ G : ι → Ω → E,
      (∀ i, AEStronglyMeasurable (G i) P) ∧
      (∀ i, ∀ᵐ ω ∂P, ‖F i ω - G i ω‖ ≤ δ) ∧
      Tendsto (fun ij : ι × ι => eLpNorm (fun ω => G ij.1 ω - G ij.2 ω) p P)
        (l ×ˢ l) (𝓝 0)) :
    Tendsto (fun ij : ι × ι => eLpNorm (fun ω => F ij.1 ω - F ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0) := by
  apply (tendsto_zero_prod_iff l (fun i j => eLpNorm (fun ω => F i ω - F j ω) p P)).mpr
  intro ε hε
  obtain ⟨G, hG, hclose, hc⟩ := happrox (ε / 4) (by positivity)
  have hbound (i : ι) : eLpNorm (fun ω => F i ω - G i ω) p P ≤ ENNReal.ofReal (ε / 4) := by
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
      eLpNorm_le_of_ae_bound (f := fun ω => F i ω - G i ω) ((hF i).sub (hG i)) (hclose i)
  have hbound' (i : ι) : eLpNorm (fun ω => G i ω - F i ω) p P ≤ ENNReal.ofReal (ε / 4) := by
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
      eLpNorm_le_of_ae_bound (f := fun ω => G i ω - F i ω) ((hG i).sub (hF i))
        ((hclose i).mono (fun ω hω => by simpa only [norm_sub_rev] using hω))
  have hevent := hc.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity : 0 < ε / 3)))
  obtain ⟨s, hs, t, ht, hst⟩ := Filter.eventually_prod_iff.mp hevent
  refine ⟨{i | s i ∧ t i}, inter_mem hs ht, ?_⟩
  intro i hi j hj
  have hδ : ENNReal.ofReal (ε / 4) < ENNReal.ofReal (ε / 3) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < ε / 3)).mpr (by linarith)
  have heq : (fun ω => F i ω - F j ω) =
      ((fun ω => F i ω - G i ω) + (fun ω => G i ω - G j ω)) +
        (fun ω => G j ω - F j ω) := by ext ω; simp only [Pi.add_apply]; abel
  calc
    _ ≤ eLpNorm ((fun ω => F i ω - G i ω) + (fun ω => G i ω - G j ω)) p P +
        eLpNorm (fun ω => G j ω - F j ω) p P := by rw [heq]; exact eLpNorm_add_le hp
    _ ≤ (eLpNorm (fun ω => F i ω - G i ω) p P +
        eLpNorm (fun ω => G i ω - G j ω) p P) + eLpNorm (fun ω => G j ω - F j ω) p P :=
      add_le_add (eLpNorm_add_le hp) le_rfl
    _ ≤ (ENNReal.ofReal (ε / 4) + eLpNorm (fun ω => G i ω - G j ω) p P) +
        ENNReal.ofReal (ε / 4) := add_le_add (add_le_add (hbound i) le_rfl) (hbound' j)
    _ < (ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3)) + ENNReal.ofReal (ε / 3) :=
      ENNReal.add_lt_add (ENNReal.add_lt_add hδ (hst hi.1 hj.2)) hδ
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Evaluationwise `Lᵖ` Cauchyness of the zeroth component implies the same for
both derivative components of bounded deterministic jets. -/
theorem jet_coordinate_cauchy_Lp {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (l : Filter ι) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (J : ι → Ω → C(ℝ, Fin 3 → ℝ)) (A M B : ℝ)
    (hJm : ∀ i, Measurable (J i)) (hJd : ∀ i, ∀ᵐ ω ∂P, JetData A M B (J i ω))
    (hpt : ∀ q, Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => J ij.1 ω q 0 - J ij.2 ω q 0) p P) (l ×ˢ l) (𝓝 0)) :
    ∀ q k, Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => J ij.1 ω q k - J ij.2 ω q k) p P) (l ×ˢ l) (𝓝 0) := by
  have hm (i : ι) (q : ℝ) (k : Fin 3) : Measurable (fun ω => J i ω q k) :=
    (measurable_pi_apply k).comp ((ContinuousMap.measurable_eval q).comp (hJm i))
  intro q k
  fin_cases k
  · exact hpt q
  · apply tendsto_eLpNorm_sub_zero_of_approx P l p hp (fun i ω => J i ω q 1)
      (fun i => (hm i q 1).aestronglyMeasurable)
    intro δ hδ
    obtain ⟨ε, hε, hεδ⟩ := exists_pos_mul_lt hδ (A * M ^ 2 / 2)
    let G : ι → Ω → ℝ := fun i ω => (J i ω (q + ε) 0 - J i ω q 0) / ε
    refine ⟨G, fun i => (((hm i (q + ε) 0).sub (hm i q 0)).div_const ε).aestronglyMeasurable,
      ?_, ?_⟩
    · intro i
      filter_upwards [hJd i] with ω hω
      have hh := hω.first_difference_error q ε hε
      change |J i ω q 1 - (J i ω (q + ε) 0 - J i ω q 0) / ε| ≤ δ
      rw [abs_sub_comm]
      nlinarith only [hh, hεδ]
    · have hd := tendsto_eLpNorm_sub_zero_sub P l p hp
        (fun i ω => J i ω (q + ε) 0) (fun i ω => J i ω q 0) (hpt (q + ε)) (hpt q)
      have hs := tendsto_eLpNorm_sub_zero_smul P l p
        (fun i ω => J i ω (q + ε) 0 - J i ω q 0) ε⁻¹ hd
      simpa only [G, smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
  · apply tendsto_eLpNorm_sub_zero_of_approx P l p hp (fun i ω => J i ω q 2)
      (fun i => (hm i q 2).aestronglyMeasurable)
    intro δ hδ
    obtain ⟨ε, hε, hεδ⟩ := exists_pos_mul_lt hδ B
    let G : ι → Ω → ℝ := fun i ω =>
      (J i ω (q + 2 * ε) 0 - 2 * J i ω (q + ε) 0 + J i ω q 0) / ε ^ 2
    refine ⟨G, fun i => (((hm i (q + 2 * ε) 0).sub
      ((hm i (q + ε) 0).const_mul 2)).add (hm i q 0)).div_const (ε ^ 2)
        |>.aestronglyMeasurable, ?_, ?_⟩
    · intro i
      filter_upwards [hJd i] with ω hω
      have hh := hω.second_difference_error q ε hε
      change |J i ω q 2 - (J i ω (q + 2 * ε) 0 - 2 * J i ω (q + ε) 0 + J i ω q 0) / ε ^ 2| ≤ δ
      rw [abs_sub_comm]
      exact hh.trans hεδ.le
    · have htwice := tendsto_eLpNorm_sub_zero_smul P l p
        (fun i ω => J i ω (q + ε) 0) 2 (hpt (q + ε))
      have hsub := tendsto_eLpNorm_sub_zero_sub P l p hp
        (fun i ω => J i ω (q + 2 * ε) 0) (fun i ω => (2 : ℝ) • J i ω (q + ε) 0)
        (hpt (q + 2 * ε)) htwice
      have hadd := tendsto_eLpNorm_sub_zero_add P l p hp
        (fun i ω => J i ω (q + 2 * ε) 0 - (2 : ℝ) • J i ω (q + ε) 0)
        (fun i ω => J i ω q 0) hsub (hpt q)
      have hs := tendsto_eLpNorm_sub_zero_smul P l p
        (fun i ω => J i ω (q + 2 * ε) 0 - (2 : ℝ) • J i ω (q + ε) 0 + J i ω q 0)
        (ε ^ 2)⁻¹ hadd
      simpa only [G, smul_eq_mul, div_eq_mul_inv, mul_comm] using hs

/-- For finitely many coordinates, coordinatewise `Lᵖ` Cauchyness implies vector
`Lᵖ` Cauchyness. -/
theorem tendsto_eLpNorm_sub_zero_pi {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (P : Measure Ω) (l : Filter ι) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (F : ι → Ω → κ → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) P)
    (hpt : ∀ k, Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => F ij.1 ω k - F ij.2 ω k) p P) (l ×ˢ l) (𝓝 0)) :
    Tendsto (fun ij : ι × ι => eLpNorm (fun ω => F ij.1 ω - F ij.2 ω) p P)
      (l ×ˢ l) (𝓝 0) := by
  classical
  have hsum : Tendsto (fun ij : ι × ι => ∑ k : κ,
      eLpNorm (fun ω => F ij.1 ω k - F ij.2 ω k) p P) (l ×ˢ l) (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun k _ => hpt k)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun ij => ?_)
  have hm (k : κ) : AEStronglyMeasurable (fun ω => F ij.1 ω k - F ij.2 ω k) P :=
    ((continuous_apply k).comp_aestronglyMeasurable (hF ij.1)).sub
      ((continuous_apply k).comp_aestronglyMeasurable (hF ij.2))
  let H : Ω → ℝ := fun ω => ∑ k : κ, ‖F ij.1 ω k - F ij.2 ω k‖
  have hmono : eLpNorm (fun ω => F ij.1 ω - F ij.2 ω) p P ≤ eLpNorm H p P := by
    apply eLpNorm_mono_ae_real ((hF ij.1).sub (hF ij.2))
    filter_upwards [] with ω
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
    intro k
    exact Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => norm_nonneg
      (F ij.1 ω j - F ij.2 ω j)) (Finset.mem_univ k)
  have hh := eLpNorm_sum_le (μ := P) (s := Finset.univ)
    (f := fun k ω => ‖F ij.1 ω k - F ij.2 ω k‖) hp
  have heq : (∑ k : κ, fun ω => ‖F ij.1 ω k - F ij.2 ω k‖) = H := by
    ext ω
    simp only [H, Finset.sum_apply]
  rw [heq] at hh
  exact hmono.trans (by simpa only [eLpNorm_norm _ (hm _)] using hh)

/-- Fixed-parameter Cauchyness of the zeroth component implies `Lᵖ` Cauchyness
of compact continuous jets, with the spatial supremum inside the random norm. -/
theorem jet_cauchy_Lp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type*} (l : Filter ι)
    (J : ι → Ω → C(ℝ, Fin 3 → ℝ)) (A M B : ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hJm : ∀ i, Measurable (J i)) (hJd : ∀ i, ∀ᵐ ω ∂P, JetData A M B (J i ω))
    (hpt : ∀ (q : ℝ) (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      ∀ ε > (0 : ℝ), ∃ s ∈ l, ∀ i ∈ s, ∀ j ∈ s,
        eLpNorm (fun ω => J i ω q 0 - J j ω q 0) p P < ENNReal.ofReal ε) :
    ∀ (a b : ℝ), a ≤ b → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      ∀ ε > (0 : ℝ), ∃ s ∈ l, ∀ i ∈ s, ∀ j ∈ s,
        eLpNorm (fun ω => restrictJet a b (J i ω) - restrictJet a b (J j ω)) p P <
          ENNReal.ofReal ε := by
  intro a b _hab p hp hp_top
  apply (tendsto_zero_prod_iff l
    (fun i j => eLpNorm (fun ω => restrictJet a b (J i ω) - restrictJet a b (J j ω)) p P)).mp
  have hpt' (q : ℝ) : Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => J ij.1 ω q 0 - J ij.2 ω q 0) p P) (l ×ˢ l) (𝓝 0) :=
    (tendsto_zero_prod_iff l _).mpr (hpt q p hp hp_top)
  have hcoords := jet_coordinate_cauchy_Lp P l p hp J A M B hJm hJd hpt'
  have hvec (q : ℝ) : Tendsto (fun ij : ι × ι => eLpNorm
      (fun ω => J ij.1 ω q - J ij.2 ω q) p P) (l ×ˢ l) (𝓝 0) :=
    tendsto_eLpNorm_sub_zero_pi P l p hp (fun i ω => J i ω q)
      (fun i => ((ContinuousMap.measurable_eval q).comp (hJm i)).aestronglyMeasurable) (hcoords q)
  apply uniform_cauchy_Lp_of_eval P l p hp (fun i ω => restrictJet a b (J i ω))
    (fun i => (measurable_restrictJet (J i) (hJm i) a b).aestronglyMeasurable)
    (A * M + A * M ^ 2 + B) (by positivity)
  · intro i
    filter_upwards [hJd i] with ω hω
    intro x y
    simpa only [restrictJet, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      Subtype.dist_eq, Real.dist_eq] using hω.lipschitz hA hM hB x y
  · intro q
    exact hvec q

/-- A deterministic compact-interval bound for a response jet. -/
theorem JetData.norm_restrictJet_le {A M B : ℝ} {f : C(ℝ, Fin 3 → ℝ)}
    (hf : JetData A M B f) (hA : 0 ≤ A) (hM : 0 ≤ M) (a b : ℝ) :
    ‖restrictJet a b f‖ ≤ A * M * max |a| |b| + A * M + A * M ^ 2 := by
  have hK : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
  have h0 : 0 ≤ A * M * max |a| |b| := by positivity
  have h1 : 0 ≤ A * M := by positivity
  have h2 : 0 ≤ A * M ^ 2 := by positivity
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro q
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  have hq : |(q : ℝ)| ≤ max |a| |b| := abs_le_max_abs_abs q.property.1 q.property.2
  have hb0 := (hf.2.2.2 q).1.trans (mul_le_mul_of_nonneg_left hq h1)
  have hb1 := (hf.2.2.2 q).2.1
  have hb2 := (hf.2.2.2 q).2.2
  fin_cases k
  · change |f q 0| ≤ _
    linarith only [hb0, h1, h2]
  · change |f q 1| ≤ _
    linarith only [hb1, h0, h2]
  · change |f q 2| ≤ _
    linarith only [hb2, h0, h1]

/-- Every compact restriction of a measurable random jet with deterministic bounds
belongs to every finite-measure `Lᵖ` space. -/
theorem memLp_restrictJet {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (J : Ω → C(ℝ, Fin 3 → ℝ)) (A M B : ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hJm : Measurable J)
    (hJd : ∀ᵐ ω ∂P, JetData A M B (J ω)) (a b : ℝ) (p : ℝ≥0∞) :
    MemLp (fun ω => restrictJet a b (J ω)) p P := by
  exact MemLp.of_bound (measurable_restrictJet J hJm a b).aestronglyMeasurable
    (A * M * max |a| |b| + A * M + A * M ^ 2)
    (hJd.mono (fun ω hω => hω.norm_restrictJet_le hA hM a b))

end Critical2DKPZ.Extensions.Response
