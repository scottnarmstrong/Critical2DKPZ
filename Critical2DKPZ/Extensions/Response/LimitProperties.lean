/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.JetInstance
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! # Properties of compact-uniform jet limits

Norm comparison on nested intervals supplies almost sure compact convergence;
uniform limits preserve the exact derivative links and deterministic bounds.
-/

public section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Every coordinate error is at most the compact jet error. -/
theorem jet_coord_sub_le_norm_restrict (F G : C(ℝ, Fin 3 → ℝ)) (a b q : ℝ)
    (j : Fin 3) (hq : q ∈ Set.Icc a b) :
    |F q j - G q j| ≤ ‖restrictJet a b F - restrictJet a b G‖ := by
  have hcoord := norm_le_pi_norm (F q - G q) j
  have heval := (restrictJet a b F - restrictJet a b G).norm_coe_le_norm ⟨q, hq⟩
  exact hcoord.trans heval

/-- Compact jet errors decrease under restriction to smaller intervals. -/
theorem norm_restrictJet_sub_mono (F G : C(ℝ, Fin 3 → ℝ)) (a b c d : ℝ)
    (hsub : Set.Icc a b ⊆ Set.Icc c d) :
    ‖restrictJet a b F - restrictJet a b G‖ ≤ ‖restrictJet c d F - restrictJet c d G‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro q
  exact (restrictJet c d F - restrictJet c d G).norm_coe_le_norm ⟨q, hsub q.property⟩

/-- The same interval restriction comparison holds for the random compact `Lᵖ` norm. -/
theorem eLpNorm_restrictJet_sub_mono {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : ℝ≥0∞) (F G : Ω → C(ℝ, Fin 3 → ℝ))
    (hF : Measurable F) (hG : Measurable G) (a b c d : ℝ)
    (hsub : Set.Icc a b ⊆ Set.Icc c d) :
    eLpNorm (fun ω => restrictJet a b (F ω) - restrictJet a b (G ω)) p P ≤
      eLpNorm (fun ω => restrictJet c d (F ω) - restrictJet c d (G ω)) p P := by
  apply eLpNorm_mono_ae (((measurable_restrictJet F hF a b).sub
    (measurable_restrictJet G hG a b)).aestronglyMeasurable)
  exact Eventually.of_forall (fun ω => norm_restrictJet_sub_mono (F ω) (G ω) a b c d hsub)

/-- Compact convergence of jets implies convergence of every coordinate evaluation. -/
theorem tendsto_jet_eval {ι : Type*} (l : Filter ι) (F : ι → C(ℝ, Fin 3 → ℝ))
    (R : C(ℝ, Fin 3 → ℝ))
    (hconv : ∀ n : ℕ, Tendsto (fun i => restrictJet (-(n : ℝ)) (n : ℝ) (F i)) l
      (𝓝 (restrictJet (-(n : ℝ)) (n : ℝ) R))) (q : ℝ) (j : Fin 3) :
    Tendsto (fun i => F i q j) l (𝓝 (R q j)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt |q|
  let qn : Set.Icc (-(n : ℝ)) (n : ℝ) := ⟨q, abs_le.mp hn.le⟩
  have hc : Continuous (fun f : C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ) => f qn j) :=
    (continuous_apply j).comp (continuous_eval_const qn)
  exact hc.continuousAt.tendsto.comp (hconv n)

/-- Compact jet convergence gives uniform convergence of each coordinate on the
interior of the interval, as needed for passage of derivatives to the limit. -/
theorem tendstoUniformlyOn_jet_coord {ι : Type*} (l : Filter ι)
    (F : ι → C(ℝ, Fin 3 → ℝ)) (R : C(ℝ, Fin 3 → ℝ)) (n : ℕ)
    (hconv : Tendsto (fun i => restrictJet (-(n : ℝ)) (n : ℝ) (F i)) l
      (𝓝 (restrictJet (-(n : ℝ)) (n : ℝ) R))) (j : Fin 3) :
    TendstoUniformlyOn (fun i q => F i q j) (fun q => R q j) l
      (Set.Ioo (-(n : ℝ)) (n : ℝ)) := by
  have hn : Tendsto (fun i => ‖restrictJet (-(n : ℝ)) (n : ℝ) (F i) -
      restrictJet (-(n : ℝ)) (n : ℝ) R‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hconv.sub
      (tendsto_const_nhds : Tendsto (fun _ : ι => restrictJet (-(n : ℝ)) (n : ℝ) R) l
        (𝓝 (restrictJet (-(n : ℝ)) (n : ℝ) R)))).norm
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hn.eventually (Iio_mem_nhds hε)] with i hi
  intro q hq
  have hh := jet_coord_sub_le_norm_restrict (F i) R (-(n : ℝ)) (n : ℝ) q j ⟨hq.1.le, hq.2.le⟩
  simpa only [Real.dist_eq, abs_sub_comm] using hh.trans_lt hi

/-- Compact-uniform limits preserve `JetData`, including the derivative links. -/
theorem jetData_of_tendsto_compact {ι : Type*} (l : Filter ι) [NeBot l]
    (F : ι → C(ℝ, Fin 3 → ℝ)) (R : C(ℝ, Fin 3 → ℝ)) (A M B : ℝ)
    (hF : ∀ i, JetData A M B (F i))
    (hconv : ∀ n : ℕ, Tendsto (fun i => restrictJet (-(n : ℝ)) (n : ℝ) (F i)) l
      (𝓝 (restrictJet (-(n : ℝ)) (n : ℝ) R))) : JetData A M B R := by
  have hpt := tendsto_jet_eval l F R hconv
  have hlink (q : ℝ) (j : Fin 2) :
      HasDerivAt (fun u => R u j.castSucc) (R q j.succ) q := by
    obtain ⟨n, hn⟩ := exists_nat_gt |q|
    have hq := abs_lt.mp hn
    apply hasDerivAt_of_tendstoUniformlyOn
      (f := fun i u => F i u j.castSucc) (g := fun u => R u j.castSucc) isOpen_Ioo
      (tendstoUniformlyOn_jet_coord l F R n (hconv n) j.succ)
    · apply Eventually.of_forall
      intro i u _
      fin_cases j
      · exact (hF i).1 u
      · exact (hF i).2.1 u
    · exact fun u _ => hpt u j.castSucc
    · exact ⟨hq.1, hq.2⟩
  refine ⟨fun q => hlink q 0, fun q => hlink q 1, ?_, ?_⟩
  · intro q q'
    exact le_of_tendsto ((hpt q 2).sub (hpt q' 2)).abs
      (Eventually.of_forall (fun i => (hF i).2.2.1 q q'))
  · intro q
    exact ⟨le_of_tendsto (hpt q 0).abs (Eventually.of_forall (fun i => (hF i).2.2.2 q |>.1)),
      le_of_tendsto (hpt q 1).abs (Eventually.of_forall (fun i => (hF i).2.2.2 q |>.2.1)),
      le_of_tendsto (hpt q 2).abs (Eventually.of_forall (fun i => (hF i).2.2.2 q |>.2.2))⟩

/-- A summable choice of compact `L¹` errors gives one sequence converging almost
surely on every symmetric compact interval. -/
theorem exists_seq_ae_tendsto_jet {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (J : Set.Ioi (0 : ℝ) → Ω → C(ℝ, Fin 3 → ℝ))
    (R : Ω → C(ℝ, Fin 3 → ℝ)) (hJm : ∀ r, Measurable (J r)) (hRm : Measurable R)
    (hconv : ∀ n : ℕ, Tendsto (fun r => eLpNorm
      (fun ω => restrictJet (-(n : ℝ)) (n : ℝ) (J r ω) -
        restrictJet (-(n : ℝ)) (n : ℝ) (R ω)) 1 P) responseScaleFilter (𝓝 0)) :
    ∃ rk : ℕ → Set.Ioi (0 : ℝ), (∀ k, (rk k : ℝ) < 1 / ((k : ℝ) + 1)) ∧
      ∀ᵐ ω ∂P, ∀ n : ℕ, Tendsto (fun k => restrictJet (-(n : ℝ)) (n : ℝ) (J (rk k) ω))
        atTop (𝓝 (restrictJet (-(n : ℝ)) (n : ℝ) (R ω))) := by
  classical
  let ε : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  have hsum : Summable ε := summable_geometric_of_abs_lt_one (by norm_num)
  have hsumE : (∑' k, ENNReal.ofReal (ε k)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => (hε k).le) hsum]
    exact ENNReal.ofReal_ne_top
  have hex (k : ℕ) : ∃ r : Set.Ioi (0 : ℝ),
      (r : ℝ) < 1 / ((k : ℝ) + 1) ∧
      eLpNorm (fun ω => restrictJet (-(k : ℝ)) (k : ℝ) (J r ω) -
        restrictJet (-(k : ℝ)) (k : ℝ) (R ω)) 1 P < ENNReal.ofReal (ε k) :=
    ((eventually_lt_responseScaleFilter _ (by positivity)).and
      ((hconv k).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (hε k))))).exists
  choose rk hrk herr using hex
  let D (n k : ℕ) : Ω → C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ) := fun ω =>
    restrictJet (-(n : ℝ)) (n : ℝ) (J (rk k) ω) - restrictJet (-(n : ℝ)) (n : ℝ) (R ω)
  have hεshift (k n : ℕ) : ε (k + n) ≤ ε k := by
    dsimp [ε]
    rw [pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
  have hsumD (n : ℕ) : (∑' k, eLpNorm (D n (k + n)) 1 P) ≠ ∞ := by
    apply ne_top_of_le_ne_top hsumE
    apply ENNReal.tsum_le_tsum
    intro k
    have hmono := eLpNorm_restrictJet_sub_mono P 1 (J (rk (k + n))) R (hJm _) hRm
      (-(n : ℝ)) (n : ℝ) (-((k + n : ℕ) : ℝ)) (k + n : ℕ)
      (symmetricIcc_subset (by omega : n ≤ k + n))
    exact hmono.trans ((herr (k + n)).le.trans (ENNReal.ofReal_le_ofReal (hεshift k n)))
  have hae : ∀ᵐ ω ∂P, ∀ n : ℕ, Summable (fun k => ‖D n (k + n) ω‖) :=
    ae_all_iff.mpr (fun n => summable_norm_of_tsum_eLpNorm_ne_top le_rfl (hsumD n))
  refine ⟨rk, hrk, ?_⟩
  filter_upwards [hae] with ω hω
  intro n
  have hnorm : Tendsto (fun k => ‖D n k ω‖) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat (f := fun k => ‖D n k ω‖) n).mp (hω n).tendsto_atTop_zero
  have hz : Tendsto (fun k => D n k ω) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hh := hz.add (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => restrictJet (-(n : ℝ)) (n : ℝ) (R ω)) atTop
    (𝓝 (restrictJet (-(n : ℝ)) (n : ℝ) (R ω))))
  simpa only [D, sub_add_cancel, zero_add] using hh

/-- Almost sure compact-uniform convergence passes deterministic jet data and
any conditional nonnegative second-component property to the global limit. -/
theorem limit_jet_properties {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (J : Set.Ioi (0 : ℝ) → Ω → C(ℝ, Fin 3 → ℝ))
    (R : Ω → C(ℝ, Fin 3 → ℝ)) (A M B : ℝ) (C : Prop)
    (hJm : ∀ r, Measurable (J r)) (hRm : Measurable R)
    (hJd : ∀ r ω, JetData A M B (J r ω))
    (hJsign : C → ∀ r ω q, 0 ≤ J r ω q 2)
    (hconv : ∀ n : ℕ, Tendsto (fun r => eLpNorm
      (fun ω => restrictJet (-(n : ℝ)) (n : ℝ) (J r ω) -
        restrictJet (-(n : ℝ)) (n : ℝ) (R ω)) 1 P) responseScaleFilter (𝓝 0)) :
    ∀ᵐ ω ∂P, JetData A M B (R ω) ∧ (C → ∀ q, 0 ≤ R ω q 2) := by
  obtain ⟨rk, _hrk, hseq⟩ := exists_seq_ae_tendsto_jet P J R hJm hRm hconv
  filter_upwards [hseq] with ω hω
  have hd := jetData_of_tendsto_compact atTop (fun k => J (rk k) ω) (R ω) A M B
    (fun k => hJd (rk k) ω) hω
  refine ⟨hd, ?_⟩
  intro hC q
  exact ge_of_tendsto (tendsto_jet_eval atTop (fun k => J (rk k) ω) (R ω) hω q 2)
    (Eventually.of_forall (fun k => hJsign hC (rk k) ω q))

/-- A compact jet limit has the same fixed-parameter identification as any
probability limit of its zeroth evaluations. -/
theorem identification {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter ι) [NeBot l] [IsCountablyGenerated l]
    (J : ι → Ω → C(ℝ, Fin 3 → ℝ)) (R : Ω → C(ℝ, Fin 3 → ℝ))
    (hJm : ∀ i, Measurable (J i)) (hRm : Measurable R) (q : ℝ) (g : Ω → ℝ)
    (hconv : Tendsto (fun i => eLpNorm
      (fun ω => restrictJet q q (J i ω) - restrictJet q q (R ω)) 1 P) l (𝓝 0))
    (hg : TendstoInMeasure P (fun i ω => J i ω q 0) l g) :
    (fun ω => R ω q 0) =ᵐ[P] g := by
  have hnorm : Tendsto (fun i => eLpNorm (fun ω => J i ω q 0 - R ω q 0) 1 P) l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
      (fun _ => bot_le) (fun i => ?_)
    have hm : AEStronglyMeasurable (fun ω => J i ω q 0 - R ω q 0) P :=
      (((measurable_pi_apply 0).comp ((ContinuousMap.measurable_eval q).comp (hJm i))).sub
        ((measurable_pi_apply 0).comp ((ContinuousMap.measurable_eval q).comp hRm))).aestronglyMeasurable
    apply eLpNorm_mono_ae hm
    exact Eventually.of_forall (fun ω => jet_coord_sub_le_norm_restrict (J i ω) (R ω) q q q 0
      ⟨le_rfl, le_rfl⟩)
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero hnorm) hg

end Critical2DKPZ.Extensions.Response
