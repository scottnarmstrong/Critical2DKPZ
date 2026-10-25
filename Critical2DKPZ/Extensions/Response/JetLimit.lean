/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.JetCauchy
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-!
# Completeness for random continuous jets

Banach-valued `Lᵖ` completeness supplies compact-interval limits.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Critical2DKPZ.Extensions.Response

/-- A Cauchy family of Banach-valued random variables has a measurable `Lᵖ` limit.
No countable-generation condition on the parameter filter is needed for this step. -/
theorem exists_measurable_Lp_limit {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) (l : Filter ι) [NeBot l] (p : ℝ≥0∞) (hp : 1 ≤ p)
    (F : ι → Ω → E) (hF : ∀ i, MemLp (F i) p P)
    (hc : ∀ ε > (0 : ℝ), ∃ s ∈ l, ∀ i ∈ s, ∀ j ∈ s,
      eLpNorm (fun ω => F i ω - F j ω) p P < ENNReal.ofReal ε) :
    ∃ R : Ω → E, Measurable R ∧ MemLp R p P ∧
      Tendsto (fun i => eLpNorm (fun ω => F i ω - R ω) p P) l (𝓝 0) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let U : ι → Lp E p P := fun i => (hF i).toLp (F i)
  have hU : Cauchy (Filter.map U l) := by
    apply EMetric.cauchy_iff.mpr
    refine ⟨neBot_iff.mp inferInstance, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    obtain ⟨s, hs, hss⟩ := hc δ (by exact_mod_cast hδ)
    refine ⟨U '' s, Filter.image_mem_map hs, ?_⟩
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    have hh := hss i hi j hj
    rw [Lp.edist_toLp_toLp]
    exact hh.trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hδε)
  obtain ⟨R, hR⟩ := cauchy_map_iff_exists_tendsto.mp hU
  refine ⟨R, (Lp.stronglyMeasurable R).measurable, Lp.memLp R, ?_⟩
  have hh := (continuous_edist.tendsto (R, R)).comp (hR.prodMk_nhds tendsto_const_nhds)
  simp only [edist_self] at hh
  have heq : (fun i => eLpNorm (fun ω => F i ω - R ω) p P) =
      (fun i => edist (U i) R) := by
    funext i
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae ((hF i).coeFn_toLp.symm.sub Filter.EventuallyEq.rfl)
  rw [heq]
  exact hh

/-- Extend a jet on `[-n,n]` by clamping its argument to that interval. -/
@[expose] def extendCompactJet (n : ℕ)
    (f : C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ)) : C(ℝ, Fin 3 → ℝ) :=
  f.comp ⟨Set.projIcc (-(n : ℝ)) (n : ℝ) (by linarith [Nat.cast_nonneg (α := ℝ) n]),
    continuous_projIcc⟩

/-- Clamping leaves values on the original interval unchanged. -/
theorem extendCompactJet_apply (n : ℕ)
    (f : C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ))
    (q : Set.Icc (-(n : ℝ)) (n : ℝ)) : extendCompactJet n f q = f q := by
  simp only [extendCompactJet, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Set.projIcc_of_mem (by linarith [Nat.cast_nonneg (α := ℝ) n]) q.property]

/-- Clamping extension preserves measurability of random compact jets. -/
theorem measurable_extendCompactJet {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (F : Ω → C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ)) (hF : Measurable F) :
    Measurable (fun ω => extendCompactJet n (F ω)) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro q
  exact (ContinuousMap.measurable_eval (Set.projIcc (-(n : ℝ)) (n : ℝ)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) q)).comp hF

/-- Almost surely compatible compact jets have a measurable global continuous
version. Compatibility is an equality on each pairwise overlap. -/
theorem exists_measurable_jet_of_compatible {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : ∀ n : ℕ, Ω → C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ))
    (hF : ∀ n, Measurable (F n))
    (hcoh : ∀ n m : ℕ, ∀ᵐ ω ∂P,
      restrictJet (-(min n m : ℕ) : ℝ) (min n m : ℕ)
          (extendCompactJet n (F n ω)) =
        restrictJet (-(min n m : ℕ) : ℝ) (min n m : ℕ)
          (extendCompactJet m (F m ω))) :
    ∃ R : Ω → C(ℝ, Fin 3 → ℝ), Measurable R ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, restrictJet (-(n : ℝ)) (n : ℝ) (R ω) = F n ω := by
  classical
  let Good : Ω → Prop := fun ω => ∀ n m : ℕ,
    restrictJet (-(min n m : ℕ) : ℝ) (min n m : ℕ) (extendCompactJet n (F n ω)) =
      restrictJet (-(min n m : ℕ) : ℝ) (min n m : ℕ) (extendCompactJet m (F m ω))
  have hGood : MeasurableSet {ω | Good ω} := by
    simp only [Good, Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro n
    apply MeasurableSet.iInter
    intro m
    exact measurableSet_eq_fun
      (measurable_restrictJet _ (measurable_extendCompactJet n (F n) (hF n)) _ _)
      (measurable_restrictJet _ (measurable_extendCompactJet m (F m) (hF m)) _ _)
  have hGoodAE : ∀ᵐ ω ∂P, Good ω := by
    exact (ae_all_iff.mpr (fun n => ae_all_iff.mpr (hcoh n)))
  have hcompat (ω : Ω) (hω : Good ω) (n m : ℕ) (q : ℝ)
      (hqn : q ∈ Set.Icc (-(n : ℝ)) (n : ℝ))
      (hqm : q ∈ Set.Icc (-(m : ℝ)) (m : ℝ)) :
      extendCompactJet n (F n ω) q = extendCompactJet m (F m ω) q := by
    have hq : |q| ≤ (min n m : ℕ) := by
      rw [Nat.cast_min]
      exact le_min (abs_le.mpr hqn) (abs_le.mpr hqm)
    exact congrArg (fun f : C(Set.Icc (-(min n m : ℕ) : ℝ) (min n m : ℕ), Fin 3 → ℝ) =>
      f ⟨q, abs_le.mp hq⟩) (hω n m)
  choose N hN using (fun q : ℝ => exists_nat_gt |q|)
  let raw : Ω → ℝ → Fin 3 → ℝ := fun ω q => extendCompactJet (N q) (F (N q) ω) q
  have hcont (ω : Ω) (hω : Good ω) : Continuous (raw ω) := by
    rw [continuous_iff_continuousAt]
    intro q
    have hq := abs_lt.mp (hN q)
    apply (extendCompactJet (N q) (F (N q) ω)).continuous.continuousAt.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hq.1 hq.2] with u hu
    exact hcompat ω hω (N u) (N q) u (abs_le.mp (hN u).le) ⟨hu.1.le, hu.2.le⟩
  let R : Ω → C(ℝ, Fin 3 → ℝ) := fun ω =>
    if hω : Good ω then ⟨raw ω, hcont ω hω⟩ else 0
  refine ⟨R, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro q
    have heq : (fun ω => R ω q) = fun ω => if Good ω then raw ω q else 0 := by
      funext ω
      dsimp [R]
      split_ifs <;> rfl
    rw [heq]
    exact (((ContinuousMap.measurable_eval q).comp
      (measurable_extendCompactJet (N q) (F (N q)) (hF (N q)))).ite hGood measurable_const)
  · intro n
    filter_upwards [hGoodAE] with ω hω
    ext q k
    have hh := hcompat ω hω (N q) n q (abs_le.mp (hN q).le) q.property
    have hR : R ω q = raw ω q := by simp only [R, dite_eq_left hω, ContinuousMap.coe_mk]
    change R ω q k = F n ω q k
    rw [hR]
    change extendCompactJet (N q) (F (N q) ω) q k = F n ω q k
    rw [hh, extendCompactJet_apply]

/-- Restricting clamped extensions is a contraction for compact uniform norms. -/
theorem norm_restrict_extend_sub_le (a b : ℝ) (n : ℕ)
    (f g : C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ)) :
    ‖restrictJet a b (extendCompactJet n f) - restrictJet a b (extendCompactJet n g)‖ ≤
      ‖f - g‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg (f - g))).mpr
  intro q
  exact (f - g).norm_coe_le_norm (Set.projIcc (-(n : ℝ)) (n : ℝ)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) q)

/-- Restriction after clamping agrees with ordinary restriction inside the original interval. -/
theorem restrict_extend_restrictJet (a b : ℝ) (n : ℕ)
    (hsub : Set.Icc a b ⊆ Set.Icc (-(n : ℝ)) (n : ℝ))
    (f : C(ℝ, Fin 3 → ℝ)) :
    restrictJet a b (extendCompactJet n (restrictJet (-(n : ℝ)) (n : ℝ) f)) =
      restrictJet a b f := by
  ext q k
  simp only [restrictJet, extendCompactJet, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    Set.projIcc_of_mem (by linarith [Nat.cast_nonneg (α := ℝ) n]) (hsub q.property)]

/-- A compact `Lᵖ` limit also controls every smaller interval after clamping extension. -/
theorem tendsto_restrictJet_of_tendsto_compact {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter ι) (p : ℝ≥0∞)
    (J : ι → Ω → C(ℝ, Fin 3 → ℝ)) (hJ : ∀ i, Measurable (J i))
    (n : ℕ) (F : Ω → C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ)) (hF : Measurable F)
    (a b : ℝ) (hsub : Set.Icc a b ⊆ Set.Icc (-(n : ℝ)) (n : ℝ))
    (hconv : Tendsto (fun i => eLpNorm
      (fun ω => restrictJet (-(n : ℝ)) (n : ℝ) (J i ω) - F ω) p P) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (fun ω => restrictJet a b (J i ω) -
      restrictJet a b (extendCompactJet n (F ω))) p P) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ => bot_le) (fun i => ?_)
  apply eLpNorm_mono_ae
    (((measurable_restrictJet (J i) (hJ i) a b).sub
      (measurable_restrictJet _ (measurable_extendCompactJet n F hF) a b)).aestronglyMeasurable)
  filter_upwards [] with ω
  have hh := norm_restrict_extend_sub_le a b n
    (restrictJet (-(n : ℝ)) (n : ℝ) (J i ω)) (F ω)
  rw [restrict_extend_restrictJet a b n hsub] at hh
  exact hh

/-- Inclusion of two symmetric compact intervals. -/
theorem symmetricIcc_subset {n m : ℕ} (hnm : n ≤ m) :
    Set.Icc (-(n : ℝ)) (n : ℝ) ⊆ Set.Icc (-(m : ℝ)) (m : ℝ) := by
  have hh : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  exact Set.Icc_subset_Icc (neg_le_neg hh) hh

/-- Compact `Lᵖ` Cauchyness of bounded random jets supplies a single measurable
global continuous jet, with convergence on every compact interval and for every
finite exponent. Countable generation is used only for uniqueness in measure. -/
theorem exists_jet_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ι : Type*} (l : Filter ι)
    [NeBot l] [IsCountablyGenerated l]
    (J : ι → Ω → C(ℝ, Fin 3 → ℝ)) (A M B : ℝ)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (_hB : 0 ≤ B)
    (hJm : ∀ i, Measurable (J i)) (hJd : ∀ i, ∀ᵐ ω ∂P, JetData A M B (J i ω))
    (hcauchy : ∀ (a b : ℝ), a ≤ b → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
      ∀ ε > (0 : ℝ), ∃ s ∈ l, ∀ i ∈ s, ∀ j ∈ s,
        eLpNorm (fun ω => restrictJet a b (J i ω) - restrictJet a b (J j ω)) p P <
          ENNReal.ofReal ε) :
    ∃ R : Ω → C(ℝ, Fin 3 → ℝ), Measurable R ∧
      ∀ a b : ℝ, a ≤ b → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
        MemLp (fun ω => restrictJet a b (R ω)) p P ∧
        Tendsto (fun i => eLpNorm (fun ω => restrictJet a b (J i ω) -
          restrictJet a b (R ω)) p P) l (𝓝 0) := by
  have hmem (i : ι) (a b : ℝ) (p : ℝ≥0∞) :
      MemLp (fun ω => restrictJet a b (J i ω)) p P :=
    memLp_restrictJet P (J i) A M B hA hM (hJm i) (hJd i) a b p
  have hex (n : ℕ) :
      ∃ F : Ω → C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ),
        Measurable F ∧ MemLp F 1 P ∧
        Tendsto (fun i => eLpNorm
          (fun ω => restrictJet (-(n : ℝ)) (n : ℝ) (J i ω) - F ω) 1 P) l (𝓝 0) :=
    exists_measurable_Lp_limit P l 1 le_rfl
      (fun i ω => restrictJet (-(n : ℝ)) (n : ℝ) (J i ω))
      (fun i => hmem i _ _ _)
      (hcauchy _ _ (by linarith [Nat.cast_nonneg (α := ℝ) n]) 1 le_rfl (by norm_num))
  choose F hFm _hFlp hFconv using hex
  have hcoh (n m : ℕ) : ∀ᵐ ω ∂P,
      restrictJet (-(min n m : ℕ) : ℝ) (min n m : ℕ) (extendCompactJet n (F n ω)) =
        restrictJet (-(min n m : ℕ) : ℝ) (min n m : ℕ) (extendCompactJet m (F m ω)) := by
    have hcn := tendsto_restrictJet_of_tendsto_compact P l 1 J hJm n (F n) (hFm n)
      (-(min n m : ℕ) : ℝ) (min n m : ℕ)
      (symmetricIcc_subset (Nat.min_le_left n m)) (hFconv n)
    have hcm := tendsto_restrictJet_of_tendsto_compact P l 1 J hJm m (F m) (hFm m)
      (-(min n m : ℕ) : ℝ) (min n m : ℕ)
      (symmetricIcc_subset (Nat.min_le_right n m)) (hFconv m)
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero hcn)
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero hcm)
  obtain ⟨R, hRm, hRcoh⟩ := exists_measurable_jet_of_compatible P F hFm hcoh
  have hRconv (a b : ℝ) : Tendsto (fun i => eLpNorm
      (fun ω => restrictJet a b (J i ω) - restrictJet a b (R ω)) 1 P) l (𝓝 0) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (max |a| |b|)
    have hsub : Set.Icc a b ⊆ Set.Icc (-(n : ℝ)) (n : ℝ) := by
      intro q hq
      exact abs_le.mp ((abs_le_max_abs_abs hq.1 hq.2).trans hn.le)
    have hconv := tendsto_restrictJet_of_tendsto_compact P l 1 J hJm n (F n) (hFm n)
      a b hsub (hFconv n)
    have heq : (fun ω => restrictJet a b (R ω)) =ᵐ[P]
        (fun ω => restrictJet a b (extendCompactJet n (F n ω))) := by
      filter_upwards [hRcoh n] with ω hω
      rw [← hω, restrict_extend_restrictJet a b n hsub]
    convert hconv using 1
    funext i
    exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub heq)
  refine ⟨R, hRm, ?_⟩
  intro a b hab p hp hp_top
  obtain ⟨S, _hSm, hSlp, hSconv⟩ := exists_measurable_Lp_limit P l p hp
    (fun i ω => restrictJet a b (J i ω)) (fun i => hmem i a b p)
    (hcauchy a b hab p hp hp_top)
  have heq : (fun ω => restrictJet a b (R ω)) =ᵐ[P] S :=
    tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero (hRconv a b))
      (tendstoInMeasure_of_tendsto_eLpNorm (p := p)
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)) hSconv)
  refine ⟨hSlp.ae_eq heq.symm, ?_⟩
  convert hSconv using 1
  funext i
  exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub heq)

end Critical2DKPZ.Extensions.Response
