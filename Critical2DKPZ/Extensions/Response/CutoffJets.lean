/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.CutoffCalculus
public import Critical2DKPZ.Extensions.Response.JetLimit
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Tactic

/-! # Measurable cutoff jets

Derivatives are measurable limits of scalar difference quotients. Compact jet
versions are joined using the generic measurable gluing theorem.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology
namespace Critical2DKPZ.Extensions.Response

/-- Scalar parameter derivatives are almost everywhere measurable when every
evaluation is, and the sample functions are almost surely differentiable. -/
theorem aemeasurable_deriv_of_ae_differentiable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ → ℝ)
    (hf : ∀ q, AEMeasurable (fun ω => f ω q) P)
    (hd : ∀ᵐ ω ∂P, Differentiable ℝ (f ω)) (q : ℝ) :
    AEMeasurable (fun ω => deriv (f ω) q) P := by
  obtain ⟨s, hs⟩ := exists_seq_tendsto (𝓝[>] (0 : ℝ))
  apply aemeasurable_of_tendsto_metrizable_ae' (f := fun n ω =>
    (s n)⁻¹ • (f ω (q + s n) - f ω q))
  · intro n
    exact ((hf (q + s n)).sub (hf q)).const_smul (s n)⁻¹
  · filter_upwards [hd] with ω hω
    exact (hω q).hasDerivAt.tendsto_slope_zero_right.comp hs

/-- Countably many dense evaluations detect almost everywhere measurability of a
compact continuous map. The target is a separable Banach space. -/
theorem aemeasurable_compactContinuousMap_of_eval {Ω X : Type*} [MeasurableSpace Ω]
    [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [Nonempty X]
    (P : Measure Ω) (F : Ω → C(X, Fin 3 → ℝ))
    (hF : ∀ x, AEMeasurable (fun ω => F ω x) P) : AEMeasurable F P := by
  let d := TopologicalSpace.denseSeq X
  let ev : C(X, Fin 3 → ℝ) → ℕ → Fin 3 → ℝ := fun f n => f (d n)
  have hm : Measurable ev := measurable_pi_iff.mpr (fun n => ContinuousMap.measurable_eval (d n))
  have hi : Function.Injective ev := by
    intro f g hfg
    apply ContinuousMap.coe_injective
    apply (TopologicalSpace.denseRange_denseSeq X).equalizer f.continuous g.continuous
    exact hfg
  have he := hm.measurableEmbedding hi
  apply he.aemeasurable_comp_iff.mp
  exact aemeasurable_pi_iff.mpr (fun n => hF (d n))

/-- A scalar almost surely `C³` random function with measurable evaluations has
one measurable global continuous jet version. -/
theorem exists_measurable_continuousJet_version {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ → ℝ) (hf : ∀ q, AEMeasurable (fun ω => f ω q) P)
    (hc : ∀ᵐ ω ∂P, ContDiff ℝ 3 (f ω)) :
    ∃ R : Ω → C(ℝ, Fin 3 → ℝ), Measurable R ∧
      ∀ᵐ ω ∂P, ∀ q (j : Fin 3), R ω q j = iteratedDeriv (j : ℕ) (f ω) q := by
  classical
  have hd : ∀ᵐ ω ∂P, Differentiable ℝ (f ω) := hc.mono (fun _ h => h.differentiable (by norm_num))
  have hder := aemeasurable_deriv_of_ae_differentiable P f hf hd
  have hdd : ∀ᵐ ω ∂P, Differentiable ℝ (deriv (f ω)) := by
    filter_upwards [hc] with ω hω
    simpa only [iteratedDeriv_one] using hω.differentiable_iteratedDeriv 1 (by norm_num)
  have hder₂ := aemeasurable_deriv_of_ae_differentiable P (fun ω => deriv (f ω)) hder hdd
  have heval (q : ℝ) (j : Fin 3) : AEMeasurable (fun ω => iteratedDeriv (j : ℕ) (f ω) q) P := by
    fin_cases j
    · simpa only [iteratedDeriv_zero] using hf q
    · simpa only [iteratedDeriv_one] using hder q
    · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hder₂ q
  let raw (n : ℕ) : Ω → C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ) := fun ω =>
    ContinuousMap.mkD (fun q j => iteratedDeriv (j : ℕ) (f ω) q) 0
  have hraw (n : ℕ) : ∀ᵐ ω ∂P, ∀ (q : Set.Icc (-(n : ℝ)) (n : ℝ)) (j : Fin 3),
      raw n ω q j = iteratedDeriv (j : ℕ) (f ω) q := by
    filter_upwards [hc] with ω hω
    have hcont : Continuous (fun q : Set.Icc (-(n : ℝ)) (n : ℝ) =>
        fun j : Fin 3 => iteratedDeriv (j : ℕ) (f ω) q) := by
      apply continuous_pi
      intro j
      exact (hω.continuous_iteratedDeriv (j : ℕ) (by
        have hj := j.isLt
        norm_cast
        omega)).comp continuous_subtype_val
    intro q j
    simp only [raw, ContinuousMap.mkD_apply_of_continuous hcont]
  have hrawm (n : ℕ) : AEMeasurable (raw n) P := by
    let : Nonempty (Set.Icc (-(n : ℝ)) (n : ℝ)) :=
      ⟨⟨0, neg_nonpos.mpr (Nat.cast_nonneg n), Nat.cast_nonneg n⟩⟩
    apply aemeasurable_compactContinuousMap_of_eval P (raw n)
    intro q
    apply aemeasurable_pi_iff.mpr
    intro j
    exact (heval q j).congr ((hraw n).mono (fun _ hω => (hω q j).symm))
  let F (n : ℕ) : Ω → C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ) := (hrawm n).mk (raw n)
  have hFm (n : ℕ) : Measurable (F n) := (hrawm n).measurable_mk
  have hFid (n : ℕ) : ∀ᵐ ω ∂P, ∀ (q : Set.Icc (-(n : ℝ)) (n : ℝ)) (j : Fin 3),
      F n ω q j = iteratedDeriv (j : ℕ) (f ω) q := by
    filter_upwards [(hrawm n).ae_eq_mk, hraw n] with ω hω hrawω
    intro q j
    change (hrawm n).mk (raw n) ω q j = _
    rw [← hω]
    exact hrawω q j
  have hcompat (n m : ℕ) : ∀ᵐ ω ∂P,
      restrictJet (-(min n m : ℕ) : ℝ) (min n m : ℕ) (extendCompactJet n (F n ω)) =
        restrictJet (-(min n m : ℕ) : ℝ) (min n m : ℕ) (extendCompactJet m (F m ω)) := by
    filter_upwards [hFid n, hFid m] with ω hn hm
    ext q j
    have hqn := symmetricIcc_subset (Nat.min_le_left n m) q.property
    have hqm := symmetricIcc_subset (Nat.min_le_right n m) q.property
    change (F n ω) (Set.projIcc (-(n : ℝ)) (n : ℝ)
      (by linarith [Nat.cast_nonneg (α := ℝ) n]) q) j =
      (F m ω) (Set.projIcc (-(m : ℝ)) (m : ℝ)
      (by linarith [Nat.cast_nonneg (α := ℝ) m]) q) j
    rw [Set.projIcc_of_mem _ hqn, Set.projIcc_of_mem _ hqm]
    exact (hn ⟨q, hqn⟩ j).trans (hm ⟨q, hqm⟩ j).symm
  obtain ⟨R, hRm, hRcoh⟩ := exists_measurable_jet_of_compatible P F hFm hcompat
  refine ⟨R, hRm, ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, restrictJet (-(n : ℝ)) (n : ℝ) (R ω) = F n ω ∧
      ∀ (q : Set.Icc (-(n : ℝ)) (n : ℝ)) (j : Fin 3),
        F n ω q j = iteratedDeriv (j : ℕ) (f ω) q :=
    ae_all_iff.mpr (fun n => (hRcoh n).and (hFid n))
  filter_upwards [hall] with ω hω
  intro q j
  obtain ⟨n, hn⟩ := exists_nat_gt |q|
  let qn : Set.Icc (-(n : ℝ)) (n : ℝ) := ⟨q, abs_le.mp hn.le⟩
  have hh := congrArg (fun g : C(Set.Icc (-(n : ℝ)) (n : ℝ), Fin 3 → ℝ) => g qn j) (hω n).1
  exact hh.trans ((hω n).2 qn j)

/-- A continuous jet identified with the first three iterated derivatives inherits
the deterministic response bounds and the Lipschitz second component. -/
theorem jetData_of_iteratedDeriv (f : ℝ → ℝ) (J : C(ℝ, Fin 3 → ℝ)) (A M B : ℝ)
    (hc : ContDiff ℝ 3 f) (hJ : ∀ q (j : Fin 3), J q j = iteratedDeriv (j : ℕ) f q)
    (hb : ∀ q, |f q| ≤ A * M * |q| ∧ |deriv f q| ≤ A * M ∧ |iteratedDeriv 2 f q| ≤ A * M ^ 2)
    (hthird : ∀ q, |iteratedDeriv 3 f q| ≤ B) : JetData A M B J := by
  have hJ0 (q : ℝ) : J q 0 = f q := by simpa using hJ q 0
  have hJ1 (q : ℝ) : J q 1 = deriv f q := by simpa using hJ q 1
  have hJ2 (q : ℝ) : J q 2 = iteratedDeriv 2 f q := by simpa using hJ q 2
  have he0 : (fun q => J q 0) = f := by
    exact funext hJ0
  have he1 : (fun q => J q 1) = deriv f := by
    exact funext hJ1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    rw [he0, hJ1 q]
    exact (hc.differentiable (by norm_num) q).hasDerivAt
  · intro q
    rw [he1, hJ2 q]
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      (hc.differentiable_iteratedDeriv 1 (by norm_num) q).hasDerivAt
  · intro q q'
    rw [hJ2 q, hJ2 q']
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := iteratedDeriv 2 f)
      (fun u _ => hc.differentiable_iteratedDeriv 2 (by norm_num) u)
      (fun u _ => by simpa only [← iteratedDeriv_succ, Real.norm_eq_abs] using hthird u)
      (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ q') (Set.mem_univ q)
    simpa only [Real.norm_eq_abs] using hh
  · intro q
    rw [hJ0 q, hJ1 q, hJ2 q]
    exact hb q

/-- The zero continuous jet satisfies all nonnegative deterministic bounds. -/
theorem jetData_zero (A M B : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    JetData A M B (0 : C(ℝ, Fin 3 → ℝ)) := by
  refine ⟨fun q => hasDerivAt_const q 0, fun q => hasDerivAt_const q 0, ?_, ?_⟩
  · intro q q'
    change |(0 : ℝ) - 0| ≤ B * |q - q'|
    rw [sub_self, abs_zero]
    exact mul_nonneg hB (abs_nonneg _)
  · intro q
    change |(0 : ℝ)| ≤ A * M * |q| ∧ |(0 : ℝ)| ≤ A * M ∧ |(0 : ℝ)| ≤ A * M ^ 2
    simp only [abs_zero]
    exact ⟨by positivity, by positivity, by positivity⟩

/-- A measurable global cutoff jet, equal almost surely to the response and its
first two derivatives, with deterministic bounds for every realization. -/
theorem exists_cutoffJet (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t r : ℝ) (ht : 0 < t) (hr : 0 < r) (h v : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∃ J : Ω → C(ℝ, Fin 3 → ℝ), Measurable J ∧
      (∀ ω, JetData (∫ x, |ψ x|) ‖v‖ (8 * (∫ x, |ψ x|) * ‖v‖ ^ 3) (J ω)) ∧
      (∀ᵐ ω ∂P, ∀ (q : ℝ) (j : Fin 3),
        J ω q j = iteratedDeriv (j : ℕ) (responseCutoff Z t r h v ψ ω) q) ∧
      ((∀ x, 0 ≤ ψ x) → ∀ ω q, 0 ≤ J ω q 2) := by
  classical
  let A : ℝ := ∫ x, |ψ x|
  let M : ℝ := ‖v‖
  let B : ℝ := 8 * A * M ^ 3
  have hA : 0 ≤ A := integral_nonneg (fun x => abs_nonneg (ψ x))
  have hM : 0 ≤ M := norm_nonneg v
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcalc := responseCutoff_hasDerivAt ϑ P Z hZ t r ht hr h v ψ
  have hbounds := responseCutoff_bounds ϑ P Z hZ t r ht hr h v ψ
  obtain ⟨R, hRm, hRid⟩ := exists_measurable_continuousJet_version P
    (fun ω => responseCutoff Z t r h v ψ ω)
    (aemeasurable_responseCutoff ϑ P Z hZ ht hr h v ψ) (hcalc.mono (fun _ hω => hω.1))
  let S : Set Ω := {ω | JetData A M B (R ω) ∧ ((∀ x, 0 ≤ ψ x) → ∀ q, 0 ≤ R ω q 2)}
  have hgood : ∀ᵐ ω ∂P, ω ∈ S := by
    filter_upwards [hRid, hcalc, hbounds] with ω hid hc hb
    refine ⟨jetData_of_iteratedDeriv _ (R ω) A M B hc.1 hid
      (fun q => ⟨(hb q).1, (hb q).2.1, (hb q).2.2.1⟩)
      (fun q => (hc.2.1 q).2.2), ?_⟩
    intro hψ q
    have heq : R ω q 2 = iteratedDeriv 2 (responseCutoff Z t r h v ψ ω) q := by
      simpa using hid q 2
    rw [heq]
    exact (hb q).2.2.2 hψ
  let G : Set Ω := (toMeasurable P Sᶜ)ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P Sᶜ).compl
  have hGsub : G ⊆ S := by
    intro ω hω
    by_contra h
    exact hω (subset_toMeasurable P Sᶜ h)
  have hGfull : ∀ᵐ ω ∂P, ω ∈ G := by
    have hnull : P Sᶜ = 0 := ae_iff.mp hgood
    apply ae_iff.mpr
    change P (Gᶜ) = 0
    simpa only [G, compl_compl, measure_toMeasurable] using hnull
  let J : Ω → C(ℝ, Fin 3 → ℝ) := fun ω => if ω ∈ G then R ω else 0
  refine ⟨J, hRm.ite hGm measurable_const, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ G
    · simpa only [J, ite_eq_left hω] using (hGsub hω).1
    · simpa only [J, ite_eq_right hω] using jetData_zero A M B hA hM hB
  · filter_upwards [hGfull, hRid] with ω hω hid
    intro q j
    simpa only [J, ite_eq_left hω] using hid q j
  · intro hψ ω q
    by_cases hω : ω ∈ G
    · simpa only [J, ite_eq_left hω] using (hGsub hω).2 hψ q
    · simp only [J, ite_eq_right hω, ContinuousMap.coe_zero, Pi.zero_apply, le_refl]

/-- Compact cutoff jets in every finite `Lᵖ` space, simultaneously chosen for
all positive smoothing widths. -/
theorem exists_cutoffJet_Q (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (t : ℝ) (ht : 0 < t) (h v : Plane →ᵇ ℝ) (ψ : TestFn)
    (a b : ℝ) (_hab : a ≤ b) (p : ℝ≥0∞) (_hp1 : 1 ≤ p) (_hp : p ≠ ⊤) :
    ∃ Q : Set.Ioi (0 : ℝ) → Ω → C(Set.Icc a b, Fin 3 → ℝ),
      (∀ r, MemLp (Q r) p P) ∧
      ∀ r, ∀ᵐ ω ∂P, ∀ (q : Set.Icc a b) (j : Fin 3),
        Q r ω q j = iteratedDeriv (j : ℕ) (responseCutoff Z t r h v ψ ω) q := by
  have hex (r : Set.Ioi (0 : ℝ)) := exists_cutoffJet ϑ P Z hZ t r ht r.property h v ψ
  choose J hJm hJd hJeq _hJsign using hex
  refine ⟨fun r ω => restrictJet a b (J r ω), ?_, ?_⟩
  · intro r
    exact memLp_restrictJet P (J r) (∫ x, |ψ x|) ‖v‖ (8 * (∫ x, |ψ x|) * ‖v‖ ^ 3)
      (integral_nonneg (fun x => abs_nonneg (ψ x))) (norm_nonneg _) (hJm r)
      (Eventually.of_forall (hJd r)) a b p
  · intro r
    filter_upwards [hJeq r] with ω hω
    intro q j
    exact hω q j

end Critical2DKPZ.Extensions.Response
