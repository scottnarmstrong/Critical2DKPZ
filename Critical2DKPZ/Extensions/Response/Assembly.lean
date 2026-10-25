/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Response.FixedQ
public import Critical2DKPZ.Extensions.Response.LimitProperties
public import Critical2DKPZ.Extensions.Response.Uniqueness
import Mathlib.Tactic

/-! # Assembly of the initial-response theorem in the continuous jet space -/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.Extensions.Response

/-- The complete response theorem, assembled from the cutoff jets and fixed-parameter limit. -/
theorem initialResponse_existsUnique_core (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (h v : Plane →ᵇ ℝ) (ψ : TestFn) :
    ∃! R : Ω →ₘ[P] C(ℝ, Fin 3 → ℝ),
      (∀ q : ℝ, (fun ω => R ω q 0) =ᵐ[P]
        (fun ω => H t (h + q • v) ω ψ - H t h ω ψ)) ∧
      (∀ᵐ ω ∂P, ∀ q : ℝ,
        HasDerivAt (fun u => R ω u 0) (R ω q 1) q ∧
        HasDerivAt (fun u => R ω u 1) (R ω q 2) q ∧
        |R ω q 0| ≤ (∫ x, |ψ x|) * ‖v‖ * |q| ∧
        |R ω q 1| ≤ (∫ x, |ψ x|) * ‖v‖ ∧
        |R ω q 2| ≤ (∫ x, |ψ x|) * ‖v‖ ^ 2 ∧
        ((∀ x, 0 ≤ ψ x) → 0 ≤ R ω q 2)) ∧
      (∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P,
        ContDiff ℝ 3 (responseCutoff Z t r h v ψ ω)) ∧
      (∀ (a b : ℝ), a ≤ b → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ →
        MemLp (fun ω => restrictJet a b (R ω)) p P ∧
        ∃ Q : Set.Ioi (0 : ℝ) → Ω → C(Set.Icc a b, Fin 3 → ℝ),
          (∀ r, MemLp (Q r) p P) ∧
          (∀ r, ∀ᵐ ω ∂P, ∀ q : Set.Icc a b, ∀ j : Fin 3,
            Q r ω q j = iteratedDeriv (j : ℕ) (responseCutoff Z t r h v ψ ω) q) ∧
          Tendsto (fun r => eLpNorm
            (fun ω => Q r ω - restrictJet a b (R ω)) p P)
            (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi (0 : ℝ)))) (𝓝 0)) := by
  classical
  let A : ℝ := ∫ x, |ψ x|
  let M : ℝ := ‖v‖
  let B : ℝ := 8 * A * M ^ 3
  let g : ℝ → Ω → ℝ := fun q ω => H t (h + q • v) ω ψ - H t h ω ψ
  have hA : 0 ≤ A := integral_nonneg (fun x => abs_nonneg (ψ x))
  have hM : 0 ≤ M := norm_nonneg v
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hex (r : Set.Ioi (0 : ℝ)) := exists_cutoffJet ϑ P Z hZ t r ht r.property h v ψ
  choose J hJm hJd hJeq hJsign using hex
  have hJzero (q : ℝ) (r : Set.Ioi (0 : ℝ)) : (fun ω => J r ω q 0) =ᵐ[P]
      (fun ω => responseCutoff Z t r h v ψ ω q) := by
    filter_upwards [hJeq r] with ω hω
    simpa using hω q 0
  have hJLp (q : ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
      Tendsto (fun r => eLpNorm ((fun ω => J r ω q 0) - g q) p P)
        responseScaleFilter (𝓝 0) := by
    have hc := (fixed_q_Lp ϑ P Z hZ H hH t ht h v ψ q p hp hp').2.2
    convert hc using 1
    funext r
    exact eLpNorm_congr_ae ((hJzero q r).sub Filter.EventuallyEq.rfl)
  have hpt (q : ℝ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ⊤) :
      ∀ ε > (0 : ℝ), ∃ s ∈ responseScaleFilter, ∀ r ∈ s, ∀ r' ∈ s,
        eLpNorm (fun ω => J r ω q 0 - J r' ω q 0) p P < ENNReal.ofReal ε :=
    (tendsto_zero_prod_iff responseScaleFilter
      (fun r r' => eLpNorm (fun ω => J r ω q 0 - J r' ω q 0) p P)).mp
      (eLpNorm_cauchy_of_tendsto P responseScaleFilter p hp (fun r ω => J r ω q 0) (g q)
        (hJLp q p hp hp'))
  obtain ⟨R₀, hR₀m, hR₀conv⟩ := exists_jet_limit_instance P responseScaleFilter J A M B
    hA hM hB hJm hJd hpt
  have hcompact (n : ℕ) : Tendsto (fun r => eLpNorm
      (fun ω => restrictJet (-(n : ℝ)) (n : ℝ) (J r ω) -
        restrictJet (-(n : ℝ)) (n : ℝ) (R₀ ω)) 1 P) responseScaleFilter (𝓝 0) :=
    (hR₀conv _ _ (by linarith [Nat.cast_nonneg (α := ℝ) n]) 1 le_rfl (by norm_num)).2
  have hR₀props := limit_jet_properties P J R₀ A M B (∀ x, 0 ≤ ψ x) hJm hR₀m hJd
    (fun hψ r ω q => hJsign r hψ ω q) hcompact
  have hR₀id (q : ℝ) : (fun ω => R₀ ω q 0) =ᵐ[P] g q :=
    identification P responseScaleFilter J R₀ hJm hR₀m q (g q)
      ((hR₀conv q q le_rfl 1 le_rfl (by norm_num)).2)
      (tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero (hJLp q 1 le_rfl (by norm_num)))
  let R : Ω →ₘ[P] C(ℝ, Fin 3 → ℝ) := AEEqFun.mk R₀ hR₀m.aestronglyMeasurable
  have hReq : (fun ω => R ω) =ᵐ[P] R₀ := AEEqFun.coeFn_mk R₀ hR₀m.aestronglyMeasurable
  have hid (q : ℝ) : (fun ω => R ω q 0) =ᵐ[P] g q := by
    filter_upwards [hReq, hR₀id q] with ω heq hid
    simpa only [heq] using hid
  have hprops : ∀ᵐ ω ∂P, ∀ q : ℝ,
      HasDerivAt (fun u => R ω u 0) (R ω q 1) q ∧
      HasDerivAt (fun u => R ω u 1) (R ω q 2) q ∧
      |R ω q 0| ≤ A * M * |q| ∧ |R ω q 1| ≤ A * M ∧ |R ω q 2| ≤ A * M ^ 2 ∧
      ((∀ x, 0 ≤ ψ x) → 0 ≤ R ω q 2) := by
    filter_upwards [hReq, hR₀props] with ω heq hω
    intro q
    rw [heq]
    exact ⟨hω.1.1 q, hω.1.2.1 q, (hω.1.2.2.2 q).1,
      (hω.1.2.2.2 q).2.1, (hω.1.2.2.2 q).2.2, fun hψ => hω.2 hψ q⟩
  refine ⟨R, ?_, ?_⟩
  · refine ⟨hid, hprops, ?_, ?_⟩
    · intro r
      exact (responseCutoff_hasDerivAt ϑ P Z hZ t r ht r.property h v ψ).mono (fun _ hω => hω.1)
    · intro a b hab p hp hp'
      have hrest : (fun ω => restrictJet a b (R ω)) =ᵐ[P]
          (fun ω => restrictJet a b (R₀ ω)) := hReq.fun_comp (restrictJet a b)
      have hlim := hR₀conv a b hab p hp hp'
      refine ⟨hlim.1.ae_eq hrest.symm, (fun r ω => restrictJet a b (J r ω)), ?_, ?_, ?_⟩
      · intro r
        exact memLp_restrictJet P (J r) A M B hA hM (hJm r) (Eventually.of_forall (hJd r)) a b p
      · intro r
        filter_upwards [hJeq r] with ω hω
        intro q j
        exact hω q j
      · convert hlim.2 using 1
        · funext r
          exact eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hrest)
        · rfl
  · intro R' hR'
    exact response_unique P g R' R
      ⟨hR'.1, hR'.2.1.mono (fun _ hω q => ⟨(hω q).1, (hω q).2.1⟩)⟩
      ⟨hid, hprops.mono (fun _ hω q => ⟨(hω q).1, (hω q).2.1⟩)⟩

end Critical2DKPZ.Extensions.Response
