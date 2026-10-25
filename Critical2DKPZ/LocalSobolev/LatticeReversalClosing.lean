/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.DistributionValuedLimits
public import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenDistributionBound
public import Critical2DKPZ.Analysis.Sobolev.Rellich.DistributionRepresentation
import Mathlib.Tactic

/-! # Uniform second moments of tested lattice fields

Local negative Sobolev energy controls the test pairing. No pointwise
second-moment estimate is used.
-/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology BoundedContinuousFunction
namespace Critical2DKPZ.LocalSobolev

/-- Uniform second moments of the tested lattice KPZ field, from its local
negative Sobolev moment bound. -/
theorem kpzLattice_testFn_sq_le_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ) {t : ℝ} (ht : 0 < t)
    (h₀ : Plane →ᵇ ℝ) (φ : TestFn) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ᶠ N : ℕ in atTop,
      ∫⁻ ω, ‖∫ x, φ x * kpzLattice ϑ N t h₀ x ω‖ₑ ^ 2 ∂disorderLaw ≤ C := by
  obtain ⟨m, hm⟩ := exists_localizer_eq_one_on_compact φ.hasCompactSupport.isCompact
  obtain ⟨B, _, hB⟩ := Analysis.Sobolev.Rellich.exists_test_sobolev_norm_bound 1 φ
  let S := Analysis.Sobolev.Rellich.sobolevNormSq 2 1 (fun x => (φ x : ℝ))
  have hS : S ≠ ⊤ := ne_of_lt (hB.trans_lt ENNReal.ofReal_lt_top)
  obtain ⟨C, hC⟩ := kpzLattice_negSobolev_moment_le_of hVD ϑ ht h₀
    (a := 1) (by norm_num) (localizer m)
  refine ⟨S * ENNReal.ofReal C, ENNReal.mul_ne_top hS ENNReal.ofReal_ne_top, ?_⟩
  filter_upwards [hC] with N hN
  have hp (ω : Disorder) :
      ‖∫ x, φ x * kpzLattice ϑ N t h₀ x ω‖ₑ ^ 2 ≤
        S * localNegSobolevSq 1
          (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) (localizer m) := by
    let T := Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤
    have hd := Analysis.Sobolev.Rellich.distribution_pairing_le_localNegSobolev_product
      1 T (localizer m) φ (hm m le_rfl)
    have he : T φ = ∫ x, φ x * kpzLattice ϑ N t h₀ x ω := by
      exact Distribution.ofFun_apply ((kpzLattice_locallyIntegrable ϑ N t h₀ ω).locallyIntegrableOn _)
    have hsq := ENNReal.rpow_le_rpow hd (by norm_num : 0 ≤ (2 : ℝ))
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ)),
      ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at hsq
    norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
      ENNReal.rpow_one, ENNReal.rpow_two] at hsq
    rw [Real.enorm_eq_ofReal_abs, ← he]
    exact hsq
  calc
    _ ≤ ∫⁻ ω, S * localNegSobolevSq 1
        (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) (localizer m)
        ∂disorderLaw := lintegral_mono hp
    _ = S * ∫⁻ ω, localNegSobolevSq 1
        (Distribution.ofFun ⊤ (fun x => kpzLattice ϑ N t h₀ x ω) volume ⊤) (localizer m)
        ∂disorderLaw := lintegral_const_mul' _ _ hS
    _ ≤ _ := by gcongr

private theorem tuple_norm_sq_le_sum {k : ℕ} (v : Fin k → ℝ) :
    ‖v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
  have hsum : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hn : ‖v‖ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) hsum).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖v j‖) (Finset.mem_univ i)
  calc
    ‖v‖ ^ 2 ≤ (Real.sqrt (∑ i, ‖v i‖ ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := Real.sq_sqrt hsum

/-- Finite vectors of tested lattice fields have an integrable squared norm bounded uniformly in the lattice scale. -/
theorem kpzLattice_testFnTuple_second_moment_le_of
    (hVD : Smoothing.PropVDBound) (ϑ : ℝ) {k : ℕ} (t : Fin k → ℝ)
    (ht : ∀ i, 0 < t i) (h₀ : Fin k → Plane →ᵇ ℝ) (φ : Fin k → TestFn) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      Integrable (fun ω => ‖(fun i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω)‖ ^ 2)
        disorderLaw ∧
      (∫ ω, ‖(fun i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω)‖ ^ 2
        ∂disorderLaw) ≤ C := by
  classical
  choose C hCtop hCb using fun i => kpzLattice_testFn_sq_le_of hVD ϑ (ht i) (h₀ i) (φ i)
  refine ⟨∑ i, (C i).toReal, Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg), ?_⟩
  filter_upwards [Filter.eventually_all.mpr hCb] with N hN
  let X : Disorder → Fin k → ℝ := fun ω i => ∫ x, φ i x * kpzLattice ϑ N (t i) (h₀ i) x ω
  have hXi (i : Fin k) : Measurable (fun ω => X ω i) := by
    have h := measurable_kpzLattice_distribution_pairing ϑ N (t i) (h₀ i) (φ i)
    convert h using 1
    funext ω
    exact (Distribution.ofFun_apply
      ((kpzLattice_locallyIntegrable ϑ N (t i) (h₀ i) ω).locallyIntegrableOn _)).symm
  have hreal (i : Fin k) : (∫⁻ ω, ENNReal.ofReal (‖X ω i‖ ^ 2) ∂disorderLaw) ≤ C i := by
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    exact hN i
  have hi (i : Fin k) : Integrable (fun ω => ‖X ω i‖ ^ 2) disorderLaw := by
    refine ⟨((hXi i).norm.pow_const 2).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖X ω i‖))).mpr
    exact (hreal i).trans_lt (lt_top_iff_ne_top.mpr (hCtop i))
  have hib (i : Fin k) : (∫ ω, ‖X ω i‖ ^ 2 ∂disorderLaw) ≤ (C i).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => sq_nonneg ‖X ω i‖)) (hi i).aestronglyMeasurable]
    exact ENNReal.toReal_mono (hCtop i) (hreal i)
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hX : Measurable X := measurable_pi_iff.mpr hXi
  have hI : Integrable (fun ω => ‖X ω‖ ^ 2) disorderLaw := by
    apply hsum.mono' (hX.norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using tuple_norm_sq_le_sum (X ω))
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ ω, ∑ i, ‖X ω i‖ ^ 2 ∂disorderLaw :=
      integral_mono hI hsum (fun ω => tuple_norm_sq_le_sum (X ω))
    _ = ∑ i, ∫ ω, ‖X ω i‖ ^ 2 ∂disorderLaw := integral_finsetSum _ (fun i _ => hi i)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hib i)

end Critical2DKPZ.LocalSobolev
