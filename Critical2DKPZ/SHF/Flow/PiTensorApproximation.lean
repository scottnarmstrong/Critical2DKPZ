/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.BigOperators.Fin

/-! # Compact tensor approximation on finite products of plane pairs

Stone–Weierstrass gives a fixed compact window on which finite products of compactly supported
coordinate tests uniformly approximate every compactly supported continuous test.
-/

@[expose] public noncomputable section

open Set
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

private def piContinuousTensorTest {n : ℕ}
    (g : Fin n → C(Plane × Plane, ℝ)) : C((Fin n → Plane × Plane), ℝ) :=
  ⟨fun q => ∏ i, g i (q i), by fun_prop⟩

private def piContinuousTensorSpan (n : ℕ) :
    Submodule ℝ C((Fin n → Plane × Plane), ℝ) :=
  Submodule.span ℝ (Set.range (piContinuousTensorTest (n := n)))

private theorem one_mem_piContinuousTensorSpan (n : ℕ) :
    (1 : C((Fin n → Plane × Plane), ℝ)) ∈ piContinuousTensorSpan n := by
  apply Submodule.subset_span
  refine ⟨fun _ => 1, ?_⟩
  ext q
  simp [piContinuousTensorTest]

private theorem mul_mem_piContinuousTensorSpan {n : ℕ}
    {f g : C((Fin n → Plane × Plane), ℝ)}
    (hf : f ∈ piContinuousTensorSpan n) (hg : g ∈ piContinuousTensorSpan n) :
    f * g ∈ piContinuousTensorSpan n := by
  have hgen {g : C((Fin n → Plane × Plane), ℝ)} (hg : g ∈ piContinuousTensorSpan n)
      (a : Fin n → C(Plane × Plane, ℝ)) :
      piContinuousTensorTest a * g ∈ piContinuousTensorSpan n := by
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨b, rfl⟩ := hg
        have heq : piContinuousTensorTest a * piContinuousTensorTest b =
            piContinuousTensorTest (fun i => a i * b i) := by
          ext q
          change (∏ i, a i (q i)) * (∏ i, b i (q i)) =
            ∏ i, (a i (q i)) * (b i (q i))
          rw [Finset.prod_mul_distrib]
        rw [heq]
        exact Submodule.subset_span ⟨fun i => a i * b i, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy =>
        rw [mul_add]
        exact (piContinuousTensorSpan n).add_mem ihx ihy
    | smul c x hx ih =>
        rw [mul_smul_comm]
        exact (piContinuousTensorSpan n).smul_mem c ih
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      exact hgen hg a
  | zero => simp
  | add f g hf hg ihf ihg =>
      rw [add_mul]
      exact (piContinuousTensorSpan n).add_mem ihf ihg
  | smul c f hf ih =>
      rw [smul_mul_assoc]
      exact (piContinuousTensorSpan n).smul_mem c ih

private def piContinuousTensorAlgebra (n : ℕ) :
    Subalgebra ℝ C((Fin n → Plane × Plane), ℝ) :=
  (piContinuousTensorSpan n).toSubalgebra (one_mem_piContinuousTensorSpan n)
    (fun _ _ hf hg => mul_mem_piContinuousTensorSpan hf hg)

private theorem piContinuousTensorAlgebra_separatesPoints {n : ℕ} :
    (piContinuousTensorAlgebra n).SeparatesPoints := by
  intro x y hxy
  obtain ⟨i, hxyi⟩ := Function.ne_iff.mp hxy
  let g : Fin n → C(Plane × Plane, ℝ) := fun j =>
    if j = i then ⟨fun z => dist z (x i), continuous_id.dist continuous_const⟩ else 1
  refine ⟨piContinuousTensorTest g,
    ⟨piContinuousTensorTest g,
      Submodule.subset_span ⟨g, rfl⟩, rfl⟩, ?_⟩
  have hx : piContinuousTensorTest g x = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [g]
  have hy : piContinuousTensorTest g y = dist (y i) (x i) := by
    change (∏ j, g j (y j)) = dist (y i) (x i)
    rw [Finset.prod_eq_single i]
    · simp [g]
    · intro j hj hji
      simp [g, hji]
    · simp
  rw [hx, hy]
  exact (dist_ne_zero.mpr (Ne.symm hxyi)).symm

private theorem exists_sum_piContinuousTensor_of_mem_span {n : ℕ} (hn : 0 < n)
    {f : C((Fin n → Plane × Plane), ℝ)} (hf : f ∈ piContinuousTensorSpan n) :
    ∃ r : ℕ, ∃ g : Fin r → Fin n → C(Plane × Plane, ℝ),
      f = ∑ b, piContinuousTensorTest (g b) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨g, rfl⟩ := hf
      exact ⟨1, fun _ => g, by simp⟩
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | add f h hf hh ihf ihh =>
      obtain ⟨m, g, hfg⟩ := ihf
      obtain ⟨k, g', hhg⟩ := ihh
      refine ⟨m + k, Fin.addCases g g', ?_⟩
      rw [Fin.sum_univ_add]
      simpa only [Fin.addCases_left, Fin.addCases_right] using congrArg₂ (· + ·) hfg hhg
  | smul c f hf ih =>
      obtain ⟨r, g, hfg⟩ := ih
      let a : Fin n := ⟨0, hn⟩
      let g' : Fin r → Fin n → C(Plane × Plane, ℝ) :=
        fun b i => (if i = a then c else 1) • g b i
      refine ⟨r, g', ?_⟩
      rw [hfg, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ext q
      change c * (∏ i, g b i (q i)) =
        ∏ i, ((if i = a then c else (1 : ℝ)) * g b i (q i))
      rw [Finset.prod_mul_distrib]
      have ha : (∏ i : Fin n, if i = a then c else (1 : ℝ)) = c := by
        rw [Finset.prod_eq_single a]
        · simp
        · intro i hi hia
          simp [hia]
        · simp
      rw [ha]

/-- Compact tests on a nonempty finite product admit uniform finite tensor approximations with a common compact support. -/
theorem exists_compactTensorProduct_uniform_approx {n : ℕ} (hn : 0 < n)
    (F : C_c((Fin n → Plane × Plane), ℝ)) :
    ∃ K : Set (Plane × Plane), IsCompact K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ r : ℕ, ∃ φ : Fin r → Fin n → C_c(Plane × Plane, ℝ),
        (∀ b i, tsupport (φ b i : Plane × Plane → ℝ) ⊆ K) ∧
        ∀ q, |(∑ b, ∏ i, φ b i (q i)) - F q| < ε := by
  classical
  let S : Set (Fin n → Plane × Plane) := tsupport (F : (Fin n → Plane × Plane) → ℝ)
  let K₀ : Set (Plane × Plane) := ⋃ i : Fin n, (fun q : Fin n → Plane × Plane => q i) '' S
  have hK₀ : IsCompact K₀ := isCompact_iUnion fun i => F.hasCompactSupport.image (continuous_apply i)
  obtain ⟨χ, hχone, hχc, hχU, hχ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK₀ isOpen_univ (subset_univ _)
  let K : Set (Plane × Plane) := tsupport (χ : Plane × Plane → ℝ)
  have hK : IsCompact K := hχc
  have hK₀sub : K₀ ⊆ K := by
    intro z hz
    have hχz : χ z ≠ 0 := by
      rw [hχone hz]
      norm_num
    exact subset_tsupport _ hχz
  let R : Set (Fin n → Plane × Plane) := Set.univ.pi fun _ => K
  have hR : IsCompact R := isCompact_univ_pi fun _ => hK
  have hSsub : S ⊆ R := by
    intro q hq
    refine Set.mem_univ_pi.mpr fun i => ?_
    apply hK₀sub
    exact Set.mem_iUnion.mpr ⟨i, ⟨q, hq, rfl⟩⟩
  refine ⟨K, hK, fun ε hε => ?_⟩
  obtain ⟨g, hgspan, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
      piContinuousTensorAlgebra_separatesPoints F.toContinuousMap hR hε
  obtain ⟨r, a, hga⟩ := exists_sum_piContinuousTensor_of_mem_span hn hgspan
  let φ : Fin r → Fin n → C_c(Plane × Plane, ℝ) := fun b i =>
    ⟨⟨fun z => χ z * a b i z, χ.continuous.mul (a b i).continuous⟩,
      (show HasCompactSupport (χ : Plane × Plane → ℝ) from hχc).mul_right⟩
  have hφsupport (b : Fin r) (i : Fin n) : tsupport (φ b i : Plane × Plane → ℝ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    have hz' : χ z * a b i z ≠ 0 := hz
    have hχz : χ z ≠ 0 := by
      intro hzero
      apply hz'
      simp [hzero]
    exact subset_tsupport _ hχz
  refine ⟨r, φ, hφsupport, ?_⟩
  intro q
  have hprod (b : Fin r) : (∏ i, φ b i (q i)) =
      (∏ i, χ (q i)) * (∏ i, a b i (q i)) := by
    dsimp [φ]
    rw [Finset.prod_mul_distrib]
  have hsum : (∑ b, ∏ i, φ b i (q i)) =
      (∏ i, χ (q i)) * (∑ b, ∏ i, a b i (q i)) := by
    simp_rw [hprod]
    rw [Finset.mul_sum]
  by_cases hqR : q ∈ R
  · have hcut : (∏ i, χ (q i)) * F q = F q := by
      by_cases hqS : q ∈ S
      · have hχS : ∀ i, χ (q i) = 1 := by
          intro i
          apply hχone
          exact Set.mem_iUnion.mpr ⟨i, ⟨q, hqS, rfl⟩⟩
        simp [hχS]
      · have hFzero : F q = 0 := image_eq_zero_of_notMem_tsupport hqS
        simp [hFzero]
    rw [hsum]
    have hval : 0 ≤ ∏ i, χ (q i) := Finset.prod_nonneg fun i hi => (hχ01 (q i)).1
    have hle : ∏ i, χ (q i) ≤ 1 := by
      calc
        ∏ i, χ (q i) ≤ ∏ i : Fin n, (1 : ℝ) :=
          Finset.prod_le_prod₀ (fun i hi => (hχ01 (q i)).1) (fun i hi => (hχ01 (q i)).2)
        _ = 1 := by simp
    have happrox : |(∑ b, ∏ i, a b i (q i)) - F q| < ε := by
      have happroxG : |g q - F q| < ε := by
        simpa only [Real.norm_eq_abs, CompactlySupportedContinuousMap.coe_toContinuousMap]
          using hg q hqR
      have hgaq : g q = ∑ b, ∏ i, a b i (q i) := by
        have h := congrArg (fun f : C((Fin n → Plane × Plane), ℝ) => f q) hga
        simpa only [ContinuousMap.sum_apply, piContinuousTensorTest, ContinuousMap.coe_mk] using h
      rw [← hgaq]
      exact happroxG
    have hrewrite :
        (∏ i, χ (q i)) * (∑ b, ∏ i, a b i (q i)) - F q =
          (∏ i, χ (q i)) * ((∑ b, ∏ i, a b i (q i)) - F q) := by
      calc
        _ = (∏ i, χ (q i)) * (∑ b, ∏ i, a b i (q i)) -
              (∏ i, χ (q i)) * F q := by
                exact congrArg (fun z =>
                  (∏ i, χ (q i)) * (∑ b, ∏ i, a b i (q i)) - z) hcut.symm
        _ = _ := (mul_sub _ _ _).symm
    rw [hrewrite, abs_mul, abs_of_nonneg hval]
    exact (mul_le_of_le_one_left (abs_nonneg _) hle).trans_lt happrox
  · have hqoutside : ¬ ∀ i, q i ∈ K := by
      intro h
      exact hqR (Set.mem_univ_pi.mpr h)
    obtain ⟨i, hi⟩ := not_forall.mp hqoutside
    have hχzero : χ (q i) = 0 := image_eq_zero_of_notMem_tsupport hi
    have hFzero : F q = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hqS
      exact hqR (hSsub hqS)
    have hprodzero : (∏ j, χ (q j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hχzero
    rw [hsum, hprodzero, hFzero]
    simpa only [zero_mul, sub_self, abs_zero] using hε

end Critical2DKPZ.SHF.Flow

end
