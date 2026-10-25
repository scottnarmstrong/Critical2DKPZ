/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.DistributionRepresentation
public import Critical2DKPZ.Analysis.Sobolev.Rellich.NegativeNormCompactness
public import Critical2DKPZ.Analysis.Sobolev.Rellich.RellichConvolvedCompact
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Bounded

/-! Uniform local negative Sobolev bounds yield a subsequence converging against every compactly supported smooth test function to a distribution. -/

@[expose] public section

set_option linter.style.haveILetI false

noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- The bounded open ball of radius `k + 1`, used as a countable exhaustion of the plane. -/
def compactnessDomain (k : ℕ) : Set Plane := Metric.ball 0 ((k : ℝ) + 1)

/-- Each member of the ball exhaustion is a bounded nonempty open domain. -/
theorem isDomain_compactnessDomain (k : ℕ) : IsDomain (compactnessDomain k) := by
  refine ⟨Metric.isOpen_ball, Metric.isBounded_ball, ⟨0, ?_⟩⟩
  rw [compactnessDomain, Metric.mem_ball, dist_self]
  positivity

/-- A sequence of distributions with uniform local negative Sobolev bounds has a subsequence converging against every smooth compactly supported test to a distribution. -/
theorem exists_strictMono_subseq_frozen_distribution_pairings
    (s₀ : ℝ) (T : ℕ → Distr)
    (hLocal : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ,
      negSobolevNorm 2 s₀ (compactnessDomain k) (distributionFunctional (T n)) ≤
        ENNReal.ofReal M) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ ∃ Tlim : Distr, ∀ φ : TestFn,
      Tendsto (fun n => T (subseq n) φ) atTop (𝓝 (Tlim φ)) := by
  classical
  set s : ℝ := s₀ + 1 with hs
  have h₀s : s₀ < s := by rw [hs]; linarith
  let η (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hη (j : ℕ) : 0 < η j := by
    dsimp [η]
    positivity
  choose M hM hbound using hLocal
  have hnetExists (k j : ℕ) :
      ∃ (N : ℕ) (ψ : Fin N → Plane → ℝ),
        (∀ i, IsTestFn (compactnessDomain k) (ψ i) ∧
          sobolevNormSq 2 s (ψ i) ≤ 1) ∧
        ∀ F G : (Plane → ℝ) → ℝ,
          (∀ φ χ, IsTestFn (compactnessDomain k) φ → IsTestFn (compactnessDomain k) χ →
            F (φ + χ) = F φ + F χ) →
          (∀ c φ, IsTestFn (compactnessDomain k) φ →
            F (fun x => c * φ x) = c * F φ) →
          (∀ φ χ, IsTestFn (compactnessDomain k) φ → IsTestFn (compactnessDomain k) χ →
            G (φ + χ) = G φ + G χ) →
          (∀ c φ, IsTestFn (compactnessDomain k) φ →
            G (fun x => c * φ x) = c * G φ) →
          negSobolevNorm 2 s₀ (compactnessDomain k) F ≤ ENNReal.ofReal (M k) →
          negSobolevNorm 2 s₀ (compactnessDomain k) G ≤ ENNReal.ofReal (M k) →
          (∀ i, ENNReal.ofReal |F (ψ i) - G (ψ i)| ≤ ENNReal.ofReal (η j)) →
            negSobolevNorm 2 s (compactnessDomain k) (fun φ => F φ - G φ) ≤
              ENNReal.ofReal (η j) + ENNReal.ofReal (η j) *
                (ENNReal.ofReal (M k) + ENNReal.ofReal (M k)) := by
    obtain ⟨N, ψ, hψ, hnet⟩ :=
      negSobolevNorm_sub_le_of_finset_pairings_with_unit_centers
        (isDomain_compactnessDomain k) h₀s (η j) (hη j)
        (ENNReal.ofReal (M k)) (ENNReal.ofReal (η j))
    exact ⟨N, ψ, hψ, hnet⟩
  choose N ψ hψ hnet using hnetExists
  let ReadoutIndex := ℕ × ℕ × ℕ
  let readout : ℕ → ReadoutIndex → ℝ := fun n idx =>
    let (k, j, i) := idx
    if hi : i < N k j then distributionFunctional (T n) (ψ k j ⟨i, hi⟩) else 0
  let B : ReadoutIndex → ℝ := fun idx =>
    let (k, j, i) := idx
    if i < N k j then M k else 0
  have hB : ∀ idx, 0 ≤ B idx := by
    intro ⟨k, j, i⟩
    by_cases hi : i < N k j <;> simp [B, hi, hM]
  have hcoord : ∀ idx n, |readout n idx| ≤ B idx := by
    intro ⟨k, j, i⟩ n
    by_cases hi : i < N k j
    · let φ := ψ k j ⟨i, hi⟩
      have hφ : IsTestFn (compactnessDomain k) φ := (hψ k j ⟨i, hi⟩).1
      have hunit : sobolevNormSq 2 s φ ≤ 1 := (hψ k j ⟨i, hi⟩).2
      have hsmul : ∀ c χ, IsTestFn (compactnessDomain k) χ →
          distributionFunctional (T n) (fun x => c * χ x) =
            c * distributionFunctional (T n) χ := by
        intro c χ hχ
        have hχU : IsTestFn Set.univ χ := ⟨hχ.1, hχ.2.1, Set.subset_univ _⟩
        exact distributionFunctional_smul (T n) hχU c
      have hunit₀ : sobolevNormSq 2 s₀ φ ≤ ENNReal.ofReal (1 ^ 2) := by
        exact (sobolevNormSq_mono (le_of_lt h₀s) φ).trans
          (by simpa using hunit)
      have happly := abs_apply_le_negSobolevNorm (D := compactnessDomain k)
        s₀ 1 (by norm_num) (distributionFunctional (T n)) hsmul hφ hunit₀
      have hval : ENNReal.ofReal |distributionFunctional (T n) φ| ≤ ENNReal.ofReal (M k) := by
        calc
          _ ≤ ENNReal.ofReal 1 *
              negSobolevNorm 2 s₀ (compactnessDomain k) (distributionFunctional (T n)) := happly
          _ ≤ ENNReal.ofReal 1 * ENNReal.ofReal (M k) :=
            mul_le_mul_right (hbound k n) _
          _ = ENNReal.ofReal (M k) := by simp
      have hreal := (ENNReal.ofReal_le_ofReal_iff (hM k)).mp hval
      simpa [readout, B, hi, φ] using hreal
    · simp [readout, B, hi]
  let Tcoord : Set (ReadoutIndex → ℝ) :=
    {v | ∀ i, v i ∈ Set.Icc (-B i) (B i)}
  letI : MetricSpace (ReadoutIndex → ℝ) := PiCountable.metricSpace
  letI : TopologicalSpace (ReadoutIndex → ℝ) := Pi.topologicalSpace
  have hcompact : IsCompact Tcoord := by
    change IsCompact {v : ReadoutIndex → ℝ | ∀ i, v i ∈ Set.Icc (-B i) (B i)}
    exact isCompact_pi_infinite fun i => isCompact_Icc
  have hseq : ∀ n, readout n ∈ Tcoord := by
    intro n
    change ∀ i, readout n i ∈ Set.Icc (-B i) (B i)
    intro i
    rw [Set.mem_Icc]
    exact abs_le.mp (hcoord i n)
  obtain ⟨v, _, subseq, hsubseq, hread⟩ := hcompact.tendsto_subseq hseq
  have hreadCoord (idx : ReadoutIndex) :
      Tendsto (fun n => readout (subseq n) idx) atTop (𝓝 (v idx)) :=
    ((continuous_apply idx).tendsto v).comp hread
  have hpair : ∀ φ : TestFn, CauchySeq (fun n => T (subseq n) φ) := by
    intro φ
    let f : Plane → ℝ := fun x => (φ x : ℝ)
    obtain ⟨r, _, hsupport⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
    obtain ⟨k, hk⟩ := exists_nat_gt r
    have hkr : r < (k : ℝ) + 1 := by
      exact lt_trans hk (by exact_mod_cast Nat.lt_succ_self k)
    have hφD : IsTestFn (compactnessDomain k) f := by
      refine ⟨φ.contDiff, φ.hasCompactSupport, ?_⟩
      intro x hx
      rw [compactnessDomain, Metric.mem_ball]
      exact lt_trans (Metric.mem_ball.mp (hsupport hx)) hkr
    obtain ⟨Bφ, hBφ, hφnorm⟩ := exists_test_sobolev_norm_bound s φ
    rw [Metric.cauchySeq_iff]
    intro ε hε
    let δ : ℝ := ε / (Bφ * (1 + 2 * M k))
    have hMk : 0 ≤ M k := hM k
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    obtain ⟨j, hj⟩ := exists_nat_gt (1 / δ)
    have hηj : 0 < η j := hη j
    have hηsmall : η j < δ := by
      dsimp [η]
      have hj' : 1 / δ < (j : ℝ) := hj
      have hden : 0 < (j : ℝ) + 1 := by positivity
      have hdelta : 0 < δ := hδ
      apply (div_lt_iff₀ hden).2
      have hjprod : 1 < (j : ℝ) * δ := (div_lt_iff₀ hdelta).mp hj'
      calc
        1 < δ * (j : ℝ) := by simpa [mul_comm] using hjprod
        _ < δ * ((j : ℝ) + 1) :=
          mul_lt_mul_of_pos_left (by norm_num : (j : ℝ) < (j : ℝ) + 1) hdelta
    have hsmall : Bφ * (η j + η j * (M k + M k)) < ε := by
      have hfac : 0 < 1 + 2 * M k := by positivity
      have hδeq : Bφ * δ * (1 + 2 * M k) = ε := by
        dsimp [δ]
        field_simp
      calc
        _ = Bφ * η j * (1 + 2 * M k) := by ring
        _ = (Bφ * (1 + 2 * M k)) * η j := by ring
        _ < (Bφ * (1 + 2 * M k)) * δ :=
          mul_lt_mul_of_pos_left hηsmall (mul_pos hBφ hfac)
        _ = Bφ * δ * (1 + 2 * M k) := by ring
        _ = ε := hδeq
    let F : ℕ → (Plane → ℝ) → ℝ := fun n χ =>
      distributionFunctional (T (subseq n)) χ
    have hFadd : ∀ n χ ξ, IsTestFn (compactnessDomain k) χ →
        IsTestFn (compactnessDomain k) ξ → F n (χ + ξ) = F n χ + F n ξ := by
      intro n χ ξ hχ hξ
      have hχU : IsTestFn Set.univ χ := ⟨hχ.1, hχ.2.1, Set.subset_univ _⟩
      have hξU : IsTestFn Set.univ ξ := ⟨hξ.1, hξ.2.1, Set.subset_univ _⟩
      exact distributionFunctional_add (T (subseq n)) hχU hξU
    have hFsmul : ∀ n c χ, IsTestFn (compactnessDomain k) χ →
        F n (fun x => c * χ x) = c * F n χ := by
      intro n c χ hχ
      have hχU : IsTestFn Set.univ χ := ⟨hχ.1, hχ.2.1, Set.subset_univ _⟩
      exact distributionFunctional_smul (T (subseq n)) hχU c
    have hFbound (n : ℕ) :
        negSobolevNorm 2 s₀ (compactnessDomain k) (F n) ≤ ENNReal.ofReal (M k) :=
      hbound k (subseq n)
    have hcoordinate : ∀ i : Fin (N k j), ∃ K, ∀ m n, K ≤ m → K ≤ n →
        |F m (ψ k j i) - F n (ψ k j i)| ≤ η j := by
      intro i
      let idx : ReadoutIndex := (k, j, i.val)
      have hreadCauchy : CauchySeq (fun n => readout (subseq n) idx) :=
        (hreadCoord idx).cauchySeq
      obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hreadCauchy (η j) hηj
      refine ⟨K, fun m n hm hn => ?_⟩
      have hdist := hK m hm n hn
      have hreadEq (q : ℕ) : readout (subseq q) idx = F q (ψ k j i) := by
        simp [readout, idx, i.isLt, F]
      have hdist' :
          dist (F m (ψ k j i)) (F n (ψ k j i)) < η j := by
        simpa only [hreadEq, Real.dist_eq] using hdist
      have habs : |F m (ψ k j i) - F n (ψ k j i)| =
          dist (F m (ψ k j i)) (F n (ψ k j i)) := by
        rw [Real.dist_eq]
      exact habs ▸ le_of_lt hdist'
    choose Kcoord hKcoord using hcoordinate
    let Kpair : ℕ := Finset.univ.sup Kcoord
    refine ⟨Kpair, ?_⟩
    intro m hm n hn
    have hcoords : ∀ i : Fin (N k j),
        ENNReal.ofReal |F m (ψ k j i) - F n (ψ k j i)| ≤ ENNReal.ofReal (η j) := by
      intro i
      have hi : Kcoord i ≤ Kpair := Finset.le_sup (Finset.mem_univ i)
      exact ENNReal.ofReal_le_ofReal
        (hKcoord i m n (le_trans hi hm) (le_trans hi hn))
    have hsubsmul : ∀ c χ, IsTestFn (compactnessDomain k) χ →
        (fun θ => F m θ - F n θ) (fun x => c * χ x) =
          c * (fun θ => F m θ - F n θ) χ := by
      intro c χ hχ
      change F m (fun x => c * χ x) - F n (fun x => c * χ x) =
        c * (F m χ - F n χ)
      rw [hFsmul m c χ hχ, hFsmul n c χ hχ]
      ring
    have hnormResult := hnet k j (F m) (F n) (hFadd m) (hFsmul m)
      (hFadd n) (hFsmul n) (hFbound m) (hFbound n) hcoords
    have hnorm : negSobolevNorm 2 s (compactnessDomain k)
          (fun θ => F m θ - F n θ) ≤
        ENNReal.ofReal (η j + η j * (M k + M k)) := by
      calc
        _ ≤ ENNReal.ofReal (η j) + ENNReal.ofReal (η j) *
            (ENNReal.ofReal (M k) + ENNReal.ofReal (M k)) := hnormResult
        _ = ENNReal.ofReal (η j + η j * (M k + M k)) := by
          rw [← ENNReal.ofReal_add (hM k) (hM k),
            ← ENNReal.ofReal_mul (hη j).le,
            ← ENNReal.ofReal_add (hη j).le
              (mul_nonneg (hη j).le (add_nonneg (hM k) (hM k)))]
    have hφDunit : sobolevNormSq 2 s f ≤ ENNReal.ofReal (Bφ ^ 2) := by
      simpa [f] using hφnorm
    have hsubsmul' : ∀ c χ, IsTestFn (compactnessDomain k) χ →
        (fun θ => F m θ - F n θ) (fun x => c * χ x) =
          c * (fun θ => F m θ - F n θ) χ := hsubsmul
    have happly := abs_apply_le_negSobolevNorm (D := compactnessDomain k)
      s Bφ hBφ (fun θ => F m θ - F n θ) hsubsmul' hφD hφDunit
    have hpairENN : ENNReal.ofReal |F m f - F n f| ≤
        ENNReal.ofReal (Bφ * (η j + η j * (M k + M k))) := by
      calc
        _ ≤ ENNReal.ofReal Bφ *
            negSobolevNorm 2 s (compactnessDomain k) (fun θ => F m θ - F n θ) := happly
        _ ≤ ENNReal.ofReal Bφ * ENNReal.ofReal (η j + η j * (M k + M k)) :=
          mul_le_mul_right hnorm _
        _ = ENNReal.ofReal (Bφ * (η j + η j * (M k + M k))) :=
          (ENNReal.ofReal_mul (le_of_lt hBφ)).symm
    have hpairReal : |F m f - F n f| ≤ Bφ * (η j + η j * (M k + M k)) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hpairENN
    have hpairLt : |F m f - F n f| < ε := hpairReal.trans_lt hsmall
    have hEq (q : ℕ) : F q f = T (subseq q) φ := by
      change distributionFunctional (T (subseq q)) (fun x => (φ x : ℝ)) = _
      have hφU : IsTestFn Set.univ (fun x => (φ x : ℝ)) :=
        ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
      have hrep : testFnOfRellich hφU.1 hφU.2.1 = φ := by
        apply TestFunction.ext
        intro x
        rfl
      rw [distributionFunctional_apply (T (subseq q))
        hφU, hrep]
    have hdist : dist (T (subseq m) φ) (T (subseq n) φ) < ε := by
      simpa [hEq m, hEq n, Real.dist_eq] using hpairLt
    exact hdist
  have hLocalSub : ∀ K : Compacts Plane, ∃ (D : Set Plane) (C : ℝ),
      (K : Set Plane) ⊆ D ∧ 0 ≤ C ∧ ∀ n,
        negSobolevNorm 2 s D (distributionFunctional (T (subseq n))) ≤ ENNReal.ofReal C := by
    intro K
    obtain ⟨r, _, hKball⟩ := K.2.isBounded.subset_ball_lt 0 (0 : Plane)
    obtain ⟨k, hk⟩ := exists_nat_gt r
    have hkr : r < (k : ℝ) + 1 := by
      exact lt_trans hk (by exact_mod_cast Nat.lt_succ_self k)
    let C := M k
    have hC : 0 ≤ C := hM k
    have hboundC : ∀ n : ℕ,
        negSobolevNorm 2 s₀ (compactnessDomain k) (distributionFunctional (T n)) ≤
          ENNReal.ofReal C := hbound k
    refine ⟨compactnessDomain k, C, ?_, hC, ?_⟩
    · intro x hx
      rw [compactnessDomain, Metric.mem_ball]
      exact lt_trans (Metric.mem_ball.mp (hKball hx)) hkr
    · intro n
      exact (negSobolevNorm_anti (le_of_lt h₀s) (compactnessDomain k)
        (distributionFunctional (T (subseq n)))).trans (hboundC (subseq n))
  obtain ⟨Tlim, hTlim⟩ := exists_frozen_distribution_limit_of_locally_bounded_cauchy_pairings
    s (fun n => T (subseq n)) hpair hLocalSub
  exact ⟨subseq, hsubseq, Tlim, hTlim⟩

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
