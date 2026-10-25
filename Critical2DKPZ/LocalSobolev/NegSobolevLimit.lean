/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.FiniteOrder
public import Critical2DKPZ.Analysis.Sobolev.Rellich.DistributionRepresentation
public import Critical2DKPZ.Analysis.Sobolev.Rellich.FrozenDistributionBound
public import Critical2DKPZ.Analysis.Sobolev.Rellich.LocalCompactnessExtraction
public import Critical2DKPZ.LocalSobolev.LimitDistribution

/-! # Almost-sure local negative Sobolev limits -/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace Critical2DKPZ.LocalSobolev

open Critical2DKPZ.Analysis.Sobolev.Rellich

private theorem localizer_eq_one_on_compactnessDomain (k : ℕ) {x : Plane}
    (hx : x ∈ compactnessDomain k) : localizer k x = 1 := by
  apply localizer_eq_one_of_mem_closedBall
  exact Metric.ball_subset_closedBall hx

private theorem localNegSobolevENorm_finset_sum_le {ι : Type*} (a : ℝ)
    (f : ι → Distr) (s : Finset ι) (χ : TestFn) :
    localNegSobolevENorm a (∑ i ∈ s, f i) χ ≤
      ∑ i ∈ s, localNegSobolevENorm a (f i) χ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (localNegSobolevENorm_add_le a (f i) (∑ j ∈ s, f j) χ).trans
        (add_le_add (le_refl _) ih)

private theorem localNegSobolevENorm_incrementSegment_le
    (T : ℕ → Distr) (k n m : ℕ) (hnm : n ≤ m) :
    localNegSobolevENorm 1 (T (n + k) - T (m + k)) (localizer k) ≤
      ∑ j ∈ Finset.range (m - n),
        localNegSobolevENorm 1 (T (j + n + k) - T (j + n + k + 1)) (localizer k) := by
  have htel : (∑ j ∈ Finset.range (m - n),
      (T ((j + 1) + (n + k)) - T (j + (n + k)))) = T (m + k) - T (n + k) := by
    have hindex : (m - n) + (n + k) = m + k := by
      rw [← Nat.add_assoc, Nat.sub_add_cancel hnm]
    simpa only [hindex, zero_add] using
      (Finset.sum_range_sub (fun j : ℕ => T (j + (n + k))) (m - n))
  have htel' : -(∑ j ∈ Finset.range (m - n),
      (T ((j + 1) + (n + k)) - T (j + (n + k)))) =
      T (n + k) - T (m + k) := by rw [htel]; abel
  calc
    localNegSobolevENorm 1 (T (n + k) - T (m + k)) (localizer k) =
        localNegSobolevENorm 1
          (∑ j ∈ Finset.range (m - n),
            (T ((j + 1) + (n + k)) - T (j + (n + k)))) (localizer k) := by
              rw [← htel', localNegSobolevENorm_neg]
    _ ≤ ∑ j ∈ Finset.range (m - n),
          localNegSobolevENorm 1
            (T ((j + 1) + (n + k)) - T (j + (n + k))) (localizer k) :=
      localNegSobolevENorm_finset_sum_le 1 _ _ _
    _ = ∑ j ∈ Finset.range (m - n),
          localNegSobolevENorm 1
            (T (j + n + k) - T (j + n + k + 1)) (localizer k) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hidx₁ : (j + 1) + (n + k) = j + n + k + 1 := by omega
      have hidx₂ : j + (n + k) = j + n + k := by omega
      have hsub : T ((j + 1) + (n + k)) - T (j + (n + k)) =
          -(T (j + n + k) - T (j + n + k + 1)) := by
        rw [hidx₁, hidx₂]
        abel
      rw [hsub, localNegSobolevENorm_neg]

private theorem localNegSobolevENorm_incrementSegment_le_tsum
    (T : ℕ → Distr) (k n m : ℕ) (hnm : n ≤ m) :
    localNegSobolevENorm 1 (T (n + k) - T (m + k)) (localizer k) ≤
      ∑' j, localNegSobolevENorm 1
        (T (j + n + k) - T (j + n + k + 1)) (localizer k) := by
  let a : ℕ → ℝ≥0∞ := fun j =>
    localNegSobolevENorm 1 (T (j + k) - T (j + k + 1)) (localizer k)
  have hseg := localNegSobolevENorm_incrementSegment_le T k n m hnm
  calc
    localNegSobolevENorm 1 (T (n + k) - T (m + k)) (localizer k) ≤
        ∑ j ∈ Finset.range (m - n), a (j + n) := by
          simpa [a, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hseg
    _ ≤ ∑' j, a (j + n) := ENNReal.sum_le_tsum (Finset.range (m - n))
    _ = ∑' j, localNegSobolevENorm 1
          (T (j + n + k) - T (j + n + k + 1)) (localizer k) := by
          apply tsum_congr
          intro j
          rfl

private theorem localizer_pairing_cauchy (T : ℕ → Distr) (k : ℕ)
    (hsum : (∑' j, localNegSobolevENorm 1
      (T (j + k) - T (j + k + 1)) (localizer k)) ≠ ⊤)
    {f : Plane → ℝ} (hf : IsTestFn (compactnessDomain k) f) :
    CauchySeq (fun n => T (n + k) (testFnOfRellich hf.1 hf.2.1)) := by
  let a : ℕ → ℝ≥0∞ := fun j => localNegSobolevENorm 1
    (T (j + k) - T (j + k + 1)) (localizer k)
  have htail : Tendsto (fun N => ∑' j, a (j + N)) atTop (𝓝 0) :=
    ENNReal.tendsto_sum_nat_add a (by simpa [a] using hsum)
  let ψ : TestFn := testFnOfRellich hf.1 hf.2.1
  obtain ⟨B, hB, hnorm⟩ := exists_test_sobolev_norm_bound 1 ψ
  let q : ℝ := (1 / (B + 1)) * 1
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hreal : B * q < 1 := by
    dsimp [q]
    have hBden : 0 < B + 1 := by positivity
    calc
      B * ((1 / (B + 1)) * 1) < (B + 1) * ((1 / (B + 1)) * 1) := by
        exact mul_lt_mul_of_pos_right (by linarith) (by positivity)
      _ = 1 := by field_simp
  have hχ : ∀ x ∈ compactnessDomain k, localizer k x = 1 := by
    intro x hx
    exact localizer_eq_one_on_compactnessDomain k hx
  have hpairENN (n m : ℕ) :
      ENNReal.ofReal |T (n + k) ψ - T (m + k) ψ| ≤
        ENNReal.ofReal B * localNegSobolevENorm 1
          (T (n + k) - T (m + k)) (localizer k) := by
    let U : Distr := T (n + k) - T (m + k)
    have hUnorm := distributionFunctional_negSobolevNorm_le_localEnergy
      U (localizer k) 1 hχ
    have hUnorm' : negSobolevNorm 2 1 (compactnessDomain k)
        (distributionFunctional U) ≤ localNegSobolevENorm 1 U (localizer k) := by
      simpa only [← localNegSobolevENorm_eq_rpow] using hUnorm
    have hsmul : ∀ (c : ℝ) g, IsTestFn (compactnessDomain k) g →
        distributionFunctional U (fun x => c * g x) = c * distributionFunctional U g := by
      intro c g hg
      exact distributionFunctional_smul U
        ⟨hg.1, hg.2.1, Set.subset_univ _⟩ c
    have happly := abs_apply_le_negSobolevNorm (D := compactnessDomain k)
      1 B hB (distributionFunctional U) hsmul hf hnorm
    have heval : distributionFunctional U f = T (n + k) ψ - T (m + k) ψ := by
      rw [distributionFunctional_apply U hf]
      rfl
    calc
      _ = ENNReal.ofReal |distributionFunctional U f| := by rw [heval]
      _ ≤ ENNReal.ofReal B * negSobolevNorm 2 1
          (compactnessDomain k) (distributionFunctional U) := happly
      _ ≤ ENNReal.ofReal B * localNegSobolevENorm 1 U (localizer k) :=
        mul_le_mul_of_nonneg_left hUnorm' (by positivity)
      _ = _ := rfl
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let qε : ℝ := ε * q
  have hqε' : 0 < qε := by dsimp [qε]; positivity
  have hsmallε : ∀ᶠ N : ℕ in atTop,
      (∑' j, a (j + N)) < ENNReal.ofReal qε :=
    (ENNReal.tendsto_sum_nat_add a (by simpa [a] using hsum)).eventually
      (Iio_mem_nhds (ENNReal.ofReal_pos.mpr hqε'))
  obtain ⟨Nε, hNε⟩ := Filter.eventually_atTop.1 hsmallε
  refine ⟨Nε, fun m hm n hn => ?_⟩
  let r : ℕ := min n m
  have hrN : Nε ≤ r := le_min hn hm
  have htailr : (∑' j, a (j + r)) < ENNReal.ofReal qε := hNε r hrN
  have hnorm : localNegSobolevENorm 1 (T (n + k) - T (m + k)) (localizer k) ≤
      ∑' j, a (j + r) := by
    by_cases hnm : n ≤ m
    · simpa [r, min_eq_left hnm, a] using
        localNegSobolevENorm_incrementSegment_le_tsum T k n m hnm
    · have hmn : m ≤ n := Nat.le_of_not_ge hnm
      have hbound := localNegSobolevENorm_incrementSegment_le_tsum T k m n hmn
      have heq : localNegSobolevENorm 1 (T (n + k) - T (m + k)) (localizer k) =
          localNegSobolevENorm 1 (T (m + k) - T (n + k)) (localizer k) := by
        have hsub : T (n + k) - T (m + k) = -(T (m + k) - T (n + k)) := by abel
        rw [hsub, localNegSobolevENorm_neg]
      have hrm : r = m := by dsimp [r]; exact min_eq_right hmn
      rw [heq, hrm]
      simpa [a] using hbound
  have hmul : ENNReal.ofReal B * (∑' j, a (j + r)) < ENNReal.ofReal ε := by
    calc
      _ < ENNReal.ofReal B * ENNReal.ofReal qε := by
        gcongr
        exact ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (B * qε) := (ENNReal.ofReal_mul hB.le).symm
      _ < ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_lt_ofReal_iff hε]
        dsimp [qε]
        calc
          B * (ε * q) = ε * (B * q) := by ring
          _ < ε * 1 := mul_lt_mul_of_pos_left hreal hε
          _ = ε := by ring
  have habs : ENNReal.ofReal |T (n + k) ψ - T (m + k) ψ| < ENNReal.ofReal ε :=
    (hpairENN n m).trans_lt (by
      exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_lt hmul)
  have habsReal : |T (n + k) ψ - T (m + k) ψ| < ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).mp habs
  simpa [ψ, abs_sub_comm, Real.dist_eq] using habsReal

private theorem exists_compactnessDomain_for_testFn {f : Plane → ℝ}
    (hf : IsTestFn Set.univ f) : ∃ k : ℕ, IsTestFn (compactnessDomain k) f := by
  obtain ⟨r, _, hball⟩ := hf.2.1.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
  obtain ⟨k, hk⟩ := exists_nat_gt r
  have hkr : r < (k : ℝ) + 1 := by
    exact lt_trans hk (by exact_mod_cast Nat.lt_succ_self k)
  refine ⟨k, ⟨hf.1, hf.2.1, ?_⟩⟩
  intro x hx
  rw [compactnessDomain, Metric.mem_ball]
  exact lt_trans (Metric.mem_ball.mp (hball hx)) hkr

/-- A sequence whose local negative Sobolev increments are summable has a distributional limit
on every test function. The representation is obtained from the canonical local-energy limit and
finite-order distribution bounds on each compact support. -/
private theorem exists_frozen_distribution_limit_of_summable_localizer_increments
    (T : ℕ → Distr)
    (hsum : ∀ k : ℕ, (∑' j, localNegSobolevENorm 1
      (T (j + k) - T (j + k + 1)) (localizer k)) ≠ ⊤) :
    ∃ H : Distr, ∀ φ : TestFn, Tendsto (fun n => T n φ) atTop (𝓝 (H φ)) := by
  classical
  let G : (Plane → ℝ) → ℝ := fun f =>
    if hf : IsTestFn Set.univ f then limUnder atTop (fun n => distributionFunctional (T n) f)
    else 0
  have hCauchy (f : Plane → ℝ) (hf : IsTestFn Set.univ f) :
      CauchySeq (fun n => distributionFunctional (T n) f) := by
    obtain ⟨k, hfk⟩ := exists_compactnessDomain_for_testFn hf
    let ψ : TestFn := testFnOfRellich hf.1 hf.2.1
    let ψk : TestFn := testFnOfRellich hfk.1 hfk.2.1
    have hψ : ψk = ψ := by
      apply TestFunction.ext
      intro x
      rfl
    have hshift : CauchySeq (fun n => T (n + k) ψ) := by
      simpa [ψ, ψk, hψ] using localizer_pairing_cauchy T k (hsum k) hfk
    have hfull : CauchySeq (fun n => T n ψ) := by
      rw [Metric.cauchySeq_iff] at hshift ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hshift ε hε
      refine ⟨N + k, ?_⟩
      intro n hn m hm
      have hn' : N ≤ n - k := by omega
      have hm' : N ≤ m - k := by omega
      have hdist := hN (n - k) hn' (m - k) hm'
      have hnk : n - k + k = n := Nat.sub_add_cancel (by omega)
      have hmk : m - k + k = m := Nat.sub_add_cancel (by omega)
      simpa [hnk, hmk] using hdist
    have heq : (fun n => distributionFunctional (T n) f) = fun n => T n ψ := by
      funext n
      exact distributionFunctional_apply (T n) hf
    rw [heq]
    exact hfull
  have hGlim (f : Plane → ℝ) (hf : IsTestFn Set.univ f) :
      Tendsto (fun n => distributionFunctional (T n) f) atTop (𝓝 (G f)) := by
    change Tendsto (fun n => distributionFunctional (T n) f) atTop
      (𝓝 (if h : IsTestFn Set.univ f then
        limUnder atTop (fun n => distributionFunctional (T n) f) else 0))
    rw [dite_eq_left hf]
    exact (hCauchy f hf).tendsto_limUnder
  have hGadd : ∀ f g, IsTestFn Set.univ f → IsTestFn Set.univ g →
      G (f + g) = G f + G g := by
    intro f g hf hg
    apply tendsto_nhds_unique (hGlim (f + g) (hf.add hg))
    have hsum : Tendsto
        (fun n => distributionFunctional (T n) f + distributionFunctional (T n) g)
        atTop (𝓝 (G f + G g)) := (hGlim f hf).add (hGlim g hg)
    have heq : (fun n => distributionFunctional (T n) f + distributionFunctional (T n) g) =
        fun n => distributionFunctional (T n) (f + g) := by
      funext n
      exact (distributionFunctional_add (T n) hf hg).symm
    simpa only [heq] using hsum
  have hGsmul : ∀ (c : ℝ) f, IsTestFn Set.univ f →
      G (fun x => c * f x) = c * G f := by
    intro c f hf
    apply tendsto_nhds_unique (hGlim (fun x => c * f x) (hf.const_mul c))
    have hmul : Tendsto (fun n => c * distributionFunctional (T n) f)
        atTop (𝓝 (c * G f)) := tendsto_const_nhds.mul (hGlim f hf)
    have heq : (fun n => c * distributionFunctional (T n) f) =
        fun n => distributionFunctional (T n) (fun x => c * f x) := by
      funext n
      exact (distributionFunctional_smul (T n) hf c).symm
    simpa only [heq] using hmul
  have hcompactBound : ∀ K : Compacts Plane, ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ φ : ContDiffMapSupportedIn Plane ℝ ⊤ K,
        |G (fun x => (φ x : ℝ))| ≤
          C * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ := by
    intro K
    obtain ⟨r, _, hball⟩ := K.isCompact.isBounded.subset_ball_lt 0 (0 : Plane)
    obtain ⟨k, hk⟩ := exists_nat_gt r
    have hkr : r < (k : ℝ) + 1 := by
      exact lt_trans hk (by exact_mod_cast Nat.lt_succ_self k)
    have hKD : (K : Set Plane) ⊆ compactnessDomain k := by
      intro x hx
      rw [compactnessDomain, Metric.mem_ball]
      exact lt_trans (Metric.mem_ball.mp (hball hx)) hkr
    have hχ : ∀ x ∈ compactnessDomain k, localizer k x = 1 := by
      intro x hx
      exact localizer_eq_one_on_compactnessDomain k hx
    let D : Set (Space 2) := compactnessDomain k
    let χ : TestFn := localizer k
    let U : ℕ → Distr := fun n => T (n + k) - T k
    let a : ℕ → ℝ≥0∞ := fun j => localNegSobolevENorm 1
      (T (j + k) - T (j + k + 1)) χ
    let E : ℝ≥0∞ := ∑' j, a j
    let M : ℝ := E.toReal
    have hEtop : E ≠ ⊤ := by simpa [E, a, χ] using hsum k
    have hM : 0 ≤ M := ENNReal.toReal_nonneg
    have hEof : ENNReal.ofReal M = E := ENNReal.ofReal_toReal hEtop
    have henergy : ∀ n, localNegSobolevSq 1 (U n) χ ≤ ENNReal.ofReal (M ^ 2) := by
      intro n
      have hseg := localNegSobolevENorm_incrementSegment_le_tsum T k 0 n (Nat.zero_le n)
      have hnormU : localNegSobolevENorm 1 (U n) χ ≤ E := by
        have hneg : T (n + k) - T k = -(T k - T (n + k)) := by abel
        change localNegSobolevENorm 1 (T (n + k) - T k) (localizer k) ≤ E
        rw [hneg, localNegSobolevENorm_neg]
        simpa [E, a, χ] using hseg
      rw [← localNegSobolevENorm_sq]
      calc
        localNegSobolevENorm 1 (U n) χ ^ 2 ≤ E ^ 2 := ENNReal.pow_le_pow_left hnormU
        _ = ENNReal.ofReal (M ^ 2) := by
          calc
            E ^ 2 = ENNReal.ofReal M ^ 2 := by rw [hEof]
            _ = ENNReal.ofReal (M ^ 2) := (ENNReal.ofReal_pow hM 2).symm
    have hpair : ∀ f (hf : IsTestFn D f), ∀ ε : ℝ, 0 < ε →
        ∃ N, ∀ n m, N ≤ n → N ≤ m →
          |U n (testFnOfRellich hf.1 hf.2.1) - U m (testFnOfRellich hf.1 hf.2.1)| ≤ ε := by
      intro f hf ε hε
      have hseq := localizer_pairing_cauchy T k (hsum k) hf
      rw [Metric.cauchySeq_iff] at hseq
      obtain ⟨N, hN⟩ := hseq ε hε
      refine ⟨N, fun n m hn hm => ?_⟩
      have hdist := hN n hn m hm
      have hreal : |T (n + k) (testFnOfRellich hf.1 hf.2.1) -
          T (m + k) (testFnOfRellich hf.1 hf.2.1)| < ε := by
        simpa only [Real.dist_eq] using hdist
      have hU : U n (testFnOfRellich hf.1 hf.2.1) - U m (testFnOfRellich hf.1 hf.2.1) =
          T (n + k) (testFnOfRellich hf.1 hf.2.1) -
            T (m + k) (testFnOfRellich hf.1 hf.2.1) := by
        simp [U]
      rw [hU]
      exact le_of_lt hreal
    obtain ⟨Gₖ, hGₖadd, hGₖsmul, hGₖbound, hGₖapprox⟩ :=
      exists_limit_distributionPairingFunctional_of_localEnergy
        (isDomain_compactnessDomain k) χ hχ hM (by norm_num : (1 : ℝ) < 2)
        U henergy hpair
    obtain ⟨m₀, C₀, hC₀, hbase⟩ := exists_distribution_compact_order_bound (T k) K
    obtain ⟨m₁, C₁, hC₁, hGₖjet⟩ :=
      exists_pairing_bound_by_compact_jet 1 M hM Gₖ D hGₖbound hGₖsmul K hKD
    let m := max m₀ m₁
    let A := M * (Real.sqrt C₁ + 1)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hmono (j : ℕ) (hj : j ≤ m) :
        ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K j ≤
          ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m := by
      let p : ℕ → Seminorm ℝ (ContDiffMapSupportedIn Plane ℝ ⊤ K) :=
        fun i => ContDiffMapSupportedIn.seminorm ℝ Plane ℝ ⊤ K i
      have hsub : Finset.Iic j ⊆ Finset.Iic m := by
        intro i hi
        exact Finset.mem_Iic.mpr
          ((Finset.mem_Iic.mp hi).trans hj)
      have heqj : (Finset.Iic j).sup p =
          ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K j := rfl
      have heqm : (Finset.Iic m).sup p =
          ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m := rfl
      rw [← heqj, ← heqm]
      exact Finset.sup_mono hsub
    refine ⟨m, C₀ + A, add_nonneg hC₀ hA, ?_⟩
    intro φ
    let f : Plane → ℝ := fun x => (φ x : ℝ)
    have hfD : IsTestFn D f := by
      refine ⟨φ.contDiff, φ.hasCompactSupport, ?_⟩
      exact φ.tsupport_subset.trans hKD
    let ψ : TestFn := testFnOfRellich hfD.1 hfD.2.1
    have hfU : IsTestFn Set.univ f := ⟨hfD.1, hfD.2.1, Set.subset_univ _⟩
    have hdecomp : G f = T k ψ + Gₖ f := by
      have hGlimShift : Tendsto (fun n => T (n + k) ψ) atTop (𝓝 (G f)) := by
        have h := (hGlim f hfU).comp (tendsto_add_atTop_nat k)
        have heq : (fun j => distributionFunctional (T (j + k)) f) =
            fun j => T (j + k) ψ := by
          funext j
          exact distributionFunctional_apply (T (j + k)) hfU
        change Tendsto (fun j => distributionFunctional (T (j + k)) f) atTop (𝓝 (G f)) at h
        rw [heq] at h
        exact h
      have hGₖpoint : Tendsto (fun n => U n ψ) atTop (𝓝 (Gₖ f)) := by
        apply Metric.tendsto_atTop.mpr
        intro ε hε
        obtain ⟨B, hB, hnormψ⟩ := exists_test_sobolev_norm_bound 2 ψ
        let η : ℝ := ε / (B + 1)
        have hη : 0 < η := by dsimp [η]; positivity
        obtain ⟨N, hN⟩ := hGₖapprox η hη
        refine ⟨N, fun n hn => ?_⟩
        let V : (Plane → ℝ) → ℝ := fun g =>
          distributionFunctional (U n) g - Gₖ g
        have hVsmul : ∀ (c : ℝ) g, IsTestFn D g →
            V (fun x => c * g x) = c * V g := by
          intro c g hg
          dsimp [V]
          rw [distributionFunctional_smul (U n)
              ⟨hg.1, hg.2.1, Set.subset_univ _⟩ c,
            hGₖsmul c g hg]
          ring
        have happly := abs_apply_le_negSobolevNorm (D := D) 2 B hB V hVsmul hfD hnormψ
        have hsmallNorm := hN n hn
        have hpair : ENNReal.ofReal |V f| ≤ ENNReal.ofReal B * ENNReal.ofReal η := by
          exact happly.trans (mul_le_mul_of_nonneg_left hsmallNorm (by positivity))
        have hprod : ENNReal.ofReal B * ENNReal.ofReal η < ENNReal.ofReal ε := by
          calc
            _ = ENNReal.ofReal (B * η) := (ENNReal.ofReal_mul hB.le).symm
            _ < ENNReal.ofReal ε := by
              rw [ENNReal.ofReal_lt_ofReal_iff hε]
              dsimp [η]
              have hden : 0 < B + 1 := by positivity
              calc
                B * (ε / (B + 1)) < (B + 1) * (ε / (B + 1)) := by
                  exact mul_lt_mul_of_pos_right (by linarith) (div_pos hε hden)
                _ = ε := by field_simp
        have hVlt : |V f| < ε :=
          (ENNReal.ofReal_lt_ofReal_iff hε).mp (hpair.trans_lt hprod)
        have hVeq : V f = U n ψ - Gₖ f := by
          dsimp [V]
          rw [distributionFunctional_apply (U n) hfD]
        simpa only [Real.dist_eq, hVeq] using hVlt
      have hsumlimit : Tendsto (fun n => T k ψ + U n ψ) atTop
          (𝓝 (T k ψ + Gₖ f)) := tendsto_const_nhds.add hGₖpoint
      have hseqeq : (fun n => T k ψ + U n ψ) = fun n => T (n + k) ψ := by
        funext n
        simp [U]
      have hsumlimit' : Tendsto (fun n => T (n + k) ψ) atTop
          (𝓝 (T k ψ + Gₖ f)) := by simpa only [hseqeq] using hsumlimit
      exact tendsto_nhds_unique hGlimShift hsumlimit'
    have hψeq : ψ = TestFunction.ofSupportedIn (Set.subset_univ _) φ := by
      apply TestFunction.ext
      intro x
      rfl
    have hbase' : |T k ψ| ≤ C₀ *
        ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m₀ φ := by
      simpa [Real.norm_eq_abs, hψeq] using hbase φ
    have hGₖ' : |Gₖ f| ≤ A * ‖compactTestJet K m₁ φ‖ := by
      simpa [A, f] using hGₖjet φ
    have hbaseMax : |T k ψ| ≤ C₀ *
        ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ :=
      hbase'.trans (mul_le_mul_of_nonneg_left (hmono m₀ (Nat.le_max_left _ _) φ) hC₀)
    have hGₖMax : |Gₖ f| ≤ A * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ := by
      exact hGₖ'.trans (mul_le_mul_of_nonneg_left
        (compactTestJet_norm_le_supSeminorm K m₁ φ |>.trans (hmono m₁ (Nat.le_max_right _ _) φ)) hA)
    calc
      |G f| ≤ |T k ψ| + |Gₖ f| := by rw [hdecomp]; exact abs_add_le _ _
      _ ≤ C₀ * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ +
          A * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ :=
        add_le_add hbaseMax hGₖMax
      _ = (C₀ + A) * ContDiffMapSupportedIn.supSeminorm ℝ Plane ℝ ⊤ K m φ := by ring
  obtain ⟨H, hH⟩ := exists_frozen_distribution_of_compact_pairing_bounds G hGadd hGsmul hcompactBound
  refine ⟨H, ?_⟩
  intro φ
  let f : Plane → ℝ := fun x => (φ x : ℝ)
  have hf : IsTestFn Set.univ f := ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩
  have hseq : (fun n => T n φ) = fun n => distributionFunctional (T n) f := by
    funext n
    symm
    exact distributionFunctional_apply (T n) hf
  rw [hH φ, hseq]
  exact hGlim f hf

/-- An expected local-energy Cauchy condition at every positive order gives a measurable distribution-valued limit, with the expected local energies of the approximation error tending to zero. -/
theorem exists_negSobolev_limit {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ) (F : ℝ → Ω → Distr)
    (hF : ∀ δ : ℝ, 0 < δ → ∀ φ : TestFn, Measurable[m] fun ω => F δ ω φ)
    (hC : ∀ a : ℝ, 0 < a → ∀ χ : TestFn,
      Tendsto (fun p : ℝ × ℝ => ∫⁻ ω, localNegSobolevSq a (F p.1 ω - F p.2 ω) χ ∂P)
        (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (𝓝 0)) :
    ∃ H : Ω → Distr, (∀ φ : TestFn, Measurable[m] fun ω => H ω φ) ∧
      ∀ a : ℝ, 0 < a → ∀ χ : TestFn,
        Tendsto (fun δ => ∫⁻ ω, localNegSobolevSq a (F δ ω - H ω) χ ∂P)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  classical
  have hdiagonal := @exists_sequence_expected_localizer_increment_bound
    Ω mΩ P (inferInstance : IsProbabilityMeasure P) F hC
  obtain ⟨δ, hδpos, hδtend, hbound⟩ := hdiagonal
  let T : ℕ → Ω → Distr := fun n ω => F (δ n) ω
  have hTmeas (n : ℕ) (φ : TestFn) : Measurable[m] fun ω => T n ω φ :=
    hF (δ n) (hδpos n) φ
  have hTmeasΩ (n : ℕ) (φ : TestFn) :
      @Measurable Ω ℝ mΩ Real.measurableSpace (fun ω => T n ω φ) :=
    Measurable.mono (ma := m) (ma' := mΩ) (mb := Real.measurableSpace)
      (mb' := Real.measurableSpace) (hTmeas n φ) hm le_rfl
  let E (k : ℕ) (ω : Ω) : ℝ≥0∞ := ∑' j,
    localNegSobolevSq 1 (T (j + k) ω - T (j + k + 1) ω) (localizer k) ^ (1 / 2 : ℝ)
  let good (ω : Ω) : Prop := ∀ k, E k ω < ⊤
  have hEmeas (k : ℕ) : Measurable[m] (E k) := by
    let : MeasurableSpace Ω := m
    apply Measurable.tsum
    intro j
    have henergy : Measurable (fun ω =>
        localNegSobolevSq 1 (T (j + k) ω - T (j + k + 1) ω) (localizer k)) := by
      apply measurable_localNegSobolevSq
      intro φ
      exact (hTmeas (j + k) φ).sub (hTmeas (j + k + 1) φ)
    simpa only [E, Function.comp_def] using
      (ENNReal.continuous_rpow_const.measurable.comp henergy)
  have hgoodSet : MeasurableSet[m] {ω | good ω} := by
    let : MeasurableSpace Ω := m
    have hI : MeasurableSet (⋂ k : ℕ, {ω | E k ω < ⊤}) :=
      MeasurableSet.iInter fun k => measurableSet_lt (hEmeas k) measurable_const
    convert hI using 1
    ext ω
    simp [good]
  have hgoodAE : ∀ᵐ ω ∂P, good ω := by
    have hAE (k : ℕ) : ∀ᵐ ω ∂P, E k ω < ⊤ := by
      simpa [E, T] using @ae_tsum_localizer_rpow_half_increment_lt_top
        Ω mΩ P (inferInstance : IsProbabilityMeasure P) T
        (fun n φ => hTmeasΩ n φ) hbound k
    filter_upwards [ae_all_iff.2 hAE] with ω hω
    exact hω
  have hdet (ω : Ω) (hω : good ω) : ∃ H : Distr,
      ∀ φ : TestFn, Tendsto (fun n => T n ω φ) atTop (𝓝 (H φ)) := by
    apply exists_frozen_distribution_limit_of_summable_localizer_increments
    intro k
    have hsum : (∑' j, localNegSobolevENorm 1
        (T (j + k) ω - T (j + k + 1) ω) (localizer k)) = E k ω := by
      apply tsum_congr
      intro j
      rw [localNegSobolevENorm_eq_rpow]
    rw [hsum]
    exact ne_of_lt (hω k)
  have hselected (ω : Ω) (hω : good ω) (φ : TestFn) :
      Tendsto (fun n => T n ω φ) atTop
        (𝓝 ((Classical.choose (hdet ω hω)) φ)) :=
    Classical.choose_spec (hdet ω hω) φ
  let H : Ω → Distr := fun ω =>
    if hω : good ω then Classical.choose (hdet ω hω) else 0
  have hHmeas (φ : TestFn) : Measurable[m] fun ω => H ω φ := by
    have hlim : StronglyMeasurable[m]
        (fun ω => limUnder atTop (fun n => T n ω φ)) := by
      exact StronglyMeasurable.limUnder fun n => (hTmeas n φ).stronglyMeasurable
    have hEq : (fun ω => H ω φ) = fun ω =>
        if good ω then limUnder atTop (fun n => T n ω φ) else 0 := by
      funext ω
      by_cases hω : good ω
      · simpa [H, hω] using (hselected ω hω φ).limUnder_eq.symm
      · simp [H, hω]
    rw [hEq]
    exact Measurable.ite hgoodSet hlim.measurable measurable_const
  have hHmeasΩ (φ : TestFn) :
      @Measurable Ω ℝ mΩ Real.measurableSpace (fun ω => H ω φ) :=
    Measurable.mono (ma := m) (ma' := mΩ) (mb := Real.measurableSpace)
      (mb' := Real.measurableSpace) (hHmeas φ) hm le_rfl
  have hHpair (ω : Ω) (hω : good ω) (φ : TestFn) :
      Tendsto (fun n => T n ω φ) atTop (𝓝 (H ω φ)) := by
    simpa [H, hω] using hselected ω hω φ
  have hFmeasΩ (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (φ : TestFn) :
      @Measurable Ω ℝ mΩ Real.measurableSpace (fun ω => F δ₀ ω φ) :=
    Measurable.mono (ma := m) (ma' := mΩ) (mb := Real.measurableSpace)
      (mb' := Real.measurableSpace) (hF δ₀ hδ₀ φ) hm le_rfl
  have hFatouFixed (δ₀ : ℝ) (hδ₀ : 0 < δ₀) (a : ℝ) (χ : TestFn) :
      ∫⁻ ω, localNegSobolevSq a (F δ₀ ω - H ω) χ ∂P ≤
        Filter.liminf (fun j => ∫⁻ ω, localNegSobolevSq a (F δ₀ ω - T j ω) χ ∂P) atTop := by
    exact @lintegral_localNegSobolevSq_le_liminf_of_ae_pairings Ω mΩ P
      (inferInstance : IsProbabilityMeasure P)
      (fun j ω => F δ₀ ω - T j ω) (fun ω => F δ₀ ω - H ω)
      (fun j φ => (hFmeasΩ δ₀ hδ₀ φ).sub (hTmeasΩ j φ))
      (fun φ => (hFmeasΩ δ₀ hδ₀ φ).sub (hHmeasΩ φ))
      (by
        filter_upwards [hgoodAE] with ω hω
        intro φ
        simpa only [sub_apply] using
          (tendsto_const_nhds.sub (hHpair ω hω φ)))
      a χ
  refine ⟨H, hHmeas, ?_⟩
  intro a ha χ
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, hr, hsmall⟩ := @exists_pos_radius_expected_localNegSobolevSq_lt
    Ω mΩ P (inferInstance : IsProbabilityMeasure P) F a χ (hC a ha χ) ε hε
  have hδsmall : ∀ᶠ n : ℕ in atTop, δ n < r :=
    hδtend.eventually (nhdsWithin_le_nhds (Iio_mem_nhds hr))
  filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds hr), self_mem_nhdsWithin] with δ₀ hδr hδ
  have hliminf : Filter.liminf
      (fun j => ∫⁻ ω, localNegSobolevSq a (F δ₀ ω - T j ω) χ ∂P) atTop ≤ ε := by
    apply Filter.liminf_le_of_frequently_le'
    have hsmallTail : ∀ᶠ j : ℕ in atTop,
        ∫⁻ ω, localNegSobolevSq a (F δ₀ ω - T j ω) χ ∂P ≤ ε := by
      filter_upwards [hδsmall] with j hj
      exact (hsmall δ₀ (δ j) hδ hδr (hδpos j) hj).le
    exact hsmallTail.frequently
  exact (hFatouFixed δ₀ hδ a χ).trans hliminf

end Critical2DKPZ.LocalSobolev

end
