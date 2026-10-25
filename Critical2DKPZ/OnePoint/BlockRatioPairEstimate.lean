/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioPairFactorization
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-! # Pair-integral estimates -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

private theorem coefficient_mul_pow_le_pow {D a α β : ℝ} {n : ℕ}
    (hD : 1 ≤ D) (ha : a ≤ D) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : 0 ≤ β) (hn : 1 ≤ n) :
    a * α ^ n ≤ (D * β) ^ n := by
  have hpow : α ^ n ≤ β ^ n := pow_le_pow_left₀ hα hαβ n
  have hDn : D ≤ D ^ n := by
    calc
      D = 1 * D := by ring
      _ ≤ D ^ (n - 1) * D :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ hD) (by linarith)
      _ = D ^ n := by rw [← pow_succ, Nat.sub_add_cancel hn]
  calc
    a * α ^ n ≤ D * α ^ n :=
      mul_le_mul_of_nonneg_right ha (pow_nonneg hα _)
    _ ≤ D * β ^ n :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    _ ≤ D ^ n * β ^ n :=
      mul_le_mul_of_nonneg_right hDn (pow_nonneg hβ _)
    _ = (D * β) ^ n := by rw [mul_pow]

private theorem pairComponent_totalIntervalLength_ge {r s : ℕ}
    {F G : Finset (ℕ × ℕ)} (hr : 1 ≤ r)
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s)
    {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G) :
    c.2 - c.1 ≤
      Finset.sum (restrictIntervalFamily F c) (fun I : ℕ × ℕ => I.2 - I.1) +
        Finset.sum (restrictIntervalFamily G c) (fun I : ℕ × ℕ => I.2 - I.1) := by
  classical
  let EF := (restrictIntervalFamily F c).biUnion fun I => Finset.Ico I.1 I.2
  let EG := (restrictIntervalFamily G c).biUnion fun I => Finset.Ico I.1 I.2
  have hcover : Finset.Ico c.1 c.2 ⊆ EF ∪ EG := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hc' := Finset.mem_filter.mp hc
    obtain ⟨I, hI, hleft, hright⟩ := hc'.2.2.1 i hi
    obtain ⟨d, hd, hdleft, hdright⟩ := interval_exists_pairComponent hr hF hG hI
    have hdi : d.1 ≤ i ∧ i < d.2 := by omega
    have hdc : d = c := by
      by_contra hne
      rcases pairComponents_span_disjoint hd hc hne with h | h <;> omega
    have hIcontained : c.1 ≤ I.1 ∧ I.2 ≤ c.2 := by
      simpa [hdc] using And.intro hdleft hdright
    rcases Finset.mem_union.mp hI with hIF | hIG
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_biUnion.mpr
      refine ⟨I, Finset.mem_filter.mpr ⟨hIF, ?_⟩, ?_⟩
      · exact hIcontained
      · exact Finset.mem_Ico.mpr ⟨hleft, hright⟩
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_biUnion.mpr
      refine ⟨I, Finset.mem_filter.mpr ⟨hIG, ?_⟩, ?_⟩
      · exact hIcontained
      · exact Finset.mem_Ico.mpr ⟨hleft, hright⟩
  have hEF : EF.card ≤
      Finset.sum (restrictIntervalFamily F c) (fun I : ℕ × ℕ => I.2 - I.1) := by
    dsimp [EF]
    calc
      _ ≤ Finset.sum (restrictIntervalFamily F c)
          (fun I : ℕ × ℕ => (Finset.Ico I.1 I.2).card) :=
        Finset.card_biUnion_le
      _ = Finset.sum (restrictIntervalFamily F c) (fun I : ℕ × ℕ => I.2 - I.1) := by
        apply Finset.sum_congr rfl
        intro I hI
        simp [Nat.card_Ico]
  have hEG : EG.card ≤
      Finset.sum (restrictIntervalFamily G c) (fun I : ℕ × ℕ => I.2 - I.1) := by
    dsimp [EG]
    calc
      _ ≤ Finset.sum (restrictIntervalFamily G c)
          (fun I : ℕ × ℕ => (Finset.Ico I.1 I.2).card) :=
        Finset.card_biUnion_le
      _ = Finset.sum (restrictIntervalFamily G c) (fun I : ℕ × ℕ => I.2 - I.1) := by
        apply Finset.sum_congr rfl
        intro I hI
        simp [Nat.card_Ico]
  have hcard : (Finset.Ico c.1 c.2).card ≤ EF.card + EG.card := by
    calc
      (Finset.Ico c.1 c.2).card ≤ (EF ∪ EG).card := Finset.card_le_card hcover
      _ ≤ EF.card + EG.card := Finset.card_union_le EF EG
  have hco : (Finset.Ico c.1 c.2).card = c.2 - c.1 := by
    simp [Nat.card_Ico]
  calc
    c.2 - c.1 = (Finset.Ico c.1 c.2).card := hco.symm
    _ ≤ EF.card + EG.card := hcard
    _ ≤ Finset.sum (restrictIntervalFamily F c) (fun I : ℕ × ℕ => I.2 - I.1) +
          Finset.sum (restrictIntervalFamily G c) (fun I : ℕ × ℕ => I.2 - I.1) :=
      Nat.add_le_add hEF hEG

private theorem pairComponent_single_interval_of_isolated {r s : ℕ}
    {F G : Finset (ℕ × ℕ)} (hr : 1 ≤ r)
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s)
    {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G)
    (hisolated : IsIsolatedComponent F G c) :
    (∃ I ∈ restrictIntervalFamily F c, I = (c.1, c.2) ∧
      restrictIntervalFamily G c = ∅) ∨
    (∃ I ∈ restrictIntervalFamily G c, I = (c.1, c.2) ∧
      restrictIntervalFamily F c = ∅) := by
  classical
  let Fc := restrictIntervalFamily F c
  let Gc := restrictIntervalFamily G c
  have hcount : Fc.card + Gc.card = 1 := by
    change (restrictIntervalFamily F c).card + (restrictIntervalFamily G c).card = 1
      at hisolated
    exact hisolated
  have hcases : (Fc.card = 1 ∧ Gc.card = 0) ∨ (Fc.card = 0 ∧ Gc.card = 1) := by
    omega
  have hbonds : ∀ i ∈ Finset.Ico c.1 c.2, PairBond F G i :=
    (Finset.mem_filter.mp hc).2.2.1
  have hspan : c.1 < c.2 := (Finset.mem_filter.mp hc).2.1
  have hcover (i : ℕ) (hi : i ∈ Finset.Ico c.1 c.2) :
      ∃ I ∈ Fc ∪ Gc, I.1 ≤ i ∧ i < I.2 := by
    obtain ⟨J, hJ, hleft, hright⟩ := hbonds i hi
    obtain ⟨d, hd, hdleft, hdright⟩ := interval_exists_pairComponent hr hF hG hJ
    have hi' := Finset.mem_Ico.mp hi
    have hdi : d.1 ≤ i ∧ i < d.2 := by omega
    have hdc : d = c := by
      by_contra hne
      rcases pairComponents_span_disjoint hd hc hne with h | h <;> omega
    have hbounds : c.1 ≤ J.1 ∧ J.2 ≤ c.2 := by
      simpa [hdc] using And.intro hdleft hdright
    rcases Finset.mem_union.mp hJ with hJF | hJG
    · exact ⟨J, Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hJF, hbounds⟩)),
        hleft, hright⟩
    · exact ⟨J, Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hJG, hbounds⟩)),
        hleft, hright⟩
  rcases hcases with hFcard | hGcard
  · obtain ⟨I, hFcEq⟩ := Finset.card_eq_one.mp hFcard.1
    have hI : I ∈ Fc := by rw [hFcEq]; simp
    have hGcEmpty : Gc = ∅ := Finset.card_eq_zero.mp hFcard.2
    have hIbounds : c.1 ≤ I.1 ∧ I.2 ≤ c.2 := Finset.mem_filter.mp hI |>.2
    have hfirst : I.1 ≤ c.1 := by
      obtain ⟨J, hJ, hleft, -⟩ := hcover c.1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
      have hJeq : J = I := by
        rcases Finset.mem_union.mp hJ with hJFc | hJGc
        · rw [hFcEq] at hJFc
          exact Finset.mem_singleton.mp hJFc
        · simp [hGcEmpty] at hJGc
      rw [hJeq] at hleft
      exact hleft
    have hlast : c.2 ≤ I.2 := by
      obtain ⟨J, hJ, -, hright⟩ := hcover (c.2 - 1)
        (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      have hJeq : J = I := by
        rcases Finset.mem_union.mp hJ with hJFc | hJGc
        · rw [hFcEq] at hJFc
          exact Finset.mem_singleton.mp hJFc
        · simp [hGcEmpty] at hJGc
      rw [hJeq] at hright
      omega
    refine Or.inl ⟨I, hI, ?_, hGcEmpty⟩
    exact Prod.ext (by omega) (by omega)

  · obtain ⟨I, hGcEq⟩ := Finset.card_eq_one.mp hGcard.2
    have hI : I ∈ Gc := by rw [hGcEq]; simp
    have hFcEmpty : Fc = ∅ := Finset.card_eq_zero.mp hGcard.1
    have hIbounds : c.1 ≤ I.1 ∧ I.2 ≤ c.2 := Finset.mem_filter.mp hI |>.2
    have hfirst : I.1 ≤ c.1 := by
      obtain ⟨J, hJ, hleft, -⟩ := hcover c.1 (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
      have hJeq : J = I := by
        rcases Finset.mem_union.mp hJ with hJFc | hJGc
        · simp [hFcEmpty] at hJFc
        · rw [hGcEq] at hJGc
          exact Finset.mem_singleton.mp hJGc
      rw [hJeq] at hleft
      exact hleft
    have hlast : c.2 ≤ I.2 := by
      obtain ⟨J, hJ, -, hright⟩ := hcover (c.2 - 1)
        (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      have hJeq : J = I := by
        rcases Finset.mem_union.mp hJ with hJFc | hJGc
        · simp [hFcEmpty] at hJFc
        · rw [hGcEq] at hJGc
          exact Finset.mem_singleton.mp hJGc
      rw [hJeq] at hright
      omega
    refine Or.inr ⟨I, hI, ?_, hFcEmpty⟩
    exact Prod.ext (by omega) (by omega)

/-- For an isolated component, the pair-component factor equals the corrector. -/
theorem pairComponentFactor_eq_corrector_of_isolated {r s : ℕ}
    (β : ℝ) (t : ℕ → ℕ) {F G : Finset (ℕ × ℕ)}
    (hr : 1 ≤ r) (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s)
    {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G)
    (hisolated : IsIsolatedComponent F G c) (ω : Disorder) :
    pairComponentFactor β t F G c ω = truncatedCorrector β t c.1 c.2 ω := by
  classical
  rcases pairComponent_single_interval_of_isolated hr hF hG hc hisolated with hleft | hright
  · obtain ⟨I, hI, hIeq, hGempty⟩ := hleft
    have hFprod :
        (∏ J ∈ restrictIntervalFamily F c, truncatedCorrector β t J.1 J.2 ω) =
          truncatedCorrector β t c.1 c.2 ω := by
      rw [show restrictIntervalFamily F c = {I} from by
        have hcard : (restrictIntervalFamily F c).card = 1 := by
          change (restrictIntervalFamily F c).card + (restrictIntervalFamily G c).card = 1
            at hisolated
          rw [hGempty, Finset.card_empty, Nat.add_zero] at hisolated
          exact hisolated
        obtain ⟨J, hEq⟩ := Finset.card_eq_one.mp hcard
        rw [hEq] at hI
        have hJI : J = I := (Finset.mem_singleton.mp hI).symm
        simpa [hJI] using hEq]
      simp [hIeq]
    have hGprod :
        (∏ J ∈ restrictIntervalFamily G c, truncatedCorrector β t J.1 J.2 ω) = 1 := by
      rw [hGempty]
      simp
    have hgood (ω : Disorder) :
        truncatedCorrector β t c.1 c.2 ω *
            ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω =
          truncatedCorrector β t c.1 c.2 ω := by
      by_cases hω : ω ∈ blockGoodSet β t c.1 c.2
      · have hω' : ∀ i ∈ Finset.Icc c.1 c.2,
            |blockMass β t i ω - 1| ≤ 1 / 2 := hω
        have hprod : ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          change (if |blockMass β t i ω - 1| ≤ 1 / 2 then 1 else 0) = 1
          split_ifs with h
          · rfl
          · exact False.elim (h (hω' i hi))
        rw [hprod]
        ring
      · have hω' : ¬ ∀ i ∈ Finset.Icc c.1 c.2,
            |blockMass β t i ω - 1| ≤ 1 / 2 := by simpa [blockGoodSet] using hω
        push Not at hω'
        obtain ⟨i, hi, hbad⟩ := hω'
        have hM : truncatedInverse β t i ω = 0 := by
          unfold truncatedInverse
          split_ifs with h
          · exact False.elim (by linarith)
          · rfl
        have hprod : ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω = 0 :=
          Finset.prod_eq_zero hi hM
        have hcorrector : truncatedCorrector β t c.1 c.2 ω = 0 := by
          rw [truncatedCorrector]
          simp [hprod]
        simp [hcorrector, pairGoodBlockFactor]
    unfold pairComponentFactor
    rw [hFprod, hGprod]
    simpa [mul_one] using hgood ω
  · obtain ⟨I, hI, hIeq, hFempty⟩ := hright
    have hFprod :
        (∏ J ∈ restrictIntervalFamily F c, truncatedCorrector β t J.1 J.2 ω) = 1 := by
      rw [hFempty]
      simp
    have hGprod :
        (∏ J ∈ restrictIntervalFamily G c, truncatedCorrector β t J.1 J.2 ω) =
          truncatedCorrector β t c.1 c.2 ω := by
      rw [show restrictIntervalFamily G c = {I} from by
        have hcard : (restrictIntervalFamily G c).card = 1 := by
          change (restrictIntervalFamily F c).card + (restrictIntervalFamily G c).card = 1
            at hisolated
          rw [hFempty, Finset.card_empty, Nat.zero_add] at hisolated
          exact hisolated
        obtain ⟨J, hEq⟩ := Finset.card_eq_one.mp hcard
        rw [hEq] at hI
        have hJI : J = I := (Finset.mem_singleton.mp hI).symm
        simpa [hJI] using hEq]
      simp [hIeq]
    have hgood (ω : Disorder) :
        truncatedCorrector β t c.1 c.2 ω *
            ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω =
          truncatedCorrector β t c.1 c.2 ω := by
      by_cases hω : ω ∈ blockGoodSet β t c.1 c.2
      · have hω' : ∀ i ∈ Finset.Icc c.1 c.2,
            |blockMass β t i ω - 1| ≤ 1 / 2 := hω
        have hprod : ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω = 1 := by
          apply Finset.prod_eq_one
          intro i hi
          change (if |blockMass β t i ω - 1| ≤ 1 / 2 then 1 else 0) = 1
          split_ifs with h
          · rfl
          · exact False.elim (h (hω' i hi))
        rw [hprod]
        ring
      · have hω' : ¬ ∀ i ∈ Finset.Icc c.1 c.2,
            |blockMass β t i ω - 1| ≤ 1 / 2 := by simpa [blockGoodSet] using hω
        push Not at hω'
        obtain ⟨i, hi, hbad⟩ := hω'
        have hM : truncatedInverse β t i ω = 0 := by
          unfold truncatedInverse
          split_ifs with h
          · exact False.elim (by linarith)
          · rfl
        have hprod : ∏ i ∈ Finset.Icc c.1 c.2, truncatedInverse β t i ω = 0 :=
          Finset.prod_eq_zero hi hM
        have hcorrector : truncatedCorrector β t c.1 c.2 ω = 0 := by
          rw [truncatedCorrector]
          simp [hprod]
        simp [hcorrector, pairGoodBlockFactor]
    unfold pairComponentFactor
    rw [hFprod, hGprod]
    simpa [one_mul] using hgood ω

private theorem pairComponentFactor_abs_integral_le_of {r s K : ℕ}
    (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKs : s < K)
    {F G : Finset (ℕ × ℕ)} (hr : 1 ≤ r) (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) {c : ℕ × ℕ}
    (hc : c ∈ pairComponents r s F G)
    (hMean : |∫ ω, truncatedCorrector β t c.1 c.2 ω ∂disorderLaw| ≤
      γ ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2))
    (hSq : ∀ I ∈ restrictIntervalFamily F c ∪ restrictIntervalFamily G c,
      ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
        (γ ^ (I.2 - I.1) / ((K : ℝ) - c.2)) ^ 2) :
    |∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw| ≤
      componentWeight γ K F G c := by
  classical
  let Fc := restrictIntervalFamily F c
  let Gc := restrictIntervalFamily G c
  let d : ℝ := (K : ℝ) - c.2
  have hc' := Finset.mem_filter.mp hc
  have hcspan := Finset.mem_product.mp hc'.1
  have hcStart := Finset.mem_Icc.mp hcspan.1
  have hcStop := Finset.mem_Icc.mp hcspan.2
  have hdpos : 0 < d := by
    dsimp [d]
    have hnat : c.2 < K := lt_of_le_of_lt hcStop.2 hKs
    have hcast : (c.2 : ℝ) < (K : ℝ) := by exact_mod_cast hnat
    linarith
  have hdone : 1 ≤ d := by
    dsimp [d]
    have hnat : 1 ≤ K - c.2 := by omega
    rw [← Nat.cast_sub (by omega : c.2 ≤ K)]
    exact_mod_cast hnat
  by_cases hisolated : IsIsolatedComponent F G c
  · have heq (ω : Disorder) : pairComponentFactor β t F G c ω =
        truncatedCorrector β t c.1 c.2 ω :=
      pairComponentFactor_eq_corrector_of_isolated β t hr hF hG hc hisolated ω
    have hIntegralEq :
        ∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw =
          ∫ ω, truncatedCorrector β t c.1 c.2 ω ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall heq
    rw [hIntegralEq]
    have hweight : componentWeight γ K F G c =
        γ ^ (c.2 - c.1) / d ^ ((3 : ℝ) / 2) := by
      unfold componentWeight
      simp [hisolated, d, Real.rpow_neg (le_of_lt hdpos), div_eq_mul_inv]
    rw [hweight]
    exact hMean
  · have hFc : Fc ∈ intervalFamilies c.1 c.2 := restrictIntervalFamily_mem hF
    have hGc : Gc ∈ intervalFamilies c.1 c.2 := restrictIntervalFamily_mem hG
    have hlength := pairComponent_totalIntervalLength_ge hr hF hG hc
    have hLpos : 1 ≤ c.2 - c.1 := by omega
    have hsumLenPos : 1 ≤
        Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1) +
          Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1) := by
      exact le_trans hLpos hlength
    have hnonempty : 0 < Fc.card + Gc.card := by
      by_contra hn
      have hFc0 : Fc = ∅ := Finset.card_eq_zero.mp (by omega)
      have hGc0 : Gc = ∅ := Finset.card_eq_zero.mp (by omega)
      simp [hFc0, hGc0] at hsumLenPos
    have hcount : 2 ≤ Fc.card + Gc.card := by
      have hisolatedCount : Fc.card + Gc.card ≠ 1 := by
        intro hcountOne
        apply hisolated
        change Fc.card + Gc.card = 1
        exact hcountOne
      omega
    let m : ℕ × ℕ → ℝ := fun I =>
      ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw
    let U : Disorder → ℝ := fun ω =>
      ∏ I ∈ Fc, truncatedCorrector β t I.1 I.2 ω
    let V : Disorder → ℝ := fun ω =>
      ∏ I ∈ Gc, truncatedCorrector β t I.1 I.2 ω
    let W : Disorder → ℝ := fun ω => ∏ i ∈ Finset.Icc c.1 c.2,
      pairGoodBlockFactor β t i ω
    have hUmem : MemLp U 2 disorderLaw := by
      simpa [U, Fc] using memLp_pairFamilyCorrectorProduct_two β t ht Fc hFc
    have hVmem : MemLp V 2 disorderLaw := by
      simpa [V, Gc] using memLp_pairFamilyCorrectorProduct_two β t ht Gc hGc
    have hUint : Integrable (fun ω => U ω * V ω) disorderLaw := by
      have hmem := Polymer.memLp_mul_double 1
        (by simpa only [mul_one] using hUmem)
        (by simpa only [mul_one] using hVmem)
      exact hmem.integrable (by norm_num)
    have hmajor : Integrable (fun ω => |U ω| * |V ω|) disorderLaw := by
      apply hUint.norm.congr
      filter_upwards [] with ω
      simp [Real.norm_eq_abs]
    have hWbound (ω : Disorder) : 0 ≤ W ω ∧ W ω ≤ 1 := by
      constructor
      · dsimp [W]
        apply Finset.prod_nonneg
        intro i hi
        dsimp [pairGoodBlockFactor]
        split_ifs <;> norm_num
      · dsimp [W]
        apply Finset.prod_le_one₀
        · intro i hi
          dsimp [pairGoodBlockFactor]
          split_ifs <;> norm_num
        · intro i hi
          dsimp [pairGoodBlockFactor]
          split_ifs <;> norm_num
    have hpoint (ω : Disorder) :
        |pairComponentFactor β t F G c ω| ≤ |U ω| * |V ω| := by
      have heq : pairComponentFactor β t F G c ω = U ω * V ω * W ω := by
        dsimp [pairComponentFactor, U, V, W, Fc, Gc]
      rw [heq, abs_mul, abs_mul]
      calc
        |U ω| * |V ω| * |W ω| ≤ |U ω| * |V ω| * 1 :=
          mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith [hWbound ω],
            hWbound ω |>.2⟩) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |U ω| * |V ω| := by ring
    have hfactorInt : Integrable (pairComponentFactor β t F G c) disorderLaw :=
      integrable_pairComponentFactor β t ht hF hG c
    have hUmem' : MemLp U (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
      simpa using hUmem
    have hVmem' : MemLp V (ENNReal.ofReal (2 : ℝ)) disorderLaw := by
      simpa using hVmem
    have hholder := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
      Real.HolderConjugate.two_two hUmem' hVmem'
    let X : ℝ := ∫ ω, U ω ^ 2 ∂disorderLaw
    let Y : ℝ := ∫ ω, V ω ^ 2 ∂disorderLaw
    have hXnonneg : 0 ≤ X := by
      dsimp [X]
      exact integral_nonneg fun ω => sq_nonneg (U ω)
    have hYnonneg : 0 ≤ Y := by
      dsimp [Y]
      exact integral_nonneg fun ω => sq_nonneg (V ω)
    have hnormU : ∫ ω, ‖U ω‖ ^ (2 : ℝ) ∂disorderLaw = X := by
      dsimp [X]
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [sq_abs]
    have hnormV : ∫ ω, ‖V ω‖ ^ (2 : ℝ) ∂disorderLaw = Y := by
      dsimp [Y]
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [sq_abs]
    rw [hnormU, hnormV] at hholder
    have hholder' : ∫ ω, |U ω| * |V ω| ∂disorderLaw ≤
        Real.sqrt X * Real.sqrt Y := by
      simpa only [Real.norm_eq_abs, Real.sqrt_eq_rpow] using hholder
    have hXeq : X = ∏ I ∈ Fc, m I := by
      dsimp [X, U]
      simpa [m, Fc] using integral_pairFamilyCorrectorProduct_sq_eq β t ht Fc hFc
    have hYeq : Y = ∏ I ∈ Gc, m I := by
      dsimp [Y, V]
      simpa [m, Gc] using integral_pairFamilyCorrectorProduct_sq_eq β t ht Gc hGc
    have hmnonneg (I : ℕ × ℕ) (hI : I ∈ Fc ∪ Gc) : 0 ≤ m I := by
      dsimp [m]
      exact integral_nonneg fun ω => sq_nonneg (truncatedCorrector β t I.1 I.2 ω)
    have hrootX : Real.sqrt X ≤ ∏ I ∈ Fc, γ ^ (I.2 - I.1) / d := by
      rw [hXeq, Real.sqrt_prod Fc (fun I hI => hmnonneg I (Finset.mem_union.mpr (Or.inl hI)))]
      apply Finset.prod_le_prod₀
      · intro I hI
        exact Real.sqrt_nonneg _
      · intro I hI
        have hmoment := hSq I (Finset.mem_union.mpr (Or.inl hI))
        have htargetNonneg : 0 ≤ γ ^ (I.2 - I.1) / d :=
          div_nonneg (pow_nonneg hγ0 _) (le_of_lt hdpos)
        exact Real.sqrt_le_iff.mpr ⟨htargetNonneg, by simpa [m] using hmoment⟩
    have hrootY : Real.sqrt Y ≤ ∏ I ∈ Gc, γ ^ (I.2 - I.1) / d := by
      rw [hYeq, Real.sqrt_prod Gc (fun I hI => hmnonneg I (Finset.mem_union.mpr (Or.inr hI)))]
      apply Finset.prod_le_prod₀
      · intro I hI
        exact Real.sqrt_nonneg _
      · intro I hI
        have hmoment := hSq I (Finset.mem_union.mpr (Or.inr hI))
        have htargetNonneg : 0 ≤ γ ^ (I.2 - I.1) / d :=
          div_nonneg (pow_nonneg hγ0 _) (le_of_lt hdpos)
        exact Real.sqrt_le_iff.mpr ⟨htargetNonneg, by simpa [m] using hmoment⟩
    have hprodF : (∏ I ∈ Fc, γ ^ (I.2 - I.1) / d) =
        γ ^ (Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1)) / d ^ Fc.card := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      simp
    have hprodG : (∏ I ∈ Gc, γ ^ (I.2 - I.1) / d) =
        γ ^ (Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1)) / d ^ Gc.card := by
      rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
      simp
    have hsumLen := pairComponent_totalIntervalLength_ge hr hF hG hc
    let L := c.2 - c.1
    let n := Fc.card + Gc.card
    let q := Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1) +
      Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1)
    have hLq : L ≤ q := by simpa [L, q, Fc, Gc] using hsumLen
    have hqPow : γ ^ q ≤ γ ^ L := by
      rw [← Nat.sub_add_cancel hLq, pow_add]
      calc
        γ ^ (q - L) * γ ^ L ≤ 1 * γ ^ L :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ hγ0 hγ1) (pow_nonneg hγ0 _)
        _ = γ ^ L := one_mul _
    have hn : 2 ≤ n := by simpa [n, Fc, Gc] using hcount
    have hdPow : d ^ 2 ≤ d ^ n := by
      have hpow : 1 ≤ d ^ (n - 2) := one_le_pow₀ hdone
      rw [← Nat.sub_add_cancel hn, pow_add]
      calc
        d ^ 2 ≤ d ^ 2 * d ^ (n - 2) :=
          calc
            d ^ 2 = d ^ 2 * 1 := by ring
            _ ≤ d ^ 2 * d ^ (n - 2) :=
              mul_le_mul_of_nonneg_left hpow (sq_nonneg d)
        _ = d ^ (n - 2) * d ^ 2 := by ring
    have hprodBound :
        (∏ I ∈ Fc, γ ^ (I.2 - I.1) / d) *
            ∏ I ∈ Gc, γ ^ (I.2 - I.1) / d ≤ γ ^ L / d ^ 2 := by
      rw [hprodF, hprodG]
      have hnum : γ ^ (Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1)) *
          γ ^ (Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1)) = γ ^ q := by
        dsimp [q]
        rw [← pow_add]
      have hden : d ^ Fc.card * d ^ Gc.card = d ^ n := by
        dsimp [n]
        rw [← pow_add]
      have hratio :
          (γ ^ (Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1)) / d ^ Fc.card) *
              (γ ^ (Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1)) / d ^ Gc.card) =
            γ ^ q / d ^ n := by
        rw [← hnum, ← hden]
        field_simp [ne_of_gt (pow_pos hdpos _)]
      rw [hratio]
      have hdiv1 : γ ^ q / d ^ n ≤ γ ^ L / d ^ n :=
        div_le_div_of_nonneg_right hqPow (by positivity)
      have hdiv2 : γ ^ L / d ^ n ≤ γ ^ L / d ^ 2 :=
        div_le_div_of_nonneg_left (pow_nonneg hγ0 _) (by positivity) hdPow
      exact hdiv1.trans hdiv2
    have hpairBound :
        ∫ ω, |U ω| * |V ω| ∂disorderLaw ≤ γ ^ L / d ^ 2 := by
      calc
        ∫ ω, |U ω| * |V ω| ∂disorderLaw ≤ Real.sqrt X * Real.sqrt Y := hholder'
        _ ≤ (∏ I ∈ Fc, γ ^ (I.2 - I.1) / d) *
              ∏ I ∈ Gc, γ ^ (I.2 - I.1) / d :=
          mul_le_mul hrootX hrootY (Real.sqrt_nonneg _) (by
            positivity)
        _ ≤ γ ^ L / d ^ 2 := hprodBound
    have habsInt := calc
      |∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw| ≤
          ∫ ω, |pairComponentFactor β t F G c ω| ∂disorderLaw := abs_integral_le_integral_abs
      _ ≤ ∫ ω, |U ω| * |V ω| ∂disorderLaw := integral_mono hfactorInt.abs hmajor hpoint
      _ ≤ γ ^ L / d ^ 2 := hpairBound
    have hweight : componentWeight γ K F G c = γ ^ L / d ^ 2 := by
      unfold componentWeight
      simp [hisolated, d, L, Real.rpow_neg (le_of_lt hdpos),
        div_eq_mul_inv]
    rw [hweight]
    exact habsInt

/-- For a component containing at least two intervals, the product of the two absolute corrector products is integrable and satisfies a Cauchy–Schwarz bound. -/
theorem pairComponent_correctorProduct_abs_mul_integral_le_of {r s K : ℕ}
    (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hKs : s < K)
    {F G : Finset (ℕ × ℕ)} (hr : 1 ≤ r) (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) {c : ℕ × ℕ}
    (hc : c ∈ pairComponents r s F G)
    (hNotIso : ¬ IsIsolatedComponent F G c)
    (hSq : ∀ I ∈ restrictIntervalFamily F c ∪ restrictIntervalFamily G c,
      ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
        (γ ^ (I.2 - I.1) / ((K : ℝ) - c.2)) ^ 2) :
    Integrable
      (fun ω =>
        |∏ I ∈ restrictIntervalFamily F c,
          truncatedCorrector β t I.1 I.2 ω| *
        |∏ I ∈ restrictIntervalFamily G c,
          truncatedCorrector β t I.1 I.2 ω|)
      disorderLaw ∧
    ∫ ω,
      |∏ I ∈ restrictIntervalFamily F c,
        truncatedCorrector β t I.1 I.2 ω| *
      |∏ I ∈ restrictIntervalFamily G c,
        truncatedCorrector β t I.1 I.2 ω| ∂disorderLaw ≤
      γ ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ 2 := by
  classical
  let Fc := restrictIntervalFamily F c
  let Gc := restrictIntervalFamily G c
  have hc' := Finset.mem_filter.mp hc
  have hcspan := Finset.mem_product.mp hc'.1
  have hcStop := Finset.mem_Icc.mp hcspan.2
  let d : ℝ := (K : ℝ) - c.2
  have hdpos : 0 < d := by
    dsimp [d]
    have hnat : c.2 < K := lt_of_le_of_lt hcStop.2 hKs
    exact sub_pos.mpr (by exact_mod_cast hnat)
  have hdone : 1 ≤ d := by
    dsimp [d]
    have hnat : 1 ≤ K - c.2 := by omega
    rw [← Nat.cast_sub (by omega : c.2 ≤ K)]
    exact_mod_cast hnat
  have hFc : Fc ∈ intervalFamilies c.1 c.2 := restrictIntervalFamily_mem hF
  have hGc : Gc ∈ intervalFamilies c.1 c.2 := restrictIntervalFamily_mem hG
  have hlength := pairComponent_totalIntervalLength_ge hr hF hG hc
  have hLpos : 1 ≤ c.2 - c.1 := by omega
  have hsumLenPos : 1 ≤
      Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1) +
        Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1) := le_trans hLpos hlength
  have hnonempty : 0 < Fc.card + Gc.card := by
    by_contra hn
    have hFc0 : Fc = ∅ := Finset.card_eq_zero.mp (by omega)
    have hGc0 : Gc = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [hFc0, hGc0] at hsumLenPos
  have hcount : 2 ≤ Fc.card + Gc.card := by
    have hnotone : Fc.card + Gc.card ≠ 1 := by
      intro hcount
      apply hNotIso
      change Fc.card + Gc.card = 1
      exact hcount
    omega
  let m : ℕ × ℕ → ℝ := fun I =>
    ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw
  let U : Disorder → ℝ := fun ω =>
    ∏ I ∈ Fc, truncatedCorrector β t I.1 I.2 ω
  let V : Disorder → ℝ := fun ω =>
    ∏ I ∈ Gc, truncatedCorrector β t I.1 I.2 ω
  have hUmem : MemLp U 2 disorderLaw := by
    simpa [U, Fc] using memLp_pairFamilyCorrectorProduct_two β t ht Fc hFc
  have hVmem : MemLp V 2 disorderLaw := by
    simpa [V, Gc] using memLp_pairFamilyCorrectorProduct_two β t ht Gc hGc
  have hUVint : Integrable (fun ω => U ω * V ω) disorderLaw := by
    have hmem := Polymer.memLp_mul_double 1
      (by simpa only [mul_one] using hUmem)
      (by simpa only [mul_one] using hVmem)
    exact hmem.integrable (by norm_num)
  have hmajor : Integrable (fun ω => |U ω| * |V ω|) disorderLaw := by
    apply hUVint.norm.congr
    filter_upwards [] with ω
    simp [Real.norm_eq_abs]
  have hUmem' : MemLp U (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hUmem
  have hVmem' : MemLp V (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hVmem
  have hholder := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    Real.HolderConjugate.two_two hUmem' hVmem'
  let X : ℝ := ∫ ω, U ω ^ 2 ∂disorderLaw
  let Y : ℝ := ∫ ω, V ω ^ 2 ∂disorderLaw
  have hXnonneg : 0 ≤ X := by dsimp [X]; exact integral_nonneg fun ω => sq_nonneg (U ω)
  have hYnonneg : 0 ≤ Y := by dsimp [Y]; exact integral_nonneg fun ω => sq_nonneg (V ω)
  have hnormU : ∫ ω, ‖U ω‖ ^ (2 : ℝ) ∂disorderLaw = X := by
    dsimp [X]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [sq_abs]
  have hnormV : ∫ ω, ‖V ω‖ ^ (2 : ℝ) ∂disorderLaw = Y := by
    dsimp [Y]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [sq_abs]
  rw [hnormU, hnormV] at hholder
  have hholder' :
      ∫ ω, |U ω| * |V ω| ∂disorderLaw ≤ Real.sqrt X * Real.sqrt Y := by
    simpa only [Real.norm_eq_abs, Real.sqrt_eq_rpow] using hholder
  have hXeq : X = ∏ I ∈ Fc, m I := by
    dsimp [X, U]
    simpa [m, Fc] using integral_pairFamilyCorrectorProduct_sq_eq β t ht Fc hFc
  have hYeq : Y = ∏ I ∈ Gc, m I := by
    dsimp [Y, V]
    simpa [m, Gc] using integral_pairFamilyCorrectorProduct_sq_eq β t ht Gc hGc
  have hmnonneg (I : ℕ × ℕ) (hI : I ∈ Fc ∪ Gc) : 0 ≤ m I := by
    dsimp [m]
    exact integral_nonneg fun ω => sq_nonneg (truncatedCorrector β t I.1 I.2 ω)
  have hrootX : Real.sqrt X ≤ ∏ I ∈ Fc, γ ^ (I.2 - I.1) / d := by
    rw [hXeq, Real.sqrt_prod Fc
      (fun I hI => hmnonneg I (Finset.mem_union.mpr (Or.inl hI)))]
    apply Finset.prod_le_prod₀
    · intro I hI
      exact Real.sqrt_nonneg _
    · intro I hI
      have hmoment := hSq I (Finset.mem_union.mpr (Or.inl hI))
      have htarget : 0 ≤ γ ^ (I.2 - I.1) / d :=
        div_nonneg (pow_nonneg hγ0 _) (le_of_lt hdpos)
      exact Real.sqrt_le_iff.mpr ⟨htarget, by simpa [m] using hmoment⟩
  have hrootY : Real.sqrt Y ≤ ∏ I ∈ Gc, γ ^ (I.2 - I.1) / d := by
    rw [hYeq, Real.sqrt_prod Gc
      (fun I hI => hmnonneg I (Finset.mem_union.mpr (Or.inr hI)))]
    apply Finset.prod_le_prod₀
    · intro I hI
      exact Real.sqrt_nonneg _
    · intro I hI
      have hmoment := hSq I (Finset.mem_union.mpr (Or.inr hI))
      have htarget : 0 ≤ γ ^ (I.2 - I.1) / d :=
        div_nonneg (pow_nonneg hγ0 _) (le_of_lt hdpos)
      exact Real.sqrt_le_iff.mpr ⟨htarget, by simpa [m] using hmoment⟩
  have hprodF : (∏ I ∈ Fc, γ ^ (I.2 - I.1) / d) =
      γ ^ (Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1)) / d ^ Fc.card := by
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    simp
  have hprodG : (∏ I ∈ Gc, γ ^ (I.2 - I.1) / d) =
      γ ^ (Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1)) / d ^ Gc.card := by
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
    simp
  let L := c.2 - c.1
  let n := Fc.card + Gc.card
  let q := Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1) +
    Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1)
  have hLq : L ≤ q := by simpa [L, q, Fc, Gc] using hlength
  have hqPow : γ ^ q ≤ γ ^ L := by
    rw [← Nat.sub_add_cancel hLq, pow_add]
    calc
      γ ^ (q - L) * γ ^ L ≤ 1 * γ ^ L :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hγ0 hγ1) (pow_nonneg hγ0 _)
      _ = γ ^ L := one_mul _
  have hn : 2 ≤ n := by simpa [n, Fc, Gc] using hcount
  have hdPow : d ^ 2 ≤ d ^ n := by
    have hpow : 1 ≤ d ^ (n - 2) := one_le_pow₀ hdone
    rw [← Nat.sub_add_cancel hn, pow_add]
    calc
      d ^ 2 ≤ d ^ 2 * d ^ (n - 2) := by
        calc
          d ^ 2 = d ^ 2 * 1 := by ring
          _ ≤ d ^ 2 * d ^ (n - 2) :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg d)
      _ = d ^ (n - 2) * d ^ 2 := by ring
  have hprodBound :
      (∏ I ∈ Fc, γ ^ (I.2 - I.1) / d) *
        ∏ I ∈ Gc, γ ^ (I.2 - I.1) / d ≤ γ ^ L / d ^ 2 := by
    rw [hprodF, hprodG]
    have hnum : γ ^ (Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1)) *
        γ ^ (Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1)) = γ ^ q := by
      dsimp [q]
      rw [← pow_add]
    have hden : d ^ Fc.card * d ^ Gc.card = d ^ n := by
      dsimp [n]
      rw [← pow_add]
    have hratio :
        (γ ^ (Finset.sum Fc (fun I : ℕ × ℕ => I.2 - I.1)) / d ^ Fc.card) *
          (γ ^ (Finset.sum Gc (fun I : ℕ × ℕ => I.2 - I.1)) / d ^ Gc.card) =
            γ ^ q / d ^ n := by
      rw [← hnum, ← hden]
      field_simp [ne_of_gt (pow_pos hdpos _)]
    rw [hratio]
    have hdiv1 : γ ^ q / d ^ n ≤ γ ^ L / d ^ n :=
      div_le_div_of_nonneg_right hqPow (by positivity)
    have hdiv2 : γ ^ L / d ^ n ≤ γ ^ L / d ^ 2 :=
      div_le_div_of_nonneg_left (pow_nonneg hγ0 _) (by positivity) hdPow
    exact hdiv1.trans hdiv2
  have hbound : ∫ ω, |U ω| * |V ω| ∂disorderLaw ≤ γ ^ L / d ^ 2 := by
    calc
      ∫ ω, |U ω| * |V ω| ∂disorderLaw ≤ Real.sqrt X * Real.sqrt Y := hholder'
      _ ≤ (∏ I ∈ Fc, γ ^ (I.2 - I.1) / d) *
            ∏ I ∈ Gc, γ ^ (I.2 - I.1) / d :=
        mul_le_mul hrootX hrootY (Real.sqrt_nonneg _) (by positivity)
      _ ≤ γ ^ L / d ^ 2 := hprodBound
  exact ⟨hmajor, by simpa [U, V, Fc, Gc, L] using hbound⟩

private theorem setIntegral_familyTerm_mul_eq_pairFactorIntegrals {r s : ℕ}
    (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t) (hr : 1 ≤ r)
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) :
    ∫ ω in blockGoodSet β t r s, familyTerm β t F ω * familyTerm β t G ω ∂disorderLaw =
      ∏ x : pairFactorIndex r s F G,
        ∫ ω, pairFactorValue β t F G x ω ∂disorderLaw := by
  classical
  have hgoodMeas : MeasurableSet (blockGoodSet β t r s) :=
    measurableSet_blockGoodSet β t r s
  have hpoint (ω : Disorder) :
      (blockGoodSet β t r s).indicator
          (fun ω => familyTerm β t F ω * familyTerm β t G ω) ω =
        ∏ x : pairFactorIndex r s F G, pairFactorValue β t F G x ω := by
    exact (pairFactorValue_prod_eq_global_indicator β t hr hF hG ω).symm
  have hInt : ∀ x : pairFactorIndex r s F G,
      Integrable (pairFactorValue β t F G x) disorderLaw := by
    intro x
    cases x with
    | inl c =>
        change Integrable (pairComponentFactor β t F G c.1) disorderLaw
        exact integrable_pairComponentFactor β t ht hF hG c.1
    | inr i =>
        change Integrable (pairGoodBlockFactor β t i.1) disorderLaw
        exact integrable_pairGoodBlockFactor β t i.1
  rw [← integral_indicator hgoodMeas]
  calc
    ∫ ω, (blockGoodSet β t r s).indicator
        (fun ω => familyTerm β t F ω * familyTerm β t G ω) ω ∂disorderLaw =
        ∫ ω, ∏ x : pairFactorIndex r s F G, pairFactorValue β t F G x ω ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∏ x : pairFactorIndex r s F G,
          ∫ ω, pairFactorValue β t F G x ω ∂disorderLaw :=
      integral_pairFactor_prod_eq_prod_integral β t ht hF hG hInt

/-- Each good-set pair integral is bounded by the product of its component weights. The
companion `integrable_familyTerm_mul_on_goodSet` supplies integrability of the set integrand. -/
theorem abs_setIntegral_familyTerm_mul_le (A : ℝ) :
    ∃ C₀ ρ₀ C : ℝ, 0 < C₀ ∧ 1 < ρ₀ ∧ 1 ≤ C ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ᶠ N : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
      ∀ F ∈ intervalFamilies r s, ∀ G ∈ intervalFamilies r s,
        |∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
            familyTerm (criticalBeta ϑ N) (blockTime N ρ) F ω *
              familyTerm (criticalBeta ϑ N) (blockTime N ρ) G ω ∂disorderLaw| ≤
          ∏ c ∈ pairComponents r s F G,
            componentWeight (C * C₀ / Real.sqrt (Real.log ρ)) (blockCount N ρ) F G c := by
  classical
  obtain ⟨Cm₀, ρm, Cm, hCm₀, hρm, hMean⟩ := abs_integral_truncatedCorrector_le A
  obtain ⟨Cs₀, ρs, Cs, hCs₀, hρs, hSq⟩ := integral_truncatedCorrector_sq_le A
  let C₀ : ℝ := max Cm₀ Cs₀
  let C : ℝ := max 1 (max |Cm| |Cs|)
  let ρ₀ : ℝ := max ρm (max ρs (Real.exp ((C * C₀) ^ 2) + 1))
  have hC₀pos : 0 < C₀ := by
    dsimp [C₀]
    exact lt_of_lt_of_le hCm₀ (le_max_left _ _)
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hCmle : Cm ≤ C := by
    dsimp [C]
    exact le_trans (le_abs_self Cm) (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCsle : |Cs| ≤ C := by
    dsimp [C]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hρ₀gt : 1 < ρ₀ := by
    dsimp [ρ₀]
    exact lt_of_lt_of_le hρm (le_max_left _ _)
  refine ⟨C₀, ρ₀, C, hC₀pos, hρ₀gt, hC1, ?_⟩
  intro ρ hρ
  have hρmρ : ρm ≤ ρ := le_trans (le_max_left _ _) hρ
  have hρinner : max ρs (Real.exp ((C * C₀) ^ 2) + 1) ≤ ρ :=
    le_trans (le_max_right _ _) hρ
  have hρsρ : ρs ≤ ρ := le_trans (le_max_left _ _) hρinner
  have hexpPlus : Real.exp ((C * C₀) ^ 2) + 1 ≤ ρ := by
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hρ
  have hexp : Real.exp ((C * C₀) ^ 2) < ρ := by linarith
  have hlog : (C * C₀) ^ 2 < Real.log ρ := by
    calc
      (C * C₀) ^ 2 = Real.log (Real.exp ((C * C₀) ^ 2)) := by rw [Real.log_exp]
      _ < Real.log ρ := Real.log_lt_log (Real.exp_pos _) hexp
  have hlogpos : 0 < Real.log ρ := by nlinarith [sq_nonneg (C * C₀)]
  have hsqrtpos : 0 < Real.sqrt (Real.log ρ) := Real.sqrt_pos.2 hlogpos
  have hsqrtCmp : C * C₀ ≤ Real.sqrt (Real.log ρ) := by
    have hsq := Real.sq_sqrt (le_of_lt hlogpos)
    nlinarith [sq_nonneg (C * C₀)]
  have hNclock : ∀ᶠ N : ℕ in atTop,
      ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N := Filter.eventually_ge_atTop _
  filter_upwards [hMean ρ hρmρ, hSq ρ hρsρ, hNclock]
    with N hMeanN hSqN hNclock
  intro ϑ hϑ r s hr hrs hsK F hF G hG
  let β : ℝ := criticalBeta ϑ N
  let t : ℕ → ℕ := blockTime N ρ
  let K : ℕ := blockCount N ρ
  let γ : ℝ := C * C₀ / Real.sqrt (Real.log ρ)
  let α₀ : ℝ := C₀ / Real.sqrt (Real.log ρ)
  let αm : ℝ := Cm₀ / Real.sqrt (Real.log ρ)
  let αs : ℝ := Cs₀ / Real.sqrt (Real.log ρ)
  have hC₀m : Cm₀ ≤ C₀ := le_max_left _ _
  have hC₀s : Cs₀ ≤ C₀ := le_max_right _ _
  have hαm0 : 0 ≤ αm := by dsimp [αm]; positivity
  have hαs0 : 0 ≤ αs := by dsimp [αs]; positivity
  have hα₀0 : 0 ≤ α₀ := by dsimp [α₀]; positivity
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hbaseEq : C * α₀ = γ := by dsimp [α₀, γ]; ring
  have hγ1 : γ ≤ 1 := by
    dsimp [γ]
    calc
      C * C₀ / Real.sqrt (Real.log ρ) ≤
          Real.sqrt (Real.log ρ) / Real.sqrt (Real.log ρ) :=
        div_le_div_of_nonneg_right hsqrtCmp hsqrtpos.le
      _ = 1 := div_self hsqrtpos.ne'
  have hαm₀ : αm ≤ α₀ := by
    dsimp [αm, α₀]
    exact div_le_div_of_nonneg_right hC₀m hsqrtpos.le
  have hαs₀ : αs ≤ α₀ := by
    dsimp [αs, α₀]
    exact div_le_div_of_nonneg_right hC₀s hsqrtpos.le
  have ht : Monotone t := by
    exact Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon
      hρ₀gt hρ hNclock
  have hsK' : s < K := by dsimp [K]; omega
  have hMeanComponent {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G) :
      |∫ ω, truncatedCorrector β t c.1 c.2 ω ∂disorderLaw| ≤
        γ ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
    have hc' := Finset.mem_filter.mp hc
    have hcspan := Finset.mem_product.mp hc'.1
    have hstart := Finset.mem_Icc.mp hcspan.1
    have hstop := Finset.mem_Icc.mp hcspan.2
    have hstrict : c.1 < c.2 := hc'.2.1
    have hMeanRaw := hMeanN ϑ hϑ c.1 c.2 (by omega) hstrict (by omega)
    have hcoeff' := coefficient_mul_pow_le_pow hC1 hCmle hαm0 hαm₀
      hα₀0 (by omega : 1 ≤ c.2 - c.1)
    have hcoeff : Cm * αm ^ (c.2 - c.1) ≤ γ ^ (c.2 - c.1) := by
      calc
        Cm * αm ^ (c.2 - c.1) ≤ (C * α₀) ^ (c.2 - c.1) := hcoeff'
        _ = γ ^ (c.2 - c.1) := by rw [hbaseEq]
    have hdenpos : 0 < ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
      apply Real.rpow_pos_of_pos
      have hnat : c.2 < K := by dsimp [K]; omega
      exact sub_pos.mpr (by exact_mod_cast hnat)
    calc
      |∫ ω, truncatedCorrector β t c.1 c.2 ω ∂disorderLaw| ≤
          Cm * αm ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) := by
            simpa [β, t, K, αm] using hMeanRaw
      _ ≤ γ ^ (c.2 - c.1) / ((K : ℝ) - c.2) ^ ((3 : ℝ) / 2) :=
        div_le_div_of_nonneg_right hcoeff hdenpos.le
  have hSqComponent {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G)
      (I : ℕ × ℕ) (hI : I ∈ restrictIntervalFamily F c ∪ restrictIntervalFamily G c) :
      ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
        (γ ^ (I.2 - I.1) / ((K : ℝ) - c.2)) ^ 2 := by
    have hc' := Finset.mem_filter.mp hc
    have hcspan := Finset.mem_product.mp hc'.1
    have hstop := Finset.mem_Icc.mp hcspan.2
    have hIcontained : c.1 ≤ I.1 ∧ I.2 ≤ c.2 := by
      rcases Finset.mem_union.mp hI with hIF | hIG
      · exact (Finset.mem_filter.mp hIF).2
      · exact (Finset.mem_filter.mp hIG).2
    have hIvalid : 1 ≤ I.1 ∧ I.1 < I.2 ∧ I.2 + 1 ≤ blockCount N ρ := by
      rcases Finset.mem_union.mp hI with hIF | hIG
      · have hB := (intervalFamilies_mem_iff r s F).mp hF |>.1 I
          (Finset.mem_filter.mp hIF).1
        exact ⟨by omega, hB.2.2.2.2, by omega⟩
      · have hB := (intervalFamilies_mem_iff r s G).mp hG |>.1 I
          (Finset.mem_filter.mp hIG).1
        exact ⟨by omega, hB.2.2.2.2, by omega⟩
    let ℓ : ℕ := I.2 - I.1
    have hraw := hSqN ϑ hϑ I.1 I.2 hIvalid.1 hIvalid.2.1 hIvalid.2.2
    have hαsβ : αs ≤ C₀ / Real.sqrt (Real.log ρ) := by
      dsimp [αs]
      exact div_le_div_of_nonneg_right hC₀s hsqrtpos.le
    have hαs₀ : αs ≤ α₀ := by simpa [α₀] using hαsβ
    have hlen : 1 ≤ ℓ := by dsimp only [ℓ]; omega
    have hcoeff' := coefficient_mul_pow_le_pow hC1 hCsle hαs0 hαs₀
      (by positivity) hlen
    have hcoeff : |Cs| * αs ^ ℓ ≤ γ ^ ℓ := by
      calc
        |Cs| * αs ^ ℓ ≤ (C * α₀) ^ ℓ := hcoeff'
        _ = γ ^ ℓ := by rw [hbaseEq]
    have hnum : (Cs * αs ^ ℓ) ^ 2 ≤ (γ ^ ℓ) ^ 2 := by
      calc
        (Cs * αs ^ ℓ) ^ 2 = (|Cs| * αs ^ ℓ) ^ 2 := by
          rw [← sq_abs, abs_mul, abs_of_nonneg (pow_nonneg hαs0 _)]
        _ ≤ (γ ^ ℓ) ^ 2 :=
          (sq_le_sq₀ (mul_nonneg (abs_nonneg _) (pow_nonneg hαs0 _))
            (pow_nonneg hγ0 _)).2 hcoeff
    have hI1cast : (I.1 : ℝ) ≤ (c.2 : ℝ) := by
      have hnat : I.1 ≤ c.2 := le_trans (Nat.le_of_lt hIvalid.2.1) hIcontained.2
      exact_mod_cast hnat
    have hI2cast : (I.2 : ℝ) ≤ (c.2 : ℝ) := by exact_mod_cast hIcontained.2
    have hdpos : 0 < (K : ℝ) - c.2 := by
      have hnat : c.2 < K := by dsimp [K]; omega
      exact sub_pos.mpr (by exact_mod_cast hnat)
    have hdenI1 : 0 < (K : ℝ) - I.1 := by
      have hnat : I.1 < K := by dsimp [K]; omega
      exact sub_pos.mpr (by exact_mod_cast hnat)
    have hdenI2 : 0 < (K : ℝ) - I.2 := by
      have hnat : I.2 < K := by dsimp [K]; omega
      exact sub_pos.mpr (by exact_mod_cast hnat)
    have hdenCmp : ((K : ℝ) - c.2) ^ 2 ≤
        ((K : ℝ) - I.1) * ((K : ℝ) - I.2) := by
      have hle1 : (K : ℝ) - c.2 ≤ (K : ℝ) - I.1 := by linarith
      have hle2 : (K : ℝ) - c.2 ≤ (K : ℝ) - I.2 := by linarith
      calc
        ((K : ℝ) - c.2) ^ 2 = ((K : ℝ) - c.2) * ((K : ℝ) - c.2) := by ring
        _ ≤ ((K : ℝ) - I.1) * ((K : ℝ) - I.2) :=
          mul_le_mul hle1 hle2 (le_of_lt hdpos) (le_of_lt hdenI1)
    have hraw' : ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
        (Cs * αs ^ ℓ) ^ 2 /
          (((K : ℝ) - I.1) * ((K : ℝ) - I.2)) := by
      simpa [β, t, K, αs, ℓ] using hraw
    calc
      ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw ≤
          (Cs * αs ^ ℓ) ^ 2 /
            (((K : ℝ) - I.1) * ((K : ℝ) - I.2)) := hraw'
      _ ≤ (γ ^ ℓ) ^ 2 /
            (((K : ℝ) - I.1) * ((K : ℝ) - I.2)) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ (γ ^ ℓ) ^ 2 / ((K : ℝ) - c.2) ^ 2 :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hdenCmp
      _ = (γ ^ (I.2 - I.1) / ((K : ℝ) - c.2)) ^ 2 := by
        dsimp [ℓ]
        rw [← div_pow]
  have hpairIntegralBound {c : ℕ × ℕ} (hc : c ∈ pairComponents r s F G) :
      |∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw| ≤
        componentWeight γ K F G c := by
    exact pairComponentFactor_abs_integral_le_of β t ht γ hγ0 hγ1 hsK' hr hF hG hc
      (hMeanComponent hc) (hSqComponent hc)
  have hgoodBlockIntegralBound (i : ℕ) :
      |∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw| ≤ 1 := by
    have hiInt := integrable_pairGoodBlockFactor β t i
    have hpoint (ω : Disorder) : 0 ≤ pairGoodBlockFactor β t i ω ∧
        pairGoodBlockFactor β t i ω ≤ 1 := by
      dsimp [pairGoodBlockFactor]
      split_ifs <;> norm_num
    have hnonneg : 0 ≤ ∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw :=
      integral_nonneg_of_ae (Eventually.of_forall fun ω => (hpoint ω).1)
    have hupper : ∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw ≤ 1 := by
      calc
        ∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw ≤
            ∫ _ω : Disorder, (1 : ℝ) ∂disorderLaw :=
          integral_mono hiInt (integrable_const 1) (fun ω => (hpoint ω).2)
        _ = 1 := by simp
    exact abs_le.mpr ⟨by linarith, hupper⟩
  have hcomponentProd :
      ∏ c ∈ pairComponents r s F G,
          |∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw| ≤
        ∏ c ∈ pairComponents r s F G, componentWeight γ K F G c := by
    apply Finset.prod_le_prod₀
    · intro c hc
      exact abs_nonneg _
    · intro c hc
      exact hpairIntegralBound hc
  have hcomponentProdNonneg :
      0 ≤ ∏ c ∈ pairComponents r s F G, componentWeight γ K F G c := by
    apply Finset.prod_nonneg
    intro c hc
    unfold componentWeight
    have hc' := Finset.mem_filter.mp hc
    have hcspan := Finset.mem_product.mp hc'.1
    have hstop := Finset.mem_Icc.mp hcspan.2
    have hnat : c.2 ≤ K := by dsimp [K]; omega
    exact mul_nonneg (pow_nonneg hγ0 _)
      (Real.rpow_nonneg (sub_nonneg.mpr (by exact_mod_cast hnat)) _)
  have huncoveredProd :
      ∏ i ∈ pairUncoveredBlocks r s F G,
          |∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw| ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i hi
      exact abs_nonneg _
    · intro i hi
      exact hgoodBlockIntegralBound i
  have hfactorProd :
      |∏ x : pairFactorIndex r s F G,
          ∫ ω, pairFactorValue β t F G x ω ∂disorderLaw| =
        (∏ c ∈ pairComponents r s F G,
          |∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw|) *
          ∏ i ∈ pairUncoveredBlocks r s F G,
            |∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw| := by
    have hCattach (f : ℕ × ℕ → ℝ) :
        ∏ c : pairComponentIndex r s F G, f c.1 =
          ∏ c ∈ pairComponents r s F G, f c := by
      rw [Finset.univ_eq_attach, Finset.prod_attach]
    have hUattach (f : ℕ → ℝ) :
        ∏ i : pairUncoveredIndex r s F G, f i.1 =
          ∏ i ∈ pairUncoveredBlocks r s F G, f i := by
      rw [Finset.univ_eq_attach, Finset.prod_attach]
    have hprod :
        ∏ x : pairFactorIndex r s F G,
          ∫ ω, pairFactorValue β t F G x ω ∂disorderLaw =
          (∏ c ∈ pairComponents r s F G,
            ∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw) *
            ∏ i ∈ pairUncoveredBlocks r s F G,
              ∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw := by
      rw [Fintype.prod_sum_type]
      simp only [pairFactorValue]
      rw [hCattach (fun c => ∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw),
        hUattach (fun i => ∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw)]
    rw [hprod, abs_mul, Finset.abs_prod, Finset.abs_prod]
  calc
    |∫ ω in blockGoodSet β t r s,
        familyTerm β t F ω * familyTerm β t G ω ∂disorderLaw| =
      |∏ x : pairFactorIndex r s F G,
          ∫ ω, pairFactorValue β t F G x ω ∂disorderLaw| := by
        rw [setIntegral_familyTerm_mul_eq_pairFactorIntegrals β t ht hr hF hG]
    _ =
      (∏ c ∈ pairComponents r s F G,
        |∫ ω, pairComponentFactor β t F G c ω ∂disorderLaw|) *
        ∏ i ∈ pairUncoveredBlocks r s F G,
          |∫ ω, pairGoodBlockFactor β t i ω ∂disorderLaw| := hfactorProd
    _ ≤ (∏ c ∈ pairComponents r s F G, componentWeight γ K F G c) * 1 :=
      mul_le_mul hcomponentProd huncoveredProd (by positivity) hcomponentProdNonneg
    _ = ∏ c ∈ pairComponents r s F G, componentWeight γ K F G c := by ring

end Critical2DKPZ.OnePoint

end
