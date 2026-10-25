/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioComponentFactorization
public import Critical2DKPZ.OnePoint.BlockRatioIntegralExpansion
public import Critical2DKPZ.OnePoint.BlockRatioCorrectorMean
import Mathlib.Probability.Independence.Integration
import Mathlib.Data.Finset.Pairwise
import Mathlib.Tactic

/-! # Independent factors for pair integrals -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- Blocks in `[r,s]` that belong to no connected pair component. -/
noncomputable def pairUncoveredBlocks (r s : ℕ) (F G : Finset (ℕ × ℕ)) : Finset ℕ := by
  classical
  exact (Finset.Icc r s).filter fun i =>
    ¬ ∃ c ∈ pairComponents r s F G, c.1 ≤ i ∧ i ≤ c.2

/-- The finite type indexing the connected components of a pair of interval families. -/
abbrev pairComponentIndex (r s : ℕ) (F G : Finset (ℕ × ℕ)) :=
  {c : ℕ × ℕ // c ∈ pairComponents r s F G}

/-- The finite type indexing uncovered blocks in `[r,s]`. -/
abbrev pairUncoveredIndex (r s : ℕ) (F G : Finset (ℕ × ℕ)) :=
  {i : ℕ // i ∈ pairUncoveredBlocks r s F G}

/-- Component and uncovered-block factors in the pair integral. -/
abbrev pairFactorIndex (r s : ℕ) (F G : Finset (ℕ × ℕ)) :=
  Sum (pairComponentIndex r s F G) (pairUncoveredIndex r s F G)

/-- Start block for an independent pair-integral factor. -/
def pairComponentStart (r s : ℕ) (F G : Finset (ℕ × ℕ))
    (x : pairFactorIndex r s F G) : ℕ :=
  match x with
  | Sum.inl c => c.1.1
  | Sum.inr i => i.1

/-- End block for an independent pair-integral factor. -/
def pairComponentStop (r s : ℕ) (F G : Finset (ℕ × ℕ))
    (x : pairFactorIndex r s F G) : ℕ :=
  match x with
  | Sum.inl c => c.1.2
  | Sum.inr i => i.1

/-- The indicator of the one-block good event as a real-valued factor. -/
noncomputable def pairGoodBlockFactor (β : ℝ) (t : ℕ → ℕ) (i : ℕ) (ω : Disorder) : ℝ :=
  if |blockMass β t i ω - 1| ≤ 1 / 2 then 1 else 0

/-- Correctors and good-block indicators restricted to one maximal component span. -/
noncomputable def pairComponentFactor (β : ℝ) (t : ℕ → ℕ) (F G : Finset (ℕ × ℕ))
    (c : ℕ × ℕ) (ω : Disorder) : ℝ :=
  (∏ I ∈ restrictIntervalFamily F c,
      truncatedCorrector β t I.1 I.2 ω) *
    (∏ I ∈ restrictIntervalFamily G c,
      truncatedCorrector β t I.1 I.2 ω) *
    ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω

/-- The random factor attached to one component or one uncovered block. -/
noncomputable def pairFactorValue {r s : ℕ} (β : ℝ) (t : ℕ → ℕ) (F G : Finset (ℕ × ℕ))
    (x : pairFactorIndex r s F G) (ω : Disorder) : ℝ := by
  classical
  cases x with
  | inl c => exact pairComponentFactor β t F G c.1 ω
  | inr i => exact pairGoodBlockFactor β t i.1 ω

/-- A component factor only sees the disorder in its span. -/
theorem measurable_pairComponentFactor_block (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {r s : ℕ} {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) (c : ℕ × ℕ) :
    Measurable[Gaussian.disorderBlock (t (c.1 - 1)) (t c.2)]
      (pairComponentFactor β t F G c) := by
  classical
  have hFprod : Measurable[Gaussian.disorderBlock (t (c.1 - 1)) (t c.2)]
      (fun ω => ∏ I ∈ restrictIntervalFamily F c,
        truncatedCorrector β t I.1 I.2 ω) := by
    apply Finset.measurable_prod
    intro I hI
    have hIc := Finset.mem_filter.mp hI
    have hIbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hIc.1
    have hstart : t (c.1 - 1) ≤ t (I.1 - 1) := ht (by omega)
    have hstop : t I.2 ≤ t c.2 := ht hIc.2.2
    exact (measurable_truncatedCorrector_block β t ht I.1 I.2 hIbounds.2.2.2.2).mono
      (Gaussian.disorderBlock_mono hstart hstop) le_rfl
  have hGprod : Measurable[Gaussian.disorderBlock (t (c.1 - 1)) (t c.2)]
      (fun ω => ∏ I ∈ restrictIntervalFamily G c,
        truncatedCorrector β t I.1 I.2 ω) := by
    apply Finset.measurable_prod
    intro I hI
    have hIc := Finset.mem_filter.mp hI
    have hIbounds := (intervalFamilies_mem_iff r s G).mp hG |>.1 I hIc.1
    have hstart : t (c.1 - 1) ≤ t (I.1 - 1) := ht (by omega)
    have hstop : t I.2 ≤ t c.2 := ht hIc.2.2
    exact (measurable_truncatedCorrector_block β t ht I.1 I.2 hIbounds.2.2.2.2).mono
      (Gaussian.disorderBlock_mono hstart hstop) le_rfl
  have hgood : Measurable[Gaussian.disorderBlock (t (c.1 - 1)) (t c.2)]
      (fun ω => ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω) := by
    apply Finset.measurable_prod
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hstart : t (c.1 - 1) ≤ t (i - 1) := ht (by omega)
    have hstop : t i ≤ t c.2 := ht hi'.2
    exact (measurable_goodBlockIndicator β t i).mono
      (Gaussian.disorderBlock_mono hstart hstop) le_rfl
  change Measurable[Gaussian.disorderBlock (t (c.1 - 1)) (t c.2)]
      (fun ω =>
        (∏ I ∈ restrictIntervalFamily F c, truncatedCorrector β t I.1 I.2 ω) *
          (∏ I ∈ restrictIntervalFamily G c, truncatedCorrector β t I.1 I.2 ω) *
            ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω)
  exact (hFprod.mul hGprod).mul hgood

/-- Each component or uncovered-block factor is measurable on its own time block. -/
theorem measurable_pairFactorValue_block {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) (x : pairFactorIndex r s F G) :
    Measurable[Gaussian.disorderBlock (t (pairComponentStart r s F G x - 1))
      (t (pairComponentStop r s F G x))] (pairFactorValue β t F G x) := by
  cases x with
  | inl c =>
      change Measurable[Gaussian.disorderBlock (t (c.1.1 - 1)) (t c.1.2)]
        (pairComponentFactor β t F G c.1)
      exact measurable_pairComponentFactor_block β t ht hF hG c.1
  | inr i =>
      change Measurable[Gaussian.disorderBlock (t (i.1 - 1)) (t i.1)]
        (pairGoodBlockFactor β t i.1)
      change Measurable[Gaussian.disorderBlock (t (i.1 - 1)) (t i.1)]
        (fun ω => if |blockMass β t i.1 ω - 1| ≤ 1 / 2 then (1 : ℝ) else 0)
      exact measurable_goodBlockIndicator β t i.1

/-- Component and uncovered-block time intervals are pairwise disjoint. -/
theorem pairFactorIndex_time_disjoint {r s : ℕ} {F G : Finset (ℕ × ℕ)}
    (t : ℕ → ℕ) (ht : Monotone t) {x y : pairFactorIndex r s F G} (hxy : x ≠ y) :
    Disjoint
      (Set.Ioc (t (pairComponentStart r s F G x - 1))
        (t (pairComponentStop r s F G x)))
      (Set.Ioc (t (pairComponentStart r s F G y - 1))
        (t (pairComponentStop r s F G y))) := by
  cases x with
  | inl c =>
    cases y with
    | inl d =>
      simp only [pairComponentStart, pairComponentStop]
      have hcd : c.1 ≠ d.1 := by
        intro h
        apply hxy
        exact congrArg Sum.inl (Subtype.ext h)
      simpa [pairComponentStart, pairComponentStop] using
        pairComponents_time_disjoint t ht c.2 d.2 hcd
    | inr i =>
      simp only [pairComponentStart, pairComponentStop]
      have hi := Finset.mem_filter.mp i.2
      have houtside : i.1 < c.1.1 ∨ c.1.2 < i.1 := by
        by_contra h
        apply hi.2
        exact ⟨c.1, c.2, by omega, by omega⟩
      rcases houtside with hleft | hright
      · apply Set.disjoint_left.mpr
        intro z hzComp hzI
        have htime : t i.1 ≤ t (c.1.1 - 1) := ht (by omega)
        exact (not_lt_of_ge (hzI.2.trans htime)) hzComp.1
      · apply Set.disjoint_left.mpr
        intro z hzComp hzI
        have htime : t c.1.2 ≤ t (i.1 - 1) := ht (by omega)
        exact (not_lt_of_ge (hzComp.2.trans htime)) hzI.1
  | inr i =>
    cases y with
    | inl c =>
      simp only [pairComponentStart, pairComponentStop]
      have hi := Finset.mem_filter.mp i.2
      have houtside : i.1 < c.1.1 ∨ c.1.2 < i.1 := by
        by_contra h
        apply hi.2
        exact ⟨c.1, c.2, by omega, by omega⟩
      rcases houtside with hleft | hright
      · apply Set.disjoint_left.mpr
        intro z hzI hzComp
        have htime : t i.1 ≤ t (c.1.1 - 1) := ht (by omega)
        exact (not_lt_of_ge (hzI.2.trans htime)) hzComp.1
      · apply Set.disjoint_left.mpr
        intro z hzI hzComp
        have htime : t c.1.2 ≤ t (i.1 - 1) := ht (by omega)
        exact (not_lt_of_ge (hzComp.2.trans htime)) hzI.1
    | inr j =>
      simp only [pairComponentStart, pairComponentStop]
      have hij : i.1 ≠ j.1 := by
        intro h
        apply hxy
        exact congrArg Sum.inr (Subtype.ext h)
      rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
      · apply Set.disjoint_left.mpr
        intro z hzi hzj
        have htime : t i.1 ≤ t (j.1 - 1) := ht (by omega)
        exact (not_lt_of_ge (hzi.2.trans htime)) hzj.1
      · apply Set.disjoint_left.mpr
        intro z hzi hzj
        have htime : t j.1 ≤ t (i.1 - 1) := ht (by omega)
        exact (not_lt_of_ge (hzj.2.trans htime)) hzi.1

/-- The factors indexed by components and uncovered blocks are jointly independent. -/
theorem pairFactorValue_iIndepFun {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {F G : Finset (ℕ × ℕ)}
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s) :
    iIndepFun (pairFactorValue (r := r) (s := s) β t F G) disorderLaw := by
  let a := pairComponentStart r s F G
  let b := pairComponentStop r s F G
  have hdisj : Pairwise (fun x y => Disjoint (Set.Ioc (t (a x - 1)) (t (b x)))
      (Set.Ioc (t (a y - 1)) (t (b y)))) := by
    intro x y hxy
    exact pairFactorIndex_time_disjoint t ht hxy
  have hmeas : ∀ x : pairFactorIndex r s F G,
      Measurable[Gaussian.disorderBlock (t (a x - 1)) (t (b x))]
        (pairFactorValue (r := r) (s := s) β t F G x) := by
    intro x
    exact measurable_pairFactorValue_block β t ht hF hG x
  exact Polymer.independent_of_blockMeasurable (fun x => t (a x - 1))
    (fun x => t (b x)) hdisj (pairFactorValue (r := r) (s := s) β t F G) hmeas

/-- Integrals of finite products of the independent pair factors split, provided each factor is
integrable. -/
theorem integral_pairFactor_prod_eq_prod_integral {r s : ℕ} (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {F G : Finset (ℕ × ℕ)}
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s)
    (hInt : ∀ x : pairFactorIndex r s F G,
      Integrable (pairFactorValue (r := r) (s := s) β t F G x) disorderLaw) :
    ∫ ω, ∏ x : pairFactorIndex r s F G, pairFactorValue β t F G x ω ∂disorderLaw =
      ∏ x : pairFactorIndex r s F G,
        ∫ ω, pairFactorValue β t F G x ω ∂disorderLaw := by
  have hInd := pairFactorValue_iIndepFun (r := r) (s := s) β t ht hF hG
  exact hInd.integral_fun_prod_eq_prod_integral fun x => (hInt x).aestronglyMeasurable

/-- A product of truncated correctors over a disjoint interval family is square integrable. -/
theorem memLp_pairFamilyCorrectorProduct_two (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {r s : ℕ} (F : Finset (ℕ × ℕ))
    (hF : F ∈ intervalFamilies r s) :
    MemLp (fun ω => ∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω) 2 disorderLaw := by
  classical
  let B : ℝ := 2 ^ ((s + 1) * F.card)
  have hclosed := memLp_intervalFamilyClosedProduct β t F hF
  have hclosedMeas : Measurable (fun ω => ∏ I ∈ F,
      closedDiscrepancy β t I.1 I.2 ω) := by
    apply Finset.measurable_prod
    intro I hI
    have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hI
    exact (measurable_closedDiscrepancy β t ht I.1 I.2
      (Nat.le_of_lt hbounds.2.2.2.2)).mono
        (Gaussian.disorderBlock_le _ _) le_rfl
  have htruncMeas : Measurable (fun ω =>
      ∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω) := by
    apply Finset.measurable_prod
    intro I hI
    have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hI
    exact (measurable_truncatedCorrector_block β t ht I.1 I.2
      hbounds.2.2.2.2).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hpoint (ω : Disorder) :
      |∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω| ≤
        B * |∏ I ∈ F, closedDiscrepancy β t I.1 I.2 ω| := by
    have hone (I : ℕ × ℕ) (hI : I ∈ F) :
        |truncatedCorrector β t I.1 I.2 ω| ≤
          2 ^ (s + 1) * |closedDiscrepancy β t I.1 I.2 ω| := by
      have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hI
      have hcard : (Finset.Icc I.1 I.2).card ≤ s + 1 := by
        have hsub : Finset.Icc I.1 I.2 ⊆ Finset.Icc 0 s := by
          intro i hi
          have hi' := Finset.mem_Icc.mp hi
          exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, by omega⟩
        calc
          (Finset.Icc I.1 I.2).card ≤ (Finset.Icc 0 s).card := Finset.card_le_card hsub
          _ = s + 1 := by simp [Nat.card_Icc]
      have hMprod : |∏ i ∈ Finset.Icc I.1 I.2, truncatedInverse β t i ω| ≤
          2 ^ (s + 1) := by
        rw [Finset.abs_prod]
        calc
          ∏ i ∈ Finset.Icc I.1 I.2, |truncatedInverse β t i ω| ≤
              ∏ _i ∈ Finset.Icc I.1 I.2, (2 : ℝ) := by
            apply Finset.prod_le_prod₀
            · intro i hi
              exact abs_nonneg _
            · intro i hi
              have hM := truncatedInverse_nonneg_le_two β t i ω
              rw [abs_of_nonneg hM.1]
              exact hM.2
          _ = 2 ^ (Finset.Icc I.1 I.2).card := by simp
          _ ≤ 2 ^ (s + 1) := pow_le_pow_right₀ (by norm_num) hcard
      rw [truncatedCorrector, abs_mul]
      calc
        |closedDiscrepancy β t I.1 I.2 ω| *
            |∏ i ∈ Finset.Icc I.1 I.2, truncatedInverse β t i ω| ≤
          |closedDiscrepancy β t I.1 I.2 ω| * 2 ^ (s + 1) :=
            mul_le_mul_of_nonneg_left hMprod (abs_nonneg _)
        _ = 2 ^ (s + 1) * |closedDiscrepancy β t I.1 I.2 ω| := by ring
    rw [Finset.abs_prod]
    calc
      ∏ I ∈ F, |truncatedCorrector β t I.1 I.2 ω| ≤
          ∏ I ∈ F, (2 ^ (s + 1) * |closedDiscrepancy β t I.1 I.2 ω|) := by
        apply Finset.prod_le_prod₀
        · intro I hI
          exact abs_nonneg _
        · intro I hI
          exact hone I hI
      _ = B * |∏ I ∈ F, closedDiscrepancy β t I.1 I.2 ω| := by
        simp [B, Finset.prod_mul_distrib, Finset.abs_prod, pow_mul]
  have hBnonneg : 0 ≤ B := by positivity
  exact (hclosed.const_mul B).mono htruncMeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω =>
      by simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hBnonneg] using hpoint ω)

/-- The second moment of a corrector product over disjoint intervals factors into interval moments.
The integrability companions are `integrable_sq_truncatedCorrector` and
`memLp_pairFamilyCorrectorProduct_two`. -/
theorem integral_pairFamilyCorrectorProduct_sq_eq (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) {r s : ℕ} (F : Finset (ℕ × ℕ))
    (hF : F ∈ intervalFamilies r s) :
    ∫ ω, (∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω) ^ 2 ∂disorderLaw =
      ∏ I ∈ F, ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw := by
  classical
  let ι := {I : ℕ × ℕ // I ∈ F}
  let f : ι → Disorder → ℝ := fun I => truncatedCorrector β t I.1.1 I.1.2
  have hdisj : Pairwise (fun I J : ι =>
      Disjoint (Set.Ioc (t (I.1.1 - 1)) (t I.1.2))
        (Set.Ioc (t (J.1.1 - 1)) (t J.1.2))) := by
    intro I J hIJ
    have hIJ' : I.1 ≠ J.1 := by
      intro h
      apply hIJ
      exact Subtype.ext h
    have hsep := (intervalFamilies_mem_iff r s F).mp hF |>.2 I.1 I.2 J.1 J.2 hIJ'
    rcases hsep with hIJ' | hJI'
    · apply Set.disjoint_left.mpr
      intro x hxI hxJ
      have htime : t I.1.2 ≤ t (J.1.1 - 1) := ht (by omega)
      exact (not_lt_of_ge (hxI.2.trans htime)) hxJ.1
    · apply Set.disjoint_left.mpr
      intro x hxI hxJ
      have htime : t J.1.2 ≤ t (I.1.1 - 1) := ht (by omega)
      exact (not_lt_of_ge (hxJ.2.trans htime)) hxI.1
  have hmeas : ∀ I : ι,
      Measurable[Gaussian.disorderBlock (t (I.1.1 - 1)) (t I.1.2)] (f I) := by
    intro I
    have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I.1 I.2
    exact measurable_truncatedCorrector_block β t ht I.1.1 I.1.2 hbounds.2.2.2.2
  have hind : iIndepFun f disorderLaw :=
    Polymer.independent_of_blockMeasurable
      (fun I : ι => t (I.1.1 - 1)) (fun I => t I.1.2) hdisj f hmeas
  have hindSq : iIndepFun (fun I : ι => fun ω => f I ω ^ 2) disorderLaw := by
    exact hind.comp (fun _ : ι => fun x : ℝ => x ^ 2) (fun _ => by fun_prop)
  have hprodAttach (g : ℕ × ℕ → ℝ) :
      (∏ I : ι, g I.1) = ∏ I ∈ F, g I := by
    rw [Finset.univ_eq_attach, Finset.prod_attach]
  have hpoint (ω : Disorder) :
      (∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω) ^ 2 =
        ∏ I : ι, f I ω ^ 2 := by
    rw [← hprodAttach (fun I => truncatedCorrector β t I.1 I.2 ω)]
    exact (Finset.prod_pow Finset.univ 2 (fun I : ι => f I ω)).symm
  have hfactor :
      ∫ ω, ∏ I : ι, f I ω ^ 2 ∂disorderLaw =
        ∏ I : ι, ∫ ω, f I ω ^ 2 ∂disorderLaw := by
    apply hindSq.integral_fun_prod_eq_prod_integral
    intro I
    exact (measurable_truncatedCorrector_block β t ht I.1.1 I.1.2
      ((intervalFamilies_mem_iff r s F).mp hF |>.1 I.1 I.2).2.2.2.2).pow_const 2
      |>.mono (Gaussian.disorderBlock_le _ _) le_rfl |>.aestronglyMeasurable
  calc
    ∫ ω, (∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω) ^ 2 ∂disorderLaw =
        ∫ ω, ∏ I : ι, f I ω ^ 2 ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∏ I : ι, ∫ ω, f I ω ^ 2 ∂disorderLaw := hfactor
    _ = ∏ I ∈ F, ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw := by
      simpa [f] using hprodAttach (fun I => ∫ ω, truncatedCorrector β t I.1 I.2 ω ^ 2 ∂disorderLaw)

/-- A component factor, including its local good-set indicator, is integrable. -/
theorem integrable_pairComponentFactor (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    {r s : ℕ} {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) (c : ℕ × ℕ) :
    Integrable (pairComponentFactor β t F G c) disorderLaw := by
  classical
  let Fc := restrictIntervalFamily F c
  let Gc := restrictIntervalFamily G c
  have hFc : Fc ∈ intervalFamilies c.1 c.2 := restrictIntervalFamily_mem hF
  have hGc : Gc ∈ intervalFamilies c.1 c.2 := restrictIntervalFamily_mem hG
  have hFmem := memLp_pairFamilyCorrectorProduct_two β t ht Fc hFc
  have hGmem := memLp_pairFamilyCorrectorProduct_two β t ht Gc hGc
  have hpairMem : MemLp (fun ω =>
      (∏ I ∈ Fc, truncatedCorrector β t I.1 I.2 ω) *
        (∏ I ∈ Gc, truncatedCorrector β t I.1 I.2 ω)) 1 disorderLaw := by
    exact Polymer.memLp_mul_double 1 (by simpa only [mul_one] using hFmem)
      (by simpa only [mul_one] using hGmem)
  have hpairInt := hpairMem.integrable (by norm_num)
  have hgoodMeas : Measurable (fun ω =>
      ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω) := by
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_goodBlockIndicator β t i).mono
      (Gaussian.disorderBlock_le _ _) le_rfl
  have hgoodBound : ∀ᵐ ω ∂disorderLaw,
      ‖∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω‖ ≤ 1 := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · apply Finset.prod_le_one₀
      · intro i hi
        dsimp [pairGoodBlockFactor]
        split_ifs <;> norm_num
      · intro i hi
        dsimp [pairGoodBlockFactor]
        split_ifs <;> norm_num
    · apply Finset.prod_nonneg
      intro i hi
      dsimp [pairGoodBlockFactor]
      split_ifs <;> norm_num
  have hgoodAS : AEStronglyMeasurable (fun ω =>
      ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω) disorderLaw :=
    hgoodMeas.aestronglyMeasurable
  have hmulInt := hpairInt.mul_bdd hgoodAS hgoodBound
  change Integrable (fun ω =>
    ((∏ I ∈ Fc, truncatedCorrector β t I.1 I.2 ω) *
      (∏ I ∈ Gc, truncatedCorrector β t I.1 I.2 ω)) *
        ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω) disorderLaw
  exact hmulInt

/-- An uncovered good-block indicator is integrable because it is bounded. -/
theorem integrable_pairGoodBlockFactor (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Integrable (pairGoodBlockFactor β t i) disorderLaw := by
  have hmeas : Measurable (pairGoodBlockFactor β t i) :=
    (measurable_goodBlockIndicator β t i).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hmem : MemLp (pairGoodBlockFactor β t i) 2 disorderLaw := by
    apply MemLp.of_bound hmeas.aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs]
    dsimp [pairGoodBlockFactor]
    split_ifs <;> norm_num
  exact hmem.integrable (by norm_num)

private theorem pairComponent_spans_pairwise_disjoint {r s : ℕ}
    (F G : Finset (ℕ × ℕ)) :
    Set.PairwiseDisjoint (pairComponents r s F G : Set (ℕ × ℕ))
      (fun c => Finset.Icc c.1 c.2) := by
  intro c hc d hd hne
  rcases pairComponents_span_disjoint hc hd hne with hcd | hdc
  · apply Finset.disjoint_left.mpr
    intro i hiC hiD
    have hiC' := Finset.mem_Icc.mp hiC
    have hiD' := Finset.mem_Icc.mp hiD
    omega
  · apply Finset.disjoint_left.mpr
    intro i hiC hiD
    have hiC' := Finset.mem_Icc.mp hiC
    have hiD' := Finset.mem_Icc.mp hiD
    omega

private theorem pairComponent_uncovered_disjoint {r s : ℕ}
    (F G : Finset (ℕ × ℕ)) :
    Disjoint ((pairComponents r s F G).biUnion fun c => Finset.Icc c.1 c.2)
      (pairUncoveredBlocks r s F G) := by
  apply Finset.disjoint_left.mpr
  intro i hiC hiU
  rcases Finset.mem_biUnion.mp hiC with ⟨c, hc, hic⟩
  have hU := (Finset.mem_filter.mp hiU).2
  exact hU ⟨c, hc, (Finset.mem_Icc.mp hic).1, (Finset.mem_Icc.mp hic).2⟩

private theorem pairBlock_partition (r s : ℕ) (F G : Finset (ℕ × ℕ)) :
    Finset.Icc r s =
      (pairComponents r s F G).biUnion (fun c => Finset.Icc c.1 c.2) ∪
        pairUncoveredBlocks r s F G := by
  classical
  ext i
  constructor
  · intro hi
    by_cases hcovered : ∃ c ∈ pairComponents r s F G, c.1 ≤ i ∧ i ≤ c.2
    · rcases hcovered with ⟨c, hc, hleft, hright⟩
      apply Finset.mem_union.mpr (Or.inl (Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩))
      exact Finset.mem_Icc.mpr ⟨hleft, hright⟩
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hi, hcovered⟩))
  · intro hi
    rcases Finset.mem_union.mp hi with hiC | hiU
    · rcases Finset.mem_biUnion.mp hiC with ⟨c, hc, hic⟩
      have hc' := Finset.mem_filter.mp hc
      have hspan := Finset.mem_product.mp hc'.1
      have hleft := Finset.mem_Icc.mp hspan.1
      have hright := Finset.mem_Icc.mp hspan.2
      have hii := Finset.mem_Icc.mp hic
      exact Finset.mem_Icc.mpr ⟨le_trans hleft.1 hii.1, le_trans hii.2 hright.2⟩
    · exact (Finset.mem_filter.mp hiU).1

private theorem pairComponent_restrictions_disjoint {r s : ℕ}
    {F G : Finset (ℕ × ℕ)} (hF : F ∈ intervalFamilies r s) :
    Set.PairwiseDisjoint (pairComponents r s F G : Set (ℕ × ℕ))
      (fun c => restrictIntervalFamily F c) := by
  intro c hc d hd hne
  rcases pairComponents_span_disjoint hc hd hne with hcd | hdc
  · apply Finset.disjoint_left.mpr
    intro I hIc hId
    have hIc' := Finset.mem_filter.mp hIc
    have hId' := Finset.mem_filter.mp hId
    have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hIc'.1
    have hIlt := hbounds.2.2.2.2
    have hleft := hId'.2.1
    have hright := hIc'.2.2
    omega
  · apply Finset.disjoint_left.mpr
    intro I hIc hId
    have hIc' := Finset.mem_filter.mp hIc
    have hId' := Finset.mem_filter.mp hId
    have hbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hIc'.1
    have hIlt := hbounds.2.2.2.2
    have hleft := hIc'.2.1
    have hright := hId'.2.2
    omega

private theorem prod_restrict_correctors_eq (β : ℝ) (t : ℕ → ℕ) (r s : ℕ)
    {F G : Finset (ℕ × ℕ)} (hr : 1 ≤ r) (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) :
    ∏ c ∈ pairComponents r s F G,
      ∏ I ∈ restrictIntervalFamily F c, truncatedCorrector β t I.1 I.2 =
        ∏ I ∈ F, truncatedCorrector β t I.1 I.2 := by
  classical
  have hdisj := pairComponent_restrictions_disjoint (G := G) hF
  have hrec := intervalFamily_reconstruct r s hr F G hF hG
  calc
    _ = ∏ I ∈ (pairComponents r s F G).biUnion (restrictIntervalFamily F),
        truncatedCorrector β t I.1 I.2 := (Finset.prod_biUnion hdisj).symm
    _ = ∏ I ∈ F, truncatedCorrector β t I.1 I.2 :=
      Finset.prod_congr hrec.symm (fun _ _ => rfl)

private theorem prod_restrict_correctors_eq_right (β : ℝ) (t : ℕ → ℕ) (r s : ℕ)
    {F G : Finset (ℕ × ℕ)} (hr : 1 ≤ r) (hF : F ∈ intervalFamilies r s)
    (hG : G ∈ intervalFamilies r s) :
    ∏ c ∈ pairComponents r s F G,
      ∏ I ∈ restrictIntervalFamily G c, truncatedCorrector β t I.1 I.2 =
        ∏ I ∈ G, truncatedCorrector β t I.1 I.2 := by
  classical
  have hdisj : Set.PairwiseDisjoint (pairComponents r s F G : Set (ℕ × ℕ))
      (fun c => restrictIntervalFamily G c) := by
    intro c hc d hd hne
    rcases pairComponents_span_disjoint hc hd hne with hcd | hdc
    · apply Finset.disjoint_left.mpr
      intro I hIc hId
      have hIc' := Finset.mem_filter.mp hIc
      have hId' := Finset.mem_filter.mp hId
      have hbounds := (intervalFamilies_mem_iff r s G).mp hG |>.1 I hIc'.1
      have hIlt := hbounds.2.2.2.2
      have hleft := hId'.2.1
      have hright := hIc'.2.2
      omega
    · apply Finset.disjoint_left.mpr
      intro I hIc hId
      have hIc' := Finset.mem_filter.mp hIc
      have hId' := Finset.mem_filter.mp hId
      have hbounds := (intervalFamilies_mem_iff r s G).mp hG |>.1 I hIc'.1
      have hIlt := hbounds.2.2.2.2
      have hleft := hIc'.2.1
      have hright := hId'.2.2
      omega
  have hrec := intervalFamily_reconstruct_right r s hr F G hF hG
  calc
    _ = ∏ I ∈ (pairComponents r s F G).biUnion (restrictIntervalFamily G),
        truncatedCorrector β t I.1 I.2 := (Finset.prod_biUnion hdisj).symm
    _ = ∏ I ∈ G, truncatedCorrector β t I.1 I.2 :=
      Finset.prod_congr hrec.symm (fun _ _ => rfl)

/-- A blockwise product splits over maximal pair components and uncovered blocks. -/
theorem pairBlockwise_prod_eq_components_mul_uncovered
    {r s : ℕ} (F G : Finset (ℕ × ℕ)) (f : ℕ → ℝ) :
    ∏ i ∈ Finset.Icc r s, f i =
      (∏ c ∈ pairComponents r s F G,
        ∏ i ∈ Finset.Icc c.1 c.2, f i) *
        ∏ i ∈ pairUncoveredBlocks r s F G, f i := by
  classical
  let C := pairComponents r s F G
  let U := pairUncoveredBlocks r s F G
  let spans := fun c : ℕ × ℕ => Finset.Icc c.1 c.2
  have hdisj : Set.PairwiseDisjoint (C : Set (ℕ × ℕ)) spans := by
    simpa [C, spans] using pairComponent_spans_pairwise_disjoint (r := r) (s := s) F G
  have hpart : Finset.Icc r s = C.biUnion spans ∪ U := by
    simpa [C, U, spans] using pairBlock_partition r s F G
  have hdisjU : Disjoint (C.biUnion spans) U := by
    simpa [C, U, spans] using pairComponent_uncovered_disjoint (r := r) (s := s) F G
  rw [hpart, Finset.prod_union hdisjU, Finset.prod_biUnion hdisj]

private theorem prod_pairGoodBlockFactor_eq_components_mul_uncovered
    (β : ℝ) (t : ℕ → ℕ) (r s : ℕ) (F G : Finset (ℕ × ℕ)) (ω : Disorder) :
    ∏ i ∈ Finset.Icc r s, pairGoodBlockFactor β t i ω =
      (∏ c ∈ pairComponents r s F G,
        ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω) *
        ∏ i ∈ pairUncoveredBlocks r s F G, pairGoodBlockFactor β t i ω := by
  exact pairBlockwise_prod_eq_components_mul_uncovered F G
    (fun i => pairGoodBlockFactor β t i ω)

/-- The independent component factors reconstruct the good-set indicator times the two global
family terms. -/
theorem pairFactorValue_prod_eq_global_indicator {r s : ℕ} (β : ℝ)
    (t : ℕ → ℕ) {F G : Finset (ℕ × ℕ)} (hr : 1 ≤ r)
    (hF : F ∈ intervalFamilies r s) (hG : G ∈ intervalFamilies r s)
    (ω : Disorder) :
    ∏ x : pairFactorIndex r s F G, pairFactorValue β t F G x ω =
      Set.indicator (blockGoodSet β t r s)
        (fun ω => familyTerm β t F ω * familyTerm β t G ω) ω := by
  classical
  let C := pairComponents r s F G
  let U := pairUncoveredBlocks r s F G
  have hCattach (f : ℕ × ℕ → ℝ) :
      ∏ c : pairComponentIndex r s F G, f c.1 = ∏ c ∈ C, f c := by
    rw [Finset.univ_eq_attach, Finset.prod_attach]
  have hUattach (f : ℕ → ℝ) :
      ∏ i : pairUncoveredIndex r s F G, f i.1 = ∏ i ∈ U, f i := by
    rw [Finset.univ_eq_attach, Finset.prod_attach]
  have hdecomp :
      ∏ x : pairFactorIndex r s F G, pairFactorValue β t F G x ω =
        (∏ c ∈ C, pairComponentFactor β t F G c ω) *
          ∏ i ∈ U, pairGoodBlockFactor β t i ω := by
    rw [Fintype.prod_sum_type]
    simp only [pairFactorValue]
    rw [hCattach (fun c => pairComponentFactor β t F G c ω),
      hUattach (fun i => pairGoodBlockFactor β t i ω)]
  have hcomponents :
      ∏ c ∈ C, pairComponentFactor β t F G c ω =
        (∏ c ∈ C, ∏ I ∈ restrictIntervalFamily F c,
          truncatedCorrector β t I.1 I.2 ω) *
          (∏ c ∈ C, ∏ I ∈ restrictIntervalFamily G c,
            truncatedCorrector β t I.1 I.2 ω) *
          ∏ c ∈ C, ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω := by
    simp [pairComponentFactor, Finset.prod_mul_distrib, mul_assoc]
  have hFprod := prod_restrict_correctors_eq β t r s hr hF hG
  have hGprod := prod_restrict_correctors_eq_right β t r s hr hF hG
  have hgoodprod := prod_pairGoodBlockFactor_eq_components_mul_uncovered
    β t r s F G ω
  have hFprodC :
      ∏ c ∈ C, ∏ I ∈ restrictIntervalFamily F c,
        truncatedCorrector β t I.1 I.2 ω =
          ∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω := by
    simpa only [Finset.prod_apply] using
      congrArg (fun f : Disorder → ℝ => f ω) hFprod
  have hGprodC :
      ∏ c ∈ C, ∏ I ∈ restrictIntervalFamily G c,
        truncatedCorrector β t I.1 I.2 ω =
          ∏ I ∈ G, truncatedCorrector β t I.1 I.2 ω := by
    simpa only [Finset.prod_apply] using
      congrArg (fun f : Disorder → ℝ => f ω) hGprod
  have hgoodprodC :
      ∏ i ∈ Finset.Icc r s, pairGoodBlockFactor β t i ω =
        (∏ c ∈ C, ∏ i ∈ Finset.Icc c.1 c.2, pairGoodBlockFactor β t i ω) *
          ∏ i ∈ U, pairGoodBlockFactor β t i ω := by
    simpa [C, U] using hgoodprod
  have hcombined :
      ∏ x : pairFactorIndex r s F G, pairFactorValue β t F G x ω =
        (∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω) *
          (∏ I ∈ G, truncatedCorrector β t I.1 I.2 ω) *
          ∏ i ∈ Finset.Icc r s, pairGoodBlockFactor β t i ω := by
    rw [hdecomp, hcomponents, hFprodC, hGprodC, hgoodprodC]
    ring
  by_cases hω : ω ∈ blockGoodSet β t r s
  · have hgood :
        ∏ i ∈ Finset.Icc r s, pairGoodBlockFactor β t i ω = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      have hω' : ∀ i ∈ Finset.Icc r s, |blockMass β t i ω - 1| ≤ 1 / 2 := hω
      change ∀ i ∈ Finset.Icc r s, |blockMass β t i ω - 1| ≤ 1 / 2 at hω'
      change (if |blockMass β t i ω - 1| ≤ 1 / 2 then 1 else 0) = 1
      split_ifs with h
      · rfl
      · exact False.elim (h (hω' i hi))
    rw [hcombined, hgood, Set.indicator_of_mem hω,
      familyTerm_eq_corrector_prod_on_goodSet β t F hF hω,
      familyTerm_eq_corrector_prod_on_goodSet β t G hG hω]
    ring
  · have hbad : ¬ ∀ i ∈ Finset.Icc r s, |blockMass β t i ω - 1| ≤ 1 / 2 := by
      simpa [blockGoodSet] using hω
    push Not at hbad
    obtain ⟨i, hi, hbad⟩ := hbad
    have hzero : pairGoodBlockFactor β t i ω = 0 := by
      change (if |blockMass β t i ω - 1| ≤ 1 / 2 then 1 else 0) = 0
      split_ifs with h
      · exact False.elim (by linarith)
      · rfl
    have hprodZero :
        ∏ i ∈ Finset.Icc r s, pairGoodBlockFactor β t i ω = 0 :=
      Finset.prod_eq_zero hi hzero
    rw [hcombined, hprodZero]
    simp [Set.indicator_of_notMem hω]

end Critical2DKPZ.OnePoint

end
