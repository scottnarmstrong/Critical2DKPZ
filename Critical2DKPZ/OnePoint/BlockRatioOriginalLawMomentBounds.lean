/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.BlockRatioComponentSum
public import Critical2DKPZ.OnePoint.BlockRatioIntegralExpansion
public import Critical2DKPZ.OnePoint.BlockRatioVariance
public import Critical2DKPZ.OnePoint.BlockMomentAndTiltedRatioBounds
public import Critical2DKPZ.OnePoint.BlockRatioInverseExpectation
public import Critical2DKPZ.OnePoint.MomentProductInverseFourthMoment
public import Critical2DKPZ.OnePoint.MomentProductTiltedIdentity
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.Blocks.DiscrepancyStringBounds
import Critical2DKPZ.MomentBounds.BlockClockBounds
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic

/-! # Good-set probabilities and truncated-corrector moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

namespace Critical2DKPZ.OnePoint

open Critical2DKPZ.Blocks

/-- A fourth moment controls the measure of the event where the absolute value exceeds one half. -/
theorem measure_abs_gt_half_le_integral_four {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f)
    (hfi : Integrable (fun ω => |f ω| ^ 4) μ) :
    (μ {ω | (1 / 2 : ℝ) < |f ω|}).toReal ≤
      16 * ∫ ω, |f ω| ^ 4 ∂μ := by
  let g : Ω → ℝ := fun ω => |f ω| ^ 4
  have hgmeas : Measurable (fun ω => ENNReal.ofReal (g ω)) := by
    exact ENNReal.measurable_ofReal.comp (hf.abs.pow_const 4)
  have hsubset : {ω | (1 / 2 : ℝ) < |f ω|} ⊆
      {ω | ENNReal.ofReal (1 / 16 : ℝ) ≤ ENNReal.ofReal (g ω)} := by
    intro ω hω
    change (1 / 2 : ℝ) < |f ω| at hω
    have habs : 0 ≤ |f ω| := abs_nonneg _
    have hprod : 0 < (|f ω| - 1 / 2) * (|f ω| + 1 / 2) :=
      mul_pos (by linarith only [hω]) (by positivity)
    have hsq : (1 / 4 : ℝ) < |f ω| ^ 2 := by nlinarith only [hprod]
    have hfour : (1 / 16 : ℝ) ≤ |f ω| ^ 4 := by
      nlinarith [sq_nonneg (|f ω| ^ 2 - 1 / 4)]
    change ENNReal.ofReal (1 / 16 : ℝ) ≤ ENNReal.ofReal (|f ω| ^ 4)
    exact ENNReal.ofReal_le_ofReal hfour
  have hmarkov :=
    (measure_mono (μ := μ) hsubset).trans
      (MeasureTheory.meas_ge_le_lintegral_div (μ := μ) hgmeas.aemeasurable
        (by norm_num : ENNReal.ofReal (1 / 16 : ℝ) ≠ 0)
        (by simp))
  have hlin : ENNReal.ofReal (∫ ω, |f ω| ^ 4 ∂μ) =
      ∫⁻ ω, ENNReal.ofReal (g ω) ∂μ := by
    exact ofReal_integral_eq_lintegral_ofReal hfi
      (Eventually.of_forall fun ω => by positivity)
  rw [← hlin] at hmarkov
  have hnonneg : 0 ≤ ∫ ω, |f ω| ^ 4 ∂μ :=
    integral_nonneg_of_ae (Eventually.of_forall fun ω => by positivity)
  have hrhs : ENNReal.ofReal (∫ ω, |f ω| ^ 4 ∂μ) /
      ENNReal.ofReal (1 / 16 : ℝ) ≠ ∞ :=
    ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
  have hreal := ENNReal.toReal_mono hrhs hmarkov
  calc
    (μ {ω | (1 / 2 : ℝ) < |f ω|}).toReal ≤
        (∫ ω, |f ω| ^ 4 ∂μ) * 16 := by
      simpa [ENNReal.toReal_div, ENNReal.toReal_ofReal hnonneg,
        ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 16), div_eq_mul_inv] using hreal
    _ = 16 * ∫ ω, |f ω| ^ 4 ∂μ := by ring

private theorem sum_shifted_inv_sq_le {r s K : ℕ} (hrs : r ≤ s) (hsK : s + 1 ≤ K) :
    ∑ i ∈ Finset.Icc r s, 1 / ((K : ℝ) + 1 - i) ^ 2 ≤
      2 / ((K : ℝ) - s) := by
  have hD : 1 ≤ K + 1 - s := by omega
  have hDT : K + 1 - s ≤ K + 1 - r := Nat.sub_le_sub_left hrs (K + 1)
  have htail := sum_nat_inv_sq_le hD hDT
  have hsum :
      ∑ i ∈ Finset.Icc r s, 1 / ((K : ℝ) + 1 - i) ^ 2 =
        ∑ i ∈ Finset.Icc r s, ((K + 1 - i : ℕ) : ℝ) ^ (-2 : ℝ) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hcast : ((K + 1 - i : ℕ) : ℝ) = (K : ℝ) + 1 - i := by
      rw [Nat.cast_sub (by omega : i ≤ K + 1), Nat.cast_add, Nat.cast_one]
    have hpos : 0 < ((K + 1 - i : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < K + 1 - i by omega)
    have hpow : ((K + 1 - i : ℕ) : ℝ) ^ (-2 : ℝ) =
        1 / ((K + 1 - i : ℕ) : ℝ) ^ 2 := by
      rw [Real.rpow_neg hpos.le]
      simp [div_eq_mul_inv]
    rw [hcast]
    simpa only [hcast] using hpow.symm
  rw [hsum]
  have hsumReindex := sum_nat_sub_reindex hrs (by omega : s < K + 1)
    (fun i => (i : ℝ) ^ (-2 : ℝ))
  have hslt : s < K := by omega
  have hdenpos : 0 < (K : ℝ) - (s : ℝ) := by
    have hsub : 0 < K - s := by omega
    rw [← Nat.cast_sub (show s ≤ K by omega)]
    exact_mod_cast hsub
  have hDcast : ((K + 1 - s : ℕ) : ℝ) = (K : ℝ) - (s : ℝ) + 1 := by
    rw [Nat.cast_sub (by omega : s ≤ K + 1), Nat.cast_add, Nat.cast_one]
    ring
  have hdenle : (K : ℝ) - (s : ℝ) ≤ ((K + 1 - s : ℕ) : ℝ) := by
    rw [hDcast]
    linarith
  calc
    ∑ i ∈ Finset.Icc r s, ((K + 1 - i : ℕ) : ℝ) ^ (-2 : ℝ) =
        ∑ i ∈ Finset.Icc (K + 1 - s) (K + 1 - r), (i : ℝ) ^ (-2 : ℝ) :=
      hsumReindex
    _ ≤ 2 / ((K + 1 - s : ℕ) : ℝ) := htail
    _ ≤ 2 / ((K : ℝ) - (s : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) hdenpos hdenle

/-- The truncated inverse is measurable on the ambient disorder space. -/
theorem measurable_truncatedInverse (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Measurable (truncatedInverse β t i) := by
  have hmass : Measurable (blockMass β t i) :=
    (measurable_blockMass β t i).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hgood : MeasurableSet {ω | |blockMass β t i ω - 1| ≤ 1 / 2} :=
    measurableSet_le (hmass.sub measurable_const |>.abs) measurable_const
  unfold truncatedInverse
  exact Measurable.ite hgood hmass.inv measurable_const

/-- The truncated inverse is measurable on its single time block. -/
theorem measurable_truncatedInverse_block (β : ℝ) (t : ℕ → ℕ) (i : ℕ) :
    Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)] (truncatedInverse β t i) := by
  have hmass : Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)] (blockMass β t i) :=
    measurable_blockMass β t i
  have hgood : MeasurableSet[Gaussian.disorderBlock (t (i - 1)) (t i)]
      {ω | |blockMass β t i ω - 1| ≤ 1 / 2} := by
    have hreal : Measurable (fun x : ℝ => |x - 1|) := by fun_prop
    have h := hreal.comp hmass
    have hdefect : Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)]
        (fun ω => |blockMass β t i ω - 1|) := by
      have heq : (fun ω : Disorder => |blockMass β t i ω - 1|) =
          (fun x : ℝ => |x - 1|) ∘ blockMass β t i := by
        funext ω
        rfl
      exact heq ▸ h
    exact isClosed_Iic.measurableSet.preimage hdefect
  have hzero : Measurable[Gaussian.disorderBlock (t (i - 1)) (t i)]
      (fun _ : Disorder => (0 : ℝ)) := measurable_const
  unfold truncatedInverse
  exact Measurable.ite hgood hmass.inv hzero

private theorem measurable_truncatedCorrector (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (u v : ℕ) (huv : u < v) :
    Measurable (truncatedCorrector β t u v) := by
  have hprod : Measurable (fun ω => ∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω) := by
    apply Finset.measurable_prod
    intro i hi
    exact measurable_truncatedInverse β t i
  have hclosed : Measurable (fun ω => closedDiscrepancy β t u v ω) :=
    (measurable_closedDiscrepancy β t ht u v (Nat.le_of_lt huv)).mono
      (Gaussian.disorderBlock_le _ _) le_rfl
  change Measurable ((fun ω => closedDiscrepancy β t u v ω) *
    (fun ω => ∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω))
  exact hclosed.mul hprod

/-- Every finite product of inverse block masses is integrable. -/
theorem integrable_prod_inv_blockMass (β : ℝ) (t : ℕ → ℕ) (S : Finset ℕ) :
    Integrable (fun ω => ∏ i ∈ S, (blockMass β t i ω)⁻¹) disorderLaw := by
  classical
  let n := S.card
  by_cases hn : n = 0
  · have hS : S = ∅ := Finset.card_eq_zero.mp hn
    simp [hS]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let q : ℝ≥0∞ := n
    have hq0 : q ≠ 0 := by
      dsimp [q]
      exact_mod_cast hn
    have hqTop : q ≠ ∞ := by
      dsimp [q]
      exact ENNReal.natCast_ne_top _
    have hfactor (i : ℕ) :
        MemLp (fun ω => (blockMass β t i ω)⁻¹) q disorderLaw := by
      have hInvPow : Integrable (fun ω => (blockMass β t i ω)⁻¹ ^ (n : ℝ)) disorderLaw := by
        have hp := integrable_rpow_smoothedP2Plane β (t (i - 1)) (t i) 0 (- (n : ℝ))
        have hEq : (fun ω => (blockMass β t i ω)⁻¹ ^ (n : ℝ)) =
            fun ω => smoothedP2Plane β (t (i - 1)) (t i) 0 ω ^ (- (n : ℝ)) := by
          funext ω
          have hpos : 0 < smoothedP2Plane β (t (i - 1)) (t i) 0 ω :=
            Polymer.smoothedP2Plane_pos β (t (i - 1)) (t i) 0 ω
          calc
            (blockMass β t i ω)⁻¹ ^ (n : ℝ) =
                ((blockMass β t i ω)⁻¹) ^ n := Real.rpow_natCast _ _
            _ = (blockMass β t i ω ^ n)⁻¹ := inv_pow _ _
            _ = smoothedP2Plane β (t (i - 1)) (t i) 0 ω ^ (- (n : ℝ)) := by
              rw [blockMass, Real.rpow_neg (le_of_lt hpos), Real.rpow_natCast]
        exact hEq ▸ hp
      have hmeas : AEStronglyMeasurable (fun ω => (blockMass β t i ω)⁻¹) disorderLaw :=
        ((measurable_blockMass β t i).mono
          (Gaussian.disorderBlock_le _ _) le_rfl).inv.aestronglyMeasurable
      apply (integrable_norm_rpow_iff hmeas hq0 hqTop).mp
      have hnorm (ω : Disorder) :
          ‖(blockMass β t i ω)⁻¹‖ ^ q.toReal =
            (blockMass β t i ω)⁻¹ ^ (n : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (le_of_lt (blockMass_pos β t i ω)))]
        simp [q]
      exact hInvPow.congr (Eventually.of_forall fun ω => (hnorm ω).symm)
    have hprod : MemLp (fun ω => ∏ i ∈ S, (blockMass β t i ω)⁻¹)
        ((∑ i ∈ S, q⁻¹)⁻¹) disorderLaw := by
      apply MemLp.fun_prod
      intro i hi
      exact hfactor i
    have hcard : (S.card : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast hn
    have hsum : (∑ i ∈ S, q⁻¹) = 1 := by
      rw [Finset.sum_const, nsmul_eq_mul]
      dsimp [q, n]
      rw [ENNReal.mul_inv_cancel hcard (ENNReal.natCast_ne_top _)]
    have hprodMem : MemLp (fun ω => ∏ i ∈ S, (blockMass β t i ω)⁻¹) 1 disorderLaw := by
      simpa [hsum] using hprod
    exact hprodMem.integrable (by norm_num)

/-- Independence factors the inverse-mass integral over any finite set of positive block indices.
The integrability companion is `integrable_prod_inv_blockMass`. -/
theorem integral_finset_prod_inv_blockMass (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (S : Finset ℕ) (hS : ∀ i ∈ S, 1 ≤ i) :
    ∫ ω, ∏ i ∈ S, (blockMass β t i ω)⁻¹ ∂disorderLaw =
      ∏ i ∈ S, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
  classical
  let ι := {i : ℕ // i ∈ S}
  let emb : ι → {i : ℕ // 1 ≤ i} := fun i => ⟨i.val, hS i.val i.property⟩
  have hemb : Function.Injective emb := by
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun q : {i : ℕ // 1 ≤ i} => q.val) hij
  have hIndMass := (Critical2DKPZ.Blocks.iIndepFun_blockMass β t ht).precomp hemb
  have hIndInv :
      iIndepFun (fun i : ι => fun ω => (blockMass β t i.val ω)⁻¹) disorderLaw := by
    have h := hIndMass.comp (fun _ : ι => fun z : ℝ => z⁻¹) (fun _ => measurable_inv)
    convert h using 1
    ext i ω
    rfl
  have hInvInt (i : ι) : Integrable (fun ω => (blockMass β t i.val ω)⁻¹) disorderLaw :=
    integrable_blockMass_inv_and_sq β t i.val |>.1
  have hprodSub :
      ∫ ω, ∏ i : ι, (blockMass β t i.val ω)⁻¹ ∂disorderLaw =
        ∏ i : ι, ∫ ω, (blockMass β t i.val ω)⁻¹ ∂disorderLaw :=
    hIndInv.integral_fun_prod_eq_prod_integral fun i => (hInvInt i).aestronglyMeasurable
  have hprodAttach (f : ℕ → ℝ) :
      (∏ i : ι, f i.val) = ∏ i ∈ S, f i := by
    rw [Finset.univ_eq_attach, Finset.prod_attach]
  calc
    ∫ ω, ∏ i ∈ S, (blockMass β t i ω)⁻¹ ∂disorderLaw =
        ∫ ω, ∏ i : ι, (blockMass β t i.val ω)⁻¹ ∂disorderLaw := by
          congr 1
          funext ω
          exact (hprodAttach fun i => (blockMass β t i ω)⁻¹).symm
    _ = ∏ i : ι, ∫ ω, (blockMass β t i.val ω)⁻¹ ∂disorderLaw := hprodSub
    _ = ∏ i ∈ S, ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw :=
      hprodAttach fun i => ∫ ω, (blockMass β t i ω)⁻¹ ∂disorderLaw

/-- A one-block bad event factors from the inverse-mass product on all other blocks. -/
theorem setIntegral_prod_inv_blockMass_on_bad (β : ℝ) (t : ℕ → ℕ)
    (ht : Monotone t) (S : Finset ℕ) (hS : ∀ i ∈ S, 1 ≤ i)
    (i : ℕ) (hi : i ∈ S) :
    ∫ ω in {ω | 1 / 2 < |blockMass β t i ω - 1|},
        ∏ j ∈ S, (blockMass β t j ω)⁻¹ ∂disorderLaw =
      (∫ ω in {ω | 1 / 2 < |blockMass β t i ω - 1|},
        (blockMass β t i ω)⁻¹ ∂disorderLaw) *
        ∏ j ∈ S.erase i, ∫ ω, (blockMass β t j ω)⁻¹ ∂disorderLaw := by
  classical
  let ι := {j : ℕ // j ∈ S}
  let i₀ : ι := ⟨i, hi⟩
  let T : Finset ι := Finset.univ.erase i₀
  let i₁ : ↥({i₀} : Finset ι) := ⟨i₀, Finset.mem_singleton_self _⟩
  let Bad : Set ℝ := {z | (1 / 2 : ℝ) < |z - 1|}
  let bad : Set Disorder := {ω | (1 / 2 : ℝ) < |blockMass β t i ω - 1|}
  let Lmap : (T → ℝ) → ℝ := fun p => ∏ j : T, (p j)⁻¹
  let Rmap : (({i₀} : Finset ι) → ℝ) → ℝ := fun p =>
    Bad.indicator Inv.inv (p i₁)
  let Hrest : Disorder → ℝ := fun ω =>
    Lmap (fun j : T => blockMass β t j.val.val ω)
  let Hbad : Disorder → ℝ := fun ω => Rmap
    (fun j : ({i₀} : Finset ι) => blockMass β t j.val.val ω)
  have hTimage : T.image (fun j : ι => j.val) = S.erase i := by
    ext j
    simp [T, i₀, ι]
  have hTval : Set.InjOn (fun j : ι => j.val) T := by
    intro j hj k hk heq
    exact Subtype.ext heq
  have hIndMass : iIndepFun (fun j : ι => blockMass β t j.val) disorderLaw := by
    let emb : ι → {j : ℕ // 1 ≤ j} := fun j => ⟨j.val, hS j.val j.property⟩
    have hemb : Function.Injective emb := by
      intro j k hjk
      exact Subtype.ext (congrArg (fun z : {j : ℕ // 1 ≤ j} => z.val) hjk)
    exact (Critical2DKPZ.Blocks.iIndepFun_blockMass β t ht).precomp hemb
  have hmeasMass (j : ι) : Measurable (blockMass β t j.val) :=
    (measurable_blockMass β t j.val).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hdisj : Disjoint T {i₀} := by
    apply Finset.disjoint_left.mpr
    intro j hjT hj0
    have hjne : j ≠ i₀ := by simpa [T] using hjT
    have hjEq : j = i₀ := Finset.mem_singleton.mp hj0
    exact hjne hjEq
  have hTuple := hIndMass.indepFun_finset T {i₀} hdisj hmeasMass
  have hLmapMeas : Measurable Lmap := by
    dsimp [Lmap]
    exact Finset.univ.measurable_fun_prod fun j _ => (measurable_pi_apply j).inv
  have hBadMeas : MeasurableSet Bad := by
    dsimp [Bad]
    exact measurableSet_lt measurable_const ((measurable_id.sub measurable_const).abs)
  have hRmapMeas : Measurable Rmap := by
    dsimp [Rmap]
    exact (measurable_inv.indicator hBadMeas).comp (measurable_pi_apply i₁)
  have hInd := hTuple.comp hLmapMeas hRmapMeas
  have hmassMeas : Measurable (blockMass β t i) :=
    (measurable_blockMass β t i).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hbadMeas : MeasurableSet bad := by
    dsimp [bad]
    exact measurableSet_lt measurable_const (hmassMeas.sub measurable_const |>.abs)
  have hrestPoint (ω : Disorder) : Hrest ω =
      ∏ j ∈ S.erase i, (blockMass β t j ω)⁻¹ := by
    dsimp [Hrest, Lmap]
    calc
      (∏ j : T, (blockMass β t j.val.val ω)⁻¹) =
          ∏ j ∈ T, (blockMass β t j.val ω)⁻¹ := by
            rw [Finset.univ_eq_attach]
            exact Finset.prod_attach T (fun j : ι => (blockMass β t j.val ω)⁻¹)
      _ = ∏ j ∈ T.image (fun j : ι => j.val), (blockMass β t j ω)⁻¹ := by
            rw [Finset.prod_image hTval]
      _ = ∏ j ∈ S.erase i, (blockMass β t j ω)⁻¹ := by rw [hTimage]
  have hrestInt : Integrable Hrest disorderLaw := by
    apply (integrable_prod_inv_blockMass β t (S.erase i)).congr
    exact Eventually.of_forall fun ω => (hrestPoint ω).symm
  have hrestIntEq : ∫ ω, Hrest ω ∂disorderLaw =
      ∏ j ∈ S.erase i, ∫ ω, (blockMass β t j ω)⁻¹ ∂disorderLaw := by
    calc
      ∫ ω, Hrest ω ∂disorderLaw =
          ∫ ω, ∏ j ∈ S.erase i, (blockMass β t j ω)⁻¹ ∂disorderLaw := by
            apply integral_congr_ae
            exact Eventually.of_forall hrestPoint
      _ = ∏ j ∈ S.erase i, ∫ ω, (blockMass β t j ω)⁻¹ ∂disorderLaw :=
            integral_finset_prod_inv_blockMass β t ht (S.erase i) (by
              intro j hj
              exact hS j (Finset.mem_of_mem_erase hj))
  have hbadPoint (ω : Disorder) : Hbad ω =
      bad.indicator (fun ω => (blockMass β t i ω)⁻¹) ω := by
    change Bad.indicator Inv.inv (blockMass β t i ω) =
      bad.indicator (fun ω => (blockMass β t i ω)⁻¹) ω
    rw [Set.indicator_apply, Set.indicator_apply]
    rfl
  have hbadInt : Integrable Hbad disorderLaw := by
    have hinv := integrable_blockMass_inv_and_sq β t i |>.1
    apply (hinv.indicator hbadMeas).congr
    exact Eventually.of_forall fun ω => (hbadPoint ω).symm
  have hIndFactor : ∫ ω, Hrest ω * Hbad ω ∂disorderLaw =
      (∫ ω, Hrest ω ∂disorderLaw) * (∫ ω, Hbad ω ∂disorderLaw) := by
    simpa [Hrest, Hbad, Lmap, Rmap] using
      hInd.integral_mul_eq_mul_integral hrestInt.aestronglyMeasurable
        hbadInt.aestronglyMeasurable
  have hprodErase (ω : Disorder) :
      (∏ j ∈ S, (blockMass β t j ω)⁻¹) = Hrest ω * (blockMass β t i ω)⁻¹ := by
    rw [hrestPoint]
    exact (Finset.prod_erase_mul S (fun j => (blockMass β t j ω)⁻¹) hi).symm
  have hnumEq :
      ∫ ω in bad, ∏ j ∈ S, (blockMass β t j ω)⁻¹ ∂disorderLaw =
        ∫ ω, Hrest ω * Hbad ω ∂disorderLaw := by
    rw [← integral_indicator hbadMeas]
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [hbadPoint ω]
    by_cases hω : ω ∈ bad
    · simp [hω, hprodErase, mul_comm]
    · simp [hω]
  have hbadIntegral : ∫ ω, Hbad ω ∂disorderLaw =
      ∫ ω in bad, (blockMass β t i ω)⁻¹ ∂disorderLaw := by
    calc
      ∫ ω, Hbad ω ∂disorderLaw =
          ∫ ω, bad.indicator (fun ω => (blockMass β t i ω)⁻¹) ω ∂disorderLaw := by
            apply integral_congr_ae
            filter_upwards [] with ω
            exact hbadPoint ω
      _ = ∫ ω in bad, (blockMass β t i ω)⁻¹ ∂disorderLaw :=
            integral_indicator hbadMeas
  rw [hnumEq, hIndFactor, hrestIntEq, hbadIntegral]
  ring

/-- On the block good set, a family ratio is the product of its truncated correctors. -/
theorem familyTerm_eq_corrector_prod_on_goodSet (β : ℝ) (t : ℕ → ℕ)
    {r s : ℕ} (F : Finset (ℕ × ℕ)) (hF : F ∈ intervalFamilies r s)
    {ω : Disorder} (hω : ω ∈ blockGoodSet β t r s) :
    familyTerm β t F ω = ∏ I ∈ F, truncatedCorrector β t I.1 I.2 ω := by
  classical
  unfold familyTerm
  apply Finset.prod_congr rfl
  intro I hI
  have hIbounds := (intervalFamilies_mem_iff r s F).mp hF |>.1 I hI
  have hmassInv :
      (∏ i ∈ Finset.Icc I.1 I.2, truncatedInverse β t i ω) =
        (∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω)⁻¹ := by
    calc
      (∏ i ∈ Finset.Icc I.1 I.2, truncatedInverse β t i ω) =
          ∏ i ∈ Finset.Icc I.1 I.2, (blockMass β t i ω)⁻¹ := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' := Finset.mem_Icc.mp hi
        have hgood : |blockMass β t i ω - 1| ≤ 1 / 2 := by
          change ∀ j ∈ Finset.Icc r s, |blockMass β t j ω - 1| ≤ 1 / 2 at hω
          apply hω i
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        unfold truncatedInverse
        rw [ite_eq_left hgood]
      _ = (∏ i ∈ Finset.Icc I.1 I.2, blockMass β t i ω)⁻¹ :=
        Finset.prod_inv_distrib _
  simp [truncatedCorrector, hmassInv, div_eq_mul_inv]

/-- The square of a truncated corrector is integrable. -/
theorem integrable_sq_truncatedCorrector (β : ℝ) (t : ℕ → ℕ) (ht : Monotone t)
    (u v : ℕ) (huv : u < v) :
    Integrable (fun ω => truncatedCorrector β t u v ω ^ 2) disorderLaw := by
  let B : ℝ := (2 ^ (v - u + 1 : ℕ)) ^ 2
  have hbase := integrable_sq_closedDiscrepancy β t u v
  have hmajor : Integrable (fun ω => B * closedDiscrepancy β t u v ω ^ 2) disorderLaw :=
    hbase.const_mul B
  have hmeas := (measurable_truncatedCorrector β t ht u v huv).pow_const 2
  apply hmajor.mono' hmeas.aestronglyMeasurable
  filter_upwards [] with ω
  have hprod : |∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω| ≤
      2 ^ (Finset.Icc u v).card := by
    rw [Finset.abs_prod]
    calc
      ∏ i ∈ Finset.Icc u v, |truncatedInverse β t i ω| ≤
          ∏ i ∈ Finset.Icc u v, (2 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact abs_nonneg _
        · intro i hi
          have hM := truncatedInverse_nonneg_le_two β t i ω
          rw [abs_of_nonneg hM.1]
          exact hM.2
      _ = 2 ^ (Finset.Icc u v).card := by simp
  have hcard : (Finset.Icc u v).card = v - u + 1 := by
    simp only [Nat.card_Icc]
    omega
  have hfactor : |truncatedCorrector β t u v ω| ≤
      2 ^ (v - u + 1) * |closedDiscrepancy β t u v ω| := by
    rw [truncatedCorrector, abs_mul]
    calc
      |closedDiscrepancy β t u v ω| *
          |∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω| ≤
        |closedDiscrepancy β t u v ω| * 2 ^ (Finset.Icc u v).card :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
      _ = 2 ^ (v - u + 1) * |closedDiscrepancy β t u v ω| := by
        rw [hcard]
        ring
  have hsq : truncatedCorrector β t u v ω ^ 2 ≤
      B * closedDiscrepancy β t u v ω ^ 2 := by
    have hsq' : |truncatedCorrector β t u v ω| ^ 2 ≤
        (2 ^ (v - u + 1) * |closedDiscrepancy β t u v ω|) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).2 hfactor
    calc
      truncatedCorrector β t u v ω ^ 2 ≤ |truncatedCorrector β t u v ω| ^ 2 := by
        rw [sq_abs]
      _ ≤ (2 ^ (v - u + 1) * |closedDiscrepancy β t u v ω|) ^ 2 := hsq'
      _ = B * closedDiscrepancy β t u v ω ^ 2 := by
        simp [B, mul_pow, sq_abs]
  rw [Real.norm_of_nonneg (sq_nonneg (truncatedCorrector β t u v ω))]
  exact hsq

/-- The truncated corrector has a geometric second-moment bound with inverse endpoint-distance factors. -/
theorem integral_truncatedCorrector_sq_le (A : ℝ) :
    ∃ C₀ ρ₀ C : ℝ, 0 < C₀ ∧ 1 < ρ₀ ∧
      ∀ ρ : ℝ, ρ₀ ≤ ρ → ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ u v : ℕ, 1 ≤ u → u < v → v + 1 ≤ blockCount N ρ →
          ∫ ω, truncatedCorrector (criticalBeta ϑ N) (blockTime N ρ) u v ω ^ 2 ∂disorderLaw ≤
            (C * (C₀ / Real.sqrt (Real.log ρ)) ^ (v - u)) ^ 2 /
              (((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v)) := by
  obtain ⟨Ck, C₀, hC₀, hDiscrepancyStringInput⟩ := Critical2DKPZ.Blocks.closedDiscrepancy_sq_integral_le A
  let ρ₀ : ℝ := Real.exp (C₀ ^ 2) + 1
  let C : ℝ := 2 * Ck
  have hρ₀ : 1 < ρ₀ := by
    dsimp [ρ₀]
    have hexp : 0 < Real.exp (C₀ ^ 2) := Real.exp_pos _
    linarith
  refine ⟨2 * C₀, ρ₀, C, by positivity, ?_, ?_⟩
  · exact hρ₀
  · intro ρ hρ₀ρ
    have hthreshold : Real.exp (C₀ ^ 2) < ρ := by
      have hexp : 0 < Real.exp (C₀ ^ 2) := Real.exp_pos _
      dsimp [ρ₀] at hρ₀ρ
      linarith
    have hNclock : ∀ᶠ N : ℕ in atTop,
        ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N := Filter.eventually_ge_atTop _
    filter_upwards [hDiscrepancyStringInput ρ hthreshold, hNclock] with N hDiscrepancyStringInputN hNclock
    intro ϑ hϑ u v hu huv hvK
    let β := criticalBeta ϑ N
    let t := blockTime N ρ
    let B : ℝ := (2 ^ (v - u + 1 : ℕ)) ^ 2
    have ht : Monotone t := by
      exact Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon
        hρ₀ hρ₀ρ hNclock
    have htruncInt := integrable_sq_truncatedCorrector β t ht u v huv
    have hclosedInt := integrable_sq_closedDiscrepancy β t u v
    have hmajor : Integrable (fun ω => B * closedDiscrepancy β t u v ω ^ 2) disorderLaw :=
      hclosedInt.const_mul B
    have hpoint (ω : Disorder) : truncatedCorrector β t u v ω ^ 2 ≤
        B * closedDiscrepancy β t u v ω ^ 2 := by
      have hprod : |∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω| ≤
          2 ^ (Finset.Icc u v).card := by
        rw [Finset.abs_prod]
        calc
          ∏ i ∈ Finset.Icc u v, |truncatedInverse β t i ω| ≤
              ∏ i ∈ Finset.Icc u v, (2 : ℝ) := by
            apply Finset.prod_le_prod₀
            · intro i hi
              exact abs_nonneg _
            · intro i hi
              have hM := truncatedInverse_nonneg_le_two β t i ω
              rw [abs_of_nonneg hM.1]
              exact hM.2
          _ = 2 ^ (Finset.Icc u v).card := by simp
      have hcard : (Finset.Icc u v).card = v - u + 1 := by
        simp only [Nat.card_Icc]
        omega
      have hfactor : |truncatedCorrector β t u v ω| ≤
          2 ^ (v - u + 1) * |closedDiscrepancy β t u v ω| := by
        rw [truncatedCorrector, abs_mul]
        calc
          |closedDiscrepancy β t u v ω| *
              |∏ i ∈ Finset.Icc u v, truncatedInverse β t i ω| ≤
            |closedDiscrepancy β t u v ω| * 2 ^ (Finset.Icc u v).card :=
              mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
          _ = 2 ^ (v - u + 1) * |closedDiscrepancy β t u v ω| := by
            rw [hcard]
            ring
      have hsq' : |truncatedCorrector β t u v ω| ^ 2 ≤
          (2 ^ (v - u + 1) * |closedDiscrepancy β t u v ω|) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).2 hfactor
      calc
        truncatedCorrector β t u v ω ^ 2 ≤ |truncatedCorrector β t u v ω| ^ 2 := by
          rw [sq_abs]
        _ ≤ (2 ^ (v - u + 1) * |closedDiscrepancy β t u v ω|) ^ 2 := hsq'
        _ = B * closedDiscrepancy β t u v ω ^ 2 := by simp [B, mul_pow, sq_abs]
    have hmono :
        ∫ ω, truncatedCorrector β t u v ω ^ 2 ∂disorderLaw ≤
          B * ∫ ω, closedDiscrepancy β t u v ω ^ 2 ∂disorderLaw := by
      calc
        ∫ ω, truncatedCorrector β t u v ω ^ 2 ∂disorderLaw ≤
            ∫ ω, B * closedDiscrepancy β t u v ω ^ 2 ∂disorderLaw :=
          integral_mono_ae htruncInt hmajor (Eventually.of_forall hpoint)
        _ = B * ∫ ω, closedDiscrepancy β t u v ω ^ 2 ∂disorderLaw := by
          rw [integral_const_mul]
    have hDiscrepancyStringInputBound := hDiscrepancyStringInputN ϑ hϑ u v hu huv hvK
    let n : ℕ := v - u
    let α : ℝ := C₀ / Real.sqrt (Real.log ρ)
    have hscale : B * (Ck * α ^ n) ^ 2 = (C * (C₀ * 2 / Real.sqrt (Real.log ρ)) ^ n) ^ 2 := by
      have hpow : (2 : ℝ) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
      dsimp [B, C, n, α]
      rw [show v - u + 1 = (v - u) + 1 by omega, pow_succ]
      rw [mul_pow]
      rw [← mul_pow]
      rw [hpow]
      ring
    have hdenom : 0 <
        ((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v) := by
      have huK : u < blockCount N ρ := by omega
      have hvK : v < blockCount N ρ := by omega
      exact mul_pos
        (by
          have hcast : (u : ℝ) < (blockCount N ρ : ℝ) := by exact_mod_cast huK
          linarith)
        (by
          have hcast : (v : ℝ) < (blockCount N ρ : ℝ) := by exact_mod_cast hvK
          linarith)
    calc
      ∫ ω, truncatedCorrector β t u v ω ^ 2 ∂disorderLaw ≤
          B * ∫ ω, closedDiscrepancy β t u v ω ^ 2 ∂disorderLaw := hmono
      _ ≤ B * ((Ck * α ^ n) ^ 2 /
            (((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v))) :=
        mul_le_mul_of_nonneg_left hDiscrepancyStringInputBound (sq_nonneg _)
      _ = (C * (C₀ / Real.sqrt (Real.log ρ) * 2) ^ (v - u)) ^ 2 /
            (((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v)) := by
        rw [← mul_div_assoc, hscale]
        congr 2
        dsimp [α, n]
        ring
      _ = (C * (2 * C₀ / Real.sqrt (Real.log ρ)) ^ (v - u)) ^ 2 /
            (((blockCount N ρ : ℝ) - u) * ((blockCount N ρ : ℝ) - v)) := by
        congr 2
        congr 1
        ring

/-- The bad-event probability is bounded by the inverse distance to the terminal block, assuming the block-moment bounds. -/
theorem measure_blockGoodSet_compl_le_of (hC6 : BlockMomentsBound)
    (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ r s : ℕ, 1 ≤ r → r ≤ s → s + 1 ≤ blockCount N ρ →
        (disorderLaw (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
          C / ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨C₆, hC₆⟩ := hC6 A ρ₀ ρ₁ hρ
  refine ⟨32 * |C₆|, ?_⟩
  intro ρ hρρ
  have hC₆ρ := hC₆ ρ hρρ
  filter_upwards [hC₆ρ] with N hC₆N
  intro ϑ hϑ r s hr hrs hsK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let K := blockCount N ρ
  let bad : ℕ → Set Disorder := fun i =>
    {ω | (1 / 2 : ℝ) < |blockMass β t i ω - 1|}
  have hbadSet : (blockGoodSet β t r s)ᶜ =
      ⋃ i ∈ Finset.Icc r s, bad i := by
    ext ω
    simp [blockGoodSet, bad, Finset.mem_Icc, not_le, and_assoc]
  have htail := sum_shifted_inv_sq_le hrs hsK
  have hKsub : s < K := by dsimp [K]; omega
  have hbad (i : ℕ) (hi : i ∈ Finset.Icc r s) :
      (disorderLaw (bad i)).toReal ≤
        16 * |C₆| / ((K : ℝ) + 1 - i) ^ 2 := by
    have hi' := Finset.mem_Icc.mp hi
    have hiK : i ≤ K := by omega
    have hmomentPair := hC₆N ϑ hϑ i (le_trans hr hi'.1) hiK
    have hmoment :
        ∫ ω, |blockMass β t i ω - 1| ^ 4 ∂disorderLaw ≤
          C₆ / ((K : ℝ) + 1 - i) ^ 2 := by
      simpa [β, t, K, blockMass] using hmomentPair.2
    have hmeas : Measurable (fun ω => blockMass β t i ω - 1) := by
      exact ((measurable_blockMass β t i).mono
        (Gaussian.disorderBlock_le _ _) le_rfl).sub measurable_const
    have hdevMem : MemLp (fun ω => blockMass β t i ω - 1) (4 : ℝ≥0∞) disorderLaw := by
      have hZ : MemLp (fun ω => smoothedP2Plane β (t (i - 1)) (t i) 0 ω)
          (4 : ℝ≥0∞) disorderLaw :=
        Polymer.memLp_smoothedP2Plane β (t (i - 1)) (t i) 0 4 (by norm_num)
      have hconst : MemLp (fun _ : Disorder => (1 : ℝ)) (4 : ℝ≥0∞) disorderLaw :=
        memLp_const (1 : ℝ)
      change MemLp ((fun ω => smoothedP2Plane β (t (i - 1)) (t i) 0 ω) -
        (fun _ : Disorder => (1 : ℝ))) (4 : ℝ≥0∞) disorderLaw
      exact hZ.sub hconst
    have hdevInt : Integrable (fun ω => |blockMass β t i ω - 1| ^ 4) disorderLaw := by
      have h := hdevMem.integrable_norm_pow'
      simpa only [Real.norm_eq_abs] using h
    have hmarkov := measure_abs_gt_half_le_integral_four
      (fun ω => blockMass β t i ω - 1) hmeas hdevInt
    have hmomentAbs :
        ∫ ω, |blockMass β t i ω - 1| ^ 4 ∂disorderLaw ≤
          |C₆| / ((K : ℝ) + 1 - i) ^ 2 := by
      exact le_trans hmoment
        (div_le_div_of_nonneg_right (le_abs_self C₆) (sq_nonneg _))
    calc
      (disorderLaw (bad i)).toReal ≤
          16 * ∫ ω, |blockMass β t i ω - 1| ^ 4 ∂disorderLaw := hmarkov
      _ ≤ 16 * (|C₆| / ((K : ℝ) + 1 - i) ^ 2) :=
        mul_le_mul_of_nonneg_left hmomentAbs (by norm_num)
      _ = 16 * |C₆| / ((K : ℝ) + 1 - i) ^ 2 := by ring
  have hunion := measureReal_biUnion_finset_le
    (μ := disorderLaw) (Finset.Icc r s) bad
  rw [← hbadSet] at hunion
  have hsum := Finset.sum_le_sum hbad
  change (disorderLaw (blockGoodSet β t r s)ᶜ).toReal ≤
    32 * |C₆| / ((K : ℝ) - s)
  calc
    (disorderLaw (blockGoodSet β t r s)ᶜ).toReal ≤
        ∑ i ∈ Finset.Icc r s, (disorderLaw (bad i)).toReal := by
      simpa only [Measure.real] using hunion
    _ ≤ ∑ i ∈ Finset.Icc r s, 16 * |C₆| / ((K : ℝ) + 1 - i) ^ 2 := hsum
    _ = 16 * |C₆| * ∑ i ∈ Finset.Icc r s,
          1 / ((K : ℝ) + 1 - i) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ 32 * |C₆| / ((K : ℝ) - s) := by
      calc
        16 * |C₆| * ∑ i ∈ Finset.Icc r s,
              1 / ((K : ℝ) + 1 - i) ^ 2 ≤
            16 * |C₆| * (2 / ((K : ℝ) - s)) :=
          mul_le_mul_of_nonneg_left htail (by positivity)
        _ = 32 * |C₆| / ((K : ℝ) - s) := by ring

/-- Block-moment bounds and componentwise pair-integral bounds control the bad-event probability and good-event block-ratio second moment. -/
theorem blockGoodSet_compl_and_ratio_bound_pair_of (hC6 : BlockMomentsBound) (A : ℝ)
    (hPair : ∃ C₀ ρp Cpair : ℝ, 0 < C₀ ∧ 1 < ρp ∧ 1 ≤ Cpair ∧
      ∀ ρ : ℝ, ρp ≤ ρ → ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s →
          s + 1 ≤ blockCount N ρ →
          ∀ F ∈ intervalFamilies r s, ∀ G ∈ intervalFamilies r s,
            |∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
                familyTerm (criticalBeta ϑ N) (blockTime N ρ) F ω *
                  familyTerm (criticalBeta ϑ N) (blockTime N ρ) G ω ∂disorderLaw| ≤
              ∏ c ∈ pairComponents r s F G,
                componentWeight (Cpair * C₀ / Real.sqrt (Real.log ρ))
                  (blockCount N ρ) F G c) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ₁ : ℝ, ∃ C : ℝ,
      ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop,
        ∀ ϑ ∈ Set.Icc (-A) A, ∀ r s : ℕ, 1 ≤ r → r ≤ s →
          s + 1 ≤ blockCount N ρ →
            (disorderLaw (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
              C / ((blockCount N ρ : ℝ) - s) ∧
            ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
                (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω - 1) ^ 2
                  ∂disorderLaw ≤ C / ((blockCount N ρ : ℝ) - s) := by
  obtain ⟨C₀, ρp, Cpair, hC₀, hρp, hCpair, hPair⟩ := hPair
  obtain ⟨ε₀, Csum, hε₀, hCsum, hsum⟩ := sum_prod_componentWeight_le
  let q : ℝ := Cpair * C₀ / ε₀
  let ρ₀ : ℝ := max (ρp + 1) (Real.exp (q ^ 2) + 1)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hρ₀ : 1 < ρ₀ := by
    dsimp [ρ₀]
    exact lt_of_lt_of_le (by linarith [hρp]) (le_max_left _ _)
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ₁
  obtain ⟨εcomp, hcomp⟩ :=
    measure_blockGoodSet_compl_le_of hC6 A ρ₀ ρ₁ hρ₀
  let C : ℝ := max εcomp (Csum * ε₀)
  refine ⟨C, ?_⟩
  intro ρ hρρ
  have hρpρ : ρp ≤ ρ := by
    have hρ₀ρ : ρ₀ ≤ ρ := hρρ.1
    have hleft : ρp + 1 ≤ ρ := le_trans (le_max_left _ _) hρ₀ρ
    linarith
  have hexpρ : Real.exp (q ^ 2) < ρ := by
    have hright : Real.exp (q ^ 2) + 1 ≤ ρ :=
      le_trans (le_max_right _ _) hρρ.1
    linarith
  have hlogρ : q ^ 2 < Real.log ρ := by
    simpa only [Real.log_exp] using
      Real.log_lt_log (Real.exp_pos (q ^ 2)) hexpρ
  have hqle : q ≤ Real.sqrt (Real.log ρ) := by
    have hqnonneg : 0 ≤ q := le_of_lt hqpos
    have hsqrtq : Real.sqrt (q ^ 2) = q := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hqnonneg]
    rw [← hsqrtq]
    exact Real.sqrt_le_sqrt (le_of_lt hlogρ)
  have hε : 0 ≤ Cpair * C₀ / Real.sqrt (Real.log ρ) := by positivity
  have hεle : Cpair * C₀ / Real.sqrt (Real.log ρ) ≤ ε₀ := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 (Real.log_pos (by
      have : 1 < ρ := lt_of_lt_of_le hρ₀ hρρ.1
      linarith)))]
    have hmul := mul_le_mul_of_nonneg_left hqle (le_of_lt hε₀)
    dsimp [q] at hmul
    field_simp [ne_of_gt hε₀] at hmul
    exact hmul
  have hclock : ∀ᶠ N : ℕ in atTop,
      ⌈2 * ρ₀ / (ρ₀ - 1)⌉₊ ≤ N := Filter.eventually_ge_atTop _
  filter_upwards [hcomp ρ ⟨hρρ.1, hρρ.2⟩,
    hPair ρ hρpρ, hclock] with N hcompN hPairN hN
  intro ϑ hϑ r s hr hrs hsK
  have ht : Monotone (blockTime N ρ) :=
    Critical2DKPZ.MomentBounds.blockTime_monotone_of_large_horizon hρ₀ hρρ.1 hN
  have hratioExp := setIntegral_blockRatio_sub_one_sq_eq
    (criticalBeta ϑ N) ht hr hrs
  have hpairSum :
      (∑ F ∈ (intervalFamilies r s).erase ∅,
        ∑ G ∈ (intervalFamilies r s).erase ∅,
          ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
            familyTerm (criticalBeta ϑ N) (blockTime N ρ) F ω *
              familyTerm (criticalBeta ϑ N) (blockTime N ρ) G ω ∂disorderLaw) ≤
        ∑ F ∈ (intervalFamilies r s).erase ∅,
          ∑ G ∈ (intervalFamilies r s).erase ∅,
            ∏ c ∈ pairComponents r s F G,
              componentWeight (Cpair * C₀ / Real.sqrt (Real.log ρ))
                (blockCount N ρ) F G c := by
    apply Finset.sum_le_sum
    intro F hF
    apply Finset.sum_le_sum
    intro G hG
    have h := hPairN ϑ hϑ r s hr hrs hsK F
      (Finset.mem_of_mem_erase hF) G (Finset.mem_of_mem_erase hG)
    exact le_trans (le_abs_self _) h
  have hcompSum := hsum (Cpair * C₀ / Real.sqrt (Real.log ρ)) hε
    hεle (blockCount N ρ) r s hr hrs (by omega)
  have hsecond :
      ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
        (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω - 1) ^ 2 ∂disorderLaw ≤
          Csum * (Cpair * C₀ / Real.sqrt (Real.log ρ)) /
            ((blockCount N ρ : ℝ) - s) := by
    rw [hratioExp]
    exact hpairSum.trans hcompSum
  have hgap : 0 < (blockCount N ρ : ℝ) - s := by
    have hnat : 0 < blockCount N ρ - s := by omega
    rw [← Nat.cast_sub (by omega : s ≤ blockCount N ρ)]
    exact_mod_cast hnat
  have hsecondBound :
      ∫ ω in blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s,
        (blockRatio (criticalBeta ϑ N) (blockTime N ρ) r s ω - 1) ^ 2 ∂disorderLaw ≤
          C / ((blockCount N ρ : ℝ) - s) := by
    dsimp [C]
    calc
      _ ≤ (Csum * ε₀) / ((blockCount N ρ : ℝ) - s) := by
        apply hsecond.trans
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hεle hCsum.le) (le_of_lt hgap)
      _ ≤ max εcomp (Csum * ε₀) / ((blockCount N ρ : ℝ) - s) :=
        div_le_div_of_nonneg_right (le_max_right _ _) (le_of_lt hgap)
  have hcomplementBound :
      (disorderLaw (blockGoodSet (criticalBeta ϑ N) (blockTime N ρ) r s)ᶜ).toReal ≤
        C / ((blockCount N ρ : ℝ) - s) := by
    dsimp [C]
    exact le_trans (hcompN ϑ hϑ r s hr hrs hsK)
      (div_le_div_of_nonneg_right (le_max_left _ _) (le_of_lt hgap))
  exact ⟨hcomplementBound, hsecondBound⟩

/-- Under the inverse-mass tilted law, the one-block bad-event probability has an inverse three-halves endpoint-distance bound, assuming the block-moment bounds. -/
theorem tilted_blockMass_bad_le_of (hC6 : BlockMomentsBound)
    (A ρ₀ ρ₁ : ℝ) (hρ : 1 < ρ₀) :
    ∃ C : ℝ, ∀ ρ ∈ Set.Icc ρ₀ ρ₁, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      ∀ i : ℕ, 1 ≤ i → i + 1 ≤ blockCount N ρ →
        (∫ ω in {ω | 1 / 2 < |blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω - 1|},
            (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) /
          (∫ ω, (blockMass (criticalBeta ϑ N) (blockTime N ρ) i ω)⁻¹ ∂disorderLaw) ≤
            C / ((blockCount N ρ : ℝ) - i) ^ ((3 : ℝ) / 2) := by
  obtain ⟨C₆, hC₆⟩ := hC6 A ρ₀ ρ₁ hρ
  obtain ⟨Cinv, hCinv⟩ :=
    integral_inv_blockMass_pow_four_le_of hC6 A ρ₀ ρ₁ hρ
  let D : ℝ := max (max |C₆| Cinv) 1
  let C : ℝ := (16 * D) ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 4)
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hC₆le : |C₆| ≤ D := by
    dsimp [D]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCinle : Cinv ≤ D := by
    dsimp [D]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨C, ?_⟩
  intro ρ hρρ
  filter_upwards [hC₆ ρ hρρ, hCinv ρ hρρ] with N hC₆N hCinvN
  intro ϑ hϑ i hi hiK
  let β := criticalBeta ϑ N
  let t := blockTime N ρ
  let Z : Disorder → ℝ := blockMass β t i
  let d : ℝ := (blockCount N ρ : ℝ) - i
  have hdpos : 0 < d := by
    dsimp [d]
    have hnat : 0 < blockCount N ρ - i := by omega
    rw [← Nat.cast_sub (show i ≤ blockCount N ρ by omega)]
    exact_mod_cast hnat
  have hdSqPos : 0 < d ^ 2 := by positivity
  have hgap : 1 ≤ d := by
    dsimp [d]
    have hnat : 1 ≤ blockCount N ρ - i := by omega
    rw [← Nat.cast_sub (show i ≤ blockCount N ρ by omega)]
    exact_mod_cast hnat
  have hdenC₆ : (blockCount N ρ : ℝ) + 1 - i = d + 1 := by
    dsimp [d]
    ring
  have hmomentRaw :
      ∫ ω, |Z ω - 1| ^ 4 ∂disorderLaw ≤
        C₆ / ((blockCount N ρ : ℝ) + 1 - i) ^ 2 := by
    simpa [Z, β, t, blockMass] using (hC₆N ϑ hϑ i hi (by omega)).2
  rw [hdenC₆] at hmomentRaw
  have hmoment : ∫ ω, |Z ω - 1| ^ 4 ∂disorderLaw ≤ D / d ^ 2 := by
    have hdsq : d ^ 2 ≤ (d + 1) ^ 2 := by nlinarith
    calc
      ∫ ω, |Z ω - 1| ^ 4 ∂disorderLaw ≤ C₆ / (d + 1) ^ 2 := hmomentRaw
      _ ≤ |C₆| / (d + 1) ^ 2 :=
        div_le_div_of_nonneg_right (le_abs_self C₆) (sq_nonneg _)
      _ ≤ |C₆| / d ^ 2 := div_le_div_of_nonneg_left
        (abs_nonneg C₆) hdSqPos hdsq
      _ ≤ D / d ^ 2 := div_le_div_of_nonneg_right hC₆le (sq_nonneg _)
  have hZmem : MemLp Z (4 : ℝ≥0∞) disorderLaw := by
    dsimp [Z, β, t, blockMass]
    exact Polymer.memLp_smoothedP2Plane _ _ _ _ 4 (by norm_num)
  have hconst : MemLp (fun _ : Disorder => (1 : ℝ)) (4 : ℝ≥0∞) disorderLaw :=
    memLp_const (1 : ℝ)
  have hXmem : MemLp (fun ω => Z ω - 1) (4 : ℝ≥0∞) disorderLaw := by
    exact hZmem.sub hconst
  have hXint : Integrable (fun ω => |Z ω - 1| ^ 4) disorderLaw := by
    have h := hXmem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using h
  have hXmeas : Measurable (fun ω => Z ω - 1) := by
    exact ((measurable_blockMass β t i).mono
      (Gaussian.disorderBlock_le _ _) le_rfl).sub measurable_const
  have hPbad := measure_abs_gt_half_le_integral_four
    (fun ω => Z ω - 1) hXmeas hXint
  let bad : Set Disorder := {ω | (1 / 2 : ℝ) < |Z ω - 1|}
  have hbad : (disorderLaw bad).toReal ≤ 16 * D / d ^ 2 := by
    calc
      (disorderLaw bad).toReal ≤
          16 * ∫ ω, |Z ω - 1| ^ 4 ∂disorderLaw := by
        simpa [bad] using hPbad
      _ ≤ 16 * (D / d ^ 2) := mul_le_mul_of_nonneg_left hmoment (by norm_num)
      _ = 16 * D / d ^ 2 := by ring
  let H : Disorder → ℝ := fun ω => (Z ω)⁻¹
  let G : Disorder → ℝ := bad.indicator (fun _ => (1 : ℝ))
  have hbadMeas : MeasurableSet bad := by
    exact measurableSet_lt measurable_const hXmeas.abs
  have hGnonneg (ω : Disorder) : 0 ≤ G ω := by
    by_cases hω : ω ∈ bad <;> simp [G, hω]
  have hGmem : MemLp G (ENNReal.ofReal ((4 : ℝ) / 3)) disorderLaw :=
    memLp_indicator_const _ hbadMeas (1 : ℝ)
      (Or.inr (measure_ne_top disorderLaw bad))
  have hHnonneg (ω : Disorder) : 0 ≤ H ω := by
    dsimp [H, Z]
    exact inv_nonneg.mpr (le_of_lt (blockMass_pos β t i ω))
  have hHint : Integrable H disorderLaw := by
    simpa [H, Z, β, t] using (integrable_blockMass_inv_and_sq β t i).1
  have hHfourInt : Integrable (fun ω => H ω ^ 4) disorderLaw := by
    simpa [H, Z] using integrable_blockMass_inv_pow_four β t i
  have hHmem : MemLp H (ENNReal.ofReal (4 : ℝ)) disorderLaw := by
    apply (integrable_norm_rpow_iff hHint.aestronglyMeasurable
      (by norm_num) (by simp)).mp
    have hpoint (ω : Disorder) : ‖H ω‖ ^ (4 : ℝ) = H ω ^ 4 := by
      calc
        ‖H ω‖ ^ (4 : ℝ) = ‖H ω‖ ^ 4 := Real.rpow_natCast _ _
        _ = H ω ^ 4 := by rw [Real.norm_eq_abs, abs_of_nonneg (hHnonneg ω)]
    rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (4 : ℝ))]
    convert hHfourInt using 1
    funext ω
    exact hpoint ω
  have hHmoment : ∫ ω, H ω ^ 4 ∂disorderLaw ≤ D := by
    have h := hCinvN ϑ hϑ i hi (by omega)
    simpa [H, Z, β, t] using h.trans hCinle
  have hHmomentReal : ∫ ω, H ω ^ (4 : ℝ) ∂disorderLaw ≤ D := by
    have heq (ω : Disorder) : H ω ^ (4 : ℝ) = H ω ^ 4 := Real.rpow_natCast _ _
    calc
      ∫ ω, H ω ^ (4 : ℝ) ∂disorderLaw = ∫ ω, H ω ^ 4 ∂disorderLaw :=
        integral_congr_ae (Eventually.of_forall heq)
      _ ≤ D := hHmoment
  have hpq : ((4 : ℝ) / 3).HolderConjugate 4 := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hGnonneg) (Filter.Eventually.of_forall hHnonneg)
    hGmem hHmem
  have hHolder' :
      ∫ ω, G ω * H ω ∂disorderLaw ≤
        (∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw) ^ ((3 : ℝ) / 4) *
          (∫ ω, H ω ^ (4 : ℝ) ∂disorderLaw) ^ ((1 : ℝ) / 4) := by
    have hq : (1 : ℝ) / ((4 : ℝ) / 3) = (3 : ℝ) / 4 := by norm_num
    simpa only [hq] using hHolder
  have hGpow (ω : Disorder) : G ω ^ ((4 : ℝ) / 3) = G ω := by
    by_cases hω : ω ∈ bad <;> simp [G, hω]
  have hGmoment :
      ∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw = (disorderLaw bad).toReal := by
    calc
      ∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw = ∫ ω, G ω ∂disorderLaw :=
        integral_congr_ae (Eventually.of_forall hGpow)
      _ = (disorderLaw bad).toReal := by
        change ∫ ω, bad.indicator (fun _ : Disorder => (1 : ℝ)) ω ∂disorderLaw = _
        simpa [Measure.real] using integral_indicator_const (1 : ℝ) hbadMeas
  have hGmomentNonneg : 0 ≤ ∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw := by
    rw [hGmoment]
    positivity
  have hGroot :
      (∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw) ^ ((3 : ℝ) / 4) ≤
        (16 * D / d ^ 2) ^ ((3 : ℝ) / 4) := by
    rw [hGmoment]
    exact Real.rpow_le_rpow
      (ENNReal.toReal_nonneg : 0 ≤ (disorderLaw bad).toReal) hbad (by norm_num)
  have hHmomentNonneg : 0 ≤ ∫ ω, H ω ^ 4 ∂disorderLaw := by
    apply integral_nonneg
    intro ω
    positivity
  have hHmomentRealNonneg : 0 ≤ ∫ ω, H ω ^ (4 : ℝ) ∂disorderLaw := by
    apply integral_nonneg
    intro ω
    exact Real.rpow_nonneg (hHnonneg ω) _
  have hHroot :
      (∫ ω, H ω ^ (4 : ℝ) ∂disorderLaw) ^ ((1 : ℝ) / 4) ≤ D ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow hHmomentRealNonneg hHmomentReal (by norm_num)
  have hden : 1 ≤ ∫ ω, H ω ∂disorderLaw := by
    simpa [H, Z, β, t] using one_le_integral_inv_blockMass β t i
  have hnumEq :
      ∫ ω in bad, H ω ∂disorderLaw = ∫ ω, G ω * H ω ∂disorderLaw := by
    rw [← integral_indicator hbadMeas]
    apply integral_congr_ae
    filter_upwards [] with ω
    by_cases hω : ω ∈ bad <;> simp [G, hω]
  have hnumNonneg : 0 ≤ ∫ ω in bad, H ω ∂disorderLaw := by
    rw [hnumEq]
    apply integral_nonneg
    intro ω
    exact mul_nonneg (hGnonneg ω) (hHnonneg ω)
  have hscale : (16 * D / d ^ 2) ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 4) =
      C / d ^ ((3 : ℝ) / 2) := by
    have hdpow : (d ^ 2) ^ ((3 : ℝ) / 4) = d ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_natCast d 2, ← Real.rpow_mul hdpos.le]
      norm_num
    rw [Real.div_rpow (by positivity) (sq_nonneg d), hdpow]
    dsimp [C]
    ring
  have hnumBound :
      (∫ ω in bad, H ω ∂disorderLaw) ≤ C / d ^ ((3 : ℝ) / 2) := by
    calc
      ∫ ω in bad, H ω ∂disorderLaw = ∫ ω, G ω * H ω ∂disorderLaw := hnumEq
      _ ≤ (∫ ω, G ω ^ ((4 : ℝ) / 3) ∂disorderLaw) ^ ((3 : ℝ) / 4) *
          (∫ ω, H ω ^ (4 : ℝ) ∂disorderLaw) ^ ((1 : ℝ) / 4) := hHolder'
      _ ≤ (16 * D / d ^ 2) ^ ((3 : ℝ) / 4) * D ^ ((1 : ℝ) / 4) :=
        mul_le_mul hGroot hHroot (by positivity) (by positivity)
      _ = C / d ^ ((3 : ℝ) / 2) := hscale
  have hboundNonneg : 0 ≤ C / d ^ ((3 : ℝ) / 2) := by
    dsimp [C]
    positivity
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).2
  exact le_trans hnumBound (by nlinarith [hden, hboundNonneg])

end Critical2DKPZ.OnePoint

end
