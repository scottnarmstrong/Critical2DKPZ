/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Gaussian.TimeBlocks
public import Critical2DKPZ.Polymer.Gaussian
public import Critical2DKPZ.Polymer.Locality
public import Critical2DKPZ.SHF.Flow.TerminalProfileAnnealing
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Tactic
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic

/-! # Annealing random weights at a terminal Gaussian layer -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Flow

/-- A terminal Gaussian exponential factors from any integrable observable
measurable with respect to the preceding disorder block. -/
theorem integral_terminalGaussian_mul_blockMeasurable
    (β : ℝ) (n : ℕ) (z : Site) (P : Disorder → ℝ)
    (hP : Measurable[Gaussian.disorderBlock 0 n] P)
    (hPint : Integrable P disorderLaw) :
    Integrable (fun ω => Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) * P ω)
        disorderLaw ∧
    ∫ ω, Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) * P ω ∂disorderLaw =
      Real.exp (15 * β ^ 2) * ∫ ω, P ω ∂disorderLaw := by
  let H : Disorder → ℝ := fun ω => Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2)
  have hHblock : Measurable[Gaussian.disorderBlock n (n + 1)] H := by
    have hcoord := Polymer.measurable_block_coordinate n (n + 1) (n + 1, z)
      (by constructor <;> dsimp <;> omega)
    change Measurable[Gaussian.disorderBlock n (n + 1)]
      (fun ω => Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2))
    exact ((measurable_const.mul hcoord).sub measurable_const).exp
  have hH : Measurable H :=
    hHblock.mono (Gaussian.disorderBlock_le n (n + 1)) le_rfl
  have hPglobal : Measurable P :=
    hP.mono (Gaussian.disorderBlock_le 0 n) le_rfl
  have hHint : Integrable H disorderLaw := by
    let e : Unit → ℕ × Site := fun _ => (n + 1, z)
    have he : Function.Injective e := by
      intro a b _
      exact Subsingleton.elim _ _
    have hfinite := Polymer.integrable_finiteExp e he
      (fun _ => 6 * β) (-3 * β ^ 2)
    have heq : H = Polymer.finiteExp e (fun _ => 6 * β) (-3 * β ^ 2) := by
      funext ω
      simp [H, Polymer.finiteExp]
      ring
    rw [heq]
    exact hfinite
  have hind : IndepFun P H disorderLaw := by
    rw [IndepFun_iff]
    intro s t hs ht
    exact (Indep_iff _ _ _).1
      (Gaussian.indep_disorderBlock_of_le (m := 0) (n := n)
        (a := n) (b := n + 1) le_rfl) s t
      (hP.comap_le s hs) (hHblock.comap_le t ht)
  have hfactor := hind.integral_fun_mul_eq_mul_integral
    hPglobal.aestronglyMeasurable hH.aestronglyMeasurable
  have hHmean : ∫ ω, H ω ∂disorderLaw = Real.exp (15 * β ^ 2) := by
    have heq : H = fun ω => Real.exp (-3 * β ^ 2) *
        Real.exp ((6 * β) * ω (n + 1, z)) := by
      funext ω
      dsimp [H]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, integral_const_mul, Polymer.integral_exp_coordinate]
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · have hmul := hind.integrable_mul hPint hHint
    convert hmul using 1
    funext ω
    change H ω * P ω = P ω * H ω
    ring
  calc
    _ = ∫ ω, P ω * H ω ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by ring
    _ = (∫ ω, P ω ∂disorderLaw) * ∫ ω, H ω ∂disorderLaw := hfactor
    _ = _ := by rw [hHmean]; ring

/-- Sixth moments of terminally weighted random profiles are bounded by the
sixth moment of their total preterminal mass. The coefficients may themselves
be random, provided they are measurable before the independent Gaussian layer. -/
theorem integral_sixth_randomWeightedBoundaryProfile_le (β : ℝ) (n : ℕ)
    (S : Finset Site) (a : Site → ℝ) (P : Site → Disorder → ℝ)
    (ha : ∀ z ∈ S, 0 ≤ a z)
    (hPblock : ∀ z ∈ S, Measurable[Gaussian.disorderBlock 0 n] (P z))
    (hPnonneg : ∀ z ∈ S, ∀ ω, 0 ≤ P z ω)
    (hQ6 : Integrable (fun ω => (∑ z ∈ S, a z * P z ω) ^ 6) disorderLaw) :
    Integrable (fun ω =>
      (∑ z ∈ S, a z * Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) * P z ω) ^ 6)
        disorderLaw ∧
    ∫ ω,
      (∑ z ∈ S, a z * Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) * P z ω) ^ 6
      ∂disorderLaw ≤
      Real.exp (15 * β ^ 2) * ∫ ω, (∑ z ∈ S, a z * P z ω) ^ 6 ∂disorderLaw := by
  classical
  let Q : Disorder → ℝ := fun ω => ∑ z ∈ S, a z * P z ω
  let W : Disorder → ℝ := fun ω =>
    ∑ z ∈ S, a z * Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) * P z ω
  have hQblock : Measurable[Gaussian.disorderBlock 0 n] Q := by
    dsimp [Q]
    exact Finset.measurable_sum _ fun z hz =>
      measurable_const.mul (hPblock z hz)
  have hQglobal : Measurable Q :=
    hQblock.mono (Gaussian.disorderBlock_le 0 n) le_rfl
  have hQnonneg (ω : Disorder) : 0 ≤ Q ω := by
    dsimp [Q]
    exact Finset.sum_nonneg fun z hz => mul_nonneg (ha z hz) (hPnonneg z hz ω)
  have hQsix : Integrable (fun ω => Q ω ^ 6) disorderLaw := by
    simpa only [Q] using hQ6
  have hweight (z : Site) (hz : z ∈ S) (ω : Disorder) :
      0 ≤ a z * P z ω ∧ a z * P z ω ≤ Q ω := by
    constructor
    · exact mul_nonneg (ha z hz) (hPnonneg z hz ω)
    · dsimp [Q]
      exact Finset.single_le_sum (fun y hy => mul_nonneg (ha y hy) (hPnonneg y hy ω)) hz
  have hpoint (ω : Disorder) : W ω ^ 6 ≤
      Q ω ^ 5 * ∑ z ∈ S,
        a z * P z ω * Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) := by
    have hJensen := weighted_nonneg_sum_pow_six_le S
      (fun z => a z * P z ω)
      (fun z => Real.exp (β * ω (n + 1, z) - β ^ 2 / 2))
      (fun z hz => (hweight z hz ω).1)
      (fun z hz => Real.exp_nonneg _)
    have hshape : (∑ z ∈ S,
        a z * Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) * P z ω) =
        ∑ z ∈ S, a z * P z ω *
          Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      ring
    have hpow (z : Site) (ω : Disorder) :
        Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) ^ 6 =
          Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hWshape : W ω =
        ∑ z ∈ S, a z * P z ω * Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) := by
      dsimp [W]
      exact hshape
    calc
      W ω ^ 6 =
          (∑ z ∈ S, a z * P z ω *
            Real.exp (β * ω (n + 1, z) - β ^ 2 / 2)) ^ 6 :=
              congrArg (fun x : ℝ => x ^ 6) hWshape
      _ ≤ _ := by simpa only [hpow] using hJensen
  have hRmeas (z : Site) (hz : z ∈ S) : Measurable (fun ω =>
      Q ω ^ 5 * (a z * P z ω)) := by
    exact (hQglobal.pow_const 5).mul
      (measurable_const.mul ((hPblock z hz).mono
        (Gaussian.disorderBlock_le 0 n) le_rfl))
  have hRbound (z : Site) (hz : z ∈ S) (ω : Disorder) :
      ‖Q ω ^ 5 * (a z * P z ω)‖ ≤ Q ω ^ 6 := by
    have hq := hQnonneg ω
    have hw := hweight z hz ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hq 5) hw.1)]
    nlinarith [mul_le_mul_of_nonneg_left hw.2 (pow_nonneg hq 5)]
  have hRint (z : Site) (hz : z ∈ S) :
      Integrable (fun ω => Q ω ^ 5 * (a z * P z ω)) disorderLaw := by
    apply hQsix.mono' (hRmeas z hz).aestronglyMeasurable
    filter_upwards [] with ω
    exact hRbound z hz ω
  have hterm (z : Site) (hz : z ∈ S) :
      Integrable (fun ω =>
        Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) *
          (Q ω ^ 5 * (a z * P z ω))) disorderLaw ∧
      ∫ ω, Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) *
          (Q ω ^ 5 * (a z * P z ω)) ∂disorderLaw =
        Real.exp (15 * β ^ 2) * ∫ ω, Q ω ^ 5 * (a z * P z ω) ∂disorderLaw := by
    exact integral_terminalGaussian_mul_blockMeasurable β n z
      (fun ω => Q ω ^ 5 * (a z * P z ω)) (hQblock.pow_const 5 |>.mul
        (measurable_const.mul (hPblock z hz))) (hRint z hz)
  have hMajor : Integrable (fun ω => ∑ z ∈ S,
      Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) *
        (Q ω ^ 5 * (a z * P z ω))) disorderLaw := by
    apply integrable_finsetSum
    intro z hz
    exact (hterm z hz).1
  have hMajorEq (ω : Disorder) :
      (∑ z ∈ S, Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) *
          (Q ω ^ 5 * (a z * P z ω))) =
        Q ω ^ 5 * ∑ z ∈ S,
          a z * P z ω * Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hmajorIntegral :
      ∫ ω, Q ω ^ 5 * ∑ z ∈ S,
        a z * P z ω * Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) ∂disorderLaw =
      Real.exp (15 * β ^ 2) * ∫ ω, Q ω ^ 6 ∂disorderLaw := by
    calc
      ∫ ω, Q ω ^ 5 * ∑ z ∈ S,
          a z * P z ω * Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) ∂disorderLaw =
        ∫ ω, ∑ z ∈ S, Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) *
          (Q ω ^ 5 * (a z * P z ω)) ∂disorderLaw := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => (hMajorEq ω).symm
      _ = ∑ z ∈ S,
          ∫ ω, Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) *
            (Q ω ^ 5 * (a z * P z ω)) ∂disorderLaw := by
              exact integral_finsetSum S (fun z hz => (hterm z hz).1)
      _ = ∑ z ∈ S, Real.exp (15 * β ^ 2) *
          ∫ ω, Q ω ^ 5 * (a z * P z ω) ∂disorderLaw := by
          apply Finset.sum_congr rfl
          intro z hz
          exact (hterm z hz).2
      _ = Real.exp (15 * β ^ 2) *
          ∫ ω, ∑ z ∈ S, Q ω ^ 5 * (a z * P z ω) ∂disorderLaw := by
            rw [integral_finsetSum S (fun z hz => hRint z hz)]
            rw [Finset.mul_sum]
      _ = Real.exp (15 * β ^ 2) * ∫ ω, Q ω ^ 6 ∂disorderLaw := by
            congr 1
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun ω => by
              calc
                (∑ z ∈ S, Q ω ^ 5 * (a z * P z ω)) =
                    Q ω ^ 5 * ∑ z ∈ S, a z * P z ω := by
                      symm
                      exact Finset.mul_sum _ _ _
                _ = Q ω ^ 6 := by simp [Q, pow_succ]
  have hWmeas : Measurable W := by
    dsimp [W]
    apply Finset.measurable_sum
    intro z hz
    have hcoord := Polymer.measurable_block_coordinate n (n + 1) (n + 1, z)
      (by constructor <;> dsimp <;> omega)
    have hcoordGlobal : Measurable (fun ω : Disorder => ω (n + 1, z)) :=
      hcoord.mono (Gaussian.disorderBlock_le n (n + 1)) le_rfl
    have hExp : Measurable (fun ω : Disorder =>
        Real.exp (β * ω (n + 1, z) - β ^ 2 / 2)) :=
      ((measurable_const.mul hcoordGlobal).sub measurable_const).exp
    have hPglobal : Measurable (P z) :=
      (hPblock z hz).mono (Gaussian.disorderBlock_le 0 n) le_rfl
    exact (measurable_const.mul hExp).mul hPglobal
  have hWmajor : Integrable (fun ω => Q ω ^ 5 * ∑ z ∈ S,
      a z * P z ω * Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2)) disorderLaw := by
    apply hMajor.congr
    exact Filter.Eventually.of_forall fun ω => hMajorEq ω
  have hWnn (ω : Disorder) : 0 ≤ W ω := by
    dsimp [W]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (mul_nonneg (ha z hz) (Real.exp_nonneg _)) (hPnonneg z hz ω)
  have hMnn (ω : Disorder) : 0 ≤ Q ω ^ 5 *
      ∑ z ∈ S, a z * P z ω * Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2) := by
    apply mul_nonneg (pow_nonneg (hQnonneg ω) 5)
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hweight z hz ω).1 (Real.exp_nonneg _)
  have hW6int : Integrable (fun ω => W ω ^ 6) disorderLaw := by
    apply hWmajor.mono' (hWmeas.pow_const 6).aestronglyMeasurable
    filter_upwards [Filter.Eventually.of_forall hpoint] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hWnn ω) 6),
      abs_of_nonneg (hMnn ω)] using hω
  refine ⟨?_, ?_⟩
  · have hshape : (fun ω =>
        (∑ z ∈ S, a z * Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) * P z ω) ^ 6) =
        fun ω => W ω ^ 6 := by
      funext ω
      rfl
    rw [hshape]
    exact hW6int
  · have hshape : (fun ω =>
        (∑ z ∈ S, a z * Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) * P z ω) ^ 6) =
        fun ω => W ω ^ 6 := by
      funext ω
      rfl
    rw [hshape]
    calc
      ∫ ω, W ω ^ 6 ∂disorderLaw ≤
          ∫ ω, Q ω ^ 5 * ∑ z ∈ S,
            a z * P z ω * Real.exp (6 * β * ω (n + 1, z) - 3 * β ^ 2)
            ∂disorderLaw := integral_mono hW6int hWmajor hpoint
      _ = Real.exp (15 * β ^ 2) * ∫ ω, Q ω ^ 6 ∂disorderLaw := hmajorIntegral
      _ = _ := by simp [Q]

end Critical2DKPZ.SHF.Flow

end
