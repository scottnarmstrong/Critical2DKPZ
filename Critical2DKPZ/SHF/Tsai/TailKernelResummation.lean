/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadTail
public import Critical2DKPZ.SHF.Tsai.WeightedFormBound
public import Critical2DKPZ.SHF.Tsai.WordFactorization
public import Critical2DKPZ.SHF.DeltaBose.ChainSummability
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Resumming the four-particle tail word bounds -/

@[expose] public section

open MeasureTheory Set Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A uniform four-particle tail-word bound with a logarithmic gain for each continuation gives a finite form bound for the full tail kernel. -/
theorem weightedFormBound_tailKernel_of_tailWord_bound (θ T : ℝ) {p a : ℝ}
    (β : CollisionPair 4)
    {c : ℝ} (hc : 1 ≤ c)
    (hword : ∀ rate : ℝ, c + 3 ≤ rate →
      ∀ (m : ℕ) (w : CollisionWord 4 m),
        (∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β) →
        ∀ t : ℝ, 0 < t → t ≤ T →
          WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
            (fun y : Configuration 4 => a * configurationOneNorm y) p 2
            (fun (z : FusedConfiguration β) (y : Configuration 4) =>
              ∫⁻ u in Ioo 0 t, ∫⁻ z' : FusedConfiguration β,
                ENNReal.ofReal (collisionKernel β θ u z z') *
                  diagramKernel θ (List.ofFn w.1) (t - u) (collisionEmbedding β z') y)
            (ENNReal.ofReal (c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 *
              (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) * t ^ (-1 / p)))) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ T →
      WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
        (fun y : Configuration 4 => a * configurationOneNorm y) p 2
        (tailKernel θ β t)
        (ENNReal.ofReal (C * t ^ (-1 / p))) := by
  classical
  let N : ℝ := (Fintype.card (CollisionPair 4) : ℝ)
  have hN : 0 < N := by
    have hcard : 0 < Fintype.card (CollisionPair 4) := Fintype.card_pos_iff.mpr (by
      let i : Fin 4 := ⟨0, by omega⟩
      let j : Fin 4 := ⟨1, by omega⟩
      exact ⟨⟨(i, j), Fin.mk_lt_mk.mpr (by omega)⟩⟩)
    dsimp [N]
    exact_mod_cast hcard
  have hcpos : 0 < c := by linarith
  let rate : ℝ := Real.exp (2 * N * c ^ 2) + c + 3
  have hrate : c + 3 ≤ rate := by
    dsimp [rate]
    have hx : 0 < 2 * N * c ^ 2 := by positivity
    have hexp : 0 < Real.exp (2 * N * c ^ 2) := Real.exp_pos _
    linarith
  have hloglower : 2 * N * c ^ 2 ≤ Real.log (rate - c - 1) := by
    have hratearg : rate - c - 1 = Real.exp (2 * N * c ^ 2) + 2 := by
      dsimp [rate]
      ring
    have harg : Real.exp (2 * N * c ^ 2) ≤ Real.exp (2 * N * c ^ 2) + 2 := by linarith
    calc
      2 * N * c ^ 2 = Real.log (Real.exp (2 * N * c ^ 2)) := (Real.log_exp _).symm
      _ ≤ Real.log (rate - c - 1) := by
        rw [hratearg]
        exact Real.log_le_log (Real.exp_pos _) harg
  have hlogpos : 0 < Real.log (rate - c - 1) := by
    have hx : 0 < 2 * N * c ^ 2 := by positivity
    linarith
  have hratio : N * c ^ 2 / Real.log (rate - c - 1) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hlogpos]
    nlinarith [hloglower]
  have hseries : Summable (fun m : ℕ => ((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m) :=
    summable_natSucc_cube_mul_pow (by norm_num) (by norm_num)
  let S : ℝ := ∑' m : ℕ, ((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact tsum_nonneg fun m => mul_nonneg (by positivity) (by positivity)
  refine ⟨c * Real.exp (rate * T) * (S + 1), ?_, ?_⟩
  · positivity
  · intro t ht htT
    let B : ℕ → ℝ := fun m => c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 *
      (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) * t ^ (-1 / p)
    let K : ∀ m : ℕ, CollisionWord 4 m → FusedConfiguration β → Configuration 4 → ℝ≥0∞ :=
      fun m w z y => if hvalid : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
        ∫⁻ u in Ioo 0 t, ∫⁻ z' : FusedConfiguration β,
          ENNReal.ofReal (collisionKernel β θ u z z') *
            diagramKernel θ (List.ofFn w.1) (t - u) (collisionEmbedding β z') y
        else 0
    let D : ∀ m : ℕ, CollisionWord 4 m → ℝ≥0∞ := fun m w =>
      if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then ENNReal.ofReal (B m) else 0
    have hmeas (m : ℕ) (w : CollisionWord 4 m) :
        Measurable (Function.uncurry (K m w)) := by
      by_cases hw : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
      · have hJ : Measurable (collisionTimeKernel β θ) := measurable_collisionTimeKernel β θ
        have hPath : Measurable (pathTimeKernel θ (List.ofFn w.1)
            (collisionEmbedding β) id) :=
          measurable_pathTimeKernel θ (List.ofFn w.1) (measurable_collisionEmbedding β) measurable_id
        have hTail : Measurable (tailWordTimeKernel θ β (List.ofFn w.1)) :=
          measurable_timeKernelComp volume (measurable_causalKernel hJ)
            (measurable_causalKernel hPath)
        have hmap : Measurable (fun q : FusedConfiguration β × Configuration 4 =>
            (t, q.1, q.2)) := by fun_prop
        have hcomp := hTail.comp hmap
        have heq : Function.uncurry (K m w) =
            fun q => tailWordTimeKernel θ β (List.ofFn w.1) (t, q.1, q.2) := by
          funext q
          change (if hw' : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then _ else 0) = _
          rw [dite_eq_left hw]
          change tailWordKernel θ β (List.ofFn w.1) t q.1 q.2 = _
          exact tailWordKernel_eq_tailWordTimeKernel θ β (List.ofFn w.1) t q.1 q.2
        rw [heq]
        exact hcomp
      · have heq : (Function.uncurry (K m w) :
          FusedConfiguration β × Configuration 4 → ℝ≥0∞) = fun _ => 0 := by
          funext q
          simp [Function.uncurry, K, hw]
        rw [heq]
        exact measurable_const
    have hbound (m : ℕ) (w : CollisionWord 4 m) :
        WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
          (fun y : Configuration 4 => a * configurationOneNorm y) p 2
          (K m w) (D m w) := by
      by_cases hw : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
      · have hk : K m w = fun z y =>
            ∫⁻ u in Ioo 0 t, ∫⁻ z' : FusedConfiguration β,
              ENNReal.ofReal (collisionKernel β θ u z z') *
                diagramKernel θ (List.ofFn w.1) (t - u) (collisionEmbedding β z') y := by
          funext z y
          simp [K, hw]
        have hD : D m w = ENNReal.ofReal (B m) := by simp [D, hw, B]
        rw [hk, hD]
        exact hword rate hrate m w hw t ht htT
      · have hk : K m w = 0 := by
          funext z y
          simp [K, hw]
        have hD : D m w = 0 := by simp [D, hw]
        rw [hk, hD]
        intro f g hf hg
        simp
    have hsumWord (m : ℕ) :
        WeightedFormBound volume volume (fun _ : FusedConfiguration β => 0)
          (fun y : Configuration 4 => a * configurationOneNorm y) p 2
          (fun z y => ∑' w : CollisionWord 4 m, K m w z y)
          (∑' w : CollisionWord 4 m, D m w) :=
      WeightedFormBound.tsum (fun w => hmeas m w) (fun w => hbound m w)
    have hsumWordMeas (m : ℕ) : Measurable (Function.uncurry
        (fun z y => ∑' w : CollisionWord 4 m, K m w z y)) := by
      apply Measurable.tsum
      intro w
      exact hmeas m w
    have hsumAll := WeightedFormBound.tsum
      (fun m => hsumWordMeas m) (fun m => hsumWord m)
    have hkernel : (fun z y => ∑' m : ℕ, ∑' w : CollisionWord 4 m, K m w z y) =
        tailKernel θ β t := by
      funext z y
      simp only [tailKernel]
      apply tsum_congr
      intro m
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hw : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
      · simp [K, hw]
      · simp [K, hw]
    rw [hkernel] at hsumAll
    have hcoefWord (m : ℕ) :
        (∑' w : CollisionWord 4 m, D m w) ≤
          ENNReal.ofReal ((Fintype.card (CollisionWord 4 m) : ℝ) * B m) := by
      rw [tsum_fintype]
      calc
        ∑ w : CollisionWord 4 m, D m w ≤
            ∑ _w : CollisionWord 4 m, ENNReal.ofReal (B m) :=
          Finset.sum_le_sum fun w _ => by
            by_cases hw : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
            · simp [D, hw]
            · simp [D, hw]
        _ = ENNReal.ofReal ((Fintype.card (CollisionWord 4 m) : ℝ) * B m) := by
          calc
            _ = (Fintype.card (CollisionWord 4 m) : ℝ≥0∞) * ENNReal.ofReal (B m) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              simp
            _ = _ := by
              rw [show (Fintype.card (CollisionWord 4 m) : ℝ≥0∞) =
                ENNReal.ofReal (Fintype.card (CollisionWord 4 m) : ℝ) by norm_num]
              exact (ENNReal.ofReal_mul (by positivity)).symm
    have hcard (m : ℕ) : (Fintype.card (CollisionWord 4 m) : ℝ) ≤ N ^ m := by
      have h := collisionWord_card_le_pow 4 m
      change (Fintype.card (CollisionWord 4 m) : ℝ) ≤
        ((Fintype.card (CollisionPair 4) : ℕ) : ℝ) ^ m
      exact_mod_cast h
    have hBnonneg (m : ℕ) : 0 ≤ B m := by positivity
    have hcoeff (m : ℕ) :
        (Fintype.card (CollisionWord 4 m) : ℝ) * B m ≤
          (c * Real.exp (rate * T) * t ^ (-1 / p)) *
            (((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m) := by
      have hpowId : c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m =
          c * (c ^ 2 / Real.log (rate - c - 1)) ^ m := by
        calc
          c ^ (m + 1) * (c / Real.log (rate - c - 1)) ^ m =
              c * (c ^ m * (c / Real.log (rate - c - 1)) ^ m) := by
                rw [pow_succ]
                ring
          _ = c * (c * (c / Real.log (rate - c - 1))) ^ m := by
                rw [← mul_pow]
          _ = c * (c ^ 2 / Real.log (rate - c - 1)) ^ m := by
                congr 2
                field_simp [ne_of_gt hlogpos]
      have hratioPow : (N * (c ^ 2 / Real.log (rate - c - 1))) ^ m ≤ (1 / 2 : ℝ) ^ m :=
        pow_le_pow_left₀ (by positivity) (by
          calc
            N * (c ^ 2 / Real.log (rate - c - 1)) = N * c ^ 2 / Real.log (rate - c - 1) := by ring
            _ ≤ 1 / 2 := hratio) _
      have htime : Real.exp (rate * t) ≤ Real.exp (rate * T) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left htT (by positivity)
      dsimp [B]
      calc
        (Fintype.card (CollisionWord 4 m) : ℝ) *
            (c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 *
              (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) * t ^ (-1 / p))
            ≤ N ^ m * (c ^ (m + 1) * ((m : ℝ) + 1) ^ 3 *
              (c / Real.log (rate - c - 1)) ^ m * Real.exp (rate * t) * t ^ (-1 / p)) := by
                exact mul_le_mul_of_nonneg_right (hcard m) (by positivity)
        _ = (c * ((m + 1 : ℝ) ^ 3) *
              (N * (c ^ 2 / Real.log (rate - c - 1))) ^ m) *
              (Real.exp (rate * t) * t ^ (-1 / p)) := by
                calc
                  _ = (N ^ m * (c ^ (m + 1) *
                        (c / Real.log (rate - c - 1)) ^ m)) *
                        ((m + 1 : ℝ) ^ 3) *
                        (Real.exp (rate * t) * t ^ (-1 / p)) := by ring
                  _ = (N ^ m * (c *
                        (c ^ 2 / Real.log (rate - c - 1)) ^ m)) *
                        ((m + 1 : ℝ) ^ 3) *
                        (Real.exp (rate * t) * t ^ (-1 / p)) := by rw [hpowId]
                  _ = c * ((m + 1 : ℝ) ^ 3) *
                        (N ^ m * (c ^ 2 / Real.log (rate - c - 1)) ^ m) *
                        (Real.exp (rate * t) * t ^ (-1 / p)) := by ring
                  _ = _ := by rw [← mul_pow]
        _ ≤ (c * ((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m) *
              (Real.exp (rate * T) * t ^ (-1 / p)) := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left hratioPow (by positivity)
                · exact mul_le_mul_of_nonneg_right htime (by positivity)
                · positivity
                · positivity
        _ = _ := by ring
    have hcoefENN (m : ℕ) :
        ENNReal.ofReal ((Fintype.card (CollisionWord 4 m) : ℝ) * B m) ≤
          ENNReal.ofReal ((c * Real.exp (rate * T) * t ^ (-1 / p)) *
            (((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m)) :=
      ENNReal.ofReal_le_ofReal (hcoeff m)
    have hsumBound :
        (∑' m : ℕ, ∑' w : CollisionWord 4 m, D m w) ≤
          ∑' m : ℕ, ENNReal.ofReal ((c * Real.exp (rate * T) * t ^ (-1 / p)) *
            (((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m)) := by
      exact ENNReal.tsum_le_tsum fun m => (hcoefWord m).trans (hcoefENN m)
    have hg (m : ℕ) : 0 ≤
        (c * Real.exp (rate * T) * t ^ (-1 / p)) *
          (((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m) := by positivity
    have hgsum : Summable (fun m : ℕ =>
        (c * Real.exp (rate * T) * t ^ (-1 / p)) *
          (((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m)) := by
      exact hseries.mul_left _
    have hsumEq : (∑' m : ℕ,
        (c * Real.exp (rate * T) * t ^ (-1 / p)) *
          (((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m)) =
        (c * Real.exp (rate * T) * t ^ (-1 / p)) * S := by
      simp [S, tsum_mul_left]
    have hENNsum := ENNReal.ofReal_tsum_of_nonneg hg hgsum
    have hsumFinal :
        (∑' m : ℕ, ENNReal.ofReal ((c * Real.exp (rate * T) * t ^ (-1 / p)) *
          (((m + 1 : ℝ) ^ 3) * (1 / 2 : ℝ) ^ m))) =
          ENNReal.ofReal ((c * Real.exp (rate * T) * S) * t ^ (-1 / p)) := by
      rw [← hENNsum, hsumEq]
      congr 1
      ring
    have hSle : S ≤ S + 1 := by linarith
    have hfinalCoeff : ENNReal.ofReal ((c * Real.exp (rate * T) * S) * t ^ (-1 / p)) ≤
        ENNReal.ofReal ((c * Real.exp (rate * T) * (S + 1)) * t ^ (-1 / p)) := by
      apply ENNReal.ofReal_le_ofReal
      have hfactor : 0 ≤ c * Real.exp (rate * T) * t ^ (-1 / p) := by positivity
      nlinarith
    have hcoefle :
        (∑' m : ℕ, ∑' w : CollisionWord 4 m, D m w) ≤
          ENNReal.ofReal ((c * Real.exp (rate * T) * (S + 1)) * t ^ (-1 / p)) :=
      (hsumBound.trans_eq hsumFinal).trans hfinalCoeff
    exact WeightedFormBound.mono hsumAll (fun _ _ => le_rfl) hcoefle

end Critical2DKPZ.SHF.Tsai

end
