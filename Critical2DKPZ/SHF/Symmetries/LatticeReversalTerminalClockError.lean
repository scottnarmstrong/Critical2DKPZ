/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.LatticeReversalPairingEstimates
import Mathlib.Tactic

/-! # Terminal two-step clock errors for lattice reversal -/

@[expose] public section

noncomputable section

open MeasureTheory Filter TopologicalSpace
open Critical2DKPZ.SHF.Moments
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Symmetries

private theorem tsum_terminalPath_split (ϑ : ℝ) {N a n : ℕ}
    (hN : 0 < N) (ha : Even a) (hn : Even (a + n + 2))
    (φ : C_c(Plane × Plane, ℝ)) (s : Fin 2 → Fin 4) (ω : Disorder) :
    (∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
      (pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω *
        Polymer.pathWeight (criticalBeta ϑ N) (a + n) q.2 s ω)) =
      (∑' q : Site × Site, cellTestWeight N φ q.1 q.2 *
        ((Polymer.pathWeight (criticalBeta ϑ N) (a + n) q.2 s ω - 1) *
          pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω)) +
      (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
        (((a + n : ℕ) : ℝ) / N) p ω) := by
  let W : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2 *
    ((Polymer.pathWeight (criticalBeta ϑ N) (a + n) q.2 s ω - 1) *
      pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω)
  let G : Site × Site → ℝ := fun q => cellTestWeight N φ q.1 q.2 *
    pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω
  let S := (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N φ).toFinset
  have hW : Summable W := by
    apply summable_of_ne_finset_zero (s := S)
    intro q hq
    simp [W, cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
  have hG : Summable G := by
    apply summable_of_ne_finset_zero (s := S)
    intro q hq
    simp [G, cellTestWeight_eq_zero_of_not_mem N φ q (by simpa [S] using hq)]
  have hbase : (∑' q : Site × Site, G q) =
      ∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
        (((a + n : ℕ) : ℝ) / N) p ω := by
    have hEvenEnd : Even (a + n) := by
      rcases hn with ⟨k, hk⟩
      refine ⟨k - 1, ?_⟩
      omega
    rw [pairing_latticeClock_eq_tsum_pointToPoint ϑ hN ha hEvenEnd φ ω]
    have hduration : a + n - a = n := by omega
    apply tsum_congr
    intro q
    simp only [G, hduration]
  calc
    _ = (∑' q : Site × Site, W q) + ∑' q : Site × Site, G q := by
      rw [← hW.tsum_add hG]
      apply tsum_congr
      intro q
      dsimp [W, G]
      ring
    _ = _ := by rw [hbase]

private theorem integral_compactAbs_pairSecondShiftTest_eq
    (η : Plane) (φ : C_c(Plane × Plane, ℝ)) :
    (∫ p, compactAbs (pairSecondShiftTest η φ) p) =
      ∫ p, compactAbs φ p := by
  have hmp : MeasurePreserving (pairSecondShift η)
      (volume : Measure (Plane × Plane)) volume := by
    rw [Measure.volume_eq_prod Plane Plane]
    exact (MeasurePreserving.id volume).prod (measurePreserving_add_right volume η)
  calc
    (∫ p, compactAbs (pairSecondShiftTest η φ) p) =
        ∫ p, compactAbs φ (pairSecondShift η p) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun p => rfl
    _ = ∫ p, compactAbs φ p := by
      exact hmp.integral_comp' (f := (pairSecondShift η).toMeasurableEquiv)
        (fun p => compactAbs φ p)

private theorem integral_abs_terminalTwoStepPairing_le
    (ϑ ε : ℝ) (hε : 0 < ε) {N a n : ℕ} (hN : 0 < N)
    (ha : Even a) (hn : Even (a + n + 2)) (hgap : ε * N ≤ n)
    (φ : C_c(Plane × Plane, ℝ)) :
    (∫ ω, |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
          (((a + n + 2 : ℕ) : ℝ) / N) p ω) -
        ∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
          (((a + n : ℕ) : ℝ) / N) p ω| ∂disorderLaw) ≤
      ∑ s : Fin 2 → Fin 4, (4 : ℝ)⁻¹ ^ 2 *
        (Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1) *
            (shiftedKernelMassConstant ε hε * ∫ p, compactAbs φ p) +
          shiftedKernelMassConstant ε hε *
            ∫ p, compactAbs
              (pairSecondShiftTest
                ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
                  Critical2DKPZ.siteToPlane (walkPosition 0 s 2)) φ - φ) p) := by
  classical
  let c : ℝ := (4 : ℝ)⁻¹ ^ 2
  let b : ℕ := a + n
  let ψ : (Fin 2 → Fin 4) → C_c(Plane × Plane, ℝ) := fun s =>
    pairSecondShiftTest
      ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
        Critical2DKPZ.siteToPlane (walkPosition 0 s 2)) φ
  let d : (Fin 2 → Fin 4) → Site := fun s => walkPosition 0 s 2
  let E : (Fin 2 → Fin 4) → Disorder → ℝ := fun s ω =>
    ∑' q : Site × Site, cellTestWeight N (ψ s) q.1 q.2 *
      ((Polymer.pathWeight (criticalBeta ϑ N) b q.2 s ω - 1) *
        pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω)
  let Q : (Fin 2 → Fin 4) → Disorder → ℝ := fun s ω =>
    ∫ p, ψ s p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω
  let B : Disorder → ℝ := fun ω =>
    ∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N) ((b : ℝ) / N) p ω
  let D : (Fin 2 → Fin 4) → Disorder → ℝ := fun s ω => Q s ω - B ω
  let f : (Fin 2 → Fin 4) → Disorder → ℝ := fun s ω => c * (E s ω + D s ω)
  have hc : 0 ≤ c := by positivity
  have hcoeff : (∑ _s : Fin 2 → Fin 4, c) = 1 := by
    simp [c, Finset.sum_const, Finset.card_univ]
    norm_num
  have hBsum (ω : Disorder) : (∑ s : Fin 2 → Fin 4, c * B ω) = B ω := by
    calc
      _ = (∑ _s : Fin 2 → Fin 4, c) * B ω := by rw [← Finset.sum_mul]
      _ = B ω := by rw [hcoeff]; ring
  have hpair (ω : Disorder) :
      (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
          (((b + 2 : ℕ) : ℝ) / N) p ω) =
        ∑ s : Fin 2 → Fin 4, c * (E s ω + Q s ω) := by
    rw [show b = a + n by rfl,
      pairing_latticeClock_terminalTwoStep_eq ϑ hN ha hn φ ω]
    apply Finset.sum_congr rfl
    intro s hs
    have hsplit := tsum_terminalPath_split ϑ hN ha hn (ψ s) s ω
    calc
      _ = c * (∑' q : Site × Site, cellTestWeight N (ψ s) q.1 q.2 *
          (pointToPoint (criticalBeta ϑ N) a n q.1 q.2 ω *
            Polymer.pathWeight (criticalBeta ϑ N) b q.2 s ω)) := by
        congr 1
        apply tsum_congr
        intro q
        ring
      _ = c * (E s ω + Q s ω) := by
        rw [hsplit]
  have hdecomp (ω : Disorder) :
      (∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
          (((b + 2 : ℕ) : ℝ) / N) p ω) - B ω =
        ∑ s : Fin 2 → Fin 4, f s ω := by
    rw [hpair ω, ← hBsum ω]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [f, D]
    ring
  have hEvenBase : Even (a + n) := by
    rcases hn with ⟨k, hk⟩
    refine ⟨k - 1, ?_⟩
    omega
  have hEint (s : Fin 2 → Fin 4) : Integrable (E s) disorderLaw := by
    simpa only [E, ψ, d, b] using
      integrable_pathWeightError_tsum ϑ s (fun q => q.2)
        (Or.inr (by simp)) (ψ s)
  have hQint (s : Fin 2 → Fin 4) : Integrable (Q s) disorderLaw :=
    integrable_pairing_latticeClock_of_test ϑ (ψ s)
  have hBint : Integrable B disorderLaw := integrable_pairing_latticeClock_of_test ϑ φ
  have hfint (s : Fin 2 → Fin 4) : Integrable (f s) disorderLaw := by
    have hD : Integrable (D s) disorderLaw := (hQint s).sub hBint
    exact ((hEint s).add hD).const_mul c
  have hsumAbs := integral_abs_finset_sum_le disorderLaw Finset.univ f
    (fun s hs => hfint s)
  have hpath (s : Fin 2 → Fin 4) :
      (∫ ω, |E s ω| ∂disorderLaw) ≤
        Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1) *
          (shiftedKernelMassConstant ε hε * ∫ p, compactAbs (ψ s) p) := by
    simpa only [E, ψ, d, b] using
      integral_abs_pathWeightError_tsum_le ϑ ε hε N b a n hN hgap s
        (fun q => q.2) (Or.inr (by simp [b])) (ψ s)
  have hpathMass (s : Fin 2 → Fin 4) :
      ∫ p, compactAbs (ψ s) p = ∫ p, compactAbs φ p := by
    exact integral_compactAbs_pairSecondShiftTest_eq _ φ
  have htest (s : Fin 2 → Fin 4) :
      (∫ ω, |D s ω| ∂disorderLaw) ≤
        shiftedKernelMassConstant ε hε * ∫ p, compactAbs (ψ s - φ) p := by
    have hgapReal : ε * (N : ℝ) ≤ (b : ℝ) - a := by
      have hnat : a ≤ b := by dsimp [b]; omega
      rw [← Nat.cast_sub hnat]
      rw [show b - a = n by dsimp [b]; omega]
      exact hgap
    simpa only [D, Q, B, b] using
      integral_abs_pairing_latticeClock_sub_test_le ϑ ε hε hN
        ha hEvenBase hgapReal (ψ s) φ
  have hfsumBound :
      (∫ ω, |∑ s : Fin 2 → Fin 4, f s ω| ∂disorderLaw) ≤
        ∑ s : Fin 2 → Fin 4, c *
          ((∫ ω, |E s ω| ∂disorderLaw) + ∫ ω, |D s ω| ∂disorderLaw) := by
    calc
      _ ≤ ∑ s : Fin 2 → Fin 4, ∫ ω, |f s ω| ∂disorderLaw := hsumAbs
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        have hadd := integral_abs_add_le disorderLaw (E s) (D s)
          (hEint s) ((hQint s).sub hBint)
        have hrewrite : (∫ ω, |f s ω| ∂disorderLaw) =
            c * ∫ ω, |E s ω + D s ω| ∂disorderLaw := by
          simp [f, abs_mul, abs_of_nonneg hc, integral_const_mul]
        rw [hrewrite]
        exact mul_le_mul_of_nonneg_left hadd hc
  have hfinalBound :
      (∫ ω, |∑ s : Fin 2 → Fin 4, f s ω| ∂disorderLaw) ≤
        ∑ s : Fin 2 → Fin 4, c *
          (Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1) *
              (shiftedKernelMassConstant ε hε * ∫ p, compactAbs φ p) +
            shiftedKernelMassConstant ε hε *
              ∫ p, compactAbs (ψ s - φ) p) := by
    calc
      _ ≤ ∑ s : Fin 2 → Fin 4, c *
            ((∫ ω, |E s ω| ∂disorderLaw) + ∫ ω, |D s ω| ∂disorderLaw) := hfsumBound
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        have hpath' := hpath s
        rw [hpathMass s] at hpath'
        exact mul_le_mul_of_nonneg_left
          (add_le_add hpath' (htest s)) hc
  have hleftInt : Integrable
      (fun ω => |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
          (((b + 2 : ℕ) : ℝ) / N) p ω) - B ω|) disorderLaw := by
    exact ((integrable_pairing_latticeClock_of_test ϑ φ).sub hBint).norm
  have hrewrite (ω : Disorder) :
      |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
          (((b + 2 : ℕ) : ℝ) / N) p ω) - B ω| =
        |∑ s : Fin 2 → Fin 4, f s ω| := by rw [hdecomp ω]
  have htranslate :
      (∫ ω, |(∫ p, φ p * rescaledP2P ϑ N ((a : ℝ) / N)
          (((b + 2 : ℕ) : ℝ) / N) p ω) - B ω| ∂disorderLaw) =
        ∫ ω, |∑ s : Fin 2 → Fin 4, f s ω| ∂disorderLaw := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hrewrite
  rw [htranslate]
  simpa [b, c, Q, B, ψ] using hfinalBound

/-- For fixed even clock sequences with an eventual macroscopic gap, the terminal two-step pairing error tends to zero in measure; the pairings are integrable by `integrable_pairing_latticeClock_of_test`. -/
theorem tendstoInMeasure_terminalTwoStepPairingError
    (ϑ ε : ℝ) (hε : 0 < ε) (a b : ℕ → ℕ)
    (ha : ∀ N, Even (a N)) (hb : ∀ N, Even (b N))
    (hgap : ∀ᶠ N : ℕ in atTop,
      (2 * ε) * (N : ℝ) + 2 ≤ ((b N - a N : ℕ) : ℝ))
    (φ : C_c(Plane × Plane, ℝ)) :
    TendstoInMeasure disorderLaw
      (fun N ω =>
        (∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N)
          (((b N + 2 : ℕ) : ℝ) / N) p ω) -
          ∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N)
            ((b N : ℝ) / N) p ω)
      atTop (fun _ => 0) := by
  classical
  let shift (N : ℕ) (s : Fin 2 → Fin 4) : ℝ :=
    ∫ p, compactAbs
      (pairSecondShiftTest
        ((Real.sqrt ((N : ℝ) / 2))⁻¹ •
          Critical2DKPZ.siteToPlane (walkPosition 0 s 2)) φ - φ) p
  let root (N : ℕ) : ℝ :=
    Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1)
  let C : ℝ := shiftedKernelMassConstant ε hε
  let mass : ℝ := ∫ p, compactAbs φ p
  let upper (N : ℕ) : ℝ :=
    ∑ s : Fin 2 → Fin 4, (4 : ℝ)⁻¹ ^ 2 *
      (root N * (C * mass) + C * shift N s)
  have hβ := Critical2DKPZ.SHF.Moments.tendsto_criticalBeta_zero ϑ
  have hβsq : Tendsto (fun N : ℕ => (criticalBeta ϑ N) ^ 2) atTop (𝓝 0) := by
    simpa using hβ.pow 2
  have hdouble : Tendsto (fun N : ℕ => 2 * (criticalBeta ϑ N) ^ 2)
      atTop (𝓝 0) := by simpa using hβsq.const_mul 2
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hdouble
  have harg : Tendsto (fun N : ℕ => Real.exp (2 * (criticalBeta ϑ N) ^ 2) - 1)
      atTop (𝓝 0) := by
    have h := hexp.sub_const 1
    convert h using 1 <;> norm_num [Real.exp_zero]
  have hroot : Tendsto root atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp harg
    simpa [root, Function.comp_def] using h
  have hshift (s : Fin 2 → Fin 4) : Tendsto (fun N => shift N s) atTop (𝓝 0) := by
    simpa [shift, compactAbs] using
      tendsto_pairSecondShiftTest_L1 φ (walkPosition 0 s 2)
  have hterm (s : Fin 2 → Fin 4) :
      Tendsto (fun N => (4 : ℝ)⁻¹ ^ 2 *
        (root N * (C * mass) + C * shift N s)) atTop (𝓝 0) := by
    have hfirst : Tendsto (fun N => root N * (C * mass)) atTop (𝓝 0) :=
      by simpa using hroot.mul_const (C * mass)
    have hsecond : Tendsto (fun N => C * shift N s) atTop (𝓝 0) :=
      by simpa using (hshift s).const_mul C
    simpa only [zero_add, mul_zero] using
      (hfirst.add hsecond).const_mul ((4 : ℝ)⁻¹ ^ 2)
  have hupper : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using tendsto_finsetSum Finset.univ (fun s hs => hterm s)
  let err (N : ℕ) (ω : Disorder) : ℝ :=
    (∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N)
      (((b N + 2 : ℕ) : ℝ) / N) p ω) -
      ∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N) ((b N : ℝ) / N) p ω
  have hbound : ∀ᶠ N : ℕ in atTop,
      (∫ ω, |err N ω| ∂disorderLaw) ≤ upper N := by
    filter_upwards [eventually_gt_atTop 0, hgap] with N hN hgapN
    have hba : a N ≤ b N := by
      by_contra h
      have hlt : b N < a N := Nat.lt_of_not_ge h
      have hzero : b N - a N = 0 := Nat.sub_eq_zero_of_le hlt.le
      rw [hzero] at hgapN
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      have hpos : 0 < (2 * ε) * (N : ℝ) + 2 := by
        have hpos' : 0 < (2 * ε) * (N : ℝ) :=
          mul_pos (mul_pos (by norm_num) hε) hNreal
        linarith
      have hgapZero : (2 * ε) * (N : ℝ) + 2 ≤ 0 := by simpa using hgapN
      exact (not_le_of_gt hpos) hgapZero
    have hnat : ε * (N : ℝ) ≤ ((b N - a N : ℕ) : ℝ) := by
      have hgapCast : (2 * ε) * (N : ℝ) + 2 ≤ (b N : ℝ) - a N := by
        rw [Nat.cast_sub hba] at hgapN
        exact hgapN
      rw [Nat.cast_sub hba]
      have hpos : 0 ≤ ε * (N : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg N)
      nlinarith
    have hnEven : Even (a N + (b N - a N) + 2) := by
      have hsum : a N + (b N - a N) = b N := by omega
      rw [hsum]
      exact Even.add (hb N) even_two
    have hboundN := integral_abs_terminalTwoStepPairing_le ϑ ε hε hN (ha N)
      hnEven hnat φ
    have hsum : a N + (b N - a N) = b N := by omega
    have hboundN' : (∫ ω, |err N ω| ∂disorderLaw) ≤ upper N := by
      simpa [err, upper, root, C, mass, shift, hsum] using hboundN
    exact hboundN'
  have habsNonneg (N : ℕ) : 0 ≤ ∫ ω, |err N ω| ∂disorderLaw :=
    integral_nonneg fun ω => abs_nonneg (err N ω)
  have hL1 : Tendsto (fun N => ∫ ω, |err N ω| ∂disorderLaw) atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall habsNonneg) hbound hupper
  have hIntegrable (N : ℕ) : Integrable (fun ω => |err N ω|) disorderLaw := by
    have h1 : Integrable (fun ω =>
        ∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N)
          (((b N + 2 : ℕ) : ℝ) / N) p ω) disorderLaw :=
      integrable_pairing_latticeClock_of_test ϑ φ
    have h2 : Integrable (fun ω =>
        ∫ p, φ p * rescaledP2P ϑ N ((a N : ℝ) / N)
          ((b N : ℝ) / N) p ω) disorderLaw :=
      integrable_pairing_latticeClock_of_test ϑ φ
    simpa [err] using (h1.sub h2).norm
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro δ hδ
  have hmarkov (N : ℕ) : disorderLaw.real {ω | δ ≤ dist (err N ω) 0} ≤
      (∫ ω, |err N ω| ∂disorderLaw) / δ :=
    measureReal_dist_le_integral_abs disorderLaw (err N) (hIntegrable N) hδ
  have hdiv : Tendsto (fun N => (∫ ω, |err N ω| ∂disorderLaw) / δ)
      atTop (𝓝 0) := by simpa using hL1.div_const δ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [zero_div] using hdiv)
    (Filter.Eventually.of_forall fun N => measureReal_nonneg)
    (Filter.Eventually.of_forall hmarkov)

end Critical2DKPZ.SHF.Symmetries

end
