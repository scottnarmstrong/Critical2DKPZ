/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Replica
public import Critical2DKPZ.Polymer.Moments

/-! # Independent linear-time window variables for the quasi-critical CLT

The walk runs freely before the left endpoint. Only the disorder in the
specified window is included, as in CCR25 equations ZAB and Xi.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- Average over the free entrance walk before introducing the window disorder. -/
def freeEntranceWindowMass (β : ℝ) (a b : ℕ) (w : Site) (ω : Disorder) : ℝ :=
  ∑ s : Fin a → Fin 4, (4 : ℝ)⁻¹ ^ a *
    pointToPlane β a (b - a) (walkPosition w s a) ω

/-- A finite spatially averaged centered window variable. The coefficient c
will be sqrt(l)/N, and the entrance weights are the actual cell averages. -/
def latticeWindowFluctuation (β c : ℝ) (a b : ℕ) (S : Finset Site)
    (ν : Site → ℝ) (ω : Disorder) : ℝ :=
  c * ∑ w ∈ S, ν w * (freeEntranceWindowMass β a b w ω - 1)

/-- Window variables are measurable in precisely the window disorder. -/
theorem measurable_freeEntranceWindowMass_block (β : ℝ) {a b : ℕ}
    (hab : a ≤ b) (w : Site) :
    Measurable[Gaussian.disorderBlock a b] (freeEntranceWindowMass β a b w) := by
  unfold freeEntranceWindowMass
  apply Finset.measurable_sum
  intro s _
  have hm := Polymer.measurable_pointToPlane_block β a (b - a) (walkPosition w s a)
  rw [Nat.add_sub_of_le hab] at hm
  exact measurable_const.mul hm

theorem memLp_freeEntranceWindowMass (β : ℝ) (a b : ℕ) (w : Site)
    (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp (freeEntranceWindowMass β a b w) p disorderLaw := by
  unfold freeEntranceWindowMass
  exact memLp_finsetSum _ fun s _ =>
    (Polymer.memLp_pointToPlane β a (b - a) (walkPosition w s a) p hp).const_mul _

/-- The free entrance and the normalized disorder each preserve mean one. -/
theorem integral_freeEntranceWindowMass (β : ℝ) (a b : ℕ) (w : Site) :
    (∫ ω, freeEntranceWindowMass β a b w ω ∂disorderLaw) = 1 := by
  unfold freeEntranceWindowMass
  rw [integral_finsetSum _ fun s _ =>
    (Polymer.integrable_pointToPlane β a (b - a) (walkPosition w s a)).const_mul _]
  simp only [integral_const_mul, Polymer.integral_pointToPlane, mul_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_pow]

theorem measurable_latticeWindowFluctuation_block (β c : ℝ) {a b : ℕ}
    (hab : a ≤ b) (S : Finset Site) (ν : Site → ℝ) :
    Measurable[Gaussian.disorderBlock a b] (latticeWindowFluctuation β c a b S ν) := by
  unfold latticeWindowFluctuation
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun w _ => measurable_const.mul
    ((measurable_freeEntranceWindowMass_block β hab w).sub measurable_const)

theorem memLp_latticeWindowFluctuation (β c : ℝ) (a b : ℕ)
    (S : Finset Site) (ν : Site → ℝ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (latticeWindowFluctuation β c a b S ν) p disorderLaw := by
  unfold latticeWindowFluctuation
  apply MemLp.const_mul
  exact memLp_finsetSum _ fun w _ =>
    ((memLp_freeEntranceWindowMass β a b w p hp).sub (memLp_const 1)).const_mul _

/-- Every window fluctuation is centered, including empty windows. -/
theorem integral_latticeWindowFluctuation (β c : ℝ) (a b : ℕ)
    (S : Finset Site) (ν : Site → ℝ) :
    (∫ ω, latticeWindowFluctuation β c a b S ν ω ∂disorderLaw) = 0 := by
  have hi (w : Site) : Integrable (freeEntranceWindowMass β a b w) disorderLaw :=
    (memLp_freeEntranceWindowMass β a b w 1 (by norm_num)).integrable le_rfl
  have hiw (w : Site) : Integrable (fun ω => ν w * (freeEntranceWindowMass β a b w ω - 1)) disorderLaw := by
    simpa only [Pi.sub_apply] using ((hi w).sub (integrable_const 1)).const_mul (ν w)
  unfold latticeWindowFluctuation
  rw [integral_const_mul, integral_finsetSum _ fun w _ => hiw w]
  simp only [integral_const_mul, integral_sub (hi _) (integrable_const 1),
    integral_freeEntranceWindowMass, integral_const, probReal_univ,
    smul_eq_mul, mul_one, sub_self, mul_zero, Finset.sum_const_zero]

/-- Disjoint linear-time windows give independent centered spatial averages.
The entrance weights can vary from one window to another. -/
theorem iIndepFun_latticeWindowFluctuation {ι : Type*}
    (β c : ℝ) (a b : ι → ℕ) (hab : ∀ i, a i ≤ b i)
    (hdisj : Pairwise fun i j => Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (S : ι → Finset Site) (ν : ι → Site → ℝ) :
    iIndepFun (fun i => latticeWindowFluctuation β c (a i) (b i) (S i) (ν i)) disorderLaw :=
  Polymer.independent_of_blockMeasurable a b hdisj _
    (fun i => measurable_latticeWindowFluctuation_block β c (hab i) (S i) (ν i))

/-- Linear-time block endpoints with integer rounding. -/
def quasiCriticalBlockClock (N M i : ℕ) : ℕ := N * i / M

theorem monotone_quasiCriticalBlockClock (N M : ℕ) : Monotone (quasiCriticalBlockClock N M) := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.mul_le_mul_left N hij)




/-- The free-entrance window is exactly the library's smoothed point-to-plane
mass, including the disorder convention at both time endpoints. -/
theorem freeEntranceWindowMass_eq_smoothedP2Plane (β : ℝ) (a b : ℕ)
    (w : Site) (ω : Disorder) :
    freeEntranceWindowMass β a b w ω = smoothedP2Plane β a b w ω := by
  have hh := Polymer.tsum_pointToPoint_mul 0 0 a w
    (fun z => pointToPlane β a (b - a) z ω) (fun _ => 0)
  simpa only [freeEntranceWindowMass, smoothedP2Plane,
    Polymer.pointToPoint_zero_beta, Polymer.pathWeight_zero_beta, mul_one] using hh.symm

end Critical2DKPZ.Extensions.GffTangent
