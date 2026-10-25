/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonWindowProjection
import Critical2DKPZ.Extensions.ScaleLimit.ArrayMoments
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! # Exact L2 error of the independent window approximation -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- A square-integrable conditional projection has its own second moment as
its cross moment with the original variable. -/
theorem integral_mul_conditional_projection {Ω : Type*} [m₀ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {X Y : Ω → ℝ} (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hYm : AEStronglyMeasurable[m] Y P) (hCE : P[X | m] =ᵐ[P] Y) :
    (∫ ω, X ω * Y ω ∂P) = ∫ ω, Y ω ^ 2 ∂P := by
  have hpull := condExp_mul_of_aestronglyMeasurable_left hYm (hY.integrable_mul hX)
    (hX.integrable (by norm_num))
  have he : (fun ω => Y ω * P[X | m] ω) =ᵐ[P] fun ω => Y ω ^ 2 := by
    filter_upwards [hCE] with ω hω
    rw [hω, pow_two]
  calc
    _ = ∫ ω, Y ω * X ω ∂P := by simp only [mul_comm]
    _ = ∫ ω, P[Y * X | m] ω ∂P := (integral_condExp hm).symm
    _ = _ := integral_congr_ae (hpull.trans he)

/-- Independent centered projections give the exact Pythagorean error identity.
The displayed residual is proved square integrable before its second moment. -/
theorem integral_sq_error_of_independent_projections {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (I : Finset ι) {X : Ω → ℝ} {Y : ι → Ω → ℝ}
    (hX : MemLp X 2 P) (hY : ∀ i, MemLp (Y i) 2 P) (hind : iIndepFun Y P)
    (hmean : ∀ i, (∫ ω, Y i ω ∂P) = 0)
    (hcross : ∀ i, (∫ ω, X ω * Y i ω ∂P) = ∫ ω, Y i ω ^ 2 ∂P) :
    MemLp (fun ω => X ω - ∑ i ∈ I, Y i ω) 2 P ∧
    (∫ ω, (X ω - ∑ i ∈ I, Y i ω) ^ 2 ∂P) =
      (∫ ω, X ω ^ 2 ∂P) - ∑ i ∈ I, ∫ ω, Y i ω ^ 2 ∂P := by
  classical
  let S : Ω → ℝ := fun ω => ∑ i ∈ I, Y i ω
  have hS : MemLp S 2 P := memLp_finsetSum I fun i _ => hY i
  have hXS : Integrable (fun ω => X ω * S ω) P := hX.integrable_mul hS
  have hsqS : (∫ ω, S ω ^ 2 ∂P) = ∑ i ∈ I, ∫ ω, Y i ω ^ 2 ∂P :=
    ScaleLimit.integral_sq_sum_indep_centered P I Y hind (fun i _ => hY i) (fun i _ => hmean i)
  have hXY (i : ι) : Integrable (fun ω => X ω * Y i ω) P := hX.integrable_mul (hY i)
  have hprod : (∫ ω, X ω * S ω ∂P) = ∑ i ∈ I, ∫ ω, Y i ω ^ 2 ∂P := by
    dsimp only [S]
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum I (fun i _ => hXY i)]
    exact Finset.sum_congr rfl fun i _ => hcross i
  refine ⟨hX.sub hS, ?_⟩
  have he (ω : Ω) : (X ω - S ω) ^ 2 = X ω ^ 2 - 2 * (X ω * S ω) + S ω ^ 2 := by ring
  simp_rw [show (fun ω => (X ω - ∑ i ∈ I, Y i ω) ^ 2) =
    (fun ω => X ω ^ 2 - 2 * (X ω * S ω) + S ω ^ 2) by funext ω; exact he ω]
  have hXsq : Integrable (fun ω => X ω ^ 2) P := hX.integrable_sq
  have hSsq : Integrable (fun ω => S ω ^ 2) P := hS.integrable_sq
  have h2XS : Integrable (fun ω => 2 * (X ω * S ω)) P := hXS.const_mul 2
  have hsub : Integrable (fun ω => X ω ^ 2 - 2 * (X ω * S ω)) P := by
    apply (hXsq.sub h2XS).congr
    filter_upwards [] with ω
    exact Pi.sub_apply _ _ ω
  rw [integral_add hsub hSsq, integral_sub hXsq h2XS, integral_const_mul, hprod, hsqS]
  ring

/-- CCR25's finite-scale orthogonality identity for the actual window variables.
No limiting variance assertion is used in this algebraic step. -/
theorem integral_sq_lattice_window_error {ι : Type*} (β c : ℝ) (N : ℕ)
    (I : Finset ι) (a b : ι → ℕ) (hab : ∀ i, a i ≤ b i) (hbN : ∀ i, b i ≤ N)
    (hdisj : Pairwise fun i j => Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j)))
    (S : Finset Site) (ν : Site → ℝ) :
    MemLp (fun ω => finiteEntranceFluctuation β c 0 N S ν ω -
      ∑ i ∈ I, latticeWindowFluctuation β c (a i) (b i) S ν ω) 2 disorderLaw ∧
    (∫ ω, (finiteEntranceFluctuation β c 0 N S ν ω -
      ∑ i ∈ I, latticeWindowFluctuation β c (a i) (b i) S ν ω) ^ 2 ∂disorderLaw) =
      (∫ ω, finiteEntranceFluctuation β c 0 N S ν ω ^ 2 ∂disorderLaw) -
        ∑ i ∈ I, ∫ ω, latticeWindowFluctuation β c (a i) (b i) S ν ω ^ 2 ∂disorderLaw := by
  have hX : MemLp (finiteEntranceFluctuation β c 0 N S ν) 2 disorderLaw := by
    unfold finiteEntranceFluctuation
    apply MemLp.const_mul
    exact memLp_finsetSum S fun w _ =>
      ((Polymer.memLp_pointToPlane β 0 N w 2 (by norm_num)).sub (memLp_const 1)).const_mul _
  have hY (i : ι) : MemLp (latticeWindowFluctuation β c (a i) (b i) S ν) 2 disorderLaw :=
    memLp_latticeWindowFluctuation _ _ _ _ _ _ _ (by norm_num)
  exact integral_sq_error_of_independent_projections disorderLaw I hX hY
    (iIndepFun_latticeWindowFluctuation β c a b hab hdisj (fun _ => S) (fun _ => ν))
    (fun i => integral_latticeWindowFluctuation _ _ _ _ _ _)
    (fun i => integral_mul_conditional_projection disorderLaw (Gaussian.disorderBlock_le _ _) hX (hY i)
      (measurable_latticeWindowFluctuation_block β c (hab i) S ν).aestronglyMeasurable
      (condExp_finiteEntranceFluctuation_window β c (hab i) (hbN i) S ν))

end Critical2DKPZ.Extensions.GffTangent
