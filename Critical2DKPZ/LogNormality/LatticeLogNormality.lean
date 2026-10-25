/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LogNormality.LatticeInputs
public import Critical2DKPZ.LogNormality.LatticeVariance
public import Critical2DKPZ.OnePoint.BlockRatioComponentSum
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Lattice log-normality from the block decomposition -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators BoundedContinuousFunction

namespace Critical2DKPZ.LogNormality

open Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer
open Critical2DKPZ.FutureProfiles Critical2DKPZ.Gaussian

private theorem variance_finset_of_iIndepFun {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (I : Finset ι) (X : ι → Ω → ℝ)
    (hInd : iIndepFun X μ) (hMem : ∀ i ∈ I, MemLp (X i) 2 μ) :
    Var[fun ω => ∑ i ∈ I, X i ω; μ] = ∑ i ∈ I, Var[X i; μ] := by
  classical
  have hpair : Set.Pairwise (↑I) (fun i j => X i ⟂ᵢ[μ] X j) := by
    intro i hi j hj hij
    exact hInd.indepFun hij
  have hsumfun : (fun ω => ∑ i ∈ I, X i ω) = ∑ i ∈ I, X i := by
    funext ω
    simp
  rw [hsumfun]
  exact IndepFun.variance_sum (s := I) (X := X) hMem hpair

private theorem abs_log_le_log_two_of_abs_sub_one_le {z : ℝ}
    (hz : 0 < z) (hclose : |z - 1| ≤ 1 / 2) : |Real.log z| ≤ Real.log 2 := by
  have hbounds := abs_le.mp hclose
  have hlo : 1 / 2 ≤ z := by linarith only [hbounds.1]
  have hhi : z ≤ 3 / 2 := by linarith only [hbounds.2]
  have hloglo : Real.log (1 / 2) ≤ Real.log z := Real.log_le_log (by norm_num) hlo
  have hloghi : Real.log z ≤ Real.log 2 :=
    (Real.log_le_log_iff (by positivity) (by norm_num)).2 (by linarith only [hhi])
  have hloghalf : Real.log (1 / 2) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  rw [abs_le]
  constructor
  · rw [← hloghalf]
    exact hloglo
  · exact hloghi

private theorem measure_abs_tail_le_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (hmean : ∫ ω, X ω ∂μ = 0) {c : ℝ} (hc : 0 < c) :
    (μ {ω | c < |X ω|}).toReal ≤ Var[X; μ] / c ^ 2 := by
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hX hc
  have hsubset : {ω | c < |X ω|} ⊆ {ω | c ≤ |X ω - μ[X]|} := by
    intro ω hω
    have hmean' : μ[X] = 0 := by simpa using hmean
    simpa [hmean'] using hω.le
  have hmeasure : μ {ω | c < |X ω|} ≤ ENNReal.ofReal (Var[X; μ] / c ^ 2) :=
    (measure_mono hsubset).trans hcheb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  have hnonneg : 0 ≤ Var[X; μ] / c ^ 2 :=
    div_nonneg (variance_nonneg X μ) (sq_nonneg c)
  simpa [ENNReal.toReal_ofReal hnonneg] using hreal

private theorem memLp_log_smoothedP2Plane_critical (ϑ : ℝ) (N m : ℕ) (x : Site) :
    MemLp (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ N) m N x ω))
      2 disorderLaw := by
  exact (variance_log_smoothedP2Plane_le
    (by dsimp [criticalBeta]; positivity) m N x).1

private theorem mul_three_div_cancel {a x : ℝ} (ha : a ≠ 0) :
    a * ((3 / a) * x) = 3 * x := by
  have h : a * (3 / a) = 3 := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ 3 ha]
  calc
    a * ((3 / a) * x) = (a * (3 / a)) * x := by ring
    _ = 3 * x := by rw [h]

private theorem three_thirds (x : ℝ) : x / 3 + x / 3 + x / 3 = x := by ring

private theorem exp_tail_coeff_le {δ s E B : ℝ} (hδ : 0 < δ) (hs : 0 < s)
    (hE : 1 ≤ E) (hscale : ((3 / δ) * (Real.log E + 1)) ^ 2 < s ^ 2)
    (hB : 3 * B / δ ≤ E) (hBnonneg : 0 ≤ B) :
    B * Real.exp (-(δ * s / 3)) ≤ δ / 3 := by
  have hrootNonneg : 0 ≤ (3 / δ) * (Real.log E + 1) :=
    mul_nonneg (by positivity) (add_nonneg (Real.log_nonneg hE) (by norm_num))
  have hroot : (3 / δ) * (Real.log E + 1) < s :=
    (sq_lt_sq₀ hrootNonneg hs.le).mp hscale
  have hmul := mul_lt_mul_of_pos_left hroot hδ
  have hcancel := mul_three_div_cancel (a := δ) (x := Real.log E + 1) (ne_of_gt hδ)
  have hraw : 3 * (Real.log E + 1) < δ * s := by
    calc
      3 * (Real.log E + 1) = δ * ((3 / δ) * (Real.log E + 1)) := hcancel.symm
      _ < δ * s := hmul
  have hsum : Real.log E + 1 < δ * s / 3 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    simpa only [mul_comm] using hraw
  have hlog : Real.log E < δ * s / 3 :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans_lt hsum
  have hEpos : 0 < E := lt_of_lt_of_le (by norm_num) hE
  have hexp : Real.exp (-(δ * s / 3)) ≤ E⁻¹ := by
    calc
      Real.exp (-(δ * s / 3)) ≤ Real.exp (-Real.log E) :=
        Real.exp_le_exp.mpr (neg_le_neg hlog.le)
      _ = E⁻¹ := by rw [Real.exp_neg, Real.exp_log hEpos]
  have hmulB := (div_le_iff₀ hδ).mp hB
  have hBInv : B * E⁻¹ ≤ δ / 3 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).2
    calc
      (B * E⁻¹) * 3 = (3 * B) * E⁻¹ := by ring
      _ ≤ (δ * E) * E⁻¹ :=
        mul_le_mul_of_nonneg_right (by simpa only [mul_comm] using hmulB)
          (inv_nonneg.mpr hEpos.le)
      _ = δ := by rw [mul_assoc, mul_inv_cancel₀ hEpos.ne', mul_one]
  exact (mul_le_mul_of_nonneg_left hexp hBnonneg).trans hBInv

private theorem measure_abs_log_tail_of_two_sided {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) {r u v w : ℝ}
    (hminus : (μ {ω | Real.log (X ω) < -r}).toReal ≤ u + v)
    (hplus : (μ {ω | r < Real.log (X ω)}).toReal ≤ w) :
    (μ {ω | r < |Real.log (X ω)|}).toReal ≤ u + v + w := by
  let A : Set Ω := {ω | Real.log (X ω) < -r}
  let B : Set Ω := {ω | r < Real.log (X ω)}
  have hsubset : {ω | r < |Real.log (X ω)|} ⊆ A ∪ B := by
    intro ω hω
    by_cases hlt : Real.log (X ω) < -r
    · exact Or.inl hlt
    · by_cases hgt : r < Real.log (X ω)
      · exact Or.inr hgt
      · have hbound : |Real.log (X ω)| ≤ r :=
          abs_le.mpr ⟨le_of_not_gt hlt, le_of_not_gt hgt⟩
        exact False.elim ((not_lt_of_ge hbound) hω)
  have hmeasure : μ {ω | r < |Real.log (X ω)|} ≤ μ A + μ B :=
    (measure_mono hsubset).trans (measure_union_le _ _)
  have htop : μ A + μ B ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top μ A, measure_ne_top μ B⟩
  have hreal := ENNReal.toReal_mono htop hmeasure
  rw [ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ B)] at hreal
  exact hreal.trans (add_le_add hminus hplus)

private theorem measure_abs_log_tail_with_exp_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) {δ s E u v w B : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hE : 1 ≤ E)
    (hscale : ((3 / δ) * (Real.log E + 1)) ^ 2 < s ^ 2)
    (hA : 3 * B / δ ≤ E) (hB : 0 ≤ B)
    (hminus : (μ {ω | Real.log (X ω) < -(δ * s / 3)}).toReal ≤ u + v)
    (hplus : (μ {ω | δ * s / 3 < Real.log (X ω)}).toReal ≤ w)
    (hcombine : v + w = B * Real.exp (-(δ * s / 3))) :
    (μ {ω | δ * s / 3 < |Real.log (X ω)|}).toReal ≤
        u + B * Real.exp (-(δ * s / 3)) ∧
      B * Real.exp (-(δ * s / 3)) ≤ δ / 3 := by
  have hprob := measure_abs_log_tail_of_two_sided μ X hminus hplus
  have hdecay := exp_tail_coeff_le hδ hs hE hscale hA hB
  constructor
  · calc
      _ ≤ u + v + w := hprob
      _ = u + B * Real.exp (-(δ * s / 3)) := by rw [← hcombine]; ring
  · exact hdecay

private theorem measure_toReal_mono_of_subset {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A B : Set Ω} (hAB : A ⊆ B)
    {c d : ℝ} (hB : (μ B).toReal ≤ c) (hcd : c ≤ d) :
    (μ A).toReal ≤ d := by
  have hmeasure : μ A ≤ μ B := measure_mono hAB
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hmeasure
  exact hreal.trans hB |>.trans hcd

private theorem finite_sum_le_eight_mul {ι : Type*} (I : Finset ι)
    (f w : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hpoint : ∀ i ∈ I, f i ≤ C * w i)
    (hweight : ∑ i ∈ I, w i ≤ 8) :
    ∑ i ∈ I, f i ≤ 8 * C := by
  calc
    ∑ i ∈ I, f i ≤ ∑ i ∈ I, C * w i := Finset.sum_le_sum hpoint
    _ = C * ∑ i ∈ I, w i := by rw [Finset.mul_sum]
    _ ≤ C * 8 := mul_le_mul_of_nonneg_left hweight hC
    _ = 8 * C := by ring

private theorem sum_grid_inv_three_halves_le {K lo hi : ℕ}
    (hlohi : lo ≤ hi) (hhiK : hi ≤ K) :
    ∑ i ∈ Finset.Icc lo hi, ((K : ℝ) + 1 - i) ^ (-(3 / 2 : ℝ)) ≤ 8 := by
  have hEndpoint := sum_endpoint_inv_three_halves_le hlohi (Nat.lt_succ_of_le hhiK)
  have hcastHi : ((K + 1 - hi : ℕ) : ℝ) = (K : ℝ) + 1 - hi := by
    rw [Nat.cast_sub (by omega : hi ≤ K + 1), Nat.cast_add]
    norm_num
  have hroot : 1 ≤ Real.sqrt (((K + 1 : ℝ) - hi)) := by
    rw [← hcastHi]
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt ((K + 1 - hi : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast (show 1 ≤ K + 1 - hi by omega))
  have hrootpos : 0 < Real.sqrt (((K + 1 : ℝ) - hi)) := lt_of_lt_of_le (by norm_num) hroot
  have hbound : 8 / Real.sqrt (((K + 1 : ℝ) - hi)) ≤ 8 := by
    apply (div_le_iff₀ hrootpos).2
    nlinarith only [hroot]
  calc
    _ = ∑ i ∈ Finset.Icc lo hi, ((K + 1 : ℝ) - i) ^ (-(3 / 2 : ℝ)) := by simp
    _ ≤ 8 / Real.sqrt (((K + 1 : ℝ) - hi)) := by simpa [Nat.cast_add] using hEndpoint
    _ ≤ 8 := hbound

private theorem interval_sum_rpow_bound {K lo hi : ℕ} (C : ℝ) (f : ℕ → ℝ)
    (hlohi : lo ≤ hi) (hhiK : hi ≤ K) (hC : 0 ≤ C)
    (hf : ∀ i ∈ Finset.Icc lo hi,
      f i ≤ C / ((K : ℝ) + 1 - i) ^ ((3 : ℝ) / 2)) :
    ∑ i ∈ Finset.Icc lo hi, f i ≤ 8 * C := by
  have hweight := sum_grid_inv_three_halves_le hlohi hhiK
  apply finite_sum_le_eight_mul (Finset.Icc lo hi) f
    (fun i => ((K : ℝ) + 1 - i) ^ (-(3 / 2 : ℝ))) hC
  · intro i hiI
    have h := hf i hiI
    have hnat : 1 ≤ K + 1 - i := by
      have hi' := Finset.mem_Icc.mp hiI
      omega
    have hcast : ((K + 1 - i : ℕ) : ℝ) = (K : ℝ) + 1 - i := by
      rw [Nat.cast_sub (by omega : i ≤ K + 1), Nat.cast_add]
      norm_num
    have hd : 0 < (K : ℝ) + 1 - i := by
      rw [← hcast]
      exact_mod_cast (show 0 < K + 1 - i by omega)
    rw [div_eq_mul_inv, ← Real.rpow_neg hd.le] at h
    simpa [mul_comm] using h
  · exact hweight

private theorem measure_union_three_toReal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B C : Set Ω) {a b c : ℝ}
    (hA : (μ A).toReal ≤ a) (hB : (μ B).toReal ≤ b) (hC : (μ C).toReal ≤ c) :
    (μ (A ∪ B ∪ C)).toReal ≤ a + b + c := by
  have hABne : μ A + μ B ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨measure_ne_top μ A, measure_ne_top μ B⟩
  have hABCne : μ A + μ B + μ C ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hABne, measure_ne_top μ C⟩
  have hmeasure : μ (A ∪ B ∪ C) ≤ μ A + μ B + μ C := by
    calc
      μ (A ∪ B ∪ C) ≤ μ (A ∪ B) + μ C := measure_union_le _ _
      _ ≤ (μ A + μ B) + μ C := add_le_add (measure_union_le _ _) le_rfl
  have hreal := ENNReal.toReal_mono hABCne hmeasure
  rw [ENNReal.toReal_add hABne (measure_ne_top μ C),
    ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ B)] at hreal
  exact hreal.trans (add_le_add (add_le_add hA hB) hC)

private theorem measure_abs_sum_three_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y Z : Ω → ℝ) {r p q t : ℝ}
    (hX : (μ {ω | r < |X ω|}).toReal ≤ p)
    (hY : (μ {ω | r < |Y ω|}).toReal ≤ q)
    (hZ : (μ {ω | r < |Z ω|}).toReal ≤ t) :
    (μ {ω | r + r + r < |X ω + Y ω + Z ω|}).toReal ≤ p + q + t := by
  let A : Set Ω := {ω | r < |X ω|}
  let B : Set Ω := {ω | r < |Y ω|}
  let C : Set Ω := {ω | r < |Z ω|}
  have hsubset : {ω | r + r + r < |X ω + Y ω + Z ω|} ⊆ A ∪ B ∪ C := by
    intro ω hω
    by_contra hn
    have hX' : |X ω| ≤ r := le_of_not_gt (fun h => hn (Or.inl (Or.inl h)))
    have hY' : |Y ω| ≤ r := le_of_not_gt (fun h => hn (Or.inl (Or.inr h)))
    have hZ' : |Z ω| ≤ r := le_of_not_gt (fun h => hn (Or.inr h))
    have htri : |X ω + Y ω + Z ω| ≤ |X ω| + |Y ω| + |Z ω| := by
      calc
        |X ω + Y ω + Z ω| ≤ |X ω + Y ω| + |Z ω| := abs_add_le _ _
        _ ≤ |X ω| + |Y ω| + |Z ω| := add_le_add (abs_add_le _ _) le_rfl
    have hsmall : |X ω + Y ω + Z ω| ≤ r + r + r := by
      calc
        |X ω + Y ω + Z ω| ≤ |X ω| + |Y ω| + |Z ω| := htri
        _ ≤ r + r + r := add_le_add (add_le_add hX' hY') hZ'
    exact (not_lt_of_ge hsmall) hω
  have hsubsetMeasure : μ {ω | r + r + r < |X ω + Y ω + Z ω|} ≤ μ (A ∪ B ∪ C) :=
    measure_mono hsubset
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) hsubsetMeasure
  exact hreal.trans (measure_union_three_toReal μ A B C hX hY hZ)

private theorem measure_abs_sum_three_small {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y Z : Ω → ℝ) {δ s a b t : ℝ}
    (hX : (μ {ω | δ * s / 3 < |X ω|}).toReal ≤ δ / 3)
    (hY : (μ {ω | δ * s / 3 < |Y ω|}).toReal ≤ a)
    (hZ : (μ {ω | δ * s / 3 < |Z ω|}).toReal ≤ b + t)
    (hsum : a + b ≤ δ / 3) (ht : t ≤ δ / 3) :
    (μ {ω | δ * s < |X ω + Y ω + Z ω|}).toReal ≤ δ := by
  have hUnion := measure_abs_sum_three_tail μ X Y Z hX hY hZ
  have hEvent : {ω | δ * s < |X ω + Y ω + Z ω|} =
      {ω | δ * s / 3 + δ * s / 3 + δ * s / 3 < |X ω + Y ω + Z ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    rw [three_thirds (δ * s)]
  rw [hEvent]
  calc
    _ ≤ δ / 3 + a + b + t := by simpa only [add_assoc] using hUnion
    _ ≤ δ / 3 + δ / 3 + δ / 3 := by
      have hfirst := add_le_add (le_rfl : δ / 3 ≤ δ / 3) hsum
      calc
        δ / 3 + a + b + t = (δ / 3 + (a + b)) + t := by simp [add_assoc]
        _ ≤ (δ / 3 + δ / 3) + δ / 3 := add_le_add hfirst ht
    _ = δ := by rw [three_thirds]

private theorem one_lt_sq_mul_of_div_bound {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hN : 2 / ε ^ 2 < (N : ℝ)) :
    1 < ε ^ 2 * (N : ℝ) := by
  have hmul : 2 < (N : ℝ) * ε ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hε)).mp hN
  calc
    (1 : ℝ) < 2 := by norm_num
    _ < (N : ℝ) * ε ^ 2 := hmul
    _ = ε ^ 2 * (N : ℝ) := by rw [mul_comm]

private theorem natCast_pos_of_div_bound {ε : ℝ} {N : ℕ}
    (hε : 0 < ε) (hN : 2 / ε ^ 2 < (N : ℝ)) : 0 < (N : ℝ) := by
  have hdiv : 0 < (2 : ℝ) / ε ^ 2 := by positivity
  exact lt_trans hdiv hN

private theorem natRatio_le_inv_sq {ε : ℝ} {N m : ℕ} (hε : 0 < ε)
    (hm : 1 ≤ m) (hbound : ε ^ 2 * (N : ℝ) ≤ (m : ℝ)) :
    (N : ℝ) / (max m 1 : ℕ) ≤ (ε ^ 2)⁻¹ := by
  rw [max_eq_left hm]
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  apply (div_le_iff₀ (by exact_mod_cast hmpos)).2
  calc
    (N : ℝ) = (ε ^ 2 * (N : ℝ)) * (ε ^ 2)⁻¹ := by
      field_simp [ne_of_gt (sq_pos_of_pos hε)]
    _ ≤ (m : ℝ) * (ε ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hbound (inv_nonneg.mpr (sq_pos_of_pos hε).le)
    _ = (ε ^ 2)⁻¹ * (m : ℝ) := by ring

private theorem log_inv_pos_of_unit_interval {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 < Real.log ε⁻¹ := by
  rw [Real.log_inv]
  exact neg_pos.mpr (Real.log_neg hε hε1)

private theorem log_le_two_log_inv_of_ratio {ε r : ℝ} (hr : 0 < r)
    (hbound : r ≤ (ε ^ 2)⁻¹) : Real.log r ≤ 2 * Real.log ε⁻¹ := by
  have hlog := Real.log_le_log hr hbound
  calc
    Real.log r ≤ Real.log ((ε ^ 2)⁻¹) := hlog
    _ = 2 * Real.log ε⁻¹ := by rw [Real.log_inv, Real.log_pow, Real.log_inv]; ring

private theorem natRatio_ge_one {N m : ℕ} (hm : 1 ≤ m) (hmN : m ≤ N) :
    1 ≤ (N : ℝ) / (max m 1 : ℕ) := by
  rw [max_eq_left hm]
  apply (one_le_div (by exact_mod_cast (show 0 < m by omega))).2
  exact_mod_cast hmN

private theorem secondMoment_fixedN {A C : ℝ} {N m : ℕ} (ϑ : ℝ)
    (hC₂ : ∀ ψ ∈ Set.Icc (-A) A, ∀ s n : ℕ, s ≤ n →
      (1 : ℝ) * N ≤ n → (n : ℝ) ≤ (1 : ℝ) * N →
        ∫ ω, smoothedP2Plane (criticalBeta ψ N) s n 0 ω ^ 2 ∂disorderLaw ≤
          C * (1 + Real.log ((n : ℝ) / (max s 1 : ℕ))))
    (hϑ : ϑ ∈ Set.Icc (-A) A) (hmN : m ≤ N) :
    ∫ ω, smoothedP2Plane (criticalBeta ϑ N) m N 0 ω ^ 2 ∂disorderLaw ≤
      C * (1 + Real.log ((N : ℝ) / (max m 1 : ℕ))) := by
  have h := hC₂ ϑ hϑ m N hmN (by norm_num) (by norm_num)
  simpa [one_mul] using h

private theorem secondMoment_quadratic_bound (x L : ℝ) (hx : 0 ≤ x)
    (hL : 2 * x + 3 < L) : (x + 1) * (1 + 2 * L) ≤ L ^ 2 := by
  have hxbound : x + 1 ≤ (L - 1) / 2 := by linarith only [hL]
  have hfactor : 0 ≤ 1 + 2 * L := by linarith only [hx, hL]
  calc
    (x + 1) * (1 + 2 * L) ≤ ((L - 1) / 2) * (1 + 2 * L) :=
      mul_le_mul_of_nonneg_right hxbound hfactor
    _ ≤ L ^ 2 := by nlinarith [sq_nonneg L]

private theorem secondMoment_abs_quadratic_bound (C L : ℝ)
    (hL : 2 * |C| + 3 < L) : (|C| + 1) * (1 + 2 * L) ≤ L ^ 2 :=
  secondMoment_quadratic_bound |C| L (abs_nonneg C) hL

private theorem secondMoment_scale_pos (C : ℝ) : 0 < 2 * |C| + 3 := by positivity

private theorem lt_of_log_le_lt {a b d : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₁ : Real.log a ≤ d) (h₂ : d < Real.log b) : a < b :=
  (Real.log_lt_log_iff ha hb).mp (lt_of_le_of_lt h₁ h₂)

private theorem secondMoment_scale_lt_of_bounds (C D L : ℝ) (hLpos : 0 < L)
    (hDsecond : max 0 (Real.log (2 * |C| + 3)) ≤ D) (hDsmall : D < Real.log L) :
    2 * |C| + 3 < L := by
  have hlog : Real.log (2 * |C| + 3) ≤ D :=
    (le_max_right (0 : ℝ) (Real.log (2 * |C| + 3))).trans hDsecond
  exact lt_of_log_le_lt (secondMoment_scale_pos C) hLpos hlog hDsmall

private theorem scaled_logρ_neg_lt_log_inv {a b : ℝ} (ha : 1 < a) (hb : 0 < b) :
    -(a * b) < -b := by
  have hmul : b * 1 < b * a := mul_lt_mul_of_pos_left ha hb
  simpa [mul_comm] using neg_lt_neg hmul

private theorem centered_tail_abs_base {δh s z c : ℝ}
    (hcenter : δh * s < |z - c|)
    (htriangle : |z - c| ≤ |z| + |c|)
    (hmean : |c| ≤ (δh / 2) * s) :
    δh * s / 2 < |z| := by
  have hmean' : |c| ≤ δh * s / 2 := by
    calc
      |c| ≤ (δh / 2) * s := hmean
      _ = δh * s / 2 := by ring
  have hlarge : δh * s < |z| + |c| := lt_of_lt_of_le hcenter htriangle
  linarith only [hlarge, hmean']

private theorem abs_add_one_nonneg (x : ℝ) : 0 ≤ |x| + 1 := by positivity

private theorem integral_sq_bound_of_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Ω → ℝ) (C L R : ℝ)
    (hInt : Integrable (fun ω => W ω ^ 2) μ)
    (hraw : ∫ ω, W ω ^ 2 ∂μ ≤ C * (1 + R))
    (hC : C ≤ |C| + 1) (hRnonneg : 0 ≤ 1 + R)
    (hRbound : 1 + R ≤ 1 + 2 * L)
    (hLlarge : 2 * |C| + 3 < L) :
    Integrable (fun ω => W ω ^ 2) μ ∧ ∫ ω, W ω ^ 2 ∂μ ≤ L ^ 2 := by
  have hquad := secondMoment_abs_quadratic_bound C L hLlarge
  refine ⟨hInt, ?_⟩
  calc
    ∫ ω, W ω ^ 2 ∂μ ≤ C * (1 + R) := hraw
    _ ≤ (|C| + 1) * (1 + R) := mul_le_mul_of_nonneg_right hC hRnonneg
    _ ≤ (|C| + 1) * (1 + 2 * L) :=
      mul_le_mul_of_nonneg_left hRbound (abs_add_one_nonneg C)
    _ ≤ L ^ 2 := hquad

private theorem zbase_eq_of_log_decomp {Ω : Type*} (F S Q V Xsum Rsum : Ω → ℝ)
    (c : ℝ) (hS : ∀ ω, S ω = Xsum ω + Rsum ω)
    (hF : ∀ ω, Real.log (F ω) = S ω + Real.log (Q ω) + Real.log (V ω)) (ω : Ω) :
    Rsum ω - c + Real.log (Q ω) + Real.log (V ω) =
      (Real.log (F ω) - Xsum ω) - c := by
  rw [hF ω, hS ω]
  ring

/-- The logarithm of the smoothed mass from time `evenCeil (ε ^ 2 * N)` to `N`, at the origin. -/
private noncomputable def latticeLogMass (ϑ ε : ℝ) (N : ℕ) (ω : Disorder) : ℝ :=
  Real.log (smoothedP2Plane (criticalBeta ϑ N) (evenCeil (ε ^ 2 * N)) N 0 ω)

private theorem blockTime_count_eq {N : ℕ} {ρ : ℝ}
    (hK : 0 < blockCount N ρ) : blockTime N ρ (blockCount N ρ) = N := by
  simp [Critical2DKPZ.blockTime, Nat.ne_of_gt hK]

private theorem smoothedP2Plane_memLp_two (β : ℝ) (m N : ℕ) :
    MemLp (smoothedP2Plane β m N 0) 2 disorderLaw :=
  Polymer.memLp_smoothedP2Plane β m N 0 2 (by norm_num)

/-- Under the block-moment and profile estimates, the mean-centred log mass divided by
`√(log log ε⁻¹)` is asymptotically standard normal in bounded continuous tests.
The estimate holds for sufficiently small `ε` and subsequently large `N`. -/
theorem lattice_logNormality_of (hC6 : BlockMomentsBound) (hPE : ProfileEstimatesBound)
    (ϑ : ℝ) :
    ∀ (h : ℝ →ᵇ ℝ) (η : ℝ), 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ᶠ N : ℕ in atTop,
        |∫ ω, h ((Real.log (smoothedP2Plane (criticalBeta ϑ N) (evenCeil (ε ^ 2 * N)) N 0 ω) -
              ∫ ω', Real.log (smoothedP2Plane (criticalBeta ϑ N) (evenCeil (ε ^ 2 * N)) N 0 ω')
                ∂disorderLaw) / Real.sqrt (Real.log (Real.log ε⁻¹))) ∂disorderLaw -
          ∫ y, h y ∂(gaussianReal 0 1)| ≤ η := by
  intro h η hη
  obtain ⟨δh, hδh, hLyaph⟩ := exists_lyapunov_clt_bound h (half_pos hη)
  obtain ⟨h₁, h₂, δtest, hδtest, hcenter⟩ :=
    exists_testFunctions_abs_integral_le 4 (half_pos hδh)
  obtain ⟨δ₁, hδ₁, hLyap₁⟩ := exists_lyapunov_clt_bound h₁ hδtest
  obtain ⟨δ₂, hδ₂, hLyap₂⟩ := exists_lyapunov_clt_bound h₂ hδtest
  let δ : ℝ := min (min δ₁ δ₂) (δh / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle₁ : δ ≤ δ₁ := by dsimp [δ]; exact min_le_left _ _ |>.trans (min_le_left _ _)
  have hδle₂ : δ ≤ δ₂ := by dsimp [δ]; exact min_le_left _ _ |>.trans (min_le_right _ _)
  have hδleH : δ ≤ δh / 2 := by dsimp [δ]; exact min_le_right _ _
  have htwoδleH : 2 * δ ≤ δh := by linarith only [hδleH]
  obtain ⟨ρVar₀, hρVar₀, hVar⟩ := sum_variance_blockMass_grid_sub_loglog_le ϑ
  obtain ⟨ρPE₀, hρPE₀, hPEA⟩ := hPE |ϑ|
  obtain ⟨ρTail₀, hρTail₀, hTailA⟩ := lastInterval_log_tail_of hPE |ϑ|
  let ρ : ℝ := max (max ρVar₀ ρPE₀) ρTail₀ + 1
  have hρgt : 1 < ρ := by
    dsimp [ρ]
    have hmax : 1 < max (max ρVar₀ ρPE₀) ρTail₀ :=
      lt_of_lt_of_le hρTail₀ (le_max_right _ _)
    exact hmax.trans (lt_add_one _)
  have hρVar : ρVar₀ ≤ ρ := by
    dsimp [ρ]
    have hmax : ρVar₀ ≤ max (max ρVar₀ ρPE₀) ρTail₀ :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    exact hmax.trans (le_add_of_nonneg_right zero_le_one)
  have hρPE : ρPE₀ ≤ ρ := by
    dsimp [ρ]
    have hmax : ρPE₀ ≤ max (max ρVar₀ ρPE₀) ρTail₀ :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    exact hmax.trans (le_add_of_nonneg_right zero_le_one)
  have hρTail : ρTail₀ ≤ ρ := by
    dsimp [ρ]
    have hmax : ρTail₀ ≤ max (max ρVar₀ ρPE₀) ρTail₀ := le_max_right _ _
    exact hmax.trans (le_add_of_nonneg_right zero_le_one)
  have hρpos : 0 < ρ := zero_lt_one.trans hρgt
  obtain ⟨CPE, ℓPE, hPEbound⟩ := hPEA (ρ ^ 2)
  obtain ⟨CTail, ℓTail, hTailBound⟩ := hTailA (ρ ^ 2)
  have hρsq : ρ ≤ ρ ^ 2 := by nlinarith [sq_nonneg (ρ - 1)]
  obtain ⟨Cmom, hMom⟩ := blockMass_log_moments_of hC6 |ϑ| ρVar₀ (ρ ^ 2) hρVar₀
  let Cmom' : ℝ := |Cmom| + 1
  let CPE' : ℝ := |CPE| + 1
  let CTail' : ℝ := |CTail| + 1
  have hCmompos : 0 < Cmom' := by dsimp [Cmom']; positivity
  have hCPEpos : 0 < CPE' := by dsimp [CPE']; positivity
  have hCTailpos : 0 < CTail' := by dsimp [CTail']; positivity
  have hCPEle : CPE ≤ CPE' :=
    (le_abs_self CPE).trans (le_add_of_nonneg_right zero_le_one)
  have hCTaile : CTail ≤ CTail' :=
    (le_abs_self CTail).trans (le_add_of_nonneg_right zero_le_one)
  have hCmom : Cmom ≤ Cmom' :=
    (le_abs_self Cmom).trans (le_add_of_nonneg_right zero_le_one)
  let ℓ₀ : ℕ := max (max ℓPE ℓTail) 1
  let ℓlarge : ℕ := ⌈3 * (CPE' + CTail') / δ⌉₊
  let ℓ : ℕ := max ℓ₀ ℓlarge
  have hℓPE : ℓPE ≤ ℓ := by dsimp [ℓ, ℓ₀]; omega
  have hℓTail : ℓTail ≤ ℓ := by dsimp [ℓ, ℓ₀]; omega
  have hℓone : 1 ≤ ℓ := by dsimp [ℓ, ℓ₀]; omega
  have hℓlarge : 3 * (CPE' + CTail') / δ ≤ (ℓ : ℝ) := by
    have hceil : 3 * (CPE' + CTail') / δ ≤ (ℓlarge : ℝ) := by
      dsimp [ℓlarge]
      exact Nat.le_ceil _
    exact hceil.trans (by exact_mod_cast (Nat.le_max_right ℓ₀ ℓlarge))
  have hbaseTail : (CPE' + CTail') / ℓ ≤ δ / 3 := by
    have hℓpos : 0 < (ℓ : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hℓone)
    apply (div_le_iff₀ hℓpos).2
    have hlarge' := (div_le_iff₀ hδ).mp hℓlarge
    nlinarith [hlarge']
  obtain ⟨Cvar, εvar, hεvar, hVarBound⟩ := hVar ρ hρVar ℓ hℓone
  have hϑ : ϑ ∈ Set.Icc (-|ϑ|) |ϑ| := by
    exact ⟨neg_abs_le ϑ, le_abs_self ϑ⟩
  let Dvar : ℝ := (|Cvar| + 1) / δ
  let Dthird : ℝ := 8 * Cmom' / δ
  let Drem : ℝ := 216 * Cmom' / δ ^ 3
  let Dlog2 : ℝ := (3 * Real.log 2 / δ) ^ 2
  let Eexp : ℝ := max 1 (3 * (CTail' * ℓ + 1) / δ)
  let Dexp : ℝ := ((3 / δ) * (Real.log Eexp + 1)) ^ 2
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_log |ϑ| 1 1 (by norm_num)
  let Dsecond : ℝ := max 0 (Real.log (2 * |C₂| + 3))
  let D : ℝ := max Dvar (max Dthird (max Drem (max Dlog2 (max Dexp Dsecond))))
  have hDnonneg : 0 ≤ D := by
    dsimp [D, Dvar, Dthird, Drem, Dlog2, Dexp, Dsecond]
    positivity
  have hDvar : (|Cvar| + 1) / δ ≤ D := by
    dsimp [D]
    exact le_max_left _ _
  have hDthird : 8 * Cmom' / δ ≤ D := by
    change Dthird ≤ max Dvar (max Dthird (max Drem (max Dlog2 (max Dexp Dsecond))))
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hDrem : 216 * Cmom' / δ ^ 3 ≤ D := by
    change Drem ≤ max Dvar (max Dthird (max Drem (max Dlog2 (max Dexp Dsecond))))
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hDlog2 : (3 * Real.log 2 / δ) ^ 2 ≤ D := by
    change Dlog2 ≤ max Dvar (max Dthird (max Drem (max Dlog2 (max Dexp Dsecond))))
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hDexp : ((3 / δ) * (Real.log Eexp + 1)) ^ 2 ≤ D := by
    change Dexp ≤ max Dvar (max Dthird (max Drem (max Dlog2 (max Dexp Dsecond))))
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hDsecond : Dsecond ≤ D := by
    change Dsecond ≤ max Dvar (max Dthird (max Drem (max Dlog2 (max Dexp Dsecond))))
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  let εgrid : ℝ := Real.exp (-((2 * (ℓ + 2 : ℕ) : ℝ) * Real.log ρ))
  let εsmall : ℝ := Real.exp (-Real.exp (D + 1))
  let ε₀ : ℝ := min εvar (min εgrid εsmall)
  have hεgridpos : 0 < εgrid := by dsimp [εgrid]; positivity
  have hεsmallpos : 0 < εsmall := by dsimp [εsmall]; positivity
  have hε₀pos : 0 < ε₀ := by dsimp [ε₀]; positivity
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro ε hε hε₀
  have hεvar' : ε < εvar := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεgrid' : ε < εgrid :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεsmall' : ε < εsmall :=
    lt_of_lt_of_le hε₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hlogρ : 0 < Real.log ρ := Real.log_pos hρgt
  have hlogε : Real.log ε < -((2 * (ℓ + 2 : ℕ) : ℝ) * Real.log ρ) := by
    have hh := Real.log_lt_log hε hεgrid'
    simpa [εgrid, Real.log_exp] using hh
  have hρinvlt : ρ⁻¹ < 1 := (inv_lt_one₀ hρpos).2 hρgt
  have hεrho : ε < ρ⁻¹ := by
    have hpow : -((2 * (ℓ + 2 : ℕ) : ℝ) * Real.log ρ) < -Real.log ρ := by
      have hell : (1 : ℝ) < 2 * (ℓ + 2 : ℕ) := by exact_mod_cast (by omega : 1 < 2 * (ℓ + 2))
      exact scaled_logρ_neg_lt_log_inv hell hlogρ
    have hloglt : Real.log ε < Real.log ρ⁻¹ := by
      simpa [Real.log_inv] using lt_trans hlogε hpow
    exact (Real.log_lt_log_iff hε (by positivity)).mp hloglt
  have hε1 : ε < 1 := lt_trans hεrho hρinvlt
  have hεscale : ε ^ 2 ≤ ρ⁻¹ ^ 2 := (sq_le_sq₀ (by positivity) (by positivity)).2 hεrho.le
  let γ : ℝ := gridRatio (ε ^ 2) ρ
  let J : ℕ := gridBlocks (ε ^ 2) ρ
  have hγmem : γ ∈ Set.Icc ρ (ρ ^ 2) := by
    simpa [γ] using gridRatio_mem hρgt (sq_pos_of_pos hε) hεscale
  have hγ : 1 < γ := lt_of_lt_of_le hρgt hγmem.1
  have hγVar : ρVar₀ ≤ γ := le_trans hρVar hγmem.1
  have hγMom : γ ∈ Set.Icc ρVar₀ (ρ ^ 2) := ⟨hγVar, hγmem.2⟩
  have hJbounds := gridBlocks_bounds hρgt (sq_pos_of_pos hε) hεscale
  have hJlarge : ℓ + 2 ≤ J := by
    have habs : |Real.log (ε ^ 2)| = -2 * Real.log ε := by
      rw [Real.log_pow, abs_of_nonpos]
      · ring
      · have hlogneg := Real.log_neg hε hε1
        exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hlogneg.le
    have hlower := hJbounds.2.1
    have hcast : (ℓ : ℝ) + 2 ≤ (J : ℝ) := by
      calc
        (ℓ : ℝ) + 2 ≤ (-2 * Real.log ε) / (4 * Real.log ρ) := by
          have hmul : 2 * Real.log ε < -4 * ((ℓ : ℝ) + 2) * Real.log ρ := by
            calc
              2 * Real.log ε < 2 * (-((2 * (ℓ + 2 : ℕ) : ℝ) * Real.log ρ)) :=
                mul_lt_mul_of_pos_left hlogε (by norm_num)
              _ = -4 * ((ℓ : ℝ) + 2) * Real.log ρ := by push_cast; ring
          have hlogLower : 4 * ((ℓ : ℝ) + 2) * Real.log ρ < -2 * Real.log ε := by
            linarith only [hmul]
          apply (le_div_iff₀ (by positivity : 0 < 4 * Real.log ρ)).2
          calc
            ((ℓ : ℝ) + 2) * (4 * Real.log ρ) = 4 * ((ℓ : ℝ) + 2) * Real.log ρ := by ring
            _ ≤ -2 * Real.log ε := le_of_lt hlogLower
        _ = |Real.log (ε ^ 2)| / (4 * Real.log ρ) := by rw [habs]
        _ ≤ J := by simpa [J] using hlower
    exact_mod_cast hcast
  have hVarN := hVarBound ε hε hεvar'
  have hMomN := hMom γ hγMom
  have hK : ∀ᶠ N : ℕ in atTop, 2 * J + ℓ + 1 ≤ blockCount N γ :=
    (blockCount_tendsto_atTop hγ).eventually_ge_atTop (2 * J + ℓ + 1)
  have htN : ∀ᶠ N : ℕ in atTop, Monotone (blockTime N γ) := blockTime_monotone hγ
  have hGridAlign := blockTime_gridRatio hρgt (sq_pos_of_pos hε) hεscale
  have hPEγ : γ ∈ Set.Icc ρPE₀ (ρ ^ 2) := ⟨le_trans hρPE hγmem.1, hγmem.2⟩
  have hTailγ : γ ∈ Set.Icc ρTail₀ (ρ ^ 2) := ⟨le_trans hρTail hγmem.1, hγmem.2⟩
  have hPEN := hPEbound γ hPEγ
  have hTailN := hTailBound γ hTailγ
  have hNstart : ∀ᶠ N : ℕ in atTop, 2 / ε ^ 2 < (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (2 / ε ^ 2)
  filter_upwards [hVarN, hMomN, hK, htN, hGridAlign, hPEN, hTailN,
    hC₂, hNstart]
    with N hVarN hMomN hKN htN hGridN hPEN hTailN hC₂N hNstartN
  let K : ℕ := blockCount N γ
  let t : ℕ → ℕ := blockTime N γ
  let β : ℝ := criticalBeta ϑ N
  let lo : ℕ := K - 2 * J + 1
  let hi : ℕ := K - ℓ
  let I : Finset ℕ := Finset.Icc lo hi
  have hKbound : 2 * J + ℓ + 1 ≤ K := by simpa [K] using hKN
  have hlo : 1 ≤ lo := by dsimp [lo]; omega
  have hhiK : hi ≤ K := by dsimp [hi]; omega
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; omega
  have hhiEll : K - hi = ℓ := by dsimp [hi]; omega
  have htimeMono : Monotone t := by simpa [t] using htN
  have hgammaGridLeft : t (K - 2 * J) = evenCeil (ε ^ 2 * N) := by
    have h := hGridN.2.1
    simpa [t, K, J] using h
  have hϑmem : ϑ ∈ Set.Icc (-|ϑ|) |ϑ| := by
    exact ⟨neg_abs_le ϑ, le_abs_self ϑ⟩
  have hmom := hMomN ϑ hϑmem
  let ι := {i : ℕ // i ∈ I}
  let X : ι → Disorder → ℝ := fun i ω => blockMass β t i.1 ω - 1
  let R : ι → Disorder → ℝ := fun i ω =>
    Real.log (blockMass β t i.1 ω) - (blockMass β t i.1 ω - 1)
  have hIndex (i : ι) : 1 ≤ i.1 ∧ i.1 ≤ K := by
    have hi' := Finset.mem_Icc.mp i.2
    constructor
    · exact hlo.trans hi'.1
    · exact hi'.2.trans hhiK
  have hMomI (i : ι) := hmom i.1 (hIndex i).1 (hIndex i).2
  have hMassMeas (i : ι) : Measurable (fun ω => blockMass β t i.1 ω) := by
    exact (measurable_blockMass β t i.1).mono (Gaussian.disorderBlock_le _ _) le_rfl
  have hXmeas (i : ι) : Measurable (X i) := by dsimp [X]; exact (hMassMeas i).sub measurable_const
  have hRmeas (i : ι) : Measurable (R i) := by dsimp [R]; fun_prop
  have hXmem (i : ι) : MemLp (X i) 3 disorderLaw := by
    dsimp [X, blockMass, β, t]
    exact (Polymer.memLp_smoothedP2Plane _ _ _ _ 3 (by norm_num)).sub (memLp_const (1 : ℝ))
  have hXmean (i : ι) : ∫ ω, X i ω ∂disorderLaw = 0 := by
    dsimp [X, blockMass, β, t]
    rw [integral_sub ((Polymer.memLp_smoothedP2Plane _ _ _ _ 1 (by norm_num)).integrable (by norm_num))
      (integrable_const (1 : ℝ)), Polymer.integral_smoothedP2Plane]
    simp
  have hRmem (i : ι) : MemLp (R i) 2 disorderLaw := by
    apply (memLp_two_iff_integrable_sq (hRmeas i).aestronglyMeasurable).2
    simpa [Real.norm_eq_abs, sq_abs] using (hMomI i).2.2.1
  let ιpos := {i : ℕ // 1 ≤ i}
  let e : ι → ιpos := fun i => ⟨i.1, (hIndex i).1⟩
  have he : Function.Injective e := by
    intro i j hij
    exact Subtype.ext (congrArg (fun q : ιpos => q.1) hij)
  have hMassInd : iIndepFun (fun i : ι => fun ω => blockMass β t i.1 ω) disorderLaw := by
    have h := (iIndepFun_blockMass β t htimeMono).precomp he
    simpa [e] using h
  have hXInd : iIndepFun X disorderLaw := by
    convert (hMassInd.comp (fun _ : ι => fun z : ℝ => z - 1)
      (fun _ => measurable_id.sub measurable_const)) using 1
    ext i ω
    rfl
  have hRInd : iIndepFun R disorderLaw := by
    convert (hMassInd.comp (fun _ : ι => fun z : ℝ => Real.log z - (z - 1))
      (fun _ => by fun_prop)) using 1
    ext i ω
    rfl
  have hthirdI (i : ι) :
      ∫ ω, |X i ω| ^ 3 ∂disorderLaw ≤ Cmom' /
        ((K : ℝ) + 1 - i.1) ^ ((3 : ℝ) / 2) := by
    have hd : 0 < (K : ℝ) + 1 - i.1 := by
      have hi := (hIndex i).2
      have hnat : 1 ≤ K + 1 - i.1 := by omega
      have hcast : ((K + 1 - i.1 : ℕ) : ℝ) = (K : ℝ) + 1 - i.1 := by
        rw [Nat.cast_sub (by omega : i.1 ≤ K + 1), Nat.cast_add]
        norm_num
      rw [← hcast]
      exact_mod_cast (show 0 < K + 1 - i.1 by omega)
    have hden : 0 ≤ ((K : ℝ) + 1 - i.1) ^ ((3 : ℝ) / 2) :=
      Real.rpow_nonneg hd.le _
    have hbound := (hMomI i).2.1.trans (div_le_div_of_nonneg_right hCmom hden)
    simpa [X, Cmom'] using hbound
  have hsecondI (i : ι) :
      ∫ ω, R i ω ^ 2 ∂disorderLaw ≤ Cmom' /
        ((K : ℝ) + 1 - i.1) ^ ((3 : ℝ) / 2) := by
    have hd : 0 < (K : ℝ) + 1 - i.1 := by
      have hi := (hIndex i).2
      have hnat : 1 ≤ K + 1 - i.1 := by omega
      have hcast : ((K + 1 - i.1 : ℕ) : ℝ) = (K : ℝ) + 1 - i.1 := by
        rw [Nat.cast_sub (by omega : i.1 ≤ K + 1), Nat.cast_add]
        norm_num
      rw [← hcast]
      exact_mod_cast (show 0 < K + 1 - i.1 by omega)
    have hden : 0 ≤ ((K : ℝ) + 1 - i.1) ^ ((3 : ℝ) / 2) :=
      Real.rpow_nonneg hd.le _
    have hbound := (hMomI i).2.2.2.trans (div_le_div_of_nonneg_right hCmom hden)
    simpa [R, Cmom'] using hbound
  have hsumInv :
      ∑ i ∈ I, ((K : ℝ) + 1 - i) ^ (-(3 / 2 : ℝ)) ≤ 8 := by
    simpa [I] using sum_grid_inv_three_halves_le hlohi hhiK
  have hthirdSum :
      ∑ i ∈ I.attach, ∫ ω, |X i ω| ^ 3 ∂disorderLaw ≤ 8 * Cmom' := by
    have hattach :
        (∑ i ∈ I.attach, ∫ ω, |X i ω| ^ 3 ∂disorderLaw) =
          ∑ i ∈ I, ∫ ω, |blockMass β t i ω - 1| ^ 3 ∂disorderLaw := by
      simpa [X] using Finset.sum_attach I
        (fun i => ∫ ω, |blockMass β t i ω - 1| ^ 3 ∂disorderLaw)
    rw [hattach]
    exact interval_sum_rpow_bound (K := K) (lo := lo) (hi := hi) Cmom'
      (fun i => ∫ ω, |blockMass β t i ω - 1| ^ 3 ∂disorderLaw)
      hlohi hhiK hCmompos.le (by
        intro i hiI
        simpa [X] using hthirdI ⟨i, hiI⟩)
  have hsecondSum :
      ∑ i ∈ I.attach, ∫ ω, R i ω ^ 2 ∂disorderLaw ≤ 8 * Cmom' := by
    have hattach :
        (∑ i ∈ I.attach, ∫ ω, R i ω ^ 2 ∂disorderLaw) =
          ∑ i ∈ I, ∫ ω,
            (Real.log (blockMass β t i ω) - (blockMass β t i ω - 1)) ^ 2 ∂disorderLaw := by
      simpa [R] using Finset.sum_attach I
        (fun i => ∫ ω, (Real.log (blockMass β t i ω) - (blockMass β t i ω - 1)) ^ 2 ∂disorderLaw)
    rw [hattach]
    exact interval_sum_rpow_bound (K := K) (lo := lo) (hi := hi) Cmom'
      (fun i => ∫ ω,
        (Real.log (blockMass β t i ω) - (blockMass β t i ω - 1)) ^ 2 ∂disorderLaw)
      hlohi hhiK hCmompos.le (by
        intro i hiI
        simpa [R] using hsecondI ⟨i, hiI⟩)
  let s : ℝ := Real.sqrt (Real.log (Real.log ε⁻¹))
  have hlogInv : Real.exp (D + 1) < Real.log ε⁻¹ := by
    have h := Real.log_lt_log hε hεsmall'
    rw [Real.log_exp] at h
    rw [Real.log_inv]
    linarith only [h]
  have hSlarge : D + 1 < Real.log (Real.log ε⁻¹) := by
    have h := Real.log_lt_log (Real.exp_pos _) hlogInv
    rw [Real.log_exp] at h
    exact h
  have hDsmall : D < Real.log (Real.log ε⁻¹) := (lt_add_one D).trans hSlarge
  have hSpos : 0 < Real.log (Real.log ε⁻¹) := hDnonneg.trans_lt hDsmall
  have hspos : 0 < s := by dsimp [s]; exact Real.sqrt_pos.mpr hSpos
  have hsSq : s ^ 2 = Real.log (Real.log ε⁻¹) := by
    dsimp [s]
    exact Real.sq_sqrt hSpos.le
  have hsOne : 1 ≤ s := by
    apply Real.one_le_sqrt.mpr
    linarith only [hDnonneg, hSlarge]
  let Xsum : Disorder → ℝ := fun ω => ∑ i ∈ I.attach, X i ω
  let Rsum : Disorder → ℝ := fun ω => ∑ i ∈ I.attach, R i ω
  let Zrem : Disorder → ℝ := fun ω => Rsum ω - ∫ ω', Rsum ω' ∂disorderLaw
  have hXsumMem : MemLp Xsum 2 disorderLaw := by
    dsimp [Xsum]
    exact memLp_finsetSum _ (fun i _ => (hXmem i).mono_exponent (by norm_num))
  have hRsumMem : MemLp Rsum 2 disorderLaw := by
    dsimp [Rsum]
    exact memLp_finsetSum _ (fun i _ => hRmem i)
  have hZremMem : MemLp Zrem 2 disorderLaw := by
    dsimp [Zrem]
    exact hRsumMem.sub (memLp_const (∫ ω', Rsum ω' ∂disorderLaw))
  have hZremMeas : Measurable Zrem := by
    dsimp [Zrem, Rsum]
    fun_prop
  have hXmeanI (i : ι) : ∫ ω, X i ω ∂disorderLaw = 0 := hXmean i
  have hVarXint (i : ι) : Var[X i; disorderLaw] = ∫ ω, X i ω ^ 2 ∂disorderLaw := by
    have hX2 : MemLp (X i) 2 disorderLaw := (hXmem i).mono_exponent (by norm_num)
    rw [variance_eq_sub hX2, hXmeanI i]
    simp
  have hVarAttach :
      (∑ i ∈ I.attach, Var[X i; disorderLaw]) =
        ∑ i ∈ I, Var[fun ω => blockMass β t i ω; disorderLaw] := by
    have hattach := Finset.sum_attach I
      (fun i => Var[fun ω => blockMass β t i ω - 1; disorderLaw])
    calc
      _ = ∑ i ∈ I, Var[fun ω => blockMass β t i ω - 1; disorderLaw] := by
        simpa [X] using hattach
      _ = ∑ i ∈ I, Var[fun ω => blockMass β t i ω; disorderLaw] := by
        apply Finset.sum_congr rfl
        intro i hiI
        exact ProbabilityTheory.variance_sub_const
          ((measurable_blockMass β t i).mono (Gaussian.disorderBlock_le _ _) le_rfl).aestronglyMeasurable 1
  have hVarIntSum :
      (∑ i ∈ I.attach, ∫ ω, X i ω ^ 2 ∂disorderLaw) =
        ∑ i ∈ I, Var[fun ω => blockMass β t i ω; disorderLaw] := by
    calc
      _ = ∑ i ∈ I.attach, Var[X i; disorderLaw] := by
        apply Finset.sum_congr rfl
        intro i hiI
        exact (hVarXint i).symm
      _ = _ := hVarAttach
  have hvarN := hVarN
  have hvarGrid :
      |(∑ i ∈ I.attach, ∫ ω, X i ω ^ 2 ∂disorderLaw) -
        Real.log (Real.log ε⁻¹)| ≤ Cvar := by
    rw [hVarIntSum]
    simpa [I, lo, hi, K, J, γ, t, β] using hvarN
  have hCvar : Cvar ≤ |Cvar| + 1 :=
    (le_abs_self Cvar).trans (le_add_of_nonneg_right zero_le_one)
  have hCvarSq : Cvar ≤ δ * s ^ 2 := by
    have hvarBound' : (|Cvar| + 1) / δ ≤ D := by
      simpa [Dvar] using hDvar
    have hvar' : |Cvar| + 1 ≤ δ * D := by
      simpa [mul_comm] using (div_le_iff₀ hδ).mp hvarBound'
    have hstrict : δ * D < δ * s ^ 2 :=
      mul_lt_mul_of_pos_left (by rw [hsSq]; exact hDsmall) hδ
    exact le_trans hCvar (le_trans hvar' (le_of_lt hstrict))
  have hthirdBound :
      ∑ i ∈ I.attach, ∫ ω, |X i ω| ^ 3 ∂disorderLaw ≤ δ * s ^ 3 := by
    have hthird' : 8 * Cmom' ≤ δ * D := by
      have h := (div_le_iff₀ hδ).mp hDthird
      simpa [mul_comm] using h
    have hDs : D < s ^ 2 := by rw [hsSq]; exact hDsmall
    have hsSqLe : s ^ 2 ≤ s ^ 3 := by
      calc
        s ^ 2 = s ^ 2 * 1 := by ring
        _ ≤ s ^ 2 * s := mul_le_mul_of_nonneg_left hsOne (sq_nonneg s)
        _ = s ^ 3 := by ring
    have hthird'' : 8 * Cmom' ≤ δ * s ^ 3 := by
      calc
        8 * Cmom' ≤ δ * D := hthird'
        _ ≤ δ * s ^ 2 := mul_le_mul_of_nonneg_left hDs.le hδ.le
        _ ≤ δ * s ^ 3 := mul_le_mul_of_nonneg_left hsSqLe hδ.le
    exact le_trans hthirdSum hthird''
  have hRVarSum : Var[Rsum; disorderLaw] ≤ 8 * Cmom' := by
    have hvarsum : Var[Rsum; disorderLaw] =
        ∑ i ∈ I.attach, Var[R i; disorderLaw] := by
      change Var[fun ω => ∑ i ∈ I.attach, R i ω; disorderLaw] = _
      exact variance_finset_of_iIndepFun disorderLaw I.attach R hRInd
        (fun i _ => hRmem i)
    calc
      Var[Rsum; disorderLaw] = ∑ i ∈ I.attach, Var[R i; disorderLaw] := hvarsum
      _ ≤ ∑ i ∈ I.attach, ∫ ω, R i ω ^ 2 ∂disorderLaw := by
        apply Finset.sum_le_sum
        intro i hiI
        rw [variance_eq_sub (hRmem i)]
        exact sub_le_self _ (sq_nonneg (∫ ω, R i ω ∂disorderLaw))
      _ ≤ 8 * Cmom' := hsecondSum
  have hZremVar : Var[Zrem; disorderLaw] ≤ 8 * Cmom' := by
    dsimp [Zrem]
    rw [ProbabilityTheory.variance_sub_const hRsumMem.aestronglyMeasurable]
    exact hRVarSum
  have hZremMean : ∫ ω, Zrem ω ∂disorderLaw = 0 := by
    dsimp [Zrem]
    rw [integral_sub (hRsumMem.integrable (by norm_num)) (integrable_const _), integral_const]
    simp
  have hZremTail : (disorderLaw {ω | δ * s / 3 < |Zrem ω|}).toReal ≤ δ / 3 := by
    have hcheb := measure_abs_tail_le_variance disorderLaw Zrem hZremMem hZremMean
      (c := δ * s / 3) (by positivity)
    have hDrem' : 216 * Cmom' ≤ δ ^ 3 * D := by
      have h := (div_le_iff₀ (pow_pos hδ 3)).mp hDrem
      simpa [mul_comm] using h
    have hDs : D < s ^ 2 := by rw [hsSq]; exact hDsmall
    have hprod : 216 * Cmom' ≤ δ ^ 3 * s ^ 2 := by
      calc
        216 * Cmom' ≤ δ ^ 3 * D := hDrem'
        _ ≤ δ ^ 3 * s ^ 2 :=
          mul_le_mul_of_nonneg_left hDs.le (by positivity)
    have hsmall : 72 * Cmom' / (δ ^ 2 * s ^ 2) ≤ δ / 3 := by
      apply (div_le_iff₀ (mul_pos (pow_pos hδ 2) (sq_pos_of_pos hspos))).2
      calc
        72 * Cmom' = (216 * Cmom') / 3 := by ring
        _ ≤ (δ ^ 3 * s ^ 2) / 3 :=
          div_le_div_of_nonneg_right hprod (by norm_num)
        _ = (δ / 3) * (δ ^ 2 * s ^ 2) := by ring
    have hbound : Var[Zrem; disorderLaw] / (δ * s / 3) ^ 2 ≤ δ / 3 := by
      have hEq : (δ * s / 3) ^ 2 = δ ^ 2 * s ^ 2 / 9 := by ring
      calc
        Var[Zrem; disorderLaw] / (δ * s / 3) ^ 2 ≤
            (8 * Cmom') / (δ * s / 3) ^ 2 :=
          div_le_div_of_nonneg_right hZremVar (by positivity)
        _ = 72 * Cmom' / (δ ^ 2 * s ^ 2) := by rw [hEq]; ring
        _ ≤ δ / 3 := hsmall
    exact hcheb.trans hbound
  let lo0 : ℕ := K - 2 * J
  let Q : Disorder → ℝ := blockRatio β t lo hi
  let V : Disorder → ℝ := smoothedP2Plane β (t lo0) N 0 /
      smoothedP2Plane β (t lo0) (t hi) 0
  let G : Set Disorder := profileGoodSet β t lo hi
  have hloPred : lo - 1 = lo0 := by omega
  have hlo0hi : lo0 ≤ hi := by dsimp [lo0, hi]; omega
  have hPEgood := hPEN ϑ hϑmem lo hi hlo hlohi (by
    have h := hℓPE
    dsimp [hi, K]
    omega)
  have hgap : (K : ℝ) - hi = ℓ := by
    have hn : K - (K - ℓ) = ℓ := Nat.sub_sub_self (by dsimp [K]; omega)
    dsimp [hi]
    exact_mod_cast hn
  have hGbad : (disorderLaw Gᶜ).toReal ≤ CPE' / ℓ := by
    have h := hPEgood.1
    have hbase : (disorderLaw Gᶜ).toReal ≤ CPE / ℓ := by
      simpa [G, β, t, K, hi, hgap] using h
    have hC : CPE ≤ CPE' :=
      (le_abs_self CPE).trans (le_add_of_nonneg_right zero_le_one)
    exact hbase.trans (div_le_div_of_nonneg_right hC (by positivity))
  have hQpos (ω : Disorder) : 0 < Q ω := by
    dsimp [Q]
    unfold blockRatio
    exact div_pos (Polymer.smoothedP2Plane_pos β (t (lo - 1)) (t hi) 0 ω)
      (Finset.prod_pos fun i hiI => blockMass_pos β t i ω)
  have hQmeas : Measurable Q := by
    dsimp [Q, blockRatio]
    have hprod : Measurable (fun ω => ∏ i ∈ I, blockMass β t i ω) := by
      apply Finset.measurable_prod
      intro i hiI
      exact (measurable_blockMass β t i).mono
        (Gaussian.disorderBlock_le _ _) le_rfl
    exact (Polymer.measurable_smoothedP2Plane β (t (lo - 1)) (t hi) 0).div hprod
  have hVpos (ω : Disorder) : 0 < V ω := by
    dsimp [V]
    exact div_pos (Polymer.smoothedP2Plane_pos β (t lo0) N 0 ω)
      (Polymer.smoothedP2Plane_pos β (t lo0) (t hi) 0 ω)
  have hVmeas : Measurable V := by
    dsimp [V]
    exact (Polymer.measurable_smoothedP2Plane β (t lo0) N 0).div
      (Polymer.measurable_smoothedP2Plane β (t lo0) (t hi) 0)
  have hlogQmeas : Measurable (fun ω => Real.log (Q ω)) := Real.measurable_log.comp hQmeas
  have hlogVmeas : Measurable (fun ω => Real.log (V ω)) := Real.measurable_log.comp hVmeas
  have hQbound (ω : Disorder) (hω : ω ∈ G) : |Real.log (Q ω)| ≤ Real.log 2 := by
    have hclose : |Q ω - 1| ≤ 1 / 2 := by simpa [G, Q, profileGoodSet] using hω.2
    exact abs_log_le_log_two_of_abs_sub_one_le (hQpos ω) hclose
  have hDlogSmall : Real.log 2 < δ * s / 3 := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hDsmall' : D < s ^ 2 := by rw [hsSq]; exact hDsmall
    have hsq : (3 * Real.log 2 / δ) ^ 2 < s ^ 2 := lt_of_le_of_lt hDlog2 hDsmall'
    have hroot : 3 * Real.log 2 / δ < s := (sq_lt_sq₀ (by positivity) hspos.le).mp hsq
    have hmul := mul_lt_mul_of_pos_left hroot hδ
    have hraw : 3 * Real.log 2 < δ * s := by
      have heq : δ * (3 * Real.log 2 / δ) = 3 * Real.log 2 := by
        field_simp [ne_of_gt hδ]
      rw [heq] at hmul
      exact hmul
    calc
      Real.log 2 = (3 * Real.log 2) / 3 := by ring
      _ < (δ * s) / 3 := div_lt_div_of_pos_right hraw (by norm_num)
      _ = δ * s / 3 := by ring
  have hQtail : (disorderLaw {ω | δ * s / 3 < |Real.log (Q ω)|}).toReal ≤ CPE' / ℓ := by
    have hsubset : {ω | δ * s / 3 < |Real.log (Q ω)|} ⊆ Gᶜ := by
      intro ω hω hG
      have hbound := hQbound ω hG
      have : |Real.log (Q ω)| ≤ δ * s / 3 := hbound.trans hDlogSmall.le
      exact (not_lt_of_ge this) hω
    have hmeasure : disorderLaw {ω | δ * s / 3 < |Real.log (Q ω)|} ≤
        disorderLaw Gᶜ := measure_mono hsubset
    exact ENNReal.toReal_mono (measure_ne_top disorderLaw _) hmeasure |>.trans hGbad
  have hVtail : (disorderLaw {ω | δ * s / 3 < |Real.log (V ω)|}).toReal ≤
      CTail' / ℓ + (CTail' * ℓ + 1) * Real.exp (-(δ * s / 3)) ∧
      (CTail' * ℓ + 1) * Real.exp (-(δ * s / 3)) ≤ δ / 3 := by
    have hthreshold : 0 < δ * s / 3 := by positivity
    have hTail := hTailN ϑ hϑmem lo0 ℓ hℓTail (by dsimp [lo0, K]; omega)
      (δ * s / 3) (le_of_lt hthreshold)
    have hminus : (disorderLaw {ω | Real.log (V ω) < -(δ * s / 3)}).toReal ≤
        CTail' / ℓ + CTail' * ℓ * Real.exp (-(δ * s / 3)) := by
      have hC : CTail ≤ CTail' := hCTaile
      have htail' : (disorderLaw {ω | Real.log (V ω) < -(δ * s / 3)}).toReal ≤
          CTail / ℓ + CTail * ℓ * Real.exp (-(δ * s / 3)) := by
        simpa only [V, β, t, K, hi, Pi.div_apply] using hTail.1
      exact htail'.trans
        (add_le_add (div_le_div_of_nonneg_right hC (by positivity))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC (by exact_mod_cast (Nat.zero_le ℓ)))
            (Real.exp_nonneg _)))
    have hplus : (disorderLaw {ω | δ * s / 3 < Real.log (V ω)}).toReal ≤
        Real.exp (-(δ * s / 3)) := by
      simpa only [V, β, t, K, hi, Pi.div_apply] using hTail.2
    have hDsmall' : D < s ^ 2 := by rw [hsSq]; exact hDsmall
    have hscale : ((3 / δ) * (Real.log Eexp + 1)) ^ 2 < s ^ 2 :=
      lt_of_le_of_lt hDexp hDsmall'
    have hEge : 1 ≤ Eexp := by dsimp [Eexp]; exact le_max_left _ _
    have hA : 3 * (CTail' * ℓ + 1) / δ ≤ Eexp := by
      exact le_max_right (1 : ℝ) (3 * (CTail' * ℓ + 1) / δ)
    have hBnonneg : 0 ≤ CTail' * ℓ + 1 :=
      add_nonneg (mul_nonneg hCTailpos.le (by exact_mod_cast (Nat.zero_le ℓ))) (by norm_num)
    have hcombine : CTail' * ℓ * Real.exp (-(δ * s / 3)) +
        Real.exp (-(δ * s / 3)) = (CTail' * ℓ + 1) * Real.exp (-(δ * s / 3)) := by ring
    exact measure_abs_log_tail_with_exp_bound (μ := disorderLaw) (X := V)
      (δ := δ) (s := s) (E := Eexp) (u := CTail' / ℓ)
      (v := CTail' * ℓ * Real.exp (-(δ * s / 3)))
      (w := Real.exp (-(δ * s / 3))) (B := CTail' * ℓ + 1)
      hδ hspos hEge hscale hA hBnonneg hminus hplus hcombine
  let Zbase : Disorder → ℝ := fun ω => Zrem ω + Real.log (Q ω) + Real.log (V ω)
  have hZbaseMeas : Measurable Zbase := by
    dsimp [Zbase]
    exact hZremMeas.add hlogQmeas |>.add hlogVmeas
  have hZbaseTail : (disorderLaw {ω | δ * s < |Zbase ω|}).toReal ≤ δ := by
    have hsum : CPE' / ℓ + CTail' / ℓ ≤ δ / 3 := by
      calc
        _ = (CPE' + CTail') / ℓ := by rw [← add_div]
        _ ≤ δ / 3 := hbaseTail
    change (disorderLaw {ω | δ * s <
      |Zrem ω + Real.log (Q ω) + Real.log (V ω)|}).toReal ≤ δ
    exact measure_abs_sum_three_small (μ := disorderLaw)
      (X := Zrem) (Y := fun ω => Real.log (Q ω)) (Z := fun ω => Real.log (V ω))
      hZremTail hQtail hVtail.1 hsum hVtail.2
  let S : Disorder → ℝ := Xsum + Rsum
  have hS (ω : Disorder) : S ω = Xsum ω + Rsum ω := rfl
  have hSlogs (ω : Disorder) : S ω =
      ∑ i ∈ I, Real.log (blockMass β t i ω) := by
    change (∑ i ∈ I.attach, X i ω) + ∑ i ∈ I.attach, R i ω =
      ∑ i ∈ I, Real.log (blockMass β t i ω)
    rw [← Finset.sum_attach I, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hiI
    dsimp [X, R]
    ring
  have hXsumMean : ∫ ω, Xsum ω ∂disorderLaw = 0 := by
    dsimp [Xsum]
    rw [integral_finsetSum _ (fun i _ => (hXmem i).integrable (by norm_num))]
    simp [hXmean]
  have hSmean : ∫ ω, S ω ∂disorderLaw = ∫ ω, Rsum ω ∂disorderLaw := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hS), integral_add
      (hXsumMem.integrable (by norm_num)) (hRsumMem.integrable (by norm_num)), hXsumMean]
    simp
  let Pmass : Disorder → ℝ := fun ω => ∏ i ∈ I, blockMass β t i ω
  have hPpos (ω : Disorder) : 0 < Pmass ω := by
    dsimp [Pmass]
    exact Finset.prod_pos fun i hi => blockMass_pos β t i ω
  have hcoarse (ω : Disorder) : smoothedP2Plane β (t lo0) (t hi) 0 ω = Pmass ω * Q ω := by
    have h := smoothedP2Plane_eq_prod_blockMass_mul_blockRatio β t lo hi ω
    simpa [Pmass, Q, hloPred] using h
  have hratioFull (ω : Disorder) : smoothedP2Plane β (t lo0) N 0 ω =
      smoothedP2Plane β (t lo0) (t hi) 0 ω * V ω := by
    dsimp [V]
    field_simp [ne_of_gt (Polymer.smoothedP2Plane_pos β (t lo0) (t hi) 0 ω)]
  have hfull (ω : Disorder) :
      smoothedP2Plane (criticalBeta ϑ N) (evenCeil (ε ^ 2 * N)) N 0 ω =
        Pmass ω * Q ω * V ω := by
    calc
      _ = smoothedP2Plane β (t lo0) N 0 ω := by
        rw [← hgammaGridLeft]
      _ = smoothedP2Plane β (t lo0) (t hi) 0 ω * V ω := hratioFull ω
      _ = Pmass ω * Q ω * V ω := by rw [hcoarse]
  have hlogP (ω : Disorder) : Real.log (Pmass ω) =
      ∑ i ∈ I, Real.log (blockMass β t i ω) := by
    dsimp [Pmass]
    rw [Real.log_prod]
    intro i hiI
    exact (blockMass_pos β t i ω).ne'
  have hlogFull (ω : Disorder) :
      Real.log (smoothedP2Plane (criticalBeta ϑ N) (evenCeil (ε ^ 2 * N)) N 0 ω) =
        S ω + Real.log (Q ω) + Real.log (V ω) := by
    rw [hfull ω, Real.log_mul (mul_ne_zero (hPpos ω).ne' (hQpos ω).ne') (hVpos ω).ne',
      Real.log_mul (hPpos ω).ne' (hQpos ω).ne', hlogP ω]
    rw [← hSlogs]
  let Lmass : Disorder → ℝ := latticeLogMass ϑ ε N
  have hLmem : MemLp Lmass 2 disorderLaw := by
    change MemLp (latticeLogMass ϑ ε N) 2 disorderLaw
    unfold latticeLogMass
    exact memLp_log_smoothedP2Plane_critical ϑ N (evenCeil (ε ^ 2 * N)) 0
  have hZbaseEq (ω : Disorder) : Zbase ω =
      (Lmass ω - Xsum ω) - ∫ ω', Rsum ω' ∂disorderLaw := by
    change Rsum ω - (∫ ω', Rsum ω' ∂disorderLaw) + Real.log (Q ω) + Real.log (V ω) =
      (Real.log (smoothedP2Plane (criticalBeta ϑ N)
        (evenCeil (ε ^ 2 * N)) N 0 ω) - Xsum ω) - ∫ ω', Rsum ω' ∂disorderLaw
    exact zbase_eq_of_log_decomp (fun ω => smoothedP2Plane (criticalBeta ϑ N)
      (evenCeil (ε ^ 2 * N)) N 0 ω) S Q V Xsum Rsum
      (∫ ω', Rsum ω' ∂disorderLaw) hS hlogFull ω
  have hZbaseMem : MemLp Zbase 2 disorderLaw := by
    have hEq : Zbase = fun ω => (Lmass ω - Xsum ω) - ∫ ω', Rsum ω' ∂disorderLaw :=
      funext hZbaseEq
    rw [hEq]
    exact (hLmem.sub hXsumMem).sub
      (memLp_const (∫ ω', Rsum ω' ∂disorderLaw))
  have hScenter (ω : Disorder) :
      (S ω - ∫ ω', S ω' ∂disorderLaw) / s = (Xsum ω + Zrem ω) / s := by
    rw [hS ω, hSmean]
    dsimp [Zrem]
    ring
  let m : ℕ := evenCeil (ε ^ 2 * N)
  have hmEq : m = t lo0 := by
    dsimp [m, lo0]
    exact hgammaGridLeft.symm
  have hKpos : 0 < K := by
    have hbasepos : 0 < 2 * J + ℓ + 1 := Nat.zero_lt_succ _
    exact Nat.lt_of_lt_of_le hbasepos hKbound
  have hKtime : t K = N := by
    change Critical2DKPZ.blockTime N γ (blockCount N γ) = N
    have hKpos' : 0 < blockCount N γ := by
      exact hKpos
    exact blockTime_count_eq hKpos'
  have hlo0K : lo0 ≤ K := by
    dsimp [lo0]
    exact Nat.sub_le _ _
  have hmN : m ≤ N := by
    calc
      m = t lo0 := hmEq
      _ ≤ t K := htimeMono hlo0K
      _ = N := hKtime
  have hstartMul : 1 < ε ^ 2 * (N : ℝ) := by
    exact one_lt_sq_mul_of_div_bound hε hNstartN
  have hmLower : ε ^ 2 * (N : ℝ) ≤ (m : ℝ) := by
    dsimp [m]
    exact Critical2DKPZ.le_evenCeil _
  have hmOne : 1 ≤ m := by
    exact_mod_cast (le_of_lt (lt_of_lt_of_le hstartMul hmLower))
  have hsecondRaw := secondMoment_fixedN (A := |ϑ|) (C := C₂) ϑ hC₂N hϑmem hmN
  have hratioPos : 0 < (N : ℝ) / (max m 1 : ℕ) := by
    apply div_pos (natCast_pos_of_div_bound hε hNstartN)
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right m 1))
  have hratioLe : (N : ℝ) / (max m 1 : ℕ) ≤ (ε ^ 2)⁻¹ :=
    natRatio_le_inv_sq hε hmOne hmLower
  let L : ℝ := Real.log ε⁻¹
  have hLpos : 0 < L := by
    dsimp [L]
    exact log_inv_pos_of_unit_interval hε hε1
  have hlogRatio : Real.log ((N : ℝ) / (max m 1 : ℕ)) ≤ 2 * L := by
    dsimp [L]
    exact log_le_two_log_inv_of_ratio hratioPos hratioLe
  have hratioGe : 1 ≤ (N : ℝ) / (max m 1 : ℕ) := natRatio_ge_one hmOne hmN
  have hlogRatioNonneg : 0 ≤ Real.log ((N : ℝ) / (max m 1 : ℕ)) :=
    Real.log_nonneg hratioGe
  have hfactorNonneg : 0 ≤ 1 + Real.log ((N : ℝ) / (max m 1 : ℕ)) :=
    add_nonneg zero_le_one hlogRatioNonneg
  have hfactorBound : 1 + Real.log ((N : ℝ) / (max m 1 : ℕ)) ≤ 1 + 2 * L :=
    add_le_add_right hlogRatio 1
  have hC₂' : C₂ ≤ |C₂| + 1 :=
    (le_abs_self C₂).trans (le_add_of_nonneg_right zero_le_one)
  have hmassSecondInt :
      Integrable (fun ω => smoothedP2Plane β m N 0 ω ^ 2) disorderLaw :=
    (smoothedP2Plane_memLp_two β m N).integrable_sq
  have hraw :
      ∫ ω, smoothedP2Plane β m N 0 ω ^ 2 ∂disorderLaw ≤
        C₂ * (1 + Real.log ((N : ℝ) / (max m 1 : ℕ))) := by
    simpa only [β, one_mul] using hsecondRaw
  have hLlarge : 2 * |C₂| + 3 < L :=
    secondMoment_scale_lt_of_bounds C₂ D L hLpos hDsecond hDsmall
  have hmassSecondData := integral_sq_bound_of_secondMoment disorderLaw
    (fun ω => smoothedP2Plane β m N 0 ω) C₂ L
    (Real.log ((N : ℝ) / (max m 1 : ℕ))) hmassSecondInt hraw hC₂'
    hfactorNonneg hfactorBound hLlarge
  have hmassSecond := hmassSecondData.2
  have hmassSquareOne : 1 ≤
      ∫ ω, smoothedP2Plane β m N 0 ω ^ 2 ∂disorderLaw := by
    have hmem := smoothedP2Plane_memLp_two β m N
    have hv := ProbabilityTheory.variance_nonneg
      (smoothedP2Plane β m N 0) disorderLaw
    rw [ProbabilityTheory.variance_eq_sub hmem, Polymer.integral_smoothedP2Plane] at hv
    norm_num at hv
    linarith only [hv]
  have hvarLog := variance_log_smoothedP2Plane_le
    (β := criticalBeta ϑ N) (by dsimp [criticalBeta]; positivity) m N 0
  have hvarLogMass : Var[Lmass; disorderLaw] ≤ 2 * Real.log
      (∫ ω, smoothedP2Plane β m N 0 ω ^ 2 ∂disorderLaw) := by
    change Var[fun ω => Real.log (smoothedP2Plane
      (criticalBeta ϑ N) m N 0 ω); disorderLaw] ≤
      2 * Real.log (∫ ω, smoothedP2Plane
        (criticalBeta ϑ N) m N 0 ω ^ 2 ∂disorderLaw)
    exact hvarLog.2
  have hvarL : Var[Lmass; disorderLaw] ≤ 4 * s ^ 2 := by
    have hlogBound := Real.log_le_log (zero_lt_one.trans_le hmassSquareOne) hmassSecond
    calc
      Var[Lmass; disorderLaw] ≤ 2 * Real.log
          (∫ ω, smoothedP2Plane β m N 0 ω ^ 2 ∂disorderLaw) := hvarLogMass
      _ ≤ 2 * Real.log (L ^ 2) := mul_le_mul_of_nonneg_left hlogBound (by norm_num)
      _ = 4 * s ^ 2 := by rw [Real.log_pow]; rw [← hsSq]; ring
  let U0 : Disorder → ℝ := fun ω => (Lmass ω - ∫ ω', S ω' ∂disorderLaw) / s
  have hU0mem : MemLp U0 2 disorderLaw := by
    change MemLp (fun ω => (Lmass ω - ∫ ω', S ω' ∂disorderLaw) * s⁻¹)
      2 disorderLaw
    exact (hLmem.sub (memLp_const (∫ ω', S ω' ∂disorderLaw))).mul_const s⁻¹
  have hU0varEq : Var[U0; disorderLaw] = (s⁻¹) ^ 2 * Var[Lmass; disorderLaw] := by
    have hEq : U0 = fun ω => s⁻¹ * (Lmass ω - ∫ ω', S ω' ∂disorderLaw) := by
      funext ω
      dsimp [U0]
      ring
    rw [hEq, ProbabilityTheory.variance_const_mul,
      ProbabilityTheory.variance_sub_const hLmem.aestronglyMeasurable]
  have hU0var : Var[U0; disorderLaw] ≤ 4 := by
    calc
      Var[U0; disorderLaw] = (s⁻¹) ^ 2 * Var[Lmass; disorderLaw] := hU0varEq
      _ ≤ (s⁻¹) ^ 2 * (4 * s ^ 2) :=
        mul_le_mul_of_nonneg_left hvarL (sq_nonneg (s⁻¹))
      _ = 4 := by field_simp [ne_of_gt hspos]
  have hU0identity (ω : Disorder) : U0 ω = (Xsum ω + Zbase ω) / s := by
    dsimp [U0, Lmass, latticeLogMass, Zbase, Zrem]
    rw [hSmean, hlogFull ω, hS ω]
    ring
  have hU0fun : (fun ω => U0 ω) = fun ω => (Xsum ω + Zbase ω) / s :=
    funext hU0identity
  have hU0int : ∫ ω, U0 ω ∂disorderLaw =
      (∫ ω, Zbase ω ∂disorderLaw) / s := by
    rw [hU0fun, integral_div,
      integral_add (hXsumMem.integrable (by norm_num)) (hZbaseMem.integrable (by norm_num)),
      hXsumMean]
    simp
  have hvarInputδ :
      |(∑ i ∈ I.attach, ∫ ω, X i ω ^ 2 ∂disorderLaw) - s ^ 2| ≤ δ * s ^ 2 := by
    simpa [hsSq] using hvarGrid.trans (by simpa [hsSq] using hCvarSq)
  have hvarInput₁ :
      |(∑ i ∈ I.attach, ∫ ω, X i ω ^ 2 ∂disorderLaw) - s ^ 2| ≤ δ₁ * s ^ 2 := by
    exact hvarInputδ.trans (mul_le_mul_of_nonneg_right hδle₁ (sq_nonneg s))
  have hvarInput₂ :
      |(∑ i ∈ I.attach, ∫ ω, X i ω ^ 2 ∂disorderLaw) - s ^ 2| ≤ δ₂ * s ^ 2 := by
    exact hvarInputδ.trans (mul_le_mul_of_nonneg_right hδle₂ (sq_nonneg s))
  have hthird₁ :
      ∑ i ∈ I.attach, ∫ ω, |X i ω| ^ 3 ∂disorderLaw ≤ δ₁ * s ^ 3 := by
    exact hthirdBound.trans (mul_le_mul_of_nonneg_right hδle₁ (by positivity))
  have hthird₂ :
      ∑ i ∈ I.attach, ∫ ω, |X i ω| ^ 3 ∂disorderLaw ≤ δ₂ * s ^ 3 := by
    exact hthirdBound.trans (mul_le_mul_of_nonneg_right hδle₂ (by positivity))
  have htail₁ :
      (disorderLaw {ω | δ₁ * s < |Zbase ω|}).toReal ≤ δ₁ := by
    have hsubset : {ω | δ₁ * s < |Zbase ω|} ⊆ {ω | δ * s < |Zbase ω|} := by
      intro ω hω
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hδle₁ hspos.le) hω
    exact measure_toReal_mono_of_subset disorderLaw hsubset hZbaseTail
      hδle₁
  have htail₂ :
      (disorderLaw {ω | δ₂ * s < |Zbase ω|}).toReal ≤ δ₂ := by
    have hsubset : {ω | δ₂ * s < |Zbase ω|} ⊆ {ω | δ * s < |Zbase ω|} := by
      intro ω hω
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hδle₂ hspos.le) hω
    exact measure_toReal_mono_of_subset disorderLaw hsubset hZbaseTail
      hδle₂
  have hCLT₁ := hLyap₁ (μ := disorderLaw) (I := I.attach) (X := X)
    (Z := Zbase) (s := s) hspos hXInd hXmeas hZbaseMeas
    (fun i _ => hXmem i) (fun i _ => hXmean i) hvarInput₁ hthird₁ htail₁
  have hCLT₂ := hLyap₂ (μ := disorderLaw) (I := I.attach) (X := X)
    (Z := Zbase) (s := s) hspos hXInd hXmeas hZbaseMeas
    (fun i _ => hXmem i) (fun i _ => hXmean i) hvarInput₂ hthird₂ htail₂
  have htest₁ :
      |∫ ω, h₁ (U0 ω) ∂disorderLaw - ∫ y, h₁ y ∂gaussianReal 0 1| ≤ δtest := by
    have hEq : (fun ω => h₁ (U0 ω)) =
        fun ω => h₁ ((Xsum ω + Zbase ω) / s) := by
      funext ω
      rw [hU0identity]
    rw [hEq]
    simpa [Xsum] using hCLT₁
  have htest₂ :
      |∫ ω, h₂ (U0 ω) ∂disorderLaw - ∫ y, h₂ y ∂gaussianReal 0 1| ≤ δtest := by
    have hEq : (fun ω => h₂ (U0 ω)) =
        fun ω => h₂ ((Xsum ω + Zbase ω) / s) := by
      funext ω
      rw [hU0identity]
    rw [hEq]
    simpa [Xsum] using hCLT₂
  have hU0mean : |∫ ω, U0 ω ∂disorderLaw| ≤ δh / 2 :=
    hcenter disorderLaw U0 hU0mem hU0var htest₁ htest₂
  have hZbaseMean :
      |∫ ω, Zbase ω ∂disorderLaw| ≤ (δh / 2) * s := by
    have h := hU0mean
    rw [hU0int, abs_div, abs_of_pos hspos] at h
    exact (div_le_iff₀ hspos).mp h
  let Zcenter : Disorder → ℝ := fun ω => Zbase ω - ∫ ω', Zbase ω' ∂disorderLaw
  have hZcenterMeas : Measurable Zcenter := by
    dsimp [Zcenter]
    exact hZbaseMeas.sub measurable_const
  have hZcenterTail :
      (disorderLaw {ω | δh * s < |Zcenter ω|}).toReal ≤ δh := by
    have hsubset : {ω | δh * s < |Zcenter ω|} ⊆
        {ω | δ * s < |Zbase ω|} := by
      intro ω hω
      have htri : |Zcenter ω| ≤ |Zbase ω| + |∫ ω', Zbase ω' ∂disorderLaw| := by
        have hEq : Zcenter ω = Zbase ω + -(∫ ω', Zbase ω' ∂disorderLaw) := by
          dsimp [Zcenter]
          ring
        calc
          |Zcenter ω| = |Zbase ω + -(∫ ω', Zbase ω' ∂disorderLaw)| := by rw [hEq]
          _ ≤ |Zbase ω| + |∫ ω', Zbase ω' ∂disorderLaw| := by
            simpa only [abs_neg] using abs_add_le (Zbase ω)
              (-(∫ ω', Zbase ω' ∂disorderLaw))
      have hbaseLarge : δh * s / 2 < |Zbase ω| := by
        exact centered_tail_abs_base hω htri hZbaseMean
      have hδlarge : δ * s ≤ δh * s / 2 := by
        have hmul := mul_le_mul_of_nonneg_right hδleH hspos.le
        calc
          δ * s ≤ (δh / 2) * s := hmul
          _ = δh * s / 2 := by ring
      exact lt_of_le_of_lt hδlarge hbaseLarge
    exact measure_toReal_mono_of_subset disorderLaw hsubset hZbaseTail
      (le_trans hδleH (half_le_self hδh.le))
  have hvarInputMain :
      |(∑ i ∈ I.attach, ∫ ω, X i ω ^ 2 ∂disorderLaw) - s ^ 2| ≤ δh * s ^ 2 := by
    exact hvarInputδ.trans (mul_le_mul_of_nonneg_right (hδleH.trans (half_le_self hδh.le)) (sq_nonneg s))
  have hthirdMain :
      ∑ i ∈ I.attach, ∫ ω, |X i ω| ^ 3 ∂disorderLaw ≤ δh * s ^ 3 := by
    exact hthirdBound.trans
      (mul_le_mul_of_nonneg_right (hδleH.trans (half_le_self hδh.le)) (by positivity))
  have hCLT := hLyaph (μ := disorderLaw) (I := I.attach) (X := X)
    (Z := Zcenter) (s := s) hspos hXInd hXmeas hZcenterMeas
    (fun i _ => hXmem i) (fun i _ => hXmean i) hvarInputMain hthirdMain hZcenterTail
  have hLdecomp (ω : Disorder) :
      Lmass ω = Xsum ω + Zbase ω + ∫ ω', Rsum ω' ∂disorderLaw := by
    rw [hZbaseEq ω]
    ring
  have hLmean : ∫ ω, Lmass ω ∂disorderLaw =
      (∫ ω, Zbase ω ∂disorderLaw) + ∫ ω', Rsum ω' ∂disorderLaw := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hLdecomp)]
    have hXint := hXsumMem.integrable (by norm_num)
    have hZint := hZbaseMem.integrable (by norm_num)
    let c : ℝ := ∫ ω', Rsum ω' ∂disorderLaw
    change ∫ ω, ((Xsum + Zbase) ω) + (fun _ : Disorder => c) ω
        ∂disorderLaw = _
    rw [integral_add (hXint.add hZint) (integrable_const c)]
    change (∫ ω, Xsum ω + Zbase ω ∂disorderLaw) +
        ∫ ω, c ∂disorderLaw = _
    rw [integral_add hXint hZint, hXsumMean]
    simp [c]
  have hfullcenter (ω : Disorder) :
      (Lmass ω - ∫ ω', Lmass ω' ∂disorderLaw) / s = (Xsum ω + Zcenter ω) / s := by
    rw [hLdecomp ω, hLmean]
    dsimp [Zcenter]
    ring
  have hfinal :
      |∫ ω, h ((Lmass ω - ∫ ω', Lmass ω' ∂disorderLaw) / s) ∂disorderLaw -
          ∫ y, h y ∂gaussianReal 0 1| ≤ η / 2 := by
    have hEq : (fun ω => h ((Lmass ω - ∫ ω', Lmass ω' ∂disorderLaw) / s)) =
        fun ω => h ((Xsum ω + Zcenter ω) / s) := by
      funext ω
      rw [hfullcenter]
    rw [hEq]
    simpa [Xsum] using hCLT
  simpa [Lmass, s, latticeLogMass] using hfinal.trans (half_le_self hη.le)

end Critical2DKPZ.LogNormality

end
