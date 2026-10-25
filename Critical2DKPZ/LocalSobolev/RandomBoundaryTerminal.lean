/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.LatticeCovarianceBase
public import Critical2DKPZ.SHF.Positivity.FinitePathEhrhard
public import Critical2DKPZ.Smoothing.Decomposition
public import Critical2DKPZ.PolymerCalculus.PathMoments
public import Critical2DKPZ.Polymer.Replica
import Mathlib.Tactic

/-! # One-step logarithmic estimates with terminal weights -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.LocalSobolev

/-- For a normalized finite initial profile and a positive terminal weight, one disorder slice
changes the logarithmic mass from its zero-noise value by a quantity with a uniform second-moment
bound. -/
theorem integral_sq_log_profileP2Fun_oneStep_terminal_ratio_le (β : ℝ) (n : ℕ)
    (A : Finset Site) (η f : Site → ℝ)
    (hηA : ∀ w ∉ A, η w = 0) (hη0 : ∀ w, 0 ≤ η w)
    (hη1 : ∑ w ∈ A, η w = 1) (hf : ∀ z, 0 < f z) :
    Integrable (fun ω =>
      (Real.log (profileP2Fun β n (n + 1) η f ω) -
        Real.log (profileP2Fun 0 n (n + 1) η f ω)) ^ 2) disorderLaw ∧
    (∫ ω,
      (Real.log (profileP2Fun β n (n + 1) η f ω) -
        Real.log (profileP2Fun 0 n (n + 1) η f ω)) ^ 2 ∂disorderLaw) ≤
      β ^ 2 + β ^ 4 / 4 := by
  classical
  let Starts := {w // w ∈ A}
  let w : Starts → Site := fun y => y.1
  let c : Starts × (Fin 1 → Fin 4) → ℝ := fun p =>
    η p.1.1 * f (walkPosition p.1.1 p.2 1) * ((4 : ℝ)⁻¹)
  let c₀ : ℝ := profileP2Fun 0 n (n + 1) η f (fun _ => 0)
  let cNorm : Starts × (Fin 1 → Fin 4) → ℝ := fun p => c p / c₀
  have hc (p : Starts × (Fin 1 → Fin 4)) : 0 ≤ c p := by
    dsimp [c]
    exact mul_nonneg (mul_nonneg (hη0 p.1.1) (hf _).le) (by positivity)
  have hηpos : ∃ y ∈ A, 0 < η y := by
    have hsum : 0 < ∑ y ∈ A, η y := by rw [hη1]; norm_num
    exact (Finset.sum_pos_iff_of_nonneg (fun y hy => hη0 y)).mp hsum
  have hc₀pos : 0 < c₀ := by
    have hpos := Critical2DKPZ.Smoothing.profileP2Fun_pos_terminal
      0 n (n + 1) η f A hηA hη0 hηpos hf (fun _ => 0)
    simpa only [c₀] using hpos
  have hc₀ : c₀ ≠ 0 := hc₀pos.ne'
  have hprofile (γ : ℝ) (ω : Disorder) :
      profileP2Fun γ n (n + 1) η f ω =
        PolymerCalculus.finitePathMass γ n 1 w c ω := by
    have h := Critical2DKPZ.SHF.Positivity.profileP2Fun_eq_finitePathMass_terminal
      γ n (n + 1) η f A hηA ω
    have hn : n + 1 - n = 1 := by omega
    rw [hn] at h
    simpa only [w, c, pow_one] using h
  have hbaseEq : c₀ = ∑ p, c p := by
    have hprof0 := hprofile 0 (fun _ => 0)
    dsimp [c₀]
    rw [hprof0]
    simp [PolymerCalculus.finitePathMass, PolymerCalculus.pathEnergy, c]
  have hcNorm : ∀ p, 0 ≤ cNorm p := by
    intro p
    dsimp [cNorm]
    exact div_nonneg (hc p) hc₀pos.le
  have hcNormSum : ∑ p, cNorm p = 1 := by
    calc
      _ = (∑ p, c p) / c₀ := by
        simp only [cNorm]
        rw [Finset.sum_div]
      _ = 1 := by rw [← hbaseEq]; exact div_self hc₀
  have hcNormPos : ∃ p, 0 < cNorm p := by
    have hsum : 0 < ∑ p, cNorm p := by rw [hcNormSum]; norm_num
    simpa only [Finset.mem_univ, true_and] using
      (Finset.sum_pos_iff_of_nonneg (fun p hp => hcNorm p)).mp hsum
  have hscale (ω : Disorder) :
      PolymerCalculus.finitePathMass β n 1 w c ω =
        c₀ * PolymerCalculus.finitePathMass β n 1 w cNorm ω := by
    unfold PolymerCalculus.finitePathMass cNorm
    calc
      _ = ∑ p, c p * Real.exp (PolymerCalculus.pathEnergy β n (w p.1) p.2 ω) := rfl
      _ = c₀ * ∑ p, (c p / c₀) *
          Real.exp (PolymerCalculus.pathEnergy β n (w p.1) p.2 ω) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro p hp
            field_simp [hc₀]
      _ = _ := rfl
  let F : Disorder → ℝ := fun ω =>
    Real.log (PolymerCalculus.finitePathMass β n 1 w cNorm ω)
  have hFpos (ω : Disorder) : 0 < PolymerCalculus.finitePathMass β n 1 w cNorm ω :=
    PolymerCalculus.finitePathMass_pos β n 1 w hcNorm hcNormPos ω
  have hFmem : MemLp F 2 disorderLaw := by
    dsimp [F]
    exact PolymerCalculus.memLp_log_finitePathMass β n 1 w hcNorm hcNormPos 2
  have hFmeas : Measurable F := by
    dsimp [F]
    exact PolymerCalculus.measurable_log_finitePathMass β n 1 w cNorm
  have hF2int : Integrable (fun ω => F ω ^ 2) disorderLaw := hFmem.integrable_sq
  have hFconv := OnePoint.logMGFRatio_finitePathMass_convex β n 1 w hcNorm hcNormPos
  have hK := PolymerCalculus.finitePathMass_bounds_of_logMGFRatio_convex
    β n 1 w hcNorm hcNormPos hcNormSum hFconv
  have hsecond : (∫ ω, PolymerCalculus.finitePathMass β n 1 w cNorm ω ^ 2
      ∂disorderLaw) ≤ Real.exp (β ^ 2) := by
    have hpairInt (p q : Starts × (Fin 1 → Fin 4)) :
        Integrable (fun ω => Polymer.pathWeight β n (w p.1) p.2 ω *
          Polymer.pathWeight β n (w q.1) q.2 ω) disorderLaw :=
      memLp_one_iff_integrable.mp (Polymer.memLp_mul_double 1
        (by simpa only [mul_one] using
          Polymer.memLp_pathWeight β n (w p.1) p.2 2 (by norm_num))
        (by simpa only [mul_one] using
          Polymer.memLp_pathWeight β n (w q.1) q.2 2 (by norm_num)))
    have hExpand (ω : Disorder) :
        PolymerCalculus.finitePathMass β n 1 w cNorm ω ^ 2 =
          ∑ p, ∑ q, (cNorm p * cNorm q) *
            (Polymer.pathWeight β n (w p.1) p.2 ω *
              Polymer.pathWeight β n (w q.1) q.2 ω) := by
      simp only [PolymerCalculus.finitePathMass, pow_two]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      change cNorm p * Polymer.pathWeight β n (w p.1) p.2 ω *
        (cNorm q * Polymer.pathWeight β n (w q.1) q.2 ω) = _
      ring
    rw [show (fun ω => PolymerCalculus.finitePathMass β n 1 w cNorm ω ^ 2) =
      fun ω => ∑ p, ∑ q, (cNorm p * cNorm q) *
        (Polymer.pathWeight β n (w p.1) p.2 ω *
          Polymer.pathWeight β n (w q.1) q.2 ω) by funext ω; exact hExpand ω]
    have hterm (p q : Starts × (Fin 1 → Fin 4)) :
        (cNorm p * cNorm q) *
            ∏ j ∈ Finset.Icc 1 1,
              (if walkPosition (w p.1) p.2 j = walkPosition (w q.1) q.2 j
                then Real.exp (β ^ 2) else 1) ≤
          (cNorm p * cNorm q) * Real.exp (β ^ 2) := by
      have hprod :
          ∏ j ∈ Finset.Icc 1 1,
              (if walkPosition (w p.1) p.2 j = walkPosition (w q.1) q.2 j
                then Real.exp (β ^ 2) else 1) ≤ Real.exp (β ^ 2) := by
        simp only [Finset.Icc_self, Finset.prod_singleton]
        split_ifs
        · exact le_rfl
        · exact Real.one_le_exp (sq_nonneg β)
      exact mul_le_mul_of_nonneg_left hprod (mul_nonneg (hcNorm p) (hcNorm q))
    calc
      _ = ∑ p, ∑ q, (cNorm p * cNorm q) *
            ∏ j ∈ Finset.Icc 1 1,
              (if walkPosition (w p.1) p.2 j = walkPosition (w q.1) q.2 j
                then Real.exp (β ^ 2) else 1) := by
        rw [integral_finsetSum _ (fun p hp =>
          integrable_finsetSum _ (fun q hq => (hpairInt p q).const_mul _))]
        apply Finset.sum_congr rfl
        intro p hp
        rw [integral_finsetSum _ (fun q hq => (hpairInt p q).const_mul _)]
        apply Finset.sum_congr rfl
        intro q hq
        rw [integral_const_mul, Polymer.integral_pathWeight_mul]
      _ ≤ ∑ p, ∑ q, (cNorm p * cNorm q) * Real.exp (β ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact hterm p q
      _ = Real.exp (β ^ 2) := by
        calc
          _ = ∑ p, cNorm p * (∑ q, cNorm q * Real.exp (β ^ 2)) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            ring
          _ = ∑ p, cNorm p * ((∑ q, cNorm q) * Real.exp (β ^ 2)) := by
            congr 1
            rw [Finset.sum_mul]
          _ = Real.exp (β ^ 2) := by
            rw [← Finset.sum_mul]
            simp [hcNormSum]
  have hmgf : mgf F disorderLaw 2 =
      ∫ ω, PolymerCalculus.finitePathMass β n 1 w cNorm ω ^ 2 ∂disorderLaw := by
    calc
      _ = ∫ ω, PolymerCalculus.finitePathMass β n 1 w cNorm ω ^ (2 : ℝ) ∂disorderLaw :=
        OnePoint.mgf_log_eq_integral_rpow hFpos 2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact Real.rpow_natCast _ 2
  have hmgfpos : 0 < mgf F disorderLaw 2 := ProbabilityTheory.mgf_pos (by
    have hdom := PolymerCalculus.integrableExpSet_log_finitePathMass
      β n 1 w hcNorm hcNormPos
    have hmem : (2 : ℝ) ∈ integrableExpSet
      (fun ω => Real.log (PolymerCalculus.finitePathMass β n 1 w cNorm ω)) disorderLaw
      := by rw [hdom]; exact Set.mem_univ _
    exact integrable_of_mem_integrableExpSet hmem)
  have hlogmgf : Real.log (mgf F disorderLaw 2) ≤ β ^ 2 := by
    calc
      _ ≤ Real.log (Real.exp (β ^ 2)) := Real.log_le_log hmgfpos (hmgf ▸ hsecond)
      _ = β ^ 2 := Real.log_exp _
  have hmeanNonpos : ∫ ω, F ω ∂disorderLaw ≤ 0 := by
    have hdef := hK.1
    unfold gaussianityDefect at hdef
    have hvar0 : 0 ≤ Var[F; disorderLaw] := variance_nonneg F disorderLaw
    linarith
  have hmeanLower : -(β ^ 2 / 2) ≤ ∫ ω, F ω ∂disorderLaw := by
    have h := hK.2.2.1
    linarith
  have hvar : Var[F; disorderLaw] ≤ β ^ 2 := by
    have h := hK.2.1
    linarith
  have hF2 : (∫ ω, F ω ^ 2 ∂disorderLaw) =
      Var[F; disorderLaw] + (∫ ω, F ω ∂disorderLaw) ^ 2 := by
    have h := ProbabilityTheory.variance_eq_sub hFmem
    have h' : Var[F; disorderLaw] =
        (∫ ω, F ω ^ 2 ∂disorderLaw) - (∫ ω, F ω ∂disorderLaw) ^ 2 := by
      simpa only [Pi.pow_apply] using h
    linarith
  have hmeanSq : (∫ ω, F ω ∂disorderLaw) ^ 2 ≤ (β ^ 2 / 2) ^ 2 := by
    nlinarith [hmeanNonpos, hmeanLower]
  have hFbound : (∫ ω, F ω ^ 2 ∂disorderLaw) ≤ β ^ 2 + β ^ 4 / 4 := by
    rw [hF2]
    nlinarith [hvar, hmeanSq]
  have hratio (ω : Disorder) :
      Real.log (profileP2Fun β n (n + 1) η f ω) -
          Real.log (profileP2Fun 0 n (n + 1) η f ω) = F ω := by
    have hβ := hprofile β ω
    have hscaleω := hscale ω
    have hbase : c₀ = profileP2Fun 0 n (n + 1) η f ω := by
      dsimp [c₀]
      rw [hprofile 0 (fun _ => 0), hprofile 0 ω]
      simp [PolymerCalculus.finitePathMass, PolymerCalculus.pathEnergy]
    rw [hβ, hscaleω, ← hbase]
    rw [Real.log_mul hc₀ (hFpos ω).ne']
    simp only [F]
    ring
  have hFint : Integrable (fun ω => F ω ^ 2) disorderLaw := hFmem.integrable_sq
  refine ⟨?_, ?_⟩
  · have heq : (fun ω =>
        (Real.log (profileP2Fun β n (n + 1) η f ω) -
          Real.log (profileP2Fun 0 n (n + 1) η f ω)) ^ 2) = fun ω => F ω ^ 2 :=
      by
        funext ω
        rw [hratio ω]
    rw [heq]
    exact hFint
  · rw [show (fun ω =>
        (Real.log (profileP2Fun β n (n + 1) η f ω) -
          Real.log (profileP2Fun 0 n (n + 1) η f ω)) ^ 2) = fun ω => F ω ^ 2 by
        funext ω
        rw [hratio ω]]
    exact hFbound

end Critical2DKPZ.LocalSobolev

end
