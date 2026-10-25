/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.LatticeReversalEstimates
public import Critical2DKPZ.Analysis.Lattice.Volume

/-! # Small spatial shifts of lattice cells -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Moments
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Symmetries

/-- The path-weight error is integrable by `Polymer.memLp_pathWeight`, with mean bounded by its second-moment deviation. -/
theorem integral_abs_pathWeight_sub_one_le (β : ℝ) (a : ℕ) (w : Site)
    {n : ℕ} (s : Fin n → Fin 4) :
    ∫ ω, |Polymer.pathWeight β a w s ω - 1| ∂disorderLaw ≤
      Real.sqrt (Real.exp ((n : ℝ) * β ^ 2) - 1) := by
  let f : Disorder → ℝ := fun ω => |Polymer.pathWeight β a w s ω - 1|
  have hvar := integral_sq_pathWeight_sub_one β a w s
  have hnonneg : 0 ≤ᵐ[disorderLaw] f := Filter.Eventually.of_forall fun ω => abs_nonneg _
  have hconst : MemLp (fun _ : Disorder => (1 : ℝ)) 2 disorderLaw := by
    exact memLp_const (1 : ℝ)
  have hf : MemLp f 2 disorderLaw := by
    have hW := Polymer.memLp_pathWeight β a w s 2 (by norm_num)
    have hsub : MemLp (fun ω => Polymer.pathWeight β a w s ω - 1) 2 disorderLaw :=
      hW.sub hconst
    simpa [f, Real.norm_eq_abs] using hsub.norm
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hf
  have hconst' : MemLp (fun _ : Disorder => (1 : ℝ))
      (ENNReal.ofReal (2 : ℝ)) disorderLaw := by simpa using hconst
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := disorderLaw) hpq hnonneg
    (Filter.Eventually.of_forall fun _ => (show 0 ≤ (1 : ℝ) by norm_num)) hf' hconst'
  have hleft : (∫ ω, f ω * 1 ∂disorderLaw) = ∫ ω, f ω ∂disorderLaw := by
    simp
  have hright : (∫ ω, f ω ^ (2 : ℝ) ∂disorderLaw) =
      Real.exp ((n : ℝ) * β ^ 2) - 1 := by
    calc
      _ = ∫ ω, (Polymer.pathWeight β a w s ω - 1) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        change |Polymer.pathWeight β a w s ω - 1| ^ (2 : ℝ) =
          (Polymer.pathWeight β a w s ω - 1) ^ 2
        rw [Real.rpow_ofNat]
        exact sq_abs (Polymer.pathWeight β a w s ω - 1)
      _ = Real.exp ((n : ℝ) * β ^ 2) - 1 := hvar
  rw [hleft, hright] at hholder
  simpa [f, measure_univ, Real.sqrt_eq_rpow] using hholder


private theorem nearestEven_add_siteToPlane_of_even (x : Plane) (d : Site)
    (hd : d ∈ Critical2DKPZ.evenLattice) :
    Critical2DKPZ.nearestEven (x + Critical2DKPZ.siteToPlane d) =
      Critical2DKPZ.nearestEven x + d := by
  obtain ⟨k, hk⟩ := hd
  let l : ℤ := d 0 - k
  have hd0 : d 0 = k + l := by dsimp [l]; omega
  have hd1 : d 1 = k - l := by dsimp [l]; omega
  have hkR : (d 0 : ℝ) + d 1 = 2 * k := by
    have hk' : d 0 + d 1 = 2 * k := by nlinarith only [hk]
    exact_mod_cast hk'
  have hlR : (d 0 : ℝ) - d 1 = 2 * l := by
    dsimp [l]
    have hkR' : (d 0 : ℝ) + d 1 = 2 * k := hkR
    norm_cast at hkR'
    push_cast
    nlinarith
  have hplus :
      round (((x + Critical2DKPZ.siteToPlane d) 0 +
          (x + Critical2DKPZ.siteToPlane d) 1) / 2) =
        round ((x 0 + x 1) / 2) + k := by
    have heq : ((x + Critical2DKPZ.siteToPlane d) 0 +
        (x + Critical2DKPZ.siteToPlane d) 1) / 2 =
        (x 0 + x 1) / 2 + (k : ℝ) := by
      simp [Critical2DKPZ.siteToPlane]
      nlinarith [hkR]
    rw [heq, round_eq]
    rw [show (x 0 + x 1) / 2 + (k : ℝ) + 1 / 2 =
      ((x 0 + x 1) / 2 + 1 / 2) + (k : ℝ) by ring]
    rw [Int.floor_add_intCast, ← round_eq]
  have hminus :
      round (((x + Critical2DKPZ.siteToPlane d) 0 -
          (x + Critical2DKPZ.siteToPlane d) 1) / 2) =
        round ((x 0 - x 1) / 2) + l := by
    have heq : ((x + Critical2DKPZ.siteToPlane d) 0 -
        (x + Critical2DKPZ.siteToPlane d) 1) / 2 =
        (x 0 - x 1) / 2 + (l : ℝ) := by
      simp [Critical2DKPZ.siteToPlane]
      nlinarith [hlR]
    rw [heq, round_eq]
    rw [show (x 0 - x 1) / 2 + (l : ℝ) + 1 / 2 =
      ((x 0 - x 1) / 2 + 1 / 2) + (l : ℝ) by ring]
    rw [Int.floor_add_intCast, ← round_eq]
  simp only [Critical2DKPZ.nearestEven]
  rw [hplus, hminus]
  ext i
  fin_cases i
  · change round ((x 0 + x 1) / 2) + k +
        (round ((x 0 - x 1) / 2) + l) =
      (round ((x 0 + x 1) / 2) + round ((x 0 - x 1) / 2)) + d 0
    rw [hd0]
    ring
  · change round ((x 0 + x 1) / 2) + k -
        (round ((x 0 - x 1) / 2) + l) =
      (round ((x 0 + x 1) / 2) - round ((x 0 - x 1) / 2)) + d 1
    rw [hd1]
    ring

/-- Translating a plane point by a scaled even site translates its lattice point exactly. -/
theorem latticePoint_add_scaled_even (N : ℕ) (hN : 0 < N) (p : Plane)
    (d : Site) (hd : d ∈ Critical2DKPZ.evenLattice) :
    Critical2DKPZ.latticePoint N
        (p + (Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d) =
      Critical2DKPZ.latticePoint N p + d := by
  unfold Critical2DKPZ.latticePoint
  rw [show Real.sqrt ((N : ℝ) / 2) •
        (p + (Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d) =
      Real.sqrt ((N : ℝ) / 2) • p + Critical2DKPZ.siteToPlane d by
        rw [smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))]
        simp]
  exact nearestEven_add_siteToPlane_of_even _ _ hd

/-- A scaled even-site translation carries a lattice cell onto the translated cell. -/
theorem cell_translate_even (N : ℕ) (hN : 0 < N) (z d : Site)
    (hd : d ∈ Critical2DKPZ.evenLattice) :
    Critical2DKPZ.cell N (z + d) =
      (fun p : Plane => p + (Real.sqrt ((N : ℝ) / 2))⁻¹ •
        Critical2DKPZ.siteToPlane d) '' Critical2DKPZ.cell N z := by
  let η : Plane := (Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d
  ext p
  constructor
  · intro hp
    refine ⟨p - η, ?_, ?_⟩
    · rw [Critical2DKPZ.mem_cell_iff] at hp ⊢
      have h := latticePoint_add_scaled_even N hN (p - η) d hd
      rw [show (p - η) + η = p by simp [η]] at h
      rw [hp] at h
      exact (add_right_cancel h).symm
    · simp [η]
  · rintro ⟨q, hq, rfl⟩
    rw [Critical2DKPZ.mem_cell_iff] at hq ⊢
    rw [latticePoint_add_scaled_even N hN q d hd, hq]

/-- Translate the second coordinate of a planar pair by a fixed displacement. -/
def pairSecondShift (η : Plane) :
    (Plane × Plane) ≃ₜ (Plane × Plane) where
  toFun p := (p.1, p.2 + η)
  invFun p := (p.1, p.2 - η)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add continuous_const)
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub continuous_const)

/-- Pull a compactly supported test back under a second-coordinate translation. -/
def pairSecondShiftTest (η : Plane) (φ : C_c(Plane × Plane, ℝ)) :
    C_c(Plane × Plane, ℝ) where
  toFun p := φ (pairSecondShift η p)
  continuous_toFun := φ.continuous.comp (pairSecondShift η).continuous
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (pairSecondShift η)

/-- Translate the second cell weight by an even site by shifting the test in that coordinate. -/
theorem cellTestWeight_translateSecond_even (N : ℕ) (hN : 0 < N)
    (x z d : Site) (hd : d ∈ Critical2DKPZ.evenLattice)
    (φ : C_c(Plane × Plane, ℝ)) :
    cellTestWeight N φ x (z + d) =
      cellTestWeight N (pairSecondShiftTest
        ((Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d) φ) x z := by
  let η : Plane := (Real.sqrt ((N : ℝ) / 2))⁻¹ • Critical2DKPZ.siteToPlane d
  let E := pairSecondShift η
  let A : Set (Plane × Plane) := Critical2DKPZ.cell N x ×ˢ Critical2DKPZ.cell N z
  have himage : E '' A =
      Critical2DKPZ.cell N x ×ˢ Critical2DKPZ.cell N (z + d) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      constructor
      · change q.1 ∈ Critical2DKPZ.cell N x
        exact hq.1
      · change q.2 + η ∈ Critical2DKPZ.cell N (z + d)
        rw [cell_translate_even N hN z d hd]
        exact ⟨q.2, hq.2, rfl⟩
    · rintro ⟨hx, hy⟩
      change p.2 ∈ Critical2DKPZ.cell N (z + d) at hy
      rw [cell_translate_even N hN z d hd] at hy
      rcases hy with ⟨q, hq, hqη⟩
      refine ⟨(p.1, q), ⟨hx, hq⟩, ?_⟩
      apply Prod.ext
      · rfl
      · change q + η = p.2
        simpa [η] using hqη
  unfold cellTestWeight
  rw [← himage]
  have hMP : MeasurePreserving E (volume : Measure (Plane × Plane)) volume := by
    rw [Measure.volume_eq_prod Plane Plane]
    change MeasurePreserving (fun p : Plane × Plane => (p.1, p.2 + η)) _ _
    exact (MeasurePreserving.id volume).prod (measurePreserving_add_right volume η)
  have h := hMP.setIntegral_image_emb E.measurableEmbedding φ A
  change (N / 4 : ℝ) *
      ∫ p in E '' A, φ p =
        (N / 4 : ℝ) * ∫ p in A, pairSecondShiftTest η φ p
  apply congrArg (fun q : ℝ => (N / 4 : ℝ) * q)
  calc
    ∫ p in E '' A, φ p = ∫ p in A, φ (E p) := h
    _ = ∫ p in A, pairSecondShiftTest η φ p := by rfl

end Critical2DKPZ.SHF.Symmetries

end
