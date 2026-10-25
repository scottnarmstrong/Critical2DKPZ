/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.JointConvergence.HeatStartLogFieldEstimates
import all Critical2DKPZ.JointConvergence.HeatStartLogFieldEstimates
public import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
public import Critical2DKPZ.SHF.Positivity.HeatBoundedIntegrability
public import Critical2DKPZ.SHF.Positivity.MeasurablePairing
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Joint convergence of spatially tested heat-start logarithms -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Positivity
open scoped BigOperators BoundedContinuousFunction ENNReal Topology

namespace Critical2DKPZ.JointConvergence

/-- Joint convergence of the spatially tested heat-start logarithm fields. -/
theorem heatStart_logField_tendsto_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane =>
        heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) =>
          ∫ p, heatKernel δ (p.1 - x) * g p.2
            ∂(polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g)
        (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane)
      (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i)
          (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ),
      0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω => Real.log (shfPairing Z s t
        (fun y => heatKernel δ (y - x)) (fun y => Real.exp (h₀ y)) ω)) P)
    (T : ℝ) (k : ℕ) (h₀ : Fin k → (Plane →ᵇ ℝ))
    (s δ : Fin k → ℝ) (φ : Fin k → TestFn)
    (hs : ∀ i, 0 ≤ s i ∧ s i < T ∧ 0 < δ i) :
    TendstoInDistribution
      (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
        ∫ x, φ i x * Real.log (profileP2Fun (criticalBeta ϑ N)
          (evenCeil (N * s i)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N x))
          (cellAverage N fun y => Real.exp (h₀ i y)) ω))
      atTop
      (fun ω i => ∫ x, φ i x * Real.log (shfPairing Z (s i) T
        (fun y => heatKernel (δ i) (y - x))
        (fun y => Real.exp (h₀ i y)) ω))
      (fun _ => disorderLaw) P := by
  classical
  let X : ℕ → Disorder → Fin k → ℝ := fun N ω i =>
    ∫ x, φ i x * heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω
  let L : Ω → Fin k → ℝ := fun ω i =>
    ∫ x, φ i x * Real.log (shfPairing Z (s i) T
      (fun y => heatKernel (δ i) (y - x)) (fun y => Real.exp (h₀ i y)) ω)
  let g : Fin k → (Plane →ᵇ ℝ) := fun i => heatStartExpTerminal (h₀ i)
  have hg (i : Fin k) (y : Plane) : g i y = Real.exp (h₀ i y) := rfl
  have hgfun (i : Fin k) : (g i : Plane → ℝ) = fun y => Real.exp (h₀ i y) := by
    funext y
    exact hg i y
  let R : ℕ → ℝ := fun j => (j : ℝ) + 1
  let η : ℕ → ℝ := fun j => Real.exp (-2 * R j)
  obtain ⟨Craw, hKernelRaw⟩ := integral_abs_heatKernel_sub_le
  let Ckernel : ℝ := |Craw|
  have hKernel : ∀ u : ℝ, 0 < u → ∀ a b : Plane,
      ∫ y, |heatKernel u (y - a) - heatKernel u (y - b)| ≤
        Ckernel * ‖a - b‖ / Real.sqrt u := by
    intro u hu a b
    have h := hKernelRaw u hu a b
    dsimp [Ckernel]
    calc
      _ ≤ Craw * ‖a - b‖ / Real.sqrt u := h
      _ ≤ |Craw| * ‖a - b‖ / Real.sqrt u := by
        gcongr
        exact le_abs_self Craw
  have hCkernel : 0 ≤ Ckernel := abs_nonneg _
  let Cprof : Fin k → ℝ := fun i => Classical.choose
    (heatStartLogProfile_square_bound ϑ (hs i).1 (hs i).2.1 (hs i).2.2 (h₀ i))
  have hCprof (i : Fin k) : 0 ≤ Cprof i ∧ ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
      Integrable (fun ω => |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω| ^ 2)
        disorderLaw ∧
      ∫ ω, |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω| ^ 2 ∂disorderLaw ≤
        Cprof i * 2 * Real.Gamma 2 := by
    exact Classical.choose_spec
      (heatStartLogProfile_square_bound ϑ (hs i).1 (hs i).2.1 (hs i).2.2 (h₀ i))
  let Mprof : Fin k → ℝ := fun i => Cprof i * 2 * Real.Gamma 2
  have hMprof (i : Fin k) : 0 ≤ Mprof i := by
    dsimp [Mprof]
    exact mul_nonneg (mul_nonneg (hCprof i).1 (by norm_num))
      (Real.Gamma_pos_of_pos (by norm_num)).le
  let Mlim : Fin k → ℝ := fun i => Classical.choose
    (shf_heatStartLogField_square_bound ϑ P Z hZ hpair hjoint hpos T (h₀ i)
      (hs i).1 (hs i).2.1 (hs i).2.2)
  have hMlim (i : Fin k) : 0 ≤ Mlim i ∧ ∀ x : Plane,
      Integrable (fun ω => |Real.log (shfPairing Z (s i) T
        (fun y => heatKernel (δ i) (y - x))
        (fun y => Real.exp (h₀ i y)) ω)| ^ 2) P ∧
      ∫ ω, |Real.log (shfPairing Z (s i) T
        (fun y => heatKernel (δ i) (y - x))
        (fun y => Real.exp (h₀ i y)) ω)| ^ 2 ∂P ≤ Mlim i := by
    exact Classical.choose_spec
      (shf_heatStartLogField_square_bound ϑ P Z hZ hpair hjoint hpos T (h₀ i)
        (hs i).1 (hs i).2.1 (hs i).2.2)
  let meshCoeff : ℕ → Fin k → ℝ := fun j i =>
    Real.exp (R j) * (‖g i‖ * (Ckernel / Real.sqrt (δ i))) *
      ∫ x, |φ i x|
  let m : ℕ → ℕ := fun j => Classical.choose
    (exists_lattice_mesh_for_finite_coefficients (meshCoeff j)
      (by positivity : 0 < (R j)⁻¹))
  have hm (j : ℕ) : 0 < m j ∧ ∀ i,
      meshCoeff j i * (Real.sqrt ((m j : ℝ) / 2))⁻¹ ≤ (R j)⁻¹ := by
    exact Classical.choose_spec
      (exists_lattice_mesh_for_finite_coefficients (meshCoeff j)
        (by positivity : 0 < (R j)⁻¹))
  let S : ℕ → Finset Site := fun j => Classical.choose (exists_finite_heatStartCells φ (m j))
  have hS (j : ℕ) : ∀ i x, φ i x ≠ 0 → latticePoint (m j) x ∈ S j :=
    Classical.choose_spec (exists_finite_heatStartCells φ (m j))
  let Fpoly : ℕ → ℕ → Fin k → Site → Disorder → ℝ := fun j N i z ω =>
    heatStartLogClamp (R j)
      (∫ p, heatKernel (δ i) (p.1 - latticeRepresentative (m j) z) *
        Real.exp (h₀ i p.2) ∂polymerMeasure ϑ N (s i) T ω)
  let Fshf : ℕ → Fin k → Site → Ω → ℝ := fun j i z ω =>
    heatStartLogClamp (R j)
      (shfPairing Z (s i) T
        (fun y => heatKernel (δ i) (y - latticeRepresentative (m j) z))
        (fun y => Real.exp (h₀ i y)) ω)
  let Hpoly : ℕ → ℕ → Fin k → Plane × Disorder → ℝ := fun j N i q =>
    ∑ z : (S j).attach,
      if latticePoint (m j) q.1 = z.1 then Fpoly j N i z.1 q.2 else 0
  let Hshf : ℕ → Fin k → Plane × Ω → ℝ := fun j i q =>
    ∑ z : (S j).attach,
      if latticePoint (m j) q.1 = z.1 then Fshf j i z.1 q.2 else 0
  let Y : ℕ → ℕ → Disorder → Fin k → ℝ := fun j N ω i =>
    ∑ z : (S j).attach,
      (∫ x in cell (m j) z.1, φ i x) * Fpoly j N i z.1 ω
  let Yl : ℕ → Ω → Fin k → ℝ := fun j ω i =>
    ∑ z : (S j).attach,
      (∫ x in cell (m j) z.1, φ i x) * Fshf j i z.1 ω
  have hXmeas : ∀ N, AEMeasurable (X N) disorderLaw := by
    intro N
    apply aemeasurable_pi_iff.mpr
    intro i
    simpa [X] using aemeasurable_integral_heatStartLogProfile ϑ N
      (s i) T (δ i) (h₀ i) (φ i)
  have hLmeas : AEMeasurable L P := by
    apply aemeasurable_pi_iff.mpr
    intro i
    simpa [L] using aemeasurable_integral_shfLogField ϑ P Z hZ
      (s i) T (δ i) (hs i).1 (hs i).2.1 (hs i).2.2 (h₀ i) (φ i)
  have hY : ∀ j, TendstoInDistribution (fun N => Y j N) atTop (Yl j)
      (fun _ => disorderLaw) P := by
    intro j
    exact finiteMesh_clamped_pairing_tendsto ϑ P k Z hjoint T h₀ s δ φ
      (fun i => hs i) (m j) (R j) (S j)
  have hYlmeas : ∀ j, AEMeasurable (Yl j) P := by
    intro j
    apply aemeasurable_pi_iff.mpr
    intro i
    apply aemeasurable_sum_of_finite_index
    intro z
    have hz := aemeasurable_shf_heatPairing_clamp_at P Z hZ hpair
      (s i) T (δ i) (hs i).1 (hs i).2.1 (hs i).2.2
      (latticeRepresentative (m j) z.1) (h₀ i) (R j)
    have hz' : AEMeasurable (fun ω => Fshf j i z.1 ω *
        (∫ x in cell (m j) z.1, φ i x)) P := hz.mul_const _
    apply hz'.congr
    filter_upwards [] with ω
    ring
  let Bpoly : ℕ → ℝ := fun j => ∑ i : Fin k,
    (((Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
      (∫ x, |φ i x|)) + (R j)⁻¹)
  let Blim : ℕ → ℝ := fun j => ∑ i : Fin k,
    (Mlim i / R j * (∫ x, |φ i x|) + (R j)⁻¹)
  have hBpoly : Tendsto Bpoly atTop (𝓝 0) := by
    have hterm (i : Fin k) : Tendsto
        (fun j : ℕ => (Mprof i / ((j : ℝ) + 1) +
          Real.exp ‖h₀ i‖ * Real.exp (-((j : ℝ) + 1))) *
          (∫ x, |φ i x|) + ((j : ℝ) + 1)⁻¹)
        atTop (𝓝 0) := by
      have hfirst := tendsto_const_div_nat_add_one (Mprof i)
      have hsecond := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.exp ‖h₀ i‖)
        atTop (𝓝 (Real.exp ‖h₀ i‖))).mul tendsto_exp_neg_nat_add_one
      have hthird := tendsto_const_div_nat_add_one 1
      have hprod := (hfirst.add hsecond).mul_const (∫ x, |φ i x|)
      convert hprod.add hthird using 1 <;> ext j <;> simp
    have hsum := tendsto_finsetSum (s := Finset.univ) (fun i hi => hterm i)
    simpa [Bpoly, R] using hsum
  have hBlim : Tendsto Blim atTop (𝓝 0) := by
    have hterm (i : Fin k) : Tendsto
        (fun j : ℕ => Mlim i / ((j : ℝ) + 1) * (∫ x, |φ i x|) +
          ((j : ℝ) + 1)⁻¹)
        atTop (𝓝 0) := by
      have hprod := (tendsto_const_div_nat_add_one (Mlim i)).mul_const
        (∫ x, |φ i x|)
      convert hprod.add (tendsto_const_div_nat_add_one 1) using 1 <;>
        ext j <;> simp
    have hsum := tendsto_finsetSum (s := Finset.univ) (fun i hi => hterm i)
    simpa [Blim, R] using hsum
  have hlimComp (j : ℕ) (i : Fin k) :
      Integrable (fun ω => |Yl j ω i - L ω i|) P ∧
      ∫ ω, |Yl j ω i - L ω i| ∂P ≤
        Mlim i / R j * (∫ x, |φ i x|) + (R j)⁻¹ := by
    let F : Plane × Ω → ℝ := fun q => Real.log (shfPairing Z (s i) T
      (fun y => heatKernel (δ i) (y - q.1)) (fun y => Real.exp (h₀ i y)) q.2)
    let H : Plane × Ω → ℝ := Hshf j i
    have hFjoint : AEMeasurable F (volume.prod P) := by
      simpa [F] using aemeasurable_shfLogField_joint ϑ P Z hZ
        (s i) T (δ i) (hs i).1 (hs i).2.1 (hs i).2.2 (h₀ i)
    have hFsec (x : Plane) : AEMeasurable (fun ω => F (x, ω)) P := by
      simpa [F] using (hpos (s i) T (δ i) x (h₀ i)
        (hs i).1 (hs i).2.1 (hs i).2.2).2
    have hFsq (x : Plane) : Integrable (fun ω => |F (x, ω)| ^ 2) P ∧
        ∫ ω, |F (x, ω)| ^ 2 ∂P ≤ Mlim i := by
      simpa [F] using (hMlim i).2 x
    have hFprod : Integrable (fun q => φ i q.1 * F q) (volume.prod P) :=
      integrable_test_mul_joint P hFjoint
        (fun x => (hFsec x).aestronglyMeasurable) (hMlim i).1 hFsq (φ i)
    have hSite (z : Site) : AEMeasurable (Fshf j i z) P := by
      simpa [Fshf] using aemeasurable_shf_heatPairing_clamp_at P Z hZ hpair
        (s i) T (δ i) (hs i).1 (hs i).2.1 (hs i).2.2
        (latticeRepresentative (m j) z) (h₀ i) (R j)
    have hHjoint : AEMeasurable H (volume.prod P) := by
      exact aemeasurable_latticeSiteSum P (m j) (S j)
        (Fshf j i) hSite
    have hHsec (x : Plane) : AEMeasurable (fun ω => H (x, ω)) P := by
      exact aemeasurable_latticeSiteSum_section P (m j) (S j)
        (Fshf j i) hSite x
    let K : ℝ := (Fintype.card (↥(S j).attach) : ℝ) * R j
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hHbound (q : Plane × Ω) : |H q| ≤ K := by
      dsimp [H, Hshf, K]
      calc
        |∑ z : (S j).attach,
            if latticePoint (m j) q.1 = z.1 then Fshf j i z.1 q.2 else 0| ≤
            ∑ z : (S j).attach,
              |if latticePoint (m j) q.1 = z.1 then Fshf j i z.1 q.2 else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ z : (S j).attach, R j := by
          apply Finset.sum_le_sum
          intro z hz
          split_ifs
          · exact abs_heatStartLogClamp_le (R j) _ (by positivity)
          · simp
            positivity
        _ = (Fintype.card (↥(S j).attach) : ℝ) * R j := by simp [nsmul_eq_mul]
    have hHprod : Integrable (fun q => φ i q.1 * H q) (volume.prod P) :=
      integrable_test_mul_bounded_field P hHjoint hHsec hK hHbound (φ i)
    have hFint (x : Plane) : Integrable (fun ω => F (x, ω)) P := by
      have habs := integrable_abs_of_integrable_sq (hFsec x).aestronglyMeasurable
        (hFsq x).1
      apply (integrable_norm_iff (hFsec x).aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs] using habs
    have hHint (x : Plane) : Integrable (fun ω => H (x, ω)) P := by
      apply Integrable.of_bound (hHsec x).aestronglyMeasurable K
      filter_upwards [] with ω
      rw [Real.norm_eq_abs]
      exact hHbound (x, ω)
    have hsec (x : Plane) : Integrable (fun ω => |F (x, ω) - H (x, ω)|) P :=
      (hFint x).sub (hHint x) |>.norm
    let Tglobal : ℝ := Real.exp (R j) *
      (‖g i‖ * (Ckernel / Real.sqrt (δ i)) *
        (Real.sqrt ((m j : ℝ) / 2))⁻¹)
    have hshiftB : Tglobal * ∫ y, |φ i y| ≤ (R j)⁻¹ := by
      calc
        _ = meshCoeff j i * (Real.sqrt ((m j : ℝ) / 2))⁻¹ := by
          dsimp [Tglobal, meshCoeff]
          ring
        _ ≤ (R j)⁻¹ := (hm j).2 i
    have hpoint (x : Plane) (hφ : φ i x ≠ 0) :
        ∫ ω, |F (x, ω) - H (x, ω)| ∂P ≤
          Mlim i / R j + Real.exp (R j) *
            (‖g i‖ * (Ckernel * (Real.sqrt ((m j : ℝ) / 2))⁻¹ /
              Real.sqrt (δ i))) := by
      have hxS := hS j i x hφ
      have hsample (ω : Ω) : H (x, ω) = Fshf j i (latticePoint (m j) x) ω := by
        dsimp [H, Hshf]
        change (∑ z : (S j).attach,
          if latticePoint (m j) x = z.1 then Fshf j i z.1 ω else 0) = _
        exact latticeSiteSum_eq_sample_of_mem (m j) (S j) (Fshf j i)
          (x := x) ω hxS
      have hposx := (hpos (s i) T (δ i) x (h₀ i)
        (hs i).1 (hs i).2.1 (hs i).2.2).1
      have hlogMeas := (hpos (s i) T (δ i) x (h₀ i)
        (hs i).1 (hs i).2.1 (hs i).2.2).2
      let A : Ω → ℝ := fun ω => shfPairing Z (s i) T
        (fun y => heatKernel (δ i) (y - x))
        (fun y => Real.exp (h₀ i y)) ω
      have hAmeas : AEMeasurable A P := by
        have h := Real.measurable_exp.comp_aemeasurable hlogMeas
        refine h.congr ?_
        filter_upwards [hposx] with ω hω
        exact Real.exp_log hω
      have hlogSq := (hMlim i).2 x
      have htrunc := integrable_abs_log_sub_heatStartLogClamp_le
        (M := Mlim i) (R := R j) hAmeas hposx
        hlogSq.1 (hMlim i).1 hlogSq.2 (by positivity)
      have hshift := shf_heatPairing_clamp_translation_l1_le ϑ P Z hjoint
        (hs i).1 (hs i).2.1 (hs i).2.2 (R j) (by positivity) Ckernel hKernel
        x (cellSample (m j) x) (g i)
      have hmeshDist : ‖x - cellSample (m j) x‖ ≤
          (Real.sqrt ((m j : ℝ) / 2))⁻¹ := by
        calc
          ‖x - cellSample (m j) x‖ = dist x (cellSample (m j) x) :=
            (dist_eq_norm _ _).symm
          _ = dist (cellSample (m j) x) x := dist_comm _ _
          _ ≤ (Real.sqrt ((m j : ℝ) / 2))⁻¹ :=
            dist_cellSample_le (hm j).1 x
      have hkernelMesh : Ckernel * ‖x - cellSample (m j) x‖ /
          Real.sqrt (δ i) ≤ Ckernel / Real.sqrt (δ i) *
            (Real.sqrt ((m j : ℝ) / 2))⁻¹ := by
        rw [show Ckernel * ‖x - cellSample (m j) x‖ / Real.sqrt (δ i) =
          (Ckernel / Real.sqrt (δ i)) * ‖x - cellSample (m j) x‖ by ring]
        exact mul_le_mul_of_nonneg_left hmeshDist
          (div_nonneg hCkernel (Real.sqrt_nonneg _))
      let A' : Ω → ℝ := fun ω => shfPairing Z (s i) T
        (fun y => heatKernel (δ i) (y - cellSample (m j) x))
        (fun y => Real.exp (h₀ i y)) ω
      have hshiftRaw : ∫ ω, |heatStartLogClamp (R j) (A ω) -
          heatStartLogClamp (R j) (A' ω)| ∂P ≤ Tglobal := by
        calc
          _ ≤ Real.exp (R j) *
              (‖g i‖ * (Ckernel * ‖x - cellSample (m j) x‖ /
                Real.sqrt (δ i))) := by
            simpa only [A, A', hgfun] using hshift.2
          _ ≤ Real.exp (R j) *
              (‖g i‖ * (Ckernel / Real.sqrt (δ i) *
                (Real.sqrt ((m j : ℝ) / 2))⁻¹)) := by
            apply mul_le_mul_of_nonneg_left
            · exact mul_le_mul_of_nonneg_left hkernelMesh (norm_nonneg _)
            · positivity
          _ = Tglobal := by dsimp [Tglobal]; ring
      have hsampleEq : ∀ ω,
          Fshf j i (latticePoint (m j) x) ω = heatStartLogClamp (R j) (A' ω) := by
        intro ω
        have hrep : latticeRepresentative (m j) (latticePoint (m j) x) =
            cellSample (m j) x := rfl
        dsimp only [Fshf, A']
        rw [hrep]
      have htruncInt : Integrable (fun ω =>
          |Real.log (A ω) - heatStartLogClamp (R j) (A ω)|) P := htrunc.1
      have hpointwise (ω : Ω) : |F (x, ω) - H (x, ω)| ≤
          |Real.log (A ω) - heatStartLogClamp (R j) (A ω)| +
          |heatStartLogClamp (R j) (A ω) - heatStartLogClamp (R j) (A' ω)| := by
        rw [hsample ω, hsampleEq ω]
        dsimp only [F, A]
        exact abs_sub_le _ _ _
      have htruncBound := htrunc.2
      have hcombine : ∫ ω, |F (x, ω) - H (x, ω)| ∂P ≤
          Mlim i / R j + Tglobal := by
        have hDiff := hsec x
        have hsumInt : Integrable (fun ω =>
            |Real.log (A ω) - heatStartLogClamp (R j) (A ω)| +
              |heatStartLogClamp (R j) (A ω) - heatStartLogClamp (R j) (A' ω)|) P := by
          let hsumSrc := htrunc.1.add hshift.1
          refine ⟨hsumSrc.aestronglyMeasurable, ?_⟩
          rw [hasFiniteIntegral_iff_norm]
          exact (hasFiniteIntegral_iff_norm _).mp hsumSrc.hasFiniteIntegral
        calc
          _ ≤ ∫ ω, |Real.log (A ω) - heatStartLogClamp (R j) (A ω)| +
              |heatStartLogClamp (R j) (A ω) - heatStartLogClamp (R j) (A' ω)| ∂P := by
                exact integral_mono hDiff hsumInt hpointwise
          _ = _ := by
            simpa only [A, A', hgfun] using (integral_add htrunc.1 hshift.1)
          _ ≤ Mlim i / R j + Tglobal := add_le_add htruncBound hshiftRaw
      calc
        _ ≤ Mlim i / R j + Tglobal := hcombine
        _ = Mlim i / R j + Real.exp (R j) *
            (‖g i‖ * (Ckernel * (Real.sqrt ((m j : ℝ) / 2))⁻¹ /
              Real.sqrt (δ i))) := by
          dsimp [Tglobal]
          ring
    have hRj : 0 < R j := by
      change 0 < (j : ℝ) + 1
      exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one
    have hEtaj : 0 ≤ η j := (Real.exp_pos (-2 * R j)).le
    have hTglobal : 0 ≤ Tglobal := by
      dsimp [Tglobal]
      exact mul_nonneg (Real.exp_nonneg _) <| mul_nonneg
        (mul_nonneg (norm_nonneg _)
          (div_nonneg hCkernel (Real.sqrt_nonneg _)))
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    have hBpoint : 0 ≤ Mlim i / R j + Tglobal :=
      add_nonneg (div_nonneg (hMlim i).1 hRj.le) hTglobal
    have hdiff : Integrable (fun ω => ∫ x, φ i x * (F (x, ω) - H (x, ω))) P ∧
        ∫ ω, |∫ x, φ i x * (F (x, ω) - H (x, ω))| ∂P ≤
          (Mlim i / R j + Tglobal) * (∫ x, |φ i x|) := by
      exact integral_test_field_difference_l1_on_support_le
        (P := P) (F := F) (G := H) (φ := φ i)
        (hF := hFprod) (hG := hHprod) (hsec := hsec)
        (B := Mlim i / R j + Tglobal) (_hB := hBpoint)
        (hpoint := fun x hx => by
          calc
            _ ≤ Mlim i / R j + Real.exp (R j) *
                (‖g i‖ * (Ckernel * (Real.sqrt ((m j : ℝ) / 2))⁻¹ /
                  Real.sqrt (δ i))) := hpoint x hx
            _ = Mlim i / R j + Tglobal := by dsimp [Tglobal]; ring)
    have hIntY (ω : Ω) : (∫ x, φ i x * H (x, ω)) = Yl j ω i := by
      simpa only [Yl, H, Hshf] using
        integral_test_latticeSiteSum_eq (φ := φ i) (m j) (S j)
          (fun z => Fshf j i z ω) (fun x hx => hS j i x hx)
    have hsections : ∀ᵐ ω ∂P,
        Integrable (fun x => φ i x * F (x, ω)) ∧
        Integrable (fun x => φ i x * H (x, ω)) :=
      hFprod.prod_left_ae.and hHprod.prod_left_ae
    have hdiffEq (ω : Ω) (hFω : Integrable (fun x => φ i x * F (x, ω)))
        (hHω : Integrable (fun x => φ i x * H (x, ω))) :
        L ω i - Yl j ω i = ∫ x, φ i x * (F (x, ω) - H (x, ω)) := by
      dsimp only [L]
      rw [← hIntY]
      calc
        (∫ x, φ i x * F (x, ω)) - ∫ x, φ i x * H (x, ω) =
            ∫ x, (φ i x * F (x, ω) - φ i x * H (x, ω)) :=
              (integral_sub hFω hHω).symm
        _ = ∫ x, φ i x * (F (x, ω) - H (x, ω)) := by
          congr 1
          funext x
          ring
    refine ⟨?_, ?_⟩
    · apply (hdiff.1.norm).congr
      filter_upwards [hsections] with ω hω
      have heq := hdiffEq ω hω.1 hω.2
      rw [show Yl j ω i - L ω i = -(∫ x, φ i x * (F (x, ω) - H (x, ω))) by linarith [heq]]
      simp [Real.norm_eq_abs]
    · have hBcomp : (Mlim i / R j + Tglobal) * (∫ x, |φ i x|) ≤
          Mlim i / R j * (∫ x, |φ i x|) + (R j)⁻¹ := by
        calc
          _ = Mlim i / R j * (∫ x, |φ i x|) +
              Tglobal * (∫ x, |φ i x|) := by ring
          _ ≤ Mlim i / R j * (∫ x, |φ i x|) + (R j)⁻¹ :=
            add_le_add le_rfl hshiftB
      calc
        _ = ∫ ω, |∫ x, φ i x * (F (x, ω) - H (x, ω))| ∂P := by
          apply integral_congr_ae
          filter_upwards [hsections] with ω hω
          have heq := hdiffEq ω hω.1 hω.2
          rw [show Yl j ω i - L ω i = -(∫ x, φ i x * (F (x, ω) - H (x, ω))) by
            linarith [heq]]
          simp
        _ ≤ (Mlim i / R j + Tglobal) * (∫ x, |φ i x|) := hdiff.2
        _ ≤ Mlim i / R j * (∫ x, |φ i x|) + (R j)⁻¹ := hBcomp

  have hpolyComp (j N : ℕ) (i : Fin k) :
      1 ≤ N →
      (∀ x : Plane, ∑' w : Site,
        |srwKernel (evenCeil ((N : ℝ) * δ i)) (w - latticePoint N x) -
          ∫ y in cell N w, heatKernel (δ i) (y - x)| ≤ η j) →
      (∀ x : Plane,
        Integrable (fun ω => |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω| ^ 2)
          disorderLaw ∧
        ∫ ω, |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω| ^ 2 ∂disorderLaw ≤
          Mprof i) →
      Integrable (fun ω => |X N ω i - Y j N ω i|) disorderLaw ∧
      ∫ ω, |X N ω i - Y j N ω i| ∂disorderLaw ≤
        (Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
          (∫ x, |φ i x|) + (R j)⁻¹ := by
    intro hN hKernelN hSqN
    let F : Plane × Disorder → ℝ := fun q =>
      heatStartLogProfile ϑ N (s i) T (δ i) q.1 (h₀ i) q.2
    let H : Plane × Disorder → ℝ := Hpoly j N i
    have hFjoint : AEMeasurable F (volume.prod disorderLaw) := by
      simpa [F] using aemeasurable_heatStartLogProfile_joint ϑ N
        (s i) T (δ i) (h₀ i)
    have hFsec (x : Plane) : AEMeasurable (fun ω => F (x, ω)) disorderLaw := by
      dsimp [F]
      exact (Polymer.measurable_profileP2Fun (criticalBeta ϑ N)
        (evenCeil (N * s i)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ i)) (w - latticePoint N x))
        (cellAverage N fun y => Real.exp (h₀ i y))).log.aemeasurable
    have hFsq (x : Plane) : Integrable (fun ω => |F (x, ω)| ^ 2) disorderLaw ∧
        ∫ ω, |F (x, ω)| ^ 2 ∂disorderLaw ≤ Mprof i := by
      simpa [F, heatStartLogProfile] using hSqN x
    have hFprod : Integrable (fun q => φ i q.1 * F q)
        (volume.prod disorderLaw) :=
      integrable_test_mul_joint disorderLaw hFjoint
        (fun x => (hFsec x).aestronglyMeasurable) (hMprof i) hFsq (φ i)
    have hSite (z : Site) : AEMeasurable (Fpoly j N i z) disorderLaw := by
      simpa [Fpoly] using aemeasurable_polymer_heatPairing_clamp_at ϑ hN
        (s i) T (δ i) (hs i).2.2 (latticeRepresentative (m j) z) (h₀ i) (R j)
    have hHjoint : AEMeasurable H (volume.prod disorderLaw) := by
      exact aemeasurable_latticeSiteSum disorderLaw (m j) (S j)
        (Fpoly j N i) hSite
    have hHsec (x : Plane) : AEMeasurable (fun ω => H (x, ω)) disorderLaw := by
      exact aemeasurable_latticeSiteSum_section disorderLaw
        (m j) (S j) (Fpoly j N i) hSite x
    let K : ℝ := (Fintype.card (↥(S j).attach) : ℝ) * R j
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hHbound (q : Plane × Disorder) : |H q| ≤ K := by
      dsimp [H, Hpoly, K]
      calc
        |∑ z : (S j).attach,
            if latticePoint (m j) q.1 = z.1 then Fpoly j N i z.1 q.2 else 0| ≤
            ∑ z : (S j).attach,
              |if latticePoint (m j) q.1 = z.1 then Fpoly j N i z.1 q.2 else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ z : (S j).attach, R j := by
          apply Finset.sum_le_sum
          intro z hz
          split_ifs
          · exact abs_heatStartLogClamp_le (R j) _ (by positivity)
          · simp
            positivity
        _ = (Fintype.card (↥(S j).attach) : ℝ) * R j := by simp [nsmul_eq_mul]
    have hHprod : Integrable (fun q => φ i q.1 * H q)
        (volume.prod disorderLaw) :=
      integrable_test_mul_bounded_field disorderLaw hHjoint hHsec hK hHbound (φ i)
    have hFint (x : Plane) : Integrable (fun ω => F (x, ω)) disorderLaw := by
      have habs := integrable_abs_of_integrable_sq (hFsec x).aestronglyMeasurable
        (hFsq x).1
      apply (integrable_norm_iff (hFsec x).aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs] using habs
    have hHint (x : Plane) : Integrable (fun ω => H (x, ω)) disorderLaw := by
      apply Integrable.of_bound (hHsec x).aestronglyMeasurable K
      filter_upwards [] with ω
      rw [Real.norm_eq_abs]
      exact hHbound (x, ω)
    have hsec (x : Plane) : Integrable (fun ω => |F (x, ω) - H (x, ω)|) disorderLaw :=
      (hFint x).sub (hHint x) |>.norm
    let Tglobal : ℝ := Real.exp (R j) *
      (‖g i‖ * (Ckernel / Real.sqrt (δ i)) *
        (Real.sqrt ((m j : ℝ) / 2))⁻¹)
    have hshiftB : Tglobal * ∫ y, |φ i y| ≤ (R j)⁻¹ := by
      calc
        _ = meshCoeff j i * (Real.sqrt ((m j : ℝ) / 2))⁻¹ := by
          dsimp [Tglobal, meshCoeff]
          ring
        _ ≤ (R j)⁻¹ := (hm j).2 i
    have hpoint (x : Plane) (hφ : φ i x ≠ 0) :
        ∫ ω, |F (x, ω) - H (x, ω)| ∂disorderLaw ≤
          Mprof i / R j + Real.exp (R j) *
            (Real.exp ‖h₀ i‖ * η j) + Tglobal := by
      have hxS := hS j i x hφ
      have hsample (ω : Disorder) :
          H (x, ω) = Fpoly j N i (latticePoint (m j) x) ω := by
        dsimp [H, Hpoly]
        change (∑ z : (S j).attach,
          if latticePoint (m j) x = z.1 then Fpoly j N i z.1 ω else 0) = _
        exact latticeSiteSum_eq_sample_of_mem (m j) (S j) (Fpoly j N i)
          (x := x) ω hxS
      have hsampleEq (ω : Disorder) :
          Fpoly j N i (latticePoint (m j) x) ω =
            heatStartLogClamp (R j)
              (∫ p, heatKernel (δ i) (p.1 - cellSample (m j) x) *
                Real.exp (h₀ i p.2) ∂polymerMeasure ϑ N (s i) T ω) := by
        have hrep : latticeRepresentative (m j) (latticePoint (m j) x) =
            cellSample (m j) x := rfl
        dsimp only [Fpoly]
        rw [hrep]
      have herr := polymer_log_profile_cellSample_error ϑ hN
        (s i) T (δ i) ⟨(hs i).1, (hs i).2.1⟩ (hs i).2.2 (h₀ i)
        (R j) (η j) (Mprof i) Ckernel (by positivity)
        (Real.exp_pos _ ) (hMprof i) hCkernel hKernel (hKernelN) (hSqN)
        (m j) (hm j).1 x
      have hrewrite : (fun ω => |F (x, ω) - H (x, ω)|) =
          fun ω => |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω -
            heatStartLogClamp (R j)
              (∫ p, heatKernel (δ i) (p.1 - cellSample (m j) x) *
                Real.exp (h₀ i p.2) ∂polymerMeasure ϑ N (s i) T ω)| := by
        funext ω
        dsimp only [F]
        rw [hsample ω, hsampleEq ω]
      rw [hrewrite]
      calc
        _ ≤ Mprof i / R j + Real.exp (R j) *
              (Real.exp ‖h₀ i‖ * η j) +
              Real.exp (R j) * (‖heatStartExpTerminal (h₀ i)‖ *
                (Ckernel / Real.sqrt (δ i) *
                  (Real.sqrt ((m j : ℝ) / 2))⁻¹)) := herr.2
        _ = Mprof i / R j + Real.exp (R j) *
              (Real.exp ‖h₀ i‖ * η j) + Tglobal := by
          dsimp [Tglobal, g]
          ring
    have hRj : 0 < R j := by
      change 0 < (j : ℝ) + 1
      exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg j) zero_lt_one
    have hEtaj : 0 ≤ η j := (Real.exp_pos (-2 * R j)).le
    have hExpErr : 0 ≤ Real.exp (R j) * (Real.exp ‖h₀ i‖ * η j) :=
      mul_nonneg (Real.exp_nonneg _) (mul_nonneg (Real.exp_nonneg _) hEtaj)
    have hTglobal : 0 ≤ Tglobal := by
      dsimp [Tglobal]
      exact mul_nonneg (Real.exp_nonneg _) <| mul_nonneg
        (mul_nonneg (norm_nonneg _)
          (div_nonneg hCkernel (Real.sqrt_nonneg _)))
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    have hBpoint : 0 ≤ Mprof i / R j + Real.exp (R j) *
        (Real.exp ‖h₀ i‖ * η j) + Tglobal :=
      add_nonneg (add_nonneg (div_nonneg (hMprof i) hRj.le) hExpErr) hTglobal
    have hdiff : Integrable (fun ω => ∫ x, φ i x * (F (x, ω) - H (x, ω))) disorderLaw ∧
        ∫ ω, |∫ x, φ i x * (F (x, ω) - H (x, ω))| ∂disorderLaw ≤
          (Mprof i / R j + Real.exp (R j) * (Real.exp ‖h₀ i‖ * η j) + Tglobal) *
            (∫ x, |φ i x|) := by
      have hpoint' : ∀ x, φ i x ≠ 0 →
          ∫ ω, |F (x, ω) - H (x, ω)| ∂disorderLaw ≤
            Mprof i / R j + Real.exp (R j) * (Real.exp ‖h₀ i‖ * η j) + Tglobal :=
        fun x hx => hpoint x hx
      exact integral_test_field_difference_l1_on_support_le
        (P := disorderLaw) (F := F) (G := H) (φ := φ i)
        (hF := hFprod) (hG := hHprod) (hsec := hsec) (B :=
          Mprof i / R j + Real.exp (R j) * (Real.exp ‖h₀ i‖ * η j) + Tglobal)
        (_hB := hBpoint) (hpoint := hpoint')
    have hIntY (ω : Disorder) :
        (∫ x, φ i x * H (x, ω)) = Y j N ω i := by
      simpa only [Y, H, Hpoly] using
        integral_test_latticeSiteSum_eq (φ := φ i) (m j) (S j)
          (fun z => Fpoly j N i z ω) (fun x hx => hS j i x hx)
    have hFsecInt : ∀ᵐ ω ∂disorderLaw,
        Integrable (fun x => φ i x * F (x, ω)) := hFprod.prod_left_ae
    have hHsecInt : ∀ᵐ ω ∂disorderLaw,
        Integrable (fun x => φ i x * H (x, ω)) := hHprod.prod_left_ae
    have hsections : ∀ᵐ ω ∂disorderLaw,
        Integrable (fun x => φ i x * F (x, ω)) ∧
        Integrable (fun x => φ i x * H (x, ω)) := hFsecInt.and hHsecInt
    have hdiffEq (ω : Disorder) (hFω : Integrable (fun x => φ i x * F (x, ω)))
        (hHω : Integrable (fun x => φ i x * H (x, ω))) : X N ω i - Y j N ω i =
        ∫ x, φ i x * (F (x, ω) - H (x, ω)) := by
      dsimp only [X]
      rw [← hIntY]
      calc
        (∫ x, φ i x * F (x, ω)) - ∫ x, φ i x * H (x, ω) =
            ∫ x, (φ i x * F (x, ω) - φ i x * H (x, ω)) :=
              (integral_sub hFω hHω).symm
        _ = ∫ x, φ i x * (F (x, ω) - H (x, ω)) := by
          congr 1
          funext x
          ring
    refine ⟨?_, ?_⟩
    · apply (hdiff.1.norm).congr
      filter_upwards [hsections] with ω hω
      rw [hdiffEq ω hω.1 hω.2]
      simp [Real.norm_eq_abs]
    · have hBcomp : (Mprof i / R j + Real.exp (R j) *
          (Real.exp ‖h₀ i‖ * η j) + Tglobal) * (∫ x, |φ i x|) ≤
          (Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
            (∫ x, |φ i x|) + (R j)⁻¹ := by
        have hEta : Real.exp (R j) * (Real.exp ‖h₀ i‖ * η j) =
            Real.exp ‖h₀ i‖ * Real.exp (-R j) := by
          dsimp [η]
          calc
            _ = Real.exp ‖h₀ i‖ * (Real.exp (R j) * Real.exp (-2 * R j)) := by ring
            _ = Real.exp ‖h₀ i‖ * Real.exp (R j + (-2 * R j)) := by
              rw [← Real.exp_add]
            _ = _ := by congr 2; ring
        rw [hEta]
        calc
          _ = (Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
                (∫ x, |φ i x|) + Tglobal * (∫ x, |φ i x|) := by ring
          _ ≤ (Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
                (∫ x, |φ i x|) + (R j)⁻¹ := add_le_add le_rfl hshiftB
      have hb := hdiff.2
      calc
        _ = ∫ ω, |∫ x, φ i x * (F (x, ω) - H (x, ω))| ∂disorderLaw := by
          apply integral_congr_ae
          filter_upwards [hsections] with ω hω
          rw [hdiffEq ω hω.1 hω.2]
        _ ≤ (Mprof i / R j + Real.exp (R j) *
              (Real.exp ‖h₀ i‖ * η j) + Tglobal) * (∫ x, |φ i x|) := hb
        _ ≤ (Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
              (∫ x, |φ i x|) + (R j)⁻¹ := hBcomp
  let Dlim : ℕ → Ω → Fin k → ℝ := fun j ω i => Yl j ω i - L ω i
  have hDlimMeas (j : ℕ) : AEMeasurable (Dlim j) P :=
    (hYlmeas j).sub hLmeas
  have hDlimComp (j : ℕ) (i : Fin k) :
      Integrable (fun ω => ‖Dlim j ω i‖) P ∧
      ∫ ω, ‖Dlim j ω i‖ ∂P ≤ Mlim i / R j * (∫ x, |φ i x|) + (R j)⁻¹ := by
    have h := hlimComp j i
    simpa [Dlim, Real.norm_eq_abs] using h
  have hDlimNormInt (j : ℕ) : Integrable (fun ω => ‖Dlim j ω‖) P := by
    have hsum : Integrable (fun ω => ∑ i : Fin k, ‖Dlim j ω i‖) P :=
      integrable_finsetSum Finset.univ (fun i hi => (hDlimComp j i).1)
    apply hsum.mono' (hDlimMeas j).aestronglyMeasurable.norm
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact pi_norm_le_sum_norm (Dlim j ω)
  have hDlimNormBound (j : ℕ) :
      ∫ ω, ‖Dlim j ω‖ ∂P ≤ Blim j := by
    have hsum : Integrable (fun ω => ∑ i : Fin k, ‖Dlim j ω i‖) P :=
      integrable_finsetSum Finset.univ (fun i hi => (hDlimComp j i).1)
    calc
      _ ≤ ∫ ω, ∑ i : Fin k, ‖Dlim j ω i‖ ∂P := by
        apply integral_mono (hDlimNormInt j) hsum
        intro ω
        exact pi_norm_le_sum_norm (Dlim j ω)
      _ = ∑ i : Fin k, ∫ ω, ‖Dlim j ω i‖ ∂P :=
        integral_finsetSum Finset.univ (fun i hi => (hDlimComp j i).1)
      _ ≤ ∑ i : Fin k, (Mlim i / R j * (∫ x, |φ i x|) + (R j)⁻¹) :=
        Finset.sum_le_sum fun i hi => (hDlimComp j i).2
      _ = Blim j := by simp [Blim]
  have hYlConv : TendstoInDistribution Yl atTop L (fun _ => P) P :=
    tendstoInDistribution_of_integral_norm_bound P Yl L hYlmeas hLmeas
      hDlimNormInt Blim hBlim hDlimNormBound
  have hYlApprox : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖Yl j ω - L ω‖ ∂P ≤ ENNReal.ofReal ε := by
    intro ε hε
    filter_upwards [hBlim.eventually (Iio_mem_nhds hε)] with j hj
    have hlin := ofReal_integral_eq_lintegral_ofReal (hDlimNormInt j)
      (Filter.Eventually.of_forall fun ω => norm_nonneg _)
    change ∫⁻ ω, ENNReal.ofReal ‖Dlim j ω‖ ∂P ≤ ENNReal.ofReal ε
    rw [← hlin]
    exact ENNReal.ofReal_le_ofReal (hDlimNormBound j |>.trans hj.le)
  have hKernelEventual (j : ℕ) : ∀ᶠ N : ℕ in atTop,
      ∀ i : Fin k, ∀ x : Plane,
        ∑' w : Site,
          |srwKernel (evenCeil ((N : ℝ) * δ i)) (w - latticePoint N x) -
            ∫ y in cell N w, heatKernel (δ i) (y - x)| ≤ η j := by
    apply Filter.eventually_all.mpr
    intro i
    have hη : 0 < η j := by dsimp [η]; positivity
    exact (srwKernel_sub_cellHeat_l1_le (δ i) (hs i).2.2 (η j) hη).mono
      fun N hN x => hN x
  have hMomentEventual : ∀ᶠ N : ℕ in atTop, ∀ i : Fin k, ∀ x : Plane,
      Integrable (fun ω => |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω| ^ 2)
        disorderLaw ∧
      ∫ ω, |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω| ^ 2 ∂disorderLaw ≤
        Mprof i := by
    apply Filter.eventually_all.mpr
    intro i
    simpa only [Mprof] using (hCprof i).2
  have hGood (j : ℕ) : ∀ᶠ N : ℕ in atTop,
      1 ≤ N ∧ (∀ i x, ∑' w : Site,
        |srwKernel (evenCeil ((N : ℝ) * δ i)) (w - latticePoint N x) -
          ∫ y in cell N w, heatKernel (δ i) (y - x)| ≤ η j) ∧
      (∀ i x, Integrable (fun ω =>
        |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω| ^ 2) disorderLaw ∧
        ∫ ω, |heatStartLogProfile ϑ N (s i) T (δ i) x (h₀ i) ω| ^ 2 ∂disorderLaw ≤
          Mprof i) := by
    filter_upwards [eventually_ge_atTop 1, hKernelEventual j, hMomentEventual]
      with N hN hK hM
    exact ⟨hN, hK, hM⟩
  have hYmeas : ∀ j N, AEMeasurable (Y j N) disorderLaw := by
    intro j N
    exact (hY j).forall_aemeasurable N
  have hXY : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ᶠ N in atTop,
      ∫⁻ ω, ENNReal.ofReal ‖X N ω - Y j N ω‖ ∂disorderLaw ≤ ENNReal.ofReal ε := by
    intro ε hε
    filter_upwards [hBpoly.eventually (Iio_mem_nhds hε)] with j hj
    filter_upwards [hGood j] with N hN
    rcases hN with ⟨hN, hK, hM⟩
    let D : Disorder → Fin k → ℝ := fun ω => X N ω - Y j N ω
    have hDmeas : AEMeasurable D disorderLaw := (hXmeas N).sub (hYmeas j N)
    have hDint (i : Fin k) : Integrable (fun ω => ‖D ω i‖) disorderLaw := by
      have h := hpolyComp j N i hN (hK i) (hM i)
      simpa [D, Real.norm_eq_abs] using h.1
    have hDcomp (i : Fin k) :
        ∫ ω, ‖D ω i‖ ∂disorderLaw ≤
          (Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
            (∫ x, |φ i x|) + (R j)⁻¹ := by
      have h := hpolyComp j N i hN (hK i) (hM i)
      simpa [D, Real.norm_eq_abs] using h.2
    have hvec := lintegral_norm_pi_le_of_component_bounds disorderLaw D hDmeas
      hDint (fun i =>
        (Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
          (∫ x, |φ i x|) + (R j)⁻¹) hDcomp
    have hsum : (∑ i : Fin k,
        ((Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
          (∫ x, |φ i x|) + (R j)⁻¹)) = Bpoly j := by simp [Bpoly]
    calc
      _ ≤ ENNReal.ofReal (∑ i : Fin k,
          ((Mprof i / R j + Real.exp ‖h₀ i‖ * Real.exp (-R j)) *
            (∫ x, |φ i x|) + (R j)⁻¹)) := by
        simpa only [D] using hvec
      _ = ENNReal.ofReal (Bpoly j) := by rw [hsum]
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hj.le
  exact tendstoInDistribution_of_approx X Y Yl L hY hYlApprox hXY hXmeas hLmeas

end Critical2DKPZ.JointConvergence

end
