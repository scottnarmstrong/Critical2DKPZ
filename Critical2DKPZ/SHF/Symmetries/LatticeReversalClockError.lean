/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.LatticeReversalRounding
public import Critical2DKPZ.Polymer.Locality

/-! # Endpoint errors for moving even lattice clocks -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Moments
open scoped CompactlySupported Topology

namespace Critical2DKPZ.SHF.Symmetries

/-- Markov's inequality for a real-valued function on a finite measure space,
stated with the real-valued measure of its distance level set. -/
theorem measureReal_dist_le_integral_abs {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → ℝ)
    (hf : Integrable (fun ω => |f ω|) μ)
    {δ : ℝ} (hδ : 0 < δ) :
    μ.real {ω | δ ≤ dist (f ω) 0} ≤ (∫ ω, |f ω| ∂μ) / δ := by
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun ω => abs_nonneg (f ω)) hf δ
  have hsubset : {ω | δ ≤ dist (f ω) 0} ⊆ {ω | δ ≤ |f ω|} := by
    intro ω hω
    simpa [Real.dist_eq] using hω
  apply (le_div_iff₀ hδ).2
  calc
    μ.real {ω | δ ≤ dist (f ω) 0} * δ =
        δ * μ.real {ω | δ ≤ dist (f ω) 0} := by ring
    _ ≤ δ * μ.real {ω | δ ≤ |f ω|} :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hδ.le
    _ ≤ ∫ ω, |f ω| ∂μ := hMarkov

private theorem indepFun_pathWeight_pointToPoint (β : ℝ) (u : ℕ)
    (s : Fin 2 → Fin 4) (a n : ℕ) (x z y : Site)
    (hdisj : u + 2 ≤ a ∨ a + n ≤ u) :
    IndepFun (Polymer.pathWeight β u x s)
      (pointToPoint β a n z y) disorderLaw := by
  have hblocks : Indep (Gaussian.disorderBlock u (u + 2))
      (Gaussian.disorderBlock a (a + n)) disorderLaw := by
    rcases hdisj with h | h
    · exact Gaussian.indep_disorderBlock_of_le h
    · exact (Gaussian.indep_disorderBlock_of_le h).symm
  have hfirst : Measurable[Gaussian.disorderBlock u (u + 2)]
      (Polymer.pathWeight β u x s) :=
    Polymer.measurable_pathWeight_block β u x s
  have hsecond : Measurable[Gaussian.disorderBlock a (a + n)]
      (pointToPoint β a n z y) :=
    Polymer.measurable_pointToPoint_block β a n z y
  exact ProbabilityTheory.indep_of_indep_of_le hblocks hfirst.comap_le hsecond.comap_le

/-- A two-step endpoint path-weight error factors from a point-to-point kernel
whose time block is disjoint from the endpoint block. -/
theorem integral_abs_pathWeightError_mul_pointToPoint_eq (β : ℝ) (u : ℕ)
    (s : Fin 2 → Fin 4) (a n : ℕ) (x z y : Site)
    (hdisj : u + 2 ≤ a ∨ a + n ≤ u) :
    ∫ ω, |Polymer.pathWeight β u x s ω - 1| *
        pointToPoint β a n z y ω ∂disorderLaw =
      (∫ ω, |Polymer.pathWeight β u x s ω - 1| ∂disorderLaw) *
        srwKernel n (y - z) := by
  have hweight : Integrable
      (fun ω => |Polymer.pathWeight β u x s ω - 1|) disorderLaw :=
    ((Polymer.integrable_pathWeight β u x s).sub (integrable_const _)).norm
  have hkernel : Integrable (pointToPoint β a n z y) disorderLaw :=
    Polymer.integrable_pointToPoint β a n z y
  have hind := (indepFun_pathWeight_pointToPoint β u s a n x z y hdisj).comp
    (show Measurable (fun z : ℝ => |z - 1|) by fun_prop) measurable_id
  have hfactor : ∫ ω, |Polymer.pathWeight β u x s ω - 1| *
      pointToPoint β a n z y ω ∂disorderLaw =
      (∫ ω, |Polymer.pathWeight β u x s ω - 1| ∂disorderLaw) *
        ∫ ω, pointToPoint β a n z y ω ∂disorderLaw := by
    simpa [Function.comp_apply] using
      hind.integral_fun_mul_eq_mul_integral hweight.aestronglyMeasurable
        hkernel.aestronglyMeasurable
  rw [hfactor, Polymer.integral_pointToPoint]

/-- The product of the short-path error and the point-to-point kernel on a disjoint time interval is integrable, and its expectation factors into their expectations. -/
theorem integrable_abs_pathWeightError_mul_pointToPoint (β : ℝ) (u : ℕ)
    (s : Fin 2 → Fin 4) (a n : ℕ) (x z y : Site)
    (hdisj : u + 2 ≤ a ∨ a + n ≤ u) :
    Integrable (fun ω => |Polymer.pathWeight β u x s ω - 1| *
      pointToPoint β a n z y ω) disorderLaw := by
  have hweight : Integrable
      (fun ω => |Polymer.pathWeight β u x s ω - 1|) disorderLaw :=
    ((Polymer.integrable_pathWeight β u x s).sub (integrable_const _)).norm
  have hkernel : Integrable (pointToPoint β a n z y) disorderLaw :=
    Polymer.integrable_pointToPoint β a n z y
  have hind := (indepFun_pathWeight_pointToPoint β u s a n x z y hdisj).comp
    (show Measurable (fun z : ℝ => |z - 1|) by fun_prop) measurable_id
  have h := hind.integrable_mul hweight hkernel
  have hfun :
      (fun ω => |Polymer.pathWeight β u x s ω - 1| *
        pointToPoint β a n z y ω) =
      ((fun z : ℝ => |z - 1|) ∘ Polymer.pathWeight β u x s) *
        (id ∘ pointToPoint β a n z y) := by
    funext ω
    rfl
  rw [hfun]
  exact h

/-- Split a two-step terminal extension into its finitely many final paths. -/
theorem pointToPoint_terminalTwoStep_eq_sum (β : ℝ) (a n : ℕ)
    (x y : Site) (ω : Disorder) :
    pointToPoint β a (n + 2) x y ω =
      ∑ s : Fin 2 → Fin 4,
        (4 : ℝ)⁻¹ ^ 2 *
          pointToPoint β a n x (y - walkPosition 0 s 2) ω *
            Critical2DKPZ.Polymer.pathWeight β (a + n) (y - walkPosition 0 s 2) s ω := by
  rw [Critical2DKPZ.Polymer.pointToPoint_chapmanKolmogorov]
  simp_rw [Critical2DKPZ.Polymer.pointToPoint_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro s hs
    let z := y - walkPosition 0 s 2
    have hendpoint (w : Site) : walkPosition w s 2 = y ↔ w = z := by
      rw [Polymer.walkPosition_eq_start_add]
      constructor
      · intro h
        dsimp [z]
        calc
          w = (w + walkPosition 0 s 2) - walkPosition 0 s 2 := by abel
          _ = y - walkPosition 0 s 2 := by rw [h]
      · rintro rfl
        simp [z]
    rw [tsum_eq_single z]
    · simp only [hendpoint, ite_true, mul_one]
      dsimp [z]
      calc
        (∑ i : Fin n → Fin 4,
            (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β a x i ω *
              if walkPosition x i n = y - walkPosition 0 s 2 then 1 else 0) *
            ((4 : ℝ)⁻¹ ^ 2 * Polymer.pathWeight β (a + n)
              (y - walkPosition 0 s 2) s ω) =
          ((4 : ℝ)⁻¹ ^ 2 *
              (∑ i : Fin n → Fin 4,
                (4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β a x i ω *
                  if walkPosition x i n = y - walkPosition 0 s 2 then 1 else 0)) *
            Polymer.pathWeight β (a + n) (y - walkPosition 0 s 2) s ω := by ring
        _ = (∑ i : Fin n → Fin 4,
              (4 : ℝ)⁻¹ ^ 2 *
                ((4 : ℝ)⁻¹ ^ n * Polymer.pathWeight β a x i ω *
                  if walkPosition x i n = y - walkPosition 0 s 2 then 1 else 0)) *
            Polymer.pathWeight β (a + n) (y - walkPosition 0 s 2) s ω := by
          rw [Finset.mul_sum]
    · intro w hw
      have hwz : w ≠ z := by simpa using hw
      simp [hendpoint, hwz]
  · intro s hs
    let z := y - walkPosition 0 s 2
    have hendpoint (w : Site) : walkPosition w s 2 = y ↔ w = z := by
      rw [Polymer.walkPosition_eq_start_add]
      constructor
      · intro h
        dsimp [z]
        calc
          w = (w + walkPosition 0 s 2) - walkPosition 0 s 2 := by abel
          _ = y - walkPosition 0 s 2 := by rw [h]
      · rintro rfl
        simp [z]
    apply summable_of_ne_finset_zero (s := {z})
    intro w hw
    have hwz : w ≠ z := by simpa using hw
    simp [hendpoint, hwz]

/-- A compact pairing is insensitive in probability to its initial Boltzmann
factor when the even lattice window varies with the scale and stays macroscopically
long. -/
theorem tendstoInMeasure_startEndpointPairingError_evenClock (ϑ : ℝ) {ε : ℝ}
    (hε : 0 < ε) (a b : ℕ → ℕ) (ha : ∀ N, Even (a N)) (hb : ∀ N, Even (b N))
    (hgap : ∀ᶠ N : ℕ in atTop, ε * N ≤ b N - a N)
    (φ : C_c(Plane × Plane, ℝ)) :
    TendstoInMeasure disorderLaw
      (fun N ω => ∫ p, φ p *
        ((Real.exp (criticalBeta ϑ N * ω
            (a N, latticePoint N p.1)) - 1) *
          rescaledP2P ϑ N ((a N : ℝ) / N) ((b N : ℝ) / N) p ω))
      atTop (fun _ => 0) := by
  obtain ⟨C, hC, hkernelMass⟩ := exists_tsum_compactAbs_cellKernel_bound hε φ
  have hroot : Tendsto (fun N : ℕ => Real.sqrt
      (Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
        2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1)) atTop (𝓝 0) := by
    exact tendsto_expPairingError_root ϑ
  let f : ℕ → Disorder → ℝ := fun N ω => ∫ p, φ p *
    ((Real.exp (criticalBeta ϑ N * ω (a N, latticePoint N p.1)) - 1) *
      rescaledP2P ϑ N ((a N : ℝ) / N) ((b N : ℝ) / N) p ω)
  have hL1 : Tendsto (fun N => ∫ ω, |f N ω| ∂disorderLaw) atTop (𝓝 0) := by
    have hbound : ∀ᶠ N : ℕ in atTop,
        (∫ ω, |f N ω| ∂disorderLaw) ≤
          Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
            2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1) *
            (C * ∫ p, compactAbs φ p) := by
      filter_upwards [eventually_gt_atTop 0, hgap] with N hN hgapN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hNreal : (N : ℝ) ≠ 0 := ne_of_gt hNr
      have haClock : evenCeil ((N : ℝ) * ((a N : ℝ) / N)) = a N := by
        rw [show (N : ℝ) * ((a N : ℝ) / N) = (a N : ℝ) by field_simp]
        exact evenCeil_natCast_of_even (ha N)
      have hbClock : evenCeil ((N : ℝ) * ((b N : ℝ) / N)) = b N := by
        rw [show (N : ℝ) * ((b N : ℝ) / N) = (b N : ℝ) by field_simp]
        exact evenCeil_natCast_of_even (hb N)
      have habR : (a N : ℝ) ≤ b N := by
        have hpos : 0 < ε * (N : ℝ) := mul_pos hε hNr
        linarith
      have hab : a N ≤ b N := by exact_mod_cast habR
      have hgapNat : ε * (N : ℝ) ≤ ((b N - a N : ℕ) : ℝ) := by
        rw [Nat.cast_sub hab]
        exact hgapN
      have hmass := hkernelMass N (b N - a N) hgapNat
      have hmass' : ∑' q : Site × Site,
          cellTestWeight N (compactAbs φ) q.1 q.2 *
            srwKernel (evenCeil ((N : ℝ) * ((b N : ℝ) / N)) -
              evenCeil ((N : ℝ) * ((a N : ℝ) / N))) (q.2 - q.1) ≤
          C * ∫ p, compactAbs φ p := by
        simpa only [haClock, hbClock] using hmass
      have herr := integral_abs_pairing_startEndpoint_error_le ϑ φ C hmass'
      change (∫ ω, |f N ω| ∂disorderLaw) ≤ _
      calc
        _ ≤ Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
            2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1) * C *
              ∫ p, compactAbs φ p := by
          simpa only [f, haClock, hbClock] using herr.2
        _ = Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
            2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1) *
              (C * ∫ p, compactAbs φ p) := by ring
    have hnonneg (N : ℕ) : 0 ≤ ∫ ω, |f N ω| ∂disorderLaw :=
      integral_nonneg fun ω => abs_nonneg (f N ω)
    have hupper : Tendsto (fun N : ℕ =>
        Real.sqrt (Real.exp (2 * (criticalBeta ϑ N) ^ 2) -
          2 * Real.exp ((criticalBeta ϑ N) ^ 2 / 2) + 1) *
          (C * ∫ p, compactAbs φ p)) atTop (𝓝 0) := by
      simpa only [zero_mul] using hroot.mul_const (C * ∫ p, compactAbs φ p)
    exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hbound hupper
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro δ hδ
  have hmarkov : ∀ᶠ N : ℕ in atTop,
      disorderLaw.real {ω | δ ≤ dist (f N ω) (0 : ℝ)} ≤
        (∫ ω, |f N ω| ∂disorderLaw) / δ := by
    filter_upwards [eventually_gt_atTop 0, hgap] with N hN hgapN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have haClock : evenCeil ((N : ℝ) * ((a N : ℝ) / N)) = a N := by
      rw [show (N : ℝ) * ((a N : ℝ) / N) = (a N : ℝ) by field_simp]
      exact evenCeil_natCast_of_even (ha N)
    have hbClock : evenCeil ((N : ℝ) * ((b N : ℝ) / N)) = b N := by
      rw [show (N : ℝ) * ((b N : ℝ) / N) = (b N : ℝ) by field_simp]
      exact evenCeil_natCast_of_even (hb N)
    have habR : (a N : ℝ) ≤ b N := by
      have hpos : 0 < ε * (N : ℝ) := mul_pos hε hNr
      linarith
    have hab : a N ≤ b N := by exact_mod_cast habR
    have hgapNat : ε * (N : ℝ) ≤ ((b N - a N : ℕ) : ℝ) := by
      rw [Nat.cast_sub hab]
      exact hgapN
    have hmass := hkernelMass N (b N - a N) hgapNat
    have hmass' : ∑' q : Site × Site,
        cellTestWeight N (compactAbs φ) q.1 q.2 *
          srwKernel (evenCeil ((N : ℝ) * ((b N : ℝ) / N)) -
            evenCeil ((N : ℝ) * ((a N : ℝ) / N))) (q.2 - q.1) ≤
        C * ∫ p, compactAbs φ p := by
      simpa only [haClock, hbClock] using hmass
    have herr := integral_abs_pairing_startEndpoint_error_le ϑ φ C hmass'
    have hint : Integrable (fun ω => |f N ω|) disorderLaw := by
      simpa only [f, haClock, hbClock, Real.norm_eq_abs] using herr.1.norm
    exact measureReal_dist_le_integral_abs disorderLaw (f N) hint hδ
  have hlim := hL1.div_const δ
  have hresult : Tendsto (fun N : ℕ => disorderLaw.real
      {ω | δ ≤ dist (f N ω) (0 : ℝ)}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [zero_div] using hlim)
      (Filter.Eventually.of_forall fun N => measureReal_nonneg) hmarkov
  simpa only [f] using hresult

end Critical2DKPZ.SHF.Symmetries

end
