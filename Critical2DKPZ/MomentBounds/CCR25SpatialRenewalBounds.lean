/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialRenewalHatGaussian
public import Critical2DKPZ.MomentBounds.WeightedLatticeKernel
public import Critical2DKPZ.MomentBounds.CSZ25Green
public import Critical2DKPZ.Renewal.Sequence
public import Critical2DKPZ.Renewal.Subcritical
import Mathlib.Tactic

/-! # Exponential moment bounds for CCR25 spatial renewal profiles -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem weighted_hatGaussian_le_half_rate {c t : ℝ} (hc : 0 < c)
    {n : ℕ} (hn : 1 ≤ n) (x : Site) :
    Real.exp (t * ‖siteToPlane x‖) * Collision.hatGaussian c n x ≤
      Real.exp (t ^ 2 * n / (2 * c)) * Collision.hatGaussian (c / 2) n x := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans_le hn)
  have hr : 0 ≤ ‖siteToPlane x‖ := norm_nonneg _
  by_cases hp : Even ((n : ℤ) + x 0 + x 1)
  · simp only [Collision.hatGaussian, hn0, hp, ↓reduceIte]
    have hexp : Real.exp (t * ‖siteToPlane x‖) *
          Real.exp (-(c * ‖siteToPlane x‖ ^ 2) / n) ≤
        Real.exp (t ^ 2 * n / (2 * c)) *
          Real.exp (-((c / 2) * ‖siteToPlane x‖ ^ 2) / n) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have harg : t * ‖siteToPlane x‖ - c * ‖siteToPlane x‖ ^ 2 / n ≤
          t ^ 2 * n / (2 * c) - (c / 2) * ‖siteToPlane x‖ ^ 2 / n := by
        apply le_of_mul_le_mul_right ?_ (by positivity : 0 < 2 * c * n)
        field_simp [ne_of_gt hc, ne_of_gt hnR]
        nlinarith [sq_nonneg (t * n - c * ‖siteToPlane x‖)]
      convert harg using 1 <;> ring
    calc
      _ = (n : ℝ)⁻¹ * (Real.exp (t * ‖siteToPlane x‖) *
            Real.exp (-(c * ‖siteToPlane x‖ ^ 2) / n)) := by ring
      _ ≤ (n : ℝ)⁻¹ * (Real.exp (t ^ 2 * n / (2 * c)) *
            Real.exp (-((c / 2) * ‖siteToPlane x‖ ^ 2) / n)) :=
        mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = _ := by ring
  · simp [Collision.hatGaussian, hn0, hp]

private theorem weighted_hatGaussian_summable_and_bound {c t : ℝ}
    (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    Summable (fun x : Site => Real.exp (t * ‖siteToPlane x‖) * Collision.hatGaussian c n x) ∧
      (∑' x : Site, Real.exp (t * ‖siteToPlane x‖) * Collision.hatGaussian c n x) ≤
        (1 + Real.sqrt (Real.pi / (c / 2))) ^ 2 * Real.exp (t ^ 2 * n / (2 * c)) := by
  have hc2 : 0 < c / 2 := by positivity
  have hhatSummable := Collision.hatGaussian_summable hc2 hn
  have hpoint := weighted_hatGaussian_le_half_rate (t := t) hc hn
  have hmajor : Summable (fun x : Site =>
      Real.exp (t ^ 2 * n / (2 * c)) * Collision.hatGaussian (c / 2) n x) :=
    hhatSummable.mul_left _
  have hsum := hmajor.of_nonneg_of_le
    (fun x => mul_nonneg (Real.exp_nonneg _) (Collision.hatGaussian_nonneg _ _)) hpoint
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' x : Site,
        Real.exp (t ^ 2 * n / (2 * c)) * Collision.hatGaussian (c / 2) n x :=
      hsum.tsum_le_tsum hpoint hmajor
    _ = Real.exp (t ^ 2 * n / (2 * c)) *
          ∑' x : Site, Collision.hatGaussian (c / 2) n x := tsum_mul_left
    _ ≤ Real.exp (t ^ 2 * n / (2 * c)) *
          (1 + Real.sqrt (Real.pi / (c / 2))) ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact Collision.hatGaussian_totalMass_le hc2 hn
      · exact (Real.exp_pos _).le
    _ = _ := by ring

private theorem spatialRenewal_nonneg_of_nonneg {σ2 : ℝ} (hσ : 0 ≤ σ2) :
    ∀ n : ℕ, ∀ x : Site, 0 ≤ Collision.spatialRenewal σ2 n x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x
      by_cases hn : n = 0
      · subst n
        simp only [Collision.spatialRenewal_zero]
        split_ifs <;> positivity
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        rw [Collision.spatialRenewal_succ]
        apply Finset.sum_nonneg
        intro m hm
        apply tsum_nonneg
        intro z
        exact mul_nonneg (mul_nonneg (ih m.val (by omega) z) hσ) (sq_nonneg _)

private theorem spatialRenewal_supported {σ2 : ℝ} (n : ℕ) {x : Site}
    (hx : x ∉ Critical2DKPZ.Polymer.endpoints 0 n) : Collision.spatialRenewal σ2 n x = 0 := by
  cases n with
  | zero =>
      have hx0 : x ≠ 0 := by
        intro h
        apply hx
        subst x
        simp [Critical2DKPZ.Polymer.endpoints, Critical2DKPZ.walkPosition]
      simp [Collision.spatialRenewal_zero, hx0]
  | succ n =>
      rw [Collision.spatialRenewal_eq_sum_compositions σ2 (by omega) x]
      apply Finset.sum_eq_zero
      intro c hc
      have hnot : x ∉ Critical2DKPZ.Polymer.endpoints 0 c.blocks.sum := by
        simpa [c.blocks_sum] using hx
      rw [Collision.squareConvolution_eq_zero_of_not_mem_endpoints hnot]
      simp

private theorem tsum_finiteConvolution_mass (F G : Site → ℝ)
    (sF sG : Finset Site) (hF : ∀ z ∉ sF, F z = 0) (hG : ∀ z ∉ sG, G z = 0) :
    (∑' x : Site, ∑' z : Site, F z * G (x - z)) =
      (∑' z : Site, F z) * (∑' y : Site, G y) := by
  classical
  let sX : Finset Site := sF.biUnion fun z => sG.image fun y => z + y
  have hdouble : Summable (fun p : Site × Site => F p.2 * G (p.1 - p.2)) := by
    apply summable_of_ne_finset_zero (s := sX ×ˢ sF)
    intro p hp
    by_cases hz : p.2 ∈ sF
    · by_cases hy : p.1 - p.2 ∈ sG
      · have hx : p.1 ∈ sX := by
          apply Finset.mem_biUnion.mpr
          refine ⟨p.2, hz, ?_⟩
          apply Finset.mem_image.mpr
          refine ⟨p.1 - p.2, hy, ?_⟩
          simp
        exact (hp (Finset.mem_product.mpr ⟨hx, hz⟩)).elim
      · rw [hG (p.1 - p.2) hy]
        simp
    · rw [hF p.2 hz]
      simp
  calc
    _ = ∑' x : Site, ∑' z : Site, F z * G (x - z) := rfl
    _ = ∑' z : Site, ∑' x : Site, F z * G (x - z) :=
      (Summable.tsum_comm (f := fun x z : Site => F z * G (x - z)) hdouble).symm
    _ = ∑' z : Site, F z * ∑' x : Site, G (x - z) := by
      apply tsum_congr
      intro z
      rw [← tsum_mul_left]
    _ = ∑' z : Site, F z * ∑' y : Site, G y := by
      apply tsum_congr
      intro z
      have hshift :
          (∑' x : Site, G (x - z)) = ∑' y : Site, G y := by
        calc
          _ = ∑' y : Site, G ((Equiv.addLeft z y) - z) :=
            (Equiv.addLeft z).tsum_eq (fun x : Site => G (x - z)) |>.symm
          _ = _ := by
            apply tsum_congr
            intro y
            simp [Equiv.addLeft]
      rw [hshift]
    _ = _ := by rw [← tsum_mul_right]

private theorem endpoint_translate_local (n : ℕ) (z y : Site)
    (hy : y ∈ Critical2DKPZ.Polymer.endpoints 0 n) :
    z + y ∈ Critical2DKPZ.Polymer.endpoints z n := by
  obtain ⟨s, hs⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff 0 y n).mp hy
  apply (Critical2DKPZ.Polymer.mem_endpoints_iff z (z + y) n).2
  refine ⟨s, ?_⟩
  calc
    Critical2DKPZ.walkPosition z s n = z + Critical2DKPZ.walkPosition 0 s n := by
      simpa using Critical2DKPZ.Polymer.walkPosition_add_start z 0 s n
    _ = z + y := by rw [hs]

private theorem endpoints_add_local {n m : ℕ} {z x : Site}
    (hz : z ∈ Critical2DKPZ.Polymer.endpoints 0 n)
    (hx : x ∈ Critical2DKPZ.Polymer.endpoints z m) :
    x ∈ Critical2DKPZ.Polymer.endpoints 0 (n + m) := by
  obtain ⟨s, hs⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff 0 z n).mp hz
  obtain ⟨t, ht⟩ := (Critical2DKPZ.Polymer.mem_endpoints_iff z x m).mp hx
  apply (Critical2DKPZ.Polymer.mem_endpoints_iff 0 x (n + m)).2
  refine ⟨Fin.append s t, ?_⟩
  rw [Critical2DKPZ.Polymer.walkPosition_append_end, hs]
  exact ht

private theorem spatialRenewal_convolution_supported {σ2 : ℝ} (m r : ℕ) {x : Site}
    (hx : x ∉ Critical2DKPZ.Polymer.endpoints 0 (m + r)) :
    (∑' z : Site, Collision.spatialRenewal σ2 m z *
      Critical2DKPZ.srwKernel r (x - z) ^ 2) = 0 := by
  let E := Critical2DKPZ.Polymer.endpoints (0 : Site) m
  have hzero (z : Site) (hz : z ∉ E) :
      Collision.spatialRenewal σ2 m z * Critical2DKPZ.srwKernel r (x - z) ^ 2 = 0 := by
    rw [spatialRenewal_supported m hz]
    simp
  calc
    _ = ∑ z ∈ E, Collision.spatialRenewal σ2 m z *
          Critical2DKPZ.srwKernel r (x - z) ^ 2 := tsum_eq_sum hzero
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      by_cases hy : x - z ∈ Critical2DKPZ.Polymer.endpoints 0 r
      · have htranslate : x ∈ Critical2DKPZ.Polymer.endpoints z r := by
          have h := endpoint_translate_local r z (x - z) hy
          convert h using 1
          ext i
          simp
        have hx' : x ∈ Critical2DKPZ.Polymer.endpoints 0 (m + r) :=
          endpoints_add_local hz htranslate
        exact (hx hx').elim
      · have h := Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem r 0 (x - z) hy
        have hq : Critical2DKPZ.srwKernel r (x - z) = 0 := by simpa only [sub_zero] using h
        simp [hq]

private theorem tsum_squareKernel_return (r : ℕ) :
    (∑' y : Site, (Critical2DKPZ.srwKernel r y) ^ 2) =
      Critical2DKPZ.srwKernel (2 * r) 0 := by
  simpa [pow_two, sub_zero] using Critical2DKPZ.Polymer.srwKernel_collision r 0 0

private theorem spatialRenewal_mass_recurrence (σ2 : ℝ) (n : ℕ) :
    (∑' x : Site, Collision.spatialRenewal σ2 (n + 1) x) =
      ∑ m : Fin (n + 1), σ2 *
        (∑' z : Site, Collision.spatialRenewal σ2 m.val z) *
          Critical2DKPZ.srwKernel (2 * (n + 1 - m.val)) 0 := by
  classical
  let E := Critical2DKPZ.Polymer.endpoints (0 : Site) (n + 1)
  have hsupp : ∀ x ∉ E, Collision.spatialRenewal σ2 (n + 1) x = 0 :=
    fun x hx => spatialRenewal_supported (n + 1) hx
  calc
    _ = ∑ x ∈ E, Collision.spatialRenewal σ2 (n + 1) x := tsum_eq_sum hsupp
    _ = ∑ x ∈ E, ∑ m : Fin (n + 1), ∑' z : Site,
          Collision.spatialRenewal σ2 m.val z * σ2 *
            Critical2DKPZ.srwKernel (n + 1 - m.val) (x - z) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Collision.spatialRenewal_succ]
    _ = ∑ m : Fin (n + 1), ∑ x ∈ E, ∑' z : Site,
          Collision.spatialRenewal σ2 m.val z * σ2 *
            Critical2DKPZ.srwKernel (n + 1 - m.val) (x - z) ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ m : Fin (n + 1), ∑' x : Site, ∑' z : Site,
          Collision.spatialRenewal σ2 m.val z * σ2 *
            Critical2DKPZ.srwKernel (n + 1 - m.val) (x - z) ^ 2 := by
          apply Finset.sum_congr rfl
          intro m hm
          have hzero (x : Site) (hx : x ∉ E) :
              (∑' z : Site, Collision.spatialRenewal σ2 m.val z * σ2 *
                Critical2DKPZ.srwKernel (n + 1 - m.val) (x - z) ^ 2) = 0 := by
            have hsum : m.val + (n + 1 - m.val) = n + 1 := by omega
            have hconv := spatialRenewal_convolution_supported (σ2 := σ2) m.val
              (n + 1 - m.val) (x := x) (by simpa [hsum] using hx)
            have hrewrite : (∑' z : Site, Collision.spatialRenewal σ2 m.val z * σ2 *
                Critical2DKPZ.srwKernel (n + 1 - m.val) (x - z) ^ 2) =
              σ2 * (∑' z : Site, Collision.spatialRenewal σ2 m.val z *
                Critical2DKPZ.srwKernel (n + 1 - m.val) (x - z) ^ 2) := by
              rw [← tsum_mul_left]
              apply tsum_congr
              intro z
              ring
            rw [hrewrite, hconv]
            simp
          exact (tsum_eq_sum (s := E) hzero).symm
    _ = ∑ m : Fin (n + 1), σ2 *
          (∑' z : Site, Collision.spatialRenewal σ2 m.val z) *
            Critical2DKPZ.srwKernel (2 * (n + 1 - m.val)) 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          let r := n + 1 - m.val
          have hr : 1 ≤ r := by dsimp [r]; omega
          have hF (z : Site) (hz : z ∉ Critical2DKPZ.Polymer.endpoints 0 m.val) :
              Collision.spatialRenewal σ2 m.val z = 0 := spatialRenewal_supported m.val hz
          have hG (z : Site) (hz : z ∉ Critical2DKPZ.Polymer.endpoints 0 r) :
              (Critical2DKPZ.srwKernel r z) ^ 2 = 0 := by
            have h := Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem r 0 z hz
            have hq : Critical2DKPZ.srwKernel r z = 0 := by simpa only [sub_zero] using h
            simp [hq]
          have hconv := tsum_finiteConvolution_mass
            (fun z => Collision.spatialRenewal σ2 m.val z)
            (fun z => (Critical2DKPZ.srwKernel r z) ^ 2)
            (Critical2DKPZ.Polymer.endpoints 0 m.val)
            (Critical2DKPZ.Polymer.endpoints 0 r) hF hG
          rw [show n + 1 - m.val = r by rfl]
          calc
            _ = ∑' x : Site, σ2 *
                (∑' z : Site, Collision.spatialRenewal σ2 m.val z *
                  Critical2DKPZ.srwKernel r (x - z) ^ 2) := by
                    apply tsum_congr
                    intro x
                    rw [← tsum_mul_left]
                    apply tsum_congr
                    intro z
                    ring
            _ = σ2 * (∑' x : Site, ∑' z : Site,
                Collision.spatialRenewal σ2 m.val z *
                  Critical2DKPZ.srwKernel r (x - z) ^ 2) := tsum_mul_left
            _ = σ2 * ((∑' z : Site, Collision.spatialRenewal σ2 m.val z) *
                (∑' y : Site, (Critical2DKPZ.srwKernel r y) ^ 2)) := by
                  rw [tsum_finiteConvolution_mass
                    (fun z => Collision.spatialRenewal σ2 m.val z)
                    (fun y => (Critical2DKPZ.srwKernel r y) ^ 2)
                    (Critical2DKPZ.Polymer.endpoints 0 m.val)
                    (Critical2DKPZ.Polymer.endpoints 0 r) hF hG]
            _ = σ2 * (∑' z : Site, Collision.spatialRenewal σ2 m.val z) *
                  Critical2DKPZ.srwKernel (2 * r) 0 := by
                  rw [tsum_squareKernel_return]
                  ring

private theorem sum_Icc_one_succ_eq_fin_local {n : ℕ} (f : ℕ → ℝ) :
    ∑ r ∈ Finset.Icc 1 (n + 1), f r = ∑ m : Fin (n + 1), f (n + 1 - m.val) := by
  classical
  refine Finset.sum_bij (fun r hr => ⟨n + 1 - r, by
    have hr := Finset.mem_Icc.mp hr
    omega⟩) ?_ ?_ ?_ ?_
  · intro r hr
    simp
  · intro r₁ hr₁ r₂ hr₂ heq
    have hr₁' : r₁ ≤ n + 1 := (Finset.mem_Icc.mp hr₁).2
    have hr₂' : r₂ ≤ n + 1 := (Finset.mem_Icc.mp hr₂).2
    have hval : n + 1 - r₁ = n + 1 - r₂ := congrArg Fin.val heq
    exact (tsub_right_inj hr₁' hr₂').mp hval
  · intro m hm
    refine ⟨n + 1 - m.val, ?_, ?_⟩
    · have hm' := m.isLt
      simp only [Finset.mem_Icc]
      omega
    · apply Fin.ext
      change n + 1 - (n + 1 - m.val) = m.val
      exact Nat.sub_sub_self (by omega)
  · intro r hr
    have hrle : r ≤ n + 1 := (Finset.mem_Icc.mp hr).2
    change f r = f (n + 1 - (n + 1 - r))
    congr 1
    exact (Nat.sub_sub_self hrle).symm

private theorem renewalMass_succ_fin_local (w : ℕ → ℝ) (n : ℕ) :
    Renewal.renewalMass w (n + 1) =
      ∑ m : Fin (n + 1), w (n + 1 - m.val) * Renewal.renewalMass w m.val := by
  rw [Renewal.renewalMass_succ]
  calc
    _ = ∑ m : Fin (n + 1),
          w (n + 1 - m.val) * Renewal.renewalMass w (n + 1 - (n + 1 - m.val)) :=
      sum_Icc_one_succ_eq_fin_local
        (fun r => w r * Renewal.renewalMass w (n + 1 - r))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      simp [Nat.sub_sub_self (by omega : m.val ≤ n + 1)]

private theorem spatialRenewal_dampedMass_eq_renewalMass (σ2 lam : ℝ) (n : ℕ) :
    Real.exp (-lam * n) * (∑' x : Site, Collision.spatialRenewal σ2 n x) =
      Renewal.renewalMass
        (fun r => σ2 * Real.exp (-lam * r) * Critical2DKPZ.srwKernel (2 * r) 0) n := by
  let w : ℕ → ℝ := fun r => σ2 * Real.exp (-lam * r) *
    Critical2DKPZ.srwKernel (2 * r) 0
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        have hmass : ∑' x : Site, Collision.spatialRenewal σ2 0 x = 1 := by
          simp [Collision.spatialRenewal_zero, tsum_ite_eq]
        simp [Collision.spatialRenewal_zero, tsum_ite_eq, Renewal.renewalMass_zero]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        have hrec := spatialRenewal_mass_recurrence σ2 k
        rw [hrec, renewalMass_succ_fin_local]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        let r : ℕ := k + 1 - m.val
        have hsum : m.val + r = k + 1 := by
          dsimp [r]
          exact Nat.add_sub_of_le (Nat.le_of_lt m.isLt)
        have hExp : Real.exp (-lam * (k + 1 : ℕ)) =
            Real.exp (-lam * r) * Real.exp (-lam * m.val) := by
          rw [← Real.exp_add]
          congr 1
          have hsumR : (m.val : ℝ) + (r : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hsum
          norm_num
          rw [← hsumR]
          ring
        have hih := ih m.val (by omega)
        calc
          Real.exp (-lam * (k + 1 : ℕ)) *
              (σ2 * (∑' z : Site, Collision.spatialRenewal σ2 m.val z) *
                Critical2DKPZ.srwKernel (2 * r) 0) =
            (σ2 * Real.exp (-lam * r) * Critical2DKPZ.srwKernel (2 * r) 0) *
              (Real.exp (-lam * m.val) *
                ∑' z : Site, Collision.spatialRenewal σ2 m.val z) := by
                  rw [hExp]
                  ring
          _ = w r * Renewal.renewalMass w m.val := by
                rw [← hih]


/-- The damped nonzero-time renewal mass is bounded by its geometric resolvent. -/
theorem sum_exp_mul_tsum_spatialRenewal_le {σ2 lam : ℝ} (hσ : 0 ≤ σ2) (_hlam : 0 ≤ lam) (L : ℕ)
    (hsmall : σ2 * dampedOverlap lam L < 1) :
    ∑ m ∈ Finset.range L, Real.exp (-lam * (m + 1 : ℕ)) *
        ∑' x : Site, Collision.spatialRenewal σ2 (m + 1) x ≤
      σ2 * dampedOverlap lam L / (1 - σ2 * dampedOverlap lam L) := by
  let w : ℕ → ℝ := fun r => σ2 * Real.exp (-lam * r) *
    Critical2DKPZ.srwKernel (2 * r) 0
  have hw : ∀ r, 0 ≤ w r := by
    intro r
    dsimp [w]
    exact mul_nonneg (mul_nonneg hσ (Real.exp_nonneg _))
      (Critical2DKPZ.srwKernel_nonneg _ _)
  have hstep : (∑ r ∈ Finset.Icc 1 L, w r) = σ2 * dampedOverlap lam L := by
    unfold w dampedOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  have hsumRange :
      (∑ m ∈ Finset.range L, Real.exp (-lam * (m + 1 : ℕ)) *
          ∑' x : Site, Collision.spatialRenewal σ2 (m + 1) x) =
        ∑ n ∈ Finset.Icc 1 L, Renewal.renewalMass w n := by
    calc
      _ = ∑ m ∈ Finset.range L,
          Renewal.renewalMass w (m + 1) := by
            apply Finset.sum_congr rfl
            intro m hm
            simpa [w] using (spatialRenewal_dampedMass_eq_renewalMass σ2 lam (m + 1))
      _ = ∑ n ∈ Finset.Icc 1 L, Renewal.renewalMass w n := by
            refine Finset.sum_bij (fun m hm => m + 1) ?_ ?_ ?_ ?_
            · intro m hm
              simp only [Finset.mem_range] at hm
              simp only [Finset.mem_Icc]
              omega
            · intro m hm m' hm' heq
              omega
            · intro n hn
              have hn' := Finset.mem_Icc.mp hn
              refine ⟨n - 1, ?_, ?_⟩
              · simp only [Finset.mem_range]
                omega
              · omega
            · intro m hm
              rfl
  have hrenewal := Renewal.renewalFunction_le_geometric hw L (by rw [hstep]; exact hsmall)
  have hresolvent :
      (∑ n ∈ Finset.Icc 1 L, Renewal.renewalMass w n) ≤
        1 / (1 - σ2 * dampedOverlap lam L) - 1 := by
    have hform : Renewal.renewalFunction w L =
        1 + ∑ n ∈ Finset.Icc 1 L, Renewal.renewalMass w n := rfl
    have h := sub_le_sub_right hrenewal 1
    rw [hform] at h
    simpa [hstep] using h
  rw [hsumRange]
  calc
    _ ≤ 1 / (1 - σ2 * dampedOverlap lam L) - 1 := hresolvent
    _ = σ2 * dampedOverlap lam L / (1 - σ2 * dampedOverlap lam L) := by
      have hden : 0 < 1 - σ2 * dampedOverlap lam L := sub_pos.mpr hsmall
      field_simp
      ring


/-- CCR25's spatial renewal profile has a Gaussian exponential moment bounded
by its total renewal mass, uniformly in its coupling and horizon. -/
theorem tsum_exp_mul_norm_spatialRenewal_le :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ σ2 : ℝ, 0 ≤ σ2 → ∀ t : ℝ, 0 ≤ t → ∀ m : ℕ,
      (∑' x : Site, Real.exp (t * ‖siteToPlane x‖) *
          Collision.spatialRenewal σ2 m x) ≤
        c * Real.exp (2 * c * t ^ 2 * m) *
          ∑' x : Site, Collision.spatialRenewal σ2 m x := by
  obtain ⟨c₀, hc₀, huniform⟩ := Collision.spatialRenewal_le_hatGaussian_uniform
  obtain ⟨Cenv, hCenv, hEnvelope⟩ := huniform c₀ (by positivity) (le_of_eq rfl)
  let c : ℝ := max 1 (max (Cenv * (1 + Real.sqrt (Real.pi / (c₀ / 2))) ^ 2)
    (1 / (4 * c₀)))
  have hc : 1 ≤ c := le_max_left _ _
  have hpref : Cenv * (1 + Real.sqrt (Real.pi / (c₀ / 2))) ^ 2 ≤ c :=
    (le_max_left _ _).trans (le_max_right 1 _)
  have hexpcoef : 1 / (4 * c₀) ≤ c :=
    (le_max_right _ _).trans (le_max_right 1 _)
  refine ⟨c, hc, ?_⟩
  intro σ2 hσ t _ht m
  by_cases hm0 : m = 0
  · subst m
    simpa [Collision.spatialRenewal_zero, tsum_ite_eq, siteToPlane_zero] using hc
  · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hspatialNonneg := spatialRenewal_nonneg_of_nonneg hσ
    have hsupport : ∀ x ∉ Critical2DKPZ.Polymer.endpoints 0 m,
        Collision.spatialRenewal σ2 m x = 0 := fun x hx => spatialRenewal_supported m hx
    have hspatialSummable : Summable (fun x : Site => Collision.spatialRenewal σ2 m x) :=
      summable_of_ne_finset_zero (s := Critical2DKPZ.Polymer.endpoints 0 m) hsupport
    let M : ℝ := ∑' x : Site, Collision.spatialRenewal σ2 m x
    have hM : 0 ≤ M := by
      dsimp [M]
      exact tsum_nonneg (fun x => hspatialNonneg m x)
    have hweightHat := weighted_hatGaussian_summable_and_bound
      (c := c₀) (t := t) hc₀ hm
    have hEnvelopePoint (x : Site) :
        Real.exp (t * ‖siteToPlane x‖) * Collision.spatialRenewal σ2 m x ≤
          Cenv * M * (Real.exp (t * ‖siteToPlane x‖) * Collision.hatGaussian c₀ m x) := by
      have henv := hEnvelope σ2 hσ m hm x
      have henv' := mul_le_mul_of_nonneg_left henv
        (Real.exp_nonneg (t * ‖siteToPlane x‖))
      calc
        _ ≤ Real.exp (t * ‖siteToPlane x‖) * (Cenv * M * Collision.hatGaussian c₀ m x) := henv'
        _ = Cenv * M * (Real.exp (t * ‖siteToPlane x‖) * Collision.hatGaussian c₀ m x) := by ring
    have hmajor : Summable (fun x : Site => Cenv * M *
        (Real.exp (t * ‖siteToPlane x‖) * Collision.hatGaussian c₀ m x)) :=
      hweightHat.1.mul_left (Cenv * M)
    have hsum : Summable (fun x : Site =>
        Real.exp (t * ‖siteToPlane x‖) * Collision.spatialRenewal σ2 m x) :=
      hmajor.of_nonneg_of_le
        (fun x => mul_nonneg (Real.exp_nonneg _) (hspatialNonneg m x)) hEnvelopePoint
    have hsumBound := hsum.tsum_le_tsum hEnvelopePoint hmajor
    have hmassBound :
        ∑' x : Site, Real.exp (t * ‖siteToPlane x‖) *
            Collision.spatialRenewal σ2 m x ≤
          Cenv * M * ((1 + Real.sqrt (Real.pi / (c₀ / 2))) ^ 2 *
            Real.exp (t ^ 2 * m / (2 * c₀))) := by
      calc
        _ ≤ ∑' x : Site, Cenv * M *
            (Real.exp (t * ‖siteToPlane x‖) * Collision.hatGaussian c₀ m x) := hsumBound
        _ = Cenv * M *
            (∑' x : Site, Real.exp (t * ‖siteToPlane x‖) * Collision.hatGaussian c₀ m x) := by
              rw [tsum_mul_left]
        _ ≤ Cenv * M * ((1 + Real.sqrt (Real.pi / (c₀ / 2))) ^ 2 *
            Real.exp (t ^ 2 * m / (2 * c₀))) :=
              mul_le_mul_of_nonneg_left hweightHat.2 (mul_nonneg hCenv.le hM)
    have hcoef : t ^ 2 * m / (2 * c₀) ≤ 2 * c * t ^ 2 * m := by
      have hnonneg : 0 ≤ t ^ 2 * m := by positivity
      have hrate : 1 / (2 * c₀) ≤ 2 * c := by
        apply (div_le_iff₀ (by positivity : 0 < 2 * c₀)).2
        have hscaled : 1 ≤ 4 * c * c₀ := by
          have h := hexpcoef
          field_simp [ne_of_gt hc₀] at h
          nlinarith [h]
        nlinarith [hscaled]
      calc
        t ^ 2 * m / (2 * c₀) = (1 / (2 * c₀)) * (t ^ 2 * m) := by ring
        _ ≤ (2 * c) * (t ^ 2 * m) := mul_le_mul_of_nonneg_right hrate hnonneg
        _ = 2 * c * t ^ 2 * m := by ring
    have hexp : Real.exp (t ^ 2 * m / (2 * c₀)) ≤ Real.exp (2 * c * t ^ 2 * m) :=
      Real.exp_le_exp.mpr hcoef
    have hfinal :
        Cenv * M * ((1 + Real.sqrt (Real.pi / (c₀ / 2))) ^ 2 *
          Real.exp (t ^ 2 * m / (2 * c₀))) ≤
        c * Real.exp (2 * c * t ^ 2 * m) * M := by
      calc
        _ = (Cenv * (1 + Real.sqrt (Real.pi / (c₀ / 2))) ^ 2) *
            Real.exp (t ^ 2 * m / (2 * c₀)) * M := by ring
        _ ≤ c * Real.exp (t ^ 2 * m / (2 * c₀)) * M := by
          apply mul_le_mul_of_nonneg_right _ hM
          exact mul_le_mul_of_nonneg_right hpref (Real.exp_nonneg _)
        _ ≤ c * Real.exp (2 * c * t ^ 2 * m) * M := by
          apply mul_le_mul_of_nonneg_right _ hM
          exact mul_le_mul_of_nonneg_left hexp (le_trans (by norm_num) hc)
        _ = _ := by ring
    simpa [M] using hmassBound.trans hfinal

end Critical2DKPZ.MomentBounds

end
