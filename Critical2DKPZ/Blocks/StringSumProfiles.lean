/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.StringSumPropagation
import Mathlib.Tactic

/-! # Fixed-time spatial profiles for occupied renewal blocks -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Blocks

open scoped BigOperators


/-- The spatial profile after the first occupied block with fixed collision times. -/
def initialSpatialProfile (σ2 : ℝ) (a b : ℕ) (y : Site) : ℝ :=
  ∑' x, srwKernel a x ^ 2 *
    (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))

/-- The spatial profile after one further occupied block with fixed collision times. -/
def transitionSpatialProfile (σ2 : ℝ) (k a b : ℕ) (f : Site → ℝ) (y : Site) : ℝ :=
  ∑' y₀, f y₀ * ∑' x,
    (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
      (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))

/-- A finite set containing the support of the initial spatial profile. -/
def initialSpatialProfileSupport (a b : ℕ) : Finset Site :=
  (Polymer.endpoints 0 a).biUnion (fun x => Polymer.endpoints x (b - a))

/-- A finite set containing the support of the transition spatial profile. -/
def transitionSpatialProfileSupport (k a b : ℕ) (S : Finset Site) : Finset Site :=
  ((S.biUnion fun y₀ => Polymer.endpoints y₀ (a - k) ∪ Polymer.endpoints 0 a)
    ).biUnion (fun x => Polymer.endpoints x (b - a))

/-- Endpoint membership is invariant under translating the starting site. -/
theorem mem_endpoints_sub_iff (x y : Site) (n : ℕ) :
    y - x ∈ Polymer.endpoints 0 n ↔ y ∈ Polymer.endpoints x n := by
  constructor
  · intro hy
    obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff 0 (y - x) n).1 hy
    apply (Polymer.mem_endpoints_iff x y n).2
    refine ⟨s, ?_⟩
    rw [Polymer.walkPosition_eq_start_add, hs]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    omega
  · intro hy
    obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff x y n).1 hy
    apply (Polymer.mem_endpoints_iff 0 (y - x) n).2
    refine ⟨s, ?_⟩
    have hrel : walkPosition x s n - x = walkPosition 0 s n := by
      rw [Polymer.walkPosition_eq_start_add]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply]
      omega
    rw [← hrel, hs]

/-- The initial profile vanishes outside its finite walk support. -/
theorem initialSpatialProfile_eq_zero_of_not_mem_support {σ2 : ℝ} {a b : ℕ}
    {y : Site} (hy : y ∉ initialSpatialProfileSupport a b) :
    initialSpatialProfile σ2 a b y = 0 := by
  change (∑' x, srwKernel a x ^ 2 *
      (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))) = 0
  have hfun : (fun x => srwKernel a x ^ 2 *
      (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))) = 0 := by
    funext x
    by_cases hx : x ∈ Polymer.endpoints 0 a
    · have hyx : y ∉ Polymer.endpoints x (b - a) := by
        intro hxy
        apply hy
        exact Finset.mem_biUnion.mpr ⟨x, hx, hxy⟩
      have hu : Collision.spatialRenewal σ2 (b - a) (y - x) = 0 :=
        spatialRenewal_eq_zero_of_not_mem_endpoints
          (by simpa only [mem_endpoints_sub_iff] using hyx)
      simp [hu]
    · have hq := Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx
      have hq' : srwKernel a x = 0 := by simpa only [sub_zero] using hq
      simp [hq']
  rw [hfun]
  exact tsum_zero

/-- A transition profile vanishes outside its finite walk support whenever its input does. -/
theorem transitionSpatialProfile_eq_zero_of_not_mem_support {σ2 : ℝ} {k a b : ℕ}
    {f : Site → ℝ} {S : Finset Site} {y : Site}
    (hf : ∀ y₀, y₀ ∉ S → f y₀ = 0)
    (hy : y ∉ transitionSpatialProfileSupport k a b S) :
    transitionSpatialProfile σ2 k a b f y = 0 := by
  change (∑' y₀, f y₀ * ∑' x,
      (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))) = 0
  have hfun : (fun y₀ => f y₀ * ∑' x,
      (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
        (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))) = 0 := by
    funext y₀
    by_cases hy₀ : y₀ ∈ S
    · have hinner : (fun x =>
          (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
            (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x))) = 0 := by
        funext x
        by_cases hx : x ∈ Polymer.endpoints y₀ (a - k) ∪ Polymer.endpoints 0 a
        · have hyx : y ∉ Polymer.endpoints x (b - a) := by
            intro hxy
            apply hy
            apply Finset.mem_biUnion.mpr
            refine ⟨x, ?_, hxy⟩
            exact Finset.mem_biUnion.mpr ⟨y₀, hy₀, hx⟩
          have hu : Collision.spatialRenewal σ2 (b - a) (y - x) = 0 :=
            spatialRenewal_eq_zero_of_not_mem_endpoints
              (by simpa only [mem_endpoints_sub_iff] using hyx)
          simp [hu]
        · have hx₁ : x ∉ Polymer.endpoints y₀ (a - k) := by
            intro hx₁
            exact hx (Finset.mem_union.mpr (Or.inl hx₁))
          have hx₂ : x ∉ Polymer.endpoints 0 a := by
            intro hx₂
            exact hx (Finset.mem_union.mpr (Or.inr hx₂))
          have hq₁ := Polymer.srwKernel_eq_zero_of_not_mem (a - k) y₀ x hx₁
          have hq₂' := Polymer.srwKernel_eq_zero_of_not_mem a 0 x hx₂
          have hq₂ : srwKernel a x = 0 := by simpa only [sub_zero] using hq₂'
          simp [hq₁, hq₂]
      have hinnerSum : ∑' x,
          (srwKernel (a - k) (x - y₀) - srwKernel a x) ^ 2 *
            (σ2 * Collision.spatialRenewal σ2 (b - a) (y - x)) = 0 := by
        rw [hinner]
        exact tsum_zero
      simp [hinnerSum]
    · simp [hf y₀ hy₀]
  rw [hfun]
  exact tsum_zero



/-- The initial spatial profile is nonnegative and summable and satisfies a Gaussian upper bound with the initial scalar mass factor. -/
theorem initialSpatialProfile_bounds {c Cwalk Crenewal σ2 : ℝ}
    (hc : 0 < c) (hCwalk : 1 ≤ Cwalk) (hCrenewal : 1 ≤ Crenewal)
    (hkernel : ∀ n x, srwKernel n x ≤ Cwalk * Collision.hatGaussian c n x)
    (hconvolution : ∀ k d : ℕ, ∀ z : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
        Cwalk * Collision.hatGaussian c (k + d) z)
    (hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x)
    (hσ : 0 ≤ σ2) (hU : ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∀ y, 0 ≤ initialSpatialProfile σ2 a b y) ∧
      Summable (initialSpatialProfile σ2 a b) ∧
      ∀ y, initialSpatialProfile σ2 a b y ≤
        (Cwalk ^ 2 * (a : ℝ)⁻¹ * Crenewal * Cwalk *
          (σ2 * (∑' z, Collision.spatialRenewal σ2 (b - a) z))) *
            Collision.hatGaussian c b y := by
  have hbound := tsum_srwKernel_sq_spatialRenewal_le hc hCwalk hCrenewal
    hkernel hconvolution hrenewal hσ ha (b - a)
  have hmass : 0 ≤ ∑' z : Site, Collision.spatialRenewal σ2 (b - a) z :=
    tsum_nonneg fun z => hU (b - a) z
  let K : ℝ := Cwalk ^ 2 * (a : ℝ)⁻¹ * Crenewal * Cwalk *
    (σ2 * (∑' z : Site, Collision.spatialRenewal σ2 (b - a) z))
  have hK : 0 ≤ K := by
    dsimp [K]
    have haR : 0 < (a : ℝ) := by exact_mod_cast (Nat.zero_lt_one.trans_le ha)
    positivity
  have hpoint (y : Site) : initialSpatialProfile σ2 a b y ≤
      K * Collision.hatGaussian c b y := by
    simpa only [initialSpatialProfile, K, Nat.add_sub_of_le hab] using hbound y
  have hnonneg (y : Site) : 0 ≤ initialSpatialProfile σ2 a b y := by
    apply tsum_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _) (mul_nonneg hσ (hU (b - a) (y - x)))
  have hb : 1 ≤ b := le_trans ha hab
  have hsum := (Collision.hatGaussian_summable hc hb).mul_left K
  refine ⟨hnonneg, ?_, ?_⟩
  · exact hsum.of_nonneg_of_le hnonneg hpoint
  · intro y
    exact hpoint y


/-- A transition preserves nonnegativity and summability and propagates the Gaussian upper bound with its scalar mass factor. -/
theorem transitionSpatialProfile_bounds {c Cwalk Crenewal σ2 : ℝ}
    (hc : 0 < c) (hCwalk : 1 ≤ Cwalk) (hCrenewal : 1 ≤ Crenewal)
    (hconvolution : ∀ k d : ℕ, ∀ z : Site,
      ∑' x, Collision.hatGaussian c k x * Collision.hatGaussian c d (z - x) ≤
        Cwalk * Collision.hatGaussian c (k + d) z)
    (hrenewal : ∀ σ : ℝ, 0 ≤ σ → ∀ n : ℕ, 1 ≤ n → ∀ x : Site,
      Collision.spatialRenewal σ n x ≤
        Crenewal * (∑' w, Collision.spatialRenewal σ n w) * Collision.hatGaussian c n x)
    (hvariance : ∀ k a : ℕ, 0 < k → k < a → ∀ x : Site,
      ∑' y, Collision.hatGaussian c k y *
        (srwKernel (a - k) (x - y) - srwKernel a x) ^ 2 ≤
          Cwalk * k / (a * (a - k)) * Collision.hatGaussian c a x)
    (hσ : 0 ≤ σ2) (hU : ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x)
    {K : ℝ} (hK : 0 ≤ K) {k a b : ℕ} (hk : 1 ≤ k) (hka : k < a) (hab : a ≤ b)
    (f : Site → ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (hf : ∀ y, f y ≤ K * Collision.hatGaussian c k y) (hfs : Summable f) :
    (∀ y, 0 ≤ transitionSpatialProfile σ2 k a b f y) ∧
      Summable (transitionSpatialProfile σ2 k a b f) ∧
      ∀ y, transitionSpatialProfile σ2 k a b f y ≤
        (K * Cwalk * k / (a * (a - k)) * Crenewal * Cwalk *
          (σ2 * (∑' z, Collision.spatialRenewal σ2 (b - a) z))) *
            Collision.hatGaussian c b y := by
  have hbound := tsum_transition_spatialRenewal_le hc hCwalk hCrenewal
    hconvolution hrenewal hU hσ hK hk hka srwKernel
    srwKernel_difference_sq_le_one hvariance f hf0 hf hfs (b - a)
  have ha : 1 ≤ a := le_trans hk (Nat.le_of_lt hka)
  have hb : 1 ≤ b := le_trans ha hab
  let L : ℝ := K * Cwalk * k / (a * (a - k)) * Crenewal * Cwalk *
    (σ2 * (∑' z : Site, Collision.spatialRenewal σ2 (b - a) z))
  have hpoint (y : Site) : transitionSpatialProfile σ2 k a b f y ≤
      L * Collision.hatGaussian c b y := by
    simpa only [transitionSpatialProfile, L, Nat.add_sub_of_le hab] using hbound y
  have hnonneg (y : Site) : 0 ≤ transitionSpatialProfile σ2 k a b f y := by
    apply tsum_nonneg
    intro y₀
    apply mul_nonneg (hf0 y₀)
    apply tsum_nonneg
    intro x
    exact mul_nonneg (sq_nonneg _)
      (mul_nonneg hσ (hU (b - a) (y - x)))
  have hsum := (Collision.hatGaussian_summable hc hb).mul_left L
  exact ⟨hnonneg, hsum.of_nonneg_of_le hnonneg hpoint, hpoint⟩


/-- The scalar cost of one fixed later occupied block. -/
def transitionProfileFactor (σ2 Cwalk Crenewal : ℝ) (k a b : ℕ) : ℝ :=
  Cwalk * k / (a * (a - k)) * Crenewal * Cwalk *
    (σ2 * (∑' z : Site, Collision.spatialRenewal σ2 (b - a) z))






/-- Each fixed occupied block has a nonnegative scalar cost. -/
theorem transitionProfileFactor_nonneg {Cwalk Crenewal σ2 : ℝ}
    (hCwalk : 1 ≤ Cwalk) (hCrenewal : 1 ≤ Crenewal)
    (hσ : 0 ≤ σ2) (hU : ∀ n x, 0 ≤ Collision.spatialRenewal σ2 n x)
    {k a b : ℕ} (hk : 1 ≤ k) (hka : k < a) :
    0 ≤ transitionProfileFactor σ2 Cwalk Crenewal k a b := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast (lt_trans hk hka)
  have hkaR : (k : ℝ) < (a : ℝ) := by exact_mod_cast hka
  have hgapR : 0 < (a : ℝ) - (k : ℝ) := sub_pos.mpr hkaR
  have hden : 0 < (a : ℝ) * ((a : ℝ) - (k : ℝ)) := mul_pos haR hgapR
  have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg _
  have hnum : 0 ≤ Cwalk * (k : ℝ) := mul_nonneg (le_trans (by norm_num) hCwalk) hkR
  have hmass : 0 ≤ ∑' z : Site, Collision.spatialRenewal σ2 (b - a) z :=
    tsum_nonneg fun z => hU (b - a) z
  have hσmass : 0 ≤ σ2 * (∑' z, Collision.spatialRenewal σ2 (b - a) z) :=
    mul_nonneg hσ hmass
  have houter : 0 ≤ Crenewal * Cwalk *
      (σ2 * (∑' z, Collision.spatialRenewal σ2 (b - a) z)) :=
    mul_nonneg (mul_nonneg (le_trans (by norm_num) hCrenewal)
      (le_trans (by norm_num) hCwalk)) hσmass
  unfold transitionProfileFactor
  convert mul_nonneg (div_nonneg hnum hden.le) houter using 1
  ring




end Critical2DKPZ.Blocks

end
