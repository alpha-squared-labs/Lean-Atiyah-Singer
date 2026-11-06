/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedHorizontalMetricTransverseBound

/-!
# The original finite horizontal sum in its prescribed metrics

Public module ID: M0094.

The actual compact support of each finite piece determines its own chart
window. The original full-symbol transverse bounds are summed in the given
Hermitian metric on the common output fiber. Inactive pieces disappear by
an explicit original weight or full-symbol vanishing condition, so no common
intersection of all source charts is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n a a' : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ B]
  [T2Space B] [SecondCountableTopology B]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : B → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) F]
  [IsSmoothComplexBundle (n := n) (r := a') F]
  {r : ℕ} {P : Type*} [TopologicalSpace P]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))
local notation "Z" => AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)

variable {ι : Type*} [Fintype ι]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- Bound the finite horizontal sum in the same target window and original fiber metrics.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option cleanup.letToHave false in

/-- The same finite horizontal sum has a metric transverse bound on the target window. -/
theorem exists_associatedSphereProductChart_finite_horizontal_metric_transverse_bound
    (p : ι → globalSymbolSpace (n := n) (r := a) (q := a') E F 1)
    (g : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : SmoothHermitianMetric (n := n) (r := a') F)
    (b : ι → B) (c : ι → OpenPartialHomeomorph B X)
    (hc : ∀ i, c i ∈ atlas X B)
    (d : ι → OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd : ∀ i, d i ∈ atlas Y (OrthogonalSphere r))
    (b₀ : B) (c₀ : OpenPartialHomeomorph B X) (hc₀ : c₀ ∈ atlas X B)
    (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r))
    (e₀ : ι → Trivialization (EuclideanSpace ℂ (Fin a)) (π (EuclideanSpace ℂ (Fin a)) E))
    (f₀ : ι → Trivialization (EuclideanSpace ℂ (Fin a')) (π (EuclideanSpace ℂ (Fin a')) F))
    (he₀ : ∀ i, MemTrivializationAtlas (e₀ i))
    (hf₀ : ∀ i, MemTrivializationAtlas (f₀ i))
    (s : ι → Set Z) (hs : ∀ i, IsCompact (s i))
    (hsChart : ∀ i, s i ⊆ (associatedSphereProductChart S (b i) (c i) (d i)).source)
    (K : Set H) (hK : IsCompact K)
    (hKChart : K ⊆ (associatedSphereProductChart S b₀ c₀ d₀).target)
    (w : ι → Z → ℝ) (hw : ∀ i z, |w i z| ≤ 1) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
    let CP := associatedSphereProductChart S b₀ c₀ d₀
    let Ci := fun i ↦ associatedSphereProductChart S (b i) (c i) (d i)
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    (∀ i z, z ∈ s i → base z ∈ (e₀ i).baseSet ∩ (f₀ i).baseSet) →
    (∀ i z, z ∉ s i → w i z = 0 ∨ ∀ ν, (p i).val (base z) ν = 0) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ (ξ : X) (η : Y),
      let coefficient : ℝ := C * ‖η‖ ^ 2
      let z₀ := CP.symm z
      let frequency (i : ι) (η : Y) := (split (covectorInChart (Ci i) z₀
        (covectorFromChart CP z₀ (split.symm (ξ, η))))).1
      let Δ := ∑ i, (w i z₀ : ℂ) •
        ((p i).val (base z₀) (covectorFromChart (c i) (base z₀) (frequency i η)) -
          (p i).val (base z₀) (covectorFromChart (c i) (base z₀) (frequency i 0)))
      ∀ u : E (base z₀), (k.pairing (base z₀) (Δ u) (Δ u)).re ≤
        coefficient * (h.pairing (base z₀) u u).re :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  intro split
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace split.symm Z
  intro CP Ci base hsFrame hsZero
  -- Intersect each actual support with the target window before choosing any local constant.
  let target := CP.symm '' K
  have htarget : IsCompact target :=
    hK.image_of_continuousOn (CP.continuousOn_symm.mono hKChart)
  have htargetChart : target ⊆ CP.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact CP.map_target (hKChart hz)
  let window (i : ι) := CP '' (s i ∩ target)
  have hwindow (i : ι) : IsCompact (window i) :=
    ((hs i).inter htarget).image_of_continuousOn
      (CP.continuousOn.mono (inter_subset_right.trans htargetChart))
  have hwindowChart (i : ι) : window i ⊆ ((Ci i).symm.trans CP).target := by
    rintro _ ⟨z, hz, rfl⟩
    have hc := htargetChart hz.2
    refine ⟨CP.map_source hc, ?_⟩
    change CP.symm (CP z) ∈ (Ci i).source
    rw [CP.left_inv hc]
    exact hsChart i hz.1
  have hwindowFrame (i : ι) (z : H) (hz : z ∈ window i) :
      base (CP.symm z) ∈ (e₀ i).baseSet ∩ (f₀ i).baseSet := by
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [CP.left_inv (htargetChart hz₀.2)]
    exact hsFrame i z₀ hz₀.1
  have hlocal (i : ι) := by
    let := he₀ i
    let := hf₀ i
    exact exists_associatedSphereProductChart_horizontal_metric_transverse_bound S
      (p i).val (p i).property g h k (b i) b₀ (c i) c₀ (hc i) hc₀ (d i) d₀ (hd i) hd₀
      (e₀ i) (f₀ i) (window i) (hwindow i) (hwindowChart i) (hwindowFrame i)
  choose C hC hbound using hlocal
  let L := ∑ i, Real.sqrt (C i)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ ↦ Real.sqrt_nonneg _)
  refine ⟨L ^ 2, sq_nonneg L, ?_⟩
  intro z hz ξ η coefficient z₀ frequency Δ u
  let δ (i : ι) : E (base z₀) →ₗ[ℂ] F (base z₀) :=
    ((p i).val (base z₀) (covectorFromChart (c i) (base z₀) (frequency i η)) -
      (p i).val (base z₀) (covectorFromChart (c i) (base z₀) (frequency i 0))).toLinearMap
  -- Only the original metric forms are realized as local norms for summing these same maps.
  let : Module ℂ (E (base z₀)) := inferInstance
  let : Module ℂ (F (base z₀)) := inferInstance
  let := h.toCore (base z₀)
  let := k.toCore (base z₀)
  let : NormedAddCommGroup (E (base z₀)) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup (F (base z₀)) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (E (base z₀)))
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (F (base z₀)))
  have hterm (i : ι) : ‖(w i z₀ : ℂ) • δ i u‖ ≤ Real.sqrt (C i) * ‖η‖ * ‖u‖ := by
    by_cases hactive : z₀ ∈ s i
    · have hzw : z ∈ window i :=
        ⟨z₀, ⟨hactive, ⟨z, hz, rfl⟩⟩, CP.right_inv (hKChart hz)⟩
      have hb := hbound i z hzw ξ η u
      change (inner ℂ (δ i u) (δ i u)).re ≤ C i * ‖η‖ ^ 2 * (inner ℂ u u).re at hb
      have hi₀ : (inner ℂ u u).re = ‖u‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
      have hi₁ : (inner ℂ (δ i u) (δ i u)).re = ‖δ i u‖ ^ 2 :=
        (norm_sq_eq_re_inner (𝕜 := ℂ) (δ i u)).symm
      rw [hi₀, hi₁, ← Real.sq_sqrt (hC i), ← mul_pow, ← mul_pow] at hb
      have hnorm := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb
      calc
        ‖(w i z₀ : ℂ) • δ i u‖ = |w i z₀| * ‖δ i u‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 1 * ‖δ i u‖ := mul_le_mul_of_nonneg_right (hw i z₀) (norm_nonneg _)
        _ ≤ Real.sqrt (C i) * ‖η‖ * ‖u‖ := by simpa only [one_mul] using hnorm
    · rcases hsZero i z₀ hactive with hi | hi
      · simp only [hi, Complex.ofReal_zero, zero_smul, norm_zero]
        positivity
      · have hzδ : δ i = 0 := by simp [δ, hi]
        simp only [hzδ, LinearMap.zero_apply, smul_zero, norm_zero]
        positivity
  have hsum : ‖Δ u‖ ≤ L * ‖η‖ * ‖u‖ := by
    have hvalue : Δ u = ∑ i, (w i z₀ : ℂ) • δ i u := by
      simp [Δ, δ]
    rw [hvalue]
    calc
      ‖∑ i, (w i z₀ : ℂ) • δ i u‖ ≤ ∑ i, ‖(w i z₀ : ℂ) • δ i u‖ := norm_sum_le _ _
      _ ≤ ∑ i, Real.sqrt (C i) * ‖η‖ * ‖u‖ := Finset.sum_le_sum (fun i _ ↦ hterm i)
      _ = L * ‖η‖ * ‖u‖ := by simp only [L, Finset.sum_mul]
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hsum
  have hi₀ : (h.pairing (base z₀) u u).re = ‖u‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  have hi₁ : (k.pairing (base z₀) (Δ u) (Δ u)).re = ‖Δ u‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (Δ u)).symm
  rw [hi₀, hi₁]
  simpa only [mul_pow] using hsquare

end AtiyahSinger
