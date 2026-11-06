/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedHorizontalLiftSymbolBound
public import AtiyahSinger.Analysis.PrincipalLocalizationFullSymbolInverse
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalAxis
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalTransverseBound
public import AtiyahSinger.Analysis.PrincipalPseudodifferentialLocalization
public import AtiyahSinger.Geometry.AtlasBundlePresentation

/-!
# The horizontal affine path fixed by the original lift

Public module ID: M0862.

The full symbol of the original finite localization is evaluated both on the
covector selected by the specified global horizontal lift and in every
original source chart of the uncut finite family. Both maps have the same
elliptic axis. Their actual metric transverse estimates control every convex
combination in one high horizontal cone, uniformly in the interval parameter.

This is the horizontal part of the supported cutoff homotopy. The full
finite symbol represents the stored base operator; no principal-class
replacement of a full factor is used within the estimate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff unitInterval

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable {V : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module ℂ (V y)]
  [TopologicalSpace (TotalSpace Unit V)]
  (A : SmoothComplexBundleAtlas (n := r) V)
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))
local notation "Z" => AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- The exact native axis and transverse energies are compared in their original metric fibers.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option cleanup.letToHave false in
/-- The given lift and finite horizontal factor have a uniformly invertible affine path. -/
theorem exists_horizontalAffineFullSymbol_conic_metric_inverse_bound
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C.baseOperator.IsElliptic) (J : AtlasBundlePresentation A)
    (ℋ : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (g : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : SmoothHermitianMetric (n := n) (r := a') E')
    (b₀ : B) (c₀ : OpenPartialHomeomorph B X) (hc₀ : c₀ ∈ atlas X B)
    (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r))
    (e₀ : Trivialization (EuclideanSpace ℂ (Fin a)) (π (EuclideanSpace ℂ (Fin a)) E))
    (f₀ : Trivialization (EuclideanSpace ℂ (Fin a')) (π (EuclideanSpace ℂ (Fin a')) E'))
    [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀]
    (K : Set H) (hK : IsCompact K)
    (hKChart : K ⊆ (associatedSphereProductChart S b₀ c₀ d₀).target) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
    let lift (z : Z) := split.symm.toContinuousLinearMap.comp (ℋ.lift z)
    let CP := associatedSphereProductChart S b₀ c₀ d₀
    let Ci (i : Fin C.size) (j : Fin J.size) :=
      associatedSphereProductChart S (C.center i) (C.piece i).chart (J.chart j)
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let x := fun z : H ↦ base (CP.symm z)
    (∀ z ∈ K, x z ∈ e₀.baseSet ∩ f₀.baseSet) →
    ∃ δ R M : ℝ, 0 < δ ∧ 0 < R ∧ 0 ≤ M ∧
      ∀ (t : unitInterval), ∀ z ∈ K, ∀ (ξ : X) (η : Y), R ≤ ‖ξ‖ → ‖η‖ ≤ δ * ‖ξ‖ →
        let coefficient : ℝ := M / (1 + ‖ξ‖) ^ 2
        let z₀ := CP.symm z
        let Ξ := covectorFromChart CP z₀ (split.symm (ξ, η))
        let frequency (i : Fin C.size) (j : Fin J.size) :=
          (split (covectorInChart (Ci i j) z₀ Ξ)).1
        let U := ∑ i, ∑ j,
          (J.cutoff j (associatedSphereTrivialization S (C.center i) z₀).2 : ℂ) •
            (C.piece i).globalSymbolFunction (x z)
              (covectorFromChart (C.piece i).chart (x z) (frequency i j))
        let V := (∑ i, (C.piece i).globalSymbol).val (x z) (Ξ.comp (lift z₀))
        let P := (1 - (t : ℂ)) • V + (t : ℂ) • U
        Function.Bijective P ∧ ∀ u : E (x z), (h.pairing (x z) u u).re ≤
          coefficient * (k.pairing (x z) (P u) (P u)).re :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  intro split
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace split.symm Z
  intro lift CP Ci base x hframe
  -- Project the original compact target window into the given native chart and frames.
  have hbaseChart (z : H) (hz : z ∈ K) : x z ∈ c₀.source := by
    have hw : CP.symm z ∈ CP.source := CP.map_target (hKChart hz)
    let t := associatedSphereTrivialization S b₀
    have ht : CP.symm z ∈ t.source := hw.1.1
    have hb : (t (CP.symm z)).1 ∈ c₀.source := hw.1.2.1
    rwa [t.coe_fst ht] at hb
  have hxcont : ContinuousOn x K :=
    (base.continuous.comp_continuousOn CP.continuousOn_symm).mono hKChart
  have hxcompact : IsCompact (x '' K) := hK.image_of_continuousOn hxcont
  have hxe : x '' K ⊆ c₀.source ∩ e₀.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hbaseChart z hz, (hframe z hz).1⟩
  have hxf : x '' K ⊆ c₀.source ∩ f₀.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hbaseChart z hz, (hframe z hz).2⟩
  obtain ⟨R, M, hR, hM, haxis⟩ := C.exists_fullSymbol_metric_inverse_bound S E E'
    hC g h k c₀ hc₀ e₀ f₀ (x '' K) hxcompact hxe hxf
  obtain ⟨N, hN, herror⟩ := C.exists_horizontalFullSymbol_metric_transverse_bound S E E'
    A J g h k b₀ c₀ hc₀ d₀ hd₀ K hK hKChart
  let p := ∑ i, (C.piece i).globalSymbol
  obtain ⟨N₀, hN₀, hLiftError⟩ :=
    exists_associatedSphere_horizontalLift_fullSymbol_metric_bound S ℋ p.val p.property
      g h k b₀ c₀ hc₀ d₀ hd₀ e₀ f₀ K hK hKChart hframe
  let c : ℝ := M + 1
  let d : ℝ := N + N₀ + 2
  let δ : ℝ := (2 * c * d)⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, R, (2 * c) ^ 2, hδ, hR, sq_nonneg _, ?_⟩
  intro t z hz ξ η hξ hcone coefficient z₀ Ξ frequency U V P
  let ax := (∑ i, (C.piece i).globalSymbol).val (x z) (covectorFromChart c₀ (x z) ξ)
  have hax := haxis ξ hξ (x z) ⟨z, hz, rfl⟩
  change ax.IsInvertible ∧ ∀ u, (h.pairing (x z) u u).re ≤
    M / (1 + ‖ξ‖) ^ 2 * (k.pairing (x z) (ax u) (ax u)).re at hax
  have haxBij : Function.Bijective ax := by
    obtain ⟨e, he⟩ := hax.1
    rw [← he]
    exact e.bijective
  have haxisEq := C.horizontalFullSymbol_axis_eq S E E' A J b₀ c₀ hc₀ d₀ hd₀
    z₀ (CP.map_target (hKChart hz)) ξ
  have he := herror z hz ξ η
  have hdiff : (∑ i, ∑ j,
      (J.cutoff j (associatedSphereTrivialization S (C.center i) z₀).2 : ℂ) •
        ((C.piece i).globalSymbolFunction (x z)
          (covectorFromChart (C.piece i).chart (x z) (frequency i j)) -
        (C.piece i).globalSymbolFunction (x z)
          (covectorFromChart (C.piece i).chart (x z)
            ((split (covectorInChart (Ci i j) z₀
              (covectorFromChart CP z₀ (split.symm (ξ, 0))))).1)))) = U - ax := by
    simp_rw [smul_sub, Finset.sum_sub_distrib]
    rw [haxisEq]
    congr 1
    simp only [ax, Submodule.coe_sum, Finset.sum_apply]
    rfl
  dsimp only at he
  rw [hdiff] at he
  have heV := hLiftError z hz ξ η
  -- Realize precisely the given metric forms; the algebraic maps keep their original fibers.
  let e := e₀.continuousLinearEquivAt ℂ (x z) (hframe z hz).1
  let : FiniteDimensional ℂ (E (x z)) := .of_injective e.toLinearMap e.injective
  let P₀ : E (x z) →ₗ[ℂ] E' (x z) := P.toLinearMap
  let A₀ : E (x z) →ₗ[ℂ] E' (x z) := ax.toLinearMap
  let U₀ : E (x z) →ₗ[ℂ] E' (x z) := U.toLinearMap
  let V₀ : E (x z) →ₗ[ℂ] E' (x z) := V.toLinearMap
  let _ : Module ℂ (E (x z)) := inferInstance
  let _ : Module ℂ (E' (x z)) := inferInstance
  let : InnerProductSpace.Core ℂ (E (x z)) := h.toCore (x z)
  let : InnerProductSpace.Core ℂ (E' (x z)) := k.toCore (x z)
  let : NormedAddCommGroup (E (x z)) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup (E' (x z)) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ (E (x z)) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : InnerProductSpace ℂ (E' (x z)) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  have hi (u : E (x z)) : (h.pairing (x z) u u).re = ‖u‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  have hj (v : E' (x z)) : (k.pairing (x z) v v).re = ‖v‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  have haNorm (u : E (x z)) : ‖u‖ ≤ c / (1 + ‖ξ‖) * ‖A₀ u‖ := by
    have hb := hax.2 u
    rw [hi, hj] at hb
    have hMc : M ≤ c ^ 2 := by dsimp [c]; nlinarith
    have hb' : ‖u‖ ^ 2 ≤ (c / (1 + ‖ξ‖) * ‖A₀ u‖) ^ 2 := by
      calc
        ‖u‖ ^ 2 ≤ M / (1 + ‖ξ‖) ^ 2 * ‖A₀ u‖ ^ 2 := hb
        _ ≤ c ^ 2 / (1 + ‖ξ‖) ^ 2 * ‖A₀ u‖ ^ 2 := by gcongr
        _ = _ := by rw [mul_pow, div_pow]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb'
  have heUNorm (u : E (x z)) : ‖(U₀ - A₀) u‖ ≤ d * ‖η‖ * ‖u‖ := by
    have hb := he u
    rw [hi, hj] at hb
    have hNd : N ≤ d ^ 2 := by dsimp [d]; nlinarith
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      ‖(U₀ - A₀) u‖ ^ 2 ≤ N * ‖η‖ ^ 2 * ‖u‖ ^ 2 := hb
      _ ≤ d ^ 2 * ‖η‖ ^ 2 * ‖u‖ ^ 2 := by gcongr
      _ = _ := by ring
  have heVNorm (u : E (x z)) : ‖(V₀ - A₀) u‖ ≤ d * ‖η‖ * ‖u‖ := by
    have hb := heV u
    rw [hi, hj] at hb
    have hNd : N₀ ≤ d ^ 2 := by dsimp [d]; nlinarith
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    calc
      ‖(V₀ - A₀) u‖ ^ 2 ≤ N₀ * ‖η‖ ^ 2 * ‖u‖ ^ 2 := hb
      _ ≤ d ^ 2 * ‖η‖ ^ 2 * ‖u‖ ^ 2 := by gcongr
      _ = _ := by ring
  -- Convexity keeps both full endpoints within the same transverse error bound.
  have heNorm (u : E (x z)) : ‖(P₀ - A₀) u‖ ≤ d * ‖η‖ * ‖u‖ := by
    have heq : (P₀ - A₀) u =
        (1 - (t : ℂ)) • ((V₀ - A₀) u) +
          (t : ℂ) • ((U₀ - A₀) u) := by
      change ((1 - (t : ℂ)) • V₀ u + (t : ℂ) • U₀ u) - A₀ u = _
      simp only [LinearMap.sub_apply]
      module
    have ht : ‖(t : ℂ)‖ = (t : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg t.property.1]
    have hs : ‖1 - (t : ℂ)‖ = 1 - (t : ℝ) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr t.property.2)]
    rw [heq]
    calc
      _ ≤ ‖(1 - (t : ℂ)) • ((V₀ - A₀) u)‖ +
          ‖(t : ℂ) • ((U₀ - A₀) u)‖ := norm_add_le _ _
      _ = (1 - (t : ℝ)) * ‖(V₀ - A₀) u‖ +
          (t : ℝ) * ‖(U₀ - A₀) u‖ := by rw [norm_smul, norm_smul, hs, ht]
      _ ≤ (1 - (t : ℝ)) * (d * ‖η‖ * ‖u‖) + (t : ℝ) * (d * ‖η‖ * ‖u‖) :=
        add_le_add (mul_le_mul_of_nonneg_left (heVNorm u) (sub_nonneg.mpr t.property.2))
          (mul_le_mul_of_nonneg_left (heUNorm u) t.property.1)
      _ = d * ‖η‖ * ‖u‖ := by ring
  -- A single cone makes the actual transverse error smaller than half the axis bound.
  have hsmall : c / (1 + ‖ξ‖) * (d * ‖η‖) ≤ 1 / 2 := by
    have hcancel : c * d * δ = 1 / 2 := by dsimp [δ]; field_simp
    have hb : c * d * ‖η‖ ≤ ‖ξ‖ / 2 := by
      calc
        c * d * ‖η‖ ≤ c * d * (δ * ‖ξ‖) :=
          mul_le_mul_of_nonneg_left hcone (by positivity)
        _ = ‖ξ‖ / 2 := by rw [← mul_assoc, hcancel]; ring
    have hden : 0 < 1 + ‖ξ‖ := by positivity
    calc
      c / (1 + ‖ξ‖) * (d * ‖η‖) = (c * d * ‖η‖) / (1 + ‖ξ‖) := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hden).mpr (by linarith)
  have hlower (u : E (x z)) : ‖u‖ ≤ (2 * c / (1 + ‖ξ‖)) * ‖P₀ u‖ := by
    have hb : ‖u‖ ≤ c / (1 + ‖ξ‖) * ‖P₀ u‖ + (1 / 2) * ‖u‖ := by
      calc
        ‖u‖ ≤ c / (1 + ‖ξ‖) * ‖A₀ u‖ := haNorm u
        _ ≤ c / (1 + ‖ξ‖) * (‖P₀ u‖ + ‖(P₀ - A₀) u‖) := by
          gcongr
          have heq : A₀ u = P₀ u - (P₀ - A₀) u := by simp
          rw [heq]
          exact norm_sub_le _ _
        _ ≤ c / (1 + ‖ξ‖) * (‖P₀ u‖ + d * ‖η‖ * ‖u‖) := by
          gcongr
          exact heNorm u
        _ = c / (1 + ‖ξ‖) * ‖P₀ u‖ +
            (c / (1 + ‖ξ‖) * (d * ‖η‖)) * ‖u‖ := by ring
        _ ≤ c / (1 + ‖ξ‖) * ‖P₀ u‖ + (1 / 2) * ‖u‖ := by gcongr
    have hrearrange : 2 * (c / (1 + ‖ξ‖) * ‖P₀ u‖) =
        (2 * c / (1 + ‖ξ‖)) * ‖P₀ u‖ := by ring
    nlinarith
  have hPinj : Function.Injective P₀ := by
    intro u v huv
    have hb := hlower (u - v)
    rw [map_sub, huv, sub_self, norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  let ea := LinearEquiv.ofBijective A₀ haxBij
  have hcomp : Function.Surjective (ea.symm.toLinearMap.comp P₀) :=
    LinearMap.injective_iff_surjective.mp (ea.symm.injective.comp hPinj)
  have hPsurj : Function.Surjective P₀ := by
    intro v
    obtain ⟨u, hu⟩ := hcomp (ea.symm v)
    exact ⟨u, ea.symm.injective hu⟩
  refine ⟨⟨hPinj, hPsurj⟩, ?_⟩
  intro u
  rw [hi, hj]
  have hb : ‖u‖ ^ 2 ≤ ((2 * c / (1 + ‖ξ‖)) * ‖P₀ u‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg u) (by positivity)).mpr (hlower u)
  change ‖u‖ ^ 2 ≤ coefficient * ‖P₀ u‖ ^ 2
  convert hb using 1
  simp only [coefficient, mul_pow, div_pow]

end PrincipalPseudodifferentialLocalization

end AtiyahSinger
