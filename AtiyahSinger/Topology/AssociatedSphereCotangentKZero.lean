/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereCotangentHomotopy
public import AtiyahSinger.Topology.AssociatedCompactControl
public import AtiyahSinger.Topology.CompactSupportFunctoriality

/-!
# Compact-support K transport for the actual associated sphere cotangent bundle

Public module ID: M1544.

Transport through the specified cotangent realization by pulling back along
its inverse. The original associated quotient and the native cotangent total
space keep their topologies. Local compactness and separation on the target
are consequences of the same homeomorphism, not replacement structures.

The inverse realizations are properly homotopic when the supplied horizontal
lift changes. Their actual inverse pullbacks therefore agree. Compactness of
the base is not needed for this comparison; it is needed later for the original
associated descent in the twisted product and for the selected horizontal lift.

Sources: SG III.13 (13.15)--(13.16), pp.251--252; compact-support homotopy
invariance as in Karoubi II.4. The explicit choice comparison is a project
supplement. No analytic index formula or Euclidean recharting is asserted.
The given-lift choice comparison is proved for these actual inverse pullbacks.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff Matrix.Norms.Elementwise

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B] [T2Space B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "OG" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle OG P (OrthogonalSphere r)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "Q" => PrincipalBundlePullback (cotangentProjection (n := n) (M := B)) projection
local notation "C" => fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ

/-- The actual associated cotangent realization induces inverse-pullback K transport. -/
def associatedSphereCotangentKZeroEquiv
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := associatedBundle_t2Space (Y := SphereCot)
      (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
    letI := associatedBundle_locallyCompactSpace (Y := SphereCot)
      (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
    let e := associatedSphereCotangentHomeomorph S H
    letI := e.t2Space
    letI := e.symm.isOpenEmbedding.locallyCompactSpace
    CompactSupportKZero (AssociatedBundle OG Q SphereCot) ≃+
      CompactSupportKZero (TotalSpace ((En × Er) →L[ℝ] ℝ) C) := by
  -- The source has the existing quotient topology and the pulled principal bundle charts.
  letI := S.toIsPrincipalBundle
  letI := associatedSphereChartedSpace S
  letI := associatedSphereIsManifold S
  letI := associatedBundle_t2Space (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  letI := associatedBundle_locallyCompactSpace (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  -- The same homeomorphism supplies properties of the unchanged native target topology.
  let e := associatedSphereCotangentHomeomorph S H
  letI := e.t2Space
  letI := e.symm.isOpenEmbedding.locallyCompactSpace
  exact compactSupportKZeroHomeomorphEquiv e

/-- K transport to the original cotangent total space is independent of the horizontal lift. -/
theorem associatedSphereCotangentKZeroEquiv_independent_horizontalLift
    (H₀ H₁ : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    associatedSphereCotangentKZeroEquiv S H₀ = associatedSphereCotangentKZeroEquiv S H₁ := by
  /- Stage 1: use the proper homotopy of the exact inverse realizations from
  exists_associatedSphereCotangentInverse_properHomotopy. Its fixed canonical
  comparison uses the same original principal pullback, sphere quotient,
  projection derivative and selected vertical atlas at both endpoints.
  Stage 2: apply compactSupportKZeroPullback_eq_of_proper_homotopy to these
  inverse maps. Their pullbacks are exactly the forward maps of the displayed
  additive equivalences. The properness is for the whole time cylinder; it
  is not inferred from the individual homeomorphism slices.
  Stage 3: additive-equivalence extensionality gives equality, including
  their inverse transports. Separation and local compactness certificates
  transferred by the two homeomorphisms are proofs about the same topologies;
  they do not change the compact-support groups. No compact base, metric,
  global norm bound or properness of the cotangent projection is assumed. -/
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let hQ := isPrincipalBundle_pullback (G := OG) (projection := projection)
    (cotangentProjection (n := n) (M := B))
  let := associatedBundle_t2Space (Y := SphereCot) hQ
  let := associatedBundle_locallyCompactSpace (Y := SphereCot) hQ
  let e₀ := associatedSphereCotangentHomeomorph S H₀
  let e₁ := associatedSphereCotangentHomeomorph S H₁
  let := e₀.t2Space
  let := e₀.symm.isOpenEmbedding.locallyCompactSpace
  -- The existing cylinder joins these exact inverse realizations and is proper as a whole.
  obtain ⟨H, _, hH⟩ := exists_associatedSphereCotangentInverse_properHomotopy S H₀ H₁
  have hpull := compactSupportKZeroPullback_eq_of_proper_homotopy
    e₀.symm.isProperMap e₁.symm.isProperMap H hH
  -- Both original additive equivalences have precisely these inverse-pullback functions.
  apply AddEquiv.ext
  intro a
  exact DFunLike.congr_fun hpull a

end AtiyahSinger
