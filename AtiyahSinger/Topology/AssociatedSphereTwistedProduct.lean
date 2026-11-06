/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereHorizontalLift
public import AtiyahSinger.Topology.AssociatedSphereCotangentKZero
public import AtiyahSinger.Topology.AssociatedTwistedProduct

/-!
# The twisted product on the original sphere-bundle cotangent space

Public module ID: M1546.

For a compact Hausdorff smooth base, the specified sphere bundle has a chosen
horizontal lift. Transport the existing associated twisted product along the
actual cotangent realization for this lift. This defines the bilinear product
in SG III.13 (13.16) on the native full-product cotangent model upstairs.

The same product is obtained from any supplied smooth horizontal lift. The
full representation-ring coefficient can move between its two inputs, using
the original associated coefficient bundle on the base. These statements
retain the original proper paired map and the exact inverse-pullback transport.
Neither cotangent projection is used as a compact-support pullback by itself.

Sources: SG III.13, pp.251--252, and Appendix C.1. Independence of the lift is
made explicit through a proper cylinder in AssociatedSphereCotangentKZero.
The laws here concern the K classes, original graph actions and cotangent transport.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.Elementwise

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereCotangent t2Space_cotangent locallyCompactSpace_cotangent

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "OG" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle OG P (OrthogonalSphere r)
local notation "BaseCot" => CotangentTotalSpace (n := n) (M := B)
local notation "SphereCot" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "C" => fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ

set_option maxHeartbeats 800000 in

/-- SG's twisted product, now valued in the original associated sphere cotangent K group. -/
def associatedSphereTwistedProduct :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := associatedBundle_t2Space (Y := SphereCot)
      (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
    letI := associatedBundle_locallyCompactSpace (Y := SphereCot)
      (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
    let e := associatedSphereCotangentHomeomorph S (associatedSphereHorizontalLift S)
    letI := e.t2Space
    letI := e.symm.isOpenEmbedding.locallyCompactSpace
    CompactSupportKZero BaseCot →+ EquivariantSupportTripleKZero OG SphereCot →+
      CompactSupportKZero (TotalSpace ((En × Er) →L[ℝ] ℝ) C) := by
  -- Fix the one associated manifold and the original pulled principal quotient.
  letI := S.toIsPrincipalBundle
  letI := associatedSphereChartedSpace S
  letI := associatedSphereIsManifold S
  letI := associatedBundle_t2Space (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  letI := associatedBundle_locallyCompactSpace (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  let H := associatedSphereHorizontalLift S
  let e := associatedSphereCotangentHomeomorph S H
  letI := e.t2Space
  letI := e.symm.isOpenEmbedding.locallyCompactSpace
  -- Descend the external product via its proper paired map, then transport by e inverse.
  exact (associatedSupportTwistedProduct (G := OG) (Y := SphereCot)
    (projection := projection) (cotangentProjection (n := n) (M := B))).compr₂
      (associatedSphereCotangentKZeroEquiv S H).toAddMonoidHom

/-- Any supplied horizontal lift realizes the same full bilinear product. -/
theorem associatedSphereTwistedProduct_eq_of_horizontalLift
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S)) :
    letI := S.toIsPrincipalBundle
    associatedSphereTwistedProduct S =
      (associatedSupportTwistedProduct (G := OG) (Y := SphereCot)
        (projection := projection) (cotangentProjection (n := n) (M := B))).compr₂
          (associatedSphereCotangentKZeroEquiv S H).toAddMonoidHom := by
  /- Stage 1: unfold only the specified composition defining this product.
  Its associated descent, external product and proper paired pullback are
  independent of the horizontal lift; their original spaces and maps agree.
  Stage 2: compare the selected lift with H using the equality of the entire
  associatedSphereCotangentKZeroEquiv operators. That equality used proper
  homotopy of the inverse realizations, matching the pullback direction.
  Postcomposition gives equality of these bilinear maps, for all two inputs.
  This does not assert equality of the underlying cotangent homeomorphisms
  or of raw support-triple representatives for different lifts. -/
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := associatedBundle_t2Space (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  let := associatedBundle_locallyCompactSpace (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  let e := associatedSphereCotangentHomeomorph S (associatedSphereHorizontalLift S)
  let := e.t2Space
  let := e.symm.isOpenEmbedding.locallyCompactSpace
  -- The associated product is fixed; only its final additive transport uses the lift.
  exact congrArg
    (fun transport ↦ (associatedSupportTwistedProduct (G := OG) (Y := SphereCot)
      (projection := projection) (cotangentProjection (n := n) (M := B))).compr₂
        transport.toAddMonoidHom)
    (associatedSphereCotangentKZeroEquiv_independent_horizontalLift S
      (associatedSphereHorizontalLift S) H)

/-- A virtual representation coefficient moves between the two inputs without changing product. -/
theorem associatedSphereTwistedProduct_balanced
    (a : RepresentationGrothendieckGroup OG) (u : CompactSupportKZero BaseCot)
    (v : EquivariantSupportTripleKZero OG SphereCot) :
    associatedSphereTwistedProduct S
        (complexKZeroCompactSupportAction (cotangentProjection (n := n) (M := B))
          (associatedRepresentationKZero S.toIsPrincipalBundle a) u) v =
      associatedSphereTwistedProduct S u (a • v) := by
  /- Stage 1: the existing associatedSupportTwistedProduct_balanced identity
  moves the original associated coefficient bundle across the external
  product. On the original fiber product its two maps to B agree, so the
  same bundle fiber acts on both sides. The degree-zero coefficient introduces
  no grading sign; the identity holds for the full representation group.
  Stage 2: apply the same additive cotangent transport to both sides. Its
  inverse-pullback formula preserves the identity on compact-support classes.
  The preceding lift comparison makes this equality intrinsic to the product.
  No properness of the cotangent projection is required: the original
  absolute K(B) action uses its proper graph construction.
  No assertion about symbols, equivariant quantization or analytic indices
  follows from this coefficient identity alone. -/
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := associatedBundle_t2Space (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  let := associatedBundle_locallyCompactSpace (Y := SphereCot)
    (isPrincipalBundle_pullback (G := OG) (projection := projection)
      (cotangentProjection (n := n) (M := B)))
  let H := associatedSphereHorizontalLift S
  let e := associatedSphereCotangentHomeomorph S H
  let := e.t2Space
  let := e.symm.isOpenEmbedding.locallyCompactSpace
  -- Keep the original associated coefficient and apply the same fixed transport to both sides.
  have hbalance := associatedSupportTwistedProduct_balanced (G := OG) (Y := SphereCot)
    (projection := projection) (cotangentProjection (n := n) (M := B)) a u v
  exact congrArg (associatedSphereCotangentKZeroEquiv S H) hbalance

end AtiyahSinger
