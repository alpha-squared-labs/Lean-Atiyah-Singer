/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CotangentOpenRestriction
public import AtiyahSinger.Analysis.CotangentRestrictionTransport
public import AtiyahSinger.Analysis.EquivariantAnalyticIndexRestriction
public import AtiyahSinger.Analysis.EquivariantIndexExcision
public import AtiyahSinger.Analysis.EquivariantIndexProduct
public import AtiyahSinger.Analysis.EquivariantOpenIndexRestriction
public import AtiyahSinger.Analysis.SphereNativePoleIndex
public import AtiyahSinger.Analysis.SphereTangentIndex
public import AtiyahSinger.Analysis.SphereCotangentPoleClass
public import AtiyahSinger.Analysis.OrthogonalPoleCotangentSource
public import AtiyahSinger.Geometry.SphereProductCotangentCoordinates
public import AtiyahSinger.Topology.EquivariantDifferentGroupOpen
public import AtiyahSinger.Topology.EquivariantOpenActionTransport
public import AtiyahSinger.Topology.EquivariantOpenRestriction
public import AtiyahSinger.Topology.OrthogonalBottDirectSum

/-!
# Orthogonal pole indices and the genuine compact product

Public module ID: M0845.

AR04: ASI I Proposition (4.4), pp.504--505, uses the common Euclidean open
subset of a sphere and a product of spheres. The two compact manifolds are
not identified. The product value below is the original full analytic index
on the actual product of the native spheres, after the original cotangent
external product. Its factors are exactly the original pole classes transported
by their prescribed round musical maps.

Excision compares the two compact environments. The pullbacks of their
round metrics to the same Euclidean base need not agree. A proper homotopy
through positive definite fiber maps identifies the two corresponding
cotangent classes before analytic excision is applied. The unchanged graded
Bott direct-sum comparison and the actual ordered block inclusion are used.
The subsequent equality with the representation external product is AR03
on this genuine compact product, including zero-dimensional factors.

Sources: ASI I (2.6), p.494; excision B1, p.502; Proposition (4.4), pp.504--505;
and different-group multiplicativity, section 9, pp.526--529. SG III.13.4--5,
pp.248--250, supplies the analytic excision and product mechanisms. Exact
musical, native-action and coordinate comparisons are project supplements.
The common-open comparison below retains these exact classes and maps.
No normalization theorem or final Atiyah--Singer theorem is an input to this
binary index comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent

/-- The actual index of the original two pole classes on the compact product of spheres. -/
def orthogonalSphereProductPoleIndex (p q : ℕ) (atInfinity : Bool) :
    RepresentationGrothendieckGroup
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) := by
  -- Adapt only the action certificate of each original cotangent class.
  let nativePoleClass (r : ℕ) :
      letI := lieGroup_orthogonalGroup r
      letI := smoothCotangentMulAction (n := r)
        (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r)
      letI := (smoothCotangentMulAction (n := r)
        (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r)).toSMul
      letI := contMDiffSMul_smoothCotangent (n := r)
        (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r)
      letI : ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
          (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
        ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel r))
          (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
      EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) := by
    let u := orthogonalSphereMusicalKMap r (orthogonalSpherePolePushforward r atInfinity 1)
    letI := lieGroup_orthogonalGroup r
    have hLift : smoothCotangentMulAction (n := r)
        (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
        𝓘(ℝ, OrthogonalGroupModel r) = orthogonalSphereCotangentMulAction r := by
      apply MulAction.ext
      funext A z
      have he : Diffeomorph.smul (M := OrthogonalSphere r)
          𝓘(ℝ, OrthogonalGroupModel r) (𝓡 r) ∞ A = orthogonalSphereDiffeomorph r A := by
        apply Diffeomorph.ext
        intro x
        rfl
      exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) he
    have transport
        (a b : MulAction (Matrix.orthogonalGroup (Fin r) ℝ)
          (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))
        (ha : letI := a
          letI := a.toSMul
          ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
            (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))
        (hb : letI := b
          letI := b.toSMul
          ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
            (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)))
        (hab : a = b) :
        (letI := a
         letI := a.toSMul
         letI := ha
         EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
           (CotangentTotalSpace (n := r) (M := OrthogonalSphere r))) →
        (letI := b
         letI := b.toSMul
         letI := hb
         EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
           (CotangentTotalSpace (n := r) (M := OrthogonalSphere r))) := by
      cases hab
      exact id
    letI := smoothCotangentMulAction (n := r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      𝓘(ℝ, OrthogonalGroupModel r)
    letI := (smoothCotangentMulAction (n := r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      𝓘(ℝ, OrthogonalGroupModel r)).toSMul
    letI := contMDiffSMul_smoothCotangent (n := r)
      (G := Matrix.orthogonalGroup (Fin r) ℝ) (M := OrthogonalSphere r)
      𝓘(ℝ, OrthogonalGroupModel r)
    letI : ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)
        (CotangentTotalSpace (n := r) (M := OrthogonalSphere r)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel r))
        (I' := (𝓡 r).prod 𝓘(ℝ, CotangentModel r)) ∞
    exact transport _ _ (continuousSMul_orthogonalSphereCotangent r)
      inferInstance hLift.symm u
  letI := lieGroup_orthogonalGroup p
  letI := lieGroup_orthogonalGroup q
  letI := compactSpace_orthogonalGroup p
  letI := compactSpace_orthogonalGroup q
  letI : MeasurableSpace (Matrix.orthogonalGroup (Fin p) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin p) ℝ)
  letI : BorelSpace (Matrix.orthogonalGroup (Fin p) ℝ) := ⟨rfl⟩
  letI : MeasurableSpace (Matrix.orthogonalGroup (Fin q) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin q) ℝ)
  letI : BorelSpace (Matrix.orthogonalGroup (Fin q) ℝ) := ⟨rfl⟩
  letI : MeasurableSpace (OrthogonalSphere p) := borel (OrthogonalSphere p)
  letI : BorelSpace (OrthogonalSphere p) := ⟨rfl⟩
  letI : MeasurableSpace (OrthogonalSphere q) := borel (OrthogonalSphere q)
  letI : BorelSpace (OrthogonalSphere q) := ⟨rfl⟩
  letI : ChartedSpace (OrthogonalGroupModel p × OrthogonalGroupModel q)
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) :=
    prodChartedSpace (OrthogonalGroupModel p) (Matrix.orthogonalGroup (Fin p) ℝ)
      (OrthogonalGroupModel q) (Matrix.orthogonalGroup (Fin q) ℝ)
  letI : LieGroup 𝓘(ℝ, OrthogonalGroupModel p × OrthogonalGroupModel q) ∞
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact Prod.instLieGroup
      (I := 𝓘(ℝ, OrthogonalGroupModel p)) (I' := 𝓘(ℝ, OrthogonalGroupModel q))
  -- Retain the separate original sphere actions in the specified product atlas.
  letI : MulAction
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere p) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst
      (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
  letI : SMul
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere p) :=
    (MulAction.compHom (OrthogonalSphere p) (ContinuousMonoidHom.fst
      (Matrix.orthogonalGroup (Fin p) ℝ)
      (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom).toSMul
  letI : ContinuousSMul
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere p) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst
      (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
  letI : MulAction
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere q) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd
      (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
  letI : SMul
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere q) :=
    (MulAction.compHom (OrthogonalSphere q) (ContinuousMonoidHom.snd
      (Matrix.orthogonalGroup (Fin p) ℝ)
      (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom).toSMul
  letI : ContinuousSMul
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere q) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd
      (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
  letI := euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  letI := isManifold_euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  letI := contMDiffSMul_euclideanProduct (n := p) (m := q)
    (VG := OrthogonalGroupModel p) (VH := OrthogonalGroupModel q)
    (G := Matrix.orthogonalGroup (Fin p) ℝ) (H := Matrix.orthogonalGroup (Fin q) ℝ)
    (OrthogonalSphere p) (OrthogonalSphere q)
  letI : MeasurableSpace
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
  letI : BorelSpace
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) := ⟨rfl⟩
  letI : MeasurableSpace (OrthogonalSphere p × OrthogonalSphere q) :=
    borel (OrthogonalSphere p × OrthogonalSphere q)
  letI : BorelSpace (OrthogonalSphere p × OrthogonalSphere q) := ⟨rfl⟩
  -- This is the actual AR03 cotangent product and the actual product-manifold index.
  exact equivariantAnalyticIndexMap (n := p + q)
    (VG := OrthogonalGroupModel p × OrthogonalGroupModel q)
    (G := Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
    (M := OrthogonalSphere p × OrthogonalSphere q)
    (equivariantCotangentKZeroExternalProduct (n := p) (m := q)
      (VG := OrthogonalGroupModel p) (VH := OrthogonalGroupModel q)
      (nativePoleClass p) (nativePoleClass q))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3200000 in
-- The same native actions and common-open maps are fixed before comparing their support classes.
/-- The common Euclidean open set compares the actual sphere and compact-product pole indices. -/
theorem orthogonalSpherePoleIndex_directSum_excision (p q : ℕ) (atInfinity : Bool) :
    representationRestrictionRingHom (orthogonalDirectSumInclusion p q)
        (orthogonalSphereTangentAnalyticIndex (p + q)
          (orthogonalSpherePolePushforward (p + q) atInfinity 1)) =
      orthogonalSphereProductPoleIndex p q atInfinity := by
  /- Use the same block action on the common Euclidean open source. The two
  prescribed pole diffeomorphisms induce its original inverse-dual cotangent
  embeddings into the sphere and sphere product. Analytic excision compares
  their indices on one specified source class.
  The positive-fiber homotopy in orthogonalSphereMusicalKMap_polePushforward
  identifies each original musical pole class with its cotangent chart class.
  On the sphere, restrict the full orthogonal index and transport the raw
  restricted action to the native cotangent lift. On the product, the original
  complex direct-sum Bott formula and open-product naturality identify the
  class through the canonical cotangent splitting. The chart-splitting
  identity checks the actual maps, including their ordered coordinates.
  Finally compose these two class comparisons with that same excision
  equality. Zero-dimensional factors keep their selected sphere point.
  Neither a global sphere/product diffeomorphism nor an index normalization
  theorem is used. -/
  classical
  let := lieGroup_orthogonalGroup p
  let := lieGroup_orthogonalGroup q
  let := compactSpace_orthogonalGroup p
  let := compactSpace_orthogonalGroup q
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin p) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin p) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin p) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin q) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin q) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin q) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere p) := borel (OrthogonalSphere p)
  let : BorelSpace (OrthogonalSphere p) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere q) := borel (OrthogonalSphere q)
  let : BorelSpace (OrthogonalSphere q) := ⟨rfl⟩
  let : ChartedSpace (OrthogonalGroupModel p × OrthogonalGroupModel q)
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) :=
    prodChartedSpace (OrthogonalGroupModel p) (Matrix.orthogonalGroup (Fin p) ℝ)
      (OrthogonalGroupModel q) (Matrix.orthogonalGroup (Fin q) ℝ)
  let : LieGroup 𝓘(ℝ, OrthogonalGroupModel p × OrthogonalGroupModel q) ∞
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) := by
    rw [modelWithCornersSelf_prod]
    exact Prod.instLieGroup
      (I := 𝓘(ℝ, OrthogonalGroupModel p)) (I' := 𝓘(ℝ, OrthogonalGroupModel q))
  -- Retain the separate original sphere actions in the specified product atlas.
  let : MulAction
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere p) :=
    MulAction.compHom _ (ContinuousMonoidHom.fst
      (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
  let : SMul
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere p) :=
    (MulAction.compHom (OrthogonalSphere p) (ContinuousMonoidHom.fst
      (Matrix.orthogonalGroup (Fin p) ℝ)
      (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom).toSMul
  let : ContinuousSMul
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere p) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst
      (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
  let : MulAction
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere q) :=
    MulAction.compHom _ (ContinuousMonoidHom.snd
      (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
  let : SMul
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere q) :=
    (MulAction.compHom (OrthogonalSphere q) (ContinuousMonoidHom.snd
      (Matrix.orthogonalGroup (Fin p) ℝ)
      (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom).toSMul
  let : ContinuousSMul
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
      (OrthogonalSphere q) :=
    MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd
      (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
  let := euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let := isManifold_euclideanProductChartedSpace (n := p) (m := q)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let := contMDiffSMul_euclideanProduct (n := p) (m := q)
    (VG := OrthogonalGroupModel p) (VH := OrthogonalGroupModel q)
    (G := Matrix.orthogonalGroup (Fin p) ℝ) (H := Matrix.orthogonalGroup (Fin q) ℝ)
    (OrthogonalSphere p) (OrthogonalSphere q)
  let : MeasurableSpace
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
  let : BorelSpace
      (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere p × OrthogonalSphere q) :=
    borel (OrthogonalSphere p × OrthogonalSphere q)
  let : BorelSpace (OrthogonalSphere p × OrthogonalSphere q) := ⟨rfl⟩
  let G := Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ
  let IG := 𝓘(ℝ, OrthogonalGroupModel p × OrthogonalGroupModel q)
  let φ := orthogonalDirectSumInclusion p q
  let := lieGroup_orthogonalGroup (p + q)
  let := compactSpace_orthogonalGroup (p + q)
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin (p + q)) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin (p + q)) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin (p + q)) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere (p + q)) := borel (OrthogonalSphere (p + q))
  let : BorelSpace (OrthogonalSphere (p + q)) := ⟨rfl⟩
  have hφ : ContMDiff IG 𝓘(ℝ, OrthogonalGroupModel (p + q)) ∞ φ := by
    simpa only [IG, modelWithCornersSelf_prod] using orthogonalDirectSumInclusion_smooth p q
  let : MulAction G (OrthogonalSphere (p + q)) := MulAction.compHom _ φ.toMonoidHom
  let : ContinuousSMul G (OrthogonalSphere (p + q)) :=
    MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul IG (𝓡 (p + q)) ∞ G (OrthogonalSphere (p + q)) :=
    MulAction.contMDiffSMul_compHom hφ
  let := orthogonalEuclideanMulAction (p + q)
  let := contMDiffSMul_orthogonalEuclidean (p + q)
  let : MulAction G (EuclideanSpace ℝ (Fin (p + q))) := MulAction.compHom _ φ.toMonoidHom
  let : SMul G (EuclideanSpace ℝ (Fin (p + q))) :=
    (MulAction.compHom (EuclideanSpace ℝ (Fin (p + q))) φ.toMonoidHom).toSMul
  let : ContMDiffSMul IG (𝓡 (p + q)) ∞ G (EuclideanSpace ℝ (Fin (p + q))) :=
    MulAction.contMDiffSMul_compHom hφ
  let : ContinuousSMul G (EuclideanSpace ℝ (Fin (p + q))) :=
    ContMDiffSMul.continuousSMul (I := IG) (I' := 𝓡 (p + q)) ∞
  let U := orthogonalSpherePoleOpen (p + q) atInfinity
  let V := orthogonalSphereProductPoleOpen p q atInfinity
  let f := orthogonalSpherePoleDiffeomorph (p + q) atInfinity
  let g := orthogonalSphereProductPoleDiffeomorph p q atInfinity
  have hf (a : G) (u : EuclideanSpace ℝ (Fin (p + q))) :
      (f (a • u) : OrthogonalSphere (p + q)) = a • (f u : OrthogonalSphere (p + q)) :=
    orthogonalSpherePoleDiffeomorph_equivariant (p + q) atInfinity (φ a) u
  have hg (a : G) (u : EuclideanSpace ℝ (Fin (p + q))) :
      (g (a • u) : OrthogonalSphere p × OrthogonalSphere q) =
        a • (g u : OrthogonalSphere p × OrthogonalSphere q) :=
    orthogonalSphereProductPoleDiffeomorph_equivariant p q atInfinity a u
  -- Analytic excision will be applied to precisely this common source and these two charts.
  have hex := equivariantAnalyticIndexMap_excision
    (n := p + q) (G := G) (O := EuclideanSpace ℝ (Fin (p + q)))
    (M := OrthogonalSphere (p + q)) (N := OrthogonalSphere p × OrthogonalSphere q)
    (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) U V f g hf hg
  let : MulAction G (EuclideanSpace ℂ (Fin (p + q))) :=
    MulAction.compHom _ φ.toMonoidHom
  let : SMul G (EuclideanSpace ℂ (Fin (p + q))) :=
    (MulAction.compHom (EuclideanSpace ℂ (Fin (p + q))) φ.toMonoidHom).toSMul
  let : ContinuousSMul G (EuclideanSpace ℂ (Fin (p + q))) :=
    MulAction.continuousSMul_compHom φ.continuous
  let := smoothCotangentMulAction (n := p + q) (G := G)
    (M := EuclideanSpace ℝ (Fin (p + q))) IG
  let : SMul G
      (CotangentTotalSpace (n := p + q) (M := EuclideanSpace ℝ (Fin (p + q)))) :=
    (smoothCotangentMulAction (n := p + q) (G := G)
      (M := EuclideanSpace ℝ (Fin (p + q))) IG).toSMul
  let := contMDiffSMul_smoothCotangent (n := p + q) (G := G)
    (M := EuclideanSpace ℝ (Fin (p + q))) IG
  let : ContinuousSMul G
      (CotangentTotalSpace (n := p + q) (M := EuclideanSpace ℝ (Fin (p + q)))) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := (𝓡 (p + q)).prod 𝓘(ℝ, CotangentModel (p + q))) ∞
  let C := euclideanCotangentComplexHomeomorph (p + q)
  have hCi (a : G) (z : EuclideanSpace ℂ (Fin (p + q))) :
      C.symm (a • z) = a • C.symm z :=
    euclideanCotangentComplexHomeomorph_symm_equivariant (p + q) φ hφ a z
  have hCe (a : G)
      (w : CotangentTotalSpace (n := p + q) (M := EuclideanSpace ℝ (Fin (p + q)))) :
      C (a • w) = a • C w := by
    apply C.symm.injective
    rw [C.symm_apply_apply, hCi, C.symm_apply_apply]
  let b := equivariantSupportTripleKZeroRestrict φ
    (equivariantExteriorBottClass (orthogonalComplexification_unitary (p + q)))
  let u := equivariantSupportTripleKZeroPullback ⟨C, C.continuous⟩ hCe C.isProperMap b
  have hu : u = equivariantSupportTripleKZeroOpenPushforward ⟨C.symm, C.symm.continuous⟩
      C.symm.isOpenEmbedding hCi b := by
    exact DFunLike.congr_fun
      (equivariantSupportTripleKZeroPullback_eq_openPushforward_symm C hCe hCi) b
  have hindex := DFunLike.congr_fun hex u
  let := smoothCotangentMulAction (n := p + q) (G := G)
    (M := OrthogonalSphere (p + q)) IG
  let : SMul G (CotangentTotalSpace (n := p + q) (M := OrthogonalSphere (p + q))) :=
    (smoothCotangentMulAction (n := p + q) (G := G)
      (M := OrthogonalSphere (p + q)) IG).toSMul
  let := contMDiffSMul_smoothCotangent (n := p + q) (G := G)
    (M := OrthogonalSphere (p + q)) IG
  let : ContinuousSMul G
      (CotangentTotalSpace (n := p + q) (M := OrthogonalSphere (p + q))) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := (𝓡 (p + q)).prod 𝓘(ℝ, CotangentModel (p + q))) ∞
  let := smoothCotangentMulAction (n := p + q) (G := G)
    (M := OrthogonalSphere p × OrthogonalSphere q) IG
  let : SMul G
      (CotangentTotalSpace (n := p + q) (M := OrthogonalSphere p × OrthogonalSphere q)) :=
    (smoothCotangentMulAction (n := p + q) (G := G)
      (M := OrthogonalSphere p × OrthogonalSphere q) IG).toSMul
  let := contMDiffSMul_smoothCotangent (n := p + q) (G := G)
    (M := OrthogonalSphere p × OrthogonalSphere q) IG
  let : ContinuousSMul G
      (CotangentTotalSpace (n := p + q) (M := OrthogonalSphere p × OrthogonalSphere q)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := (𝓡 (p + q)).prod 𝓘(ℝ, CotangentModel (p + q))) ∞
  let k₁ := cotangentOpenEmbeddingMap U f
  let k₂ := cotangentOpenEmbeddingMap V g
  have hk₁ := isOpenEmbedding_cotangentOpenEmbeddingMap U f
  have hk₂ := isOpenEmbedding_cotangentOpenEmbeddingMap V g
  have he₁ := cotangentOpenEmbeddingMap_equivariant
    (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) U f hf
  have he₂ := cotangentOpenEmbeddingMap_equivariant
    (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) V g hg
  let j₁ := orthogonalSphereCotangentChart (p + q) atInfinity
  let j₂ := orthogonalSphereProductCotangentChart p q atInfinity
  have hj₁ := orthogonalSphereCotangentChart_isOpenEmbedding (p + q) atInfinity
  have hj₂ := orthogonalSphereProductCotangentChart_isOpenEmbedding p q atInfinity
  have hje₁ (a : G) (z : EuclideanSpace ℂ (Fin (p + q))) : j₁ (a • z) = a • j₁ z := by
    change k₁ (C.symm (a • z)) = a • k₁ (C.symm z)
    rw [hCi]
    exact he₁ a (C.symm z)
  have hje₂ (a : G) (z : EuclideanSpace ℂ (Fin (p + q))) : j₂ (a • z) = a • j₂ z := by
    change k₂ (C.symm (a • z)) = a • k₂ (C.symm z)
    rw [hCi]
    exact he₂ a (C.symm z)
  have hpush₁ : equivariantCotangentKZeroOpenEmbedding
      (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) U f hf u =
        equivariantSupportTripleKZeroOpenPushforward j₁ hj₁ hje₁ b := by
    change equivariantSupportTripleKZeroOpenPushforward k₁ hk₁ he₁ u = _
    rw [hu]
    exact (DFunLike.congr_fun (equivariantSupportTripleKZeroOpenPushforward_functoriality.2
      ⟨C.symm, C.symm.continuous⟩ C.symm.isOpenEmbedding hCi k₁ hk₁ he₁) b).symm
  have hpush₂ : equivariantCotangentKZeroOpenEmbedding
      (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) V g hg u =
        equivariantSupportTripleKZeroOpenPushforward j₂ hj₂ hje₂ b := by
    change equivariantSupportTripleKZeroOpenPushforward k₂ hk₂ he₂ u = _
    rw [hu]
    exact (DFunLike.congr_fun (equivariantSupportTripleKZeroOpenPushforward_functoriality.2
      ⟨C.symm, C.symm.continuous⟩ C.symm.isOpenEmbedding hCi k₂ hk₂ he₂) b).symm
  let A := equivariantAnalyticIndexMap (n := p + q)
    (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) (G := G)
    (M := OrthogonalSphere (p + q))
  let B := equivariantAnalyticIndexMap (n := p + q)
    (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) (G := G)
    (M := OrthogonalSphere p × OrthogonalSphere q)
  have hcommon : A (equivariantSupportTripleKZeroOpenPushforward j₁ hj₁ hje₁ b) =
      B (equivariantSupportTripleKZeroOpenPushforward j₂ hj₂ hje₂ b) := by
    change A (equivariantCotangentKZeroOpenEmbedding
      (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) U f hf u) =
        B (equivariantCotangentKZeroOpenEmbedding
          (VG := OrthogonalGroupModel p × OrthogonalGroupModel q) V g hg u) at hindex
    simpa only [hpush₁, hpush₂] using hindex
  -- Convert the original pole index once, before applying native group restriction.
  let NA := smoothCotangentMulAction (n := p + q)
    (G := Matrix.orthogonalGroup (Fin (p + q)) ℝ) (M := OrthogonalSphere (p + q))
    𝓘(ℝ, OrthogonalGroupModel (p + q))
  let := NA
  let : SMul (Matrix.orthogonalGroup (Fin (p + q)) ℝ)
      (CotangentTotalSpace (n := p + q) (M := OrthogonalSphere (p + q))) := NA.toSMul
  let := contMDiffSMul_smoothCotangent (n := p + q)
    (G := Matrix.orthogonalGroup (Fin (p + q)) ℝ) (M := OrthogonalSphere (p + q))
    𝓘(ℝ, OrthogonalGroupModel (p + q))
  let : ContinuousSMul (Matrix.orthogonalGroup (Fin (p + q)) ℝ)
      (CotangentTotalSpace (n := p + q) (M := OrthogonalSphere (p + q))) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel (p + q)))
      (I' := (𝓡 (p + q)).prod 𝓘(ℝ, CotangentModel (p + q))) ∞
  have hNative : NA = orthogonalSphereCotangentMulAction (p + q) := by
    apply MulAction.ext
    funext a z
    have hd : Diffeomorph.smul (M := OrthogonalSphere (p + q))
        𝓘(ℝ, OrthogonalGroupModel (p + q)) (𝓡 (p + q)) ∞ a =
        orthogonalSphereDiffeomorph (p + q) a := by
      apply Diffeomorph.ext
      intro x
      rfl
    exact congrArg (fun e ↦ cotangentDiffeomorphMap e z) hd
  have heNative (a : Matrix.orthogonalGroup (Fin (p + q)) ℝ)
      (z : EuclideanSpace ℂ (Fin (p + q))) :
      j₁ (orthogonalComplexificationRepresentation (p + q) a z) = a • j₁ z := by
    change j₁ (orthogonalComplexificationRepresentation (p + q) a z) = NA.smul a (j₁ z)
    rw [hNative]
    exact orthogonalSphereCotangentChart_equivariant (p + q) atInfinity a z
  have hPole := orthogonalSpherePoleIndex_eq_nativeOpenIndex
    (p + q) atInfinity heNative
  have hrestriction := representationRestriction_equivariantAnalyticIndexMap_openPushforward
    (n := p + q) (M := OrthogonalSphere (p + q))
    (VG := OrthogonalGroupModel (p + q))
    (VH := OrthogonalGroupModel p × OrthogonalGroupModel q) φ hφ j₁ hj₁
    heNative hje₁
    (equivariantExteriorBottClass (orthogonalComplexification_unitary (p + q)))
  have hleft : representationRestrictionRingHom φ
      (orthogonalSphereTangentAnalyticIndex (p + q)
        (orthogonalSpherePolePushforward (p + q) atInfinity 1)) =
        A (equivariantSupportTripleKZeroOpenPushforward j₁ hj₁ hje₁ b) := by
    exact (congrArg (representationRestrictionRingHom φ) hPole).trans
      hrestriction
  have hright : B (equivariantSupportTripleKZeroOpenPushforward j₂ hj₂ hje₂ b) =
      orthogonalSphereProductPoleIndex p q atInfinity := by
    -- The product class uses the same two native factor lifts and the specified splitting.
    let := smoothCotangentMulAction (n := p)
      (G := Matrix.orthogonalGroup (Fin p) ℝ) (M := OrthogonalSphere p)
      𝓘(ℝ, OrthogonalGroupModel p)
    let := contMDiffSMul_smoothCotangent (n := p)
      (G := Matrix.orthogonalGroup (Fin p) ℝ) (M := OrthogonalSphere p)
      𝓘(ℝ, OrthogonalGroupModel p)
    let : ContinuousSMul (Matrix.orthogonalGroup (Fin p) ℝ)
        (CotangentTotalSpace (n := p) (M := OrthogonalSphere p)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel p))
        (I' := (𝓡 p).prod 𝓘(ℝ, CotangentModel p)) ∞
    let : MulAction G (EuclideanSpace ℂ (Fin p)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
    let : SMul G (EuclideanSpace ℂ (Fin p)) :=
      (MulAction.compHom (EuclideanSpace ℂ (Fin p)) (ContinuousMonoidHom.fst
        (Matrix.orthogonalGroup (Fin p) ℝ)
        (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom).toSMul
    let : ContinuousSMul G (EuclideanSpace ℂ (Fin p)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
    let : MulAction G (CotangentTotalSpace (n := p) (M := OrthogonalSphere p)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
    let : SMul G (CotangentTotalSpace (n := p) (M := OrthogonalSphere p)) :=
      (MulAction.compHom (CotangentTotalSpace (n := p) (M := OrthogonalSphere p))
        (ContinuousMonoidHom.fst (Matrix.orthogonalGroup (Fin p) ℝ)
          (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom).toSMul
    let : ContinuousSMul G (CotangentTotalSpace (n := p) (M := OrthogonalSphere p)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
    let := smoothCotangentMulAction (n := q)
      (G := Matrix.orthogonalGroup (Fin q) ℝ) (M := OrthogonalSphere q)
      𝓘(ℝ, OrthogonalGroupModel q)
    let := contMDiffSMul_smoothCotangent (n := q)
      (G := Matrix.orthogonalGroup (Fin q) ℝ) (M := OrthogonalSphere q)
      𝓘(ℝ, OrthogonalGroupModel q)
    let : ContinuousSMul (Matrix.orthogonalGroup (Fin q) ℝ)
        (CotangentTotalSpace (n := q) (M := OrthogonalSphere q)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, OrthogonalGroupModel q))
        (I' := (𝓡 q).prod 𝓘(ℝ, CotangentModel q)) ∞
    let : MulAction G (EuclideanSpace ℂ (Fin q)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
    let : SMul G (EuclideanSpace ℂ (Fin q)) :=
      (MulAction.compHom (EuclideanSpace ℂ (Fin q)) (ContinuousMonoidHom.snd
        (Matrix.orthogonalGroup (Fin p) ℝ)
        (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom).toSMul
    let : ContinuousSMul G (EuclideanSpace ℂ (Fin q)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
    let : MulAction G (CotangentTotalSpace (n := q) (M := OrthogonalSphere q)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
    let : SMul G (CotangentTotalSpace (n := q) (M := OrthogonalSphere q)) :=
      (MulAction.compHom (CotangentTotalSpace (n := q) (M := OrthogonalSphere q))
        (ContinuousMonoidHom.snd (Matrix.orthogonalGroup (Fin p) ℝ)
          (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom).toSMul
    let : ContinuousSMul G (CotangentTotalSpace (n := q) (M := OrthogonalSphere q)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
    let K := cotangentProductHomeomorph (n := p) (m := q)
      (OrthogonalSphere p) (OrthogonalSphere q)
    have hKe (a : G)
        (z : CotangentTotalSpace (n := p + q) (M := OrthogonalSphere p × OrthogonalSphere q)) :
        K (a • z) = a • K z :=
      cotangentProductHomeomorph_equivariant (n := p) (m := q)
        (VG := OrthogonalGroupModel p) (VH := OrthogonalGroupModel q)
        (G := Matrix.orthogonalGroup (Fin p) ℝ) (H := Matrix.orthogonalGroup (Fin q) ℝ)
        (OrthogonalSphere p) (OrthogonalSphere q) a z
    have hKi (a : G)
        (z : CotangentTotalSpace (n := p) (M := OrthogonalSphere p) ×
          CotangentTotalSpace (n := q) (M := OrthogonalSphere q)) :
        K.symm (a • z) = a • K.symm z := by
      apply K.injective
      rw [K.apply_symm_apply, hKe, K.apply_symm_apply]
    let E := (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := p) (m := q)).toHomeomorph
    have hEi (a : G) (z : EuclideanSpace ℂ (Fin p) × EuclideanSpace ℂ (Fin q)) :
        E.symm (a • z) = a • E.symm z :=
      orthogonalDirectSumInclusion_complexification p q a z
    have hEe (a : G) (z : EuclideanSpace ℂ (Fin (p + q))) :
        E (a • z) = a • E z := by
      apply E.symm.injective
      rw [E.symm_apply_apply, hEi, E.symm_apply_apply]
    let e : C(EuclideanSpace ℂ (Fin (p + q)),
        EuclideanSpace ℂ (Fin p) × EuclideanSpace ℂ (Fin q)) := ⟨E, E.continuous⟩
    let J := (orthogonalSphereCotangentChart p atInfinity).prodMap
      (orthogonalSphereCotangentChart q atInfinity)
    have hJ : Topology.IsOpenEmbedding J :=
      (orthogonalSphereCotangentChart_isOpenEmbedding p atInfinity).prodMap
        (orthogonalSphereCotangentChart_isOpenEmbedding q atInfinity)
    have hJe (a : G) (z : EuclideanSpace ℂ (Fin p) × EuclideanSpace ℂ (Fin q)) :
        J (a • z) = a • J z :=
      Prod.ext (orthogonalSphereCotangentChart_equivariant p atInfinity a.1 z.1)
        (orthogonalSphereCotangentChart_equivariant q atInfinity a.2 z.2)
    let b₁ := equivariantExteriorBottClass (orthogonalComplexification_unitary p)
    let b₂ := equivariantExteriorBottClass (orthogonalComplexification_unitary q)
    have hBott : equivariantSupportTripleKZeroOpenPushforward e E.isOpenEmbedding hEe b =
        equivariantSupportKZeroDifferentGroupExternalProduct b₁ b₂ := by
      have hpull := equivariantSupportTripleKZeroPullback_eq_openPushforward_symm
        E.symm hEi hEe
      exact (DFunLike.congr_fun hpull b).symm.trans (orthogonalExteriorBottClass_directSum p q)
    have hopen : equivariantSupportTripleKZeroOpenPushforward J hJ hJe
        (equivariantSupportKZeroDifferentGroupExternalProduct b₁ b₂) =
        equivariantSupportKZeroDifferentGroupExternalProduct
          (orthogonalSphereMusicalKMap p (orthogonalSpherePolePushforward p atInfinity 1))
          (orthogonalSphereMusicalKMap q (orthogonalSpherePolePushforward q atInfinity 1)) := by
      rw [orthogonalSphereMusicalKMap_polePushforward,
        orthogonalSphereMusicalKMap_polePushforward]
      exact equivariantSupportKZeroDifferentGroupExternalProduct_openPushforward
        (orthogonalSphereCotangentChart p atInfinity)
        (orthogonalSphereCotangentChart_isOpenEmbedding p atInfinity)
        (orthogonalSphereCotangentChart_equivariant p atInfinity)
        (orthogonalSphereCotangentChart q atInfinity)
        (orthogonalSphereCotangentChart_isOpenEmbedding q atInfinity)
        (orthogonalSphereCotangentChart_equivariant q atInfinity) b₁ b₂
    -- The same ordered complex splitting intertwines the two actual cotangent charts.
    let k : C(CotangentTotalSpace (n := p) (M := OrthogonalSphere p) ×
        CotangentTotalSpace (n := q) (M := OrthogonalSphere q),
        CotangentTotalSpace (n := p + q) (M := OrthogonalSphere p × OrthogonalSphere q)) :=
      ⟨K.symm, K.symm.continuous⟩
    have hJe' (a : G) (z : EuclideanSpace ℂ (Fin (p + q))) :
        (J.comp e) (a • z) = a • (J.comp e) z :=
      (congrArg J (hEe a z)).trans (hJe a (e z))
    have hmaps : k.comp (J.comp e) = j₂ := by
      apply ContinuousMap.ext
      intro z
      apply K.injective
      change K (K.symm (J (E z))) = K (j₂ z)
      rw [K.apply_symm_apply]
      exact (orthogonalSphereProductCotangentChart_split p q atInfinity z).symm
    have hfun₁ := DFunLike.congr_fun
      ((equivariantSupportTripleKZeroOpenPushforward_functoriality (G := G)
        (X := EuclideanSpace ℂ (Fin (p + q)))
        (Y := EuclideanSpace ℂ (Fin p) × EuclideanSpace ℂ (Fin q))
        (Z := CotangentTotalSpace (n := p) (M := OrthogonalSphere p) ×
          CotangentTotalSpace (n := q) (M := OrthogonalSphere q))).2
          e E.isOpenEmbedding hEe J hJ hJe) b
    have hfun₂ := DFunLike.congr_fun
      ((equivariantSupportTripleKZeroOpenPushforward_functoriality (G := G)
        (X := EuclideanSpace ℂ (Fin (p + q)))
        (Y := CotangentTotalSpace (n := p) (M := OrthogonalSphere p) ×
          CotangentTotalSpace (n := q) (M := OrthogonalSphere q))
        (Z := CotangentTotalSpace (n := p + q) (M := OrthogonalSphere p × OrthogonalSphere q))).2
          (J.comp e) (hJ.comp E.isOpenEmbedding) hJe' k K.symm.isOpenEmbedding hKi) b
    have hclass : equivariantSupportTripleKZeroOpenPushforward j₂ hj₂ hje₂ b =
        equivariantSupportTripleKZeroOpenPushforward k K.symm.isOpenEmbedding hKi
          (equivariantSupportKZeroDifferentGroupExternalProduct
            (orthogonalSphereMusicalKMap p (orthogonalSpherePolePushforward p atInfinity 1))
            (orthogonalSphereMusicalKMap q
              (orthogonalSpherePolePushforward q atInfinity 1))) := by
      have hcomp := hfun₂.trans
        (congrArg (equivariantSupportTripleKZeroOpenPushforward k K.symm.isOpenEmbedding hKi)
          hfun₁)
      change equivariantSupportTripleKZeroOpenPushforward (k.comp (J.comp e)) _ _ b =
        equivariantSupportTripleKZeroOpenPushforward k K.symm.isOpenEmbedding hKi
          (equivariantSupportTripleKZeroOpenPushforward J hJ hJe
            (equivariantSupportTripleKZeroOpenPushforward e E.isOpenEmbedding hEe b)) at hcomp
      rw [hBott, hopen] at hcomp
      simpa only [hmaps] using hcomp
    rw [hclass]
    have hpull := equivariantSupportTripleKZeroPullback_eq_openPushforward_symm K hKe hKi
    have hvalue := congrArg B (DFunLike.congr_fun hpull
      (equivariantSupportKZeroDifferentGroupExternalProduct
        (orthogonalSphereMusicalKMap p (orthogonalSpherePolePushforward p atInfinity 1))
        (orthogonalSphereMusicalKMap q (orthogonalSpherePolePushforward q atInfinity 1))))
    -- Unfold only the prescribed index and product; their original transports agree.
    exact hvalue.symm
  exact hleft.trans (hcommon.trans hright)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- AR03 evaluates this genuine compact-product index by the original two factor indices. -/
theorem orthogonalSphereProductPoleIndex_eq (p q : ℕ) (atInfinity : Bool) :
    orthogonalSphereProductPoleIndex p q atInfinity =
      representationExternalProduct
        (orthogonalSphereTangentAnalyticIndex p
          (orthogonalSpherePolePushforward p atInfinity 1))
        (orthogonalSphereTangentAnalyticIndex q
          (orthogonalSpherePolePushforward q atInfinity 1)) := by
  /- Stage 1: unfold precisely the defined compact-product index and apply
  equivariantAnalyticIndexMap_externalProduct for O(p), O(q), S^p and S^q.
  Their native Cayley models, separate actions, original cotangent lifts
  and the concatenated Euclidean product atlas are the same installed
  instances. The external product uses the same canonical cotangent
  splitting and original support product, with no new Bott generator.
  Stage 2: each input is the original inverse-round-flat image of its pole
  class, transported only along equality of the native cotangent actions.
  The identical transport in orthogonalSphereAnalyticIndex makes the two
  factor values exactly orthogonalSphereTangentAnalyticIndex. Equality
  elimination for the same action equations, and proof irrelevance for
  the continuity certificates, identify these original quotient arguments.
  Stage 3: AR03 already includes zero-dimensional factors and disconnected
  compact manifolds. In particular its finite section calculation retains
  the chosen S0 point; no separate unit-index assumption enters. The
  inherited UL01/UL02 tensor-domain and symbol-cutoff comparisons are
  supplied by the full AR03 proof for the same cotangent product and representation index. -/
  let := lieGroup_orthogonalGroup p
  let := lieGroup_orthogonalGroup q
  let := compactSpace_orthogonalGroup p
  let := compactSpace_orthogonalGroup q
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin p) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin p) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin p) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin q) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin q) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin q) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere p) := borel (OrthogonalSphere p)
  let : BorelSpace (OrthogonalSphere p) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere q) := borel (OrthogonalSphere q)
  let : BorelSpace (OrthogonalSphere q) := ⟨rfl⟩
  have hm : (inferInstance : MeasurableSpace (OrthogonalSphere p × OrthogonalSphere q)) =
      borel (OrthogonalSphere p × OrthogonalSphere q) := BorelSpace.measurable_eq
  dsimp only [orthogonalSphereProductPoleIndex, orthogonalSphereTangentAnalyticIndex,
    AddMonoidHom.comp_apply, orthogonalSphereAnalyticIndex]
  have h := equivariantAnalyticIndexMap_externalProduct (n := p) (m := q)
    (VG := OrthogonalGroupModel p) (VH := OrthogonalGroupModel q)
    (G := Matrix.orthogonalGroup (Fin p) ℝ) (H := Matrix.orthogonalGroup (Fin q) ℝ)
    (M := OrthogonalSphere p) (N := OrthogonalSphere q)
    (orthogonalSphereMusicalKMap p (orthogonalSpherePolePushforward p atInfinity 1))
    (orthogonalSphereMusicalKMap q (orthogonalSpherePolePushforward q atInfinity 1))
  convert h using 2
  · congr 1
    · exact hm.symm
    · exact proof_irrel_heq _ _
  · rfl
  · rfl
  · rfl


/-- The actual orthogonal point index restricts to the product of the two actual point indices. -/
theorem orthogonalSpherePoleIndex_directSum (p q : ℕ) (atInfinity : Bool) :
    representationRestrictionRingHom (orthogonalDirectSumInclusion p q)
        (orthogonalSphereTangentAnalyticIndex (p + q)
          (orthogonalSpherePolePushforward (p + q) atInfinity 1)) =
      representationExternalProduct
        (orthogonalSphereTangentAnalyticIndex p
          (orthogonalSpherePolePushforward p atInfinity 1))
        (orthogonalSphereTangentAnalyticIndex q
          (orthogonalSpherePolePushforward q atInfinity 1)) := by
  /- First use the preceding common-open excision comparison with the
  actual sphere-product value. Then use its AR03 evaluation. Both steps
  retain the same two factor dimensions, pole choice, original Bott classes
  and native group actions. This establishes the binary relation before
  any low-dimensional normalization or character-detection argument. -/
  exact (orthogonalSpherePoleIndex_directSum_excision p q atInfinity).trans
    (orthogonalSphereProductPoleIndex_eq p q atInfinity)

end AtiyahSinger
