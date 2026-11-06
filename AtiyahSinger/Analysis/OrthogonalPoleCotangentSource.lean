/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantIndexExcision
public import AtiyahSinger.Geometry.OrthogonalEuclideanAction
public import AtiyahSinger.Geometry.SphereCotangentPoleCoordinates

/-!
# Native cotangent coordinates for the common orthogonal open source

Public module ID: M0844.

The same real Euclidean representation and its complexification are intertwined
by real Riesz duality. The comparison also retains any specified smooth subgroup
restriction. Its proof uses injectivity of the original pole cotangent chart,
so the actual inverse-differential action is kept throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology
open scoped Manifold ContDiff Matrix.Norms.L2Operator

set_option maxSynthPendingDepth 35

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Ordered complex coordinates intertwine the actual restricted Euclidean cotangent action. -/
theorem euclideanCotangentComplexHomeomorph_symm_equivariant (r : ℕ)
    (φ : G →ₜ* Matrix.orthogonalGroup (Fin r) ℝ)
    (hφ : ContMDiff 𝓘(ℝ, VG) 𝓘(ℝ, OrthogonalGroupModel r) ∞ φ) :
    letI := orthogonalEuclideanMulAction r
    letI := contMDiffSMul_orthogonalEuclidean r
    letI : MulAction G (EuclideanSpace ℝ (Fin r)) :=
      MulAction.compHom _ φ.toMonoidHom
    letI : ContMDiffSMul 𝓘(ℝ, VG) (𝓡 r) ∞ G (EuclideanSpace ℝ (Fin r)) :=
      MulAction.contMDiffSMul_compHom hφ
    letI := smoothCotangentMulAction (n := r) (G := G)
      (M := EuclideanSpace ℝ (Fin r)) 𝓘(ℝ, VG)
    ∀ (a : G) (z : EuclideanSpace ℂ (Fin r)),
      (euclideanCotangentComplexHomeomorph r).symm
          (orthogonalComplexificationRepresentation r (φ a) z) =
        a • (euclideanCotangentComplexHomeomorph r).symm z := by
  let := orthogonalEuclideanMulAction r
  let := contMDiffSMul_orthogonalEuclidean r
  let : MulAction G (EuclideanSpace ℝ (Fin r)) := MulAction.compHom _ φ.toMonoidHom
  let : ContMDiffSMul 𝓘(ℝ, VG) (𝓡 r) ∞ G (EuclideanSpace ℝ (Fin r)) :=
    MulAction.contMDiffSMul_compHom hφ
  let : ContinuousSMul G (EuclideanSpace ℝ (Fin r)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG)) (I' := 𝓡 r) ∞
  let := smoothCotangentMulAction (n := r) (G := G)
    (M := EuclideanSpace ℝ (Fin r)) 𝓘(ℝ, VG)
  let : MulAction G (OrthogonalSphere r) := MulAction.compHom _ φ.toMonoidHom
  let : ContMDiffSMul 𝓘(ℝ, VG) (𝓡 r) ∞ G (OrthogonalSphere r) :=
    MulAction.contMDiffSMul_compHom hφ
  let : ContinuousSMul G (OrthogonalSphere r) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG)) (I' := 𝓡 r) ∞
  let C := euclideanCotangentComplexHomeomorph r
  let U := orthogonalSpherePoleOpen r false
  let f := orthogonalSpherePoleDiffeomorph r false
  let k := cotangentOpenEmbeddingMap U f
  have hf (a : G) (u : EuclideanSpace ℝ (Fin r)) : (f (a • u) : OrthogonalSphere r) =
      a • (f u : OrthogonalSphere r) :=
    orthogonalSpherePoleDiffeomorph_equivariant r false (φ a) u
  have hk := cotangentOpenEmbeddingMap_equivariant (VG := VG) U f hf
  intro a z
  -- The faithful pole embedding compares the two specified lifts on the same covector.
  apply (isOpenEmbedding_cotangentOpenEmbeddingMap U f).injective
  change orthogonalSphereCotangentChart r false
    (orthogonalComplexificationRepresentation r (φ a) z) = k (a • C.symm z)
  rw [orthogonalSphereCotangentChart_equivariant]
  have he : Diffeomorph.smul (M := OrthogonalSphere r) 𝓘(ℝ, VG) (𝓡 r) ∞ a =
      orthogonalSphereDiffeomorph r (φ a) := by
    apply Diffeomorph.ext
    intro x
    rfl
  have hh := hk a (C.symm z)
  change k (a • C.symm z) = cotangentDiffeomorphMap
    (Diffeomorph.smul (M := OrthogonalSphere r) 𝓘(ℝ, VG) (𝓡 r) ∞ a) (k (C.symm z)) at hh
  rw [he] at hh
  exact hh.symm

end AtiyahSinger
