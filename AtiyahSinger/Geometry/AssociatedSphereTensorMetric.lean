/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereMetric
public import AtiyahSinger.Geometry.AssociatedSphereTensorBundle
public import AtiyahSinger.Geometry.TensorAtlasConnection

/-!
# The specified product metric on the associated tensor bundle

Public module ID: M1080.

Pull back the original base metric and tensor it with the descended original
invariant sphere metric. The smooth metric lives on the existing base-first
tensor fibers and has the exact product pairing at every original principal
representative. No auxiliary frame norm or sphere cutoff is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z

variable [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original factor metrics give the exact smooth product metric on the associated tensor. -/
theorem exists_associatedSphereTensorMetric
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (h : letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      ContinuousHermitianMetric E)
    (hh : letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      (nativeSmoothComplexBundleAtlas (n := n) (r := a) E).IsSmoothHermitianMetric h)
    (k : ContinuousHermitianMetric F) (hk : A.IsSmoothHermitianMetric k)
    (hInvariant : ∀ (g : G) (y : OrthogonalSphere r) (u v : F y),
      (k.toCore (g • y)).inner (σ.linearMap g y u) (σ.linearMap g y v) =
        (k.toCore y).inner u v) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∃ l : ContinuousHermitianMetric T,
      (associatedSphereTensorBundleAtlas S E A σ hσ).IsSmoothHermitianMetric l ∧
        ∀ (p : P) (y : OrthogonalSphere r) (u v : E (projection p)) (s t : F y),
          (l.toCore (associatedBundleMk G P (OrthogonalSphere r) p y)).inner
              (associatedSphereTensorFiberEquiv S E σ p y (u ⊗ₜ[ℂ] s))
              (associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] t)) =
            (h.toCore (projection p)).inner u v * (k.toCore y).inner s t := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph e Z
  let := linearModelChartedSpace e Z
  let := isManifold_linearModelChartedSpace e Z
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
    (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let hD := associatedEquivariantMetric S.toIsPrincipalBundle σ k hInvariant
  have hhD : AD.IsSmoothHermitianMetric hD :=
    isSmoothHermitianMetric_associatedEquivariantMetric S A σ hσ k hk hInvariant
  have hhE := AE.isSmoothHermitianMetric_pullback q hq h hh
  -- Both factors are the specified forms on the original pullback and quotient fibers.
  let l := tensorAtlasMetric (h.pullback q) hhE hD hhD
  have hl := tensorAtlasMetric_properties (h.pullback q) hhE hD hhD
  refine ⟨l, hl.1, ?_⟩
  intro p y u v s t
  have hprod := hl.2 (associatedBundleMk G P (OrthogonalSphere r) p y) u v
    (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl s)
    (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl t)
  have hfiber := associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ k hInvariant
    p y rfl s t
  exact hprod.trans (congrArg (fun c : ℂ ↦ (h.toCore (projection p)).inner u v * c) hfiber)

end AtiyahSinger
