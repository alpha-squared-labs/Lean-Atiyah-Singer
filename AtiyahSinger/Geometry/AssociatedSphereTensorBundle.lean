/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSmoothBundleDescent
public import AtiyahSinger.Geometry.NativeSmoothAtlas
public import AtiyahSinger.Geometry.SmoothAtlasPullback
public import AtiyahSinger.Geometry.SmoothTensorAtlas

/-!
# The original tensor bundle over an associated sphere

Public module ID: M1079.

Pull back the specified base bundle by the original quotient projection and
tensor it with the original associated equivariant bundle. The base factor
comes first. The smooth atlas retains the original principal, base and sphere
charts, and the only manifold model change is the specified Euclidean sum
equivalence already used for the associated sphere.

At each actual principal point, the fiber identification is the identity on
the base vector and the original quotient-fiber identification on the sphere
vector. These are shared data for both horizontal and vertical operators in
SG III.13.6, not a substitute finite-kernel bundle.
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

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified base-first tensor atlas on the original associated-sphere fibers. -/
def associatedSphereTensorBundleAtlas
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    SmoothComplexBundleAtlas (n := n + r) T := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
    (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
  exact tensorSmoothAtlas (E := (q : Z → B) *ᵖ E) (F := D)
    ((nativeSmoothComplexBundleAtlas (n := n) (r := a) E).pullback q hq)
    (associatedSphereSmoothBundleAtlas S A σ hσ)

set_option maxSynthPendingDepth 30 in
/-- The actual principal fiber identification keeps the original base tensor factor. -/
def associatedSphereTensorFiberEquiv (p : P) (y : OrthogonalSphere r) :
    E (projection p) ⊗[ℂ] F y ≃ₗ[ℂ]
      T (associatedBundleMk G P (OrthogonalSphere r) p y) :=
  TensorProduct.congr (LinearEquiv.refl ℂ (E (projection p)))
    (LinearEquiv.ofBijective
      (associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle σ p y rfl).mk'
      (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p y rfl))

omit [IsManifold (𝓡 n) ∞ B] in
/-- The specified identification has the unchanged base vector and original quotient vector. -/
theorem associatedSphereTensorFiberEquiv_tmul (p : P) (y : OrthogonalSphere r)
    (v : E (projection p)) (w : F y) :
    associatedSphereTensorFiberEquiv S E σ p y (v ⊗ₜ[ℂ] w) =
      v ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl w := rfl

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original tensor chart evaluates the base coordinate times the descended fiber coordinate. -/
theorem associatedSphereTensorBundleAtlas_chart_tmul
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (e : Trivialization (EuclideanSpace ℂ (Fin a))
      (π (EuclideanSpace ℂ (Fin a)) E)) (he : MemTrivializationAtlas e)
    (b : B) (j : A.Index) (p : P) (y : OrthogonalSphere r)
    (hp : projection p ∈ (S.trivialization b).baseSet)
    (hx : projection p ∈ e.baseSet)
    (hy : associatedBundleMk G P (OrthogonalSphere r) p y ∈
      (associatedSphereBundleChart S A σ (b, j)).baseSet)
    (v : E (projection p)) (w : F y) (i : Fin a) (k : Fin (A.rank j)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ((associatedSphereTensorBundleAtlas S E A σ hσ).chart (⟨e, he⟩, (b, j))
      ⟨associatedBundleMk G P (OrthogonalSphere r) p y,
        v ⊗ₜ[ℂ] associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl w⟩).2
        (finProdFinEquiv (i, k)) =
      (e ⟨projection p, v⟩).2 i *
        (A.chart j ⟨(S.trivialization b p).2 • y,
          σ.linearMap (S.trivialization b p).2 y w⟩).2 k := by
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let l := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  let d := linearModelDiffeomorph l Z
  let := linearModelChartedSpace l Z
  let AE := nativeSmoothComplexBundleAtlas (n := n) (r := a) E
  have hq : ContMDiff (𝓡 (n + r)) (𝓡 n) ∞ q :=
    (smoothAssociatedSphereProjection S).contMDiff.comp d.symm.contMDiff
  let AC := AE.pullback q hq
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let z := associatedBundleMk G P (OrthogonalSphere r) p y
  have hbase : z ∈ (AC.chart ⟨e, he⟩).baseSet := by
    have hbaseEq : (AC.chart ⟨e, he⟩).baseSet = q ⁻¹' (AE.chart ⟨e, he⟩).baseSet :=
      (AE.exists_pullbackChart q ⟨e, he⟩).choose_spec.1
    exact hbaseEq.symm ▸ hx
  have h := (exists_tensor_trivialization (AC.chart ⟨e, he⟩) (AD.chart (b, j))
    (AC.linear ⟨e, he⟩) (AD.linear (b, j))).choose_spec.2.2
      z ⟨hbase, hy⟩ v (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl w) i k
  have hpull := (AE.exists_pullbackChart q ⟨e, he⟩).choose_spec.2
    (⟨z, v⟩ : TotalSpace Unit ((q : Z → B) *ᵖ E))
  have hassoc := (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
    (S.trivialization b) (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.2.2
      p y z rfl w hp
  change (AC.chart ⟨e, he⟩ ⟨z, v⟩).2 = _ at hpull
  change (AD.chart (b, j)
    ⟨z, associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl w⟩).2 = _ at hassoc
  rw [hpull, hassoc] at h
  exact h

end AtiyahSinger
