/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedHermitianTwistedProduct
public import AtiyahSinger.Topology.AssociatedSphereTwistedProduct

/-!
# The Hermitian product class on the associated-sphere cotangent space

The selected Hermitian twisted triple uses the original paired map, four
factor maps and ordered tensor bundles. Pulling its K class back by the
inverse cotangent realization gives associatedSphereTwistedProduct for the
specified horizontal lift.

The proof applies the selected triple's class formula, then the established
independence of the lift. The full boundary formula in supplied target bundles
is provided by AssociatedSphereHermitianSumTransport.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct Manifold ContDiff Matrix.Norms.Elementwise

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant tensorTopology isFiniteRank_tensor
  sumTopology isFiniteRank_sum isFiniteRank_pullback
  continuousSMul_orthogonalSphere continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent

variable {n r : ℕ} {P B : Type*}
  [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [CompactSpace B] [T2Space B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Er" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => CotangentTotalSpace (n := n) (M := B)
local notation "Y" => CotangentTotalSpace (n := r) (M := OrthogonalSphere r)
local notation "f" => cotangentProjection (n := n) (M := B)
local notation "W" => AssociatedBundle G (PrincipalBundlePullback f projection) Y
local notation "CotFiber" => fun z : Z ↦ TangentSpace 𝓘(ℝ, En × Er) z →L[ℝ] ℝ
local notation "NativeCot" => TotalSpace ((En × Er) →L[ℝ] ℝ) CotFiber

variable {E₀ E₁ : CotangentTotalSpace (n := n) (M := B) → Type*}
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace Unit E₀)] [IsFiniteRank E₀]
  [TopologicalSpace (TotalSpace Unit E₁)] [IsFiniteRank E₁]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4800000 in
-- The original cotangent realization and both nested tensor pullbacks stay explicit.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original Hermitian factor maps realize the prescribed associated-sphere product class. -/
theorem associatedSphereTwistedProduct_eq_hermitian
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (a : CompactSupportTriple E₀ E₁)
    (b : EquivariantSupportBundleTriple G Y)
    (h₀ : ∀ x, InnerProductSpace.Core ℂ (E₀ x))
    (h₁ : ∀ x, InnerProductSpace.Core ℂ (E₁ x))
    (k₀ : ContinuousHermitianMetric b.1.source.Fiber)
    (k₁ : ContinuousHermitianMetric b.1.target.Fiber)
    (hk₀ : ∀ (g : G) (y : Y) (u v : b.1.source.Fiber y),
      (k₀.toCore (g • y)).inner (b.2.sourceAction.linearMap g y u)
        (b.2.sourceAction.linearMap g y v) = (k₀.toCore y).inner u v)
    (hk₁ : ∀ (g : G) (y : Y) (u v : b.1.target.Fiber y),
      (k₁.toCore (g • y)).inner (b.2.targetAction.linearMap g y u)
        (b.2.targetAction.linearMap g y v) = (k₁.toCore y).inner u v)
    (p : Hom E₀ E₁) (pi : Hom E₁ E₀)
    (q : Hom b.1.source.Fiber b.1.target.Fiber)
    (qi : Hom b.1.target.Fiber b.1.source.Fiber)
    (hp : ∀ x u v, (h₁ x).inner (p.linearMap x u) v =
      (h₀ x).inner u (pi.linearMap x v))
    (hq : ∀ y u v, (k₁.toCore y).inner (q.linearMap y u) v =
      (k₀.toCore y).inner u (qi.linearMap y v))
    (hqg : q.IsEquivariant b.2.sourceAction b.2.targetAction)
    (hqig : qi.IsEquivariant b.2.targetAction b.2.sourceAction)
    (ha : ∀ x : (a.controlᶜ : Set X),
      (a.boundary.linearEquiv x).toLinearMap = p.linearMap x.val)
    (hb : ∀ y : (b.1.datum.controlᶜ : Set Y),
      (b.1.datum.boundary.linearEquiv y).toLinearMap = q.linearMap y.val) :
    letI := S.toIsPrincipalBundle
    letI := associatedSphereChartedSpace S
    letI := associatedSphereIsManifold S
    letI := associatedBundle_t2Space («Y» := Y)
      (isPrincipalBundle_pullback («G» := G) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace («Y» := Y)
      (isPrincipalBundle_pullback («G» := G) (projection := projection) f)
    letI := associatedBundle_t2Space («Y» := Y) S.toIsPrincipalBundle
    letI := associatedBundle_locallyCompactSpace («Y» := Y) S.toIsPrincipalBundle
    let e := associatedSphereCotangentHomeomorph S H
    letI := e.t2Space
    letI := e.symm.isOpenEmbedding.locallyCompactSpace
    let D₀ := AssociatedEquivariantFiber S.toIsPrincipalBundle b.2.sourceAction
    let D₁ := AssociatedEquivariantFiber S.toIsPrincipalBundle b.2.targetAction
    let A₀ := (ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ E₀
    let A₁ := (ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ E₁
    let B₀ := (ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ D₀
    let B₁ := (ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ D₁
    letI : TopologicalSpace (TotalSpace Unit (fun z ↦ A₀ z ⊗[ℂ] B₀ z)) :=
      tensorTopology (E := A₀) (F := B₀)
    letI : TopologicalSpace (TotalSpace Unit (fun z ↦ A₁ z ⊗[ℂ] B₁ z)) :=
      tensorTopology (E := A₁) (F := B₁)
    letI : TopologicalSpace (TotalSpace Unit (fun z ↦ A₁ z ⊗[ℂ] B₀ z)) :=
      tensorTopology (E := A₁) (F := B₀)
    letI : TopologicalSpace (TotalSpace Unit (fun z ↦ A₀ z ⊗[ℂ] B₁ z)) :=
      tensorTopology (E := A₀) (F := B₁)
    let Source := fun z ↦ (A₀ z ⊗[ℂ] B₀ z) × (A₁ z ⊗[ℂ] B₁ z)
    let Target := fun z ↦ (A₁ z ⊗[ℂ] B₀ z) × (A₀ z ⊗[ℂ] B₁ z)
    letI : TopologicalSpace (TotalSpace Unit Source) :=
      sumTopology (E := fun z ↦ A₀ z ⊗[ℂ] B₀ z) (F := fun z ↦ A₁ z ⊗[ℂ] B₁ z)
    letI : TopologicalSpace (TotalSpace Unit Target) :=
      sumTopology (E := fun z ↦ A₁ z ⊗[ℂ] B₀ z) (F := fun z ↦ A₀ z ⊗[ℂ] B₁ z)
    letI : IsFiniteRank Source := isFiniteRank_sum
    letI : IsFiniteRank Target := isFiniteRank_sum
    let j := associatedBundlePullbackProdMap
      («G» := G) («Y» := Y) (projection := projection) f
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ Source)) :=
      pullbackTopology Unit Source j
    letI : TopologicalSpace (TotalSpace Unit (j *ᵖ Target)) :=
      pullbackTopology Unit Target j
    let d₀ := (exists_associatedHermitianTwistedProduct (projection := projection)
      f a b h₀ h₁ k₀ k₁ hk₀ hk₁ p pi q qi hp hq hqg hqig ha hb).choose
    let inverse : C(NativeCot, W) := ⟨e.symm, e.symm.continuous⟩
    compactSupportKZeroPullback inverse e.symm.isProperMap d₀.compactSupportClass =
      associatedSphereTwistedProduct S a.compactSupportClass b.kZeroClass := by
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := associatedBundle_t2Space («Y» := Y)
    (isPrincipalBundle_pullback («G» := G) (projection := projection) f)
  let := associatedBundle_locallyCompactSpace («Y» := Y)
    (isPrincipalBundle_pullback («G» := G) (projection := projection) f)
  let := associatedBundle_t2Space («Y» := Y) S.toIsPrincipalBundle
  let := associatedBundle_locallyCompactSpace («Y» := Y) S.toIsPrincipalBundle
  intro e D₀ D₁ A₀ A₁ B₀ B₁ Source Target j d₀ inverse
  let := e.t2Space
  let := e.symm.isOpenEmbedding.locallyCompactSpace
  -- Read the class formula for this exact selected Hermitian twisted triple.
  have hclass := (exists_associatedHermitianTwistedProduct (projection := projection)
    f a b h₀ h₁ k₀ k₁ hk₀ hk₁ p pi q qi hp hq hqg hqig ha hb).choose_spec.2.2
  -- Apply the same inverse compact-support pullback to both sides of that class equality.
  refine (congrArg (compactSupportKZeroPullback inverse e.symm.isProperMap) hclass).trans ?_
  -- The supplied lift gives exactly the original inverse transport of the associated product.
  exact (congrArg (fun product ↦ product a.compactSupportClass b.kZeroClass)
    (associatedSphereTwistedProduct_eq_of_horizontalLift S H)).symm

end AtiyahSinger
