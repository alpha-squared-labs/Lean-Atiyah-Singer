/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedHermitianTwistedProduct
public import AtiyahSinger.Topology.AssociatedSphereTwistedProduct

/-!
# Original Hermitian products in specified bundles

Public module ID: M1545.

The original equivariant support packet and factor maps are retained. Its
associated product is pulled by the actual inverse cotangent realization and
conjugated by the two supplied bundle isomorphisms. Both its original class
and its complete reciprocal boundary are retained together.

For native sums the caller supplies the literal original ofBoundary packet
and the composites of its selected tensor comparisons with its selected sum
isomorphisms. The construction uses the supplied native bundles and bundle isomorphisms.
-/

@[expose] public noncomputable section

set_option Elab.async false

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct Manifold ContDiff Matrix.Norms.Elementwise

/- The private lemma combines proper pullback and bundle congruence, preserving
  the class and transporting the boundary formula into the supplied bundles. -/
attribute [local instance] isFiniteRank_pullback

private theorem transport_exists_boundary {U V : Type*}
    [TopologicalSpace U] [LocallyCompactSpace U] [T2Space U]
    [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V]
    {EF FF : U → Type*} [∀ x, AddCommGroup (EF x)] [∀ x, Module ℂ (EF x)]
    [TopologicalSpace (TotalSpace Unit EF)] [IsFiniteRank EF]
    [∀ x, AddCommGroup (FF x)] [∀ x, Module ℂ (FF x)]
    [TopologicalSpace (TotalSpace Unit FF)] [IsFiniteRank FF]
    {formula : ∀ x, EF x →ₗ[ℂ] FF x} {c : CompactSupportKZero U}
    {pred : CompactSupportTriple EF FF → Prop}
    (h : ∃ d : CompactSupportTriple EF FF, pred d ∧
      (∀ z : (d.controlᶜ : Set U),
        (d.boundary.linearEquiv z).toLinearMap = formula z.val) ∧
      d.compactSupportClass = c)
    (pull : C(V, U)) (hf : IsProperMap pull)
    (NS NT : V → Type*) [∀ z, AddCommGroup (NS z)] [∀ z, Module ℂ (NS z)]
    [TopologicalSpace (TotalSpace Unit NS)] [IsFiniteRank NS]
    [∀ z, AddCommGroup (NT z)] [∀ z, Module ℂ (NT z)]
    [TopologicalSpace (TotalSpace Unit NT)] [IsFiniteRank NT]
    (s : Iso (pull *ᵖ EF) NS) (t : Iso (pull *ᵖ FF) NT) :
    ∃ d : CompactSupportTriple NS NT,
      d.compactSupportClass = compactSupportKZeroPullback pull hf c ∧
      ∀ (z : (d.controlᶜ : Set V)) (w : EF (pull z.val)),
        d.boundary.linearEquiv z (s.linearEquiv z.val w) =
          t.linearEquiv z.val (formula (pull z.val) w) := by
  obtain ⟨a, _, ha, hc⟩ := h
  let pulled := a.pullback pull hf
  let d := pulled.congr s t
  refine ⟨d, ?_, ?_⟩
  · -- Proper pullback and the supplied bundle coordinates give the same K class.
    exact (pulled.compactSupportClass_congr s t).trans
      ((a.compactSupportClass_pullback pull hf).trans
        (congrArg (compactSupportKZeroPullback pull hf) hc))
  · -- Evaluate the original boundary at the same exterior point and cancel only s inverse.
    intro z w
    have hcongr := pulled.congr_apply s t z (s.linearEquiv z.val w)
    have hs : s.symm.linearEquiv z.val (s.linearEquiv z.val w) = w :=
      (s.linearEquiv z.val).symm_apply_apply w
    have hsource := congrArg (pulled.boundary.linearEquiv z) hs
    have hpull := RelativeTriple.pullback_apply a.boundary pull z w
    have hmatrix := LinearMap.congr_fun (ha ⟨pull z.val, z.property⟩) w
    exact hcongr.trans (congrArg (t.linearEquiv z.val)
      (hsource.trans (hpull.trans hmatrix)))

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
set_option maxHeartbeats 16000000 in
-- The original nested associated pullbacks and their fixed metric witnesses are retained.
set_option synthInstance.maxHeartbeats 200000 in
-- The original cotangent realization and both nested tensor pullbacks stay explicit.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original associated Hermitian product retains its full boundary in specified bundles. -/
theorem exists_associatedSphereHermitianSumTransport
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
    let inverse : C(NativeCot, W) := ⟨e.symm, e.symm.continuous⟩
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ Source))) :=
      pullbackTopology Unit (j *ᵖ Source) inverse
    letI : TopologicalSpace (TotalSpace Unit (inverse *ᵖ (j *ᵖ Target))) :=
      pullbackTopology Unit (j *ᵖ Target) inverse
    ∀ (NS NT : NativeCot → Type*)
      [∀ z, AddCommGroup (NS z)] [∀ z, Module ℂ (NS z)]
      [TopologicalSpace (TotalSpace Unit NS)] [IsFiniteRank NS]
      [∀ z, AddCommGroup (NT z)] [∀ z, Module ℂ (NT z)]
      [TopologicalSpace (TotalSpace Unit NT)] [IsFiniteRank NT]
      (s : Iso (inverse *ᵖ (j *ᵖ Source)) NS)
      (t : Iso (inverse *ᵖ (j *ᵖ Target)) NT),
      ∃ d : CompactSupportTriple NS NT,
        d.compactSupportClass =
          associatedSphereTwistedProduct S a.compactSupportClass b.kZeroClass ∧
        ∀ (z : (d.controlᶜ : Set NativeCot)) (u : Source (j (inverse z.val))),
          d.boundary.linearEquiv z (s.linearEquiv z.val u) =
            t.linearEquiv z.val
              (reciprocalTensorSymbol (p.linearMap (j (inverse z.val)).1)
                (pi.linearMap (j (inverse z.val)).1)
                ((associatedEquivariantHom S.toIsPrincipalBundle b.2.sourceAction
                  b.2.targetAction q hqg).linearMap (j (inverse z.val)).2)
                ((associatedEquivariantHom S.toIsPrincipalBundle b.2.targetAction
                  b.2.sourceAction qi hqig).linearMap (j (inverse z.val)).2) u) := by
  let := S.toIsPrincipalBundle
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  let := associatedBundle_t2Space («Y» := Y)
    (isPrincipalBundle_pullback («G» := G) (projection := projection) f)
  let := associatedBundle_locallyCompactSpace («Y» := Y)
    (isPrincipalBundle_pullback («G» := G) (projection := projection) f)
  let := associatedBundle_t2Space («Y» := Y) S.toIsPrincipalBundle
  let := associatedBundle_locallyCompactSpace («Y» := Y) S.toIsPrincipalBundle
  -- Select the original product before introducing the supplied transport coordinates.
  have originalProduct := exists_associatedHermitianTwistedProduct (projection := projection)
    f a b h₀ h₁ k₀ k₁ hk₀ hk₁ p pi q qi hp hq hqg hqig ha hb
  -- Expose the original certificate's own local maps before passing its existential type.
  dsimp (config := { zeta := true, zetaHave := true }) only at originalProduct
  intro e D₀ D₁ A₀ A₁ B₀ B₁ Source Target j inverse
  let := e.t2Space
  let := e.symm.isOpenEmbedding.locallyCompactSpace
  let := tensorTopology (E := A₀) (F := B₀)
  let := tensorTopology (E := A₁) (F := B₁)
  let := tensorTopology (E := A₁) (F := B₀)
  let := tensorTopology (E := A₀) (F := B₁)
  let := sumTopology (E := fun z ↦ A₀ z ⊗[ℂ] B₀ z) (F := fun z ↦ A₁ z ⊗[ℂ] B₁ z)
  let := sumTopology (E := fun z ↦ A₁ z ⊗[ℂ] B₀ z) (F := fun z ↦ A₀ z ⊗[ℂ] B₁ z)
  let : IsFiniteRank Source := isFiniteRank_sum
  let : IsFiniteRank Target := isFiniteRank_sum
  let := pullbackTopology Unit Source j
  let := pullbackTopology Unit Target j
  let := pullbackTopology Unit (j *ᵖ Source) inverse
  let := pullbackTopology Unit (j *ᵖ Target) inverse
  intro NS NT _ _ _ _ _ _ _ _ s t
  have htransport := transport_exists_boundary
    (EF := j *ᵖ Source) (FF := j *ᵖ Target)
    (formula := fun x ↦ reciprocalTensorSymbol
      (p.linearMap (j x).1) (pi.linearMap (j x).1)
      ((associatedEquivariantHom S.toIsPrincipalBundle b.2.sourceAction
        b.2.targetAction q hqg).linearMap (j x).2)
      ((associatedEquivariantHom S.toIsPrincipalBundle b.2.targetAction
        b.2.sourceAction qi hqig).linearMap (j x).2))
    (c := associatedSupportTwistedProduct («G» := G) (projection := projection) f
      a.compactSupportClass b.kZeroClass)
    (pred := fun d ↦ d.control = j ⁻¹'
      (a.control ×ˢ associatedControl G P Y b.1.datum.control))
    originalProduct inverse e.symm.isProperMap NS NT s t
  let d := htransport.choose
  have hdClass := htransport.choose_spec.1
  have hdBoundary := htransport.choose_spec.2
  refine ⟨d, ?_, hdBoundary⟩
  exact hdClass.trans
    (congrArg (fun product ↦ product a.compactSupportClass b.kZeroClass)
      (associatedSphereTwistedProduct_eq_of_horizontalLift S H)).symm

end AtiyahSinger
