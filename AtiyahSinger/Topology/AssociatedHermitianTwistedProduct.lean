/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedInvariantMetric
public import AtiyahSinger.Topology.AssociatedTwistedProduct
public import AtiyahSinger.Topology.HermitianSupportProductRealization

/-!
# The full Hermitian representative of the associated twisted product

Public module ID: M1539.

Descend the original equivariant full maps and their prescribed adjoints over
the original compact principal base. Their positive graded product with the
base full maps is pulled back along the original proper paired map. The
result retains the actual associated fibers, tensor order, and compact
control, and its class is the prescribed associated twisted product.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant tensorTopology isFiniteRank_tensor
  sumTopology isFiniteRank_sum isFiniteRank_pullback

variable {G P B X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [TopologicalSpace X]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [hP : IsPrincipalBundle G projection]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [CompactSpace B] [T2Space B]
  [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
  {E₀ E₁ : X → Type*}
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [TopologicalSpace (TotalSpace Unit E₀)] [IsFiniteRank E₀]
  [TopologicalSpace (TotalSpace Unit E₁)] [IsFiniteRank E₁]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- The original quotient bundles and exact paired pullback retain their induced topologies.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual associated full graded boundary represents the original twisted product. -/
theorem exists_associatedHermitianTwistedProduct
    (f : C(X, B)) (a : CompactSupportTriple E₀ E₁)
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
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    letI := associatedBundle_locallyCompactSpace (Y := Y)
      (isPrincipalBundle_pullback (G := G) (projection := projection) f)
    let j := associatedBundlePullbackProdMap (G := G) (Y := Y) (projection := projection) f
    let D₀ := AssociatedEquivariantFiber hP b.2.sourceAction
    let D₁ := AssociatedEquivariantFiber hP b.2.targetAction
    let Q := associatedEquivariantHom hP b.2.sourceAction b.2.targetAction q hqg
    let Qi := associatedEquivariantHom hP b.2.targetAction b.2.sourceAction qi hqig
    let Source := fun z : X × AssociatedBundle G P Y ↦
      (((ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ E₀) z ⊗[ℂ]
        ((ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ D₀) z) ×
      (((ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ E₁) z ⊗[ℂ]
        ((ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ D₁) z)
    let Target := fun z : X × AssociatedBundle G P Y ↦
      (((ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ E₁) z ⊗[ℂ]
        ((ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ D₀) z) ×
      (((ContinuousMap.fst : C(X × AssociatedBundle G P Y, X)) *ᵖ E₀) z ⊗[ℂ]
        ((ContinuousMap.snd : C(X × AssociatedBundle G P Y, AssociatedBundle G P Y)) *ᵖ D₁) z)
    ∃ d : CompactSupportTriple (j *ᵖ Source) (j *ᵖ Target),
      d.control = j ⁻¹' (a.control ×ˢ associatedControl G P Y b.1.datum.control) ∧
      (∀ z : (d.controlᶜ : Set (AssociatedBundle G (PrincipalBundlePullback f projection) Y)),
        (d.boundary.linearEquiv z).toLinearMap =
          reciprocalTensorSymbol (p.linearMap (j z.val).1) (pi.linearMap (j z.val).1)
            (Q.linearMap (j z.val).2) (Qi.linearMap (j z.val).2)) ∧
      d.compactSupportClass =
        associatedSupportTwistedProduct (G := G) (projection := projection) f
          a.compactSupportClass b.kZeroClass := by
  classical
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let := associatedBundle_t2Space (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
  let := associatedBundle_locallyCompactSpace (Y := Y)
    (isPrincipalBundle_pullback (G := G) (projection := projection) f)
  intro j D₀ D₁ Q Qi Source Target
  let c := associatedSupportTriple hP b.1.datum b.2.sourceAction b.2.targetAction
    b.2.isEquivariant
  let K₀ := associatedEquivariantMetricCore hP b.2.sourceAction k₀
  let K₁ := associatedEquivariantMetricCore hP b.2.targetAction k₁
  -- Descending both maps and both invariant metrics preserves the actual adjoint equation.
  have hQ (z : AssociatedBundle G P Y) (u : D₀ z) (v : D₁ z) :
      (K₁ z).inner (Q.linearMap z u) v = (K₀ z).inner u (Qi.linearMap z v) := by
    let p₀ := (Quotient.out z).1
    let y := (Quotient.out z).2
    have hz : associatedBundleMk G P Y p₀ y = z := Quotient.out_eq z
    obtain ⟨u, rfl⟩ := (associatedEquivariantFiberMk_bijective hP b.2.sourceAction p₀ y hz).2 u
    obtain ⟨v, rfl⟩ := (associatedEquivariantFiberMk_bijective hP b.2.targetAction p₀ y hz).2 v
    change (K₁ z).inner
      ((associatedEquivariantHom hP b.2.sourceAction b.2.targetAction q hqg).linearMap z _)
      _ = (K₀ z).inner _
        ((associatedEquivariantHom hP b.2.targetAction b.2.sourceAction qi hqig).linearMap z _)
    rw [associatedEquivariantHom_apply, associatedEquivariantHom_apply]
    change (associatedEquivariantMetricCore hP b.2.targetAction k₁ z).inner _ _ =
      (associatedEquivariantMetricCore hP b.2.sourceAction k₀ z).inner _ _
    rw [associatedEquivariantMetricCore_inner hP b.2.targetAction k₁ hk₁,
      associatedEquivariantMetricCore_inner hP b.2.sourceAction k₀ hk₀]
    exact hq y u v
  have hc : ∀ z : (c.controlᶜ : Set (AssociatedBundle G P Y)),
      (c.boundary.linearEquiv z).toLinearMap = Q.linearMap z.val := by
    rintro ⟨z, hz⟩
    induction z using Quotient.inductionOn with
    | h z =>
      let y : (b.1.datum.controlᶜ : Set Y) := ⟨z.2, fun hy ↦ hz
        ((associatedControl_mk_mem_iff b.1.datum.control
          b.2.isEquivariant.invariant_control z.1 z.2).mpr hy)⟩
      apply LinearMap.ext
      intro v
      obtain ⟨v, rfl⟩ :=
        (associatedEquivariantFiberMk_bijective hP b.2.sourceAction z.1 z.2 rfl).2 v
      exact (associatedSupportBoundary_apply hP b.1.datum b.2.sourceAction
        b.2.targetAction b.2.isEquivariant z.1 y v).trans
          ((congrArg (associatedEquivariantFiberMk hP b.2.targetAction z.1 z.2 rfl)
            (LinearMap.congr_fun (hb y) v)).trans
              (associatedEquivariantHom_apply hP b.2.sourceAction b.2.targetAction
                q hqg z.1 z.2 rfl v).symm)
  obtain ⟨d₀, hd₀, hformula, hclass⟩ := exists_hermitianSupportProduct a c
    h₀ h₁ K₀ K₁ p pi Q Qi hp hQ ha hc
  have hj : IsProperMap j := (associatedBundlePullbackProdMap_isClosedEmbedding f).isProperMap
  let d : CompactSupportTriple (j *ᵖ Source) (j *ᵖ Target) := d₀.pullback j hj
  refine ⟨d, ?_, ?_, ?_⟩
  · change j ⁻¹' d₀.control = _
    rw [hd₀]
    rfl
  · intro z
    apply LinearMap.ext
    intro v
    exact (RelativeTriple.pullback_apply d₀.boundary j z v).trans
      (LinearMap.congr_fun (hformula ⟨j z.val, z.property⟩) v)
  · -- The proper paired map supplies compact-support pullback; no projection properness is assumed.
    rw [d₀.compactSupportClass_pullback j hj, hclass]
    change compactSupportKZeroPullback j hj
        (compactSupportKZeroExternalProduct a.compactSupportClass c.compactSupportClass) =
      compactSupportKZeroPullback j hj
        (compactSupportKZeroExternalProduct a.compactSupportClass
          (associatedSupportKZero hP b.kZeroClass))
    rw [associatedSupportKZero_class]
    rfl

end AtiyahSinger
