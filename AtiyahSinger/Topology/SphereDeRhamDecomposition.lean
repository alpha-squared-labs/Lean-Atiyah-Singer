/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantDisjointKZero
public import AtiyahSinger.Topology.EquivariantOpenHomeomorph
public import AtiyahSinger.Topology.SphereDeRhamWindows
public import AtiyahSinger.Topology.SphereTangentKTheory

/-!
# The equivariant two-pole decomposition of the original sphere de Rham symbol

Public module ID: M2161.

The endpoint is first restricted to the actual disjoint hemisphere windows,
which contain its whole compact control. Reconstruction uses the original
clopen and open-extension maps. The prescribed unitary exterior frames then
identify its two full-chart classes with the original Bott representative
and its actual conjugation pullback. All objects and actions remain native.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Topology
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphereTangent
  isFiniteRank_pullback locallyCompactSpace_sigma

section CompactControl

variable {G X Y Z : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]
  [MulAction G Z] [ContinuousSMul G Z]

/-- Pullback of the specified representative with compact inverse-image control. -/
@[reducible] private def compactPullback (a : EquivariantSupportBundleTriple G X)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hK : IsCompact (f ⁻¹' a.1.datum.control)) : EquivariantSupportBundleTriple G Y :=
  EquivariantSupportBundleTriple.ofBoundary (a.1.source.pullback f) (a.1.target.pullback f)
    { control := f ⁻¹' a.1.datum.control
      isCompact_control := hK
      boundary := a.1.datum.boundary.pullback f }
    (a.2.sourceAction.pullback f heq) (a.2.targetAction.pullback f heq)
    (CompactSupportTriple.IsEquivariant.pullback_of_isCompact_preimage a.1.datum
      a.2.sourceAction a.2.targetAction a.2.isEquivariant f heq hK)

set_option backward.isDefEq.respectTransparency.types false in
/-- Both routes preserve the same fiber vectors, boundary maps, and compact preimage. -/
private theorem compactPullback_comp_class (a : EquivariantSupportBundleTriple G X)
    (f : C(Y, X)) (heq : ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hK : IsCompact (f ⁻¹' a.1.datum.control))
    (k : C(Z, Y)) (hkeq : ∀ (g : G) (z : Z), k (g • z) = g • k z)
    (hL : IsCompact (k ⁻¹' (f ⁻¹' a.1.datum.control))) :
    (compactPullback (compactPullback a f heq hK) k hkeq hL).kZeroClass =
      (compactPullback a (f.comp k)
        (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z))) hL).kZeroClass := by
  let d := compactPullback (compactPullback a f heq hK) k hkeq hL
  let c := compactPullback a (f.comp k)
    (fun g z ↦ (congrArg f (hkeq g z)).trans (heq g (k z))) hL
  apply equivariantSupportTripleKZero_generator_relations.1 d c
  let K := c.1.datum.control
  have hcompact : IsCompact K := c.1.datum.isCompact_control
  let u := pullbackCompIso (E := a.1.source.Fiber) f k
  let v := pullbackCompIso (E := a.1.target.Fiber) f k
  refine ⟨K, hcompact, c.2.isEquivariant.invariant_control, Set.Subset.rfl,
    Set.Subset.rfl, u, v,
    a.2.sourceAction.pullbackCompIso_isEquivariant f heq k hkeq,
    a.2.targetAction.pullbackCompIso_isEquivariant f heq k hkeq, ?_⟩
  intro x s
  have hl := d.1.datum.enlarge_apply K hcompact (Set.Subset.refl _) x s
  have hp := RelativeTriple.pullback_apply (a.1.datum.boundary.pullback f) k x s
  have hq := RelativeTriple.pullback_apply a.1.datum.boundary f ⟨k x, x.property⟩ s
  have hr := c.1.datum.enlarge_apply K hcompact (Set.Subset.refl _) x s
  have ht := RelativeTriple.pullback_apply a.1.datum.boundary (f.comp k) x s
  have hv := pullbackCompIso_apply (E := a.1.target.Fiber) f k x
    ((d.1.datum.enlarge K hcompact (Set.Subset.refl _)).boundary.linearEquiv x s)
  have hu := pullbackCompIso_apply (E := a.1.source.Fiber) f k x s
  exact hv.trans (((hl.trans (hp.trans hq)).trans (hr.trans ht).symm).trans
    (congrArg ((c.1.datum.enlarge K hcompact (Set.Subset.refl _)).boundary.linearEquiv x)
      hu).symm)

end CompactControl

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1500000 in
-- The original restricted representatives retain both orders of dependent base pullback.
private theorem sphereDeRhamEndpoint_eq_sum_chart (r : ℕ)
    [CompactSpace (Matrix.orthogonalGroup (Fin r) ℝ)]
    [LocallyCompactSpace (TangentBundle (𝓡 r) (OrthogonalSphere r))]
    [T2Space (TangentBundle (𝓡 r) (OrthogonalSphere r))] :
    (equivariantSphereDeRhamTriple r 1).kZeroClass =
      ∑ b : Bool, equivariantSupportTripleKZeroOpenPushforward
        (orthogonalSphereTangentChart r b) (orthogonalSphereTangentChart_isOpenEmbedding r b)
        (orthogonalSphereTangentChart_equivariant r b)
        (equivariantSphereDeRhamChartTriple r b).kZeroClass := by
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let V := EuclideanSpace ℂ (Fin r)
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  let W := orthogonalSphereDeRhamWindow r
  let S := SphereDeRhamWindows r
  let : DistribMulAction G V := orthogonalComplexificationDistribMulAction r
  let : MulAction G W := sphereDeRhamWindowMulAction r
  let : MulAction G S := sphereDeRhamWindowsMulAction r
  let : SMul G V := (orthogonalComplexificationDistribMulAction r).toSMul
  let : SMul G W := (sphereDeRhamWindowMulAction r).toSMul
  let : SMul G S := (sphereDeRhamWindowsMulAction r).toSMul
  let := compactSpace_orthogonalGroup r
  let := (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
  let := tangentBundleFullChartedSpace (E := EuclideanSpace ℝ (Fin r))
    (M := OrthogonalSphere r)
  let := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) T
  let : LocallyCompactSpace W := (isOpen_orthogonalSphereDeRhamWindow r).locallyCompactSpace
  let B := equivariantSphereDeRhamTriple r 1
  let chartTriple (b : Bool) := equivariantSphereDeRhamChartTriple r b
  let j := sphereDeRhamWindowsMap r
  have hj := sphereDeRhamWindowsMap_isOpenEmbedding r
  have hjeq := sphereDeRhamWindowsMap_equivariant r
  have hcontrol := sphereDeRhamTriple_control_subset_range_windows r
  let D := B.openRestrict j hj hjeq hcontrol
  let i (b : Bool) : C(W, S) :=
    { toFun := fun x ↦ (⟨b, x⟩ : S)
      continuous_toFun := by exact continuous_sigmaMk (σ := fun _ : Bool ↦ W) (i := b) }
  have hi (b : Bool) : IsOpenEmbedding (i b) :=
    IsOpenEmbedding.sigmaMk (σ := fun _ : Bool ↦ W) (i := b)
  have hieq (b : Bool) (g : G) (x : W) : i b (g • x) = g • i b x := rfl
  have hip (b : Bool) : IsProperMap (i b) :=
    (IsClosedEmbedding.sigmaMk (σ := fun _ : Bool ↦ W) (i := b)).isProperMap
  let k : C(W, V) := ⟨Subtype.val, continuous_subtype_val⟩
  have hk : IsOpenEmbedding k := (isOpen_orthogonalSphereDeRhamWindow r).isOpenEmbedding_subtypeVal
  have hkeq (g : G) (x : W) : k (g • x) = g • k x := rfl
  have hck (b : Bool) : (chartTriple b).1.datum.control ⊆ Set.range k := by
    intro z hz
    have hz0 := (sphereDeRhamVector_tangentChart_eq_zero_iff r b z).mp hz
    subst z
    refine ⟨⟨0, ?_⟩, rfl⟩
    change ‖(0 : EuclideanSpace ℝ (Fin r))‖ < 1
    simp
  have hpieces (b : Bool) :
      (D.pullback (i b) (hieq b) (hip b)).kZeroClass =
        ((chartTriple b).openRestrict k hk hkeq (hck b)).kZeroClass := by
    -- Both iterated restrictions are the same direct pullback through the actual chart window.
    have h₁ := compactPullback_comp_class B j hjeq D.1.datum.isCompact_control
      (i b) (hieq b) (D.pullback (i b) (hieq b) (hip b)).1.datum.isCompact_control
    have h₂ := compactPullback_comp_class B (orthogonalSphereTangentChart r b)
      (orthogonalSphereTangentChart_equivariant r b) (chartTriple b).1.datum.isCompact_control
      k hkeq ((chartTriple b).openRestrict k hk hkeq (hck b)).1.datum.isCompact_control
    exact h₁.trans h₂.symm
  have hdecomp := equivariantSupportTripleKZero_sigma_eq_sum_openPushforward
    (fun _ : Bool ↦ W) hieq D.kZeroClass
  have hrecover := equivariantSupportTripleKZeroOpenPushforward_class j hj hjeq B hcontrol
  rw [← hrecover, hdecomp, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [equivariantSupportTripleKZeroPullback_apply, hpieces]
  have hleft := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    (i b) (hi b) (hieq b) j hj hjeq
  have hright := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    k hk hkeq (orthogonalSphereTangentChart r b)
    (orthogonalSphereTangentChart_isOpenEmbedding r b)
    (orthogonalSphereTangentChart_equivariant r b)
  have hmaps : equivariantSupportTripleKZeroOpenPushforward (j.comp (i b))
      (hj.comp (hi b))
      (fun g x ↦ (congrArg j (hieq b g x)).trans (hjeq g (i b x))) =
      equivariantSupportTripleKZeroOpenPushforward ((orthogonalSphereTangentChart r b).comp k)
        ((orthogonalSphereTangentChart_isOpenEmbedding r b).comp hk)
        (fun g x ↦ (congrArg (orthogonalSphereTangentChart r b) (hkeq g x)).trans
          (orthogonalSphereTangentChart_equivariant r b g (k x))) := rfl
  have hcomp := DFunLike.congr_fun (hleft.symm.trans (hmaps.trans hright))
    ((chartTriple b).openRestrict k hk hkeq (hck b)).kZeroClass
  simp only [AddMonoidHom.comp_apply] at hcomp
  exact hcomp.trans (congrArg (equivariantSupportTripleKZeroOpenPushforward
    (orthogonalSphereTangentChart r b) (orthogonalSphereTangentChart_isOpenEmbedding r b)
    (orthogonalSphereTangentChart_equivariant r b))
    (equivariantSupportTripleKZeroOpenPushforward_class k hk hkeq (chartTriple b) (hck b)))

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Compare the original nested support representatives through the exact chart square.
/-- ASI Lemma (3.2): the original sphere exterior symbol splits into its two actual pole classes. -/
theorem orthogonalSphereDeRhamClass_eq_pole_sum (r : ℕ) :
    orthogonalSphereDeRhamClass r =
      orthogonalSpherePolePushforward r false 1 +
        orthogonalSphereTangentNegationPullback r
          (orthogonalSpherePolePushforward r true 1) := by
  /- The original uniform homotopy moves the control to the two actual poles.
  Restrict to their disjoint open hemisphere windows and reconstruct by the
  same support presentation. In each full chart the normalized unitary
  exterior frames give the Bott boundary up to a nonzero equivariant scalar.
  The upper chart has complex conjugation; its exact coordinate square
  transports that pullback to the native tangent-fiber reversal. -/
  let V := EuclideanSpace ℂ (Fin r)
  let T := TangentBundle (𝓡 r) (OrthogonalSphere r)
  let := compactSpace_orthogonalGroup r
  let := (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
  let := tangentBundleFullChartedSpace (E := EuclideanSpace ℝ (Fin r))
    (M := OrthogonalSphere r)
  let := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) T
  let a := equivariantExteriorBottClass (orthogonalComplexification_unitary r)
  have hpole (b : Bool) : orthogonalSpherePolePushforward r b 1 =
      equivariantSupportTripleKZeroOpenPushforward (orthogonalSphereTangentChart r b)
        (orthogonalSphereTangentChart_isOpenEmbedding r b)
        (orthogonalSphereTangentChart_equivariant r b) a := by
    change equivariantSupportTripleKZeroOpenPushforward _ _ _
      ((1 : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) • a) = _
    rw [one_smul]
  have hupper : equivariantSupportTripleKZeroOpenPushforward
      (orthogonalSphereTangentChart r true) (orthogonalSphereTangentChart_isOpenEmbedding r true)
      (orthogonalSphereTangentChart_equivariant r true)
      (orthogonalComplexificationConjugationPullback r a) =
        orthogonalSphereTangentNegationPullback r
          (orthogonalSpherePolePushforward r true 1) := by
    -- Use the original involutions and their exact square on these same chart representatives.
    let f := orthogonalSphereTangentChart r true
    have hf := orthogonalSphereTangentChart_isOpenEmbedding r true
    have he := orthogonalSphereTangentChart_equivariant r true
    let θ := orthogonalSphereTangentNegation r
    have hθ := (orthogonalSphereTangentNegation_properties r).2.2
    have hθinv : Function.Involutive θ := by
      intro z
      cases z
      simp only [θ, orthogonalSphereTangentNegation, ContinuousMap.coe_mk, neg_neg]
    let e : T ≃ₜ T :=
      { toEquiv := ⟨θ, θ, hθinv, hθinv⟩
        continuous_toFun := θ.continuous
        continuous_invFun := θ.continuous }
    let k : C(T, T) := ⟨e.symm, e.symm.continuous⟩
    let c := orthogonalComplexificationConjugation r
    have hc := orthogonalComplexificationConjugation_equivariant r
    have hcinv : Function.Involutive c := by
      intro z
      ext j
      exact star_star (z j)
    let d : V ≃ₜ V :=
      { toEquiv := ⟨c, c, hcinv, hcinv⟩
        continuous_toFun := c.continuous
        continuous_invFun := c.continuous }
    let l : C(V, V) := ⟨d.symm, d.symm.continuous⟩
    have hchart : k.comp f = f.comp l := by
      apply ContinuousMap.ext
      intro z
      exact (orthogonalSphereTangentChart_conjugation r true z).symm
    have hmaps : equivariantSupportTripleKZeroOpenPushforward (k.comp f)
        (e.symm.isOpenEmbedding.comp hf)
        (fun g x ↦ (congrArg k (he g x)).trans (hθ g (f x))) =
        equivariantSupportTripleKZeroOpenPushforward (f.comp l)
          (hf.comp d.symm.isOpenEmbedding)
          (fun g x ↦ (congrArg f (hc g x)).trans (he g (l x))) := by
      congr 1
    have hleft := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
      f hf he k e.symm.isOpenEmbedding hθ
    have hright := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
      l d.symm.isOpenEmbedding hc f hf he
    have hlvalue : equivariantSupportTripleKZeroOpenPushforward l d.symm.isOpenEmbedding hc a =
        orthogonalComplexificationConjugationPullback r a :=
      (DFunLike.congr_fun (equivariantSupportTripleKZeroPullback_eq_openPushforward_symm
        d hc hc) a).symm
    rw [hpole true]
    change _ = equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ hθ e.isProperMap
      (equivariantSupportTripleKZeroOpenPushforward f hf he a)
    rw [equivariantSupportTripleKZeroPullback_eq_openPushforward_symm e hθ hθ]
    have hcomp := DFunLike.congr_fun (hleft.symm.trans (hmaps.trans hright)) a
    simp only [AddMonoidHom.comp_apply] at hcomp
    rw [hlvalue] at hcomp
    exact hcomp.symm
  -- The actual uniformly controlled homotopy compares the original endpoint triples.
  obtain ⟨H, _⟩ := exists_sphereDeRhamHomotopy r
  have hhom := equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
    (sphereDeRhamParityBundle r 0) (sphereDeRhamParityBundle r 1)
    (sphereDeRhamParityAction r 0) (sphereDeRhamParityAction r 1)
    (sphereDeRhamTriple r 0) (sphereDeRhamTriple r 1)
    (sphereDeRhamTriple_isEquivariant r 0) (sphereDeRhamTriple_isEquivariant r 1) ⟨H⟩
  change (equivariantSphereDeRhamTriple r 0).kZeroClass = _
  apply hhom.trans
  change (equivariantSphereDeRhamTriple r 1).kZeroClass = _
  rw [sphereDeRhamEndpoint_eq_sum_chart]
  simp only [Fintype.sum_bool, equivariantSphereDeRhamChartTriple_class, Bool.false_eq_true,
    ↓reduceIte]
  rw [← hpole false, hupper]
  exact add_comm _ _

end AtiyahSinger
