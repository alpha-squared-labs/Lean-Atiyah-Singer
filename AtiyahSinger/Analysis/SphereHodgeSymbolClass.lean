/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolKClass
public import AtiyahSinger.Geometry.OrthogonalSmoothAction
public import AtiyahSinger.Geometry.SphereMusical
public import AtiyahSinger.Geometry.TangentDualMetric
public import AtiyahSinger.Topology.EquivariantPullbackTransport
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality
public import AtiyahSinger.Topology.SphereDeRhamClass

/-!
# The native Hodge symbol and the original sphere support class

Public module ID: M1010.

A specified equivariant bundle comparison and its exact off-zero symbol square
identify the original sphere exterior support class after the round musical
pullback with the native homogeneous symbol class. The proof uses the actual
zero section and the original two actions. It retains both bundles also in
dimension zero, where the exterior boundary is empty.

Source: SG II.5 and III.13. The explicit native-bundle comparison is a project
supplement; the geometric bundle maps and the Hodge symbol square are inputs
here and are constructed separately on the same fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent
  lieGroup_orthogonalGroup sphereComplexifiedTangentTopology
  isFiniteRank_sphereComplexifiedTangent exteriorTopology exteriorParityTopology
  isFiniteRank_exteriorParity isFiniteRank_pullback

set_option maxSynthPendingDepth 30

set_option maxHeartbeats 3600000 in
-- Retain both iterated native pullback types and the exact original boundary maps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified native sphere symbol square identifies the two original equivariant K classes. -/
theorem equivariantHomogeneousSymbolKClass_eq_sphereDeRham
    (n : ℕ) (E F : SmoothFiniteComplexBundle (n := n) (OrthogonalSphere n))
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      EquivariantStructure (Matrix.orthogonalGroup (Fin n) ℝ) E.Fiber)
    (τ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      EquivariantStructure (Matrix.orthogonalGroup (Fin n) ℝ) F.Fiber)
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      Iso (fun x : OrthogonalSphere n ↦ CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (SphereComplexifiedTangent n x)) 0) E.Fiber)
    (f : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      Iso (fun x : OrthogonalSphere n ↦ CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (SphereComplexifiedTangent n x)) 1) F.Fiber)
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      e.IsEquivariant (sphereExteriorParityEquivariantStructure n 0) σ)
    (hf : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      f.IsEquivariant (sphereExteriorParityEquivariantStructure n 1) τ)
    {m : ℝ} (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber m)
    (hi : IsEllipticGlobalSymbol E.Fiber F.Fiber a.val)
    (ha : ∀ (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : OrthogonalSphere n)
      (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, OrthogonalGroupModel n) σ τ A a.val x ξ = a.val x ξ)
    (hsquare : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ (x : OrthogonalSphere n) (v : TangentSpace (𝓡 n) x), v ≠ 0 →
        ∀ u : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent n x)) 0,
          f.linearEquiv x (sphereDeRhamSymbol n 0 ⟨x, v⟩ u) =
            a.val x ((orthogonalSphereRoundMetric n).inner x v) (e.linearEquiv x u)) :
    equivariantSupportTripleKZeroPullback
        ⟨(orthogonalSphereRoundMetric n).flatHomeomorph.symm,
          (orthogonalSphereRoundMetric n).flatHomeomorph.symm.continuous⟩
        (orthogonalSphereRoundMetric_flat_symm_equivariant n)
        (orthogonalSphereRoundMetric n).flatHomeomorph.symm.isProperMap
        (orthogonalSphereDeRhamClass n) =
      equivariantHomogeneousSymbolKClass 𝓘(ℝ, OrthogonalGroupModel n) σ τ m a hi ha := by
  classical
  let g := orthogonalSphereRoundMetric n
  let S := OrthogonalSphere n
  let T := TangentBundle (𝓡 n) S
  let C := CotangentTotalSpace (n := n) (M := S)
  let P (i : ZMod 2) (x : S) : Type :=
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (SphereComplexifiedTangent n x)) i
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let p := orthogonalSphereTangentProjection n
  let q := cotangentProjection (n := n) (M := S)
  -- Use the explicit inverse-musical formula so that the composite projection keeps its base.
  let θ : C(C, T) := ⟨fun z ↦ ⟨z.proj, g.sharp z.proj z.snd⟩,
    g.contMDiff_sharp.continuous⟩
  have hθ : θ = ⟨g.flatHomeomorph.symm, g.flatHomeomorph.symm.continuous⟩ := by
    apply ContinuousMap.ext
    intro z
    exact (g.flatHomeomorph_symm_apply z.proj z.snd).symm
  have hθg (A : Matrix.orthogonalGroup (Fin n) ℝ) (z : C) : θ (A • z) = A • θ z := by
    rw [hθ]
    exact orthogonalSphereRoundMetric_flat_symm_equivariant n A z
  have hproper : IsProperMap θ := by
    rw [hθ]
    exact g.flatHomeomorph.symm.isProperMap
  let d₀ := (pullbackCompIso (E := P 0) p θ).trans (e.pullback q)
  let d₁ := (pullbackCompIso (E := P 1) p θ).trans (f.pullback q)
  have hd₀ (z : C) (u : P 0 z.proj) : d₀.linearEquiv z u = e.linearEquiv z.proj u := by
    change e.linearEquiv z.proj ((pullbackCompIso (E := P 0) p θ).linearEquiv z u) = _
    rw [pullbackCompIso_apply]
  have hd₁ (z : C) (u : P 1 z.proj) : d₁.linearEquiv z u = f.linearEquiv z.proj u := by
    change f.linearEquiv z.proj ((pullbackCompIso (E := P 1) p θ).linearEquiv z u) = _
    rw [pullbackCompIso_apply]
  let A := (equivariantSphereDeRhamTriple n 0).pullback θ hθg hproper
  let B := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((q : C → S) *ᵖ E.Fiber))
    (FiniteBundle.ofFamily ((q : C → S) *ᵖ F.Fiber))
    (ellipticSymbolTriple a.val a.property.1.continuous hi)
    (σ.pullback q (fun _ _ ↦ rfl)) (τ.pullback q (fun _ _ ↦ rfl))
    (ellipticSymbolTriple_isEquivariant 𝓘(ℝ, OrthogonalGroupModel n)
      σ τ a.val a.property.1.continuous hi ha)
  have hcontrol : A.1.datum.control ⊆ cotangentZeroSet := by
    intro z hz
    have hv : g.sharp z.proj z.snd = 0 :=
      ((sphereDeRhamVector_properties n).1 0 (θ z)).mp hz |>.1
    change z.snd = 0
    rw [← (g.sharp_flat_inverse z.proj 0 z.snd).2, hv, map_zero]
  -- The two global maps intertwine exactly the iterated and native pulled actions.
  have heq₀ : d₀.IsEquivariant A.2.sourceAction B.2.sourceAction := by
    have hc := (sphereExteriorParityEquivariantStructure n 0).pullbackCompIso_isEquivariant
      p (fun _ _ ↦ rfl) θ hθg
    have hp := ((sphereExteriorParityEquivariantStructure n 0).pullback_maps σ q
      (fun _ _ ↦ rfl)).2 e he
    intro γ z u
    exact (congrArg (e.linearEquiv (γ • z).proj) (hc γ z u)).trans
      (hp γ z ((pullbackCompIso (E := P 0) p θ).linearEquiv z u))
  have heq₁ : d₁.IsEquivariant A.2.targetAction B.2.targetAction := by
    have hc := (sphereExteriorParityEquivariantStructure n 1).pullbackCompIso_isEquivariant
      p (fun _ _ ↦ rfl) θ hθg
    have hp := ((sphereExteriorParityEquivariantStructure n 1).pullback_maps τ q
      (fun _ _ ↦ rfl)).2 f hf
    intro γ z u
    exact (congrArg (f.linearEquiv (γ • z).proj) (hc γ z u)).trans
      (hp γ z ((pullbackCompIso (E := P 1) p θ).linearEquiv z u))
  clear_value d₀ d₁
  have hIso : A.IsIsomorphic B := by
    refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet,
      B.2.isEquivariant.invariant_control, hcontrol, subset_rfl, d₀, d₁, heq₀, heq₁, ?_⟩
    intro z u
    let zA : (θ ⁻¹' (sphereDeRhamTriple n 0).controlᶜ : Set C) :=
      ⟨z.val, fun h ↦ z.property (hcontrol h)⟩
    have hleft : (A.1.datum.enlarge cotangentZeroSet isCompact_cotangentZeroSet
        hcontrol).boundary.linearEquiv z u =
        sphereDeRhamSymbol n 0 ⟨z.val.proj, g.sharp z.val.proj z.val.snd⟩ u :=
      (A.1.datum.enlarge_apply cotangentZeroSet isCompact_cotangentZeroSet hcontrol z u).trans
        (RelativeTriple.pullback_apply (sphereDeRhamTriple n 0).boundary θ zA u)
    have hright (v : E.Fiber z.val.proj) :
        (B.1.datum.enlarge cotangentZeroSet isCompact_cotangentZeroSet
          subset_rfl).boundary.linearEquiv z v = a.val z.val.proj z.val.snd v :=
      (B.1.datum.enlarge_apply cotangentZeroSet isCompact_cotangentZeroSet subset_rfl z v).trans
        (ellipticSymbolTriple_boundary_apply a.val a.property.1.continuous hi z v)
    have hv : g.sharp z.val.proj z.val.snd ≠ 0 := by
      intro h
      apply z.property
      change z.val.snd = 0
      rw [← (g.sharp_flat_inverse z.val.proj 0 z.val.snd).2, h, map_zero]
    have hs := hsquare z.val.proj (g.sharp z.val.proj z.val.snd) hv u
    rw [(g.sharp_flat_inverse z.val.proj 0 z.val.snd).2] at hs
    exact (hd₁ z.val _).trans ((congrArg (f.linearEquiv z.val.proj) hleft).trans
      (hs.trans ((hright _).symm.trans (congrArg
        ((B.1.datum.enlarge cotangentZeroSet isCompact_cotangentZeroSet
          subset_rfl).boundary.linearEquiv z) (hd₀ z.val u).symm))))
  have hclass := equivariantSupportTripleKZero_generator_relations.1 A B hIso
  change equivariantSupportTripleKZeroPullback _ _ _
    (equivariantSphereDeRhamTriple n 0).kZeroClass = B.kZeroClass
  have hmaps : equivariantSupportTripleKZeroPullback θ hθg hproper =
      equivariantSupportTripleKZeroPullback
        ⟨g.flatHomeomorph.symm, g.flatHomeomorph.symm.continuous⟩
        (orthogonalSphereRoundMetric_flat_symm_equivariant n)
        g.flatHomeomorph.symm.isProperMap := by
    congr 1
  rw [← hmaps, equivariantSupportTripleKZeroPullback_apply]
  exact hclass

end AtiyahSinger
