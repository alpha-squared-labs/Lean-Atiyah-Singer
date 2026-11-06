/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Geometry.EquivariantCotangentRadial
public import AtiyahSinger.Geometry.InvariantCotangentMetric
public import AtiyahSinger.Topology.EquivariantBundleHomotopy
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero

import AtiyahSinger.Topology.RealBundleSupport
import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Equivariant homogeneous representatives on the original cotangent space

Public module ID: M1776.

Every original equivariant support K class over the cotangent space of a
compact smooth manifold has a continuous degree-zero representative whose
bundles are actual projection pullbacks. The base bundles retain locally
finite, possibly varying ranks, and the boundary is defined off exactly the
zero section. The same pulled actions certify its class in the original
equivariant support group, not merely its image after forgetting the action.

This is the compact-base equivariant extension of SG III.13 Lemma 13.3,
pp.245--246. The book states the ordinary result for a more general real
bundle and a finite-topological-type base. The original equivariant triple
framework is ASI I Section 2. Equivariant homotopy invariance and invariant
metric averaging supply the additional constructions here. The full
equivariant radial statement is an explicit project supplement; the ordinary
lemma alone does not establish it.

The fiber contraction is used only to compare actual bundles. It need not
be proper, and no compact-support K pullback along it is used. Compactness
of the base makes the zero section and one uniform invariant disk compact.
No smoothness of the resulting complex bundles or boundary is asserted.
The proof retains the actual zero-section bundle comparisons and the invariant
radial boundary homotopy on those same pullbacks.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [hDim : FiniteDimensional ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [hG : IsManifold IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

include hDim hG hGC hGT hM hT hSC hC hAction

set_option maxHeartbeats 1000000 in
-- Retain the actual nested pullbacks throughout contraction and class transport.
/-- Every original equivariant cotangent K class has a degree-zero pullback representative. -/
theorem exists_equivariant_homogeneous_cotangent_representative :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ z : EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)),
      ∃ E F : FiniteBundle M,
        ∃ (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber),
          ∃ a : CompactSupportTriple
            ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
            ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
            ∃ ha : a.IsEquivariant
              (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
              (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)),
              a.control = cotangentZeroSet ∧
              (∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
                ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ)
                  (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ),
                  a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
                    a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩) ∧
              (EquivariantSupportBundleTriple.ofBoundary
                (E.pullback cotangentProjection) (F.pullback cotangentProjection) a
                (ρE.pullback cotangentProjection (fun _ _ ↦ rfl))
                (ρF.pullback cotangentProjection (fun _ _ ↦ rfl)) ha).kZeroClass = z :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro z
  let Z := CotangentTotalSpace (n := n) (M := M)
  let C := CotangentModel n
  let W := CotangentFiber (n := n) (M := M)
  let πV := cotangentProjection (n := n) (M := M)
  let z₀ : C(M, Z) := ⟨cotangentZeroSection, continuous_cotangentZeroSection⟩
  let : RealBundle.IsFiniteRank C W := RealBundle.isFiniteRank_of_vectorBundle C W
  let : SecondCountableTopology Z := RealBundle.secondCountableTopology_totalSpace C W
  let : ParacompactSpace Z := inferInstance
  have hz₀ (g : G) (x : M) : z₀ (g • x) = g • z₀ x := by
    rfl
  have hπ (g : G) (v : Z) : πV (g • v) = g • πV v := rfl
  have hcomp (g : G) (v : Z) : (z₀.comp πV) (g • v) = g • (z₀.comp πV) v :=
    (congrArg z₀ (hπ g v)).trans (hz₀ g (πV v))
  -- Only actual bundle pullbacks use the equivariant fiber contraction.
  -- This map is not asserted proper and does not induce a compact-support K pullback.
  let H : ContinuousMap.Homotopy (z₀.comp πV) (ContinuousMap.id Z) := {
    toFun p := ⟨p.2.proj, (p.1 : ℝ) • p.2.snd⟩
    continuous_toFun := (RealBundle.continuous_scaling C W).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    map_zero_left v := by change (⟨v.proj, (0 : ℝ) • v.snd⟩ : Z) = ⟨v.proj, 0⟩; simp
    map_one_left v := by change (⟨v.proj, (1 : ℝ) • v.snd⟩ : Z) = v; simp }
  have hH (t : unitInterval) (g : G) (v : Z) : H (t, g • v) = g • H (t, v) := by
    rfl
  have hcompare (P : FiniteBundle Z) (ρ : EquivariantStructure G P.Fiber) :
      ∃ e : Iso P.Fiber ((πV : Z → M) *ᵖ ((z₀ : M → Z) *ᵖ P.Fiber)),
        e.IsEquivariant ρ ((ρ.pullback z₀ hz₀).pullback πV hπ) := by
    obtain ⟨i, hi⟩ := ρ.exists_pullback_iso_of_homotopy (z₀.comp πV)
      (ContinuousMap.id Z) hcomp (fun _ _ ↦ rfl) H hH
    let c := pullbackCompIso (E := P.Fiber) z₀ πV
    let e := c.trans (i.trans (pullbackIdIso (E := P.Fiber)))
    have he : e.IsEquivariant ((ρ.pullback z₀ hz₀).pullback πV hπ) ρ := by
      intro g v w
      have hc := ρ.pullbackCompIso_isEquivariant z₀ hz₀ πV hπ g v w
      change c.linearEquiv (g • v) _ = (ρ.pullback (z₀.comp πV) hcomp).linearMap g v
        (c.linearEquiv v w) at hc
      have hh := hi g v (c.linearEquiv v w)
      change e.linearEquiv (g • v) _ = ρ.linearMap g v (e.linearEquiv v w)
      change (pullbackIdIso (E := P.Fiber)).linearEquiv (g • v)
        (i.linearEquiv (g • v) (c.linearEquiv (g • v) _)) =
        ρ.linearMap g v ((pullbackIdIso (E := P.Fiber)).linearEquiv v
          (i.linearEquiv v (c.linearEquiv v w)))
      rw [pullbackIdIso_apply, pullbackIdIso_apply, hc]
      exact hh
    refine ⟨e.symm, ?_⟩
    intro g v w
    apply (e.linearEquiv (g • v)).injective
    change e.linearEquiv (g • v) ((e.linearEquiv (g • v)).symm _) =
      e.linearEquiv (g • v) (((ρ.pullback z₀ hz₀).pullback πV hπ).linearMap g v
        ((e.linearEquiv v).symm w))
    rw [LinearEquiv.apply_symm_apply]
    exact (he g v ((e.linearEquiv v).symm w) |>.trans
      (congrArg (ρ.linearMap g v) ((e.linearEquiv v).apply_symm_apply w))).symm
  obtain ⟨a, ha⟩ := equivariantSupportBundleTriple_kZeroClass_surjective (G := G) z
  obtain ⟨e, he⟩ := hcompare a.1.source a.2.sourceAction
  obtain ⟨f, hf⟩ := hcompare a.1.target a.2.targetAction
  let E := a.1.source.pullback z₀
  let F := a.1.target.pullback z₀
  let ρE := a.2.sourceAction.pullback z₀ hz₀
  let ρF := a.2.targetAction.pullback z₀ hz₀
  let σE := ρE.pullback πV hπ
  let σF := ρF.pullback πV hπ
  let a' := a.1.datum.congr e f
  have heinv (g : G) (x : Z) (v : E.Fiber (πV x)) :
      (e.linearEquiv (g • x)).symm (σE.linearMap g x v) =
        a.2.sourceAction.linearMap g x ((e.linearEquiv x).symm v) := by
    apply (e.linearEquiv (g • x)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (he g x ((e.linearEquiv x).symm v) |>.trans
      (congrArg (σE.linearMap g x) ((e.linearEquiv x).apply_symm_apply v))).symm
  have ha' : a'.IsEquivariant σE σF := by
    refine ⟨a.2.isEquivariant.invariant_control, ?_⟩
    intro g x v
    let gx : (a.1.datum.controlᶜ : Set Z) := ⟨g • x.val,
      fun h ↦ x.property ((a.2.isEquivariant.invariant_control g x.val).mp h)⟩
    change f.linearEquiv (g • x.val) (a.1.datum.boundary.linearEquiv gx
        ((e.linearEquiv (g • x.val)).symm (σE.linearMap g x.val v))) =
      σF.linearMap g x.val (f.linearEquiv x.val
        (a.1.datum.boundary.linearEquiv x ((e.linearEquiv x.val).symm v)))
    refine (congrArg (fun w : a.1.source.Fiber (g • x.val) ↦
      f.linearEquiv (g • x.val) (a.1.datum.boundary.linearEquiv gx w))
      (heinv g x.val v)).trans ?_
    exact (congrArg (f.linearEquiv (g • x.val))
      (a.2.isEquivariant.boundary_intertwines g x ((e.linearEquiv x.val).symm v))).trans
      (hf g x.val _)
  let A := EquivariantSupportBundleTriple.ofBoundary
    (E.pullback πV) (F.pullback πV) a' σE σF ha'
  have hA : A.kZeroClass = a.kZeroClass := by
    apply Eq.symm
    apply equivariantSupportTripleKZero_generator_relations.1 a A
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, Set.Subset.refl _, Set.Subset.refl _,
      e, f, he, hf, ?_⟩
    intro x v
    refine (congrArg (f.linearEquiv x.val)
      (a.1.datum.enlarge_apply a.1.datum.control a.1.datum.isCompact_control
        (Set.Subset.refl _) x v)).trans ?_
    refine Eq.trans ?_ (a'.enlarge_apply a.1.datum.control a.1.datum.isCompact_control
      (Set.Subset.refl _) x (e.linearEquiv x.val v)).symm
    change f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x v) =
      f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x
        ((e.linearEquiv x.val).symm (e.linearEquiv x.val v)))
    exact congrArg (fun w : a.1.source.Fiber x.val ↦
      f.linearEquiv x.val (a.1.datum.boundary.linearEquiv x w))
      ((e.linearEquiv x.val).symm_apply_apply v).symm
  -- Normalize the same transported boundary, and retain its fixed-action homotopy witness.
  obtain ⟨b, hb, hzero, hhom, Hrad⟩ :=
    exists_equivariant_radial_cotangent_representative IG E F ρE ρF a' ha'
  refine ⟨E, F, ρE, ρF, b, hb, hzero, hhom, ?_⟩
  exact (equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
    (E.pullback πV) (F.pullback πV) σE σF a' b ha' hb Hrad).symm.trans (hA.trans ha)

end AtiyahSinger
