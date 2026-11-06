/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantBoundarySmoothing
public import AtiyahSinger.Geometry.EquivariantBundleSmoothing
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Smooth representatives of original fixed-rank equivariant support triples

Public module ID: M1210.

For a compact finite-dimensional Lie group on a compact smooth base, an
original continuous equivariant support triple has a smooth representative
with the same compact control, provided each
original bundle has one fixed rank. The statement retains actual equivariant
isomorphisms from those original bundles to the selected smooth bundles.
The initial boundary on the new bundles is exactly the original boundary
conjugated by those isomorphisms. One actual continuous equivariant boundary
homotopy connects it to the selected smooth boundary with the original control
unchanged, and the new generator equals the original equivariant K generator.

The two prescribed ranks need not agree when the original exterior is empty.
No arbitrary original continuous frame is declared smooth, and the original
continuous boundary is not required to extend through its compact control.
This theorem does not assemble varying-rank smooth bundles or construct a
homogeneous elliptic symbol from an arbitrary equivariant K class.

SG I.9.23--9.26 and ASI I Section 2 supply the support-triple framework;
SG Appendix A, Remark A.1, supplies ordinary smooth classification, and
SG III.9 supplies compact-group averaging. The equivariant smoothing used
here is a project supplement; SG is not claimed to state this exact result.
The same specified original objects and control enter both constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle TopologicalSpace
open scoped Manifold ContDiff

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [hLie : LieGroup 𝓘(ℝ, VG) ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

include hDim hLie hGC hGT hM hT hSC hC hAction

/-- A fixed-rank continuous equivariant support triple has a smooth representative of its class. -/
theorem EquivariantSupportBundleTriple.exists_smooth_representative
    (a : EquivariantSupportBundleTriple G M) (r q : ℕ)
    (hSourceRank : ∀ x : M, Module.finrank ℂ (a.1.source.Fiber x) = r)
    (hTargetRank : ∀ x : M, Module.finrank ℂ (a.1.target.Fiber x) = q) :
    ∃ E F : SmoothFiniteComplexBundle (n := n) M, E.rank = r ∧ F.rank = q ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ (σE : EquivariantStructure G E.Fiber) (σF : EquivariantStructure G F.Fiber),
        σE.IsSmooth (n := n) (r := E.rank) 𝓘(ℝ, VG) ∧
        σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
        ∃ (e : Iso a.1.source.Fiber E.Fiber) (f : Iso a.1.target.Fiber F.Fiber),
          e.IsEquivariant a.2.sourceAction σE ∧ f.IsEquivariant a.2.targetAction σF ∧
          let c := a.1.datum.congr e f
          let W : Opens M :=
            ⟨a.1.datum.controlᶜ, a.1.datum.isCompact_control.isClosed.isOpen_compl⟩
          ∃ β : RelativeTriple E.Fiber F.Fiber a.1.datum.controlᶜ,
            IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank) (M := W)
              (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E.Fiber))
              (F := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ F.Fiber))
              (fun x ↦ (β.linearEquiv x).toLinearMap) ∧
            let b : CompactSupportTriple E.Fiber F.Fiber :=
              { control := a.1.datum.control
                isCompact_control := a.1.datum.isCompact_control
                boundary := β }
            ∃ hb : b.IsEquivariant σE σF,
              (∃ H : CompactSupportTriple.EquivariantHomotopy σE σF c b,
                H.control = a.1.datum.control) ∧
              a.kZeroClass =
                (EquivariantSupportBundleTriple.ofBoundary
                  (FiniteBundle.ofFamily E.Fiber) (FiniteBundle.ofFamily F.Fiber)
                  b σE σF hb).kZeroClass := by
  /- Stage 1: apply smooth equivariant bundle realization separately to
  the original source and target of a, using their own fixed-rank witnesses.
  Retain the selected smooth bundles E and F, their exact ranks r and q,
  their jointly smooth actions sigmaE and sigmaF, and the actual continuous
  equivariant bundle isomorphisms e and f from the original fibers. Their
  continuity refers to the original input topologies and the selected target
  topologies, retyped only through modelTopology. The source and target
  ranks are not identified with each other.
  Stage 2: take c to be exactly a.datum.congr e f. Its control is the original
  K, and its exterior map is f_x composed with a_x composed with e_x inverse.
  The original invariance of K and the three given intertwining equations
  show locally in this proof that c is equivariant for sigmaE and sigmaF.
  The inverse of e intertwines because its actual fiber equivalences are
  inverse to those of e. No replacement boundary, arbitrary homotopy class
  or new equivariant action is selected at this step.
  Stage 3: apply the existing same-control equivariant boundary smoothing
  theorem to c on these same smooth bundles and actions. Since c.control=K
  by its original constructor, its exterior is exactly the stated W. Keep
  the resulting actual beta, its native pullback-atlas smoothness and the
  actual continuous equivariant homotopy H from c to b. Form b by copying
  the original K and its compactness certificate and using this beta. The
  certificate H.control=K is retained exactly, rather than replaced by an
  unspecified larger compact set. This step uses pointwise fine approximation
  on W; compactness of M does not imply a uniform exterior inverse bound.
  Stage 4: package E and F as FiniteBundle.ofFamily using their exact modeled
  topologies and existing finite-rank certificates. The original e and f
  give an actual IsIsomorphic square from a to the packaged c, with common
  control K. Its boundary equation is the explicit conjugation formula and
  the inverse identity for e. The isomorphism generator relation therefore
  equates the original a.kZeroClass with this particular c generator.
  Stage 5: the existing controlled equivariant homotopy theorem identifies
  that c generator with the b generator built from the very same E, F,
  sigmaE, sigmaF and beta. The original smooth manifold is locally compact
  by its finite-dimensional charts, as required by that class theorem.
  Compose these two equalities to obtain the displayed original K-class
  equality. No new quotient model or class-level representative is chosen.
  Zero ranks and empty bases use the same existing realization statements;
  an empty exterior permits different global source and target ranks. The
  argument never enlarges a previously specified proper K to discard its
  exterior, and it makes no homogeneity or elliptic-realization assertion. -/
  classical
  -- Realize the two original actions separately, retaining their independent ranks.
  obtain ⟨E, hEr, σE, hσE, e, he⟩ :=
    a.2.sourceAction.exists_smooth_bundle_iso (VG := VG) (n := n) r hSourceRank
  obtain ⟨F, hFq, σF, hσF, f, hf⟩ :=
    a.2.targetAction.exists_smooth_bundle_iso (VG := VG) (n := n) q hTargetRank
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let c := a.1.datum.congr e f
  have hc : c.IsEquivariant σE σF := by
    refine ⟨a.2.isEquivariant.invariant_control, ?_⟩
    intro g x v
    -- Solve the forward intertwining equation for the actual inverse of e.
    have hinv : e.symm.linearEquiv (g • x.val) (σE.linearMap g x.val v) =
        a.2.sourceAction.linearMap g x.val (e.symm.linearEquiv x.val v) := by
      have he' := he g x.val (e.symm.linearEquiv x.val v)
      change e.linearEquiv (g • x.val)
        (a.2.sourceAction.linearMap g x.val ((e.linearEquiv x.val).symm v)) =
          σE.linearMap g x.val (e.linearEquiv x.val ((e.linearEquiv x.val).symm v)) at he'
      rw [LinearEquiv.apply_symm_apply] at he'
      exact (congrArg (e.linearEquiv (g • x.val)).symm he').symm.trans
        ((e.linearEquiv (g • x.val)).symm_apply_apply _)
    let gx : (a.1.datum.controlᶜ : Set M) :=
      ⟨g • x.val, fun hx ↦ x.property ((a.2.isEquivariant.invariant_control g x.val).mp hx)⟩
    change f.linearEquiv (g • x.val)
      (a.1.datum.boundary.linearEquiv gx
        (e.symm.linearEquiv (g • x.val) (σE.linearMap g x.val v))) = _
    rw [hinv]
    exact (congrArg (f.linearEquiv (g • x.val))
      (a.2.isEquivariant.boundary_intertwines g x _)).trans (hf g x.val _)
  -- Smooth this exact conjugated boundary on its unchanged exterior.
  obtain ⟨β, hβ, hb, H, hH⟩ :=
    c.exists_equivariant_smooth_boundary_homotopy 𝓘(ℝ, VG) σE σF hσE hσF hc
  let b : CompactSupportTriple E.Fiber F.Fiber :=
    { control := a.1.datum.control
      isCompact_control := a.1.datum.isCompact_control
      boundary := β }
  let c' := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily E.Fiber) (FiniteBundle.ofFamily F.Fiber) c σE σF hc
  have hiso : a.IsIsomorphic c' := by
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, (fun _ hx ↦ hx), (fun _ hx ↦ hx),
      e, f, he, hf, ?_⟩
    intro x v
    -- Both sides have the original control; the conjugation square cancels e inverse.
    rw [a.1.datum.enlarge_apply a.1.datum.control a.1.datum.isCompact_control
      (fun _ hx ↦ hx),
      c'.1.datum.enlarge_apply a.1.datum.control a.1.datum.isCompact_control
        (fun _ hx ↦ hx)]
    change f.linearEquiv x (a.1.datum.boundary.linearEquiv x v) =
      f.linearEquiv x (a.1.datum.boundary.linearEquiv x
        ((e.linearEquiv x).symm (e.linearEquiv x v)))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨E, F, hEr, hFq, σE, σF, hσE, hσF, e, f, he, hf,
    β, hβ, hb, ⟨H, hH⟩, ?_⟩
  -- Compose the isomorphism relation with the fixed-action controlled homotopy relation.
  exact (equivariantSupportTripleKZero_generator_relations.1 a c' hiso).trans
    (equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
      (FiniteBundle.ofFamily E.Fiber) (FiniteBundle.ofFamily F.Fiber)
      σE σF c b hc hb ⟨H⟩)

end AtiyahSinger.ComplexBundle
