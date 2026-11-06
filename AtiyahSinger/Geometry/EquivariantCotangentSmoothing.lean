/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousSmoothing
public import AtiyahSinger.Geometry.EquivariantBundleSmoothing
public import AtiyahSinger.Geometry.InvariantCotangentMetric
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Smooth homogeneous replacement of original equivariant cotangent triples

Public module ID: M1185.

An original continuous equivariant triple on the cotangent pullbacks of two
constant-rank bundles, with the zero section as its control, has a smooth
homogeneous elliptic representative. The base is compact, while its
cotangent space need not be compact. The selected
smooth bundles retain the respective prescribed ranks, and actual equivariant
base isomorphisms compare them with the original continuous bundles. The
initial boundary on the new bundles is exactly the conjugation by the native
cotangent pullbacks of those same isomorphisms. An actual equivariant homotopy
with the original zero-section control connects that boundary to precisely
the elliptic triple of the selected degree-zero symbol. The resulting equality
is in the original equivariant support group, before forgetting the action.

The compact finite-dimensional Lie-group hypothesis comes from smooth bundle
realization, even though invariant metrics and fixed-smooth-bundle boundary
smoothing admit weaker group hypotheses. Source and target ranks may differ
when the punctured cotangent domain is empty, including in dimension zero.
This theorem does not choose a global fixed rank for a varying-rank bundle.

SG III.13 Lemma 13.3 and the paragraph preceding (13.7), pp.245--246, give
the ordinary homogeneous representative route. SG Appendix A, Remark A.1,
gives ordinary smooth classification, and SG III.9 gives averaging. The
present equivariant assembly is a project supplement using those routes,
not a separately numbered result claimed in SG. The smooth bundle
realization, homogeneous boundary smoothing and fine approximation
used here are project supplements. The original bundles, pulled actions
and zero control are retained.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

include hDim hLie hGC hGT hM hT hSC hC hAction

set_option linter.unusedVariables false in

set_option maxHeartbeats 1000000 in
-- The native iterated pullbacks retain the original dependent fiber topologies.
/-- Smooth homogeneous replacement on the exact original constant-rank cotangent pullbacks. -/
theorem CompactSupportTriple.exists_equivariant_smooth_cotangent_replacement
    (E₀ F₀ : FiniteBundle M) (r q : ℕ)
    (hSourceRank : ∀ x : M, Module.finrank ℂ (E₀.Fiber x) = r)
    (hTargetRank : ∀ x : M, Module.finrank ℂ (F₀.Fiber x) = q)
    (ρE : EquivariantStructure G E₀.Fiber) (ρF : EquivariantStructure G F₀.Fiber)
    (a : CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E₀.Fiber)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F₀.Fiber))
    (hControl : a.control = cotangentZeroSet)
    (ha : letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
      letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
      letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
        ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      a.IsEquivariant
        (ρE.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))
        (ρF.pullback (cotangentProjection (n := n) (M := M)) (fun _ _ ↦ rfl))) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∃ E F : SmoothFiniteComplexBundle (n := n) M, E.rank = r ∧ F.rank = q ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ (σE : EquivariantStructure G E.Fiber) (σF : EquivariantStructure G F.Fiber),
        σE.IsSmooth (n := n) (r := E.rank) 𝓘(ℝ, VG) ∧
        σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
        ∃ (e : Iso E₀.Fiber E.Fiber) (f : Iso F₀.Fiber F.Fiber),
          e.IsEquivariant ρE σE ∧ f.IsEquivariant ρF σF ∧
          let p := cotangentProjection (n := n) (M := M)
          let τE := σE.pullback p (fun _ _ ↦ rfl)
          let τF := σF.pullback p (fun _ _ ↦ rfl)
          let c := a.congr (e.pullback p) (f.pullback p)
          ∃ hc : c.IsEquivariant τE τF,
            ∃ s : homogeneousGlobalSymbolSpace
                (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0,
              ∃ hi : IsEllipticGlobalSymbol E.Fiber F.Fiber s.val,
                (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
                  equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF g s.val x ξ =
                    s.val x ξ) ∧
                let b := ellipticSymbolTriple s.val s.property.1.continuous hi
                ∃ hb : b.IsEquivariant τE τF,
                  (∃ H : CompactSupportTriple.EquivariantHomotopy τE τF c b,
                    H.control = cotangentZeroSet) ∧
                  (EquivariantSupportBundleTriple.ofBoundary
                    (E₀.pullback p) (F₀.pullback p) a
                    (ρE.pullback p (fun _ _ ↦ rfl))
                    (ρF.pullback p (fun _ _ ↦ rfl)) ha).kZeroClass =
                  (EquivariantSupportBundleTriple.ofBoundary
                    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E.Fiber))
                    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F.Fiber))
                    b τE τF hb).kZeroClass := by
  /- Stage 1: apply exists_smooth_bundle_iso separately to the original
  E0 and F0, their original actions rhoE and rhoF, and their respective
  rank witnesses. Retain the resulting E and F of ranks r and q, smooth
  actions sigmaE and sigmaF, and the actual equivariant isomorphisms e and
  f from the original bundles. The finite-dimensional compact Lie-group
  hypothesis is used here for automatic smoothness of finite-dimensional
  representations; it is not inferred merely from a smooth base action.
  Stage 2: use exactly the native isomorphisms e.pullback pi and
  f.pullback pi along the original cotangent projection. Existing
  equivariant pullback functoriality shows that they intertwine the
  original pulled actions and tauE, tauF. Form c by the existing congr
  constructor. Its boundary is f_x composed with a_(x,xi) composed with
  e_x inverse, and its control is definitionally the original control.
  These intertwining equations give hc without choosing another boundary
  or changing any fiber topology. The projection need not be proper:
  only bundles and their isomorphisms are pulled back in this step.
  Stage 3: choose a smooth cotangent metric invariant for the native
  inverse-differential action, using exists_invariant_smoothCotangentMetric.
  Its inner-product invariance implies length invariance by evaluating
  the same pairing at xi,xi and applying the nonnegative square root.
  Apply exists_equivariant_homogeneous_smooth_boundary to this very c,
  the same sigmaE and sigmaF, and its zero-control equality from hControl.
  This returns the displayed homogeneous s, its actual ellipticity and
  equivariance, and precisely b=ellipticSymbolTriple(s), with the actual
  equivariant boundary homotopy from c to b and control equal to zero.
  Invertibility is controlled on the compact unit cosphere; no compactness
  of the punctured cotangent space or uniform inverse bound there is used.
  Stage 4: the same pulled e and f form an original equivariant
  isomorphism square from the input generator to the generator of c.
  Use the explicit congr boundary formula and the inverse identity for
  e to check this square with the original compact zero control. Its
  generator relation identifies the two original equivariant K classes.
  The existing controlled-homotopy relation then identifies c with the
  generator of the same b, same pulled actions and same selected s from
  Stage 3. Compose these equalities before applying any forgetful map.
  Only the target phantom total-space models use modelTopology, and the
  original cotangent action, original input fibers and boundary remain
  fixed throughout. Empty bases, rank-zero bundles and n=0 use the same
  statements. In dimension zero the punctured domain is empty, so no
  equality between r and q is imposed. Varying-rank classes still require
  a finite invariant clopen decomposition and subsequent assembly. -/
  classical
  obtain ⟨E, hEr, σE, hσE, e, he⟩ :=
    ρE.exists_smooth_bundle_iso (VG := VG) (n := n) r hSourceRank
  obtain ⟨F, hFq, σF, hσF, f, hf⟩ :=
    ρF.exists_smooth_bundle_iso (VG := VG) (n := n) q hTargetRank
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  let τE := σE.pullback p (fun _ _ ↦ rfl)
  let τF := σF.pullback p (fun _ _ ↦ rfl)
  let e' := e.pullback p
  let f' := f.pullback p
  have he' := (ρE.pullback_maps σE p (fun _ _ ↦ rfl)).2 e he
  have hf' := (ρF.pullback_maps σF p (fun _ _ ↦ rfl)).2 f hf
  let c := a.congr e' f'
  have hc : c.IsEquivariant τE τF := by
    refine ⟨ha.invariant_control, ?_⟩
    intro g x v
    -- The actual inverse pullback map intertwines by the original forward equation.
    have hinv : e'.symm.linearEquiv (g • x.val) (τE.linearMap g x.val v) =
        (ρE.pullback p (fun _ _ ↦ rfl)).linearMap g x.val
          (e'.symm.linearEquiv x.val v) := by
      have h := he' g x.val (e'.symm.linearEquiv x.val v)
      change e'.linearEquiv (g • x.val)
        ((ρE.pullback p (fun _ _ ↦ rfl)).linearMap g x.val
          ((e'.linearEquiv x.val).symm v)) =
          τE.linearMap g x.val (e'.linearEquiv x.val ((e'.linearEquiv x.val).symm v)) at h
      rw [LinearEquiv.apply_symm_apply] at h
      exact (congrArg (e'.linearEquiv (g • x.val)).symm h).symm.trans
        ((e'.linearEquiv (g • x.val)).symm_apply_apply _)
    let gx : (a.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))) :=
      ⟨g • x.val, fun hx ↦ x.property ((ha.invariant_control g x.val).mp hx)⟩
    change f'.linearEquiv (g • x.val)
      (a.boundary.linearEquiv gx
        (e'.symm.linearEquiv (g • x.val) (τE.linearMap g x.val v))) = _
    rw [hinv]
    exact (congrArg (f'.linearEquiv (g • x.val))
      (ha.boundary_intertwines g x _)).trans (hf' g x.val _)
  -- The invariant metric determines the same radial normalization in every translated fiber.
  obtain ⟨h, hinner⟩ := exists_invariant_smoothCotangentMetric (G := G) (n := n) (M := M) 𝓘(ℝ, VG)
  have hlength (g : G) (x : M) (ξ : CotangentFiber (n := n) x) :
      h.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
          ⟨x, ξ⟩).snd = h.length x ξ := by
    exact congrArg Real.sqrt (hinner g x ξ ξ)
  obtain ⟨s, hi, hs, hb, hH, hclass⟩ :=
    c.exists_equivariant_homogeneous_smooth_boundary 𝓘(ℝ, VG) σE σF hσE hσF
      h hlength hControl hc
  let c' := EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E.Fiber))
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F.Fiber)) c τE τF hc
  let a' := EquivariantSupportBundleTriple.ofBoundary (E₀.pullback p) (F₀.pullback p) a
    (ρE.pullback p (fun _ _ ↦ rfl)) (ρF.pullback p (fun _ _ ↦ rfl)) ha
  have hiso : a'.IsIsomorphic c' := by
    refine ⟨a.control, a.isCompact_control, ha.invariant_control,
      (fun _ hx ↦ hx), (fun _ hx ↦ hx), e', f', he', hf', ?_⟩
    intro x v
    -- The conjugation square uses identity control inclusions and cancels the same inverse.
    rw [a'.1.datum.enlarge_apply a.control a.isCompact_control (fun _ hx ↦ hx),
      c'.1.datum.enlarge_apply a.control a.isCompact_control (fun _ hx ↦ hx)]
    change f'.linearEquiv x (a.boundary.linearEquiv x v) =
      f'.linearEquiv x (a.boundary.linearEquiv x
        ((e'.linearEquiv x).symm (e'.linearEquiv x v)))
    rw [LinearEquiv.symm_apply_apply]
  refine ⟨E, F, hEr, hFq, σE, σF, hσE, hσF, e, f, he, hf,
    hc, s, hi, hs, hb, hH, ?_⟩
  exact (equivariantSupportTripleKZero_generator_relations.1 a' c' hiso).trans hclass

end AtiyahSinger.ComplexBundle
