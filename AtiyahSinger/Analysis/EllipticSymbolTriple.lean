/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PuncturedSymbol
public import AtiyahSinger.Topology.ModelBundleHom
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# The actual elliptic symbol as an isomorphism at infinity

Public module ID: M0455.

SG III.1 (1.6) and III.13 (13.1). Pull back the original bundles to the actual
cotangent total space. On the complement of the zero section, joint continuity
and fiber bijectivity give the original symbol as the boundary isomorphism.
Its compact control is the zero section over a compact base; no homogeneous
representative or cotangent metric is required for this topological step.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

open ComplexBundle

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

/-- The original symbol on the exterior, with canonical pullback reassociation. -/
def ellipticSymbolBoundary (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    RelativeTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) cotangentZeroSetᶜ :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let p := cotangentProjection (n := n) (M := M)
  let i : C(PuncturedCotangentBundle (n := n) (M := M),
      CotangentTotalSpace (n := n) (M := M)) := ⟨Subtype.val, continuous_subtype_val⟩
  let e := modelPullbackIso (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin q)) (p.comp i)
    (fun z ↦ a z.val.proj z.val.snd) ha
    (fun z ↦ hi z.val.proj z.val.snd z.property)
  let cE : Iso (Restrict ((p : _ → M) *ᵖ E) cotangentZeroSetᶜ)
      (((p.comp i : C(_, M)) : _ → M) *ᵖ E) := pullbackCompIso (E := E) p i
  let cF : Iso (Restrict ((p : _ → M) *ᵖ F) cotangentZeroSetᶜ)
      (((p.comp i : C(_, M)) : _ → M) *ᵖ F) := pullbackCompIso (E := F) p i
  cE.trans (e.trans cF.symm)

/-- The exterior isomorphism is exactly the given symbol, on every original vector. -/
theorem ellipticSymbolBoundary_apply (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a)
    (z : PuncturedCotangentBundle (n := n) (M := M)) (v : E z.val.proj) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (ellipticSymbolBoundary a ha hi).linearEquiv z v = a z.val.proj z.val.snd v := by
  /- The two pullback reassociation isomorphisms preserve each vector. The middle isomorphism
  has the original Hom map as its forward function. Compose their action formulas to recover
  the original symbol value. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let p := cotangentProjection (n := n) (M := M)
  let i : C(PuncturedCotangentBundle (n := n) (M := M),
      CotangentTotalSpace (n := n) (M := M)) := ⟨Subtype.val, continuous_subtype_val⟩
  -- Cancel the target comparison, whose forward map fixes every original vector.
  apply ((pullbackCompIso (E := F) p i).linearEquiv z).injective
  change (pullbackCompIso (E := F) p i).linearEquiv z
    (((pullbackCompIso (E := F) p i).linearEquiv z).symm
      ((modelPullbackIso (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin q))
        (p.comp i) (fun z ↦ a z.val.proj z.val.snd) ha
        (fun z ↦ hi z.val.proj z.val.snd z.property)).linearEquiv z
          ((pullbackCompIso (E := E) p i).linearEquiv z v))) = _
  rw [LinearEquiv.apply_symm_apply]
  change a z.val.proj z.val.snd
    ((pullbackCompIso (E := E) p i).linearEquiv z v) =
      (pullbackCompIso (E := F) p i).linearEquiv z (a z.val.proj z.val.snd v)
  rw [pullbackCompIso_apply, pullbackCompIso_apply]

/-- The boundary inverse is the inverse of the original symbol. -/
theorem ellipticSymbolBoundary_symm_apply (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a)
    (z : PuncturedCotangentBundle (n := n) (M := M)) (v : E z.val.proj) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (ellipticSymbolBoundary a ha hi).symm.linearEquiv z (a z.val.proj z.val.snd v) = v := by
  /- Use the exact forward formula and the left-inverse law of that same fiber equivalence.
  There are no basis or finite-bundle choices in this raw boundary statement. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  rw [← ellipticSymbolBoundary_apply a ha hi z v]
  exact ((ellipticSymbolBoundary a ha hi).linearEquiv z).symm_apply_apply v

variable [CompactSpace M]

/-- The support triple with the original pulled-back bundles and zero-section control. -/
def ellipticSymbolTriple (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  { control := cotangentZeroSet
    isCompact_control := isCompact_cotangentZeroSet
    boundary := ellipticSymbolBoundary a ha hi }

/-- The triple uses exactly the zero section as control. -/
theorem ellipticSymbolTriple_control (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (ellipticSymbolTriple a ha hi).control = cotangentZeroSet := by
  /- The support-triple constructor explicitly stores this set. Compactness is supplied by the
  image of the compact base under its zero section. -/
  rfl

/-- The support triple preserves the original symbol action. -/
theorem ellipticSymbolTriple_boundary_apply (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a)
    (z : PuncturedCotangentBundle (n := n) (M := M)) (v : E z.val.proj) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (ellipticSymbolTriple a ha hi).boundary.linearEquiv z v = a z.val.proj z.val.snd v := by
  /- The triple boundary is the boundary isomorphism already constructed. Its exact application
  theorem gives the formula, without passing through a K-group comparison. -/
  exact ellipticSymbolBoundary_apply a ha hi z v

/-- Only off-zero values determine the actual raw triple. -/
theorem ellipticSymbolTriple_congr (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a)
    (b : GlobalSymbolFunction (n := n) E F)
    (hb : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) b) (hj : IsEllipticGlobalSymbol E F b)
    (hab : ∀ x ξ, ξ ≠ 0 → a x ξ = b x ξ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ellipticSymbolTriple a ha hi = ellipticSymbolTriple b hb hj := by
  /- The controls coincide. The given off-zero equality and boundary action formulas identify
  every fiber equivalence. The remaining continuity and compactness fields are proof
  irrelevant; zero-section values are unused. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  -- Both data constructors use the very same zero-section control.
  change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
    CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
  congr 1
  apply Iso.ext
  intro z
  apply LinearEquiv.ext
  intro v
  exact (ellipticSymbolBoundary_apply a ha hi z v).trans
    ((congrArg (fun L ↦ L v) (hab z.val.proj z.val.snd z.property)).trans
      (ellipticSymbolBoundary_apply b hb hj z v).symm)

/-- A jointly continuous elliptic family gives a uniformly controlled triple homotopy. -/
theorem ellipticSymbolTriple_homotopic (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a)
    (b : GlobalSymbolFunction (n := n) E F)
    (hb : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) b) (hj : IsEllipticGlobalSymbol E F b)
    (H : unitInterval → GlobalSymbolFunction (n := n) E F)
    (hH : IsContinuousOffZeroSymbolFamily (r := r) (q := q) H)
    (hI : ∀ t, IsEllipticGlobalSymbol E F (H t)) (h0 : H 0 = a) (h1 : H 1 = b) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (ellipticSymbolTriple a ha hi).Homotopic (ellipticSymbolTriple b hb hj) := by
  /- Use the compact zero section as the single control for all times. Apply the modeled Hom
  adapter over the product of the interval and nonzero covectors, then the canonical
  pullback comparisons. Local finite rank makes the inverse jointly continuous. The stated
  endpoint equalities and exact action formulas give the required cylinder isomorphism. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let p := cotangentProjection (n := n) (M := M)
  let i : C(PuncturedCotangentBundle (n := n) (M := M),
      CotangentTotalSpace (n := n) (M := M)) := ⟨Subtype.val, continuous_subtype_val⟩
  let s : C(unitInterval × PuncturedCotangentBundle (n := n) (M := M),
      PuncturedCotangentBundle (n := n) (M := M)) := ⟨Prod.snd, continuous_snd⟩
  -- Build one invertible Hom section over the actual product of time and exterior.
  let e := modelPullbackIso (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin q))
    ((p.comp i).comp s) (fun z ↦ H z.1 z.2.val.proj z.2.val.snd) hH
    (fun z ↦ hI z.1 z.2.val.proj z.2.val.snd z.2.property)
  let cE := ((pullbackCompIso (E := E) p i).pullback s).trans
    (pullbackCompIso (E := E) (p.comp i) s)
  let cF := ((pullbackCompIso (E := F) p i).pullback s).trans
    (pullbackCompIso (E := F) (p.comp i) s)
  let J := cE.trans (e.trans cF.symm)
  -- The reassociations preserve vectors at every time, not merely at the endpoints.
  have hcE (t : unitInterval) (z : PuncturedCotangentBundle (n := n) (M := M))
      (v : E z.val.proj) : cE.linearEquiv (t, z) v = v := by
    change (pullbackCompIso (E := E) (p.comp i) s).linearEquiv (t, z)
      ((pullbackCompIso (E := E) p i).linearEquiv z v) = v
    exact (pullbackCompIso_apply (E := E) (p.comp i) s (t, z) _).trans
      (pullbackCompIso_apply (E := E) p i z v)
  have hcF (t : unitInterval) (z : PuncturedCotangentBundle (n := n) (M := M))
      (w : F z.val.proj) : cF.linearEquiv (t, z) w = w := by
    change (pullbackCompIso (E := F) (p.comp i) s).linearEquiv (t, z)
      ((pullbackCompIso (E := F) p i).linearEquiv z w) = w
    exact (pullbackCompIso_apply (E := F) (p.comp i) s (t, z) _).trans
      (pullbackCompIso_apply (E := F) p i z w)
  have hJ (t : unitInterval) (z : PuncturedCotangentBundle (n := n) (M := M))
      (v : E z.val.proj) : J.linearEquiv (t, z) v = H t z.val.proj z.val.snd v := by
    apply (cF.linearEquiv (t, z)).injective
    change cF.linearEquiv (t, z)
      ((cF.linearEquiv (t, z)).symm (e.linearEquiv (t, z)
        (cE.linearEquiv (t, z) v))) = _
    rw [LinearEquiv.apply_symm_apply]
    change H t z.val.proj z.val.snd (cE.linearEquiv (t, z) v) =
      cF.linearEquiv (t, z) (H t z.val.proj z.val.snd v)
    rw [hcE, hcF]
  -- A single compact zero section controls the full cylinder and both original triples.
  refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet,
    Set.Subset.refl _, Set.Subset.refl _, ⟨{ iso := J, map_zero := ?_, map_one := ?_ }⟩⟩
  · intro z v
    have hstart : J.linearEquiv (0, z) v = a z.val.proj z.val.snd v :=
      (hJ 0 z v).trans
        (congrArg (fun A : GlobalSymbolFunction (n := n) E F ↦ A z.val.proj z.val.snd v) h0)
    have hboundary : ((ellipticSymbolTriple a ha hi).enlarge cotangentZeroSet
        isCompact_cotangentZeroSet (Set.Subset.refl _)).boundary.linearEquiv z v =
          a z.val.proj z.val.snd v :=
      ((ellipticSymbolTriple a ha hi).enlarge_apply cotangentZeroSet
        isCompact_cotangentZeroSet (Set.Subset.refl _) z v).trans
          (ellipticSymbolTriple_boundary_apply a ha hi z v)
    exact hstart.trans hboundary.symm
  · intro z v
    have hend : J.linearEquiv (1, z) v = b z.val.proj z.val.snd v :=
      (hJ 1 z v).trans
        (congrArg (fun A : GlobalSymbolFunction (n := n) E F ↦ A z.val.proj z.val.snd v) h1)
    have hboundary : ((ellipticSymbolTriple b hb hj).enlarge cotangentZeroSet
        isCompact_cotangentZeroSet (Set.Subset.refl _)).boundary.linearEquiv z v =
          b z.val.proj z.val.snd v :=
      ((ellipticSymbolTriple b hb hj).enlarge_apply cotangentZeroSet
        isCompact_cotangentZeroSet (Set.Subset.refl _) z v).trans
          (ellipticSymbolTriple_boundary_apply b hb hj z v)
    exact hend.trans hboundary.symm

/-- Reversing the elliptic symbol inverts its actual support triple. -/
theorem ellipticSymbolTriple_inverse (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ellipticSymbolTriple (r := q) (q := r) (globalSymbolInverse a)
      (IsContinuousOffZeroGlobalSymbol.inverse (r := r) (q := q) ha hi)
      (IsEllipticGlobalSymbol.inverse (r := r) (q := q) hi) =
      (ellipticSymbolTriple a ha hi).inverse := by
  /- The two triples have identical zero-section control. On each nonzero fiber the totalized
  analytic inverse agrees with the inverse of the bijective original continuous linear map.
  Use boundary extensionality. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  -- Compare the two original boundaries on their common nonzero-covector domain.
  change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
    CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
  congr 1
  apply Iso.ext
  intro z
  apply LinearEquiv.ext
  intro w
  obtain ⟨v, rfl⟩ := (hi z.val.proj z.val.snd z.property).surjective w
  rw [ellipticSymbolBoundary_apply]
  have hleft := congrArg (fun L ↦ L v)
    (globalSymbolInverse_comp (r := r) (q := q) hi z.val.proj z.val.snd z.property)
  change globalSymbolInverse a z.val.proj z.val.snd (a z.val.proj z.val.snd v) = _
  exact hleft.trans (ellipticSymbolBoundary_symm_apply a ha hi z v).symm

end AtiyahSinger
