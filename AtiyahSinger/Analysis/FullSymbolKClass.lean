/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolBundleHom
public import AtiyahSinger.Analysis.FullSymbolExterior
public import AtiyahSinger.Geometry.CotangentMetricCompact
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# The compact-support class of the original general elliptic full symbol

Public module ID: M2283.

The actual full symbol supplies an exterior isomorphism on its original cotangent
pullbacks. Quantitative ellipticity constructs the compact control internally. A global
isomorphism of the original target cotangent pullback changes that exterior map without changing
its compact-support class. No analytic index equality is assumed or encoded in the triple.

Sources: SG I.9.26 and III.13 (13.1). Principal-representative independence is separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

attribute [local instance] isFiniteRank_pullback isFiniteRank_restrict
  t2Space_cotangent locallyCompactSpace_cotangent

/-- The original full-symbol map on the exterior of a specified compact control. -/
def fullSymbolTripleWithControl {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (K : Set (CotangentTotalSpace (n := n) (M := M))) (hK : IsCompact K)
    (hi : ∀ z : CotangentTotalSpace (n := n) (M := M),
      z ∉ K → (a.val z.proj z.snd).IsInvertible) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  { control := K
    isCompact_control := hK
    boundary := ((fullSymbolBundleHom a).restrict Kᶜ).toIso <| by
      intro z
      change Function.Bijective (a.val z.val.proj z.val.snd)
      obtain ⟨e, he⟩ := hi z.val z.property
      rw [← he]
      exact e.bijective }

/-- The exterior boundary retains the exact original forward symbol map. -/
theorem fullSymbolTripleWithControl_boundary_apply {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (K : Set (CotangentTotalSpace (n := n) (M := M))) (hK : IsCompact K)
    (hi : ∀ z : CotangentTotalSpace (n := n) (M := M),
      z ∉ K → (a.val z.proj z.snd).IsInvertible) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (z : ↥(Kᶜ)) (v : E z.val.proj),
      (fullSymbolTripleWithControl a K hK hi).boundary.linearEquiv z v =
        a.val z.val.proj z.val.snd v := by
  /- Restriction and conversion to an Iso keep the same forward linear map. -/
  let : TopologicalSpace (TotalSpace Unit E) := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let : TopologicalSpace (TotalSpace Unit F) := modelTopology (EuclideanSpace ℂ (Fin q)) F
  intro z v
  rfl

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- Quantitative ellipticity constructs compact control for the original full-symbol triple. -/
def fullSymbolTriple {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let g : SmoothCotangentMetric (n := n) (M := M) := SmoothCotangentMetric.nonempty.some
  let R := (ha.exists_metric_radius g).choose
  let hR := (ha.exists_metric_radius g).choose_spec
  fullSymbolTripleWithControl a {z | g.length z.proj z.snd ≤ R} (g.isCompact_sublevel R)
    (fun z hz ↦ hR.2 z.proj z.snd (lt_of_not_ge hz))

/-- The internally selected compact control does not change the original boundary map. -/
theorem fullSymbolTriple_boundary_apply {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (z : ↥((fullSymbolTriple a ha).controlᶜ)) (v : E z.val.proj),
      (fullSymbolTriple a ha).boundary.linearEquiv z v = a.val z.val.proj z.val.snd v := by
  /- The constructor obtains only the exterior domain and its invertibility certificate. -/
  let : TopologicalSpace (TotalSpace Unit E) := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let : TopologicalSpace (TotalSpace Unit F) := modelTopology (EuclideanSpace ℂ (Fin q)) F
  intro z v
  rfl

/-- The actual compact-support K class of the original generally elliptic full symbol. -/
def fullSymbolKClass {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  (fullSymbolTriple a ha).compactSupportClass

/-- A global automorphism of the target cotangent pullback preserves the full-symbol class. -/
theorem fullSymbolKClass_eq_of_targetIso {m : ℝ}
    (a b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val)
    (hb : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m b.val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (u : Iso ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F)),
      (∀ (z : CotangentTotalSpace (n := n) (M := M)) (v : E z.proj),
        a.val z.proj z.snd v = u.linearEquiv z (b.val z.proj z.snd v)) →
      fullSymbolKClass a ha = fullSymbolKClass b hb := by
  /- Enlarge both genuine symbol triples to the union of their compact controls. On this
  common exterior their original forward maps differ by u on the target cotangent pullback.
  This permits u to depend on both the base point and its covector. The existing
  global-bundle-isomorphism invariance then gives the same compact-support class. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  intro u hu
  let A := fullSymbolTriple a ha
  let B := fullSymbolTriple b hb
  let K := A.control ∪ B.control
  have hK : IsCompact K := A.isCompact_control.union B.isCompact_control
  -- Compare the actual original actions on this common exterior, using the same u.
  have heq : A.enlarge K hK Set.subset_union_left =
      (B.enlarge K hK Set.subset_union_right).congr (Iso.refl _) u := by
    change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    change E z.val.proj at v
    -- Retype the same vector and both actual outputs in their original fibers.
    let zA : ↥((fullSymbolTriple a ha).controlᶜ) :=
      ⟨z.val, fun hz ↦ z.property (Set.subset_union_left hz)⟩
    let zB : ↥((fullSymbolTriple b hb).controlᶜ) :=
      ⟨z.val, fun hz ↦ z.property (Set.subset_union_right hz)⟩
    have hAouter := A.enlarge_apply K hK Set.subset_union_left z v
    have hBouter := B.enlarge_apply K hK Set.subset_union_right z v
    dsimp only [A] at hAouter
    dsimp only [B] at hBouter
    have hleft : ((A.enlarge K hK Set.subset_union_left).boundary.linearEquiv z v :
        F z.val.proj) = a.val z.val.proj z.val.snd v :=
      hAouter.trans (fullSymbolTriple_boundary_apply a ha zA v)
    have hright : ((B.enlarge K hK Set.subset_union_right).boundary.linearEquiv z v :
        F z.val.proj) = b.val z.val.proj z.val.snd v :=
      hBouter.trans (fullSymbolTriple_boundary_apply b hb zB v)
    change (A.enlarge K hK Set.subset_union_left).boundary.linearEquiv z v =
      u.linearEquiv z.val ((B.enlarge K hK Set.subset_union_right).boundary.linearEquiv z v)
    exact hleft.trans ((hu z.val v).trans (congrArg (u.linearEquiv z.val) hright).symm)
  change A.compactSupportClass = B.compactSupportClass
  -- Enlargement and conjugation use the already established support-class invariances.
  calc
    A.compactSupportClass = (A.enlarge K hK Set.subset_union_left).compactSupportClass :=
      (A.compactSupportClass_enlarge K hK Set.subset_union_left).symm
    _ = ((B.enlarge K hK Set.subset_union_right).congr (Iso.refl _) u).compactSupportClass :=
      congrArg CompactSupportTriple.compactSupportClass heq
    _ = (B.enlarge K hK Set.subset_union_right).compactSupportClass :=
      (B.enlarge K hK Set.subset_union_right).compactSupportClass_congr (Iso.refl _) u
    _ = B.compactSupportClass := B.compactSupportClass_enlarge K hK Set.subset_union_right

end AtiyahSinger
