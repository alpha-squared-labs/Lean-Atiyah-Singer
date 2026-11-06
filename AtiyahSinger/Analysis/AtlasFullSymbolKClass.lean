/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolBundleHom
public import AtiyahSinger.Analysis.AtlasFullSymbolExterior
public import AtiyahSinger.Geometry.CotangentMetricCompact
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# The compact-support class of an original general elliptic atlas symbol

Public module ID: M2299.

The supplied full symbol determines an actual exterior isomorphism on its original
cotangent pullbacks. Quantitative ellipticity constructs compact control internally.
Any other compact exterior for the same original map computes exactly the same class.
The original fibers may have different locally constant ranks on different components.

Sources: SG I.9.26 and III.13 (13.1). The explicit varying-rank atlas construction is a
project supplement; no analytic-index conclusion is an input to this class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

attribute [local instance] isFiniteRank_pullback isFiniteRank_restrict
  t2Space_cotangent locallyCompactSpace_cotangent

/-- The exact original atlas symbol as an exterior triple with specified compact control. -/
def atlasFullSymbolTripleWithControl {m : ℝ} (a : atlasGlobalSymbolSpace A B m)
    (K : Set (CotangentTotalSpace (n := n) (M := M))) (hK : IsCompact K)
    (hi : ∀ z : CotangentTotalSpace (n := n) (M := M),
      z ∉ K → Function.Bijective (a.val z.proj z.snd)) :
    CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) :=
  letI := A.isFiniteRank
  letI := B.isFiniteRank
  { control := K
    isCompact_control := hK
    boundary := ((atlasFullSymbolBundleHom A B a).restrict Kᶜ).toIso
      (fun z ↦ hi z.val z.property) }

variable [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- Quantitative ellipticity constructs compact control for the exact original atlas symbol. -/
def atlasFullSymbolTriple {m : ℝ} (a : atlasGlobalSymbolSpace A B m)
    (ha : IsEllipticFullAtlasSymbol A B m a.val) :
    CompactSupportTriple
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) :=
  let g : SmoothCotangentMetric (n := n) (M := M) := SmoothCotangentMetric.nonempty.some
  let R := (ha.exists_metric_radius A B g).choose
  let hR := (ha.exists_metric_radius A B g).choose_spec
  atlasFullSymbolTripleWithControl A B a {z | g.length z.proj z.snd ≤ R}
    (g.isCompact_sublevel R) (fun z hz ↦ hR.2 z.proj z.snd (lt_of_not_ge hz))

/-- The chosen compact exterior retains the original forward symbol map on every fiber. -/
theorem atlasFullSymbolTriple_boundary_apply {m : ℝ} (a : atlasGlobalSymbolSpace A B m)
    (ha : IsEllipticFullAtlasSymbol A B m a.val)
    (z : ↥((atlasFullSymbolTriple A B a ha).controlᶜ)) (v : E z.val.proj) :
    (atlasFullSymbolTriple A B a ha).boundary.linearEquiv z v =
      a.val z.val.proj z.val.snd v := by
  rfl

/-- The genuine compact-support K class of the original general elliptic atlas full symbol. -/
def atlasFullSymbolKClass {m : ℝ} (a : atlasGlobalSymbolSpace A B m)
    (ha : IsEllipticFullAtlasSymbol A B m a.val) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  letI := A.isFiniteRank
  letI := B.isFiniteRank
  (atlasFullSymbolTriple A B a ha).compactSupportClass

/-- Any compact exterior of the same original atlas map computes its constructed class. -/
theorem atlasFullSymbolKClass_eq_tripleWithControl {m : ℝ}
    (a : atlasGlobalSymbolSpace A B m) (ha : IsEllipticFullAtlasSymbol A B m a.val)
    (D : Set (CotangentTotalSpace (n := n) (M := M))) (hD : IsCompact D)
    (hi : ∀ z : CotangentTotalSpace (n := n) (M := M),
      z ∉ D → Function.Bijective (a.val z.proj z.snd)) :
    letI := A.isFiniteRank
    letI := B.isFiniteRank
    atlasFullSymbolKClass A B a ha =
      (atlasFullSymbolTripleWithControl A B a D hD hi).compactSupportClass := by
  /- Enlarge both actual triples to the union of their compact controls.
  Their boundary maps then agree as the original full symbol on every exterior vector.
  The existing enlargement invariance identifies their compact-support classes. -/
  let := A.isFiniteRank
  let := B.isFiniteRank
  let T := atlasFullSymbolTriple A B a ha
  let U := atlasFullSymbolTripleWithControl A B a D hD hi
  let K := T.control ∪ U.control
  have hK : IsCompact K := T.isCompact_control.union U.isCompact_control
  have heq : T.enlarge K hK Set.subset_union_left =
      U.enlarge K hK Set.subset_union_right := by
    change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    change E z.val.proj at v
    let zT : ↥((atlasFullSymbolTriple A B a ha).controlᶜ) :=
      ⟨z.val, fun hz ↦ z.property (Set.subset_union_left hz)⟩
    let zU : ↥(Dᶜ) := ⟨z.val, fun hz ↦ z.property (Set.subset_union_right hz)⟩
    have hTouter := T.enlarge_apply K hK Set.subset_union_left z v
    have hUouter := U.enlarge_apply K hK Set.subset_union_right z v
    have hTinner := atlasFullSymbolTriple_boundary_apply A B a ha zT v
    have hUinner : U.boundary.linearEquiv zU v = a.val z.val.proj z.val.snd v := rfl
    exact (hTouter.trans hTinner).trans (hUouter.trans hUinner).symm
  change T.compactSupportClass = U.compactSupportClass
  calc
    T.compactSupportClass = (T.enlarge K hK Set.subset_union_left).compactSupportClass :=
      (T.compactSupportClass_enlarge K hK Set.subset_union_left).symm
    _ = (U.enlarge K hK Set.subset_union_right).compactSupportClass :=
      congrArg CompactSupportTriple.compactSupportClass heq
    _ = U.compactSupportClass := U.compactSupportClass_enlarge K hK Set.subset_union_right

end AtiyahSinger
