/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolKClass
public import AtiyahSinger.Analysis.FullSymbolKClassHomotopy
public import AtiyahSinger.Analysis.NativeAtlasFullEllipticity

/-!
# Transport of the original general full-symbol compact-support class

Public module ID: M2300.

The actual bundle isomorphisms preserve the original exterior maps after enlargement to
one compact control. Their pullbacks therefore identify the genuine full-symbol classes.
The native atlas comparison forgets only continuity certificates of the same linear
maps and retains both original cotangent pullbacks at every frequency.

Sources: SG I.9.26 and III.13 (13.1). The explicit atlas/native comparison is a project
supplement and makes no homogeneous-principal or analytic-index assumption.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F G H : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]
  [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {C : SmoothComplexBundleAtlas (n := n) G}
  {D : SmoothComplexBundleAtlas (n := n) H}

attribute [local instance] isFiniteRank_pullback isFiniteRank_restrict
  t2Space_cotangent locallyCompactSpace_cotangent

/-- The actual boundary square preserves the general full-symbol class across bundle atlases. -/
theorem atlasFullSymbolKClass_eq_of_bundleIso {m : ℝ} (e : Iso E G) (f : Iso F H)
    (a : atlasGlobalSymbolSpace A B m) (b : atlasGlobalSymbolSpace C D m)
    (ha : IsEllipticFullAtlasSymbol A B m a.val)
    (hb : IsEllipticFullAtlasSymbol C D m b.val)
    (hab : ∀ (x : M) (ξ : CotangentFiber (n := n) x) (v : E x),
      f.linearEquiv x (a.val x ξ v) = b.val x ξ (e.linearEquiv x v)) :
    atlasFullSymbolKClass A B a ha = atlasFullSymbolKClass C D b hb := by
  /- Enlarge the two actual triples to the union of their compact controls.
  Pull back the supplied source and target isomorphisms, then use the exact
  boundary square on the original fibers. Conjugation and enlargement preserve
  the class in the original compact-support K group. -/
  let := A.isFiniteRank
  let := B.isFiniteRank
  let := C.isFiniteRank
  let := D.isFiniteRank
  let πM := cotangentProjection (n := n) (M := M)
  let s := atlasFullSymbolTriple A B a ha
  let t := atlasFullSymbolTriple C D b hb
  let K := s.control ∪ t.control
  have hK : IsCompact K := s.isCompact_control.union t.isCompact_control
  let s' := s.enlarge K hK Set.subset_union_left
  let t' := t.enlarge K hK Set.subset_union_right
  have hst : s'.congr (e.pullback πM) (f.pullback πM) = t' := by
    change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    change G z.val.proj at v
    let w : E z.val.proj := (e.linearEquiv z.val.proj).symm v
    let zs : ↥(s.controlᶜ) := ⟨z.val, fun hz ↦ z.property (Set.subset_union_left hz)⟩
    let zt : ↥(t.controlᶜ) := ⟨z.val, fun hz ↦ z.property (Set.subset_union_right hz)⟩
    have hs : s'.boundary.linearEquiv z w = a.val z.val.proj z.val.snd w :=
      (s.enlarge_apply K hK Set.subset_union_left z w).trans
        (atlasFullSymbolTriple_boundary_apply A B a ha zs w)
    have ht : t'.boundary.linearEquiv z v = b.val z.val.proj z.val.snd v :=
      (t.enlarge_apply K hK Set.subset_union_right z v).trans
        (atlasFullSymbolTriple_boundary_apply C D b hb zt v)
    change f.linearEquiv z.val.proj (s'.boundary.linearEquiv z w) =
      t'.boundary.linearEquiv z v
    rw [hs, ht, hab]
    exact congrArg (b.val z.val.proj z.val.snd) ((e.linearEquiv z.val.proj).apply_symm_apply v)
  change s.compactSupportClass = t.compactSupportClass
  calc
    s.compactSupportClass = s'.compactSupportClass :=
      (s.compactSupportClass_enlarge K hK Set.subset_union_left).symm
    _ = (s'.congr (e.pullback πM) (f.pullback πM)).compactSupportClass :=
      (s'.compactSupportClass_congr (e.pullback πM) (f.pullback πM)).symm
    _ = t'.compactSupportClass := congrArg CompactSupportTriple.compactSupportClass hst
    _ = t.compactSupportClass := t.compactSupportClass_enlarge K hK Set.subset_union_right

end AtiyahSinger

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  {F : M → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

attribute [local instance] isFiniteRank_pullback isFiniteRank_restrict
  t2Space_cotangent locallyCompactSpace_cotangent

/-- The native atlas and native full-symbol constructions retain exactly the same K class. -/
theorem atlasFullSymbolKClass_native {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a.val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    atlasFullSymbolKClass
        (nativeSmoothComplexBundleAtlas (n := n) (r := r) E)
        (nativeSmoothComplexBundleAtlas (n := n) (r := q) F) (nativeAtlasGlobalSymbol m a)
        ((isEllipticFullAtlasSymbol_native_iff m a.val).mpr ha) = fullSymbolKClass a ha := by
  /- Use one genuine metric exterior for the original native map on both sides.
  The atlas conversion forgets only the continuous-linear certificate. The two
  raw triples consequently have identical boundary maps on the same fibers. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  let b := nativeAtlasGlobalSymbol m a
  have hb : IsEllipticFullAtlasSymbol A B m b.val :=
    (isEllipticFullAtlasSymbol_native_iff m a.val).mpr ha
  let g : SmoothCotangentMetric (n := n) (M := M) := SmoothCotangentMetric.nonempty.some
  obtain ⟨R, _, hR⟩ := ha.exists_metric_radius g
  let K : Set (CotangentTotalSpace (n := n) (M := M)) := {z | g.length z.proj z.snd ≤ R}
  have hK : IsCompact K := g.isCompact_sublevel R
  have hi : ∀ z : CotangentTotalSpace (n := n) (M := M),
      z ∉ K → (a.val z.proj z.snd).IsInvertible :=
    fun z hz ↦ hR z.proj z.snd (lt_of_not_ge hz)
  have hj : ∀ z : CotangentTotalSpace (n := n) (M := M),
      z ∉ K → Function.Bijective (b.val z.proj z.snd) := fun z hz ↦ (hi z hz).bijective
  change atlasFullSymbolKClass A B b hb = fullSymbolKClass a ha
  rw [atlasFullSymbolKClass_eq_tripleWithControl A B b hb K hK hj,
    fullSymbolKClass_eq_tripleWithControl a ha K hK hi]
  apply congrArg CompactSupportTriple.compactSupportClass
  -- The common-control boundaries have definitionally equal original forward maps.
  change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
  rfl

end AtiyahSinger
