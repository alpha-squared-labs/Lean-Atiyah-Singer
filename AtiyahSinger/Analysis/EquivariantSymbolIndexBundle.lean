/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantBundleIndex
public import AtiyahSinger.Analysis.EquivariantHomogeneousAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantSymbolKClass
public import AtiyahSinger.Analysis.HomogeneousSymbolOperations
public import AtiyahSinger.Analysis.SmoothBundleMapPrincipalSymbol

/-!
# Original bundle isomorphisms preserve equivariant symbol classes and indices

Public module ID: M0591.

The same off-zero square between the original homogeneous symbols and the
original source and target bundle isomorphisms preserves their equivariant
support K classes and their full representation-valued analytic indices.
The K-class assertion uses only continuous equivariant isomorphisms and permits
any real degree; the analytic assertion uses smooth forward maps and degree
zero. Neither assertion requires equality of ranks or unitary isomorphisms.

Sources: SG III.13 (13.1), (13.5), pp.244--245, and ASI I Section 2, pp.494--495,
for the original equivariant symbol triple and its isomorphism relation;
SG III.3 Theorem 3.10, formula (3.10), p.183, for the local leading-symbol
product, Theorem 3.17(iii), p.187, for global PDO composition, and III.9
Definition 9.3 and Proposition 9.4, pp.212--213, for the full equivariant index. The precise
same-symbol comparison across independently normed original bundles is a
project supplement, not a separately numbered theorem in these sources.

The K-class theorem retains the existing original K construction's small-fiber
universe restriction. The analytic theorem allows independent fiber universes
and uses compact Lie-group hypotheses only through the existing canonical
symbol-index construction. Empty bases and dimension zero are allowed. No
index homomorphism on arbitrary equivariant K classes is asserted. The original
K-class compatibility and the analytic-index comparison are both proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

section SymbolClass

variable {n r q r' q' : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  {E' : M → Type}
  [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin r')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r')) E']
  {F' : M → Type}
  [∀ x, NormedAddCommGroup (F' x)] [∀ x, NormedSpace ℂ (F' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q')) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin q')) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q')) F']
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (σE' : letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
    EquivariantStructure G E')
  (σF' : letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
    EquivariantStructure G F')

/-- The original off-zero bundle square preserves the full equivariant symbol K class. -/
theorem equivariantHomogeneousSymbolKClass_eq_of_bundleIso (m : ℝ)
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      Iso E E')
    (f : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      Iso F F')
    (heg : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      e.IsEquivariant σE σE')
    (hfg : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      f.IsEquivariant σF σF')
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (t : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') E' F' m)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hj : IsEllipticGlobalSymbol E' F' t.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
    (ht : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE' σF' g t.val x ξ = t.val x ξ)
    (hst : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → ∀ u : E x,
        f.linearEquiv x (s.val x ξ u) = t.val x ξ (e.linearEquiv x u)) :
    equivariantHomogeneousSymbolKClass IG σE σF m s hi hs =
      equivariantHomogeneousSymbolKClass IG σE' σF' m t hj ht := by
  /- Stage 1: use the original cotangent lift and its projection p. Pull back
  exactly e and f along p. EquivariantStructure.pullback_maps proves that
  these same pullback isomorphisms intertwine the original pulled actions.
  No invariant metric, group compactness or smoothness of e and f is needed.
  Stage 2: both original elliptic triples use zero-section compact control.
  On its complement ellipticSymbolTriple_boundary_apply gives precisely
  the supplied s and t values. The equation hst is therefore the exterior
  commuting square for the exact pulled isomorphisms from Stage 1. The
  zero-section is invariant under the native cotangent lift, so this is an
  actual EquivariantSupportBundleTriple.IsIsomorphic witness with the same
  control, not a square available only after forgetting the actions.
  Stage 3: the isomorphism relation in
  equivariantSupportTripleKZero_generator_relations identifies those exact
  generators. Unfold both equivariantHomogeneousSymbolKClass constructions
  to identify them with the displayed classes. The given ellipticity and
  equivariance certificates describe the same symbols in the boundary
  square; any proof-certificate changes are proof-irrelevant. When n=0
  the exterior square is vacuous but e and f still match the two original
  source and target actions separately. No equality at zero is required. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin r')) E'
  let := modelTopology (EuclideanSpace ℂ (Fin q')) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r')) E'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q')) F'
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  have hequiv :=
    ellipticSymbolTriple_isEquivariant IG σE σF s.val s.property.1.continuous hi hs
  -- Pull back the specified two equivariant isomorphisms, retaining the same zero control.
  apply (equivariantSupportTripleKZero_generator_relations
    (G := G) (X := CotangentTotalSpace (n := n) (M := M))).1
  refine ⟨cotangentZeroSet, isCompact_cotangentZeroSet, hequiv.invariant_control,
    subset_rfl, subset_rfl, e.pullback p, f.pullback p, ?_, ?_, ?_⟩
  · exact (σE.pullback_maps σE' p (fun _ _ ↦ rfl)).2 e heg
  · exact (σF.pullback_maps σF' p (fun _ _ ↦ rfl)).2 f hfg
  · -- The exterior square is the supplied square on the same original fiber vectors.
    intro z v
    simp only [CompactSupportTriple.enlarge, Iso.restrictTo_apply]
    change f.linearEquiv z.val.proj
        ((ellipticSymbolTriple s.val s.property.1.continuous hi).boundary.linearEquiv z v) =
      (ellipticSymbolTriple t.val t.property.1.continuous hj).boundary.linearEquiv z
        (e.linearEquiv z.val.proj v)
    exact (congrArg (f.linearEquiv z.val.proj)
      (ellipticSymbolTriple_boundary_apply s.val s.property.1.continuous hi z v)).trans
        ((hst z.val.proj z.val.snd z.property v).trans
          (ellipticSymbolTriple_boundary_apply t.val t.property.1.continuous hj z _).symm)

end SymbolClass

section AnalyticIndex

variable {n r q r' q' : ℕ} {M : Type*} [TopologicalSpace M]
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
  {E' : M → Type*}
  [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin r')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r')) E']
  {F' : M → Type*}
  [∀ x, NormedAddCommGroup (F' x)] [∀ x, NormedSpace ℂ (F' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q')) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin q')) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q')) F']
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [IsSmoothComplexBundle (n := n) (r := r') E']
  [IsSmoothComplexBundle (n := n) (r := q') F']

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (σE' : letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
    EquivariantStructure G E')
  (σF' : letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
    EquivariantStructure G F')
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  (hσE' : σE'.IsSmooth (n := n) (r := r') IG)
  (hσF' : σF'.IsSmooth (n := n) (r := q') IG)

/-- A smooth original bundle square preserves the canonical full equivariant symbol index. -/
theorem equivariantHomogeneousAnalyticIndex_eq_of_bundleIso
    (e : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      Iso E E')
    (f : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      Iso F F')
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      IsSmoothBundleMap (n := n) (r := r) (q := r') e.toHom.linearMap)
    (hf : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      IsSmoothBundleMap (n := n) (r := q) (q := q') f.toHom.linearMap)
    (heg : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      e.IsEquivariant σE σE')
    (hfg : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      f.IsEquivariant σF σF')
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (t : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') E' F' 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hj : IsEllipticGlobalSymbol E' F' t.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
    (ht : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE' σF' g t.val x ξ = t.val x ξ)
    (hst : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
      letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
      ∀ (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 → ∀ u : E x,
        f.linearEquiv x (s.val x ξ u) = t.val x ξ (e.linearEquiv x u)) :
    equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs =
      equivariantHomogeneousAnalyticIndex IG σE' σF' hσE' hσF' t hj ht := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin r')) E'
  let := modelTopology (EuclideanSpace ℂ (Fin q')) F'
  -- One invariant geometry realizes the original source symbol and its actual transport.
  obtain ⟨μ, hμ, hμInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ
  obtain ⟨h, hInvariant⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, kInvariant⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  obtain ⟨h', hInvariant'⟩ := exists_invariant_smoothHermitianMetric IG σE' hσE'
  obtain ⟨k', kInvariant'⟩ := exists_invariant_smoothHermitianMetric IG σF' hσF'
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q) (E := E) (F := F)
  obtain ⟨R'⟩ := nonempty_quantizationPresentation
    (n := n) (r := r') (q := q') (E := E') (F := F')
  obtain ⟨P, hPg, hPclass⟩ := PseudodifferentialOperator.exists_equivariant_principalSymbol
    (μ := μ) IG σE σF hσE hσF 0
    (globalPrincipalSymbolClass E F 0 (R.regularizedSymbol 0 s.val s.property.1 s.property.2))
    (fun g ↦ (R.equivariant_regularizedSymbol_class_eq_iff
      IG σE σF hσE hσF R 0 s s g).mpr (hs g))
  have hP : P.IsElliptic := ⟨_, hPclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 s.val
      s.property.1 s.property.2).mpr hi⟩
  obtain ⟨Q, hQmap, hQg, hQ, hindex⟩ :=
    PseudodifferentialOperator.exists_equivariant_bundleIso_transport
    IG σE σF σE' σF' hσE hσF hσE' hσF' h k h' k'
    hInvariant kInvariant hInvariant' kInvariant' hμInvariant e f he hf heg hfg P hPg hP
  -- The specified inverse and forward maps have their actual multiplication symbols.
  let A := smoothBundleMapOperator (μ := μ)
    (fun x ↦ (e.linearEquiv x).symm.toLinearMap) (he.symm e.linearEquiv)
  let B := smoothBundleMapOperator (μ := μ) f.toHom.linearMap hf
  obtain ⟨a, ha, hAclass⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ)
    (fun x ↦ (e.linearEquiv x).symm.toLinearMap) (he.symm e.linearEquiv)
  obtain ⟨b, hb, hBclass⟩ :=
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) f.toHom.linearMap hf
  obtain ⟨RA⟩ := nonempty_quantizationPresentation
    (n := n) (r := r') (q := r) (E := E') (F := E)
  obtain ⟨RB⟩ := nonempty_quantizationPresentation
    (n := n) (r := q) (q := q') (E := F) (F := F')
  obtain ⟨RT⟩ := nonempty_quantizationPresentation
    (n := n) (r := r') (q := q) (E := E') (F := F)
  have hu : IsHomogeneousGlobalSymbol E' F 0 (globalSymbolComp s.val a.val) := by
    simpa only [zero_add] using s.property.2.globalSymbolComp a.property.2
  let u : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q) E' F 0 :=
    ⟨globalSymbolComp s.val a.val, s.property.1.globalSymbolComp a.property.1, hu⟩
  let T : PseudodifferentialOperator (n := n) (r := r') (q := q) E' F μ 0 :=
    { toLinearMap := P.toLinearMap.comp A.toLinearMap
      isPseudodifferentialOperator := by
        simpa only [PseudodifferentialOperator.comp, zero_add] using
          (P.comp A).isPseudodifferentialOperator }
  -- First compare the principal class before transporting its exact real order.
  have hu' : IsHomogeneousGlobalSymbol E' F (0 + 0) u.val := by
    simpa only [zero_add] using u.property.2
  have hTraw : (P.comp A).principalSymbol = globalPrincipalSymbolClass E' F (0 + 0)
      (RT.regularizedSymbol (0 + 0) u.val u.property.1 hu') := by
    rw [P.principalSymbol_comp A, hPclass, hAclass RA]
    exact globalPrincipalSymbolComp_regularizedSymbol_eq RA R RT a s
      ⟨u.val, u.property.1, hu'⟩ (fun _ _ _ ↦ rfl)
  have htransferT (l : ℝ) (hl : l = 0)
      (S : PseudodifferentialOperator (n := n) (r := r') (q := q) E' F μ l)
      (hh : IsHomogeneousGlobalSymbol E' F l u.val)
      (hS : S.toLinearMap = T.toLinearMap)
      (hclass : S.principalSymbol = globalPrincipalSymbolClass E' F l
        (RT.regularizedSymbol l u.val u.property.1 hh)) :
      T.principalSymbol = globalPrincipalSymbolClass E' F 0
        (RT.regularizedSymbol 0 u.val u.property.1 u.property.2) := by
    subst l
    exact (T.principalSymbol_eq_of_toLinearMap_eq μ S hS.symm).trans hclass
  have hTclass := htransferT _ (zero_add 0) (P.comp A) hu' rfl hTraw
  -- The supplied square gives the second product on these same fiber vectors.
  have ht' : IsHomogeneousGlobalSymbol E' F' (0 + 0) t.val := by
    simpa only [zero_add] using t.property.2
  have htcomp (x : M) (ξ : CotangentFiber (n := n) x) (hξ : ξ ≠ 0) :
      t.val x ξ = globalSymbolComp b.val u.val x ξ := by
    ext v
    change t.val x ξ v = b.val x ξ (s.val x ξ (a.val x ξ v))
    rw [ha, hb]
    change t.val x ξ v = f.linearEquiv x (s.val x ξ ((e.linearEquiv x).symm v))
    simpa only [LinearEquiv.apply_symm_apply] using
      (hst x ξ hξ ((e.linearEquiv x).symm v)).symm
  have hQraw : (B.comp T).principalSymbol = globalPrincipalSymbolClass E' F' (0 + 0)
      (R'.regularizedSymbol (0 + 0) t.val t.property.1 ht') := by
    rw [B.principalSymbol_comp T, hBclass RB, hTclass]
    exact globalPrincipalSymbolComp_regularizedSymbol_eq RT RB R' u b
      ⟨t.val, t.property.1, ht'⟩ htcomp
  have htransferQ (l : ℝ) (hl : l = 0)
      (S : PseudodifferentialOperator (n := n) (r := r') (q := q') E' F' μ l)
      (hh : IsHomogeneousGlobalSymbol E' F' l t.val)
      (hS : S.toLinearMap = Q.toLinearMap)
      (hclass : S.principalSymbol = globalPrincipalSymbolClass E' F' l
        (R'.regularizedSymbol l t.val t.property.1 hh)) :
      Q.principalSymbol = globalPrincipalSymbolClass E' F' 0
        (R'.regularizedSymbol 0 t.val t.property.1 t.property.2) := by
    subst l
    exact (Q.principalSymbol_eq_of_toLinearMap_eq μ S hS.symm).trans hclass
  have hQclass := htransferQ _ (zero_add 0) (B.comp T) ht' (by
    rw [hQmap]
    rfl) hQraw
  -- Both canonical values are evaluated on exactly the operators in the transport square.
  rw [equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF s hi hs
    μ hμ h k hInvariant kInvariant hμInvariant R P hPg hP hPclass,
    equivariantHomogeneousAnalyticIndex_eq IG σE' σF' hσE' hσF' t hj ht
    μ hμ h' k' hInvariant' kInvariant' hμInvariant R' Q hQg hQ hQclass]
  exact hindex

end AnalyticIndex

end AtiyahSinger
