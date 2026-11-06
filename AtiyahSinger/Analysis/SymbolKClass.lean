/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticSymbolTriple

/-!
# The compact-support K class of continuous elliptic cotangent data

Public module ID: M1024.

The class is the support-triple class of the actual original symbol. It depends
only on its off-zero boundary, and uniformly elliptic homotopies preserve it.
The construction makes no assertion that arbitrary K-class equality determines
an analytic index; representability and index descent are additional results.
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

variable [CompactSpace M] [T2Space M]

/-- The compact-support K class of the original off-zero elliptic symbol. -/
def symbolKClass (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) :=
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  (ellipticSymbolTriple a ha hi).compactSupportClass

/-- The class is exactly the constructed raw support-triple class. -/
theorem symbolKClass_eq_triple (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
    symbolKClass a ha hi = (ellipticSymbolTriple a ha hi).compactSupportClass := by
  /- Unfold the class constructor. It uses the actual pulled-back families with the transported
  topologies and their finite-rank certificates, then applies the raw support-class
  construction. -/
  rfl

/-- Off-zero equality gives the same compact-support K class. -/
theorem symbolKClass_congr (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a)
    (b : GlobalSymbolFunction (n := n) E F)
    (hb : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) b) (hj : IsEllipticGlobalSymbol E F b)
    (hab : ∀ x ξ, ξ ≠ 0 → a x ξ = b x ξ) :
    symbolKClass a ha hi = symbolKClass b hb hj := by
  /- The two actual support triples agree by their original boundary action. Apply the support-
  class function to this equality; zero-section values do not contribute. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  exact congrArg CompactSupportTriple.compactSupportClass
    (ellipticSymbolTriple_congr a ha hi b hb hj hab)

/-- The symbol K class is invariant under a jointly continuous elliptic homotopy. -/
theorem symbolKClass_eq_of_family (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a)
    (b : GlobalSymbolFunction (n := n) E F)
    (hb : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) b) (hj : IsEllipticGlobalSymbol E F b)
    (H : unitInterval → GlobalSymbolFunction (n := n) E F)
    (hH : IsContinuousOffZeroSymbolFamily (r := r) (q := q) H)
    (hI : ∀ t, IsEllipticGlobalSymbol E F (H t)) (h0 : H 0 = a) (h1 : H 1 = b) :
    symbolKClass a ha hi = symbolKClass b hb hj := by
  /- First obtain the homotopy of original support triples with the zero section as uniform
  compact control. The established support-class homotopy theorem then gives equality. No
  analytic operators are involved. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  exact (ellipticSymbolTriple a ha hi).compactSupportClass_eq_of_homotopic _
    (ellipticSymbolTriple_homotopic a ha hi b hb hj H hH hI h0 h1)

/-- Inverting the elliptic symbol negates its K class. -/
theorem symbolKClass_inverse (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    symbolKClass (r := q) (q := r) (globalSymbolInverse a)
      (IsContinuousOffZeroGlobalSymbol.inverse (r := r) (q := q) ha hi)
      (IsEllipticGlobalSymbol.inverse (r := r) (q := q) hi) = -symbolKClass a ha hi := by
  /- The inverse symbol gives the inverse raw triple, with source and target exchanged. Apply
  the support-class inverse formula and its compatibility with resizing. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  change (ellipticSymbolTriple (globalSymbolInverse a) _ _).compactSupportClass =
    -(ellipticSymbolTriple a ha hi).compactSupportClass
  rw [ellipticSymbolTriple_inverse]
  exact (ellipticSymbolTriple a ha hi).compactSupportClass_inverse

/-- A global extension of the exterior isomorphism makes the class vanish. -/
theorem symbolKClass_eq_zero_of_extension (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    (∃ e : Iso ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F),
      e.restrict cotangentZeroSetᶜ = ellipticSymbolBoundary a ha hi) →
    symbolKClass a ha hi = 0 := by
  /- A displayed global extension identifies the original boundary germ with the germ of a
  globally invertible triple after enlarging its empty control to the zero section. The
  latter class is zero. This condition is sufficient; stable extension, not necessarily
  unstabilized extension, characterizes all zero classes. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  rintro ⟨e, he⟩
  let b := CompactSupportTriple.ofIso e
  have hb : b.control ⊆ cotangentZeroSet := Set.empty_subset _
  have htriple : ellipticSymbolTriple a ha hi =
      b.enlarge cotangentZeroSet isCompact_cotangentZeroSet hb := by
    change CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _ =
      CompactSupportTriple.mk cotangentZeroSet isCompact_cotangentZeroSet _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro v
    -- Both boundaries are the restriction of this same supplied global isomorphism.
    have hleft := congrArg (fun d ↦ d.linearEquiv z v) he.symm
    have hright := b.enlarge_apply cotangentZeroSet isCompact_cotangentZeroSet
      hb z v
    exact hleft.trans hright.symm
  change (ellipticSymbolTriple a ha hi).compactSupportClass = 0
  rw [htriple, CompactSupportTriple.compactSupportClass_enlarge]
  exact CompactSupportTriple.compactSupportClass_ofIso e

/-- The original class can be computed in any chosen small pullback-bundle models. -/
theorem symbolKClass_eq_model (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
    ∀ G H : FiniteBundle (CotangentTotalSpace (n := n) (M := M)),
      ∀ e : Iso ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E) G.Fiber,
      ∀ f : Iso ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) H.Fiber,
      symbolKClass a ha hi =
        (SupportBundleTriple.ofBoundary G H
          ((ellipticSymbolTriple a ha hi).congr e f)).compactSupportClass := by
  /- Apply the raw support-class model independence theorem to the actual symbol triple. The
  target class uses precisely the conjugated original boundary, so this equality fixes the
  geometric meaning of resizing. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  intro G H e f
  exact (ellipticSymbolTriple a ha hi).compactSupportClass_eq_model G H e f

/-- Zero-dimensional symbols give the source-minus-target bundle class. -/
theorem symbolKClass_of_dim_zero (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r)
    (q := q) a)
    (hi : IsEllipticGlobalSymbol E F a)
    (hn : n = 0) :
    compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback
        ⟨(cotangentProjectionHomeomorphOfDimZero hn).symm,
          (cotangentProjectionHomeomorphOfDimZero hn).symm.continuous⟩
        (cotangentProjectionHomeomorphOfDimZero hn).symm.isProperMap
        (symbolKClass a ha hi)) =
      (modelFiniteBundle (EuclideanSpace ℂ (Fin r)) E).kZeroClass -
        (modelFiniteBundle (EuclideanSpace ℂ (Fin q)) F).kZeroClass := by
  /- In dimension zero the projection is the specified homeomorphism with inverse the zero
  section. Pulling the actual triple back along that inverse gives E and F on the compact
  base, with all of M as control and empty boundary. The compact-support-to-absolute
  comparison therefore returns the source bundle class minus the target class. No equality
  of their ranks is assumed or follows from vacuous ellipticity. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let p := cotangentProjection (n := n) (M := M)
  let i : C(M, CotangentTotalSpace (n := n) (M := M)) :=
    ⟨(cotangentProjectionHomeomorphOfDimZero hn).symm,
      (cotangentProjectionHomeomorphOfDimZero hn).symm.continuous⟩
  have hi' : IsProperMap i := (cotangentProjectionHomeomorphOfDimZero hn).symm.isProperMap
  have hpi : p.comp i = ContinuousMap.id M := by
    ext x
    exact (cotangentProjectionHomeomorphOfDimZero_apply hn _).symm.trans
      ((cotangentProjectionHomeomorphOfDimZero hn).apply_symm_apply x)
  -- Reassociate each actual pullback, then use the original projection inverse identity.
  let eE : Iso ((i : _ → _) *ᵖ ((p : _ → M) *ᵖ E)) E := by
    have e := pullbackCompIso (E := E) p i
    rw [hpi] at e
    exact e.trans pullbackIdIso
  let eF : Iso ((i : _ → _) *ᵖ ((p : _ → M) *ᵖ F)) F := by
    have e := pullbackCompIso (E := F) p i
    rw [hpi] at e
    exact e.trans pullbackIdIso
  let G := modelFiniteBundle (EuclideanSpace ℂ (Fin r)) E
  let H := modelFiniteBundle (EuclideanSpace ℂ (Fin q)) F
  let b := (ellipticSymbolTriple a ha hi).pullback i hi'
  have hmodel := b.compactSupportClass_eq_model G H
    (eE.trans (modelFiniteBundleIso (EuclideanSpace ℂ (Fin r)) E))
    (eF.trans (modelFiniteBundleIso (EuclideanSpace ℂ (Fin q)) F))
  -- Proper naturality and compact-base normalization now refer to those same two models.
  calc
    _ = compactSupportKZeroToAbsolute b.compactSupportClass :=
      congrArg compactSupportKZeroToAbsolute
        ((ellipticSymbolTriple a ha hi).compactSupportClass_pullback i hi').symm
    _ = G.kZeroClass - H.kZeroClass := by
      rw [hmodel]
      exact SupportBundleTriple.compactSupportClass_toAbsolute _

end AtiyahSinger
