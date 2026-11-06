/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousSymbol
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Geometry.EquivariantCotangentAction
public import AtiyahSinger.Topology.EquivariantBundlePullback
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import AtiyahSinger.Topology.SupportKZeroComparison

/-!
# Original equivariant K classes of homogeneous elliptic symbols

Public module ID: M0598.

An equivariant elliptic symbol determines a class in the existing original
equivariant support-triple group. The construction retains the actual native
cotangent lift, the original projection pullbacks of both bundles, their
specified pulled actions, and precisely the original elliptic symbol triple.
It does not define this class by forgetting equivariance. Forgetting followed
by the existing compact-support comparison recovers the ordinary homogeneous
symbol class. Equality of regularized homogeneous principal classes preserves
the original equivariant class when the source and target actions are fixed.

Sources: SG III.13 (13.1) and (13.5), pp.244--245, for the symbol triple and
homogeneous leading data; SG III.9, pp.211 and 214, for equivariance; SG I.9.26
for ordinary compact support; and ASI I Section 2, pp.494--495, for the
equivariant compact-support extension.
These are standard constructions and their compatibility, not additional
numbered theorems attributed to SG. General real degrees and independent
source and target ranks are allowed. No compactness of the group, invariant
metric, invariant regularization, or equality at zero is assumed. The
original class and its compatibility are proved below; no analytic-index descent is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent

/-- Original off-zero symbol equivariance makes its exact elliptic triple equivariant. -/
theorem ellipticSymbolTriple_isEquivariant
    (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a)
    (hi : IsEllipticGlobalSymbol E F a)
    (heq : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a x ξ = a x ξ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    let p := cotangentProjection (n := n) (M := M)
    (ellipticSymbolTriple a ha hi).IsEquivariant
      (σ.pullback p (fun _ _ ↦ rfl)) (τ.pullback p (fun _ _ ↦ rfl)) := by
  /- Stage 1: the native cotangent lift is fiberwise invertible and linear.
  It sends zero covectors to zero and nonzero covectors to nonzero, so the
  exact zero-section control of ellipticSymbolTriple is invariant.
  Stage 2: evaluate the supplied conjugation equation at the image of an
  original nonzero cotangent vector. The inverse cotangent lift returns
  that same vector. The original source action and its inverse cancel,
  giving the moving-fiber intertwining equation for the original symbol.
  Stage 3: use ellipticSymbolTriple_boundary_apply to replace both boundary
  evaluations by those same symbol values. The projection is equivariant
  for the native lift, and its pulled actions are precisely sigma and tau
  on each original base fiber. The pullback-composition identifications
  preserve each vector, so the obtained equation is the required boundary
  square. Dependent index transports use only the original action laws.
  Compactness of M supplies compact control; neither group compactness,
  smoothness of the bundle actions, homogeneity, nor values at zero enter.
  When n=0 the exterior is empty and no equality of ranks is required. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  let W := TotalSpace Unit ((p : _ → M) *ᵖ E)
  let : MulAction G W := (σ.pullback p (fun _ _ ↦ rfl)).toMulAction
  let : MulAction G (TotalSpace Unit F) := τ.toMulAction
  let T : W → TotalSpace Unit F :=
    fun w ↦ ⟨w.proj.proj, a w.proj.proj w.proj.snd w.snd⟩
  -- The conjugation formula is equality in the original target total space.
  let transport : ∀ {x y : M}, x = y → F x →L[ℂ] F y := fun {x y} h ↦ by
    subst y
    exact ContinuousLinearMap.id ℂ (F x)
  have htransport {x y : M} (h : x = y) (v : F x) :
      (⟨y, transport h v⟩ : TotalSpace Unit F) = ⟨x, v⟩ := by
    subst y
    rfl
  have hconj (g : G) (w : W) :
      (⟨w.proj.proj,
        equivariantGlobalSymbolLinearMap IG σ τ g a w.proj.proj w.proj.snd w.snd⟩ :
          TotalSpace Unit F) = g • T (g⁻¹ • w) := by
    change (⟨w.proj.proj,
      transport (smul_inv_smul g w.proj.proj)
      (τ.linearMap g (g⁻¹ • w.proj.proj)
        (a (g⁻¹ • w.proj.proj)
          ((cotangentDiffeomorphMap
            (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm)
              w.proj).snd (σ.linearMap g⁻¹ w.proj.proj w.snd)))⟩ :
        TotalSpace Unit F) = _
    rw [htransport]
    erw [Diffeomorph.smul_symm]
    rfl
  have hintertwine (g : G) (w : W) (hw : w.proj.snd ≠ 0) :
      T (g • w) = g • T w := by
    have hfixed := congrArg (fun L : E w.proj.proj →L[ℂ] F w.proj.proj ↦
      (⟨w.proj.proj, L w.snd⟩ : TotalSpace Unit F))
        (heq g⁻¹ w.proj.proj w.proj.snd hw)
    have h := congrArg (fun z : TotalSpace Unit F ↦ g • z)
      ((hconj g⁻¹ w).symm.trans hfixed)
    simpa only [inv_inv, smul_inv_smul] using h
  -- Linearity preserves zero; applying the inverse group element reflects it.
  have hzero (g : G) (z : CotangentTotalSpace (n := n) (M := M))
      (hz : z.snd = 0) : (g • z).snd = 0 := by
    ext v
    change z.snd _ = 0
    rw [hz]
    rfl
  have hcontrol (g : G) (z : CotangentTotalSpace (n := n) (M := M)) :
      g • z ∈ cotangentZeroSet ↔ z ∈ cotangentZeroSet := by
    change (g • z).snd = 0 ↔ z.snd = 0
    constructor
    · intro hz
      have h : g⁻¹ • (g • z) ∈ cotangentZeroSet := hzero g⁻¹ (g • z) hz
      rw [inv_smul_smul] at h
      exact h
    · exact hzero g z
  refine ⟨hcontrol, ?_⟩
  -- The original boundary and pulled actions act on exactly these original vectors.
  intro g z v
  let gz : PuncturedCotangentBundle (n := n) (M := M) :=
    ⟨g • z.val, fun hz ↦ z.property ((hcontrol g z.val).mp hz)⟩
  have hvalue : a (g • z.val.proj) (g • z.val).snd (σ.linearMap g z.val.proj v) =
      τ.linearMap g z.val.proj (a z.val.proj z.val.snd v) :=
    TotalSpace.mk_injective (g • z.val.proj)
      (hintertwine g (⟨z.val, v⟩ : W) z.property)
  exact (ellipticSymbolTriple_boundary_apply a ha hi gz _).trans
    (hvalue.trans (congrArg (τ.linearMap g z.val.proj)
      (ellipticSymbolTriple_boundary_apply a ha hi z v).symm))

/-- The original equivariant support class of the displayed homogeneous elliptic symbol. -/
def equivariantHomogeneousSymbolKClass (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val)
    (heq : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ = a.val x ξ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) := by
  letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
  letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
  letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  exact (EquivariantSupportBundleTriple.ofBoundary
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E))
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F))
    (ellipticSymbolTriple a.val a.property.1.continuous hi)
    (σ.pullback p (fun _ _ ↦ rfl)) (τ.pullback p (fun _ _ ↦ rfl))
    (ellipticSymbolTriple_isEquivariant IG σ τ a.val a.property.1.continuous hi heq)).kZeroClass

variable [T2Space M]

/-- Forgetting the original actions recovers the existing ordinary homogeneous symbol class. -/
theorem equivariantHomogeneousSymbolKClass_forget (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val)
    (heq : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ = a.val x ξ) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    supportTripleKZeroToCompactSupport
        (equivariantSupportTripleKZeroForget
          (equivariantHomogeneousSymbolKClass IG σ τ m a hi heq)) =
      homogeneousSymbolKClass m a hi := by
  /- Stage 1: the equivariant forgetful map sends the original packaged
  generator to its same ordinary support-triple generator. It changes
  neither the pulled bundles nor the boundary or zero-section control.
  Stage 2: supportTripleKZeroToCompactSupport sends this generator to its
  compact-window class. The existing ofBoundary comparison identifies
  that class with the raw elliptic triple's compactSupportClass.
  Stage 3: unfold the existing homogeneousSymbolKClass and symbolKClass.
  Their raw triple is exactly the preceding triple, with the same original
  function, continuity witness and ellipticity witness. Hausdorffness is
  used for the ordinary compact-support comparison on the cotangent LCH
  space; no injectivity of forgetting or equivariant descent is claimed. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  -- Both functorial maps evaluate on the same original equivariant generator.
  simp only [equivariantHomogeneousSymbolKClass, equivariantSupportTripleKZeroForget_apply,
    supportTripleKZeroToCompactSupport_apply]
  exact (compactSupportTriple_compactSupportClass_ofBoundary
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ E))
    (FiniteBundle.ofFamily ((p : _ → M) *ᵖ F))
    (ellipticSymbolTriple a.val a.property.1.continuous hi)).symm

variable [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hE hF in
/-- Equal displayed homogeneous principal classes give the same original equivariant K class. -/
theorem equivariantHomogeneousSymbolKClass_eq_of_principalClass_eq (m : ℝ)
    (R S : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hi : IsEllipticGlobalSymbol E F a.val) (hj : IsEllipticGlobalSymbol E F b.val)
    (heqa : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g a.val x ξ = a.val x ξ)
    (heqb : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σ τ g b.val x ξ = b.val x ξ)
    (hab : globalPrincipalSymbolClass E F m
        (R.regularizedSymbol m a.val a.property.1 a.property.2) =
      globalPrincipalSymbolClass E F m
        (S.regularizedSymbol m b.val b.property.1 b.property.2)) :
    equivariantHomogeneousSymbolKClass IG σ τ m a hi heqa =
      equivariantHomogeneousSymbolKClass IG σ τ m b hj heqb := by
  /- Stage 1: use regularizedSymbol_class_eq_iff for the independently
  supplied presentations R and S at the same real degree m. Their actual
  principal-quotient equality determines the two original Hom maps at
  every nonzero cotangent vector, without controlling their values at zero.
  Stage 2: ellipticSymbolTriple_congr identifies the exact raw triples.
  Both constructions retain the same original source and target actions
  and their same native projection pullbacks. After the raw equality,
  only proof-irrelevant equivariance certificates differ, so the packaged
  original equivariant generators and their K classes coincide.
  Smoothness of the bundles enters principal-class uniqueness. Smoothness
  of their actions and group compactness are unnecessary: this is direct
  equality of the original equivariant generators, not an inference from
  equality after forgetting equivariance. Independent r,q and n=0 remain
  valid, as do empty M and independently chosen regularizations. -/
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let p := cotangentProjection (n := n) (M := M)
  -- Homogeneous recovery identifies the two original raw exterior triples.
  have hoff := (R.regularizedSymbol_class_eq_iff S m a.val b.val
    a.property.1 a.property.2 b.property.1 b.property.2).mp hab
  have htriple := ellipticSymbolTriple_congr a.val a.property.1.continuous hi
    b.val b.property.1.continuous hj hoff
  -- The source and target actions stay fixed; only proof certificates then differ.
  simp only [equivariantHomogeneousSymbolKClass]
  congr 2

end AtiyahSinger
