/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.RelativeHomogeneousSmoothing
public import AtiyahSinger.Topology.BundleIsoHomotopyGluing
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Relative homogeneous smoothing preserves the actual compact-support class

Public module ID: M0921.

The punctured cotangent homotopy extends across the exterior zero covectors,
where every time slice equals the prescribed smooth bundle map. Gluing the
whole cylinder supplies one compact zero-section control for the original
and smoothed triples. This is the class-preserving relative refinement of
the homogeneous representative in SG III.13 Lemma 13.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle IsManifold TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  isFiniteRank_pullback

include hM hT hSC hE hF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- Canonical reassociation compares the same three dependent pullbacks throughout the cylinder.
/-- Relative smoothing retains the original raw triple class, including exterior zero fibers. -/
theorem exists_smooth_homogeneous_triple_relative
    (h : SmoothCotangentMetric (n := n) (M := M))
    (K L : Set M) (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L)
    (c : ∀ x, E x →L[ℂ] F x)
    (hc : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (c x).toLinearMap))
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F))
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.control = cotangentZeroSection '' K)
    (hhom : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ), 0 < t →
        ∀ (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ)
          (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ),
          a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
            a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩)
    (hac : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (x : M), x ∉ K → ∀ (ξ : CotangentFiber (n := n) x)
        (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ) (v : E x),
        a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v = c x v) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
    ∃ s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0,
      IsEllipticGlobalSymbol E F s.val ∧
      (∀ (x : M), x ∉ L → ∀ ξ : CotangentFiber (n := n) x, s.val x ξ = c x) ∧
      ∃ b : CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F),
        b.control = cotangentZeroSection '' L ∧
        (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
          (v : E z.val.proj), b.boundary.linearEquiv z v = s.val z.val.proj z.val.snd v) ∧
        b.compactSupportClass = a.compactSupportClass := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : IsFiniteRank E := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let : IsFiniteRank F := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let CT := CotangentTotalSpace (n := n) (M := M)
  let p : C(CT, M) := cotangentProjection (n := n) (M := M)
  let E' := (p : CT → M) *ᵖ E
  let F' := (p : CT → M) *ᵖ F
  let : TopologicalSpace (TotalSpace Unit E') := inferInstance
  let : TopologicalSpace (TotalSpace Unit F') := inferInstance
  let : IsFiniteRank E' := isFiniteRank_pullback p
  let : IsFiniteRank F' := isFiniteRank_pullback p
  have hsub : a.control ⊆ cotangentZeroSet := by
    rw [ha]
    rintro _ ⟨x, _, rfl⟩
    rfl
  let α : RelativeTriple E' F' cotangentZeroSetᶜ :=
    a.boundary.restrictTo (Set.compl_subset_compl.mpr hsub)
  have hα (z : (cotangentZeroSetᶜ : Set CT)) (v : E z.val.proj) :
      α.linearEquiv z v =
        a.boundary.linearEquiv ⟨z.val, fun hz ↦ z.property (hsub hz)⟩ v :=
    Iso.restrictTo_apply (E := E') (F := F') a.boundary
      (Set.compl_subset_compl.mpr hsub) z v
  -- Smooth the punctured boundary while retaining the entire fixed exterior homotopy.
  obtain ⟨s, hs, hsc, β, hβ, H, hH⟩ :=
    exists_smooth_homogeneous_boundary_relative h K L hK hKL c hc α
      (by
        intro x ξ hξ t ht v
        exact (hα ⟨⟨x, t • ξ⟩, smul_ne_zero ht.ne' hξ⟩ v).trans
          ((congrArg (fun (e : E x ≃ₗ[ℂ] F x) ↦ e v) (hhom x ξ t ht _ _)).trans
            (hα ⟨⟨x, ξ⟩, hξ⟩ v).symm))
      (by
        intro x hx ξ hξ v
        exact (hα ⟨⟨x, ξ⟩, hξ⟩ v).trans (hac x hx ξ _ v))
  let Z : Set CT := cotangentZeroSection '' L
  have hZ : IsCompact Z := hL.image continuous_cotangentZeroSection
  have haZ : a.control ⊆ Z := by
    rw [ha]
    exact Set.image_mono (hKL.trans interior_subset)
  let X : Opens CT := ⟨Zᶜ, hZ.isClosed.isOpen_compl⟩
  let W : Opens CT := ⟨cotangentZeroSetᶜ, isClosed_cotangentZeroSet.isOpen_compl⟩
  let iX : C(X, CT) := ContinuousMap.subtypeVal (X : Set CT)
  let iW : C(W, CT) := ContinuousMap.subtypeVal (W : Set CT)
  let EX := (iX : X → CT) *ᵖ E'
  let FX := (iX : X → CT) *ᵖ F'
  let : TopologicalSpace (TotalSpace Unit EX) := inferInstance
  let : TopologicalSpace (TotalSpace Unit FX) := inferInstance
  let : IsFiniteRank EX := isFiniteRank_pullback iX
  let : IsFiniteRank FX := isFiniteRank_pullback iX
  let aL := a.enlarge Z hZ haZ
  have heqzero (z : CT) (hz : z.snd = 0) : cotangentZeroSection z.proj = z := by
    cases z with
    | mk x ξ =>
      change ξ = 0 at hz
      simp only [cotangentZeroSection, hz]
  let U : Opens X := ⟨Subtype.val ⁻¹' (W : Set CT),
    W.isOpen.preimage continuous_subtype_val⟩
  let V : Opens X := ⟨(p.comp iX) ⁻¹' Lᶜ,
    hL.isClosed.isOpen_compl.preimage (p.comp iX).continuous⟩
  have hcover : (U : Set X) ∪ (V : Set X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z.val.snd = 0
    · right
      intro hzL
      apply z.property
      refine ⟨z.val.proj, hzL, ?_⟩
      exact heqzero z.val hz
    · exact Or.inl hz
  let iU : C(U, X) := ContinuousMap.subtypeVal (U : Set X)
  let j : C(U, W) := ⟨fun z ↦ ⟨z.val.val, z.property⟩,
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  -- Both restriction routes preserve the same original fiber vector.
  let eE : Iso ((iU : U → X) *ᵖ EX)
      ((j : U → W) *ᵖ ((iW : W → CT) *ᵖ E')) :=
    (pullbackCompIso (E := E') iX iU).trans (pullbackCompIso (E := E') iW j).symm
  let eF : Iso ((iU : U → X) *ᵖ FX)
      ((j : U → W) *ᵖ ((iW : W → CT) *ᵖ F')) :=
    (pullbackCompIso (E := F') iX iU).trans (pullbackCompIso (E := F') iW j).symm
  have heE (z : U) (v : E z.val.val.proj) : eE.linearEquiv z v = v := by
    change ((pullbackCompIso (E := E') iW j).linearEquiv z).symm
      ((pullbackCompIso (E := E') iX iU).linearEquiv z v) = v
    apply ((pullbackCompIso (E := E') iW j).linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have heF (z : U) (v : F z.val.val.proj) : eF.symm.linearEquiv z v = v := by
    change ((pullbackCompIso (E := F') iX iU).linearEquiv z).symm
      ((pullbackCompIso (E := F') iW j).linearEquiv z v) = v
    apply ((pullbackCompIso (E := F') iX iU).linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  let : TopologicalSpace (TotalSpace Unit (Restrict EX (U : Set X))) := inferInstance
  let : TopologicalSpace (TotalSpace Unit (Restrict FX (U : Set X))) := inferInstance
  obtain ⟨J, hJ⟩ := H.exists_pullback j
  let πU : C(unitInterval × U, U) := ⟨Prod.snd, continuous_snd⟩
  let aU : RelativeTriple EX FX (U : Set X) :=
    eE.trans ((Iso.pullback j α).trans eF.symm)
  let bU : RelativeTriple EX FX (U : Set X) :=
    eE.trans ((Iso.pullback j β).trans eF.symm)
  let J' : IsoHomotopy aU bU :=
    { iso := (eE.pullback πU).trans (J.iso.trans (eF.symm.pullback πU))
      map_zero z v := congrArg (eF.symm.linearEquiv z) (J.map_zero z (eE.linearEquiv z v))
      map_one z v := congrArg (eF.symm.linearEquiv z) (J.map_one z (eE.linearEquiv z v)) }
  have hJ' (t : unitInterval) (z : U) (v : E z.val.val.proj) :
      J'.iso.linearEquiv (t, z) v = H.iso.linearEquiv (t, j z) v := by
    change eF.symm.linearEquiv z (J.iso.linearEquiv (t, z) (eE.linearEquiv z v)) = _
    rw [heE, heF]
    exact hJ t z v
  have haU (z : U) (v : E z.val.val.proj) :
      aU.linearEquiv z v = aL.boundary.linearEquiv z.val v := by
    change eF.symm.linearEquiv z (α.linearEquiv (j z) (eE.linearEquiv z v)) = _
    rw [heE, heF]
    exact (hα (j z) v).trans (a.enlarge_apply Z hZ haZ z.val v).symm
  have hfix (t : unitInterval) (z : U) (hz : z.val ∈ V)
      (v : E z.val.val.proj) :
      J'.iso.linearEquiv (t, z) v = aL.boundary.linearEquiv z.val v := by
    have hzK : z.val.val.proj ∉ K := fun hk ↦ hz (interior_subset (hKL hk))
    exact (hJ' t z v).trans ((hH t (j z) hz v).trans
      ((a.enlarge_apply Z hZ haZ z.val v).trans (hac _ hzK _ _ v)).symm)
  -- Extend every time slice across exterior zero covectors, with one compact control.
  obtain ⟨bL, G, hGU, hGV⟩ := IsoHomotopy.exists_extension_of_fixed_overlap
    (E := EX) (F := FX) U V hcover aL.boundary J' haU hfix
  let b : CompactSupportTriple E' F' :=
    { control := Z
      isCompact_control := hZ
      boundary := bL }
  refine ⟨s, hs, hsc, b, rfl, ?_, ?_⟩
  · intro z v
    by_cases hz : z.val.snd = 0
    · have hzV : (z : X) ∈ V := by
        intro hzL
        apply z.property
        refine ⟨z.val.proj, hzL, ?_⟩
        exact heqzero z.val hz
      have hzK : z.val.proj ∉ K := fun hk ↦ hzV (interior_subset (hKL hk))
      exact (G.map_one z v).symm.trans ((hGV 1 ⟨z, hzV⟩ v).trans
        ((a.enlarge_apply Z hZ haZ z v).trans ((hac _ hzK _ _ v).trans
          (congrArg (fun f ↦ f v) (hsc z.val.proj hzV z.val.snd)).symm)))
    · let zU : U := ⟨z, hz⟩
      exact (G.map_one z v).symm.trans ((hGU 1 zU v).trans
        ((hJ' 1 zU v).trans ((H.map_one (j zU) v).trans (hβ (j zU) v))))
  · have hbb : (b.enlarge Z hZ (Set.Subset.refl _)).boundary = bL := by
      apply Iso.ext
      intro z
      apply LinearEquiv.ext
      intro v
      exact b.enlarge_apply Z hZ (Set.Subset.refl _) z v
    have hab : a.Homotopic b := by
      refine ⟨Z, hZ, haZ, Set.Subset.refl _, ?_⟩
      rw [hbb]
      exact ⟨G⟩
    exact (a.compactSupportClass_eq_of_homotopic b hab).symm

end AtiyahSinger.ComplexBundle
