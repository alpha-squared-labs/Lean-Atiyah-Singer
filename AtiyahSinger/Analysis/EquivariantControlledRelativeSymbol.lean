/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantCotangentExteriorSmoothing
public import AtiyahSinger.Analysis.EquivariantRelativeHomogeneousTripleSmoothing
public import AtiyahSinger.Analysis.EquivariantSymbolCovariance
public import AtiyahSinger.Geometry.EquivariantControlledExteriorExtension
public import AtiyahSinger.Geometry.EquivariantRelativeCotangentRadial
public import AtiyahSinger.Topology.EquivariantCotangentBaseFlattening
public import AtiyahSinger.Topology.EquivariantHomotopyControl

/-!
# Relative smooth symbols with a prescribed common compact window

Public module ID: M0492.

One original equivariant cotangent boundary is smoothed, flattened at base
infinity, normalized radially, and smoothed homogeneously on the same bundles.
The specified nested compact windows and invariant cutoffs control every
homotopy. The final multiplier is invertible off the middle window, while the
symbol equals it off the last window. The combined actual homotopy can thus
be restricted through any common open image containing that last window.

This assembles the relative representative construction of SG III.13.3--13.4
with the original equivariant support model. No equality of analytic indices,
properness of an open inclusion, or finite CW model is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle IsManifold TopologicalSpace
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  {E F : M → Type}
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

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [hDim : FiniteDimensional ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [hGC : CompactSpace G] [hGT : T2Space G]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hDim hM hT hSC hC hE hF hG hGC hGT hAction hσE hσF

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2400000 in
-- Keep four original dependent cylinders and their two native pullback bundle models together.
/-- Smooth a relative cotangent class without letting any homotopy leave its prescribed window. -/
theorem CompactSupportTriple.exists_equivariant_smooth_relative_symbol
    (g₀ : SmoothCotangentMetric (n := n) (M := M))
    (hg₀ : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g₀.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
          ⟨x, ξ⟩).snd = g₀.length x ξ)
    (K₀ K₁ K₂ : Set M) (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hK₂ : IsCompact K₂) (h01 : K₀ ⊆ K₁) (h12 : K₁ ⊆ interior K₂)
    (hK₁i : ∀ (g : G) (x : M), g • x ∈ K₁ ↔ x ∈ K₁)
    (hK₂i : ∀ (g : G) (x : M), g • x ∈ K₂ ↔ x ∈ K₂)
    (χ₀ χ₁ : M → ℝ)
    (hχ₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ₀)
    (hχ₁ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ₁)
    (hχ₀support : tsupport χ₀ ⊆ K₀ᶜ) (hχ₁support : tsupport χ₁ ⊆ K₁ᶜ)
    (hχ₀one : ∀ x ∉ K₁, χ₀ x = 1) (hχ₁one : ∀ x ∉ K₂, χ₁ x = 1)
    (hχ₁bounds : ∀ x, 0 ≤ χ₁ x ∧ χ₁ x ≤ 1)
    (hχ₀inv : ∀ (g : G) (x : M), χ₀ (g • x) = χ₀ x)
    (hχ₁inv : ∀ (g : G) (x : M), χ₁ (g • x) = χ₁ x)
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      CompactSupportTriple
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
        ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F))
    (hControl : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      a.control = cotangentZeroSection '' K₀)
    (ha : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
      letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
      letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
        ContMDiffSMul.continuousSMul (I := IG)
          (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
      a.IsEquivariant (σE.pullback cotangentProjection (fun _ _ ↦ rfl))
        (σF.pullback cotangentProjection (fun _ _ ↦ rfl))) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := IG)
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∃ c : Hom E F,
      IsSmoothBundleMap (n := n) (r := r) (q := q) c.linearMap ∧
      c.IsEquivariant σE σF ∧
      (∀ x ∉ K₁, Function.Bijective (c.linearMap x)) ∧
      ∃ s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0,
        IsEllipticGlobalSymbol E F s.val ∧
        (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
          equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ) ∧
        (∀ x ∉ K₂, ∀ ξ v, s.val x ξ v = c.linearMap x v) ∧
        ∃ b : CompactSupportTriple
            ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
            ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F),
          b.control = cotangentZeroSection '' K₂ ∧
          (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
            (v : E z.val.proj), b.boundary.linearEquiv z v = s.val z.val.proj z.val.snd v) ∧
          b.IsEquivariant (σE.pullback cotangentProjection (fun _ _ ↦ rfl))
            (σF.pullback cotangentProjection (fun _ _ ↦ rfl)) ∧
          ∃ H : CompactSupportTriple.EquivariantHomotopy
              (σE.pullback cotangentProjection (fun _ _ ↦ rfl))
              (σF.pullback cotangentProjection (fun _ _ ↦ rfl)) a b,
            ∀ z ∈ H.control, z.proj ∈ K₂ := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let : IsFiniteRank E := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let : IsFiniteRank F := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := IG)
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let CT := CotangentTotalSpace (n := n) (M := M)
  let πV := cotangentProjection (n := n) (M := M)
  let τE := σE.pullback πV (fun _ _ ↦ rfl)
  let τF := σF.pullback πV (fun _ _ ↦ rfl)
  have h02 : K₀ ⊆ K₂ := h01.trans (h12.trans interior_subset)
  have hproj (z : CT) (hz : z ∈ a.control) : z.proj ∈ K₀ := by
    rw [hControl] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hx
  -- Smooth the boundary with its original control before taking exterior zero-fiber values.
  obtain ⟨a₀, ha₀control, ha₀, ⟨H₀, hH₀⟩, τ, hτsmooth, hτzero⟩ :=
    a.exists_equivariant_smooth_exterior_cotangent_boundary IG σE σF hσE hσF
      K₀ hK₀ hControl ha
  have ha₀proj (z : CT) (hz : z ∈ a₀.control) : z.proj ∈ K₀ :=
    hproj z (ha₀control ▸ hz)
  have hK₀i (g : G) (x : M) : g • x ∈ K₀ ↔ x ∈ K₀ := by
    have hz (y : M) : (cotangentZeroSection y : CT) ∈ a.control ↔ y ∈ K₀ := by
      rw [hControl]
      constructor
      · rintro ⟨z, hz, he⟩
        have hzy : z = y := congrArg (fun z : CT ↦ z.proj) he
        exact hzy ▸ hz
      · intro hy
        exact ⟨y, hy, rfl⟩
    rw [← hz (g • x), ← hz x]
    exact ha.invariant_control g (cotangentZeroSection x)
  let W : Opens M := ⟨K₀ᶜ, hK₀.isClosed.isOpen_compl⟩
  have hWi (g : G) (x : M) : g • x ∈ W ↔ x ∈ W :=
    not_congr (hK₀i g x)
  let τL (x : W) : E x.val →L[ℂ] F x.val :=
    (show E x.val →ₗ[ℂ] F x.val from (τ.linearEquiv x).toLinearMap).toContinuousLinearMap
  have hτeq (g : G) (x : W) (v : E x.val) :
      τL ⟨g • x.val, (hWi g x.val).mpr x.property⟩ (σE.linearMap g x.val v) =
        σF.linearMap g x.val (τL x v) := by
    have hx : cotangentZeroSection x.val ∈ a₀.controlᶜ :=
      fun hz ↦ x.property (ha₀proj _ hz)
    have hgx : cotangentZeroSection (g • x.val) ∈ a₀.controlᶜ :=
      fun hz ↦ x.property ((hK₀i g x.val).mp (ha₀proj _ hz))
    change τ.linearEquiv ⟨g • x.val, (hWi g x.val).mpr x.property⟩
      (σE.linearMap g x.val v) = σF.linearMap g x.val (τ.linearEquiv x v)
    rw [hτzero _ hgx, hτzero x hx]
    exact ha₀.boundary_intertwines g ⟨cotangentZeroSection x.val, hx⟩ v
  -- The supplied cutoff extends this same smooth exterior map without enlarging K₁.
  obtain ⟨c, hc, hcg, hcτ, _hc0⟩ :=
    exists_smooth_equivariant_extension_of_exterior_with_cutoff σE σF W hWi τL
      hτsmooth hτeq χ₀ hχ₀ hχ₀support hχ₀inv
  have hcExterior (x : M) (hx : x ∉ K₁) (v : E x) :
      c.linearMap x v = τ.linearEquiv ⟨x, fun h ↦ hx (h01 h)⟩ v := by
    have h := hcτ ⟨x, fun h ↦ hx (h01 h)⟩ v
    change c.linearMap x v = (χ₀ x : ℂ) •
      τ.linearEquiv ⟨x, fun h ↦ hx (h01 h)⟩ v at h
    simpa only [hχ₀one x hx, Complex.ofReal_one, one_smul] using h
  have hcBijective (x : M) (hx : x ∉ K₁) : Function.Bijective (c.linearMap x) := by
    have heq : (c.linearMap x : E x → F x) =
        τ.linearEquiv ⟨x, fun h ↦ hx (h01 h)⟩ := funext (hcExterior x hx)
    rw [heq]
    exact (τ.linearEquiv ⟨x, fun h ↦ hx (h01 h)⟩).bijective
  -- Flatten outside K₁; every intermediate control is still the original zero-section control.
  have hχ₀zero (z : CT) (hz : z ∈ a₀.control) : χ₀ z.proj = 0 := by
    by_contra hne
    exact hχ₀support (subset_tsupport χ₀ hne) (ha₀proj z hz)
  obtain ⟨a₁, ha₁, ha₁control, ha₁ext, H₁, hH₁⟩ :=
    exists_equivariant_cotangent_base_flattening IG (FiniteBundle.ofFamily E)
      (FiniteBundle.ofFamily F) σE σF a₀ ha₀ K₁
      (fun z hz ↦ h01 (ha₀proj z hz)) ⟨χ₀, hχ₀.continuous⟩ hχ₀zero hχ₀one hχ₀inv
  let τ₁ : RelativeTriple E F K₁ᶜ := τ.restrictTo (Set.compl_subset_compl.mpr h01)
  have ha₁τ (z : CT) (hz : z.proj ∉ K₁) (hz' : z ∈ a₁.controlᶜ) :
      a₁.boundary.linearEquiv ⟨z, hz'⟩ = τ₁.linearEquiv ⟨z.proj, hz⟩ := by
    apply LinearEquiv.ext
    intro v
    have hzero : cotangentZeroSection z.proj ∈ a₀.controlᶜ :=
      fun h ↦ hz (h01 (ha₀proj (cotangentZeroSection z.proj) h))
    exact (congrArg (fun L ↦ L v) (ha₁ext z.proj hz z.snd hz')).trans
      ((congrArg (fun L ↦ L v) (hτzero ⟨z.proj, fun h ↦ hz (h01 h)⟩ hzero)).symm.trans
        (Iso.restrictTo_apply τ (Set.compl_subset_compl.mpr h01) ⟨z.proj, hz⟩ v).symm)
  -- Normalize only the same real fibers, keeping their exterior isomorphism fixed.
  obtain ⟨a₂, ha₂, ha₂control, ha₂hom, ha₂ext, H₂, hH₂⟩ :=
    exists_equivariant_relative_radial_cotangent_representative IG
      (FiniteBundle.ofFamily E) (FiniteBundle.ofFamily F) σE σF a₁ ha₁ K₁ hK₁ hK₁i
      (fun z hz ↦ h01 (ha₀proj z (ha₁control ▸ hz))) τ₁ ha₁τ
  let cL (x : M) : E x →L[ℂ] F x := (c.linearMap x).toContinuousLinearMap
  have ha₂c (x : M) (hx : x ∉ K₁) (ξ : CotangentFiber (n := n) x)
      (hξ : (⟨x, ξ⟩ : CT) ∈ a₂.controlᶜ) (v : E x) :
      a₂.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v = cL x v := by
    exact (congrArg (fun L ↦ L v) (ha₂ext ⟨x, ξ⟩ hx hξ)).trans
      ((Iso.restrictTo_apply τ (Set.compl_subset_compl.mpr h01) ⟨x, hx⟩ v).trans
        (hcExterior x hx v).symm)
  obtain ⟨s, hs, hsext, b, hbcontrol, hbs, hb, H₃, hH₃⟩ :=
    exists_equivariant_smooth_homogeneous_triple_relative IG σE σF hσE hσF
      g₀ hg₀ K₁ K₂ hK₁ hK₂ h12 hK₂i cL hc a₂ ha₂control ha₂hom ha₂c ha₂
      χ₁ hχ₁ hχ₁support hχ₁one hχ₁bounds hχ₁inv
  -- The actual boundary square gives fixedness of the same symbol at every nonzero covector.
  have hsg : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ := by
    apply (equivariantGlobalSymbolLinearMap_eq_iff IG σE σF s.val).mpr
    intro g x ξ hξ v
    have hz : (⟨x, ξ⟩ : CT) ∈ b.controlᶜ := by
      intro h
      rw [hbcontrol] at h
      obtain ⟨y, _, he⟩ := h
      have hy : y = x := congrArg (fun z : CT ↦ z.proj) he
      subst y
      exact hξ (TotalSpace.mk_injective x he).symm
    let z : (b.controlᶜ : Set CT) := ⟨⟨x, ξ⟩, hz⟩
    let gz : (b.controlᶜ : Set CT) :=
      ⟨g • z.val, fun h ↦ hz ((hb.invariant_control g z.val).mp h)⟩
    exact (hbs gz (σE.linearMap g x v)).symm.trans
      ((hb.boundary_intertwines g z v).trans (congrArg (σF.linearMap g x) (hbs z v)))
  -- Compose actual cylinders with their union controls, retaining containment in K₂.
  obtain ⟨H01, hH01⟩ := H₀.exists_trans_control ha₀ H₁
  obtain ⟨H012, hH012⟩ := H01.exists_trans_control ha₁ H₂
  obtain ⟨H, hH⟩ := H012.exists_trans_control ha₂ H₃
  refine ⟨c, hc, hcg, hcBijective, s, hs, hsg, ?_, b, hbcontrol, hbs, hb, H, ?_⟩
  · intro x hx ξ v
    exact congrArg (fun A ↦ A v) (hsext x hx ξ)
  · intro z hz
    rw [hH, hH012, hH01] at hz
    rcases hz with ((hz | hz) | hz) | hz
    · exact h02 (hproj z (hH₀ ▸ hz))
    · exact h02 (ha₀proj z (hH₁ ▸ hz))
    · exact (h12.trans interior_subset) (hH₂ z hz)
    · rw [hH₃] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact hx

end AtiyahSinger.ComplexBundle
