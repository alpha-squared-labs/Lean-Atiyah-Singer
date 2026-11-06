/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantControlledRelativeSymbol
public import AtiyahSinger.Geometry.EquivariantSmoothRelativeStabilization
public import AtiyahSinger.Topology.EquivariantOpenStabilization
public import AtiyahSinger.Topology.EquivariantRelativeCotangentRepresentative

/-!
# A smooth relative representative retaining the common-open class

Public module ID: M0536.

The actual zero-section bundle comparisons, two controlled radial homotopies,
the same finite-representation stabilization and controlled smoothing are
composed on the common open source. Every homotopy control stays in the
specified compact window. The resulting source carries the original finite
representation through its literal native Euclidean bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [MulAction G X] [ContinuousSMul G X]

attribute [local instance] isFiniteRank_pullback t2Space_cotangent
  locallyCompactSpace_cotangent sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- Compose the same four controlled deformations with their native bundle comparisons.
/-- Relative smoothing and stabilization retain the original class on the specified open source. -/
theorem exists_equivariant_localized_relative_symbol
    (hn : 0 < n)
    (g₀ : SmoothCotangentMetric (n := n) (M := M))
    (hg₀ : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      g₀.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
          ⟨x, ξ⟩).snd = g₀.length x ξ)
    (K₀ K₁ K₂ : Set M) (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁)
    (hK₂ : IsCompact K₂) (h01 : K₀ ⊆ K₁) (h12 : K₁ ⊆ interior K₂)
    (hK₀i : ∀ (g : G) (x : M), g • x ∈ K₀ ↔ x ∈ K₀)
    (hK₁i : ∀ (g : G) (x : M), g • x ∈ K₁ ↔ x ∈ K₁)
    (hK₂i : ∀ (g : G) (x : M), g • x ∈ K₂ ↔ x ∈ K₂)
    (χ₀ χ₁ : M → ℝ)
    (hχ₀ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ₀)
    (hχ₁ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℝ) ∞ χ₁)
    (hχ₀support : tsupport χ₀ ⊆ K₀ᶜ) (hχ₁support : tsupport χ₁ ⊆ K₁ᶜ)
    (hχ₀one : ∀ x ∉ K₁, χ₀ x = 1) (hχ₁one : ∀ x ∉ K₂, χ₁ x = 1)
    (hχ₁bounds : ∀ x, 0 ≤ χ₁ x ∧ χ₁ x ≤ 1)
    (hχ₀inv : ∀ (g : G) (x : M), χ₀ (g • x) = χ₀ x)
    (hχ₁inv : ∀ (g : G) (x : M), χ₁ (g • x) = χ₁ x) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ (A : EquivariantSupportBundleTriple G (CotangentTotalSpace (n := n) (M := M)))
      (φ : C(X, CotangentTotalSpace (n := n) (M := M))) (hφ : IsOpenEmbedding φ)
      (hφg : ∀ (g : G) (x : X), φ (g • x) = g • φ x)
      (hArange : A.1.datum.control ⊆ Set.range φ)
      (_hA₀ : ∀ z ∈ A.1.datum.control, z.proj ∈ K₀)
      (_hK₂range : ∀ z : CotangentTotalSpace (n := n) (M := M),
        z.proj ∈ K₂ → z ∈ Set.range φ)
      (ψ : C(M, ℝ)) (_hψzero : ∀ z ∈ A.1.datum.control, ψ z.proj = 0)
      (_hψone : ∀ x ∉ K₀, ψ x = 1)
      (_hψinv : ∀ (g : G) (x : M), ψ (g • x) = ψ x),
      ∃ (ρ : FiniteContinuousRepresentation G)
        (hT : IsSmoothComplexBundle (n := n) (r := ρ.dimension)
          (Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension)))),
        letI := hT
        let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
        letI := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) T
        letI := isFiniteRank_model (EuclideanSpace ℂ (Fin ρ.dimension)) T
        ∃ σT : EquivariantStructure G T,
          σT.IsSmooth (n := n) (r := ρ.dimension) 𝓘(ℝ, VG) ∧
          (∀ (g : G) (x : M) (v : T x), σT.linearMap g x v =
            (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
              (ρ.representation g ((EuclideanSpace.equiv (Fin ρ.dimension) ℂ) v))) ∧
          ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = ρ.dimension ∧
            letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
            letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
            ∃ σF : EquivariantStructure G F.Fiber,
              σF.IsSmooth (n := n) (r := F.rank) 𝓘(ℝ, VG) ∧
              ∃ c : Hom T F.Fiber,
                IsSmoothBundleMap (n := n) (r := ρ.dimension) (q := F.rank) c.linearMap ∧
                c.IsEquivariant σT σF ∧
                (∀ x ∉ K₂, Function.Bijective (c.linearMap x)) ∧
                ∃ s : homogeneousGlobalSymbolSpace (n := n) (r := ρ.dimension) (q := F.rank)
                    T F.Fiber 0,
                  IsEllipticGlobalSymbol T F.Fiber s.val ∧
                  (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
                    equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σT σF g s.val x ξ = s.val x ξ) ∧
                  (∀ x ∉ K₂, ∀ ξ v, s.val x ξ v = c.linearMap x v) ∧
                  ∃ b : CompactSupportTriple
                      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ T)
                      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
                    b.control = cotangentZeroSection '' K₂ ∧
                    (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
                      (v : T z.val.proj),
                      b.boundary.linearEquiv z v = s.val z.val.proj z.val.snd v) ∧
                    ∃ hb : b.IsEquivariant
                        (σT.pullback cotangentProjection (fun _ _ ↦ rfl))
                        (σF.pullback cotangentProjection (fun _ _ ↦ rfl)),
                      ∃ hbrange : b.control ⊆ Set.range φ,
                        ((EquivariantSupportBundleTriple.ofBoundary
                          ((FiniteBundle.ofFamily T).pullback cotangentProjection)
                          ((FiniteBundle.ofFamily F.Fiber).pullback cotangentProjection) b
                          (σT.pullback cotangentProjection (fun _ _ ↦ rfl))
                          (σF.pullback cotangentProjection (fun _ _ ↦ rfl)) hb).openRestrict
                          φ hφ hφg hbrange).kZeroClass =
                            (A.openRestrict φ hφ hφg hArange).kZeroClass := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  intro A φ hφ hφg hArange hA₀ hK₂range ψ hψzero hψone hψinv
  let Y := CotangentTotalSpace (n := n) (M := M)
  let p : C(Y, M) := cotangentProjection
  have h02 : K₀ ⊆ K₂ := h01.trans (h12.trans interior_subset)
  have hK₀range (z : Y) (hz : z.proj ∈ K₀) : z ∈ Set.range φ := hK₂range z (h02 hz)
  -- The actual original bundle contraction and radial deformations retain both cylinders.
  obtain ⟨E, F, ρE, ρF, _τ, a₀, ha₀, ha₀control, _ha₀hom, _ha₀ext, _ha₀class,
      e, j, he, hj, d, hd, H₀, H₁, hH₀, hH₁⟩ :=
    exists_equivariant_relative_homogeneous_cotangent_representative 𝓘(ℝ, VG) A
      K₀ hK₀ hK₀i hA₀ ψ hψzero hψone hψinv
  let τE := ρE.pullback p (fun _ _ ↦ rfl)
  let τF := ρF.pullback p (fun _ _ ↦ rfl)
  let a' := A.1.datum.congr e j
  have ha' : a'.IsEquivariant τE τF := by
    refine ⟨A.2.isEquivariant.invariant_control, ?_⟩
    intro g z v
    let gz : (A.1.datum.controlᶜ : Set Y) :=
      ⟨g • z.val, fun hz ↦ z.property ((A.2.isEquivariant.invariant_control g z.val).mp hz)⟩
    have heinv : (e.linearEquiv (g • z.val)).symm (τE.linearMap g z.val v) =
        A.2.sourceAction.linearMap g z.val ((e.linearEquiv z.val).symm v) := by
      apply (e.linearEquiv (g • z.val)).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (he g z.val ((e.linearEquiv z.val).symm v) |>.trans
        (congrArg (τE.linearMap g z.val) ((e.linearEquiv z.val).apply_symm_apply v))).symm
    change j.linearEquiv (g • z.val)
        (A.1.datum.boundary.linearEquiv gz
          ((e.linearEquiv (g • z.val)).symm (τE.linearMap g z.val v))) =
      τF.linearMap g z.val
        (j.linearEquiv z.val (A.1.datum.boundary.linearEquiv ⟨z.val, z.property⟩
          ((e.linearEquiv z.val).symm v)))
    rw [heinv, A.2.isEquivariant.boundary_intertwines]
    exact hj g z.val _
  let A' := EquivariantSupportBundleTriple.ofBoundary (E.pullback p) (F.pullback p)
    a' τE τF ha'
  have hflat : (A.openRestrict φ hφ hφg hArange).kZeroClass =
      (A'.openRestrict φ hφ hφg hArange).kZeroClass := by
    apply EquivariantSupportBundleTriple.kZeroClass_openRestrict_eq_of_boundary A A'
      φ hφ hφg A.1.datum.control A.1.datum.isCompact_control
      A.2.isEquivariant.invariant_control (Set.Subset.refl _) (Set.Subset.refl _)
      hArange e j he hj
    intro z hz v
    change j.linearEquiv z (A.1.datum.boundary.linearEquiv ⟨z, hz⟩ v) =
      j.linearEquiv z (A.1.datum.boundary.linearEquiv ⟨z, hz⟩
        ((e.linearEquiv z).symm (e.linearEquiv z v)))
    rw [LinearEquiv.symm_apply_apply]
  have hH₀range : H₀.control ⊆ Set.range φ := fun z hz ↦ hK₀range z (hH₀ z hz)
  have hH₁range : H₁.control ⊆ Set.range φ := fun z hz ↦ hK₀range z (hH₁ z hz)
  have hclass₀ := H₀.kZeroClass_openRestrict_eq (E.pullback p) (F.pullback p)
    τE τF a' d ha' hd φ hφ hφg hH₀range
  have hclass₁ := H₁.kZeroClass_openRestrict_eq (E.pullback p) (F.pullback p)
    τE τF d a₀ hd ha₀ φ hφ hφg hH₁range
  -- One actual complement and finite representation produce the native smooth bundles.
  obtain ⟨C, σC, ρ, hT, σT, hσT, hσTvalue, F', hF', σF, hσF,
      eT, eF, heT, heF, a₁, ha₁, ha₁control, ha₁boundary, _ha₁class⟩ :=
    exists_smooth_relative_equivariant_cotangent_stabilization hn E F ρE ρF K₀
      a₀ ha₀control ha₀
  let := hT
  let T := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))
  let := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension)) T
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin ρ.dimension)) T
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let τT := σT.pullback p (fun _ _ ↦ rfl)
  let τF' := σF.pullback p (fun _ _ ↦ rfl)
  let A₀ := EquivariantSupportBundleTriple.ofBoundary (E.pullback p) (F.pullback p)
    a₀ τE τF ha₀
  let A₁ := EquivariantSupportBundleTriple.ofBoundary
    ((FiniteBundle.ofFamily T).pullback p) ((FiniteBundle.ofFamily F'.Fiber).pullback p)
    a₁ τT τF' ha₁
  let eT' := (sumPullbackIso p E C).symm.trans (eT.pullback p)
  let eF' := (sumPullbackIso p F C).symm.trans (eF.pullback p)
  have heT' : eT'.IsEquivariant (τE.sum (σC.pullback p (fun _ _ ↦ rfl))) τT := by
    intro g z v
    exact heT g z.proj v
  have heF' : eF'.IsEquivariant (τF.sum (σC.pullback p (fun _ _ ↦ rfl))) τF' := by
    intro g z v
    exact heF g z.proj v
  have ha₀range : a₀.control ⊆ Set.range φ := H₁.right_control.trans hH₁range
  have hstab := EquivariantSupportBundleTriple.kZeroClass_openRestrict_eq_of_stabilization
    A₀ A₁ (C.pullback p) (σC.pullback p (fun _ _ ↦ rfl)) eT' eF' heT' heF'
    ha₁control (fun z h₀ h₁ v ↦ ha₁boundary z h₀ h₁ v) φ hφ hφg ha₀range
  -- Controlled smoothing keeps the entire final cylinder inside K₂, including exterior zero fibers.
  obtain ⟨c, hc, hcg, hcbij, s, hs, hsg, hsext, b, hbcontrol, hbboundary, hb,
      H₂, hH₂⟩ :=
    a₁.exists_equivariant_smooth_relative_symbol 𝓘(ℝ, VG) σT σF hσT hσF g₀ hg₀
      K₀ K₁ K₂ hK₀ hK₁ hK₂ h01 h12 hK₁i hK₂i χ₀ χ₁ hχ₀ hχ₁
      hχ₀support hχ₁support hχ₀one hχ₁one hχ₁bounds hχ₀inv hχ₁inv
      (ha₁control.trans ha₀control) ha₁
  have hH₂range : H₂.control ⊆ Set.range φ := fun z hz ↦ hK₂range z (hH₂ z hz)
  have hbrange : b.control ⊆ Set.range φ := H₂.right_control.trans hH₂range
  have hclass₂ := H₂.kZeroClass_openRestrict_eq
    ((FiniteBundle.ofFamily T).pullback p) ((FiniteBundle.ofFamily F'.Fiber).pullback p)
    τT τF' a₁ b ha₁ hb φ hφ hφg hH₂range
  refine ⟨ρ, hT, σT, hσT, hσTvalue, F', hF', σF, hσF, c, hc, hcg,
    (fun x hx ↦ hcbij x (fun h ↦ hx ((h12.trans interior_subset) h))),
    s, hs, hsg, hsext, b, hbcontrol, hbboundary, hb, hbrange, ?_⟩
  exact hclass₂.symm.trans (hstab.trans (hclass₁.symm.trans (hclass₀.symm.trans hflat.symm)))

end AtiyahSinger
