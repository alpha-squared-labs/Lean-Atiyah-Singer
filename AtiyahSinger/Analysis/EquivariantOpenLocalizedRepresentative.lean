/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantLocalizedRelativeRepresentative
public import AtiyahSinger.Geometry.EquivariantRelativeCutoffs
public import AtiyahSinger.Geometry.InvariantCotangentMetric

/-!
# Relative symbols localized in an actual invariant open image

Public module ID: M0545.

Starting with the original ambient controlled triple, this construction chooses
all compact windows, smooth invariant cutoffs and the invariant cotangent metric.
The resulting native finite-representation symbol has its exact zero-section
control inside the specified open image and retains the original restricted class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
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
-- Choose all localization data before applying the complete controlled homotopy chain.
/-- An original triple supported in an invariant open image has a smooth relative representative. -/
theorem exists_equivariant_localized_relative_symbol_of_open
    (hn : 0 < n) (U : Opens M)
    (hUi : ∀ (g : G) (x : M), g • x ∈ U ↔ x ∈ U) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
    ∀ (A : EquivariantSupportBundleTriple G (CotangentTotalSpace (n := n) (M := M)))
      (φ : C(X, CotangentTotalSpace (n := n) (M := M))) (hφ : IsOpenEmbedding φ)
      (hφg : ∀ (g : G) (x : X), φ (g • x) = g • φ x)
      (hArange : A.1.datum.control ⊆ Set.range φ)
      (_hφrange : ∀ z : CotangentTotalSpace (n := n) (M := M),
        z ∈ Set.range φ ↔ z.proj ∈ U),
      ∃ K : Set M, IsCompact K ∧ K ⊆ U ∧
        (∀ (g : G) (x : M), g • x ∈ K ↔ x ∈ K) ∧
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
                (∀ x ∉ K, Function.Bijective (c.linearMap x)) ∧
                ∃ s : homogeneousGlobalSymbolSpace (n := n) (r := ρ.dimension) (q := F.rank)
                    T F.Fiber 0,
                  IsEllipticGlobalSymbol T F.Fiber s.val ∧
                  (∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
                    equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σT σF g s.val x ξ = s.val x ξ) ∧
                  (∀ x ∉ K, ∀ ξ v, s.val x ξ v = c.linearMap x v) ∧
                  ∃ b : CompactSupportTriple
                      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ T)
                      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
                    b.control = cotangentZeroSection '' K ∧
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
  intro A φ hφ hφg hArange hφrange
  let Y := CotangentTotalSpace (n := n) (M := M)
  let p : C(Y, M) := cotangentProjection
  let D : Set M := p '' A.1.datum.control
  have hD : IsCompact D := A.1.datum.isCompact_control.image p.continuous
  have hDi (g : G) (x : M) : g • x ∈ D ↔ x ∈ D := by
    constructor
    · rintro ⟨z, hz, hpz⟩
      refine ⟨g⁻¹ • z, (A.2.isEquivariant.invariant_control g⁻¹ z).mpr hz, ?_⟩
      change g⁻¹ • p z = x
      rw [hpz, inv_smul_smul]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨g • z, (A.2.isEquivariant.invariant_control g z).mpr hz, rfl⟩
  have hDU : D ⊆ U := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hφrange z).mp (hArange hz)
  -- The compact windows and full closed cutoff supports all stay inside this same open image.
  obtain ⟨K₀, K₁, K₂, hK₀, hK₁, hK₂, hD₀, h01, h12, hK₂U,
      hK₀i, hK₁i, hK₂i, ψ, χ₀, χ₁, hψzero, hψone, hψinv,
      hχ₀support, hχ₁support, hχ₀one, hχ₁one, hχ₁bounds, hχ₀inv, hχ₁inv⟩ :=
    exists_invariant_relative_cutoffs (VG := VG) (n := n) D hD hDi U hDU hUi
  have hA₀ (z : Y) (hz : z ∈ A.1.datum.control) : z.proj ∈ K₀ :=
    hD₀ ⟨z, hz, rfl⟩
  have hK₂range (z : Y) (hz : z.proj ∈ K₂) : z ∈ Set.range φ :=
    (hφrange z).mpr (hK₂U hz)
  -- Averaging the original cotangent pairing provides the metric for the same radial deformation.
  obtain ⟨g₀, hg₀⟩ :=
    exists_invariant_smoothCotangentMetric (G := G) (n := n) (M := M) 𝓘(ℝ, VG)
  have hlength (g : G) (x : M) (ξ : CotangentFiber (n := n) x) :
      g₀.length (g • x)
        (cotangentDiffeomorphMap
          (Diffeomorph.smul (M := M) 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
          ⟨x, ξ⟩).snd = g₀.length x ξ := congrArg Real.sqrt (hg₀ g x ξ ξ)
  refine ⟨K₂, hK₂, hK₂U, hK₂i, ?_⟩
  exact exists_equivariant_localized_relative_symbol hn g₀ hlength
    K₀ K₁ K₂ hK₀ hK₁ hK₂ h01 h12 hK₀i hK₁i hK₂i
    χ₀ χ₁ χ₀.property χ₁.property hχ₀support hχ₁support hχ₀one hχ₁one
    hχ₁bounds hχ₀inv hχ₁inv A φ hφ hφg hArange hA₀ hK₂range
    ⟨ψ, ψ.property.continuous⟩ (fun z hz ↦ hψzero z.proj ⟨z, hz, rfl⟩) hψone hψinv

end AtiyahSinger
