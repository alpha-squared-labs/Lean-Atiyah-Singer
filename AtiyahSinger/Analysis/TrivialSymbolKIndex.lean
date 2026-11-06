/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSymbolKIndexInvariance
public import AtiyahSinger.Analysis.HomogeneousSymbolBundleIso
public import AtiyahSinger.Analysis.TrivialSymbolIndex
public import AtiyahSinger.Geometry.SmallSmoothBundleModel

/-!
# Ordinary stable classes and the index for a subsingleton group

Public module ID: M1038.

The original ordinary compact-support class determines the homogeneous
index when the acting group has one element. The proof moves arbitrary
original fiber universes into actual small smooth models, applies the
existing equivariant stable-germ theorem, and returns along the same smooth
isomorphisms. No new stable relation or choice of index on all K classes is
assumed. This is the ordinary specialization of the SG III.13 descent.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

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

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [hDim : FiniteDimensional ℝ VG]
  [Group G] [Subsingleton G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [LieGroup 𝓘(ℝ, VG) ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (σE' : letI := modelTopology (EuclideanSpace ℂ (Fin r')) E'
    EquivariantStructure G E')
  (σF' : letI := modelTopology (EuclideanSpace ℂ (Fin q')) F'
    EquivariantStructure G F')
  (hσE : σE.IsSmooth (n := n) (r := r) 𝓘(ℝ, VG))
  (hσF : σF.IsSmooth (n := n) (r := q) 𝓘(ℝ, VG))
  (hσE' : σE'.IsSmooth (n := n) (r := r') 𝓘(ℝ, VG))
  (hσF' : σF'.IsSmooth (n := n) (r := q') 𝓘(ℝ, VG))

include hDim in
/-- For a subsingleton group the ordinary class determines the full homogeneous index. -/
theorem equivariantHomogeneousAnalyticIndex_eq_of_homogeneousSymbolKClass_eq
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (t : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') E' F' 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hj : IsEllipticGlobalSymbol E' F' t.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE σF g s.val x ξ = s.val x ξ)
    (ht : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σE' σF' g t.val x ξ = t.val x ξ)
    (hK : homogeneousSymbolKClass 0 s hi = homogeneousSymbolKClass 0 t hj) :
    equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG) σE σF hσE hσF s hi hs =
      equivariantHomogeneousAnalyticIndex 𝓘(ℝ, VG) σE' σF' hσE' hσF' t hj ht := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin r')) E'
  let := modelTopology (EuclideanSpace ℂ (Fin q')) F'
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let := hμ
  -- Preserve all four original smooth bundles through actual small smooth comparisons.
  obtain ⟨C, _, e, he⟩ := exists_small_smooth_bundle_model (n := n) (r := r) E
  let := modelTopology (EuclideanSpace ℂ (Fin C.rank)) C.Fiber
  let σC := EquivariantStructure.ofSubsingleton (G := G) C.Fiber
  have hσC := σC.isSmooth_of_subsingleton (n := n) (r := C.rank) 𝓘(ℝ, VG)
  obtain ⟨D, _, f, hf⟩ := exists_small_smooth_bundle_model (n := n) (r := q) F
  let := modelTopology (EuclideanSpace ℂ (Fin D.rank)) D.Fiber
  let σD := EquivariantStructure.ofSubsingleton (G := G) D.Fiber
  have hσD := σD.isSmooth_of_subsingleton (n := n) (r := D.rank) 𝓘(ℝ, VG)
  obtain ⟨C', _, e', he'⟩ := exists_small_smooth_bundle_model (n := n) (r := r') E'
  let := modelTopology (EuclideanSpace ℂ (Fin C'.rank)) C'.Fiber
  let σC' := EquivariantStructure.ofSubsingleton (G := G) C'.Fiber
  have hσC' := σC'.isSmooth_of_subsingleton (n := n) (r := C'.rank) 𝓘(ℝ, VG)
  obtain ⟨D', _, f', hf'⟩ := exists_small_smooth_bundle_model (n := n) (r := q') F'
  let := modelTopology (EuclideanSpace ℂ (Fin D'.rank)) D'.Fiber
  let σD' := EquivariantStructure.ofSubsingleton (G := G) D'.Fiber
  have hσD' := σD'.isSmooth_of_subsingleton (n := n) (r := D'.rank) 𝓘(ℝ, VG)
  obtain ⟨S, hSi, hS⟩ := exists_homogeneousSymbol_of_bundleIso μ e f
    (he.symm e.linearEquiv) hf s hi
  obtain ⟨T, hTi, hT⟩ := exists_homogeneousSymbol_of_bundleIso μ e' f'
    (he'.symm e'.linearEquiv) hf' t hj
  have hSg (g : G) (x : M) (ξ : CotangentFiber (n := n) x) (_ : ξ ≠ 0) :
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σC σD g S.val x ξ = S.val x ξ :=
    congrFun (congrFun (equivariantGlobalSymbolLinearMap_eq_of_subsingleton
      𝓘(ℝ, VG) σC σD hσC hσD S.val g) x) ξ
  have hTg (g : G) (x : M) (ξ : CotangentFiber (n := n) x) (_ : ξ ≠ 0) :
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, VG) σC' σD' g T.val x ξ = T.val x ξ :=
    congrFun (congrFun (equivariantGlobalSymbolLinearMap_eq_of_subsingleton
      𝓘(ℝ, VG) σC' σD' hσC' hσD' T.val g) x) ξ
  -- The same original bundle squares preserve both the full index and the ordinary K class.
  have hindexS := equivariantHomogeneousAnalyticIndex_eq_of_bundleIso 𝓘(ℝ, VG)
    σE σF σC σD hσE hσF hσC hσD e f he hf
    (e.toHom.isEquivariant_of_subsingleton σE σC)
    (f.toHom.isEquivariant_of_subsingleton σF σD) s S hi hSi hs hSg
    (fun x ξ _ u ↦ hS x ξ u)
  have hindexT := equivariantHomogeneousAnalyticIndex_eq_of_bundleIso 𝓘(ℝ, VG)
    σE' σF' σC' σD' hσE' hσF' hσC' hσD' e' f' he' hf'
    (e'.toHom.isEquivariant_of_subsingleton σE' σC')
    (f'.toHom.isEquivariant_of_subsingleton σF' σD') t T hj hTi ht hTg
    (fun x ξ _ u ↦ hT x ξ u)
  have hsmallK : homogeneousSymbolKClass 0 S hSi = homogeneousSymbolKClass 0 T hTi :=
    (homogeneousSymbolKClass_eq_of_bundleIso 0 e f s S hi hSi
      (fun x ξ _ u ↦ hS x ξ u)).symm.trans (hK.trans
        (homogeneousSymbolKClass_eq_of_bundleIso 0 e' f' t T hj hTi
          (fun x ξ _ u ↦ hT x ξ u)))
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := t2Space_cotangent (n := n) (M := M)
  let := locallyCompactSpace_cotangent (n := n) (M := M)
  have hsmallEq : equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σC σD 0 S hSi hSg =
      equivariantHomogeneousSymbolKClass 𝓘(ℝ, VG) σC' σD' 0 T hTi hTg := by
    -- Forgetting a one-element action is injective on the actual support-triple presentation.
    apply equivariantSupportTripleKZeroForget_injective_of_subsingleton
    apply supportTripleKZeroToCompactSupport_injective
    rw [equivariantHomogeneousSymbolKClass_forget,
      equivariantHomogeneousSymbolKClass_forget]
    exact hsmallK
  exact hindexS.trans
    ((equivariantHomogeneousAnalyticIndex_eq_of_equivariantSymbolKClass_eq
      σC σD σC' σD' hσC hσD hσC' hσD' S T hSi hTi hSg hTg hsmallEq).trans hindexT.symm)

end AtiyahSinger
