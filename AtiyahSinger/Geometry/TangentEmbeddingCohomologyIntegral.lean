/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentDoubleTubeDerivative
public import AtiyahSinger.Topology.CompactSupportOpenHomeomorph
public import AtiyahSinger.Topology.ComplexificationNativeOrientation
public import AtiyahSinger.Topology.HomologicalOrientationPath
public import AtiyahSinger.Topology.SupportedComplexCohomologyThom
public import AtiyahSinger.Topology.TangentEmbeddingPushforward
public import AtiyahSinger.Topology.ThomGysinComparison

/-!
# The original tangent tube preserves the normalized complex Thom integral

Public module ID: M1478.

The specified complexification, normalized tangent-normal splitting and whole
normal tube give the original open embedding into the target tangent space.
Its cohomological pushforward preserves integration with the canonical tangent
orientations and the supplied complex Thom orientation.

The proof uses interleaved native charts on the fixed complexification topology,
with the supplied Hermitian fiber norms. Their frames have positive complex
orientation. At fiber zero the derivative of the actual composite tube is
positive in the same coordinates; local-homology excision compares the exact
integral generators. Agreement extends along each original fiber. The existing
Thom-integral and open-extension identities then compare the actual maps.

The source and target dimensions are explicit. The dimension inequality also
covers empty manifolds, where immersion alone cannot establish it. Rank zero,
zero-dimensional bases, and noncompact tangent spaces are retained. No orientation
of either base, smoothness of the Hermitian metric, or substitute normal norm is
assumed. Changing native atlas data repackages the same fiber classes; the
original Thom inverse remains definitionally identical after this repackaging.

Source: the standard oriented tubular-neighborhood/Thom integration comparison,
with the interleaved tangent convention of Lawson--Michelsohn, Spin Geometry,
III.12--13 and Atiyah--Singer III. The actual chart and determinant comparisons
supply the project-specific translation to its original Thom maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem interleaved_native_charts {r : ℕ} {B B' X : Type}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup B'] [NormedSpace ℝ B'] (a : B ≃L[ℝ] B')
    [TopologicalSpace X] [ChartedSpace B X]
    (E : X → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
    (h : letI := ComplexBundle.complexificationTopology (EuclideanSpace ℝ (Fin r)) E
      ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (hr : ∀ x : X, Module.finrank ℂ (ℂ ⊗[ℝ] E x) = r) :
    let V := EuclideanSpace ℝ (Fin r)
    let C := fun x ↦ ℂ ⊗[ℝ] E x
    letI := ComplexBundle.complexificationTopology V E
    letI := ComplexBundle.isFiniteRank_complexification V E
    letI : ∀ x, NormedAddCommGroup (C x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (C x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (C x) := h.realFiberInnerProductSpace
    let W := EuclideanSpace ℝ (Fin (2 * r))
    letI := ComplexBundle.nativeModelTopology C W
    let H := (ComplexBundle.nativeModelTotalHomeomorph C W).trans
      (ComplexBundle.complexificationDoubleTotalHomeomorph V E)
    let cD : TotalSpace (V × V) (E ×ᵇ E) →
        OpenPartialHomeomorph (TotalSpace (V × V) (E ×ᵇ E)) (ModelProd B (V × V)) :=
      chartAt (ModelProd B (V × V))
    letI := linearModelChartedSpace a X
    ∃ b : FiberBundle W C, ∃ v : (letI := b; VectorBundle ℝ W C),
      letI := b
      letI := v
      (∀ x, ((EuclideanSpace.basisFun (Fin (2 * r)) ℝ).toBasis.map
        (VectorBundle.continuousLinearEquivAt ℝ W C x).symm.toLinearEquiv).orientation =
          h.complexRealOrientation r hr x) ∧
      ∀ z : TotalSpace W C,
        (∀ w, chartAt (ModelProd B' W) z w =
          (a.prodCongr (tangentModelCoordinateEquiv r)) (cD (H z) (H w))) ∧
        ∀ p, H ((chartAt (ModelProd B' W) z).symm p) =
          (cD (H z)).symm ((a.prodCongr (tangentModelCoordinateEquiv r)).symm p) := by
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let C := fun x ↦ ℂ ⊗[ℝ] E x
  let := ComplexBundle.complexificationTopology V E
  let := ComplexBundle.isFiniteRank_complexification V E
  let : ∀ x, NormedAddCommGroup (C x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (C x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (C x) := h.realFiberInnerProductSpace
  let W := EuclideanSpace ℝ (Fin (2 * r))
  let := ComplexBundle.nativeModelTopology C W
  let H := (ComplexBundle.nativeModelTotalHomeomorph C W).trans
    (ComplexBundle.complexificationDoubleTotalHomeomorph V E)
  let cB : X → OpenPartialHomeomorph X B := chartAt B
  let cD : TotalSpace (V × V) (E ×ᵇ E) →
      OpenPartialHomeomorph (TotalSpace (V × V) (E ×ᵇ E)) (ModelProd B (V × V)) :=
    chartAt (ModelProd B (V × V))
  obtain ⟨b, v, hb⟩ := exists_interleaved_complexificationNativeFiberBundle E h
  let := linearModelChartedSpace a X
  refine ⟨b, v, ?_⟩
  let := b
  let := v
  constructor
  · intro x
    let e := VectorBundle.continuousLinearEquivAt ℝ V E x
    let t := trivializationAt W C x
    let q := VectorBundle.continuousLinearEquivAt ℝ W C x
    let L := (complexificationReIm (E x)).trans
      ((e.toLinearEquiv.prodCongr e.toLinearEquiv).trans
        (tangentModelCoordinateEquiv r).toLinearEquiv)
    have hq : q.toLinearEquiv = L := by
      apply DFunLike.ext
      intro w
      change (t ⟨x, w⟩).2 = _
      have ht := hb x
      change t = _ at ht
      rw [ht]
      change tangentModelCoordinateEquiv r
        (((trivializationAt V E x).prod (trivializationAt V E x))
          ⟨x, complexificationReIm (E x) w⟩).2 = _
      rw [Trivialization.prod_apply' ℝ
        (mem_baseSet_trivializationAt V E x) (mem_baseSet_trivializationAt V E x)]
      rfl
    change ((EuclideanSpace.basisFun (Fin (2 * r)) ℝ).toBasis.map
      q.symm.toLinearEquiv).orientation = _
    have hqs : q.symm.toLinearEquiv = L.symm := congrArg LinearEquiv.symm hq
    rw [hqs, complexification_interleaved_basis e.toLinearEquiv]
    exact h.complexRealOrientation_basis r hr x
      (((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.map e.symm.toLinearEquiv).baseChange ℂ)
  intro z
  let t := trivializationAt W C z.proj
  let e := trivializationAt V E z.proj
  have ht := hb z.proj
  change t = _ at ht
  have hcs : chartAt (ModelProd B' W) z =
      t.toOpenPartialHomeomorph.trans
        (((cB z.proj).trans a.toHomeomorph.toOpenPartialHomeomorph).prod
          (OpenPartialHomeomorph.refl W)) := by
    rw [FiberBundle.chartedSpace_chartAt]
    rfl
  have hcd : cD (H z) =
      (e.prod e).toOpenPartialHomeomorph.trans
        ((cB z.proj).prod (OpenPartialHomeomorph.refl (V × V))) := by
    rw [show cD (H z) = chartAt (ModelProd B (V × V)) (H z) from rfl,
      FiberBundle.chartedSpace_chartAt]
    rfl
  constructor
  · intro w
    change chartAt (ModelProd B' W) z w =
      (a.prodCongr (tangentModelCoordinateEquiv r)) (cD (H z) (H w))
    rw [hcs, hcd]
    change (a (cB z.proj (t w).1), (t w).2) =
      (a (cB z.proj ((e.prod e) (H w)).1),
        tangentModelCoordinateEquiv r ((e.prod e) (H w)).2)
    rw [ht]
    rfl
  · intro p
    change H ((chartAt (ModelProd B' W) z).symm p) =
      (cD (H z)).symm ((a.prodCongr (tangentModelCoordinateEquiv r)).symm p)
    rw [hcs, hcd]
    change H (t.toOpenPartialHomeomorph.symm ((cB z.proj).symm (a.symm p.1), p.2)) =
      (e.prod e).toOpenPartialHomeomorph.symm
        ((cB z.proj).symm (a.symm p.1), (tangentModelCoordinateEquiv r).symm p.2)
    rw [ht]
    exact H.apply_symm_apply _


open CategoryTheory Topology

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem chart_open_embedding_positive {n : ℕ} {X Y : Type} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin n)))
    (d : OpenPartialHomeomorph Y (EuclideanSpace ℝ (Fin n)))
    (x : X) (he : x ∈ e.source) (hd : f x ∈ d.source)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : HasFDerivAt (fun v ↦ d (f (e.symm v))) L.toContinuousLinearMap (e x))
    (hpos : 0 < LinearMap.det L.toLinearMap) :
    localHomologyChartEquiv d (f x) hd n
      (localHomologyOpenEmbeddingEquiv f hf x n
        ((localHomologyChartEquiv e x he n).symm
          (euclideanLocalOrientationCycle n (e x)))) =
      euclideanLocalOrientationCycle n (d (f x)) := by
  let : Nonempty X := ⟨x⟩
  let F := hf.toOpenPartialHomeomorph f
  let c := F.trans d
  have hcx : x ∈ c.source := ⟨Set.mem_univ x, hd⟩
  let C := (localHomologyChartEquiv c x hcx n).toModuleIso
  let D := (localHomologyChartEquiv d (f x) hd n).toModuleIso
  let H := (localHomologyOpenEmbeddingEquiv f hf x n).toModuleIso
  -- Restrict to the actual target-chart preimage and compare the same pair maps.
  have hmaps : H.hom ≫ D.hom = C.hom := by
    let U := f ⁻¹' d.source
    have hU : IsOpen U := d.open_source.preimage f.continuous
    let a : U := ⟨x, hd⟩
    let i : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hi : Set.MapsTo i ({a}ᶜ : Set U) ({x}ᶜ : Set X) :=
      fun z hz heq ↦ hz (Subtype.ext heq)
    have hj : Set.MapsTo (f.comp i) ({a}ᶜ : Set U) ({f x}ᶜ : Set Y) :=
      fun z hz heq ↦ hz (Subtype.ext (hf.injective heq))
    let I := (localHomologyOpenInclusionEquiv U hU a n).toModuleIso
    have hcI := localHomologyChartEquiv_naturality c x hcx i
      (fun z ↦ ⟨Set.mem_univ z.val, z.property⟩) hi n
    have hdI := localHomologyChartEquiv_naturality d (f x) hd (f.comp i)
      (fun z ↦ z.property) hj n
    have hcomp : I.hom ≫ H.hom = relativeSingularHomologyMap ℤ (f.comp i) hj n := by
      change HomologicalComplex.homologyMap _ n ≫ HomologicalComplex.homologyMap _ n = _
      rw [← HomologicalComplex.homologyMap_comp, ← relativeSingularChainsMap_comp]
      rfl
    apply (cancel_epi I.hom).mp
    rw [← Category.assoc, hcomp]
    exact hdI.trans hcI.symm
  -- The original chart-transition derivative compares this actual pulled-back chart with e.
  have hder : HasFDerivAt (fun v ↦ c (e.symm v)) L.toContinuousLinearMap (e x) := hL
  have ht := localHomologyChartEquiv_transition_derivative e c x he hcx L hder n
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  rw [relativeSingularHomologyMap_eq_id_of_det_pos ℤ b L hpos n,
    Category.id_comp] at ht
  have hvalue := congrArg (fun Q ↦ Q (realOrientationCycle b b.orientation)) ht
  change C.hom ((localHomologyChartEquiv e x he n).symm
    (euclideanLocalOrientationCycle n (e x))) =
      euclideanLocalOrientationCycle n (c x) at hvalue
  have h := congrArg (fun Q ↦ Q ((localHomologyChartEquiv e x he n).symm
    (euclideanLocalOrientationCycle n (e x)))) hmaps
  exact h.trans hvalue


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem chart_transport_apply (i j : ℕ) (h : i = j) {X : Type} [TopologicalSpace X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin i)) X) (x y : X) :
    letI := C
    let c := chartAt (EuclideanSpace ℝ (Fin i)) x
    letI : ChartedSpace (EuclideanSpace ℝ (Fin j)) X := h ▸ C
    let d := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h)).toContinuousLinearEquiv
    chartAt (EuclideanSpace ℝ (Fin j)) x y = d (c y) := by
  subst j
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem chart_transport_symm (i j : ℕ) (h : i = j) {X : Type} [TopologicalSpace X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin i)) X) (x : X)
    (v : EuclideanSpace ℝ (Fin j)) :
    letI := C
    let c := chartAt (EuclideanSpace ℝ (Fin i)) x
    letI : ChartedSpace (EuclideanSpace ℝ (Fin j)) X := h ▸ C
    let d := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h)).toContinuousLinearEquiv
    (chartAt (EuclideanSpace ℝ (Fin j)) x).symm v = c.symm (d.symm v) := by
  subst j
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem integral_transport (i j : ℕ) (h : i = j) {X : Type} [TopologicalSpace X]
    [T2Space X] [SecondCountableTopology X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin i)) X)
    (O : HomologicalOrientation i X) (a : compactSupportCohomology ℚ X i) :
    letI := C
    let old := compactSupportCohomologyIntegral O a
    letI : ChartedSpace (EuclideanSpace ℝ (Fin j)) X := h ▸ C
    compactSupportCohomologyIntegral (h ▸ O)
      ((eqToIso (congrArg (compactSupportCohomology ℚ X) h)).hom a) = old := by
  subst j
  rfl


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem orientation_chart_transport (i j : ℕ) (h : i = j) {X : Type}
    [TopologicalSpace X] [T2Space X]
    (C : ChartedSpace (EuclideanSpace ℝ (Fin i)) X)
    (O : HomologicalOrientation i X)
    (hnorm : letI := C
      ∀ z : X, localHomologyChartEquiv (chartAt (EuclideanSpace ℝ (Fin i)) z) z
        (mem_chart_source _ z) i (O.localGenerator z 1) =
          euclideanLocalOrientationCycle i (chartAt (EuclideanSpace ℝ (Fin i)) z z)) :
    letI : ChartedSpace (EuclideanSpace ℝ (Fin j)) X := h ▸ C
    ∀ z : X, localHomologyChartEquiv (chartAt (EuclideanSpace ℝ (Fin j)) z) z
      (mem_chart_source _ z) j ((h ▸ O).localGenerator z 1) =
        euclideanLocalOrientationCycle j (chartAt (EuclideanSpace ℝ (Fin j)) z z) := by
  subst j
  exact hnorm

open CategoryTheory Manifold Topology
open scoped ContDiff

attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology
  tangentBundleFullChartedSpace tangentBundle_full_isManifold

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in
-- The exact pullback, complexification and transported total charts share nested bundle instances.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original complex Thom inverse and the specified tangent tube have equal
integrals for the canonical source and target tangent orientations. -/
theorem compactSupportCohomologyIntegral_tangentEmbedding {n m : ℕ} (hnm : n ≤ m) {M N : Type}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
    [T2Space N] [SecondCountableTopology N]
    (f : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (S : TangentNormalSplitting f hf)
    (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f hf))
    (h : ComplexBundle.ContinuousHermitianMetric (ComplexifiedNormalPullback f)) :
    let E := EuclideanSpace ℝ (Fin n)
    let F := EuclideanSpace ℝ (Fin m)
    let TM := TangentBundle 𝓘(ℝ, E) M
    let TN := TangentBundle 𝓘(ℝ, F) N
    let r := Module.finrank ℝ F - Module.finrank ℝ E
    letI : T2Space TM := (tangentBundle_topology E M).1
    letI : T2Space TN := (tangentBundle_topology F N).1
    letI : SecondCountableTopology TM := (tangentBundle_topology E M).2.1
    letI : SecondCountableTopology TN := (tangentBundle_topology F N).2.1
    letI := tangentBundleEuclideanChartedSpace (n := n) (M := M)
    letI := tangentBundleEuclideanChartedSpace (n := m) (M := N)
    letI := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
    let hdim : 2 * n + 2 * r = 2 * m := by
      have hrank : r = m - n := by simp [r, E, F]
      omega
    ∀ (hr : ∀ z : TM, Module.finrank ℂ (ComplexifiedNormalPullback f z) = r)
      (a : compactSupportCohomology ℚ (TotalSpace Unit (ComplexifiedNormalPullback f))
        (2 * n + 2 * r)),
      compactSupportCohomologyIntegral (tangentHomologicalOrientation (n := n) (M := M))
        (h.supportedComplexCohomologyThomIntegral r hr (2 * n) a) =
      compactSupportCohomologyIntegral (tangentHomologicalOrientation (n := m) (M := N))
        (compactSupportCohomologyOpenExtension ℚ (tangentEmbeddingTubularMap f hf S T)
          (isOpenEmbedding_tangentEmbeddingTubularMap f hf S T) (2 * m)
          ((eqToIso (congrArg
            (compactSupportCohomology ℚ (TotalSpace Unit (ComplexifiedNormalPullback f)))
              hdim)).hom a)) := by
  classical
  -- Retain the actual normal model, original total topology and supplied Hermitian fiber norms.
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  let TM := TangentBundle 𝓘(ℝ, E) M
  let TN := TangentBundle 𝓘(ℝ, F) N
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : SecondCountableTopology TM := (tangentBundle_topology E M).2.1
  let : SecondCountableTopology TN := (tangentBundle_topology F N).2.1
  let := normalBundleFiberBundle f hf.isImmersion
  let := normalBundleVectorBundle f hf.isImmersion
  let ν := NormalBundle 𝓘(ℝ, E) 𝓘(ℝ, F) f
  let r := Module.finrank ℝ F - Module.finrank ℝ E
  let V := EuclideanSpace ℝ (Fin r)
  let νP := ((smoothTangentBundleProjection E M : TM → M) *ᵖ ν)
  let C := ComplexifiedNormalPullback f
  let := isFiniteRank_complexifiedNormalPullback f hf.isImmersion
  have hr (z : TM) : Module.finrank ℂ (C z) = r := by
    rw [Module.finrank_baseChange]
    exact ((VectorBundle.continuousLinearEquivAt ℝ V νP z).toLinearEquiv.finrank_eq).trans
      (by simp [V])
  let : ∀ z, NormedAddCommGroup (C z) := h.fiberNormedAddCommGroup
  let : ∀ z, InnerProductSpace ℂ (C z) := h.fiberInnerProductSpace
  let : ∀ z, InnerProductSpace ℝ (C z) := h.realFiberInnerProductSpace
  let W := EuclideanSpace ℝ (Fin (2 * r))
  let := ComplexBundle.nativeModelTopology C W
  let H := (ComplexBundle.nativeModelTotalHomeomorph C W).trans
    (ComplexBundle.complexificationDoubleTotalHomeomorph V νP)
  let : ChartedSpace ((E × E) × (V × V)) (TotalSpace (V × V) (νP ×ᵇ νP)) :=
    inferInstanceAs (ChartedSpace (ModelProd (E × E) (V × V))
      (TotalSpace (V × V) (νP ×ᵇ νP)))
  let cD : TotalSpace (V × V) (νP ×ᵇ νP) →
      OpenPartialHomeomorph (TotalSpace (V × V) (νP ×ᵇ νP))
        ((E × E) × (V × V)) := chartAt ((E × E) × (V × V))
  let : FiberBundle W C := h.realNativeFiberBundle r hr
  let : VectorBundle ℝ W C := h.realNativeVectorBundle r hr
  let o₀ : CohomologyOrientation ℤ (2 * r) C := h.complexCohomologyOrientation r hr
  let int₀ := compactSupportCohomologyThomIntegral ℚ (2 * r) C o₀.rationalization (2 * n)
  let fc := o₀.fiberClass
  have hgen := o₀.is_generator
  have hcompat := o₀.locally_compatible
  have hclass (z : TM) (β : Module.Basis (Fin (2 * r)) ℝ (C z)) :
      fc z = realOrientationClass β (h.complexRealOrientation r hr z) :=
    geometricCohomologyOrientation_fiberClass (2 * r) C
      (h.complexRealOrientation r hr) (h.complexRealOrientation_locally_compatible r hr) z β
  -- The same doubled real frames provide both the complex orientation and exact chart maps.
  obtain ⟨b, v, hframe, hcharts⟩ :=
    interleaved_native_charts (tangentModelCoordinateEquiv n) νP h hr
  let := tangentBundleEuclideanChartedSpace (n := n) (M := M)
  let := tangentBundleEuclideanChartedSpace (n := m) (M := N)
  let : FiberBundle W C := b
  let : VectorBundle ℝ W C := v
  let : T2Space (TotalSpace W C) := t2Space_fiberBundleTotal W C
  let : SecondCountableTopology (TotalSpace W C) := secondCountable_fiberBundleTotal W C
  let o : CohomologyOrientation ℤ (2 * r) C := ⟨fc, hgen, hcompat⟩
  have hint : compactSupportCohomologyThomIntegral ℚ (2 * r) C o.rationalization (2 * n) =
      int₀ := by rfl
  let OB := tangentHomologicalOrientation (n := n) (M := M)
  let OT := bundleHomologicalOrientation (2 * r) C OB o
  let CB := bundleTotalEuclideanChartedSpace (2 * n) (2 * r) C
  let : ChartedSpace (EuclideanSpace ℝ (Fin (2 * n + 2 * r))) (TotalSpace W C) := CB
  -- The base's canonical tangent generator and the actual complex frame both have sign +1.
  have hcoeff (z : TotalSpace W C) :
      bundleTotalLocalOrientationCoefficient (2 * r) C OB o z = 1 := by
    let c := chartAt (EuclideanSpace ℝ (Fin (2 * n))) z.proj
    let q := VectorBundle.continuousLinearEquivAt ℝ W C z.proj
    let β := (EuclideanSpace.basisFun (Fin (2 * r)) ℝ).toBasis.map q.symm.toLinearEquiv
    have hbase : (OB.localGenerator z.proj).symm
        ((localHomologyChartEquiv c z.proj (mem_chart_source _ z.proj) (2 * n)).symm
          (euclideanLocalOrientationCycle (2 * n) (c z.proj))) = 1 := by
      rw [← tangentHomologicalOrientation_chart z.proj z.proj (mem_chart_source _ z.proj)]
      change (OB.localGenerator z.proj).symm
        ((localHomologyChartEquiv c z.proj (mem_chart_source _ z.proj) (2 * n)).symm
          ((localHomologyChartEquiv c z.proj (mem_chart_source _ z.proj) (2 * n))
            (OB.localGenerator z.proj 1))) = 1
      simp only [LinearEquiv.symm_apply_apply]
    have hfiber : realOrientationEvaluation β β.orientation (o.fiberClass z.proj) = 1 := by
      have ho : o.fiberClass z.proj = realOrientationClass β
          (h.complexRealOrientation r hr z.proj) :=
        hclass z.proj β
      rw [ho, ← hframe z.proj]
      exact realOrientationClass_evaluation β β.orientation
    change _ * _ = 1
    rw [hbase, hfiber, mul_one]
  have hchart (z : TotalSpace W C) :
      localHomologyChartEquiv (chartAt (EuclideanSpace ℝ (Fin (2 * n + 2 * r))) z) z
        (mem_chart_source _ z) (2 * n + 2 * r) (OT.localGenerator z 1) =
          euclideanLocalOrientationCycle (2 * n + 2 * r)
            (chartAt (EuclideanSpace ℝ (Fin (2 * n + 2 * r))) z z) := by
    rw [bundleHomologicalOrientation_chart, hcoeff, one_smul]
  -- Transport only the dimension index of these exact charts and orientation.
  have hdim : 2 * n + 2 * r = 2 * m := by
    have hrank : r = m - n := by simp [r, E, F]
    omega
  let : ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) (TotalSpace W C) := hdim ▸ CB
  let O : HomologicalOrientation (2 * m) (TotalSpace W C) := hdim ▸ OT
  let c : TotalSpace W C → OpenPartialHomeomorph (TotalSpace W C)
      (EuclideanSpace ℝ (Fin (2 * m))) := chartAt (EuclideanSpace ℝ (Fin (2 * m)))
  have hnorm := orientation_chart_transport (2 * n + 2 * r) (2 * m) hdim CB OT hchart
  let d : EuclideanSpace ℝ (Fin (2 * n + 2 * r)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * m)) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr hdim)).toContinuousLinearEquiv
  let a := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2 * n) (m := 2 * r)
  let B : ((E × E) × (V × V)) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)) :=
    ((tangentModelCoordinateEquiv n).prodCongr
      (tangentModelCoordinateEquiv r)).trans (a.symm.trans d)
  have hcv (z w : TotalSpace W C) : c z w = B (cD (H z) (H w)) := by
    rw [show c z w = d (@chartAt (EuclideanSpace ℝ (Fin (2 * n + 2 * r))) _
      (TotalSpace W C) _ CB z w) from
        chart_transport_apply (2 * n + 2 * r) (2 * m) hdim CB z w]
    change d (a.symm (chartAt (ModelProd (EuclideanSpace ℝ (Fin (2 * n))) W) z w)) = _
    rw [(hcharts z).1 w]
    rfl
  have hci (z : TotalSpace W C) (p : EuclideanSpace ℝ (Fin (2 * m))) :
      H ((c z).symm p) = (cD (H z)).symm (B.symm p) := by
    rw [show (c z).symm p =
      (@chartAt (EuclideanSpace ℝ (Fin (2 * n + 2 * r))) _ (TotalSpace W C) _ CB z).symm
        (d.symm p) from
          chart_transport_symm (2 * n + 2 * r) (2 * m) hdim CB z p]
    change H ((chartAt (ModelProd (EuclideanSpace ℝ (Fin (2 * n))) W) z).symm
      (a (d.symm p))) = _
    exact (hcharts z).2 (a (d.symm p))
  let G : C(TotalSpace W C, TN) := (tangentEmbeddingTubularMap f hf S T).comp
    ⟨ComplexBundle.nativeModelTotalHomeomorph C W,
      (ComplexBundle.nativeModelTotalHomeomorph C W).continuous⟩
  have hG : IsOpenEmbedding G := (isOpenEmbedding_tangentEmbeddingTubularMap f hf S T).comp
    (ComplexBundle.nativeModelTotalHomeomorph C W).isOpenEmbedding
  -- In these charts, use the same normalized tube derivative and its determinant-square sign.
  have hder (z : TM) :
      let w₀ : TotalSpace W C := ⟨z, 0⟩
      ∃ L : EuclideanSpace ℝ (Fin (2 * m)) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * m)),
        HasFDerivAt (fun p ↦ chartAt (EuclideanSpace ℝ (Fin (2 * m))) (G w₀)
          (G ((c w₀).symm p))) L.toContinuousLinearMap (c w₀ w₀) ∧
        0 < LinearMap.det L.toLinearMap := by
    let w₀ : TotalSpace W C := ⟨z, 0⟩
    let wD : TotalSpace (V × V) (νP ×ᵇ νP) := ⟨z, 0⟩
    have hH0 : H w₀ = wD := by
      change (⟨z, complexificationReIm (ν z.proj) 0⟩ : TotalSpace (V × V) (νP ×ᵇ νP)) = _
      rw [map_zero]
    have hG0 : G w₀ = smoothTangentMap f z := by
      change T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
        ((S.totalHomeomorph f hf).symm (H w₀)) = _
      rw [hH0]
      change (T.diffeomorph ⟨z, (S.equiv z).symm 0⟩ : TN) = _
      rw [map_zero]
      exact T.map_zero z
    obtain ⟨e, A, hA, hdet⟩ := exists_tangentDoubleTube_normalized_derivative f hf S T z
    let L := (B.symm.trans A).trans (tangentModelCoordinateEquiv m)
    have hA' : HasFDerivAt (fun p ↦ chartAt (F × F) (smoothTangentMap f z)
        (T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
          ((S.totalHomeomorph f hf).symm ((cD wD).symm p))))
        A.toContinuousLinearMap (B.symm (c w₀ w₀)) := by
      rw [hcv, B.symm_apply_apply, hH0]
      exact hA
    have hpre := hA'.comp (c w₀ w₀) B.symm.toContinuousLinearMap.hasFDerivAt
    have hpost := (tangentModelCoordinateEquiv m).toContinuousLinearMap.hasFDerivAt.comp
      (c w₀ w₀) hpre
    refine ⟨L, ?_, ?_⟩
    · change HasFDerivAt (fun p ↦ chartAt (EuclideanSpace ℝ (Fin (2 * m))) (G w₀)
        (G ((c w₀).symm p))) L.toContinuousLinearMap (c w₀ w₀)
      rw [hG0]
      apply hpost.congr_of_eventuallyEq
      filter_upwards [] with p
      change tangentModelCoordinateEquiv m
        (chartAt (F × F) (smoothTangentMap f z)
          (T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f hf)
            ((S.totalHomeomorph f hf).symm (H ((c w₀).symm p))))) = _
      rw [hci, hH0]
      rfl
    · let q := VectorBundle.continuousLinearEquivAt ℝ V νP z
      let : FiniteDimensional ℝ (νP z) := FiniteDimensional.of_injective q.toLinearMap q.injective
      let R := (ContinuousLinearEquiv.refl ℝ (E × E)).prodCongr (q.prodCongr q)
      let Aq := R.trans A
      have hnr : n + r = m := by
        have hrank : r = m - n := by simp [r, E, F]
        omega
      have hpos := det_pos_interleaved_of_normalized_double n r m hnr q e Aq hdet
      have heq :
          ((((ContinuousLinearEquiv.refl ℝ (E × E)).prodCongr (q.prodCongr q)).trans
            (((tangentModelCoordinateEquiv n).prodCongr (tangentModelCoordinateEquiv r)).trans
              (a.symm.trans d))).symm.trans Aq).trans
                (tangentModelCoordinateEquiv m) = L := by
        apply DFunLike.ext
        intro p
        change tangentModelCoordinateEquiv m (A (R (R.symm (B.symm p)))) = _
        rw [R.apply_symm_apply]
        rfl
      change 0 < LinearMap.det
        (((R.trans B).symm.trans Aq).trans (tangentModelCoordinateEquiv m)).toLinearMap at hpos
      rw [heq] at hpos
      exact hpos
  let : LocallyCompactSpace TN :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin (2 * m))) TN
  let ON := tangentHomologicalOrientation (n := m) (M := N)
  let P := homologicalOrientationOpenPullback ON G hG
  -- Excision and the actual positive derivative identify the two generators at fiber zero.
  have hzero (z : TM) :
      O.localGenerator (⟨z, 0⟩ : TotalSpace W C) 1 =
        P.localGenerator (⟨z, 0⟩ : TotalSpace W C) 1 := by
    let w₀ : TotalSpace W C := ⟨z, 0⟩
    let D := chartAt (EuclideanSpace ℝ (Fin (2 * m))) (G w₀)
    let e₀ := localHomologyChartEquiv (c w₀) w₀ (mem_chart_source _ w₀) (2 * m)
    let e₁ := localHomologyChartEquiv D (G w₀) (mem_chart_source _ (G w₀)) (2 * m)
    let eG := localHomologyOpenEmbeddingEquiv G hG w₀ (2 * m)
    obtain ⟨L, hL, hpos⟩ := hder z
    have hp := chart_open_embedding_positive G hG (c w₀) D w₀
      (mem_chart_source _ w₀) (mem_chart_source _ (G w₀)) L hL hpos
    have hsrc : e₀.symm (euclideanLocalOrientationCycle (2 * m) (c w₀ w₀)) =
        O.localGenerator w₀ 1 := by
      apply e₀.injective
      rw [e₀.apply_symm_apply]
      exact (hnorm w₀).symm
    change e₁ (eG (e₀.symm (euclideanLocalOrientationCycle (2 * m) (c w₀ w₀)))) = _ at hp
    rw [hsrc] at hp
    have ht := tangentHomologicalOrientation_chart (G w₀) (G w₀) (mem_chart_source _ (G w₀))
    apply eG.injective
    change eG (O.localGenerator w₀ 1) = eG (eG.symm (ON.localGenerator (G w₀) 1))
    rw [eG.apply_symm_apply]
    exact e₁.injective (hp.trans ht.symm)
  -- Every vector is joined to zero in its original fiber, so the agreement is global.
  have hpoint (z : TotalSpace W C) : O.localGenerator z 1 = P.localGenerator z 1 := by
    have hpath : Joined (⟨z.proj, 0⟩ : TotalSpace W C) z :=
      (PathConnectedSpace.joined (0 : C z.proj) z.snd).map
        (FiberBundle.continuous_totalSpaceMk W C z.proj)
    exact O.localGenerator_eq_of_joined P hpath (hzero z.proj)
  have hOP : O = P := by
    have hmaps : O.localGenerator = P.localGenerator := by
      funext z
      apply LinearEquiv.toLinearMap_injective
      apply LinearMap.ext
      intro a
      have h₀ := (O.localGenerator z).map_smul a (1 : ℤ)
      have h₁ := (P.localGenerator z).map_smul a (1 : ℤ)
      simp only [smul_eq_mul, mul_one, hpoint z] at h₀
      simp only [smul_eq_mul, mul_one] at h₁
      exact h₀.trans h₁.symm
    rcases O with ⟨O', hO'⟩
    rcases P with ⟨P', hP'⟩
    change O' = P' at hmaps
    cases hmaps
    rfl
  -- Apply the existing normalized Thom inverse and open-extension integration theorems.
  have hIntegral (a : compactSupportCohomology ℚ (TotalSpace W C) (2 * n + 2 * r)) :
      compactSupportCohomologyIntegral OB (int₀ a) =
        compactSupportCohomologyIntegral ON
          (compactSupportCohomologyOpenExtension ℚ G hG (2 * m)
            ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace W C)) hdim)).hom a)) := by
    let a' := (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace W C)) hdim)).hom a
    calc
      _ = compactSupportCohomologyIntegral OT a := by
        rw [← hint]
        exact compactSupportCohomologyIntegral_thomIntegral (2 * r) C OB o a
      _ = compactSupportCohomologyIntegral O a' :=
        (integral_transport (2 * n + 2 * r) (2 * m) hdim CB OT a).symm
      _ = compactSupportCohomologyIntegral P a' :=
        congrArg (fun O' ↦ compactSupportCohomologyIntegral O' a') hOP
      _ = _ := (compactSupportCohomologyIntegral_openExtension ON G hG a').symm
  -- Finally cancel the actual native-to-Unit homeomorphism in compact-support cohomology.
  let J := ComplexBundle.nativeModelTotalHomeomorph C W
  let τ := tangentEmbeddingTubularMap f hf S T
  let hτ := isOpenEmbedding_tangentEmbeddingTubularMap f hf S T
  let : T2Space (TotalSpace Unit C) := hτ.isEmbedding.t2Space
  have hcast {i j : ℕ} (hij : i = j)
      (a : compactSupportCohomology ℚ (TotalSpace Unit C) i) :
      (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace W C)) hij)).hom
        (compactSupportCohomologyHomeomorphPullback ℚ J i a) =
      compactSupportCohomologyHomeomorphPullback ℚ J j
        ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hij)).hom a) := by
    subst j
    rfl
  have hUnitIntegral (a : compactSupportCohomology ℚ (TotalSpace Unit C) (2 * n + 2 * r)) :
      compactSupportCohomologyIntegral OB
        (h.supportedComplexCohomologyThomIntegral r hr (2 * n) a) =
      compactSupportCohomologyIntegral ON
        (compactSupportCohomologyOpenExtension ℚ τ hτ (2 * m)
          ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hdim)).hom a)) := by
    let a' := (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit C)) hdim)).hom a
    have hp := hIntegral (compactSupportCohomologyHomeomorphPullback ℚ J (2 * n + 2 * r) a)
    rw [hcast hdim a] at hp
    have hc := congrArg
      (fun Q ↦ Q (compactSupportCohomologyHomeomorphPullback ℚ J (2 * m) a'))
      (compactSupportCohomologyOpenExtension_comp ℚ ⟨J, J.continuous⟩ J.isOpenEmbedding τ hτ
        (2 * m))
    change compactSupportCohomologyOpenExtension ℚ G hG (2 * m)
      (compactSupportCohomologyHomeomorphPullback ℚ J (2 * m) a') =
      compactSupportCohomologyOpenExtension ℚ τ hτ (2 * m)
        (compactSupportCohomologyOpenExtension ℚ ⟨J, J.continuous⟩ J.isOpenEmbedding (2 * m)
          (compactSupportCohomologyHomeomorphPullback ℚ J (2 * m) a')) at hc
    rw [compactSupportCohomologyOpenExtension_homeomorph] at hc
    change compactSupportCohomologyOpenExtension ℚ G hG (2 * m)
      (compactSupportCohomologyHomeomorphPullback ℚ J (2 * m) a') =
      compactSupportCohomologyOpenExtension ℚ τ hτ (2 * m)
        ((compactSupportCohomologyHomeomorphEquiv ℚ J (2 * m)).symm
          ((compactSupportCohomologyHomeomorphEquiv ℚ J (2 * m)) a')) at hc
    rw [LinearEquiv.symm_apply_apply] at hc
    change compactSupportCohomologyIntegral OB
      (int₀ (compactSupportCohomologyHomeomorphPullback ℚ J (2 * n + 2 * r) a)) = _
    exact hp.trans (congrArg (compactSupportCohomologyIntegral ON) hc)
  dsimp only
  intro hr₀ a₀
  exact hUnitIntegral a₀

end AtiyahSinger
