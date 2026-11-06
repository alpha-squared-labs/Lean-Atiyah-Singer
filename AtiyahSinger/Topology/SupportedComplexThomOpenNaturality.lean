/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportOpenHomeomorph
public import AtiyahSinger.Topology.ComplexCohomologyOrientationNaturality
public import AtiyahSinger.Topology.FiniteBundleTopology
public import AtiyahSinger.Topology.SupportedCohomologyThomOpenNaturality
public import AtiyahSinger.Topology.SupportedComplexProjectionFormula

/-!
# Open-extension naturality of the specified complex Thom inverse

Public module ID: M2210.

The original complex-oriented supported Thom map commutes with actual complex
bundle isomorphisms over open embeddings. The two supplied Hermitian metrics
need not agree: the original fiber orientation comparison supplies their same
canonical complex generators. The inverse formula uses the very same supported
Thom inverse, also on a noncompact base.

Sources: SG III.12--13; Milnor--Stasheff, Sections 9 and 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory Topology

universe u

variable {X Y : Type u} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] [T2Space Y]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : Y → Type u} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
  (r : ℕ) (hrE : ∀ x, Module.finrank ℂ (E x) = r)
  (hrF : ∀ y, Module.finrank ℂ (F y) = r)
  (f : C(X, Y)) (hfOpen : IsOpenEmbedding f)
  (e : ∀ x, E x ≃ₗ[ℂ] F (f x))
  (g : C(TotalSpace Unit E, TotalSpace Unit F))
  (hg : ∀ z, g z = ⟨f z.proj, e z.proj z.snd⟩) (hgOpen : IsOpenEmbedding g)

attribute [local instance] t2Space_totalSpace t2Space_fiberBundleTotal

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

include hg in
/-- The specified supported complex Thom map commutes with the same open extension. -/
theorem supportedComplexCohomologyThomMap_openExtension (p : ℕ)
    (a : compactSupportCohomology ℚ X p) :
    hF.supportedComplexCohomologyThomMap r hrF p
        (compactSupportCohomologyOpenExtension ℚ f hfOpen p a) =
      compactSupportCohomologyOpenExtension ℚ g hgOpen (p + 2 * r)
        (hE.supportedComplexCohomologyThomMap r hrE p a) := by
  let : ∀ x, NormedAddCommGroup (E x) := hE.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := hE.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := hE.realFiberInnerProductSpace
  let : ∀ y, NormedAddCommGroup (F y) := hF.fiberNormedAddCommGroup
  let : ∀ y, InnerProductSpace ℂ (F y) := hF.fiberInnerProductSpace
  let : ∀ y, InnerProductSpace ℝ (F y) := hF.realFiberInnerProductSpace
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let : ∀ y, FiniteDimensional ℂ (F y) := fun y ↦ finite_fiber (E := F) y
  let V := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E V
  let := hE.realNativeFiberBundle r hrE
  let := hE.realNativeVectorBundle r hrE
  let := hE.realNativeRiemannianBundle r hrE
  let := nativeModelTopology F V
  let := hF.realNativeFiberBundle r hrF
  let := hF.realNativeVectorBundle r hrF
  let := hF.realNativeRiemannianBundle r hrF
  let HE := nativeModelTotalHomeomorph E V
  let HF := nativeModelTotalHomeomorph F V
  let he : C(TotalSpace V E, TotalSpace Unit E) := ⟨HE, HE.continuous⟩
  let hf : C(TotalSpace V F, TotalSpace Unit F) := ⟨HF, HF.continuous⟩
  let G : C(TotalSpace V E, TotalSpace V F) :=
    (⟨HF.symm, HF.symm.continuous⟩ : C(_, _)).comp (g.comp he)
  have hGOpen : IsOpenEmbedding G :=
    HF.symm.isOpenEmbedding.comp (hgOpen.comp HE.isOpenEmbedding)
  let eC (x : X) : E x ≃L[ℂ] F (f x) := (e x).toContinuousLinearEquiv
  let eR (x : X) : E x ≃L[ℝ] F (f x) :=
    { (e x).restrictScalars ℝ with
      continuous_toFun := (eC x).continuous
      continuous_invFun := (eC x).symm.continuous }
  have hG (x : X) : G.comp (bundleFiberInclusion (2 * r) E x) =
      (bundleFiberInclusion (2 * r) F (f x)).comp ⟨eR x, (eR x).continuous⟩ := by
    apply ContinuousMap.ext
    intro v
    exact congrArg HF.symm (hg ⟨x, v⟩)
  have hN : Set.MapsTo G (bundleNonzero (2 * r) E) (bundleNonzero (2 * r) F) := by
    rintro ⟨x, v⟩ hv
    have hz : G ⟨x, v⟩ = ⟨f x, eR x v⟩ :=
      congrArg (fun t ↦ t v) (hG x)
    change (G ⟨x, v⟩).snd ≠ 0
    rw [hz]
    exact fun hzero ↦ hv ((eR x).injective (hzero.trans (eR x).map_zero.symm))
  let oE := (hE.complexCohomologyOrientation r hrE).rationalization
  let oF := (hF.complexCohomologyOrientation r hrF).rationalization
  -- The native map preserves the original fiber generators, not merely an unspecified orientation.
  have ho (x : X) : relativeSingularCohomologyPullback ℚ
      (⟨eR x, (eR x).continuous⟩ : C(E x, F (f x)))
      (show Set.MapsTo (eR x) {v : E x | v ≠ 0} {v : F (f x) | v ≠ 0} from
        fun _ hv hz ↦ hv ((eR x).injective (hz.trans (eR x).map_zero.symm))) (2 * r)
      (oF.fiberClass (f x)) = oE.fiberClass x :=
    complexCohomologyOrientation_fiberClass_pullback hE hF r hrE hrF x (f x) (eC x)
  have hnat := compactSupportCohomologyThomMap_openExtension ℚ (2 * r) E F oE oF
    f hfOpen G hGOpen hN eR hG ho p a
  have hEMap (b : compactSupportCohomology ℚ X p) :
      hE.supportedComplexCohomologyThomMap r hrE p b =
        compactSupportCohomologyOpenExtension ℚ he HE.isOpenEmbedding (p + 2 * r)
          (compactSupportCohomologyThomMap ℚ (2 * r) E oE p b) :=
    (compactSupportCohomologyOpenExtension_homeomorph ℚ HE (p + 2 * r) _).symm
  have hFMap (b : compactSupportCohomology ℚ Y p) :
      hF.supportedComplexCohomologyThomMap r hrF p b =
        compactSupportCohomologyOpenExtension ℚ hf HF.isOpenEmbedding (p + 2 * r)
          (compactSupportCohomologyThomMap ℚ (2 * r) F oF p b) :=
    (compactSupportCohomologyOpenExtension_homeomorph ℚ HF (p + 2 * r) _).symm
  -- Both paths extend along exactly the same original map of total spaces.
  have hcomm : hf.comp G = g.comp he := by
    apply ContinuousMap.ext
    intro z
    exact HF.apply_symm_apply (g (HE z))
  rw [hFMap, hEMap, hnat]
  change (compactSupportCohomologyOpenExtension ℚ G hGOpen (p + 2 * r) ≫
    compactSupportCohomologyOpenExtension ℚ hf HF.isOpenEmbedding (p + 2 * r)) _ =
      (compactSupportCohomologyOpenExtension ℚ he HE.isOpenEmbedding (p + 2 * r) ≫
        compactSupportCohomologyOpenExtension ℚ g hgOpen (p + 2 * r)) _
  rw [← compactSupportCohomologyOpenExtension_comp,
    ← compactSupportCohomologyOpenExtension_comp]
  have hchange (j k : C(TotalSpace V E, TotalSpace Unit F)) (hjk : j = k)
      (hj : IsOpenEmbedding j) (hk : IsOpenEmbedding k) :
      compactSupportCohomologyOpenExtension ℚ j hj (p + 2 * r) =
        compactSupportCohomologyOpenExtension ℚ k hk (p + 2 * r) := by
    subst k
    rfl
  exact congrArg (fun t ↦ t (compactSupportCohomologyThomMap ℚ (2 * r) E oE p a))
    (hchange (hf.comp G) (g.comp he) hcomm _ _)

include hg in
/-- The specified supported complex integral commutes with this same open extension. -/
theorem supportedComplexCohomologyThomIntegral_openExtension (p : ℕ)
    (b : compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2 * r)) :
    hF.supportedComplexCohomologyThomIntegral r hrF p
        (compactSupportCohomologyOpenExtension ℚ g hgOpen (p + 2 * r) b) =
      compactSupportCohomologyOpenExtension ℚ f hfOpen p
        (hE.supportedComplexCohomologyThomIntegral r hrE p b) := by
  -- Recover the original b by this very Thom inverse and use the just-proved forward square.
  have h := supportedComplexCohomologyThomMap_openExtension hE hF r hrE hrF
    f hfOpen e g hg hgOpen p (hE.supportedComplexCohomologyThomIntegral r hrE p b)
  rw [hE.supportedComplexCohomologyThomMap_thomIntegral] at h
  rw [← h, hF.supportedComplexCohomologyThomIntegral_thomMap]

/-- On a compact base, forgetting the support of this integral gives the original fiber integral. -/
theorem supportedComplexCohomologyThomIntegral_compact [CompactSpace X] (p : ℕ)
    (a : compactSupportCohomology ℚ (TotalSpace Unit E) (p + 2 * r)) :
    compactSupportCohomologyToOrdinary ℚ X p
        (hE.supportedComplexCohomologyThomIntegral r hrE p a) =
      hE.complexCohomologyFiberIntegral r hrE p a := by
  -- The known forward comparison determines the inverse comparison for this same a.
  have h := hE.supportedComplexCohomologyThomMap_compact r hrE p
    (hE.supportedComplexCohomologyThomIntegral r hrE p a)
  rw [hE.supportedComplexCohomologyThomMap_thomIntegral] at h
  exact (hE.complexCohomologyFiberIntegral_thomMap r hrE p _).symm.trans
    (congrArg (hE.complexCohomologyFiberIntegral r hrE p) h.symm)

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
