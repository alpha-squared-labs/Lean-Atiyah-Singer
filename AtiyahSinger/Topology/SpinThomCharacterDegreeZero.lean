/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleCompactSupportCharacter
public import AtiyahSinger.Topology.CompactSupportCohomologyProperFunctoriality
public import AtiyahSinger.Topology.ComplexThomCharacter
public import AtiyahSinger.Topology.RealThomIntegralNaturality
public import AtiyahSinger.Topology.ReducedChernCharacterNaturality
public import AtiyahSinger.Topology.SpinCohomologyOrientation
public import AtiyahSinger.Topology.SpinCoordinateOrientation
public import AtiyahSinger.Topology.SpinThomFiberClass
public import AtiyahSinger.Topology.TrivialBundleThom

/-!
# The sign of the spin Thom characteristic defect in degree zero

Public module ID: M2171.

The specified spin frame compares the actual fiber symbol with the exterior
Bott symbol and preserves the canonical complex orientation. Naturality of the
original compact-support Thom inverse then compares the degree-zero defect with
the complex Thom defect over a point. The complex normalization fixes its sign.

Source: SG III.12, Proposition 12.5, with the interleaved orientation of SG I.5.
The proof uses the actual original supported classes and normalized integrals.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_totalSpace locallyCompactSpace_totalSpace sumTopology isFiniteRank_sum

universe u v

variable {m : ℕ} {B : Type u} {P : Type v} {E : B → Type u}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [CompactSpace B] [T2Space B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

set_option maxHeartbeats 1600000 in
-- Normalize the specified spin point and its original degree-zero exterior generator.
set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original oriented spin Thom defect has degree-zero coefficient exactly `(-1)^m`. -/
theorem TopologicalSpinStructure.fiberIntegral_chernCharacter_spinorThom_zero
    (S : TopologicalSpinStructure m E o hm hP) :
    compactSupportCohomologyFiberIntegral ℚ (2 * m) E
        S.integralCohomologyOrientation.rationalization 0
        ((eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ
              (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) (2 * m) ≅
            compactSupportCohomology ℚ
              (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) (0 + 2 * m)).hom
          (bundleCompactSupportChernCharacterComponent (2 * m) E m S.spinorThomClass)) =
      (-1 : ℚ) ^ m • singularCohomologyOne ℚ B := by
  classical
  apply singularCohomology_zero_ext ℚ B
  intro b
  obtain ⟨p, hp⟩ := hP.projection_properties.2.2 b
  let R := EuclideanSpace ℝ (Fin (2 * m))
  let V := EuclideanSpace ℂ (Fin m)
  let W := ULift.{u} V
  let X := PUnit.{u + 1}
  let F := Bundle.Trivial X W
  let := modelTopology W F
  let := isFiniteRank_model W F
  let := FiniteDimensional.proper ℂ W
  let H := (unitTotalHomeomorph W F).trans (Bundle.Trivial.homeomorphProd X W)
  have hinner : Continuous (fun z : TotalSpace Unit (F ×ᵇ F) ↦
      inner ℂ z.snd.1 z.snd.2) :=
    (H.continuous.snd.comp (continuous_sum_fst (E := F) (F := F))).inner
      (H.continuous.snd.comp (continuous_sum_snd (E := F) (F := F)))
  let h := ContinuousHermitianMetric.ofInnerProduct F hinner
  have hr : ∀ x : X, Module.finrank ℂ (F x) = m := by
    intro x
    change Module.finrank ℂ W = m
    exact (LinearIsometryEquiv.ulift ℂ V).toLinearEquiv.finrank_eq.trans
      (by simp only [V, finrank_euclideanSpace, Fintype.card_fin])
  let e := (realSpinorCoordinateIsometry m).symm.trans (S.frame p b hp)
  let down := LinearIsometryEquiv.ulift ℂ V
  let downLinear : W ≃ₗ[ℂ] V := down.toLinearEquiv
  let μ : C(V, TotalSpace R E) := ⟨fun v ↦ ⟨b, e v⟩,
    (FiberBundle.continuous_totalSpaceMk R E b).comp e.continuous⟩
  have hμ : IsProperMap μ :=
    (FiberBundle.totalSpaceMk_isClosedEmbedding R E b).isProperMap.comp
      e.toHomeomorph.isProperMap
  let q : C(TotalSpace Unit F, W) := ⟨fun z ↦ (H z).2, H.continuous.snd⟩
  have hq : IsProperMap q := isProperMap_snd_of_compactSpace.comp H.isProperMap
  let d : C(W, V) := ⟨down, down.continuous⟩
  let g := μ.comp (d.comp q)
  have hg : IsProperMap g := hμ.comp (down.toHomeomorph.isProperMap.comp hq)
  let oneK := AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)
  let τ := h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm oneK)
  -- One specified principal point gives the actual exterior generator on this point bundle.
  have hunit : τ = exteriorThomClass F hinner := by
    dsimp only [τ, h]
    rw [ContinuousHermitianMetric.supportedThomHom_ofInnerProduct, supportedThomHom_compact,
      AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    exact complexKZeroCompactSupportAction_one
      ⟨π Unit F, ComplexBundle.continuous_proj⟩ _
  have hK : compactSupportKZeroPullback g hg S.spinorThomClass = τ := by
    rw [compactSupportKZeroPullback_comp (d.comp q) μ
      (down.toHomeomorph.isProperMap.comp hq) hμ, AddMonoidHom.comp_apply]
    rw [S.spinorThomClass_pullback_frame p b hp]
    rw [compactSupportKZeroPullback_comp q d hq down.toHomeomorph.isProperMap,
      AddMonoidHom.comp_apply]
    have hB : compactSupportKZeroPullback d down.toHomeomorph.isProperMap
        (exteriorBottClass V) = exteriorBottClass W :=
      exteriorBottClass_natural down.symm
    rw [hB, hunit]
    exact (exteriorThomClass_trivial_pullback (X := X) W hinner).symm
  -- Proper Chern naturality keeps the same infinity pair and hence the actual support class.
  have hch : compactSupportCohomologyProperPullback ℚ g hg (2 * m)
      (bundleCompactSupportChernCharacterComponent (2 * m) E m S.spinorThomClass) =
      h.compactSupportChernCharacterComponent m hr m τ := by
    apply (h.compactSupportCohomologyToOnePoint_bijective ℚ m hr (2 * m)).injective
    rw [compactSupportCohomologyProperPullback_toOnePoint,
      bundleCompactSupportChernCharacterComponent_toOnePoint,
      h.compactSupportChernCharacterComponent_toOnePoint]
    have hc := reducedChernCharacterComponent_pullback
      (OnePoint.infty : OnePoint (TotalSpace Unit F))
      (OnePoint.infty : OnePoint (TotalSpace R E)) (properOnePointMap g hg) rfl
      S.spinorThomClass m
    exact hc.trans (congrArg (reducedChernCharacterComponent
      (OnePoint.infty : OnePoint (TotalSpace Unit F)) m) hK)
  -- The native real model changes only the phantom total-space model, keeping every vector.
  let nW : NormedAddCommGroup W := h.fiberNormedAddCommGroup PUnit.unit
  let : NormedAddCommGroup W := nW
  let : SeminormedAddCommGroup W := nW.toSeminormedAddCommGroup
  let : MetricSpace W := nW.toMetricSpace
  let : PseudoMetricSpace W := nW.toMetricSpace.toPseudoMetricSpace
  let : UniformSpace W := nW.toMetricSpace.toPseudoMetricSpace.toUniformSpace
  let : TopologicalSpace W :=
    nW.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : InnerProductSpace ℂ W := h.fiberInnerProductSpace PUnit.unit
  let : InnerProductSpace ℝ W := h.realFiberInnerProductSpace PUnit.unit
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦ finite_fiber (E := F) x
  let : ∀ x, FiniteDimensional ℝ (F x) := fun x ↦ Module.Finite.trans ℂ (F x)
  let := nativeModelTopology F R
  let := h.realNativeFiberBundle m hr
  let := h.realNativeVectorBundle m hr
  let := h.realNativeRiemannianBundle m hr
  let HF := nativeModelTotalHomeomorph F R
  let iF : C(TotalSpace R F, TotalSpace Unit F) := ⟨HF, HF.continuous⟩
  let G := g.comp iF
  have hG : IsProperMap G := hg.comp HF.isProperMap
  let f : C(X, B) := ContinuousMap.const X b
  let a (x : X) : F x ≃L[ℝ] E (f x) :=
    ((downLinear.restrictScalars ℝ).trans e.toLinearEquiv).toContinuousLinearEquiv
  have hGfiber (x : X) : G.comp (bundleFiberInclusion (2 * m) F x) =
      (bundleFiberInclusion (2 * m) E (f x)).comp ⟨a x, (a x).continuous⟩ := by
    rfl
  have hN : Set.MapsTo G (bundleNonzero (2 * m) F) (bundleNonzero (2 * m) E) := by
    rintro ⟨x, v⟩ hv
    exact fun hz ↦ hv ((a x).injective (hz.trans (a x).map_zero.symm))
  let oF := h.complexCohomologyOrientation m hr
  let oE := S.integralCohomologyOrientation
  have ho (x : X) : relativeSingularCohomologyPullback ℚ
      (⟨a x, (a x).continuous⟩ : C(F x, E (f x)))
      (show Set.MapsTo (a x) {v : F x | v ≠ 0} {v : E (f x) | v ≠ 0} from
        fun _ hv hz ↦ hv ((a x).injective (hz.trans (a x).map_zero.symm))) (2 * m)
      (oE.rationalization.fiberClass (f x)) = oF.rationalization.fiberClass x := by
    let bV := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis
    let bF : Module.Basis (Fin m) ℂ (F x) := bV.map downLinear.symm
    let bE := (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.map
      (S.frame p b hp).toLinearEquiv
    have hmap : (complexBasisRealification bF).map (a x).toLinearEquiv =
        (complexBasisRealification bV).map e.toLinearEquiv := by
      apply DFunLike.ext
      intro j
      let ij : Fin m × Fin 2 :=
        (finProdFinEquiv.trans (finCongr (Nat.mul_comm m 2))).symm j
      have hd : downLinear (Complex.basisOneI ij.2 • downLinear.symm (bV ij.1)) =
          Complex.basisOneI ij.2 • bV ij.1 := by
        rw [map_smul, LinearEquiv.apply_symm_apply]
      have hFj : complexBasisRealification bF j =
          Complex.basisOneI ij.2 • downLinear.symm (bV ij.1) := by
        simp only [complexBasisRealification, Module.Basis.reindex_apply,
          Module.Basis.smulTower'_apply, bF, Module.Basis.map_apply, ij]
        rfl
      have hVj : complexBasisRealification bV j = Complex.basisOneI ij.2 • bV ij.1 := by
        simp only [complexBasisRealification, Module.Basis.reindex_apply,
          Module.Basis.smulTower'_apply, ij]
      calc
        ((complexBasisRealification bF).map (a x).toLinearEquiv) j =
            a x (complexBasisRealification bF j) :=
          (complexBasisRealification bF).map_apply (a x).toLinearEquiv j
        _ = a x (Complex.basisOneI ij.2 • downLinear.symm (bV ij.1)) := congrArg (a x) hFj
        _ = e (Complex.basisOneI ij.2 • bV ij.1) := congrArg e hd
        _ = e (complexBasisRealification bV j) := congrArg e hVj.symm
        _ = ((complexBasisRealification bV).map e.toLinearEquiv) j :=
          ((complexBasisRealification bV).map_apply e.toLinearEquiv j).symm
    have hor : Orientation.map (Fin (2 * m)) (a x).toLinearEquiv
        (h.complexRealOrientation m hr x) = o (f x) := by
      rw [← h.complexRealOrientation_basis m hr x bF,
        ← Module.Basis.orientation_map, hmap, Module.Basis.orientation_map]
      exact S.frame_complexOrientation p b hp
    have hFx : oF.fiberClass x = realOrientationClass (complexBasisRealification bF)
        (h.complexRealOrientation m hr x) :=
      geometricCohomologyOrientation_fiberClass (2 * m) F (h.complexRealOrientation m hr)
        (h.complexRealOrientation_locally_compatible m hr) x (complexBasisRealification bF)
    have hEb : oE.fiberClass (f x) = realOrientationClass bE (o (f x)) :=
      geometricCohomologyOrientation_fiberClass (2 * m) E o
        S.isLocallyCompatibleBundleOrientation (f x) bE
    let fx : C(F x, E (f x)) := ⟨a x, (a x).continuous⟩
    have hfx : Set.MapsTo fx {v : F x | v ≠ 0} {v : E (f x) | v ≠ 0} :=
      fun _ hv hz ↦ hv ((a x).injective (hz.trans (a x).map_zero.symm))
    have hi : relativeSingularCohomologyPullback ℤ fx hfx (2 * m)
        (oE.fiberClass (f x)) = oF.fiberClass x := by
      rw [hFx, hEb]
      exact realOrientationClass_pullback (complexBasisRealification bF)
        (h.complexRealOrientation m hr x) bE (o (f x)) (a x) hor
    exact (relativeSingularCohomologyRationalization_naturality
      fx hfx (2 * m)
      (oE.fiberClass (f x))).symm.trans (congrArg
        (relativeSingularCohomologyRationalization {v : F x | v ≠ 0} (2 * m)) hi)
  -- Naturality compares the specified inverses; the complex point normalization fixes the sign.
  let cE := (eqToIso (show compactSupportCohomology ℚ (TotalSpace R E) (2 * m) =
      compactSupportCohomology ℚ (TotalSpace R E) (0 + 2 * m) by congr 1; omega)).hom
    (bundleCompactSupportChernCharacterComponent (2 * m) E m S.spinorThomClass)
  have hnat := compactSupportCohomologyFiberIntegral_pullback ℚ (2 * m) F E
    oF.rationalization oE.rationalization f G hN a hGfiber ho hG 0 cE
  have hsquare (c : compactSupportCohomology ℚ (TotalSpace R E) (0 + 2 * m)) :
      compactSupportCohomologyHomeomorphPullback ℚ HF (0 + 2 * m)
        (compactSupportCohomologyProperPullback ℚ g hg (0 + 2 * m) c) =
      compactSupportCohomologyProperPullback ℚ G hG (0 + 2 * m) c := by
    rw [← compactSupportCohomologyProperPullback_homeomorph,
      ← compactSupportCohomologyProperPullback_comp]
  have hcast {j k : ℕ} (hjk : j = k)
      (c : compactSupportCohomology ℚ (TotalSpace R E) j) :
      compactSupportCohomologyProperPullback ℚ g hg k
        ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace R E)) hjk)).hom c) =
      (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit F)) hjk)).hom
        (compactSupportCohomologyProperPullback ℚ g hg j c) := by
    subst k
    rfl
  rw [map_smul, singularCohomologyPullback_one]
  change singularCohomologyPullback ℚ f 0
    (compactSupportCohomologyFiberIntegral ℚ (2 * m) E oE.rationalization 0 cE) = _
  rw [← hnat, ← hsquare]
  change h.complexCohomologyFiberIntegral m hr 0
    (compactSupportCohomologyProperPullback ℚ g hg (0 + 2 * m) cE) = _
  dsimp only [cE]
  rw [hcast (show 2 * m = 0 + 2 * m by omega), hch]
  have hvalue := h.complexThomDefectComponent_eq_inverseTodd m hr 0
  rw [inverseToddClassComponent_zero] at hvalue
  exact hvalue

end AtiyahSinger
