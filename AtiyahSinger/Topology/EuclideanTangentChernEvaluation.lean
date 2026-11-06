/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentHomologicalOrientation
public import AtiyahSinger.Topology.CompactSupportCohomologyProperFunctoriality
public import AtiyahSinger.Topology.ComplexThomCharacter
public import AtiyahSinger.Topology.EuclideanTangentKTheory
public import AtiyahSinger.Topology.ReducedChernCharacterNaturality
public import AtiyahSinger.Topology.SpinCoordinateOrientation
public import AtiyahSinger.Topology.ThomIntegralNormalization
public import AtiyahSinger.Topology.TrivialBundleThom

/-!
# Euclidean Bott coordinates and the canonical tangent Chern evaluation

Public module ID: M1826.

The specified integer Bott coordinate on the actual tangent bundle of real
Euclidean space equals (-1)^N times the top Chern evaluation on its canonical
interleaved locally finite fundamental class. The compact-support class in the
statement is identified with its actual reduced Chern character at infinity.
No orientation comparison or generator normalization is assumed.

The proof transports the actual positive exterior symbol from the point bundle,
uses the original complex Thom defect, and compares the same relative Thom class
with the integral local generator in the original interleaved tangent chart.
The zero-dimensional case uses the positive empty frame and the same point class.

Source: Atiyah--Singer III, Proposition 2.11, Theorem 2.12, and the positive Bott
normalization on pp.556--557; Lawson--Michelsohn, Spin Geometry III.12--III.13.
The native singular-support and coordinate comparisons implement these conventions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_totalSpace locallyCompactSpace_totalSpace sumTopology isFiniteRank_sum

set_option maxHeartbeats 800000 in
-- Retain the original one-point and native Thom transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in

/-- The specified positive Bott coordinate is the signed canonical tangent Chern evaluation. -/
theorem euclideanTangentKZeroEquivInt_eq_chern_evaluation (N : ℕ)
    (u : CompactSupportKZero
      (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin N))))
    (c : compactSupportCohomology ℚ
      (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin N))) (2 * N))
    (hc : compactSupportCohomologyToOnePoint ℚ _ (2 * N) c =
      reducedChernCharacterComponent (OnePoint.infty : OnePoint
        (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin N)))) N u) :
    ((euclideanTangentKZeroEquivInt N u : ℤ) : ℚ) =
      (-1 : ℚ) ^ N * compactSupportLocallyFinitePairing ℚ _ (2 * N) c
        (rationalTangentFundamentalClass (n := N) (M := EuclideanSpace ℝ (Fin N))) := by
  classical
  -- Keep the point-bundle exterior symbol and the original x + i v coordinate map.
  let V := EuclideanSpace ℂ (Fin N)
  let X := PUnit.{1}
  let F := Bundle.Trivial X V
  let := modelTopology V F
  let := isFiniteRank_model V F
  let := FiniteDimensional.proper ℂ V
  let H := (unitTotalHomeomorph V F).trans (Bundle.Trivial.homeomorphProd X V)
  have hinner : Continuous (fun z : TotalSpace Unit (F ×ᵇ F) ↦
      inner ℂ z.snd.1 z.snd.2) :=
    (H.continuous.snd.comp (continuous_sum_fst (E := F) (F := F))).inner
      (H.continuous.snd.comp (continuous_sum_snd (E := F) (F := F)))
  let h := ContinuousHermitianMetric.ofInnerProduct F hinner
  have hr : ∀ x : X, Module.finrank ℂ (F x) = N := by
    intro x
    simp only [F, V, finrank_euclideanSpace, Fintype.card_fin]
  let q : C(TotalSpace Unit F, V) := ⟨fun z ↦ (H z).2, H.continuous.snd⟩
  have hq : IsProperMap q := isProperMap_snd_of_compactSpace.comp H.isProperMap
  let e := (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℂ)).trans
    (euclideanTangentComplexHomeomorph N).symm
  let f := (⟨e, e.continuous⟩ : C(V, _)).comp q
  have hf : IsProperMap f := e.isProperMap.comp hq
  let oneK := AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)
  let τ := h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm oneK)
  have hunit : τ = exteriorThomClass F hinner := by
    dsimp only [τ, h]
    rw [ContinuousHermitianMetric.supportedThomHom_ofInnerProduct, supportedThomHom_compact,
      AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    exact complexKZeroCompactSupportAction_one
      ⟨π Unit F, ComplexBundle.continuous_proj⟩ _
  let b := compactSupportKZeroHomeomorph e (exteriorBottClass V)
  have hb : euclideanTangentKZeroEquivInt N b = 1 := by
    change bottEuclideanClassEquivInt N
      (compactSupportKZeroHomeomorph (euclideanTangentComplexHomeomorph N) b) = 1
    have hcomp := compactSupportKZeroPullback_comp
      ⟨(euclideanTangentComplexHomeomorph N).symm,
        (euclideanTangentComplexHomeomorph N).symm.continuous⟩ ⟨e.symm, e.symm.continuous⟩
      (euclideanTangentComplexHomeomorph N).symm.isProperMap e.symm.isProperMap
    have hcoords : (⟨e.symm, e.symm.continuous⟩ : C(_, V)).comp
        ⟨(euclideanTangentComplexHomeomorph N).symm,
          (euclideanTangentComplexHomeomorph N).symm.continuous⟩ =
        ⟨(PiLp.homeomorph 2 (fun _ : Fin N ↦ ℂ)).symm,
          (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℂ)).symm.continuous⟩ := by
      apply ContinuousMap.ext
      intro z
      exact congrArg (PiLp.homeomorph 2 (fun _ : Fin N ↦ ℂ)).symm
        ((euclideanTangentComplexHomeomorph N).apply_symm_apply z)
    change bottEuclideanClassEquivInt N
      (compactSupportKZeroPullback _ _ (compactSupportKZeroPullback _ _ _)) = _
    rw [← AddMonoidHom.comp_apply, ← hcomp]
    simp only [hcoords]
    exact bottEuclideanClassEquivInt_exteriorBottEuclideanClass N
  have hpre : compactSupportKZeroPullback f hf b = τ := by
    change compactSupportKZeroPullback ((⟨e, e.continuous⟩ : C(V, _)).comp q) hf
      (compactSupportKZeroHomeomorph e (exteriorBottClass V)) = τ
    rw [compactSupportKZeroPullback_comp q ⟨e, e.continuous⟩ hq e.isProperMap,
      AddMonoidHom.comp_apply]
    change compactSupportKZeroPullback q hq
      (compactSupportKZeroHomeomorph e.symm (compactSupportKZeroHomeomorph e
        (exteriorBottClass V))) = τ
    have hcancel : compactSupportKZeroHomeomorph e.symm
        (compactSupportKZeroHomeomorph e (exteriorBottClass V)) = exteriorBottClass V :=
      DFunLike.congr_fun (compactSupportKZeroHomeomorph_symm e) (exteriorBottClass V)
    rw [hcancel, hunit]
    exact (exteriorThomClass_trivial_pullback (X := X) V hinner).symm
  let k := euclideanTangentKZeroEquivInt N u
  have hu : u = k • b := by
    apply (euclideanTangentKZeroEquivInt N).injective
    rw [map_zsmul, hb, zsmul_eq_mul, mul_one]
    rfl
  have hK : compactSupportKZeroPullback f hf u = k • τ := by rw [hu, map_zsmul, hpre]
  have hch : compactSupportCohomologyProperPullback ℚ f hf (2 * N) c =
      k • h.compactSupportChernCharacterComponent N hr N τ := by
    apply (h.compactSupportCohomologyToOnePoint_bijective ℚ N hr (2 * N)).injective
    rw [compactSupportCohomologyProperPullback_toOnePoint, hc, map_zsmul,
      h.compactSupportChernCharacterComponent_toOnePoint]
    have hc' := reducedChernCharacterComponent_pullback
      (OnePoint.infty : OnePoint (TotalSpace Unit F)) (OnePoint.infty : OnePoint _)
      (properOnePointMap f hf) rfl u N
    change _ = reducedChernCharacterComponent (OnePoint.infty : OnePoint (TotalSpace Unit F))
      N (compactSupportKZeroPullback f hf u) at hc'
    rw [hK, map_zsmul] at hc'
    exact hc'
  -- The actual complex Thom inverse determines the top Chern component, including its sign.
  let U := h.complexCohomologyThomMap N hr 0 (singularCohomologyOne ℚ X)
  let A : compactSupportCohomology ℚ (TotalSpace Unit F) (2 * N) ≅
      compactSupportCohomology ℚ (TotalSpace Unit F) (0 + 2 * N) :=
    eqToIso (by congr 1; omega)
  have hdef : h.complexCohomologyFiberIntegral N hr 0
      (A.hom (h.compactSupportChernCharacterComponent N hr N τ)) =
      (-1 : ℚ) ^ N • singularCohomologyOne ℚ X := by
    have hd := h.complexThomDefectComponent_eq_inverseTodd N hr 0
    rw [inverseToddClassComponent_zero] at hd
    simpa only [ContinuousHermitianMetric.complexThomDefectComponent, Nat.add_zero,
      Nat.mul_zero] using hd
  have hC : h.compactSupportChernCharacterComponent N hr N τ =
      (-1 : ℚ) ^ N • A.inv U := by
    have h' := congrArg (h.complexCohomologyThomMap N hr 0) hdef
    rw [h.complexCohomologyThomMap_fiberIntegral, map_smul] at h'
    have hh := congrArg (fun z ↦ A.inv z) h'
    rw [map_smul, ← ModuleCat.comp_apply, A.hom_inv_id, ModuleCat.id_apply] at hh
    exact hh
  rw [hC] at hch
  -- Native real Thom support is the original zero point of this same point bundle.
  let R := EuclideanSpace ℝ (Fin (2 * N))
  let L₀ := (realSpinorCoordinateIsometry N).toLinearEquiv
  let bV := (EuclideanSpace.basisFun (Fin N) ℂ).toBasis
  have hcoordinate (z : TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin N))
      (EuclideanSpace ℝ (Fin N))) :
      (realSpinorCoordinateIsometry N).symm
        ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℂ)).symm
          (euclideanTangentComplexHomeomorph N z)) =
        tangentModelCoordinateEquiv N
          (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) z) := by
    ext k
    obtain ⟨⟨i, j⟩, rfl⟩ :=
      (finProdFinEquiv.trans (finCongr (Nat.mul_comm N 2))).surjective k
    fin_cases j <;>
      simp [realSpinorCoordinateIsometry, OrthonormalBasis.reindex, tangentModelCoordinateEquiv,
        euclideanTangentComplexHomeomorph, PiLp.homeomorph, Pi.orthonormalBasis_repr,
        Complex.orthonormalBasisOneI_repr_apply]
  let Q := H.trans (Homeomorph.uniqueProd X V)
  let QE := Q.trans e
  let := nativeModelTopology F R
  let HF := nativeModelTotalHomeomorph F R
  let G := HF.trans QE
  -- The actual realification frame transports the positive local simplex to the canonical one.
  let TM := TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin N))
  let : SecondCountableTopology TM :=
    (tangentBundle_topology (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin N))).2.1
  let cT : ChartedSpace R TM :=
    tangentBundleEuclideanChartedSpace (n := N) (M := EuclideanSpace ℝ (Fin N))
  let O := tangentHomologicalOrientation (n := N) (M := EuclideanSpace ℝ (Fin N))
  let w₀ : TotalSpace R F := ⟨PUnit.unit, 0⟩
  let z₀ := G w₀
  let t := chartAt R z₀
  have hcharts (z : TM) : z ∈ t.source ∧ t z = tangentModelCoordinateEquiv N
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) z) := by
    constructor
    · dsimp only [t, cT, chartAt, tangentBundleEuclideanChartedSpace, linearModelChartedSpace,
        ChartedSpace.comp, OpenPartialHomeomorph.singletonChartedSpace]
      change z ∈ (chartAt (ModelProd (EuclideanSpace ℝ (Fin N))
        (EuclideanSpace ℝ (Fin N))) z₀).toPartialEquiv.source ∧ _
      rw [tangentBundle_model_space_chartAt]
      trivial
    · change tangentModelCoordinateEquiv N
        (chartAt (ModelProd (EuclideanSpace ℝ (Fin N)) (EuclideanSpace ℝ (Fin N))) z₀ z) = _
      rw [tangentBundle_model_space_coe_chartAt]
      rfl
  have hchartG (v : V) : t (G (⟨PUnit.unit, v⟩ : TotalSpace R F)) = L₀.symm v := by
    rw [(hcharts _).2, ← hcoordinate]
    change (realSpinorCoordinateIsometry N).symm
      ((PiLp.homeomorph 2 (fun _ : Fin N ↦ ℂ)).symm
        (euclideanTangentComplexHomeomorph N (e v))) = _
    simp only [e, Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
      Homeomorph.symm_apply_apply]
    rfl
  let nV : NormedAddCommGroup V := h.fiberNormedAddCommGroup PUnit.unit
  let : NormedAddCommGroup V := nV
  let : SeminormedAddCommGroup V := nV.toSeminormedAddCommGroup
  let : MetricSpace V := nV.toMetricSpace
  let : PseudoMetricSpace V := nV.toMetricSpace.toPseudoMetricSpace
  let : UniformSpace V := nV.toMetricSpace.toPseudoMetricSpace.toUniformSpace
  let : TopologicalSpace V :=
    nV.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : InnerProductSpace ℂ V := h.fiberInnerProductSpace PUnit.unit
  let : InnerProductSpace ℝ V := h.realFiberInnerProductSpace PUnit.unit
  let := nativeModelTopology F R
  let := h.realNativeFiberBundle N hr
  let := h.realNativeVectorBundle N hr
  let := h.realNativeRiemannianBundle N hr
  let oF := h.complexCohomologyOrientation N hr
  let UN := cohomologyZeroSectionPushforward ℚ (2 * N) F oF.rationalization 0
    (singularCohomologyOne ℚ X)
  have hUN : compactSupportCohomologyHomeomorphPullback ℚ HF (0 + 2 * N) U = UN := by
    exact (compactSupportCohomologyHomeomorphEquiv ℚ HF (0 + 2 * N)).apply_symm_apply _
  let AN : compactSupportCohomology ℚ (TotalSpace R F) (2 * N) ≅
      compactSupportCohomology ℚ (TotalSpace R F) (0 + 2 * N) := eqToIso (by congr 1; omega)
  have hThom : AN.inv UN = compactSupportCohomologyThomClass ℚ (2 * N) F oF.rationalization := by
    have hcast {a b : ℕ} (hab : a = b)
        (x : relativeSingularCohomology ℚ (bundleNonzero (2 * N) F) a) :
        (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace R F)) hab)).hom
          (compactSupportCohomologyClass ℚ (TotalSpace R F)
            (cohomologyZeroSectionSupport (2 * N) F) a x) =
          compactSupportCohomologyClass ℚ (TotalSpace R F)
            (cohomologyZeroSectionSupport (2 * N) F) b
              ((eqToIso (congrArg (relativeSingularCohomology ℚ
                (bundleNonzero (2 * N) F)) hab)).hom x) := by
      subst b
      rfl
    change (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace R F))
      (Nat.zero_add (2 * N)))).hom
        (compactSupportCohomologyClass ℚ (TotalSpace R F)
          (cohomologyZeroSectionSupport (2 * N) F) (0 + 2 * N)
            (cohomologyThomMap ℚ (2 * N) F oF.rationalization 0
              (singularCohomologyOne ℚ X))) = _
    rw [hcast (Nat.zero_add (2 * N))]
    dsimp only [cohomologyThomMap, LinearMap.comp_apply, LinearMap.flip_apply,
      ModuleCat.hom_comp, ModuleCat.hom_ofHom]
    rw [singularCohomologyPullback_one, relativeSingularCohomologyAction_one]
    rfl
  have hcommute : compactSupportCohomologyHomeomorphPullback ℚ HF (2 * N) (A.inv U) =
      AN.inv (compactSupportCohomologyHomeomorphPullback ℚ HF (0 + 2 * N) U) := by
    have hcast {a b : ℕ} (hab : a = b)
        (x : compactSupportCohomology ℚ (TotalSpace Unit F) a) :
        compactSupportCohomologyHomeomorphPullback ℚ HF b
          ((eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit F)) hab)).hom x) =
          (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace R F)) hab)).hom
            (compactSupportCohomologyHomeomorphPullback ℚ HF a x) := by
      subst b
      rfl
    exact hcast (Nat.zero_add (2 * N)) U
  have hGclass : compactSupportCohomologyHomeomorphPullback ℚ G (2 * N) c =
      k • (-1 : ℚ) ^ N • compactSupportCohomologyThomClass ℚ (2 * N) F oF.rationalization := by
    have hh := congrArg (compactSupportCohomologyHomeomorphPullback ℚ HF (2 * N)) hch
    rw [map_zsmul, map_smul, hcommute, hUN, hThom] at hh
    have hcomp := compactSupportCohomologyProperPullback_comp ℚ
      (⟨HF, HF.continuous⟩ : C(_, _)) f HF.isProperMap hf (2 * N) c
    rw [compactSupportCohomologyProperPullback_homeomorph] at hcomp
    rw [← compactSupportCohomologyProperPullback_homeomorph ℚ G]
    exact hcomp.trans hh
  let L : R ≃L[ℝ] F PUnit.unit := L₀.toContinuousLinearEquiv
  let p : C(R, TM) := (⟨G, G.continuous⟩ : C(TotalSpace R F, TM)).comp
    ((bundleFiberInclusion (2 * N) F PUnit.unit).comp ⟨L, L.continuous⟩)
  have hp₀ : p 0 = z₀ := by
    change G (⟨PUnit.unit, L 0⟩ : TotalSpace R F) = G w₀
    rw [map_zero]
  have hp : Function.Injective p := by
    intro v w hvw
    apply L.injective
    exact congrArg (fun z : TotalSpace R F ↦ (z.snd : V)) (G.injective hvw)
  have hpA : Set.MapsTo p {v : R | v ≠ 0} ({z₀}ᶜ : Set TM) :=
    fun _ hv hz ↦ hv (hp (hz.trans hp₀.symm))
  have hchartp (v : R) : t (p v) = v := by
    change t (G (⟨PUnit.unit, L v⟩ : TotalSpace R F)) = v
    rw [hchartG]
    exact L₀.symm_apply_apply v
  have ht₀ : t z₀ = 0 := hp₀ ▸ hchartp 0
  let bR := (EuclideanSpace.basisFun (Fin (2 * N)) ℝ).toBasis
  let γ := realOrientationCycle bR bR.orientation
  have hcanonical : relativeSingularHomologyMap ℤ p hpA (2 * N) γ =
      O.localGenerator z₀ 1 := by
    apply (localHomologyChartEquiv t z₀ (hcharts z₀).1 (2 * N)).injective
    rw [tangentHomologicalOrientation_chart]
    have hn := congrArg (fun F ↦ F γ)
      (localHomologyChartEquiv_naturality t z₀ (hcharts z₀).1 p
        (fun v ↦ (hcharts (p v)).1) hpA (2 * N))
    change localHomologyChartEquiv t z₀ (hcharts z₀).1 (2 * N)
      (relativeSingularHomologyMap ℤ p hpA (2 * N) γ) = _ at hn
    rw [hn]
    have hm : (⟨fun v ↦ t (p v),
        t.continuousOn.comp_continuous p.continuous (fun v ↦ (hcharts (p v)).1)⟩ : C(R, R)) =
        ⟨fun v ↦ t z₀ + v, continuous_const.add continuous_id⟩ := by
      apply ContinuousMap.ext
      intro v
      change t (p v) = t z₀ + v
      rw [hchartp, ht₀, zero_add]
    have hmaps (f g : C(R, R)) (hfg : f = g)
        (hf : Set.MapsTo f {v : R | v ≠ 0} ({t z₀}ᶜ : Set R))
        (hg : Set.MapsTo g {v : R | v ≠ 0} ({t z₀}ᶜ : Set R)) :
        relativeSingularHomologyMap ℤ f hf (2 * N) =
          relativeSingularHomologyMap ℤ g hg (2 * N) := by
      subst g
      rfl
    exact congrArg (fun F ↦ F γ) (hmaps _ _ hm _ _)
  have hLorientation : Orientation.map (Fin (2 * N)) L.toLinearEquiv bR.orientation =
      h.complexRealOrientation N hr PUnit.unit := by
    rw [← Module.Basis.orientation_map]
    have hb : bR.map L.toLinearEquiv = complexBasisRealification bV :=
      realSpinorCoordinateIsometry_basis N
    rw [hb]
    exact h.complexRealOrientation_basis N hr PUnit.unit bV
  let β := cohomologyThomClass ℚ (2 * N) F oF.rationalization
  let back : C(TM, TotalSpace R F) := ⟨G.symm, G.symm.continuous⟩
  have hpoint (w : TotalSpace R F) : w = ⟨PUnit.unit, w.snd⟩ := by
    rcases w with ⟨x, v⟩
    cases x
    rfl
  have hBA : Set.MapsTo back ({z₀}ᶜ : Set TM) (bundleNonzero (2 * N) F) := by
    intro z hz hzero
    have hw : back z = w₀ := (hpoint (back z)).trans
      (congrArg (fun v : V ↦ (⟨PUnit.unit, v⟩ : TotalSpace R F)) hzero)
    exact hz ((G.apply_symm_apply z).symm.trans (congrArg G hw))
  let α := relativeSingularCohomologyPullback ℚ back hBA (2 * N) β
  let l : C(R, F PUnit.unit) := ⟨L, L.continuous⟩
  have hl : Set.MapsTo l {v : R | v ≠ 0} {v : F PUnit.unit | v ≠ 0} :=
    fun _ hv hz ↦ hv (L.injective (hz.trans L.map_zero.symm))
  have hα : relativeSingularCohomologyPullback ℚ p hpA (2 * N) α =
      relativeSingularCohomologyRationalization {v : R | v ≠ 0} (2 * N)
        (realOrientationClass bR bR.orientation) := by
    have hcomp : back.comp p = (bundleFiberInclusion (2 * N) F PUnit.unit).comp l := by
      apply ContinuousMap.ext
      intro v
      exact G.symm_apply_apply _
    have hfiber : relativeSingularCohomologyPullback ℚ
        (bundleFiberInclusion (2 * N) F PUnit.unit)
        (A := {v : F PUnit.unit | v ≠ 0}) (B := bundleNonzero (2 * N) F)
        (fun _ hv ↦ hv) (2 * N) β = oF.rationalization.fiberClass PUnit.unit :=
      (existsUnique_cohomologyThomClass ℚ (2 * N) F
        oF.rationalization).exists.choose_spec PUnit.unit
    have hcomp₁ := congrArg (fun T ↦ T β)
      (relativeSingularCohomologyPullback_comp ℚ p back hpA hBA (2 * N))
    have hcomp₂ := congrArg (fun T ↦ T β)
      (relativeSingularCohomologyPullback_comp ℚ l
        (bundleFiberInclusion (2 * N) F PUnit.unit) hl
        (B := {v : F PUnit.unit | v ≠ 0}) (C := bundleNonzero (2 * N) F)
        (fun _ hv ↦ hv) (2 * N))
    have hmaps (f g : C(R, TotalSpace R F)) (hfg : f = g)
        (hf : Set.MapsTo f {v : R | v ≠ 0} (bundleNonzero (2 * N) F))
        (hg : Set.MapsTo g {v : R | v ≠ 0} (bundleNonzero (2 * N) F)) :
        relativeSingularCohomologyPullback ℚ f hf (2 * N) =
          relativeSingularCohomologyPullback ℚ g hg (2 * N) := by
      subst g
      rfl
    refine hcomp₁.symm.trans ((congrArg (fun T ↦ T β) (hmaps _ _ hcomp _ _)).trans
      (hcomp₂.trans ?_))
    change relativeSingularCohomologyPullback ℚ l hl (2 * N)
      (relativeSingularCohomologyPullback ℚ (bundleFiberInclusion (2 * N) F PUnit.unit)
        (A := {v : F PUnit.unit | v ≠ 0}) (B := bundleNonzero (2 * N) F)
        (fun _ hv ↦ hv) (2 * N) β) = _
    rw [hfiber]
    have hi : relativeSingularCohomologyPullback ℤ l hl (2 * N)
        (oF.fiberClass PUnit.unit) = realOrientationClass bR bR.orientation := by
      have hF : oF.fiberClass PUnit.unit =
          realOrientationClass (complexBasisRealification bV)
            (h.complexRealOrientation N hr PUnit.unit) :=
        geometricCohomologyOrientation_fiberClass (2 * N) F (h.complexRealOrientation N hr)
          (h.complexRealOrientation_locally_compatible N hr) PUnit.unit
          (complexBasisRealification bV)
      rw [hF]
      exact realOrientationClass_pullback bR bR.orientation (complexBasisRealification bV)
        (h.complexRealOrientation N hr PUnit.unit) L hLorientation
    exact (relativeSingularCohomologyRationalization_naturality l hl (2 * N)
      (oF.fiberClass PUnit.unit)).symm.trans
        (congrArg (relativeSingularCohomologyRationalization {v : R | v ≠ 0} (2 * N)) hi)
  have hevaluation : (singularCochainHomologyEvaluation ℚ
      (relativeSingularChains ℚ ({z₀}ᶜ : Set TM)) (2 * N) α
      (relativeSingularHomologyRationalization ({z₀}ᶜ : Set TM) (2 * N)
        (O.localGenerator z₀ 1))).down = 1 := by
    rw [← hcanonical, singularCochainHomologyEvaluation_rationalization_natural, hα,
      singularCochainHomologyEvaluation_rationalization]
    have he := realOrientationClass_evaluation bR bR.orientation
    rw [realOrientationEvaluation, relativeSingularCapProduct_augmentation] at he
    exact congrArg (fun z : ℤ ↦ (z : ℚ)) he
  let a := compactSupportCohomologyClass ℚ TM ⟨{z₀}, isCompact_singleton⟩ (2 * N) α
  have haIntegral : compactSupportCohomologyIntegral O a = 1 :=
    (compactSupportCohomologyIntegral_singleton O z₀ α).trans hevaluation
  -- The same point representative pulls back to the original zero-section Thom class.
  let g : C(TotalSpace R F, TM) := ⟨G, G.continuous⟩
  let K := properCompactPreimage g G.isProperMap ⟨{z₀}, isCompact_singleton⟩
  have hK : K = cohomologyZeroSectionSupport (2 * N) F := by
    apply TopologicalSpace.Compacts.ext
    ext w
    change G w = z₀ ↔ w.snd = 0
    constructor
    · intro hw
      exact congrArg (fun z : TotalSpace R F ↦ (z.snd : V)) (G.injective hw)
    · intro hw
      exact congrArg G ((hpoint w).trans
        (congrArg (fun v : V ↦ (⟨PUnit.unit, v⟩ : TotalSpace R F)) hw))
  have hKc : ((K : Set (TotalSpace R F))ᶜ) = bundleNonzero (2 * N) F :=
    congrArg (fun A : TopologicalSpace.Compacts (TotalSpace R F) ↦
      (A : Set (TotalSpace R F))ᶜ) hK
  have hGa : compactSupportCohomologyHomeomorphPullback ℚ G (2 * N) a =
      compactSupportCohomologyThomClass ℚ (2 * N) F oF.rationalization := by
    have hcastClass (K₁ K₂ : TopologicalSpace.Compacts (TotalSpace R F)) (h : K₁ = K₂)
        (x : relativeSingularCohomology ℚ (K₁ : Set (TotalSpace R F))ᶜ (2 * N)) :
        compactSupportCohomologyClass ℚ (TotalSpace R F) K₁ (2 * N) x =
          compactSupportCohomologyClass ℚ (TotalSpace R F) K₂ (2 * N)
            ((eqToIso (congrArg (fun A : TopologicalSpace.Compacts (TotalSpace R F) ↦
              relativeSingularCohomology ℚ (A : Set (TotalSpace R F))ᶜ (2 * N)) h)).hom x) := by
      subst K₂
      rfl
    have hgK : Set.MapsTo g (K : Set (TotalSpace R F))ᶜ ({z₀}ᶜ : Set TM) :=
      fun _ hx ↦ hx
    rw [← compactSupportCohomologyProperPullback_homeomorph]
    change compactSupportCohomologyProperPullback ℚ g G.isProperMap (2 * N)
      (compactSupportCohomologyClass ℚ TM ⟨{z₀}, isCompact_singleton⟩ (2 * N) α) = _
    rw [compactSupportCohomologyProperPullback_representative,
      hcastClass K (cohomologyZeroSectionSupport (2 * N) F) hK]
    apply congrArg (compactSupportCohomologyClass ℚ (TotalSpace R F)
      (cohomologyZeroSectionSupport (2 * N) F) (2 * N))
    have hcastPull {A₁ A₂ : Set (TotalSpace R F)} (hA : A₁ = A₂)
        (j : C(TotalSpace R F, TotalSpace R F))
        (h₁ : Set.MapsTo j A₁ (bundleNonzero (2 * N) F))
        (h₂ : Set.MapsTo j A₂ (bundleNonzero (2 * N) F)) :
        (eqToIso (congrArg (fun A : Set (TotalSpace R F) ↦
          relativeSingularCohomology ℚ A (2 * N)) hA)).hom
            (relativeSingularCohomologyPullback ℚ j h₁ (2 * N) β) =
          relativeSingularCohomologyPullback ℚ j h₂ (2 * N) β := by
      subst A₂
      rfl
    have hbackid : back.comp g = ContinuousMap.id (TotalSpace R F) := by
      apply ContinuousMap.ext
      intro w
      exact G.symm_apply_apply w
    have hbg : Set.MapsTo (back.comp g) (bundleNonzero (2 * N) F)
        (bundleNonzero (2 * N) F) := by
      intro w hw
      change (G.symm (G w)).snd ≠ 0
      intro hz
      exact hw ((congrArg (fun z : TotalSpace R F ↦ (z.snd : V))
        (G.symm_apply_apply w)).symm.trans hz)
    have hcomp := congrArg (fun T ↦ T β)
      (relativeSingularCohomologyPullback_comp ℚ g back hgK hBA (2 * N))
    have hc : (eqToIso (congrArg (fun A : Set (TotalSpace R F) ↦
        relativeSingularCohomology ℚ A (2 * N)) hKc)).hom
          (relativeSingularCohomologyPullback ℚ g hgK (2 * N) α) =
        relativeSingularCohomologyPullback ℚ (back.comp g) hbg (2 * N) β :=
      (congrArg (fun x ↦ (eqToIso (congrArg (fun A : Set (TotalSpace R F) ↦
        relativeSingularCohomology ℚ A (2 * N)) hKc)).hom x) hcomp.symm).trans
          (hcastPull hKc (back.comp g) _ hbg)
    refine hc.trans ?_
    have hmaps (f g : C(TotalSpace R F, TotalSpace R F)) (hfg : f = g)
        (hf : Set.MapsTo f (bundleNonzero (2 * N) F) (bundleNonzero (2 * N) F))
        (hg : Set.MapsTo g (bundleNonzero (2 * N) F) (bundleNonzero (2 * N) F)) :
        relativeSingularCohomologyPullback ℚ f hf (2 * N) =
          relativeSingularCohomologyPullback ℚ g hg (2 * N) := by
      subst g
      rfl
    have hchains : relativeSingularChainsMap ℚ (ContinuousMap.id (TotalSpace R F))
        (show Set.MapsTo (ContinuousMap.id (TotalSpace R F)) (bundleNonzero (2 * N) F)
          (bundleNonzero (2 * N) F) from fun _ hx ↦ hx) = 𝟙 _ := by
      apply (cancel_epi (relativeSingularChainsProjection ℚ (bundleNonzero (2 * N) F))).mp
      simp [relativeSingularChainsMap, relativeSingularChainsProjection, Limits.cokernel.map]
    have hid : relativeSingularCohomologyPullback ℚ (ContinuousMap.id (TotalSpace R F))
        (show Set.MapsTo (ContinuousMap.id (TotalSpace R F)) (bundleNonzero (2 * N) F)
          (bundleNonzero (2 * N) F) from fun _ hx ↦ hx) (2 * N) = 𝟙 _ := by
      let H := singularCochainDualFunctor ℚ ⋙
        HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) (2 * N)
      change H.map (relativeSingularChainsMap ℚ (ContinuousMap.id (TotalSpace R F)) _).op = _
      rw [hchains]
      exact H.map_id _
    exact congrArg (fun T ↦ T β) ((hmaps _ _ hbackid hbg (fun _ hx ↦ hx)).trans hid)
  have hcEq : c = k • (-1 : ℚ) ^ N • a := by
    apply (compactSupportCohomologyHomeomorphEquiv ℚ G (2 * N)).injective
    change compactSupportCohomologyHomeomorphPullback ℚ G (2 * N) c =
      compactSupportCohomologyHomeomorphPullback ℚ G (2 * N) (k • (-1 : ℚ) ^ N • a)
    rw [map_zsmul, map_smul, hGa]
    exact hGclass
  -- Rational linearity extracts the Bott coordinate and the two equal signs cancel.
  change (k : ℚ) = (-1 : ℚ) ^ N * compactSupportCohomologyIntegral O c
  clear_value k
  rw [hcEq, map_zsmul, map_smul, haIntegral]
  simp only [zsmul_eq_mul, smul_eq_mul, mul_one]
  have hsign : (-1 : ℚ) ^ N * (-1 : ℚ) ^ N = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  calc
    (k : ℚ) = (k : ℚ) * ((-1 : ℚ) ^ N * (-1 : ℚ) ^ N) := by rw [hsign, mul_one]
    _ = (-1 : ℚ) ^ N * ((k : ℚ) * (-1 : ℚ) ^ N) := by ring

end AtiyahSinger
