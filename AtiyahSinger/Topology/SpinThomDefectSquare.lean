/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexBundleChernNative
public import AtiyahSinger.Topology.ComplexThomDefectDefinition
public import AtiyahSinger.Topology.ComplexificationChernSquare
public import AtiyahSinger.Topology.ComplexificationProductMap
public import AtiyahSinger.Topology.ProductCompactificationCohomology
public import AtiyahSinger.Topology.RealBundleChernAction
public import AtiyahSinger.Topology.RealBundleProductOnePoint
public import AtiyahSinger.Topology.SpinCohomologyOrientation
public import AtiyahSinger.Topology.SpinorDoublingThomClass
public import AtiyahSinger.Topology.SupportedCohomologyThomVanishing

/-!
# The square of the original real spin Thom coefficient

Public module ID: M2172.

The same supported spin self-product, actual real/imaginary proper map,
native total-space homeomorphism and original supported Chern character
identify its complex inverse Thom integral in two ways. The common
complexification sign cancels as an invertible rational scalar. Thus the
real Thom coefficients square to the original complex Thom defect.
No Euler class or nonunit cohomology class is cancelled.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_totalSpace locallyCompactSpace_totalSpace

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

local notation "RealModel" => EuclideanSpace ℝ (Fin (2 * m))

set_option maxHeartbeats 2000000 in
-- Normalize the supported spin cup square and its degree-shifted fiber integral.
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The self-convolution of the original real spin Thom coefficients is the complex Thom defect. -/
theorem TopologicalSpinStructure.fiberIntegral_chernCharacter_spinorThom_square
    (S : TopologicalSpinStructure m E o hm hP)
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (hr : ∀ x, Module.finrank ℂ (ℂ ⊗[ℝ] E x) = 2 * m) (j : ℕ) :
    letI := complexificationTopology RealModel E
    letI := isFiniteRank_complexification RealModel E
    let δ (n : ℕ) := compactSupportCohomologyFiberIntegral ℚ (2 * m) E
      S.integralCohomologyOrientation.rationalization (2 * n)
      ((eqToIso (by congr 1; omega) :
        compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * (m + n)) ≅
          compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * n + 2 * m)).hom
        (bundleCompactSupportChernCharacterComponent (2 * m) E (m + n) S.spinorThomClass))
    ∑ i : Fin (j + 1),
      (eqToIso (by congr 1; omega) :
        singularCohomology ℚ B (2 * (i.val + (j - i.val))) ≅
          singularCohomology ℚ B (2 * j)).hom
        (singularCohomologyEvenCup ℚ B i.val (j - i.val) (δ i.val) (δ (j - i.val))) =
      hV.complexThomDefectComponent (2 * m) hr j := by
  classical
  let F := fun x ↦ ℂ ⊗[ℝ] E x
  let := complexificationTopology RealModel E
  let := isFiniteRank_complexification RealModel E
  let : ∀ x, NormedAddCommGroup (F x) := hV.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hV.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (F x) := hV.realFiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
  let := hV.realNativeFiberBundle (2 * m) hr
  let := hV.realNativeVectorBundle (2 * m) hr
  let := hV.realNativeRiemannianBundle (2 * m) hr
  let : ∀ x, FiniteDimensional ℝ (F x) := fun x ↦
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin (2 * (2 * m)))) F x
  let : ∀ x, FiniteDimensional ℝ (E x) := fun x ↦
    VectorBundle.finiteDimensional ℝ RealModel E x
  let TE := TotalSpace RealModel E
  let TC := TotalSpace Unit F
  let TF := TotalSpace (EuclideanSpace ℝ (Fin (2 * (2 * m)))) F
  let eN := nativeModelTotalHomeomorph F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
  let fN : C(TF, TC) := ⟨eN, eN.continuous⟩
  let Q₀ := complexificationProductMap RealModel E
  let Q : C(TF, TE × TE) := Q₀.comp fN
  let q₁ := (ContinuousMap.fst : C(TE × TE, TE)).comp Q
  let q₂ := (ContinuousMap.snd : C(TE × TE, TE)).comp Q
  let e (x : B) : F x ≃L[ℝ] E x × E x :=
    (complexificationReIm (E x)).toContinuousLinearEquiv
  have he (x : B) : (e x).toLinearEquiv = complexificationReIm (E x) := rfl
  have hq₁ (x : B) (v : F x) : q₁ ⟨x, v⟩ = ⟨x, (e x v).1⟩ := rfl
  have hq₂ (x : B) (v : F x) : q₂ ⟨x, v⟩ = ⟨x, (e x v).2⟩ := rfl
  have hp : IsProperMap Q := (isProperMap_complexificationProductMap RealModel E).comp
    eN.isProperMap
  -- The detector is proved on the actual product of the two original real total spaces.
  have hdetect (k : ℕ) : Function.Injective (fun z : relativeSingularCohomology ℚ
      ({OnePoint.infty} : Set (OnePoint (TE × TE))) (2 * k) ↦
      singularCohomologyPullback ℚ onePointProductCollapseMap (2 * k)
        (relativeSingularCohomologyToOrdinary ℚ {OnePoint.infty} (2 * k) z)) :=
    singularCohomologyPullback_onePointProductCollapse_injective ℚ
      (cofinal_contractible_onePoint_complements_realBundle (2 * m) E)
      (cofinal_contractible_onePoint_complements_realBundle (2 * m) E) (2 * k)
      (compactSupportCohomologyToOnePoint_realBundleProd_bijective ℚ (2 * m) E (2 * k)).surjective
  have hvan (k : ℕ) (hk : k < m) :
      bundleCompactSupportChernCharacterComponent (2 * m) E k S.spinorThomClass = 0 :=
    (compactSupportCohomology_subsingleton_below_rank_of_orientation ℚ (2 * m) E
      S.integralCohomologyOrientation.rationalization (2 * k) (by omega)).elim _ _
  have hsquare := complexificationCohomologyFiberIntegral_chern_square E o
    S.isLocallyCompatibleBundleOrientation hV hr e he q₁ q₂ hq₁ hq₂ hp
      S.spinorThomClass hvan hdetect j
  let U := hV.supportedThomHom ((compactSupportKZeroCompactEquiv B).symm
    (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1)))
  -- First pull the same supported K identity through the actual native homeomorphism.
  have hK : compactSupportKZeroPullback Q hp
      (compactSupportKZeroExternalProduct S.spinorThomClass S.spinorThomClass) =
      (-1 : ℤ) ^ m • compactSupportKZeroPullback fN eN.isProperMap U := by
    rw [compactSupportKZeroPullback_comp fN Q₀ eN.isProperMap
      (isProperMap_complexificationProductMap RealModel E)]
    change compactSupportKZeroPullback fN eN.isProperMap
      (compactSupportKZeroPullback Q₀ _ _) = _
    rw [S.spinorThomClass_self_product hV, map_zsmul]
  have hcharacter : bundleCompactSupportChernCharacterComponent (2 * (2 * m)) F (2 * m + j)
      (compactSupportKZeroPullback Q hp
        (compactSupportKZeroExternalProduct S.spinorThomClass S.spinorThomClass)) =
      (-1 : ℤ) ^ m • compactSupportCohomologyHomeomorphPullback ℚ eN (2 * (2 * m + j))
        (hV.compactSupportChernCharacterComponent (2 * m) hr (2 * m + j) U) := by
    rw [hK, map_zsmul, hV.compactSupportChernCharacterComponent_native]
  let c {p q : ℕ} (h : p = q) : compactSupportCohomology ℚ TF p →ₗ[ℚ]
      compactSupportCohomology ℚ TF q :=
    (eqToIso (congrArg (compactSupportCohomology ℚ TF) h)).hom.hom
  have hcast (p q : ℕ) (h : p = q) (a : compactSupportCohomology ℚ TC p) :
      c h (compactSupportCohomologyHomeomorphPullback ℚ eN p a) =
      compactSupportCohomologyHomeomorphPullback ℚ eN q
        ((eqToIso (congrArg (compactSupportCohomology ℚ TC) h)).hom a) := by
    subst q
    rfl
  let I := compactSupportCohomologyFiberIntegral ℚ (2 * (2 * m)) F
    (hV.complexCohomologyOrientation (2 * m) hr).rationalization (2 * j)
  -- The definition of the original complex inverse uses exactly this native pullback.
  have hvalue : I (c (by omega)
      (bundleCompactSupportChernCharacterComponent (2 * (2 * m)) F (2 * m + j)
        (compactSupportKZeroPullback Q hp
          (compactSupportKZeroExternalProduct S.spinorThomClass S.spinorThomClass)))) =
      (-1 : ℚ) ^ m • hV.complexThomDefectComponent (2 * m) hr j := by
    rw [hcharacter, map_zsmul, map_zsmul, hcast _ _ (by omega)]
    change (-1 : ℤ) ^ m • hV.complexThomDefectComponent (2 * m) hr j = _
    rw [← Int.cast_smul_eq_zsmul ℚ]
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  have hsign : (-1 : ℚ) ^ m * (-1 : ℚ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  -- Multiply both paths by the same invertible scalar; no cohomology class is cancelled.
  have h := hvalue.symm.trans hsquare
  have h' := congrArg (fun a : singularCohomology ℚ B (2 * j) ↦ (-1 : ℚ) ^ m • a) h
  simpa only [TopologicalSpinStructure.integralCohomologyOrientation,
    smul_smul, hsign, one_smul] using h'.symm

end AtiyahSinger
