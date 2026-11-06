/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasDifferentialIndex
public import AtiyahSinger.Analysis.TwistedSpinSymbolClass
public import AtiyahSinger.Geometry.SpinDiracCharacteristic

/-!
# The index of the actual twisted positive spin Dirac operator

Public module ID: M1039.

T04, Lawson--Michelsohn, Spin Geometry III.13.10, formula (13.26).
On the original closed Riemannian spin manifold of dimension 2m, use the
original quotient half-spin bundles and any specified smooth complex connection
on W. The index is that of the actual product-connection contraction D+.
This extends the book's unitary case: the connection changes only lower-order terms.
Its characteristic number is the degree-2m part of ch(W) cup A-hat(TM),
evaluated in the integral orientation induced by that same spin frame lift.

The auxiliary hV only computes the existing topological A-hat components;
the metric on TM and the Levi-Civita connection remain precisely g. The
standard finite convolution is expanded on the original W by
spinDiracCharacteristicClass_bundle. No connectedness, global coefficient
rank, four-divisibility or extra desired symbol equality is assumed.
The native zero-dimensional continuation is stated in ZeroTwistedSpinIndex.
The proof retains the same differential operator, musical transport, spin Thom class
and integral orientation through the general base characteristic formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology ComplexBundle.isFiniteRank_tensor
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_cotangent locallyCompactSpace_cotangent

set_option maxSynthPendingDepth 40

variable {m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m}
  {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))
  {W : M → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 2 * m) W) (covW : AtlasComplexConnection B)

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => (TangentSpace I : M → Type _)
local notation "TModel" => EuclideanSpace ℝ (Fin (2 * m))

namespace TopologicalSpinStructure

set_option maxHeartbeats 3000000 in
-- The extended limit accommodates the same Dirac symbol, spin Thom class and characteristic-number
-- transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The twisted chiral spin index is the original ch(W) times A-hat characteristic number. -/
theorem twistedDiracPlus_index
    (hV : letI := complexificationTopology TModel TM
      ComplexBundle.ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TM x)) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle TModel TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    letI : IsContMDiffRiemannianBundle I ∞ TModel TM :=
      ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
    letI := B.isFiniteRank
    ∀ S : TopologicalSpinStructure m TM o hm hP,
      (((S.twistedDiracPlus g B covW).toLinearMap.index : ℤ) : ℚ) =
        compactManifoldCohomologyIntegral (S.homologicalOrientation g)
          (spinDiracCharacteristicClass hV (ComplexBundle.kZeroClass W)) := by
  /- Stage 1: retain S.twistedDiracPlus g B covW, whose actual derivative
  uses the same g Levi-Civita connection and covW. Any smooth complex
  connection covW has this same Clifford principal symbol; the unitary
  case is included without changing the operator. This symbol is elliptic
  by twistedDiracPlus_symbol_properties. The generic atlas differential
  Fredholm theorem supplies finite original kernel and cokernel and their
  comparison with the actual critical Sobolev extension. Thus the displayed
  index is the actual analytic index, not an unverified totalized value.
  Stage 2: apply AtlasDifferentialOperator.index_eq_base_characteristic_number
  to that same operator, g, hV and the induced S.homologicalOrientation g.
  Choose any smooth radial cotangent metric, used only to regularize its
  own polynomial; no replacement quantization or prescribed-class premise
  enters. The inverse tangentCotangentKZeroEquiv is exactly pullback along
  g.flatHomeomorph. twistedDiracPlus_symbolClass identifies this original
  symbol class with S.spinThomHom (ComplexBundle.kZeroClass W), including
  the fixed nonzero +i phase and the original positive chirality.
  Stage 3: baseIndexCharacteristicClass_spinThom compares the same tangent
  integral with the spin-normalized Thom inverse and cancels the inverse
  A-hat against one factor of A-hat squared. Its class is precisely
  (-1)^m times spinDiracCharacteristicClass hV [W]. Integral orientation
  agreement is a theorem of the original local generators, not a premise.
  Stage 4: linearity of the base pairing extracts this sign. Since
  (2*m)*(2*m+1)/2 = m*(2*m+1), its sum with m is even. Therefore the T03
  sign and spin Thom sign cancel for every m, including odd m. Expand the
  finite convolution is exactly the degree-2m component of
  ch(W) cup A-hat(TM), by the existing bundle comparison. No Euler-class
  cancellation or restriction to dimension divisible by four is used. -/
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle TModel TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContMDiffRiemannianBundle I ∞ TModel TM :=
    ⟨g.inner, g.contMDiff, fun _ _ _ ↦ rfl⟩
  let := B.isFiniteRank
  intro S
  let D := S.twistedDiracPlus g B covW
  let q : SmoothCotangentMetric (n := 2 * m) (M := M) :=
    Classical.choice SmoothCotangentMetric.nonempty
  have hi : D.IsElliptic := (S.twistedDiracPlus_symbol_properties g B covW).2
  have hsymbol := S.twistedDiracPlus_symbolClass g B covW
  change compactSupportKZeroPullback ⟨g.flatHomeomorph, g.flatHomeomorph.continuous⟩
    g.flatHomeomorph.isProperMap
    (atlasSymbolKClass _ _ D.principalSymbol D.isSmoothOffZeroAtlasSymbol_principalSymbol hi) =
      S.spinThomHom (ComplexBundle.kZeroClass W) at hsymbol
  change ((D.toLinearMap.index : ℤ) : ℚ) = _
  -- Apply the characteristic-number formula to the specified twisted Dirac operator.
  clear_value D
  have hindex := D.index_eq_base_characteristic_number (S.homologicalOrientation g) g hV q hi
  have hmusical (a : CompactSupportKZero (CotangentTotalSpace (n := 2 * m) (M := M))) :
      (tangentCotangentKZeroEquiv g).symm a =
        compactSupportKZeroPullback ⟨g.flatHomeomorph, g.flatHomeomorph.continuous⟩
          g.flatHomeomorph.isProperMap a := by
    apply (tangentCotangentKZeroEquiv g).injective
    rw [AddEquiv.apply_symm_apply]
    change a = compactSupportKZeroHomeomorph g.flatHomeomorph
      (compactSupportKZeroHomeomorph g.flatHomeomorph.symm a)
    exact (DFunLike.congr_fun
      (compactSupportKZeroHomeomorph_symm g.flatHomeomorph.symm) a).symm
  have htransport : (tangentCotangentKZeroEquiv g).symm
      (atlasSymbolKClass _ _ D.principalSymbol D.isSmoothOffZeroAtlasSymbol_principalSymbol hi) =
        S.spinThomHom (ComplexBundle.kZeroClass W) := (hmusical _).trans hsymbol
  rw [htransport, S.baseIndexCharacteristicClass_spinThom g hV] at hindex
  let J := compactManifoldCohomologyIntegral (S.homologicalOrientation g)
  let c := spinDiracCharacteristicClass hV (ComplexBundle.kZeroClass W)
  change ((D.toLinearMap.index : ℤ) : ℚ) =
    (-1 : ℚ) ^ ((2 * m) * (2 * m + 1) / 2) * J ((-1 : ℚ) ^ m • c) at hindex
  change ((D.toLinearMap.index : ℤ) : ℚ) = J c
  clear_value J c
  have hscalar : J ((-1 : ℚ) ^ m • c) = (-1 : ℚ) ^ m * J c :=
    J.map_smul ((-1 : ℚ) ^ m) c
  -- The base-first Thom sign and the fixed positive-spin sign cancel in every even dimension.
  have hexponent : (2 * m) * (2 * m + 1) / 2 + m = 2 * (m * (m + 1)) := by
    rw [show (2 * m) * (2 * m + 1) = 2 * (m * (2 * m + 1)) by ring]
    rw [Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
    ring
  have hsign : (-1 : ℚ) ^ ((2 * m) * (2 * m + 1) / 2) * (-1 : ℚ) ^ m = 1 := by
    rw [← pow_add, hexponent, pow_mul]
    norm_num
  exact hindex.trans (by rw [hscalar, ← mul_assoc, hsign, one_mul])

end TopologicalSpinStructure

end AtiyahSinger
