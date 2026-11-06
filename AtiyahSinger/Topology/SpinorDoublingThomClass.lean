/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinorDoublingParitySymbol
public import AtiyahSinger.Geometry.SpinorParitySquare
public import AtiyahSinger.Topology.ComplexificationHermitianMetric
public import AtiyahSinger.Topology.ComplexificationProductMap
public import AtiyahSinger.Topology.ComplexificationTensorPullback
public import AtiyahSinger.Topology.ExteriorParityThomClass
public import AtiyahSinger.Topology.HermitianSupportedThom
public import AtiyahSinger.Topology.SkewExternalProduct
public import AtiyahSinger.Topology.SpinorTensorExteriorParity
public import AtiyahSinger.Topology.ThomTensorReassociation

/-!
# The supported self-tensor identity of the original spin symbol

Public module ID: M2177.

The actual real/imaginary proper map restricts the external square to one base.
The corrected doubling isomorphism identifies its actual symbol with exterior
Clifford multiplication, with the prescribed parity shift. All tensor factors,
zero controls and metrics are retained through these comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct


private theorem congr_pullback_boundary
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {A B : X → Type*} [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
    [TopologicalSpace (TotalSpace Unit A)] [∀ x, AddCommGroup (B x)]
    [∀ x, Module ℂ (B x)] [TopologicalSpace (TotalSpace Unit B)]
    {G H : Y → Type*} [∀ y, AddCommGroup (G y)] [∀ y, Module ℂ (G y)]
    [TopologicalSpace (TotalSpace Unit G)] [∀ y, AddCommGroup (H y)]
    [∀ y, Module ℂ (H y)] [TopologicalSpace (TotalSpace Unit H)]
    (a : CompactSupportTriple A B) (f : C(Y, X)) (hf : IsProperMap f)
    (i : Iso ((f : Y → X) *ᵖ A) G) (j : Iso ((f : Y → X) *ᵖ B) H)
    (y : ((f ⁻¹' a.control)ᶜ : Set Y)) (v : G y) :
    ((a.pullback f hf).congr i j).boundary.linearEquiv y v =
      j.linearEquiv y (a.boundary.linearEquiv ⟨f y, y.property⟩
        ((i.linearEquiv y).symm v)) := by
  refine (CompactSupportTriple.congr_apply (a.pullback f hf) i j y v).trans ?_
  exact congrArg (j.linearEquiv y) (RelativeTriple.pullback_apply a.boundary f y _)


private theorem congr_pullback_class
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
    {A B : X → Type*} [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
    [TopologicalSpace (TotalSpace Unit A)] [∀ x, AddCommGroup (B x)]
    [∀ x, Module ℂ (B x)] [TopologicalSpace (TotalSpace Unit B)]
    {G H : Y → Type*} [∀ y, AddCommGroup (G y)] [∀ y, Module ℂ (G y)]
    [TopologicalSpace (TotalSpace Unit G)] [∀ y, AddCommGroup (H y)]
    [∀ y, Module ℂ (H y)] [TopologicalSpace (TotalSpace Unit H)]
    [IsFiniteRank A] [IsFiniteRank B] [IsFiniteRank G] [IsFiniteRank H]
    (a : CompactSupportTriple A B) (f : C(Y, X)) (hf : IsProperMap f)
    (i : Iso ((f : Y → X) *ᵖ A) G) (j : Iso ((f : Y → X) *ᵖ B) H) :
    letI := isFiniteRank_pullback (E := A) f
    letI := isFiniteRank_pullback (E := B) f
    ((a.pullback f hf).congr i j).compactSupportClass =
      compactSupportKZeroPullback f hf a.compactSupportClass := by
  let := isFiniteRank_pullback (E := A) f
  let := isFiniteRank_pullback (E := B) f
  exact (CompactSupportTriple.compactSupportClass_congr (a.pullback f hf) i j).trans
    (CompactSupportTriple.compactSupportClass_pullback a f hf)

private theorem exists_congr_pullback_triple
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
    {A B : X → Type*} [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
    [TopologicalSpace (TotalSpace Unit A)] [∀ x, AddCommGroup (B x)]
    [∀ x, Module ℂ (B x)] [TopologicalSpace (TotalSpace Unit B)]
    {G H : Y → Type*} [∀ y, AddCommGroup (G y)] [∀ y, Module ℂ (G y)]
    [TopologicalSpace (TotalSpace Unit G)] [∀ y, AddCommGroup (H y)]
    [∀ y, Module ℂ (H y)] [TopologicalSpace (TotalSpace Unit H)]
    [IsFiniteRank A] [IsFiniteRank B] [IsFiniteRank G] [IsFiniteRank H]
    (a : CompactSupportTriple A B) (f : C(Y, X)) (hf : IsProperMap f)
    (i : Iso ((f : Y → X) *ᵖ A) G) (j : Iso ((f : Y → X) *ᵖ B) H) :
    ∃ (b : CompactSupportTriple G H) (hc : b.control = f ⁻¹' a.control),
      (∀ (y : (b.controlᶜ : Set Y)) (v : G y),
        b.boundary.linearEquiv y v = j.linearEquiv y
          (a.boundary.linearEquiv ⟨f y, by
            change y.val ∉ f ⁻¹' a.control
            rw [← hc]
            exact y.property⟩ ((i.linearEquiv y).symm v))) ∧
      b.compactSupportClass = compactSupportKZeroPullback f hf a.compactSupportClass := by
  let := isFiniteRank_pullback (E := A) f
  let := isFiniteRank_pullback (E := B) f
  refine ⟨(a.pullback f hf).congr i j, rfl, ?_, congr_pullback_class a f hf i j⟩
  intro y v
  exact congr_pullback_boundary a f hf i j y v

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum isFiniteRank_pullback
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity
  t2Space_totalSpace locallyCompactSpace_totalSpace


set_option maxHeartbeats 800000 in
-- Normalize the pulled-back exterior metrics and support maps in this comparison.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem exteriorParity_class_eq_supportedThom
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (h₀ hV : ContinuousHermitianMetric E) (m : ℕ) :
    letI : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h₀.toCore x).toNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
      InnerProductSpace.ofCore (h₀.toCore x).toCore
    let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
    let P (i : ZMod 2) : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
    ∀ (a : CompactSupportTriple (p *ᵖ (P (m : ZMod 2))) (p *ᵖ (P ((m : ZMod 2) + 1))))
      (_hcontrol : a.control = {z | z.snd = 0})
      (_hsymbol : ∀ (z : (a.controlᶜ : Set (TotalSpace Unit E))) v,
        a.boundary.linearEquiv z v = cliffordSymbolParity z.val.snd (m : ZMod 2) v),
      a.compactSupportClass = (-1 : ℤ) ^ m • hV.supportedThomHom
        ((compactSupportKZeroCompactEquiv X).symm
          (AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1))) := by
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h₀.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (h₀.toCore x).toCore
  dsimp only
  intro a hcontrol hsymbol
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let oneK := AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)
  have hsign : (if (m : ZMod 2) = 0 then (1 : ℤ) else -1) = (-1 : ℤ) ^ m := by
    simp only [ZMod.natCast_eq_zero_iff_even, neg_one_pow_eq_ite]
  have hparity := compactSupportClass_exteriorParity E h₀.continuous_pairing
    (m : ZMod 2) a hcontrol hsymbol
  have hunit : h₀.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm oneK) =
      exteriorThomClass E h₀.continuous_pairing := by
    change ComplexBundle.supportedThomHom E h₀.continuous_pairing _ = _
    rw [supportedThomHom_compact, AddMonoidHom.comp_apply]
    rw [show (compactSupportKZeroCompactEquiv X).toAddMonoidHom
      ((compactSupportKZeroCompactEquiv X).symm oneK) = oneK from
        (compactSupportKZeroCompactEquiv X).apply_symm_apply oneK]
    exact complexKZeroCompactSupportAction_one p _
  have hmetric : h₀.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm oneK) =
      hV.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm oneK) :=
    congrArg (fun f : CompactSupportKZero X →+ CompactSupportKZero (TotalSpace Unit E) ↦
      f ((compactSupportKZeroCompactEquiv X).symm oneK))
        (ContinuousHermitianMetric.supportedThomHom_eq h₀ hV)
  exact hparity.trans
    ((congrArg (fun z : ℤ ↦ z • exteriorThomClass E h₀.continuous_pairing) hsign).trans
      (congrArg (fun z : CompactSupportKZero (TotalSpace Unit E) ↦ (-1 : ℤ) ^ m • z)
        (hunit.symm.trans hmetric)))

variable {m : ℕ} {B P : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
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
local notation "SpinPlus" => HalfSpinorBundle m hP (0 : ZMod 2)
local notation "SpinMinus" => HalfSpinorBundle m hP (1 : ZMod 2)
local notation "VectorProjection" => (π RealModel E)
local notation "ZeroSet" => Set.range (zeroSection RealModel E)

variable [CompactSpace B] [T2Space B]

set_option maxHeartbeats 4000000 in
-- Normalize both spinor tensor bundles and the same complexification Thom map.
set_option maxRecDepth 4096 in
set_option synthInstance.maxHeartbeats 100000 in

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual supported self-tensor spin symbol is the signed exterior Thom class. -/
theorem TopologicalSpinStructure.spinorThomClass_self_product
    (S : TopologicalSpinStructure m E o hm hP)
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun b ↦ ℂ ⊗[ℝ] E b)) :
    letI := complexificationTopology RealModel E
    letI := isFiniteRank_complexification RealModel E
    compactSupportKZeroPullback (complexificationProductMap RealModel E)
        (isProperMap_complexificationProductMap RealModel E)
        (compactSupportKZeroExternalProduct S.spinorThomClass S.spinorThomClass) =
      (-1 : ℤ) ^ m • hV.supportedThomHom
        ((compactSupportKZeroCompactEquiv B).symm
          (AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1))) := by
  classical
  let C (b : B) := ℂ ⊗[ℝ] E b
  let H := HalfSpinorBundle m hP
  let TE := TotalSpace RealModel E
  let TC := TotalSpace Unit C
  let := complexificationTopology RealModel E
  let := isFiniteRank_complexification RealModel E
  let h₀ := complexificationHermitianMetric (R := RealModel) (E := E)
  let (i : ZMod 2) := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m i)
    (continuous_complexSpinParityRepresentation m i)
  let πE : C(TE, B) := ⟨VectorProjection, FiberBundle.continuous_proj RealModel E⟩
  let πC : C(TC, B) := ⟨π Unit C, continuous_proj⟩
  let A := πE *ᵖ (H 0)
  let F := πE *ᵖ (H 1)
  let := isFiniteRank_pullback (E := H 0) πE
  let := isFiniteRank_pullback (E := H 1) πE
  let c : Hom A F := S.cliffordParityHom 0
  let c' : Hom F A := S.cliffordParityHom 1
  have hcvalue (z : TE) : c.linearMap z = S.cliffordParity z.proj z.snd 0 := rfl
  have hcvalue' (z : TE) : c'.linearMap z = S.cliffordParity z.proj z.snd 1 := rfl
  let r (z : TE) : ℝ := ‖z.snd‖ ^ 2
  have hc : ∀ z : (S.spinorSymbolTriple.controlᶜ : Set TE),
      (S.spinorSymbolTriple.boundary.linearEquiv z).toLinearMap = c.linearMap z.val :=
    fun _ ↦ rfl
  have hsq (z : TE) : (c'.linearMap z).comp (c.linearMap z) = -(r z : ℂ) • LinearMap.id ∧
      (c.linearMap z).comp (c'.linearMap z) = -(r z : ℂ) • LinearMap.id := by
    constructor
    · apply LinearMap.ext
      intro v
      change S.cliffordParity z.proj z.snd 1 (S.cliffordParity z.proj z.snd 0 v) =
        -((‖z.snd‖ ^ 2 : ℝ) : ℂ) • v
      rw [Complex.ofReal_pow]
      exact S.cliffordParity_one_zero z.proj z.snd v
    · apply LinearMap.ext
      intro v
      change S.cliffordParity z.proj z.snd 0 (S.cliffordParity z.proj z.snd 1 v) =
        -((‖z.snd‖ ^ 2 : ℝ) : ℂ) • v
      rw [Complex.ofReal_pow]
      exact S.cliffordParity_zero_one z.proj z.snd v
  have hpos (z : TE) (hz : z ∉ S.spinorSymbolTriple.control) : 0 < r z := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hzero
    apply hz
    refine ⟨z.proj, ?_⟩
    change TotalSpace.mk z.proj 0 = z
    rw [← hzero]
  -- The skew-symbol comparison represents the external square with product control.
  obtain ⟨k, hk, hboundary, hclass⟩ :=
    S.spinorSymbolTriple.exists_skewExternalProduct S.spinorSymbolTriple c c' c c'
      r r hc hc hsq hsq (fun z ↦ sq_nonneg _) (fun z ↦ sq_nonneg _) hpos hpos
  let Q : C(TC, TE × TE) := complexificationProductMap RealModel E
  have hQ : IsProperMap Q := isProperMap_complexificationProductMap RealModel E
  let (i j : ZMod 2) := isFiniteRank_tensor (E := H i) (F := H j)
  let (j : ZMod 2) := exteriorParityTopology (E := C) j
  obtain ⟨r₀, r₁, hr₀, hr₁⟩ := exists_complexificationTensorPullback_iso RealModel E H
  obtain ⟨e, he⟩ := exists_complexSpinor_invariantDuality m
  obtain ⟨d₀, d₁, hd⟩ := S.exists_spinorTensor_exteriorParity_symbol_iso e he
  -- The second even summand has the explicit minus sign of the positive reciprocal convention.
  let N : Iso (fun b ↦ H 1 b ⊗[ℂ] H 1 b) (fun b ↦ H 1 b ⊗[ℂ] H 1 b) :=
    Iso.scalar _ (ContinuousMap.const _ (-1)) (fun _ ↦ neg_ne_zero.mpr one_ne_zero)
  let D₀ := ((Iso.refl (fun b ↦ H 0 b ⊗[ℂ] H 0 b)).sum N).trans d₀
  have hD₀ (b : B) (v : (H 0 b ⊗[ℂ] H 0 b) × (H 1 b ⊗[ℂ] H 1 b)) :
      D₀.linearEquiv b v = d₀.linearEquiv b (v.1, -v.2) := by
    change d₀.linearEquiv b (v.1, (-1 : ℂ) • v.2) = _
    exact congrArg (fun w ↦ d₀.linearEquiv b (v.1, w)) (neg_one_smul ℂ v.2)
  clear_value D₀
  let I₀ := r₀.trans (D₀.pullback πC)
  let I₁ := r₁.trans (d₁.pullback πC)
  have hI₀ (z : TC) (v : (H 0 z.proj ⊗[ℂ] H 0 z.proj) ×
      (H 1 z.proj ⊗[ℂ] H 1 z.proj)) :
      I₀.linearEquiv z v = d₀.linearEquiv z.proj (v.1, -v.2) := by
    change D₀.linearEquiv z.proj (r₀.linearEquiv z v) = _
    exact (congrArg (D₀.linearEquiv z.proj) (hr₀ z v)).trans (hD₀ z.proj v)
  have hI₁ (z : TC) (v : (H 1 z.proj ⊗[ℂ] H 0 z.proj) ×
      (H 0 z.proj ⊗[ℂ] H 1 z.proj)) :
      I₁.linearEquiv z v = d₁.linearEquiv z.proj v := by
    change d₁.linearEquiv z.proj (r₁.linearEquiv z v) = _
    exact congrArg (d₁.linearEquiv z.proj) (hr₁ z v)
  -- The remaining comparison uses only these fiber formulas, not the composite constructions.
  clear_value I₀ I₁
  obtain ⟨a, hpreimage, haboundary, ha₀⟩ := exists_congr_pullback_triple k Q hQ I₀ I₁
  have ha : a.compactSupportClass = compactSupportKZeroPullback Q hQ
      (compactSupportKZeroExternalProduct S.spinorThomClass S.spinorThomClass) :=
    ha₀.trans (congrArg (compactSupportKZeroPullback Q hQ) hclass)
  have hcontrol : a.control = {z : TC | z.snd = 0} := by
    refine hpreimage.trans ((congrArg (fun t : Set (TE × TE) ↦ Q ⁻¹' t) hk).trans ?_)
    have hzero (z : TE) : z ∈ S.spinorSymbolTriple.control ↔ z.snd = 0 := by
      constructor
      · rintro ⟨b, rfl⟩
        rfl
      · intro hz
        refine ⟨z.proj, ?_⟩
        change TotalSpace.mk z.proj 0 = z
        rw [← hz]
    ext z
    change (Q z).1 ∈ S.spinorSymbolTriple.control ∧
      (Q z).2 ∈ S.spinorSymbolTriple.control ↔ z.snd = 0
    rw [hzero, hzero]
    change (complexificationReIm (E z.proj) z.snd).1 = 0 ∧
      (complexificationReIm (E z.proj) z.snd).2 = 0 ↔ z.snd = 0
    constructor
    · intro hz
      apply (complexificationReIm (E z.proj)).injective
      rw [map_zero]
      exact Prod.ext hz.1 hz.2
    · intro hz
      rw [hz, map_zero]
      exact ⟨rfl, rfl⟩
  -- Use the canonical extension for the symbol comparison; metric independence is applied last.
  let : ∀ b, NormedAddCommGroup (C b) := fun b ↦ (h₀.toCore b).toNormedAddCommGroup
  let : ∀ b, InnerProductSpace ℂ (C b) := fun b ↦
    InnerProductSpace.ofCore (h₀.toCore b).toCore
  have hsymbol : ∀ (z : (a.controlᶜ : Set TC)) v,
      a.boundary.linearEquiv z v = cliffordSymbolParity z.val.snd (m : ZMod 2) v := by
    intro z v
    refine (haboundary z v).trans ?_
    let u : (H 0 z.val.proj ⊗[ℂ] H 0 z.val.proj) ×
        (H 1 z.val.proj ⊗[ℂ] H 1 z.val.proj) := (I₀.linearEquiv z.val).symm v
    refine (hI₁ z.val _).trans ?_
    let zQ : (k.controlᶜ : Set (TE × TE)) := ⟨Q z.val, by
      change z.val ∉ Q ⁻¹' k.control
      rw [← hpreimage]
      exact z.property⟩
    have hkvalue := LinearMap.congr_fun (hboundary zQ) u
    change k.boundary.linearEquiv zQ u = _ at hkvalue
    refine (congrArg (d₁.linearEquiv z.val.proj) hkvalue).trans ?_
    let vR := (complexificationReIm (E z.val.proj) z.val.snd).1
    let vI := (complexificationReIm (E z.val.proj) z.val.snd).2
    simp only [hcvalue, hcvalue']
    refine (hd z.val.proj vR vI u).trans ?_
    have hvector : (1 : ℂ) ⊗ₜ[ℝ] vR + Complex.I ⊗ₜ[ℝ] vI = z.val.snd := by
      rw [← (complexificationReIm_properties (E z.val.proj)).2.1]
      exact (complexificationReIm (E z.val.proj)).symm_apply_apply z.val.snd
    have hu : d₀.linearEquiv z.val.proj (u.1, -u.2) = v :=
      (hI₀ z.val u).symm.trans ((I₀.linearEquiv z.val).apply_symm_apply v)
    exact (congrArg (fun ξ : C z.val.proj ↦ cliffordSymbolParity ξ (m : ZMod 2)
      (d₀.linearEquiv z.val.proj (u.1, -u.2))) hvector).trans
        (congrArg (cliffordSymbolParity z.val.snd (m : ZMod 2)) hu)
  -- The symbol comparison has fixed this metric; class-level arguments now use only its axioms.
  clear_value h₀
  exact ha.symm.trans
    (exteriorParity_class_eq_supportedThom C h₀ hV m a hcontrol hsymbol)

end AtiyahSinger
