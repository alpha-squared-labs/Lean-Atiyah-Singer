/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportKMinusOneExactness
public import AtiyahSinger.Topology.HalfRayCompactification
public import AtiyahSinger.Topology.SuspendedKTheory

import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# The actual half-ray suspension comparison for automorphism K^{-1}

Public module ID: M1587.

Karoubi II.4.8 applies the preceding compactified five-term sequence to the
zero section in X × [0,∞). The two groups on the half-ray product vanish by a
pointed contraction of its actual compactification. The connecting map is
therefore bijective. We keep that same connecting map, the original zero-section
homeomorphism, and the increasing logarithmic coordinate on the complement.

This gives the specified group comparison with the existing real-suspension
carrier. Its identification with the clutching map of II.3.30 and with the
alpha-inverse-beta boundary of II.4.9 is proved in `ClutchingKTheoryComparison`.
Proper-map
naturality is stated explicitly; the source's larger category of all pointed
compactification maps is not claimed here. The two half-ray vanishing statements,
the specified suspension comparison, its proper naturality and the reflection
formula are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint
open scoped NNReal

/-- KA II.4.8: the compactly supported K-zero group of the half-ray product is zero. -/
theorem compactSupportKZero_halfRay_subsingleton (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] : Subsingleton (CompactSupportKZero (X × ℝ≥0)) := by
  /- Stage 1: use halfRayCompactificationHomotopy X on the actual compact Hausdorff
  compactification. Absolute K-zero homotopy invariance identifies identity
  pullback with pullback by the constant map at infinity.
  Stage 2: the latter factors through evaluation at infinity, hence vanishes on
  the defining reduced kernel. Identity is zero on that subgroup, so it is a
  subsingleton. Only ordinary homotopy invariance on the compactification is
  used; no proper-homotopy interpretation of its final constant map is needed.
  The construction also covers empty X. -/
  -- Contract the actual compactification, so ordinary homotopy invariance applies.
  let Y := OnePoint (X × ℝ≥0)
  have hid : complexKZeroPullback (ContinuousMap.id Y) =
      AddMonoidHom.id (ComplexKZero Y) := by
    change kZeroMap (RingHom.id _) = _
    exact kZeroMap_id
  have hhom := complexKZeroPullback_eq_of_homotopy
    (ContinuousMap.id Y) (ContinuousMap.const Y ∞) (halfRayCompactificationHomotopy X)
  -- Constant precomposition factors through the original evaluation at infinity.
  let ev : C(Y, ℂ) →+* ℂ := (ContinuousMap.evalAlgHom ℂ ℂ (∞ : Y)).toRingHom
  let const : ℂ →+* C(Y, ℂ) := algebraMap ℂ C(Y, ℂ)
  have hconst : complexKZeroPullback (ContinuousMap.const Y (∞ : Y)) =
      (kZeroMap const).comp (kZeroMap ev) := by
    rw [← kZeroMap_comp]
    rfl
  have hz (a : CompactSupportKZero (X × ℝ≥0)) : a = 0 := by
    apply Subtype.ext
    change a.val = 0
    have ha : kZeroMap ev a.val = 0 := a.property
    have heq := DFunLike.congr_fun hhom a.val
    rw [hid, hconst] at heq
    change a.val = kZeroMap const (kZeroMap ev a.val) at heq
    simpa only [ha, map_zero] using heq
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

namespace ComplexBundle

/-- KA II.4.8: the compactified automorphism kernel of the half-ray product is zero. -/
theorem compactSupportBundleKMinusOne_halfRay_subsingleton (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] :
    Subsingleton (CompactSupportBundleKMinusOne (X × ℝ≥0)) := by
  /- Stage 1: apply ordinary automorphism K-minus-one homotopy invariance to the
  explicit halfRayCompactificationHomotopy X. Its source and target are the same
  compact Hausdorff one-point compactification, not the noncompact product.
  Stage 2: constant pullback at infinity factors through restriction to that
  point, using the existing ordinary pullback composition law. It is zero on
  reducedBundleKMinusOne infinity. Identity pullback agrees with it, so every
  element of that original kernel is zero. No point-group vanishing, suspension
  isomorphism or later suspended closed-pair sequence is used. -/
  -- Apply homotopy invariance on the same compact Hausdorff compactification.
  let Y := OnePoint (X × ℝ≥0)
  have hhom := bundleKMinusOnePullback_eq_of_homotopic
    (ContinuousMap.id Y) (ContinuousMap.const Y ∞) ⟨halfRayCompactificationHomotopy X⟩
  -- The endpoint factors through the same PUnit evaluation defining the reduced kernel.
  let p : C(Y, PUnit.{1}) := ContinuousMap.const Y PUnit.unit
  let i : C(PUnit.{1}, Y) := ContinuousMap.const PUnit.{1} ∞
  have hconst : ContinuousMap.const Y (∞ : Y) = i.comp p := rfl
  have hz (a : CompactSupportBundleKMinusOne (X × ℝ≥0)) : a = 0 := by
    apply Subtype.ext
    change a.val = 0
    have ha : bundleKMinusOnePullback i a.val = 0 := a.property
    have heq := DFunLike.congr_fun hhom a.val
    rw [bundleKMinusOnePullback_id, hconst, bundleKMinusOnePullback_comp] at heq
    change a.val = bundleKMinusOnePullback p (bundleKMinusOnePullback i a.val) at heq
    simpa only [ha, map_zero] using heq
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

/-- The actual II.4.8 map: zero-section transport, its positive boundary, and logarithm. -/
def compactSupportBundleKMinusOneSuspension (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] :
    CompactSupportBundleKMinusOne X →+ CompactSupportKZero (X × ℝ) :=
  letI := (isClosed_halfRayZeroSection X).isClosedEmbedding_subtypeVal.locallyCompactSpace
  letI := (isClosed_halfRayZeroSection X).isOpen_compl.locallyCompactSpace
  (compactSupportKZeroHomeomorph (halfRayComplementHomeomorph X)).comp
    ((compactSupportBundleKMinusOneBoundary (halfRayZeroSection X)
      (isClosed_halfRayZeroSection X)).comp
        (compactSupportBundleKMinusOneHomeomorphEquiv
          (halfRayZeroSectionHomeomorph X)).toAddMonoidHom)

/-- KA II.4.8: the specified half-ray connecting map is bijective. -/
theorem compactSupportBundleKMinusOneSuspension_bijective (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] :
    Function.Bijective (compactSupportBundleKMinusOneSuspension X) := by
  /- Stage 1: apply the independently constructed II.4.7 sequence to the closed
  zero section of the literal half-ray product. Its ambient automorphism kernel
  and its ambient compact-support K-zero group are zero by the two preceding
  half-ray vanishing results.
  Stage 2: exactness at the zero-section automorphism group makes the kernel of
  its boundary zero. Exactness at the complementary K-zero group makes the image
  of that same boundary the whole group. Thus that boundary is bijective.
  Stage 3: compose with actual zero-section transport and with the increasing
  logarithm homeomorphism on the complement. Both are already bijective, giving
  precisely the displayed map. No arbitrary abstract group isomorphism replaces
  the boundary, and the later alpha-inverse-beta formula is not used. -/
  let A := halfRayZeroSection X
  let hA : IsClosed A := isClosed_halfRayZeroSection X
  let := hA.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let := compactSupportBundleKMinusOne_halfRay_subsingleton X
  let := compactSupportKZero_halfRay_subsingleton X
  let δ := compactSupportBundleKMinusOneBoundary A hA
  -- The exact sequence has zero ambient groups on both sides of this same boundary.
  have hδ : Function.Bijective δ := by
    constructor
    · apply (injective_iff_map_eq_zero δ).mpr
      intro a ha
      obtain ⟨b, hb⟩ := (range_compactSupportBundleKMinusOneClosedRestriction A hA).ge ha
      have hbzero : b = 0 := Subsingleton.elim b 0
      simpa only [hbzero, map_zero] using hb.symm
    · intro a
      have ha : a ∈ (compactSupportKZeroOpenExtension (Aᶜ : Set (X × ℝ≥0))
          hA.isOpen_compl).ker := Subsingleton.elim _ _
      exact (range_compactSupportBundleKMinusOneBoundary A hA).ge ha
  -- The two coordinate changes retain the original zero section and increasing logarithm.
  exact (compactSupportKZeroHomeomorph_bijective (halfRayComplementHomeomorph X)).comp
    (hδ.comp (compactSupportBundleKMinusOneHomeomorphEquiv
      (halfRayZeroSectionHomeomorph X)).bijective)

/-- The suspension equivalence keeps the specified half-ray map as its forward function. -/
def compactSupportBundleKMinusOneSuspensionEquiv (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] :
    CompactSupportBundleKMinusOne X ≃+ CompactSupportKZero (X × ℝ) :=
  AddEquiv.ofBijective (compactSupportBundleKMinusOneSuspension X)
    (compactSupportBundleKMinusOneSuspension_bijective X)

variable {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]

/-- The same suspension comparison is natural for a proper map of locally compact bases. -/
theorem compactSupportBundleKMinusOneSuspension_natural (f : C(X, Y)) (hf : IsProperMap f) :
    (compactSupportKZeroPullback (f.prodMap (ContinuousMap.id ℝ))
      (hf.prodMap isProperMap_id)).comp (compactSupportBundleKMinusOneSuspension Y) =
      (compactSupportBundleKMinusOneSuspension X).comp
        (compactSupportBundleKMinusOnePullback f hf) := by
  /- Stage 1: f times identity on the half-ray is proper, and the inverse image
  of Y's zero section is exactly X's zero section. Apply the independent
  compactified-boundary naturality square to this map of closed pairs.
  Stage 2: the specified zero-section homeomorphisms commute with f. The
  complement homeomorphisms use logarithm on the unchanged radial coordinate,
  so they commute with f times identity on the real line.
  Stage 3: compose these squares with proper pullback functoriality. This gives
  the displayed equality for the same positive boundary and the same increasing
  real coordinate; no reflection, inverse boundary or compactness of X is added. -/
  let AX := halfRayZeroSection X
  let AY := halfRayZeroSection Y
  let hAX : IsClosed AX := isClosed_halfRayZeroSection X
  let hAY : IsClosed AY := isClosed_halfRayZeroSection Y
  let := hAX.locallyCompactSpace
  let := hAY.locallyCompactSpace
  let := hAX.isOpen_compl.locallyCompactSpace
  let := hAY.isOpen_compl.locallyCompactSpace
  let F := f.prodMap (ContinuousMap.id ℝ≥0)
  let hF : IsProperMap F := hf.prodMap isProperMap_id
  let := (hAY.preimage F.continuous).locallyCompactSpace
  let := (hAY.preimage F.continuous).isOpen_compl.locallyCompactSpace
  let := (hAY.isOpen_compl.preimage F.continuous).locallyCompactSpace
  let fA : C(AX, AY) := preimageSubspaceMap AY F
  let fC : C((AXᶜ : Set (X × ℝ≥0)), (AYᶜ : Set (Y × ℝ≥0))) :=
    preimageSubspaceMap (AYᶜ : Set (Y × ℝ≥0)) F
  let hfA : IsProperMap fA := isProperMap_preimageSubspaceMap AY F hF
  let hfC : IsProperMap fC := isProperMap_preimageSubspaceMap (AYᶜ : Set _) F hF
  let fR := f.prodMap (ContinuousMap.id ℝ)
  let hfR : IsProperMap fR := hf.prodMap isProperMap_id
  let eX := halfRayZeroSectionHomeomorph X
  let eY := halfRayZeroSectionHomeomorph Y
  let qX := halfRayComplementHomeomorph X
  let qY := halfRayComplementHomeomorph Y
  let sX := (compactSupportBundleKMinusOneHomeomorphEquiv eX).toAddMonoidHom
  let sY := (compactSupportBundleKMinusOneHomeomorphEquiv eY).toAddMonoidHom
  let tX := compactSupportKZeroHomeomorph qX
  let tY := compactSupportKZeroHomeomorph qY
  let δX := compactSupportBundleKMinusOneBoundary AX hAX
  let δY := compactSupportBundleKMinusOneBoundary AY hAY
  -- The actual zero-section inverse commutes with f, without changing its radial coordinate.
  have hzero : (⟨eY.symm, eY.symm.continuous⟩ : C(AY, Y)).comp fA =
      f.comp (⟨eX.symm, eX.symm.continuous⟩ : C(AX, X)) := by
    ext p
    rfl
  have hs : (compactSupportBundleKMinusOnePullback fA hfA).comp sY =
      sX.comp (compactSupportBundleKMinusOnePullback f hf) := by
    change (compactSupportBundleKMinusOnePullback fA hfA).comp
      (compactSupportBundleKMinusOnePullback _ eY.symm.isProperMap) =
        (compactSupportBundleKMinusOnePullback _ eX.symm.isProperMap).comp
          (compactSupportBundleKMinusOnePullback f hf)
    rw [← compactSupportBundleKMinusOnePullback_comp,
      ← compactSupportBundleKMinusOnePullback_comp]
    simp only [hzero]
  -- The complement inverse uses exp in both bases and the same real parameter.
  have hcomplement : (⟨qY.symm, qY.symm.continuous⟩ : C(Y × ℝ, _)).comp fR =
      fC.comp (⟨qX.symm, qX.symm.continuous⟩ : C(X × ℝ, _)) := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    rfl
  have ht : (compactSupportKZeroPullback fR hfR).comp tY =
      tX.comp (compactSupportKZeroPullback fC hfC) := by
    change (compactSupportKZeroPullback fR hfR).comp
      (compactSupportKZeroPullback _ qY.symm.isProperMap) =
        (compactSupportKZeroPullback _ qX.symm.isProperMap).comp
          (compactSupportKZeroPullback fC hfC)
    rw [← compactSupportKZeroPullback_comp, ← compactSupportKZeroPullback_comp]
    simp only [hcomplement]
  -- Boundary naturality for this actual inverse-image pair gives the middle square.
  have hδ := compactSupportBundleKMinusOneBoundary_natural AY hAY F hF
  change (compactSupportKZeroPullback fC hfC).comp δY =
    δX.comp (compactSupportBundleKMinusOnePullback fA hfA) at hδ
  apply AddMonoidHom.ext
  intro a
  change compactSupportKZeroPullback fR hfR (tY (δY (sY a))) =
    tX (δX (sX (compactSupportBundleKMinusOnePullback f hf a)))
  calc
    _ = tX (compactSupportKZeroPullback fC hfC (δY (sY a))) :=
      DFunLike.congr_fun ht (δY (sY a))
    _ = tX (δX (compactSupportBundleKMinusOnePullback fA hfA (sY a))) :=
      congrArg tX (DFunLike.congr_fun hδ (sY a))
    _ = tX (δX (sX (compactSupportBundleKMinusOnePullback f hf a))) :=
      congrArg (fun b ↦ tX (δX b)) (DFunLike.congr_fun hs a)

/-- Compare with the existing degree-one carrier by inserting the sole real coordinate. -/
def compactSupportBundleKMinusOneDegreeOneEquiv (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] :
    CompactSupportBundleKMinusOne X ≃+ CompactSupportK 1 X :=
  (compactSupportBundleKMinusOneSuspensionEquiv X).trans
    (compactSupportKZeroHomeomorphEquiv
      ((Homeomorph.refl X).prodCongr (Homeomorph.funUnique (Fin 1) ℝ).symm))

/-- The coordinate comparison preserves the already defined suspended proper pullback. -/
theorem compactSupportBundleKMinusOneDegreeOneEquiv_natural
    (f : C(X, Y)) (hf : IsProperMap f) :
    (compactSupportKPullback 1 f hf).comp
        (compactSupportBundleKMinusOneDegreeOneEquiv Y).toAddMonoidHom =
      (compactSupportBundleKMinusOneDegreeOneEquiv X).toAddMonoidHom.comp
        (compactSupportBundleKMinusOnePullback f hf) := by
  /- The coordinate homeomorphism sends (x,r) to (x, the constant one-coordinate
  tuple with value r). It commutes with f on the base and identity on that tuple.
  Combine the preceding suspension naturality with inverse-pullback transport
  along this square. The target is the original CompactSupportK 1 definition,
  not a newly substituted negative K carrier or a Bott periodicity identification. -/
  let eX := (Homeomorph.refl X).prodCongr (Homeomorph.funUnique (Fin 1) ℝ).symm
  let eY := (Homeomorph.refl Y).prodCongr (Homeomorph.funUnique (Fin 1) ℝ).symm
  let fR := f.prodMap (ContinuousMap.id ℝ)
  let fN := f.prodMap (ContinuousMap.id (Fin 1 → ℝ))
  let hfR : IsProperMap fR := hf.prodMap isProperMap_id
  let hfN : IsProperMap fN := hf.prodMap isProperMap_id
  -- Evaluation of the sole coordinate commutes with the same proper map on the base.
  have hcoordinates : (⟨eY.symm, eY.symm.continuous⟩ : C(_, Y × ℝ)).comp fN =
      fR.comp (⟨eX.symm, eX.symm.continuous⟩ : C(_, X × ℝ)) := by
    apply ContinuousMap.ext
    intro p
    rfl
  have htransport : (compactSupportKZeroPullback fN hfN).comp
      (compactSupportKZeroHomeomorph eY) =
        (compactSupportKZeroHomeomorph eX).comp (compactSupportKZeroPullback fR hfR) := by
    change (compactSupportKZeroPullback fN hfN).comp
      (compactSupportKZeroPullback _ eY.symm.isProperMap) =
        (compactSupportKZeroPullback _ eX.symm.isProperMap).comp
          (compactSupportKZeroPullback fR hfR)
    rw [← compactSupportKZeroPullback_comp, ← compactSupportKZeroPullback_comp]
    simp only [hcoordinates]
  -- Combine this actual coordinate square with the already proved half-ray boundary square.
  change (compactSupportKZeroPullback fN hfN).comp
    ((compactSupportKZeroHomeomorph eY).comp (compactSupportBundleKMinusOneSuspension Y)) =
      ((compactSupportKZeroHomeomorph eX).comp (compactSupportBundleKMinusOneSuspension X)).comp
        (compactSupportBundleKMinusOnePullback f hf)
  rw [← AddMonoidHom.comp_assoc, htransport, AddMonoidHom.comp_assoc,
    compactSupportBundleKMinusOneSuspension_natural]
  rfl

/-- On compact Hausdorff X this identifies the original automorphism group with degree minus one. -/
def bundleKMinusOneRealSuspensionEquiv (X : Type*) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] : BundleKMinusOne X ≃+ CompactSupportK 1 X :=
  (compactSupportBundleKMinusOneCompactEquiv X).symm.trans
    (compactSupportBundleKMinusOneDegreeOneEquiv X)

end ComplexBundle

/-- KA II.4.10: reversing the sole real suspension coordinate acts by negation. -/
theorem compactSupportKZeroPullback_realReflection (X : Type*) [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] (a : CompactSupportKZero (X × ℝ)) :
    let e := (Homeomorph.refl X).prodCongr (Homeomorph.neg ℝ)
    compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap a = -a := by
  /- For the compact base X⁺, use the original cylinder X⁺×[0,1] with
  its two closed ends. The zero-end retraction and interval homotopy make
  absolute K-zero restriction injective, so compact-pair exactness makes the
  original automorphism boundary surjective.
  Reflection exchanges those ends. On their two clopen components, the two
  orders of the original automorphisms are conjugate. Their cylinder composite
  therefore restricts to a class plus its exchanged pullback. This class has
  zero boundary, and boundary naturality gives negation on relative K-zero.
  The increasing sigmoid identifies ℝ with (0,1), and
  sigmoid(-r)=1-sigmoid(r) makes its quotient square commute with reflection.
  Transport the relative result through this exact complement comparison.
  Finally, X×ℝ is the open complement of {∞}×ℝ in X⁺×ℝ. Its proper
  meridian retraction makes the supported boundary zero, hence open extension
  injective. Reflection commutes with extension, transferring the result to X. -/
  open ComplexBundle Topology Bundle in
  open scoped unitInterval in
  classical
  let Y := OnePoint X
  have hdiagonal :
      let E : Set (Y × I) := {p | p.2 = 0 ∨ p.2 = 1}
      ∀ (τ : C(E, E)) (_hτ : ∀ z : E, (τ z).val = (z.val.1, σ z.val.2))
        (a : BundleKMinusOne E),
        ∃ b : BundleKMinusOne (Y × I),
          bundleKMinusOneRestriction E b = a + bundleKMinusOnePullback τ a := by
    classical
    intro E τ hτ a
    have hE : IsClosed E :=
      (isClosed_singleton.preimage continuous_snd).union
        (isClosed_singleton.preimage continuous_snd)
    let := hE.isClosedEmbedding_subtypeVal.compactSpace
    obtain ⟨w, rfl⟩ := bundleAutomorphism_kMinusOneClass_surjective a
    obtain ⟨n, α, hα⟩ := w.exists_trivial_representative
    rw [← hα]
    let {Z : Type _} [TopologicalSpace Z] :
        TopologicalSpace (TotalSpace Unit (Bundle.Trivial Z (Fin n → ℂ))) := trivialTopology n
    let TE := FiniteBundle.trivial E n
    let TY := FiniteBundle.trivial (Y × I) n
    let := TE.totalTopology
    let := TY.totalTopology
    let := TE.isFiniteRank
    let := TY.isFiniteRank
    let A (z : E) : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := α.linearEquiv z
    let j : C(E, Y × I) := ⟨Subtype.val, continuous_subtype_val⟩
    let p₀ : C(Y × I, E) :=
      ⟨fun z ↦ ⟨(z.1, 0), Or.inl rfl⟩,
        (continuous_fst.prodMk continuous_const).subtype_mk _⟩
    let p₁ : C(Y × I, E) :=
      ⟨fun z ↦ ⟨(z.1, 1), Or.inr rfl⟩,
        (continuous_fst.prodMk continuous_const).subtype_mk _⟩
    -- Every pullback trivialization below preserves the same original coordinate vector.
    let tr {Z : Type _} [TopologicalSpace Z] (f : C(Z, E)) :
        Iso (FiniteBundle.trivial Z n).Fiber (FiniteBundle.trivial Z n).Fiber :=
      ((pullbackTrivialIso f n).symm.trans (α.pullback f)).trans (pullbackTrivialIso f n)
    have htr {Z : Type _} [TopologicalSpace Z] (f : C(Z, E)) (z : Z) (v : Fin n → ℂ) :
        (tr f).linearEquiv z v = α.linearEquiv (f z) v := by
      have hi : ((pullbackTrivialIso f n).linearEquiv z).symm v = v := by
        apply ((pullbackTrivialIso f n).linearEquiv z).injective
        rw [LinearEquiv.apply_symm_apply, pullbackTrivialIso_apply]
      change (pullbackTrivialIso f n).linearEquiv z
        ((α.pullback f).linearEquiv z (((pullbackTrivialIso f n).linearEquiv z).symm v)) = _
      exact (pullbackTrivialIso_apply f n z _).trans
        (congrArg (fun u : Fin n → ℂ ↦ A (f z) u) hi)
    have htrclass {Z : Type _} [TopologicalSpace Z] (f : C(Z, E)) :
        (⟨FiniteBundle.trivial Z n, tr f⟩ : BundleAutomorphism Z).kMinusOneClass =
          bundleKMinusOnePullback f (⟨TE, α⟩ : BundleAutomorphism E).kMinusOneClass := by
      rw [bundleKMinusOnePullback_class]
      apply Eq.symm
      apply BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic
      refine ⟨pullbackTrivialIso f n, ?_⟩
      intro z v
      change (pullbackTrivialIso f n).linearEquiv z ((α.pullback f).linearEquiv z v) =
        (tr f).linearEquiv z ((pullbackTrivialIso f n).linearEquiv z v)
      rw [htr]
      change (pullbackTrivialIso f n).linearEquiv z (α.linearEquiv (f z) v) =
        α.linearEquiv (f z) ((pullbackTrivialIso f n).linearEquiv z v)
      exact (pullbackTrivialIso_apply f n z _).trans
        (congrArg (α.linearEquiv (f z)) (pullbackTrivialIso_apply f n z v).symm)
    let β₀ : Iso TY.Fiber TY.Fiber := tr p₀
    let β₁ : Iso TY.Fiber TY.Fiber := tr p₁
    let β := β₀.trans β₁
    let γ := α.trans (tr τ)
    let βE := tr (p₀.comp j) |>.trans (tr (p₁.comp j))
    -- On the two clopen ends the reversed product is conjugate to the original product.
    let S : Set E := {z | z.val.2 = 1}
    have hS : IsClopen S := by
      have hc : IsClosed S := isClosed_singleton.preimage continuous_subtype_val.snd
      have hcompl : Sᶜ = {z : E | z.val.2 = 0} := by
        ext z
        change (¬z.val.2 = 1) ↔ z.val.2 = 0
        rcases z.property with hz | hz <;> simp [hz]
      refine ⟨hc, ?_⟩
      rw [← isClosed_compl_iff, hcompl]
      exact isClosed_singleton.preimage continuous_subtype_val.snd
    let c : Iso TE.Fiber TE.Fiber :=
      { linearEquiv := fun z ↦ if z ∈ S then (tr (p₁.comp j)).linearEquiv z
          else LinearEquiv.refl ℂ _
        continuous_total := by
          have hcl : IsClopen {z : TotalSpace Unit TE.Fiber | z.proj ∈ S} :=
            hS.preimage continuous_proj
          have hc := Continuous.if (p := fun z : TotalSpace Unit TE.Fiber ↦ z.proj ∈ S)
            (fun z hz ↦ (show False from by
              simp only [hcl.frontier_eq, Set.mem_empty_iff_false] at hz).elim)
            (tr (p₁.comp j)).continuous_total continuous_id
          exact hc.congr (fun z ↦ by split_ifs <;> rfl)
        continuous_symm := by
          have hcl : IsClopen {z : TotalSpace Unit TE.Fiber | z.proj ∈ S} :=
            hS.preimage continuous_proj
          have hc := Continuous.if (p := fun z : TotalSpace Unit TE.Fiber ↦ z.proj ∈ S)
            (fun z hz ↦ (show False from by
              simp only [hcl.frontier_eq, Set.mem_empty_iff_false] at hz).elim)
            (tr (p₁.comp j)).continuous_symm continuous_id
          exact hc.congr (fun z ↦ by split_ifs <;> rfl) }
    have hconj : (⟨TE, γ⟩ : BundleAutomorphism E).IsIsomorphic ⟨TE, βE⟩ := by
      refine ⟨c, ?_⟩
      intro z v
      have hzτ := hτ z
      rcases z.property with hz | hz
      · have hnot : z ∉ S := by simp [S, hz]
        have hz₀ : p₀ (j z) = z := Subtype.ext (Prod.ext rfl hz.symm)
        have hz₁ : p₁ (j z) = τ z := by
          apply Subtype.ext
          rw [hzτ]
          simp only [hz, unitInterval.symm_zero]
          rfl
        change (if z ∈ S then (tr (p₁.comp j)).linearEquiv z else LinearEquiv.refl ℂ _)
          ((tr τ).linearEquiv z (α.linearEquiv z v)) =
            (tr (p₁.comp j)).linearEquiv z ((tr (p₀.comp j)).linearEquiv z
              ((if z ∈ S then (tr (p₁.comp j)).linearEquiv z
                else LinearEquiv.refl ℂ _) v))
        simp only [ite_eq_right hnot, LinearEquiv.refl_apply, htr, ContinuousMap.comp_apply]
        change A (τ z) (A z v) = A (p₁ (j z)) (A (p₀ (j z)) v)
        simp only [hz₀, hz₁]
      · have hyes : z ∈ S := hz
        have hz₁ : p₁ (j z) = z := Subtype.ext (Prod.ext rfl hz.symm)
        have hz₀ : p₀ (j z) = τ z := by
          apply Subtype.ext
          rw [hzτ]
          simp only [hz, unitInterval.symm_one]
          rfl
        change (if z ∈ S then (tr (p₁.comp j)).linearEquiv z else LinearEquiv.refl ℂ _)
          ((tr τ).linearEquiv z (α.linearEquiv z v)) =
            (tr (p₁.comp j)).linearEquiv z ((tr (p₀.comp j)).linearEquiv z
              ((if z ∈ S then (tr (p₁.comp j)).linearEquiv z
                else LinearEquiv.refl ℂ _) v))
        simp only [ite_eq_left hyes, htr, ContinuousMap.comp_apply]
        change A (p₁ (j z)) (A (τ z) (A z v)) =
          A (p₁ (j z)) (A (p₀ (j z)) (A (p₁ (j z)) v))
        simp only [hz₀, hz₁]
    have hβE : (⟨TE, βE⟩ : BundleAutomorphism E).kMinusOneClass =
        bundleKMinusOneRestriction E (⟨TY, β⟩ : BundleAutomorphism (Y × I)).kMinusOneClass := by
      change (⟨TE, (tr (p₀.comp j)).trans (tr (p₁.comp j))⟩ :
        BundleAutomorphism E).kMinusOneClass =
          bundleKMinusOnePullback j
            (⟨TY, (tr p₀).trans (tr p₁)⟩ : BundleAutomorphism (Y × I)).kMinusOneClass
      rw [BundleAutomorphism.kMinusOneClass_trans, BundleAutomorphism.kMinusOneClass_trans,
        map_add, htrclass, htrclass, htrclass, htrclass]
      rw [bundleKMinusOnePullback_comp, bundleKMinusOnePullback_comp]
      rfl
    refine ⟨(⟨TY, β⟩ : BundleAutomorphism (Y × I)).kMinusOneClass, ?_⟩
    rw [← hβE, ← BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ hconj,
      BundleAutomorphism.kMinusOneClass_trans, htrclass]
  have hcompact (a : CompactSupportKZero (Y × ℝ)) :
      let e := (Homeomorph.refl Y).prodCongr (Homeomorph.neg ℝ)
      compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap a = -a := by
    classical
    let E : Set (Y × I) := {p | p.2 = 0 ∨ p.2 = 1}
    let hE : IsClosed E :=
      (isClosed_singleton.preimage continuous_snd).union
        (isClosed_singleton.preimage continuous_snd)
    let := hE.isClosedEmbedding_subtypeVal.compactSpace
    let := hE.isOpen_compl.locallyCompactSpace
    let := PointedQuotient.t2Space.{_, 0} E hE
    let := PointedQuotient.compactSpace.{_, 0} E
    let j : C(E, Y × I) := ⟨Subtype.val, continuous_subtype_val⟩
    let p₀ : C(Y × I, E) :=
      ⟨fun z ↦ ⟨(z.1, 0), Or.inl rfl⟩,
        (continuous_fst.prodMk continuous_const).subtype_mk _⟩
    -- Evaluation at the zero end retracts the cylinder up to the actual interval homotopy.
    have htime (p : I × (Y × I)) : (1 - (p.1 : ℝ)) * (p.2.2 : ℝ) ∈ Set.Icc 0 1 := by
      constructor
      · exact mul_nonneg (sub_nonneg.mpr p.1.property.2) p.2.2.property.1
      · nlinarith [p.2.2.property.2, mul_nonneg p.1.property.1 p.2.2.property.1]
    let H : (ContinuousMap.id (Y × I)).Homotopy (j.comp p₀) :=
      { toFun := fun p ↦ (p.2.1, ⟨(1 - (p.1 : ℝ)) * (p.2.2 : ℝ), htime p⟩)
        continuous_toFun := continuous_snd.fst.prodMk
          (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            (continuous_subtype_val.comp continuous_snd.snd)).subtype_mk htime)
        map_zero_left := by
          intro p
          change (p.1, _) = (p.1, p.2)
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            simp
        map_one_left := by
          intro p
          change (p.1, _) = (p.1, (0 : I))
          apply Prod.ext
          · rfl
          · apply Subtype.ext
            simp }
    have hrestriction : Function.Injective (complexKZeroRestriction E hE) := by
      apply (injective_iff_map_eq_zero _).mpr
      intro b hb
      have hhom := DFunLike.congr_fun
        (complexKZeroPullback_eq_of_homotopy (ContinuousMap.id (Y × I)) (j.comp p₀) H) b
      change kZeroMap (RingHom.id _) b = complexKZeroPullback (j.comp p₀) b at hhom
      rw [kZeroMap_id, complexKZeroPullback_comp] at hhom
      change b = complexKZeroPullback p₀ (complexKZeroPullback j b) at hhom
      change complexKZeroPullback j b = 0 at hb
      simpa only [hb, map_zero] using hhom
    let δ : BundleKMinusOne E →+ RelativeKZero.{_, 0} E hE := bundleKMinusOneBoundary E hE
    have hδsurj : Function.Surjective δ := by
      intro b
      have hb : relativeKZeroForget E hE b = 0 :=
        hrestriction ((complexKZeroRestriction_relativeKZeroForget E hE b).trans
          (map_zero _).symm)
      exact (range_bundleKMinusOneBoundary E hE).ge hb
    -- Reflection exchanges the same two ends. Diagonal classes are killed by the positive boundary.
    let c := (Homeomorph.refl Y).prodCongr unitInterval.symmHomeomorph
    let f : C(Y × I, Y × I) := ⟨c, c.continuous⟩
    have hf : Set.MapsTo f E E := by
      intro z hz
      rcases hz with hz | hz
      · exact Or.inr (by change σ z.2 = 1; rw [hz, unitInterval.symm_zero])
      · exact Or.inl (by change σ z.2 = 0; rw [hz, unitInterval.symm_one])
    let τ : C(E, E) :=
      ⟨fun z ↦ ⟨f z, hf z.property⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
    let R : RelativeKZero.{_, 0} E hE →+ RelativeKZero.{_, 0} E hE :=
      relativeKZeroPullback E hE E hE f hf
    have hrelative (b : RelativeKZero.{_, 0} E hE) : R b = -b := by
      obtain ⟨w, rfl⟩ := hδsurj b
      obtain ⟨v, hv⟩ := hdiagonal τ (fun _ ↦ rfl) w
      have hzero : δ (w + bundleKMinusOnePullback τ w) = 0 := by
        rw [← hv]
        exact (range_bundleKMinusOneRestriction E hE).le ⟨v, rfl⟩
      have hnatural := DFunLike.congr_fun (bundleKMinusOneBoundary_natural E hE E hE f hf) w
      change R (δ w) = δ (bundleKMinusOnePullback τ w) at hnatural
      rw [map_add, ← hnatural] at hzero
      exact eq_neg_of_add_eq_zero_right hzero
    -- Sigmoid supplies the increasing interior coordinate; its negation is precisely interval flip.
    let s : Y × ℝ → Y × I := fun p ↦ (p.1, unitInterval.sigmoid p.2)
    have hs : IsEmbedding s := (IsEmbedding.id.prodMap Topology.isEmbedding_sigmoid)
    have hrange : Set.range s = Eᶜ := by
      ext p
      constructor
      · rintro ⟨q, rfl⟩ hp
        have hsig : unitInterval.sigmoid q.2 ∈ Set.Ioo (0 : I) 1 :=
          unitInterval.range_sigmoid ▸ Set.mem_range_self q.2
        exact hp.elim (fun h ↦ hsig.1.ne' h) (fun h ↦ hsig.2.ne h)
      · intro hp
        have hmem : p.2 ∈ Set.Ioo (0 : I) 1 := by
          exact ⟨lt_of_le_of_ne (unitInterval.nonneg p.2) (fun h ↦ hp (Or.inl h.symm)),
            lt_of_le_of_ne (unitInterval.le_one p.2) (fun h ↦ hp (Or.inr h))⟩
        obtain ⟨r, hr⟩ := (unitInterval.range_sigmoid ▸ hmem : p.2 ∈ Set.range unitInterval.sigmoid)
        exact ⟨(p.1, r), Prod.ext rfl hr⟩
    let e : (Y × ℝ) ≃ₜ (Eᶜ : Set (Y × I)) :=
      hs.toHomeomorph.trans (Homeomorph.setCongr hrange)
    let T : RelativeKZero.{_, 0} E hE →+ CompactSupportKZero (Y × ℝ) :=
      (compactSupportKZeroHomeomorph e.symm).comp (relativeKZeroToCompactSupport E hE)
    have hTsurj : Function.Surjective T :=
      (compactSupportKZeroHomeomorph_bijective e.symm).2.comp
        (relativeKZeroToCompactSupport_bijective E hE).2
    let q := PointedQuotient.onePointHomeomorph.{_, 0} E hE
    let k : C(OnePoint (Y × ℝ), PointedQuotient.{_, 0} E) :=
      (⟨q.symm, q.symm.continuous⟩ : C(_, _)).comp
        (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap)
    have hkinfty : k OnePoint.infty = PointedQuotient.basepoint E :=
      PointedQuotient.onePointHomeomorph_symm_infty E hE
    have hkfinite (p : Y × ℝ) :
        k (p : OnePoint (Y × ℝ)) = PointedQuotient.of E (s p) := by
      exact q.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of E hE (e p)).symm
    let ρ := (Homeomorph.refl Y).prodCongr (Homeomorph.neg ℝ)
    let g : C(Y × ℝ, Y × ℝ) := ⟨ρ, ρ.continuous⟩
    let gInf := properOnePointMap g ρ.isProperMap
    let fq := PointedQuotient.mapContinuous E E f hf
    have hsquare : fq.comp k = k.comp gInf := by
      apply ContinuousMap.ext
      intro z
      cases z using OnePoint.rec with
      | infty =>
        change fq (k OnePoint.infty) = k OnePoint.infty
        rw [hkinfty]
        rfl
      | coe p =>
        change fq (k (p : OnePoint (Y × ℝ))) = k (g p : OnePoint (Y × ℝ))
        rw [hkfinite, hkfinite]
        change PointedQuotient.of E (p.1, σ (unitInterval.sigmoid p.2)) =
          PointedQuotient.of E (p.1, unitInterval.sigmoid (-p.2))
        rw [unitInterval.sigmoid_neg]
    have hT (b : RelativeKZero.{_, 0} E hE) : (T b).val = complexKZeroPullback k b.val := by
      change complexKZeroPullback (properOnePointMap ⟨e, e.continuous⟩ e.isProperMap)
        (complexKZeroPullback ⟨q.symm, q.symm.continuous⟩ b.val) = _
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have htransport (b : RelativeKZero.{_, 0} E hE) :
        compactSupportKZeroPullback g ρ.isProperMap (T b) = T (R b) := by
      apply Subtype.ext
      change complexKZeroPullback gInf (T b).val = (T (R b)).val
      rw [hT, hT]
      change complexKZeroPullback gInf (complexKZeroPullback k b.val) =
        complexKZeroPullback k (complexKZeroPullback fq b.val)
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
    obtain ⟨b, rfl⟩ := hTsurj a
    change compactSupportKZeroPullback g ρ.isProperMap (T b) = -T b
    rw [htransport, hrelative, map_neg]
  let A : Set (OnePoint X × ℝ) := {p | p.1 = OnePoint.infty}
  let hA : IsClosed A := isClosed_singleton.preimage continuous_fst
  let U : Set (OnePoint X × ℝ) := Aᶜ
  let hU : IsOpen U := hA.isOpen_compl
  let := hA.locallyCompactSpace
  let := hU.locallyCompactSpace
  let i : C(A, OnePoint X × ℝ) := ⟨Subtype.val, continuous_subtype_val⟩
  let hi : IsProperMap i := hA.isClosedEmbedding_subtypeVal.isProperMap
  let er : ℝ ≃ₜ A :=
    { toFun := fun t ↦ ⟨(OnePoint.infty, t), rfl⟩
      invFun := fun p ↦ p.val.2
      left_inv := fun _ ↦ rfl
      right_inv := fun p ↦ Subtype.ext (Prod.ext p.property.symm rfl)
      continuous_toFun := (continuous_const.prodMk continuous_id).subtype_mk _
      continuous_invFun := continuous_subtype_val.snd }
  let r : C(OnePoint X × ℝ, A) :=
    (⟨er, er.continuous⟩ : C(ℝ, A)).comp ⟨Prod.snd, continuous_snd⟩
  let hr : IsProperMap r := er.isProperMap.comp isProperMap_snd_of_compactSpace
  have hri : r.comp i = ContinuousMap.id A := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    exact Prod.ext p.property.symm rfl
  -- The actual proper retraction makes the supported boundary zero, hence open extension injective.
  have hδzero (w : CompactSupportBundleKMinusOne A) :
      compactSupportBundleKMinusOneBoundary A hA w = 0 := by
    have hw : compactSupportBundleKMinusOneClosedRestriction A hA
        (compactSupportBundleKMinusOnePullback r hr w) = w := by
      change compactSupportBundleKMinusOnePullback i hi
        (compactSupportBundleKMinusOnePullback r hr w) = w
      rw [← AddMonoidHom.comp_apply, ← compactSupportBundleKMinusOnePullback_comp]
      simpa only [hri, AddMonoidHom.id_apply] using DFunLike.congr_fun
        (compactSupportBundleKMinusOnePullback_id (X := A)) w
    exact (range_compactSupportBundleKMinusOneClosedRestriction A hA).le
      ⟨compactSupportBundleKMinusOnePullback r hr w, hw⟩
  let J := compactSupportKZeroOpenExtension U hU
  have hJinj : Function.Injective J := by
    apply (injective_iff_map_eq_zero J).mpr
    intro b hb
    obtain ⟨w, hw⟩ := (range_compactSupportBundleKMinusOneBoundary A hA).ge hb
    exact hw.symm.trans (hδzero w)
  -- The open complement is exactly X × ℝ, including when X is empty or already compact.
  let s : X × ℝ → OnePoint X × ℝ := fun p ↦ (p.1, p.2)
  have hs : IsEmbedding s := OnePoint.isOpenEmbedding_coe.isEmbedding.prodMap IsEmbedding.id
  have hrange : Set.range s = U := by
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact OnePoint.coe_ne_infty z.1
    · intro hp
      rcases p with ⟨x, t⟩
      cases x using OnePoint.rec with
      | infty => exact (hp rfl).elim
      | coe x => exact ⟨(x, t), rfl⟩
  let e : (X × ℝ) ≃ₜ U := hs.toHomeomorph.trans (Homeomorph.setCongr hrange)
  let ep : C(X × ℝ, U) := ⟨e, e.continuous⟩
  let P := compactSupportKZeroPullback ep e.isProperMap
  have hPsurj : Function.Surjective P := (compactSupportKZeroHomeomorph_bijective e.symm).2
  let ρ := (Homeomorph.refl X).prodCongr (Homeomorph.neg ℝ)
  let g : C(X × ℝ, X × ℝ) := ⟨ρ, ρ.continuous⟩
  let R := (Homeomorph.refl (OnePoint X)).prodCongr (Homeomorph.neg ℝ)
  let F : C(OnePoint X × ℝ, OnePoint X × ℝ) := ⟨R, R.continuous⟩
  let fU : C(U, U) := preimageSubspaceMap U F
  let hfU : IsProperMap fU := isProperMap_preimageSubspaceMap U F R.isProperMap
  have hcoordinates : fU.comp ep = ep.comp g := by
    apply ContinuousMap.ext
    intro p
    apply Subtype.ext
    rfl
  have hproper : (compactSupportKZeroPullback g ρ.isProperMap).comp P =
      P.comp (compactSupportKZeroPullback fU hfU) := by
    change (compactSupportKZeroPullback g ρ.isProperMap).comp
      (compactSupportKZeroPullback ep e.isProperMap) =
        (compactSupportKZeroPullback ep e.isProperMap).comp
          (compactSupportKZeroPullback fU hfU)
    rw [← compactSupportKZeroPullback_comp, ← compactSupportKZeroPullback_comp]
    simp only [hcoordinates]
  have hopen := compactSupportKZeroPullback_openExtension U hU F R.isProperMap
  change (compactSupportKZeroPullback F R.isProperMap).comp J =
    J.comp (compactSupportKZeroPullback fU hfU) at hopen
  have hreflection (b : CompactSupportKZero U) : compactSupportKZeroPullback fU hfU b = -b := by
    apply hJinj
    calc
      J (compactSupportKZeroPullback fU hfU b) =
          compactSupportKZeroPullback F R.isProperMap (J b) :=
        (DFunLike.congr_fun hopen b).symm
      _ = -J b := hcompact (J b)
      _ = J (-b) := (map_neg J b).symm
  obtain ⟨b, rfl⟩ := hPsurj a
  change compactSupportKZeroPullback g ρ.isProperMap (P b) = -P b
  calc
    _ = P (compactSupportKZeroPullback fU hfU b) := DFunLike.congr_fun hproper b
    _ = -P b := by rw [hreflection, map_neg]

end AtiyahSinger
