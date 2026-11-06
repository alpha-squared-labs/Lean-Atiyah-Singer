/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Analysis.ZeroOrderBundleMap
public import AtiyahSinger.Geometry.OpenSections
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Extending an exterior zero-order bundle map

Public module ID: M0606.

The exterior identity in SG III.13.4 is a smooth bundle map on an exterior open
set. A cutoff extends it to a global zero-order differential operator after
allowing a larger exceptional neighborhood. The two bundles are already given
over the entire base; the theorem does not extend them to another ambient manifold.

The cutoff is constructed directly from mathlib's smooth separation theorem;
the established zero-order classification identifies the original exterior action.
The extension has no asserted interior invertibility or prescribed values all the
way to the boundary of the original exterior domain.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

variable [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hT hSC hE hF

/-- An exterior smooth bundle map extends globally while preserving its values farther out. -/
theorem exists_zeroOrder_extension_of_exterior (U : Opens M)
    (K : Set M) (hK : IsCompact K) (hKU : Kᶜ ⊆ (U : Set M))
    (B : DifferentialOperator (n := n) (r := r) (q := q) (M := U)
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F) 0)
    (W : Set M) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ D : DifferentialOperator (n := n) (r := r) (q := q) E F 0,
      ∀ (s : smoothSections (n := n) (r := r) E) (x : U), x.val ∉ W →
        (D.toLinearMap s).val x.val =
          (B.toLinearMap (smoothSectionRestriction E U s)).val x := by
  /- Stage 1: use mathlib smooth separation to choose a compactly supported real χ
  equal to one near K and supported in W. The closed set C=M minus the interior
  of {χ=1} lies in K-complement and hence in U; it need not be compact.
  Stage 2: the zero-order classification identifies B with its smooth fiber map b.
  Multiply b by 1-χ on U and extend it by zero. Ambient-closed support in C makes
  this global fiber map smooth, including at the boundary of U. Its section map
  is therefore a differential operator of order zero. Outside W the multiplier
  is one, giving the original exterior action. No invertibility in W or agreement
  with B on all of U is asserted. -/

  classical
  let H := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let Z := EuclideanSpace ℂ (Fin q)
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- Choose a cutoff with compact support inside W and value one near K.
  obtain ⟨O, hO, hKO, hOW, hOc⟩ :=
    exists_open_between_and_isCompact_closure hK hW hKW
  obtain ⟨Vχ, hVχ, hKVχ, hVχO⟩ := hK.exists_isOpen_closure_subset
    (hO.mem_nhdsSet.mpr hKO)
  obtain ⟨χ, hχsmooth, _, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, H)
      (n := (⊤ : ℕ∞)) hO isClosed_closure hVχO
  have hχW : tsupport χ ⊆ W := by
    simpa only [tsupport, hχsupport] using hOW
  have _hχcompact : HasCompactSupport χ := by
    simpa only [HasCompactSupport, tsupport, hχsupport] using hOc
  let C : Set M := (interior {x | χ x = 1})ᶜ
  have hC : IsClosed C := isOpen_interior.isClosed_compl
  have hKC : K ⊆ interior {x | χ x = 1} := by
    intro x hx
    apply (interior_maximal ?_ hVχ) (hKVχ hx)
    intro y hy
    exact (hχone y).mp (subset_closure hy)
  have hCU : C ⊆ (U : Set M) := by
    intro x hx
    apply hKU
    intro hxK
    exact hx (hKC hxK)
  -- The native pullback atlas keeps the same transition maps and original fiber values.
  let : IsSmoothComplexBundle (n := n) (r := r) ((i : U → M) *ᵖ E) := by
    constructor
    rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
    let := he
    let := hf
    refine ((IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f).comp
      contMDiff_subtype_val.contMDiffOn (fun x hx ↦ hx)).congr ?_
    intro x hx
    apply ContinuousLinearMap.ext
    intro v
    change ((e.pullback i).coordChangeL ℂ (f.pullback i) x) v =
      (e.coordChangeL ℂ f x.val) v
    rw [e.coordChangeL_apply f hx, (e.pullback i).coordChangeL_apply' _]
    · rfl
    · exact hx
  let : IsSmoothComplexBundle (n := n) (r := q) ((i : U → M) *ᵖ F) := by
    constructor
    rintro _ _ ⟨e, he, rfl⟩ ⟨f, hf, rfl⟩
    let := he
    let := hf
    refine ((IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e f).comp
      contMDiff_subtype_val.contMDiffOn (fun x hx ↦ hx)).congr ?_
    intro x hx
    apply ContinuousLinearMap.ext
    intro v
    change ((e.pullback i).coordChangeL ℂ (f.pullback i) x) v =
      (e.coordChangeL ℂ f x.val) v
    rw [e.coordChangeL_apply f hx, (e.pullback i).coordChangeL_apply' _]
    · rfl
    · exact hx
  obtain ⟨a, ⟨ha, hBa⟩, _⟩ := existsUnique_smoothBundleMap_of_order_zero B
  let b (x : M) : E x →ₗ[ℂ] F x :=
    if hx : x ∈ U then ((1 - χ x : ℝ) : ℂ) • a ⟨x, hx⟩ else 0
  -- Over U, descend the same smooth columns from the open submanifold.
  have haLocal (e : Trivialization V (π V E)) [MemTrivializationAtlas e]
      (f : Trivialization Z (π Z F)) [MemTrivializationAtlas f]
      (j : Fin r) (x : M) (hx : x ∈ e.baseSet ∩ f.baseSet) (hxU : x ∈ U) :
      ContMDiffAt 𝓘(ℝ, H) 𝓘(ℝ, Z) ∞
        (fun y ↦ if hy : y ∈ U then
          (f ⟨y, a ⟨y, hy⟩ (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 else 0) x := by
    let x' : U := ⟨x, hxU⟩
    let : MemTrivializationAtlas (e.pullback i) := ⟨e, inferInstance, rfl⟩
    let : MemTrivializationAtlas (f.pullback i) := ⟨f, inferInstance, rfl⟩
    have hx' : x' ∈ (e.pullback i).baseSet ∩ (f.pullback i).baseSet := hx
    have hlocal := (ha (e.pullback i) (f.pullback i) j).contMDiffAt
      (((e.pullback i).open_baseSet.inter (f.pullback i).open_baseSet).mem_nhds hx')
    apply (contMDiffAt_subtype_iff (U := U) (x := x')).mp
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [((e.pullback i).open_baseSet.inter
      (f.pullback i).open_baseSet).mem_nhds hx'] with y hy
    have heq : (e.pullback i).symmL ℂ y (EuclideanSpace.single j 1) =
        e.symmL ℂ y.val (EuclideanSpace.single j 1) := by
      rw [(e.pullback i).symmL_apply (R := ℂ) hy.1]
      change (e.pullback i).symm y (EuclideanSpace.single j 1) =
        e.symmL ℂ (i y) (EuclideanSpace.single j 1)
      rw [e.symmL_apply (R := ℂ) hy.1, (e.pullback i).symm_apply hy.1]
      rfl
    erw [dite_eq_left y.property]
    change (f ⟨y.val, a y (e.symmL ℂ y.val (EuclideanSpace.single j 1))⟩).2 =
      (f ⟨y.val, a y ((e.pullback i).symmL ℂ y (EuclideanSpace.single j 1))⟩).2
    rw [heq]
  have hb : IsSmoothBundleMap (n := n) (r := r) (q := q) b := by
    intro e he f hf j x hx
    let := he
    let := hf
    by_cases hxU : x ∈ U
    · -- Multiplication by the cutoff preserves the original smooth local matrix columns.
      have hscalar : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, ℂ) ∞
          (fun y ↦ ((1 - χ y : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub hχsmooth)
      have hmul : ContDiff ℝ ∞ (fun t : ℂ × Z ↦ t.1 • t.2) := contDiff_smul
      have hs := hmul.contMDiff.contMDiffAt.comp x
        (hscalar.contMDiffAt.prodMk_space (haLocal e f j x hx hxU))
      apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
      filter_upwards [U.isOpen.mem_nhds hxU, f.open_baseSet.mem_nhds hx.2] with y hyU hyf
      change (f ⟨y, b y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 =
        ((1 - χ y : ℝ) : ℂ) • (if hy : y ∈ U then
          (f ⟨y, a ⟨y, hy⟩ (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 else 0)
      have hbval : b y (e.symmL ℂ y (EuclideanSpace.single j 1)) =
          ((1 - χ y : ℝ) : ℂ) •
            a ⟨y, hyU⟩ (e.symmL ℂ y (EuclideanSpace.single j 1)) := by
        dsimp only [b]
        erw [dite_eq_left hyU]
        rfl
      rw [hbval]
      erw [dite_eq_left hyU]
      change (f ⟨y, ((1 - χ y : ℝ) : ℂ) •
        a ⟨y, hyU⟩ (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 = _
      exact (f.linearEquivAt ℂ y hyf).map_smul _ _
    · -- Ambient-closed support in C makes the zero extension smooth at every boundary point.
      have hxC : x ∉ C := fun h ↦ hxU (hCU h)
      apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : Z))).congr_of_eventuallyEq
      filter_upwards [hC.isOpen_compl.mem_nhds hxC,
        f.open_baseSet.mem_nhds hx.2] with y hyC hyf
      have hyone : y ∈ interior {z | χ z = 1} := by simpa only [C, compl_compl] using hyC
      have hχy : χ y = 1 := interior_subset (s := {z : M | χ z = 1}) hyone
      have hby : b y = 0 := by
        dsimp only [b]
        by_cases hyU : y ∈ U
        · erw [dite_eq_left hyU]
          rw [hχy, sub_self, Complex.ofReal_zero, zero_smul]
          rfl
        · erw [dite_eq_right hyU]
      change (f ⟨y, b y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 = 0
      rw [hby, LinearMap.zero_apply]
      exact (f.linearEquivAt ℂ y hyf).map_zero
  let D : DifferentialOperator (n := n) (r := r) (q := q) E F 0 :=
    ⟨smoothSectionMap b hb, isDifferentialOperator_smoothSectionMap b hb⟩
  refine ⟨D, ?_⟩
  intro s x hxW
  -- Outside W the same multiplier is one, so the original exterior action is retained.
  have hχx : χ x.val = 0 := image_eq_zero_of_notMem_tsupport
    (fun h ↦ hxW (hχW h))
  have haction := congrArg
    (fun L ↦ (L (smoothSectionRestriction E U s)).val x) hBa
  change (B.toLinearMap (smoothSectionRestriction E U s)).val x = a x (s.val x.val)
    at haction
  change b x.val (s.val x.val) = _
  rw [haction]
  dsimp only [b]
  erw [dite_eq_left x.property]
  rw [hχx, sub_zero, Complex.ofReal_one, one_smul]
  rfl

end AtiyahSinger
