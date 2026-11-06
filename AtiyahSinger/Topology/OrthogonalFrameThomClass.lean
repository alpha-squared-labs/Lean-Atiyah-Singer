/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedSupportKZero
public import AtiyahSinger.Topology.BundleThom
public import AtiyahSinger.Topology.OrthogonalFrameExteriorDescent
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# The exterior Bott class in orthogonal frame coordinates

Public module ID: M1979.

The original orthogonal equivariant exterior Bott class descends to exactly
the exterior Thom class of the actual scalar complexification. The returned
homeomorphism retains its original real and imaginary frame coordinates.
The original canonical Hermitian pairing intertwines wedge minus contraction;
no replacement class, orientation reversal or sign convention is introduced.

The comparison uses the same descended parity bundle isomorphisms on one
common compact exterior and retains the original zero controls. This is the
standard associated frame description of the Thom construction (SG Appendix C
and III.13; HU IV.5). It supplies the compact-base class comparison needed by
the normal sphere argument; coefficients over a noncompact pullback base and
sphere open extension are subsequent comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct Matrix.Norms.Elementwise

variable {n r : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin r)) V]

local notation "RModel" => EuclideanSpace ℝ (Fin r)
local notation "W" => EuclideanSpace ℂ (Fin r)
local notation "GO" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "P" => OrthogonalFrameBundle r V
local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))



attribute [local instance] orthogonalFrameTopology exteriorAlgebraNormedAddCommGroup
  exteriorAlgebraNormedSpace exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology isFiniteRank_associatedEquivariant isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable [CompactSpace B] [T2Space B]

include n r V in
set_option maxSynthPendingDepth 40 in
set_option synthInstance.maxHeartbeats 100000 in
-- Resolve the original associated exterior, scalar-extension and pullback instances.
set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Keep the original quotient, scalar-extension topology and support representatives fixed.
/-- The actual associated exterior Bott class is the original complexification Thom class. -/
theorem exists_orthogonalFrame_thomClass_homeomorph :
    letI := continuousSMul_orthogonalFrame r V I
    let hP := (smoothOrthogonalFrameAtlas r V I).toIsPrincipalBundle
    let C := fun b : B ↦ ℂ ⊗[ℝ] V b
    letI := complexificationTopology RModel V
    letI := ComplexBundle.isFiniteRank_complexification RModel V
    letI : IsContinuousRiemannianBundle RModel V := by
      obtain ⟨g, hg, hinner⟩ :=
        IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := ∞) (F := RModel) (E := V)
      exact ⟨g, hg.continuous, hinner⟩
    let h := complexificationHermitianMetric (R := RModel) (E := V)
    letI (b : B) : NormedAddCommGroup (C b) := (h.toCore b).toNormedAddCommGroup
    letI (b : B) : InnerProductSpace ℂ (C b) := InnerProductSpace.ofCore (h.toCore b).toCore
    let Z := AssociatedBundle GO P W
    letI := associatedBundle_t2Space (Y := W) hP
    letI := associatedBundle_locallyCompactSpace (Y := W) hP
    ∃ e : Z ≃ₜ TotalSpace Unit C,
      (∀ (p : P) (z : W),
        e (associatedBundleMk GO P W p z) =
          ⟨p.1, (complexificationReIm (V p.1)).symm
            (p.2 (WithLp.toLp 2 (fun i ↦ (z i).re)),
              p.2 (WithLp.toLp 2 (fun i ↦ (z i).im)))⟩) ∧
      associatedSupportKZero hP
          (equivariantExteriorBottClass (orthogonalComplexification_unitary r)) =
        compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap
          (exteriorThomClass C h.continuous_pairing) := by
  classical
  let := continuousSMul_orthogonalFrame r V I
  let hP := (smoothOrthogonalFrameAtlas r V I).toIsPrincipalBundle
  let := complexificationTopology RModel V
  let := ComplexBundle.isFiniteRank_complexification RModel V
  let C := fun b : B ↦ ℂ ⊗[ℝ] V b
  let : IsContinuousRiemannianBundle RModel V := by
    obtain ⟨g, hg, hinner⟩ :=
      IsContMDiffRiemannianBundle.exists_contMDiff (IB := I) (n := ∞) (F := RModel) (E := V)
    exact ⟨g, hg.continuous, hinner⟩
  let h := complexificationHermitianMetric (R := RModel) (E := V)
  let (b : B) : NormedAddCommGroup (C b) := (h.toCore b).toNormedAddCommGroup
  let (b : B) : InnerProductSpace ℂ (C b) := InnerProductSpace.ofCore (h.toCore b).toCore
  let Z := AssociatedBundle GO P W
  let := associatedBundle_t2Space (Y := W) hP
  let := associatedBundle_locallyCompactSpace (Y := W) hP
  let T := TotalSpace Unit C
  let base : C(Z, B) := associatedBundleProjection hP
  let πC : C(T, B) := ⟨π Unit C, continuous_proj⟩
  let Parity (i : ZMod 2) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) i
  let H (i : ZMod 2) : B → Type _ :=
    fun b ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (C b)) i
  let F (i : ZMod 2) := (base : Z → B) *ᵖ (H i)
  let (i : ZMod 2) : TopologicalSpace (TotalSpace Unit (Trivial W (Parity i))) :=
    modelTopology (Parity i) (Trivial W (Parity i))
  let (i : ZMod 2) : IsFiniteRank (Trivial W (Parity i)) :=
    isFiniteRank_model (Parity i) (Trivial W (Parity i))
  let σ (i : ZMod 2) := exteriorParityEquivariantStructure (G := GO) (V := W) i
  obtain ⟨L, hL, hpair, hdesc⟩ := exists_orthogonalFrame_exterior_descent (n := n) (r := r) V
  obtain ⟨η, hη⟩ := exists_orthogonalFrame_complexification_homeomorph (n := n) (r := r) V
  have hηL (p : P) (z : W) : η (associatedBundleMk GO P W p z) = ⟨p.1, L p z⟩ := by
    rw [hη]
    apply congrArg (fun w : C p.1 ↦ (⟨p.1, w⟩ : T))
    exact (complexificationReIm (V p.1)).symm_apply_eq.mpr (hL p z).symm
  have hb (z : Z) : (η z).proj = base z := by
    induction z using Quotient.inductionOn with
    | h w => exact congrArg (fun z : T ↦ z.proj) (hηL w.1 w.2)
  -- Express the same total map with its unchanged base coordinate definitionally visible.
  let f (z : Z) : T := ⟨base z, cast (congrArg C (hb z)) (η z).snd⟩
  have hf (z : Z) : f z = η z := TotalSpace.mk_cast (F := Unit) (E := C) (hb z) (η z).snd
  let e : Z ≃ₜ T :=
    { toFun := f
      invFun := η.symm
      left_inv z := by rw [hf]; exact η.symm_apply_apply z
      right_inv z := by rw [hf]; exact η.apply_symm_apply z
      continuous_toFun := η.continuous.congr (fun z ↦ (hf z).symm)
      continuous_invFun := η.symm.continuous }
  have he (p : P) (z : W) : e (associatedBundleMk GO P W p z) = ⟨p.1, L p z⟩ :=
    (hf _).trans (hηL p z)
  have hefib (p : P) (z : W) : (e (associatedBundleMk GO P W p z)).snd = L p z :=
    eq_of_heq (congr_arg_heq (fun z : T ↦ z.snd) (he p z))
  let eMap : C(Z, T) := ⟨e, e.continuous⟩
  let (i : ZMod 2) : IsFiniteRank ((πC : T → B) *ᵖ (H i)) :=
    isFiniteRank_pullback (E := H i) πC
  let Source (i : ZMod 2) := (eMap : Z → T) *ᵖ ((πC : T → B) *ᵖ (H i))
  let (i : ZMod 2) : IsFiniteRank (Source i) :=
    isFiniteRank_pullback (E := (πC : T → B) *ᵖ (H i)) eMap
  let j (i : ZMod 2) : Iso (F i) (Source i) := (pullbackCompIso (E := H i) πC eMap).symm
  have hj (i : ZMod 2) (z : Z) (w : H i (base z)) : (j i).linearEquiv z w = w := by
    have h := pullbackCompIso_apply (E := H i) πC eMap z ((j i).linearEquiv z w)
    exact h.symm.trans (((pullbackCompIso (E := H i) πC eMap).linearEquiv z).apply_symm_apply w)
  let U (i : ZMod 2) : Iso (AssociatedEquivariantFiber hP (σ i)) (Source i) :=
    (hdesc i).choose.trans (j i)
  have hU (i : ZMod 2) (p : P) (z : W) (w : Parity i) :
      ((U i).linearEquiv (associatedBundleMk GO P W p z)
        (associatedEquivariantFiberMk hP (σ i) p z rfl w)).val =
          ExteriorAlgebra.map (L p).toLinearMap w.val := by
    change ((j i).linearEquiv _ ((hdesc i).choose.linearEquiv _ _)).val = _
    rw [hj]
    exact (hdesc i).choose_spec p z w
  have hsymbol (p : P) (v : W) (a : ExteriorAlgebra ℂ W) :
      ExteriorAlgebra.map (L p).toLinearMap (cliffordSymbol v a) =
        cliffordSymbol (L p v) (ExteriorAlgebra.map (L p).toLinearMap a) := by
    have hcontract (a : ExteriorAlgebra ℂ W) :
        CliffordAlgebra.contractLeft (innerₛₗ ℂ (L p v))
            (ExteriorAlgebra.map (L p).toLinearMap a) =
          ExteriorAlgebra.map (L p).toLinearMap
            (CliffordAlgebra.contractLeft (innerₛₗ ℂ v) a) := by
      induction a using CliffordAlgebra.left_induction with
      | algebraMap r =>
        simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
      | add a b ha hb => simp only [map_add, ha, hb]
      | ι_mul a w ha =>
        rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
          CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
          ExteriorAlgebra.map_apply_ι, ha]
        change inner ℂ (L p v) (L p w) • _ - _ = inner ℂ v w • _ - _
        rw [show inner ℂ (L p v) (L p w) = inner ℂ v w from hpair p v w]
    change ExteriorAlgebra.map (L p).toLinearMap
      (ExteriorAlgebra.ι ℂ v * a - CliffordAlgebra.contractLeft (innerₛₗ ℂ v) a) =
      ExteriorAlgebra.ι ℂ (L p v) * ExteriorAlgebra.map (L p).toLinearMap a -
        CliffordAlgebra.contractLeft (innerₛₗ ℂ (L p v)) (ExteriorAlgebra.map (L p).toLinearMap a)
    rw [map_sub, map_mul, ExteriorAlgebra.map_apply_ι, hcontract]
    rfl
  let A := associatedSupportTriple hP (exteriorBottTriple W) (σ 0) (σ 1)
    (exteriorBottTriple_isEquivariant (orthogonalComplexification_unitary r))
  let D := exteriorThomTriple C h.continuous_pairing
  let Q := D.pullback eMap e.isProperMap
  have hzero (p : P) (y : W) : associatedBundleMk GO P W p y ∈ A.control ↔ y = 0 :=
    associatedControl_mk_mem_iff (exteriorBottTriple W).control
      (exteriorBottTriple_isEquivariant
        (orthogonalComplexification_unitary r)).invariant_control p y
  have hAboundary (p : P) (y : W) (hy : y ≠ 0) (v : Parity 0) :
      A.boundary.linearEquiv
          ⟨associatedBundleMk GO P W p y, fun hz ↦ hy ((hzero p y).mp hz)⟩
          (associatedEquivariantFiberMk hP (σ 0) p y rfl v) =
        associatedEquivariantFiberMk hP (σ 1) p y rfl (cliffordSymbolParity y 0 v) :=
    associatedSupportBoundary_apply hP (exteriorBottTriple W) (σ 0) (σ 1)
      (exteriorBottTriple_isEquivariant (orthogonalComplexification_unitary r)) p ⟨y, hy⟩ v
  have hQboundary (z : (Q.controlᶜ : Set Z)) (w : Source 0 z) :
      Q.boundary.linearEquiv z w = cliffordSymbolParity (e z.val).snd 0 w := by
    exact RelativeTriple.pullback_apply D.boundary eMap z w
  have hAclass : associatedSupportKZero hP
        (equivariantExteriorBottClass (orthogonalComplexification_unitary r)) =
      A.compactSupportClass := by
    rw [equivariantExteriorBottClass, associatedSupportKZero_class]
    rfl
  have hQclass : Q.compactSupportClass =
      compactSupportKZeroPullback eMap e.isProperMap
        (exteriorThomClass C h.continuous_pairing) :=
    D.compactSupportClass_pullback eMap e.isProperMap
  have hmk (p : P) (y : W) (w : AssociatedEquivariantFiber hP (σ 0)
      (associatedBundleMk GO P W p y)) :
      ∃ v : Parity 0, associatedEquivariantFiberMk hP (σ 0) p y rfl v = w :=
    (associatedEquivariantFiberMk_bijective hP (σ 0) p y rfl).surjective w
  clear_value U A Q σ hP
  -- Enlarge both exact controls once; compare the original boundary on this common exterior.
  let K := A.control ∪ Q.control
  have hK : IsCompact K := A.isCompact_control.union Q.isCompact_control
  have hAK : A.control ⊆ K := Set.subset_union_left
  have hQK : Q.control ⊆ K := Set.subset_union_right
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hsquare : ∀ (z : (Kᶜ : Set Z)) (w : AssociatedEquivariantFiber hP (σ 0) z),
      (U 1).linearEquiv z ((A.enlarge K hK hAK).boundary.linearEquiv z w) =
        (Q.enlarge K hK hQK).boundary.linearEquiv z ((U 0).linearEquiv z w) := by
    rintro ⟨z, hz⟩ w
    induction z using Quotient.inductionOn with
    | h t =>
      change AssociatedEquivariantFiber hP (σ 0)
        (associatedBundleMk GO P W t.1 t.2) at w
      let v : Parity 0 := (hmk t.1 t.2 w).choose
      have hv : associatedEquivariantFiberMk hP (σ 0) t.1 t.2 rfl v = w :=
        (hmk t.1 t.2 w).choose_spec
      rw [← hv]
      have hy : t.2 ≠ 0 := by
        intro hy
        exact hz (Or.inl ((hzero t.1 t.2).mpr hy))
      let z : (Kᶜ : Set Z) := ⟨associatedBundleMk GO P W t.1 t.2, hz⟩
      let a := associatedEquivariantFiberMk hP (σ 0) t.1 t.2 rfl v
      have hleft := (A.enlarge_apply K hK hAK z a).trans (hAboundary t.1 t.2 hy v)
      have hright := (Q.enlarge_apply K hK hQK z ((U 0).linearEquiv z a)).trans
        (hQboundary ⟨z.val, fun hx ↦ z.property (hQK hx)⟩ ((U 0).linearEquiv z a))
      refine (congrArg ((U 1).linearEquiv z) hleft).trans (Eq.trans ?_ hright.symm)
      apply Subtype.ext
      refine (hU 1 t.1 t.2 (cliffordSymbolParity t.2 0 v)).trans ?_
      change ExteriorAlgebra.map (L t.1).toLinearMap (cliffordSymbol t.2 v.val) =
        cliffordSymbol (e (associatedBundleMk GO P W t.1 t.2)).snd
          (((U 0).linearEquiv (associatedBundleMk GO P W t.1 t.2)
            (associatedEquivariantFiberMk hP (σ 0) t.1 t.2 rfl v)).val)
      rw [hefib t.1 t.2, hU 0 t.1 t.2 v]
      exact hsymbol t.1 t.2 v.val
  have htriples : (A.enlarge K hK hAK).congr (U 0) (U 1) = Q.enlarge K hK hQK := by
    change CompactSupportTriple.mk K hK _ = CompactSupportTriple.mk K hK _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro w
    change (U 1).linearEquiv z ((A.enlarge K hK hAK).boundary.linearEquiv z
      ((U 0).symm.linearEquiv z w)) = (Q.enlarge K hK hQK).boundary.linearEquiv z w
    exact (hsquare z ((U 0).symm.linearEquiv z w)).trans
      (congrArg ((Q.enlarge K hK hQK).boundary.linearEquiv z)
        (((U 0).linearEquiv z).apply_symm_apply w))
  have hclass : A.compactSupportClass = Q.compactSupportClass := by
    calc
      A.compactSupportClass = (A.enlarge K hK hAK).compactSupportClass :=
        (A.compactSupportClass_enlarge K hK hAK).symm
      _ = ((A.enlarge K hK hAK).congr (U 0) (U 1)).compactSupportClass :=
        ((A.enlarge K hK hAK).compactSupportClass_congr (U 0) (U 1)).symm
      _ = (Q.enlarge K hK hQK).compactSupportClass := congrArg _ htriples
      _ = Q.compactSupportClass := Q.compactSupportClass_enlarge K hK hQK
  have hThom : associatedSupportKZero hP
        (equivariantExteriorBottClass (orthogonalComplexification_unitary r)) =
      compactSupportKZeroPullback eMap e.isProperMap
        (exteriorThomClass C h.continuous_pairing) := by
    exact hAclass.trans (hclass.trans hQclass)
  refine ⟨e, ?_, hThom⟩
  intro p z
  exact (hf _).trans (hη p z)

end AtiyahSinger
