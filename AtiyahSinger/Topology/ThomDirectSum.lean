/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleSumTotalSpace
public import AtiyahSinger.Topology.ExteriorBundleSum
public import AtiyahSinger.Topology.HermitianMetricPullback
public import AtiyahSinger.Topology.HermitianMetricSum
public import AtiyahSinger.Topology.HermitianSupportedThom
public import AtiyahSinger.Topology.ModelBundleTopology
public import AtiyahSinger.Topology.ThomCutoffNormalization
public import AtiyahSinger.Topology.ThomNaturality
public import AtiyahSinger.Topology.ThomTensorReassociation

/-!
# Direct sums and the zero-rank normalization of the supported Thom operator

Public module ID: M2246.

The standard multiplicativity of the complex Thom construction is stated for
the actual noncompact supported operators. First apply the Thom operator for E,
then that for the original pullback of F to E. The target is identified with
the total space of E plus F by its specified reassociation homeomorphism.
The order is E first, F second, matching the ordered exterior tensor product.

KA IV.1.7--1.8 proves the compact-base exterior-class formula. The supported
operator version uses IV.1.10 and a common compact control for its homotopies;
it is not an equality of bare noncompact Thom classes. No compact-support
pullback along the generally nonproper bundle projection is used.

The zero-rank statement identifies the actual map with transport by the zero
section. Ordered exterior multiplication preserves the graded sum of the
actual wedge-minus-contraction symbols.
The direct-sum operator comparison follows from an affine cutoff homotopy on
one common compact control, retaining the actual native tensor boundaries.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open scoped TensorProduct

/-- Ordered exterior multiplication preserves the graded sum of wedge-minus-contraction symbols.
The second factor acts with the original parity involution on the first factor. -/
theorem exteriorSumTensorMap_symbol {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (dV : Module.Dual ℂ V) (dW : Module.Dual ℂ W) (v : V) (w : W)
    (a : ExteriorAlgebra ℂ V) (b : ExteriorAlgebra ℂ W) :
    ExteriorAlgebra.ι ℂ (v, w) * exteriorSumTensorMap (a ⊗ₜ[ℂ] b) -
        CliffordAlgebra.contractLeft (dV.coprod dW) (exteriorSumTensorMap (a ⊗ₜ[ℂ] b)) =
      exteriorSumTensorMap
        ((ExteriorAlgebra.ι ℂ v * a - CliffordAlgebra.contractLeft dV a) ⊗ₜ[ℂ] b +
          CliffordAlgebra.involute a ⊗ₜ[ℂ]
            (ExteriorAlgebra.ι ℂ w * b - CliffordAlgebra.contractLeft dW b)) := by
  /- The contraction is an odd derivation and commutes with the two inclusions.
  Moving a generator from the second summand past the first exterior factor
  contributes its parity involution. Subtract the contraction identity from the
  wedge identity with the given order; no metric or finite-rank choice enters. -/
  let iV := ExteriorAlgebra.map (LinearMap.inl ℂ V W)
  let iW := ExteriorAlgebra.map (LinearMap.inr ℂ V W)
  let d := dV.coprod dW
  have hcontract_mul (x y : ExteriorAlgebra ℂ (V × W)) :
      CliffordAlgebra.contractLeft d (x * y) =
        CliffordAlgebra.contractLeft d x * y +
          CliffordAlgebra.involute x * CliffordAlgebra.contractLeft d y := by
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r =>
      simp only [CliffordAlgebra.contractLeft_algebraMap_mul,
        CliffordAlgebra.contractLeft_algebraMap, AlgHom.commutes, zero_mul, zero_add]
    | add x x' hx hx' =>
      simp only [add_mul, map_add, hx, hx']
      abel
    | ι_mul x u hx =>
      rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, hx, map_mul, CliffordAlgebra.involute_ι]
      simp only [smul_mul_assoc, mul_add, sub_mul, neg_mul, mul_assoc]
      noncomm_ring
  have hcontract_V (x : ExteriorAlgebra ℂ V) :
      CliffordAlgebra.contractLeft d (iV x) =
        iV (CliffordAlgebra.contractLeft dV x) := by
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r =>
      simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
    | ι_mul x u hx =>
      have hι : iV (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) u) =
          CliffordAlgebra.ι (0 : QuadraticForm ℂ (V × W)) (u, 0) :=
        ExteriorAlgebra.map_apply_ι (LinearMap.inl ℂ V W) u
      rw [map_mul, hι, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, hι, hx]
      simp only [d, LinearMap.coprod_apply, map_zero, add_zero]
  have hcontract_W (x : ExteriorAlgebra ℂ W) :
      CliffordAlgebra.contractLeft d (iW x) =
        iW (CliffordAlgebra.contractLeft dW x) := by
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r =>
      simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap, map_zero]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
    | ι_mul x u hx =>
      have hι : iW (CliffordAlgebra.ι (0 : QuadraticForm ℂ W) u) =
          CliffordAlgebra.ι (0 : QuadraticForm ℂ (V × W)) (0, u) :=
        ExteriorAlgebra.map_apply_ι (LinearMap.inr ℂ V W) u
      rw [map_mul, hι, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul, hι, hx]
      simp only [d, LinearMap.coprod_apply, map_zero, zero_add]
  have hinvolute (x : ExteriorAlgebra ℂ V) :
      CliffordAlgebra.involute (iV x) = iV (CliffordAlgebra.involute x) := by
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | ι_mul x u hx =>
      have hι : iV (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) u) =
          CliffordAlgebra.ι (0 : QuadraticForm ℂ (V × W)) (u, 0) :=
        ExteriorAlgebra.map_apply_ι (LinearMap.inl ℂ V W) u
      simp only [map_mul, hι, CliffordAlgebra.involute_ι, hx, map_neg]
  have hsecond (x : ExteriorAlgebra ℂ V) :
      ExteriorAlgebra.ι ℂ (0, w) * iV x =
        iV (CliffordAlgebra.involute x) * ExteriorAlgebra.ι ℂ (0, w) := by
    induction x using CliffordAlgebra.left_induction with
    | algebraMap r =>
      simp only [AlgHom.commutes]
      exact (Algebra.commutes r _).symm
    | add x y hx hy =>
      simp only [map_add, mul_add, add_mul, hx, hy]
    | ι_mul x u hx =>
      have hι : iV (CliffordAlgebra.ι (0 : QuadraticForm ℂ V) u) =
          ExteriorAlgebra.ι ℂ (u, 0) :=
        ExteriorAlgebra.map_apply_ι (LinearMap.inl ℂ V W) u
      have hswap : ExteriorAlgebra.ι ℂ (0, w) * ExteriorAlgebra.ι ℂ (u, 0) =
          -(ExteriorAlgebra.ι ℂ (u, 0) * ExteriorAlgebra.ι ℂ (0, w)) :=
        eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (0, w) (u, 0))
      rw [map_mul, hι, ← mul_assoc, hswap, neg_mul, mul_assoc, hx,
        map_mul, CliffordAlgebra.involute_ι, map_mul, map_neg, hι]
      simp only [neg_mul, mul_assoc]
  have hι : ExteriorAlgebra.ι ℂ (v, w) =
      iV (ExteriorAlgebra.ι ℂ v) + iW (ExteriorAlgebra.ι ℂ w) := by
    rw [show (v, w) = (v, 0) + (0, w) from by simp, map_add]
    simp only [iV, iW, ExteriorAlgebra.map_apply_ι, LinearMap.inl_apply,
      LinearMap.inr_apply]
  have hpure (x : ExteriorAlgebra ℂ V) (y : ExteriorAlgebra ℂ W) :
      exteriorSumTensorMap (x ⊗ₜ[ℂ] y) = iV x * iW y := rfl
  rw [map_add, TensorProduct.sub_tmul, TensorProduct.tmul_sub,
    map_sub, map_sub, hpure, hpure, hpure, hpure, hpure]
  rw [hcontract_mul, hcontract_V, hcontract_W, hinvolute, hι,
    add_mul, map_mul, map_mul]
  have hs : iW (ExteriorAlgebra.ι ℂ w) * (iV a * iW b) =
      iV (CliffordAlgebra.involute a) * (iW (ExteriorAlgebra.ι ℂ w) * iW b) := by
    rw [show iW (ExteriorAlgebra.ι ℂ w) = ExteriorAlgebra.ι ℂ (0, w) from
      ExteriorAlgebra.map_apply_ι (LinearMap.inr ℂ V W) w]
    change ExteriorAlgebra.ι ℂ (0, w) * (iV a * iW b) =
      iV (CliffordAlgebra.involute a) * (ExteriorAlgebra.ι ℂ (0, w) * iW b)
    rw [← mul_assoc, hsecond, mul_assoc]
  rw [hs]
  noncomm_ring

section ParitySymbol

open Bundle
open scoped TensorProduct

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity

variable {X : Type*} [TopologicalSpace X]
  {E F : X → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, InnerProductSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Normalize the ordered exterior parity comparison and both reciprocal symbol blocks.
/-- The ordered exterior comparison preserves both original reciprocal symbol blocks. -/
private theorem exists_exteriorParity_sum_symbol_iso :
    let P (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
    let Q (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
    let S (i : ZMod 2) := fun x ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((E ×ᵇ F) x)) i
    ∃ u₀ : Iso ((fun x ↦ P 0 x ⊗[ℂ] Q 0 x) ×ᵇ (fun x ↦ P 1 x ⊗[ℂ] Q 1 x)) (fun x ↦ S 0 x),
      ∃ u₁ : Iso ((fun x ↦ P 1 x ⊗[ℂ] Q 0 x) ×ᵇ (fun x ↦ P 0 x ⊗[ℂ] Q 1 x)) (fun x ↦ S 1 x),
        ∀ x (v : E x) (w : F x),
          let C := Algebra.lmul ℂ (ExteriorAlgebra ℂ (E x × F x)) (ExteriorAlgebra.ι ℂ (v, w)) -
            CliffordAlgebra.contractLeft ((innerₛₗ ℂ v).coprod (innerₛₗ ℂ w))
          ((S 1 x).subtype.comp (u₁.linearEquiv x).toLinearMap).comp
              (reciprocalTensorSymbol (cliffordSymbolParity v 0) (cliffordSymbolParity v 1)
                (cliffordSymbolParity w 0) (cliffordSymbolParity w 1)) =
            C.comp ((S 0 x).subtype.comp (u₀.linearEquiv x).toLinearMap) ∧
          ((S 0 x).subtype.comp (u₀.linearEquiv x).toLinearMap).comp
              (reciprocalTensorSymbolReverse (cliffordSymbolParity v 0) (cliffordSymbolParity v 1)
                (cliffordSymbolParity w 0) (cliffordSymbolParity w 1)) =
            C.comp ((S 1 x).subtype.comp (u₁.linearEquiv x).toLinearMap) := by
  obtain ⟨u₀, u₁, hu₀, hu₁⟩ := exists_exteriorParity_sum_iso (E := E) (F := F)
  refine ⟨u₀, u₁, ?_⟩
  intro x v w
  dsimp only
  have hE (i : ZMod 2) (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i) :
      (cliffordSymbolParity v i a).val = ExteriorAlgebra.ι ℂ v * a.val -
        CliffordAlgebra.contractLeft (innerₛₗ ℂ v) a.val := rfl
  have hF (i : ZMod 2) (a : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i) :
      (cliffordSymbolParity w i a).val = ExteriorAlgebra.ι ℂ w * a.val -
        CliffordAlgebra.contractLeft (innerₛₗ ℂ w) a.val := rfl
  have hS (a : ExteriorAlgebra ℂ (E x × F x)) :
      (Algebra.lmul ℂ (ExteriorAlgebra ℂ (E x × F x)) (ExteriorAlgebra.ι ℂ (v, w)) -
        CliffordAlgebra.contractLeft ((innerₛₗ ℂ v).coprod (innerₛₗ ℂ w)) :
          Module.End ℂ (ExteriorAlgebra ℂ (E x × F x))) a =
      ExteriorAlgebra.ι ℂ (v, w) * a -
        CliffordAlgebra.contractLeft ((innerₛₗ ℂ v).coprod (innerₛₗ ℂ w)) a := rfl
  constructor
  all_goals
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro a b
  all_goals
    have h := exteriorSumTensorMap_symbol (innerₛₗ ℂ v) (innerₛₗ ℂ w) v w a.val b.val
    simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearMap.inr_apply,
      LinearEquiv.coe_coe, Submodule.subtype_apply,
      reciprocalTensorSymbol, reciprocalTensorSymbolReverse,
      LinearMap.prod_apply, Function.prod_apply, LinearMap.coprod_apply, TensorProduct.map_tmul,
      LinearMap.neg_apply, LinearMap.id_apply, map_zero, add_zero, zero_add,
      hu₀, hu₁, map_add, map_neg]
    simp only [hS]
  · erw [hE 0 a, hF 0 b]
    simpa only [CliffordAlgebra.involute_eq_of_mem_even a.property, map_add] using h.symm
  · erw [hE 1 a, hF 1 b, add_comm]
    simpa only [CliffordAlgebra.involute_eq_of_mem_odd a.property,
      TensorProduct.neg_tmul, map_add, map_neg] using h.symm
  · erw [hE 1 a, hF 0 b]
    simpa only [CliffordAlgebra.involute_eq_of_mem_odd a.property,
      TensorProduct.neg_tmul, map_add, map_neg] using h.symm
  · erw [hE 0 a, hF 1 b, add_comm]
    simpa only [CliffordAlgebra.involute_eq_of_mem_even a.property,
      map_add] using h.symm


end ParitySymbol

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The existing skew Thom convention is the reciprocal convention with the negative reverse. -/
private theorem thomTensorSymbol_eq_reciprocal {A B V : Type*} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (d : A →ₗ[ℂ] B) (d' : B →ₗ[ℂ] A) (v : V) :
    thomTensorSymbol d d' v = reciprocalTensorSymbol d (-d')
      (cliffordSymbolParity v 0) (cliffordSymbolParity v 1) ∧
    thomTensorSymbolReverse d d' v = reciprocalTensorSymbolReverse d (-d')
      (cliffordSymbolParity v 0) (cliffordSymbolParity v 1) := by
  constructor <;> apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
    intro a b <;> apply Prod.ext <;> simp [thomTensorSymbol, thomTensorSymbolReverse,
      reciprocalTensorSymbol, reciprocalTensorSymbolReverse, TensorProduct.neg_tmul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 6000000 in
-- Normalize the ordered tensor reassociation of the same two native Thom symbols.
omit [LocallyCompactSpace X] [T2Space X] in
/-- Ordered tensor reassociation identifies the same two Thom symbols in the native topologies. -/
private theorem exists_thom_sum_symbol_iso (hE : ContinuousHermitianMetric E)
    (hF : ContinuousHermitianMetric F) (J K : FiniteBundle X) :
    let := fun x ↦ (hE.toCore x).toNormedAddCommGroup
    let := fun x ↦ InnerProductSpace.ofCore (hE.toCore x).toCore
    let := fun x ↦ (hF.toCore x).toNormedAddCommGroup
    let := fun x ↦ InnerProductSpace.ofCore (hF.toCore x).toCore
    let := fun x ↦ ((hE.sum hF).toCore x).toNormedAddCommGroup
    let := fun x ↦ ((hE.sum hF).toCore x).toNormedAddCommGroup.toSeminormedAddCommGroup
    let := fun x ↦ InnerProductSpace.ofCore ((hE.sum hF).toCore x).toCore
    let P (i : ZMod 2) : X → Type _ := fun x ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
    let Q (i : ZMod 2) : X → Type _ := fun x ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
    let S (i : ZMod 2) : X → Type _ := fun x ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((E ×ᵇ F) x)) i
    let A := fun x ↦ (J.Fiber x ⊗[ℂ] P 0 x) × (K.Fiber x ⊗[ℂ] P 1 x)
    let B := fun x ↦ (K.Fiber x ⊗[ℂ] P 0 x) × (J.Fiber x ⊗[ℂ] P 1 x)
    ∃ R₀ : Iso (fun x ↦ (A x ⊗[ℂ] Q 0 x) × (B x ⊗[ℂ] Q 1 x))
        (fun x ↦ (J.Fiber x ⊗[ℂ] S 0 x) × (K.Fiber x ⊗[ℂ] S 1 x)),
      ∃ R₁ : Iso (fun x ↦ (B x ⊗[ℂ] Q 0 x) × (A x ⊗[ℂ] Q 1 x))
        (fun x ↦ (K.Fiber x ⊗[ℂ] S 0 x) × (J.Fiber x ⊗[ℂ] S 1 x)),
        ∀ x (d : J.Fiber x →ₗ[ℂ] K.Fiber x) (d' : K.Fiber x →ₗ[ℂ] J.Fiber x)
          (v : E x) (w : F x),
          (R₁.linearEquiv x).toLinearMap.comp
            (thomTensorSymbol (thomTensorSymbol d d' v) (-(thomTensorSymbolReverse d d' v)) w) =
          (thomTensorSymbol d d' (v, w)).comp (R₀.linearEquiv x).toLinearMap := by
  dsimp only
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (hE.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (hE.toCore x).toCore
  let : ∀ x, NormedAddCommGroup (F x) := fun x ↦ (hF.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := fun x ↦
    InnerProductSpace.ofCore (hF.toCore x).toCore
  let : ∀ x, NormedAddCommGroup ((E ×ᵇ F) x) :=
    fun x ↦ ((hE.sum hF).toCore x).toNormedAddCommGroup
  let : ∀ x, SeminormedAddCommGroup ((E ×ᵇ F) x) :=
    fun x ↦ ((hE.sum hF).toCore x).toNormedAddCommGroup.toSeminormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ ((E ×ᵇ F) x) := fun x ↦
    InnerProductSpace.ofCore ((hE.sum hF).toCore x).toCore
  let P (i : ZMod 2) : X → Type _ := fun x ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
  let Q (i : ZMod 2) : X → Type _ := fun x ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
  obtain ⟨u₀, u₁, hu⟩ := exists_exteriorParity_sum_symbol_iso (E := E) (F := F)
  obtain ⟨g₀, hg₀⟩ := exists_graded_tensor_assoc_iso
    J.Fiber K.Fiber (P 0) (P 1) (Q 0) (Q 1)
  obtain ⟨g₁, hg₁⟩ := exists_graded_tensor_assoc_iso
    K.Fiber J.Fiber (P 0) (P 1) (Q 0) (Q 1)
  let L₀ := ((Iso.refl J.Fiber).tensor u₀).sum ((Iso.refl K.Fiber).tensor u₁)
  let L₁ := ((Iso.refl K.Fiber).tensor u₀).sum ((Iso.refl J.Fiber).tensor u₁)
  refine ⟨g₀.trans L₀, g₁.trans L₁, ?_⟩
  intro x d d' v w
  let e := reciprocalTensorSymbol (cliffordSymbolParity v 0) (cliffordSymbolParity v 1)
    (cliffordSymbolParity w 0) (cliffordSymbolParity w 1)
  let e' := reciprocalTensorSymbolReverse (cliffordSymbolParity v 0) (cliffordSymbolParity v 1)
    (cliffordSymbolParity w 0) (cliffordSymbolParity w 1)
  have h₀ (a) : u₁.linearEquiv x (e a) =
      cliffordSymbolParity (v, w) 0 (u₀.linearEquiv x a) := by
    apply Subtype.ext
    exact LinearMap.congr_fun (hu x v w).1 a
  have h₁ (a) : u₀.linearEquiv x (e' a) =
      cliffordSymbolParity (v, w) 1 (u₁.linearEquiv x a) := by
    apply Subtype.ext
    exact LinearMap.congr_fun (hu x v w).2 a
  have houter : (L₁.linearEquiv x).toLinearMap.comp (reciprocalTensorSymbol d (-d') e e') =
      (reciprocalTensorSymbol d (-d') (cliffordSymbolParity (v, w) 0)
        (cliffordSymbolParity (v, w) 1)).comp (L₀.linearEquiv x).toLinearMap := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    as_aux_lemma =>
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
        intro a b <;> apply Prod.ext <;>
        simp [L₀, L₁, Iso.tensor, Iso.sum, Iso.refl, reciprocalTensorSymbol, h₀, h₁]
  have hassoc := reciprocalTensorSymbol_assoc (J.Fiber x) (K.Fiber x)
    (P 0 x) (P 1 x) (Q 0 x) (Q 1 x) d (-d')
    (cliffordSymbolParity v 0) (cliffordSymbolParity v 1)
    (cliffordSymbolParity w 0) (cliffordSymbolParity w 1)
  rw [← hg₀ x, ← hg₁ x] at hassoc
  erw [(thomTensorSymbol_eq_reciprocal _ _ w).1, neg_neg,
    (thomTensorSymbol_eq_reciprocal d d' v).1, (thomTensorSymbol_eq_reciprocal d d' v).2,
    (thomTensorSymbol_eq_reciprocal d d' (v, w)).1]
  change ((L₁.linearEquiv x).toLinearMap.comp (g₁.linearEquiv x).toLinearMap).comp _ =
    LinearMap.comp _ ((L₀.linearEquiv x).toLinearMap.comp (g₀.linearEquiv x).toLinearMap)
  rw [LinearMap.comp_assoc, hassoc, ← LinearMap.comp_assoc, houter, LinearMap.comp_assoc]



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Normalize the specified polymorphic tensor pullback before native fiber instantiation.
/-- The specified tensor pullback transport, kept polymorphic before native fiber instantiation. -/
private theorem exists_thomTensor_pullback_iso {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : C(Y, X)) (q : C(Z, Y)) (F A B : X → Type*) (J K : Y → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
    [∀ x, AddCommGroup (B x)] [∀ x, Module ℂ (B x)]
    [∀ y, AddCommGroup (J y)] [∀ y, Module ℂ (J y)]
    [∀ y, AddCommGroup (K y)] [∀ y, Module ℂ (K y)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    [TopologicalSpace (TotalSpace Unit A)] [IsFiniteRank A]
    [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B]
    [TopologicalSpace (TotalSpace Unit J)] [IsFiniteRank J]
    [TopologicalSpace (TotalSpace Unit K)] [IsFiniteRank K]
    (u : Iso J (p *ᵖ A)) (v : Iso K (p *ᵖ B)) :
    let P (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
    let Pp (i : ZMod 2) := fun y ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((p *ᵖ F) y)) i
    ∃ N : Iso (q *ᵖ fun y ↦ (J y ⊗[ℂ] Pp 0 y) × (K y ⊗[ℂ] Pp 1 y))
        ((p.comp q) *ᵖ fun x ↦ (A x ⊗[ℂ] P 0 x) × (B x ⊗[ℂ] P 1 x)),
      ∀ z w, N.linearEquiv z w =
        ((TensorProduct.congr (u.linearEquiv (q z))
          (LinearEquiv.refl ℂ (P 0 (p (q z))))).prodCongr
            (TensorProduct.congr (v.linearEquiv (q z))
            (LinearEquiv.refl ℂ (P 1 (p (q z)))))) w := by
  dsimp only
  let P (i : ZMod 2) : X → Type _ := fun x ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
  obtain ⟨j₀, hj₀⟩ := exteriorParity_pullback_comparison F p 0
  obtain ⟨j₁, hj₁⟩ := exteriorParity_pullback_comparison F p 1
  obtain ⟨k, hk⟩ := tensorSum_pullback_comparison
    (E := A) (F := P 0) (G := B) (H := P 1) p
  let S := fun x ↦ (A x ⊗[ℂ] P 0 x) × (B x ⊗[ℂ] P 1 x)
  let N := ((((u.tensor j₀).sum (v.tensor j₁)).trans k).pullback q).trans
    (pullbackCompIso (E := S) p q)
  refine ⟨N, ?_⟩
  intro z w
  -- Both pullback comparisons retain the vector; only u and v act on the source factors.
  change (pullbackCompIso (E := S) p q).linearEquiv z
    (k.linearEquiv (q z) (((u.tensor j₀).sum (v.tensor j₁)).linearEquiv (q z) w)) = _
  refine (pullbackCompIso_apply (E := S) p q z _).trans ?_
  refine (hk (q z) _).trans ?_
  change
    ((TensorProduct.congr (u.linearEquiv (q z)) (j₀.linearEquiv (q z))) w.1,
      (TensorProduct.congr (v.linearEquiv (q z)) (j₁.linearEquiv (q z))) w.2) = _
  apply Prod.ext
  · change (TensorProduct.congr (u.linearEquiv (q z)) (j₀.linearEquiv (q z))) w.1 =
      (TensorProduct.congr (u.linearEquiv (q z))
        (LinearEquiv.refl ℂ (P 0 (p (q z))))) w.1
    induction w.1 using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hj₀]
    | add a b ha hb => simp only [map_add, ha, hb]
  · change (TensorProduct.congr (v.linearEquiv (q z)) (j₁.linearEquiv (q z))) w.2 =
      (TensorProduct.congr (v.linearEquiv (q z))
        (LinearEquiv.refl ℂ (P 1 (p (q z))))) w.2
    induction w.2 using TensorProduct.inductionOn with
    | tmul a b =>
      simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, hj₁]
    | add a b ha hb => simp only [map_add, ha, hb]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Normalize the same tensor pullback after removing small-model resizing.
/-- The same tensor pullback transport after removing small-model resizing. -/
private theorem exists_thomTensor_unresized_pullback_iso {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (p : C(Y, X)) (q : C(Z, Y)) (F A B : X → Type*)
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
    [∀ x, AddCommGroup (B x)] [∀ x, Module ℂ (B x)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    [TopologicalSpace (TotalSpace Unit A)] [IsFiniteRank A]
    [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B] :
    let P (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
    let Pp (i : ZMod 2) := fun y ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((p *ᵖ F) y)) i
    ∃ N : Iso (q *ᵖ fun y ↦ ((p *ᵖ A) y ⊗[ℂ] Pp 0 y) × ((p *ᵖ B) y ⊗[ℂ] Pp 1 y))
        ((p.comp q) *ᵖ fun x ↦ (A x ⊗[ℂ] P 0 x) × (B x ⊗[ℂ] P 1 x)),
      ∀ z w, N.linearEquiv z w = w := by
  dsimp only
  obtain ⟨N, hN⟩ := exists_thomTensor_pullback_iso p q F A B (p *ᵖ A) (p *ᵖ B)
    (Iso.refl _) (Iso.refl _)
  refine ⟨N, ?_⟩
  intro z w
  have h := hN z w
  simpa only [Iso.refl, TensorProduct.congr_refl_refl,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, Prod.mk.eta] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- Normalize the direct-sum supported Thom map and its prescribed iterated operator.
/-- Thom multiplication for an orthogonal direct sum is the prescribed iterated operator. -/
theorem supportedThomHom_sum (hE : ContinuousHermitianMetric E)
    (hF : ContinuousHermitianMetric F) :
    let proj : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
    letI := isFiniteRank_pullback (E := F) proj
    (compactSupportKZeroHomeomorph (sumTotalPullbackHomeomorph (E := E) (F := F))).comp
        (hE.sum hF).supportedThomHom =
      (hF.pullback proj).supportedThomHom.comp hE.supportedThomHom := by
  /- Stage 1: fix an original support representative and one admissible base
  cutoff rho with enlarged compact control L. The first Thom tensor symbol F_E
  has reverse block G_E and F_E G_E = G_E F_E = -A, where
  A = rho^2 + norm(e)^2. Its control is the zero section over L.
  Stage 2: applying the second Thom operator chooses another cutoff psi on E,
  equal to one outside a compact M containing that first control. Its two base
  maps are psi F_E and psi F_E^{-1}, extended by zero near the first control.
  They are not literally F_E and -G_E. On A nonzero interpolate their scalar
  coefficients to 1 and 1: (1-t)psi+t and (1-t)psi/A+t. Continuity uses the
  affine family of the two actual continuous endpoint boundary maps. The
  composite scalar is nonnegative everywhere and positive off M. Together
  with the negative-square F exterior symbol, this yields an invertible homotopy
  off the zero section of the pulled-back F over M. That set is compact for
  the whole homotopy. No arbitrary properness of the projection is required.
  Stage 3: at the final endpoint the odd operator is the genuine graded sum
  D_a tensor 1 + Gamma_a tensor C_E tensor 1 + Gamma_a Gamma_E tensor C_F.
  Use the standard exterior tensor isomorphism in the E-before-F order:
  xi tensor eta maps to inclusion_E(xi) wedge inclusion_F(eta).
  It preserves parity and identifies this symbol with the original symbol for
  E plus F with its orthogonal sum metric. The actual reassociation sends
  (x,(e,f)) to ((x,e),f), and the compact supports correspond under this map.
  Stage 4: the common-control homotopy, original representative formula and
  surjectivity of support representatives give the equality of homomorphisms.
  This extends the source compact-class formula to supported operators. It
  neither pulls a Kc class back along pi_E nor treats the first output symbol
  and its cutoff inverse as equal to their final homotopic normalizations. -/
 classical
  have thom_symbol_intertwining
      {A₀ : Type (0)} {A₁ : Type (0)} {B₀ : Type (u_2)} {B₁ : Type (u_2)} {W : Type (u_3)}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
      [NormedAddCommGroup W] [InnerProductSpace ℂ W]
      (d : A₀ →ₗ[ℂ] A₁) (d' : A₁ →ₗ[ℂ] A₀)
      (e : B₀ →ₗ[ℂ] B₁) (e' : B₁ →ₗ[ℂ] B₀)
      (u : A₀ →ₗ[ℂ] B₀) (v : A₁ →ₗ[ℂ] B₁) (w : W)
      (h : ∀ x, v (d x) = e (u x)) (h' : ∀ x, u (d' x) = e' (v x)) :
      ((TensorProduct.map v LinearMap.id).prodMap (TensorProduct.map u LinearMap.id)).comp
          (thomTensorSymbol d d' w) =
        (thomTensorSymbol e e' w).comp
          ((TensorProduct.map u LinearMap.id).prodMap (TensorProduct.map v LinearMap.id)) := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    as_aux_lemma =>
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
        intro a b <;> apply Prod.ext <;> simp [thomTensorSymbol, h, h']
  have thom_symbol_affine {A₀ : Type (u_2)} {A₁ : Type (u_2)} {V : Type (u_3)}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (d₀ d₁ : A₀ →ₗ[ℂ] A₁) (d₀' d₁' : A₁ →ₗ[ℂ] A₀)
      (v : V) (r s : ℂ) (hrs : r + s = 1) :
      thomTensorSymbol (r • d₀ + s • d₁) (r • d₀' + s • d₁') v =
        r • thomTensorSymbol d₀ d₀' v + s • thomTensorSymbol d₁ d₁' v := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    as_aux_lemma =>
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
        intro a b <;> apply Prod.ext <;>
        simp only [thomTensorSymbol, LinearMap.coe_comp, LinearMap.coe_inl,
            LinearMap.coe_inr, Function.comp_apply, LinearMap.prod_apply, Function.prod_apply,
            LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.add_apply,
            LinearMap.smul_apply, LinearMap.id_coe, id_eq, TensorProduct.add_tmul,
            LinearMap.neg_apply, map_zero, add_zero, zero_add, LinearMap.coe_add,
            LinearMap.coe_smul, Pi.add_apply, Pi.smul_apply, Prod.smul_mk,
            TensorProduct.smul_tmul', Prod.mk_add_mk, neg_add_rev, smul_neg]
      · rw [← TensorProduct.add_tmul, ← add_smul, hrs, one_smul]
      · rw [← neg_add, ← TensorProduct.add_tmul, ← add_smul, hrs, one_smul]
      · exact add_comm _ _
  have cutoff_conjugation
      {X : Type (max u_1 u_2)} [TopologicalSpace X] {E : X → Type (u_2)}
      {F : X → Type (u_2)}
      {G : X → Type (0)}
      {H : X → Type (0)}
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
      [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
      [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
      [TopologicalSpace (TotalSpace Unit G)] [TopologicalSpace (TotalSpace Unit H)]
      (a : CompactSupportTriple E F)
      (u : Iso E G) (v : Iso F H) (ρ : C(X, I)) (x : X) (w : G x) :
      (v.linearEquiv x).symm ((a.congr u v).cutoffLinearMap ρ x w) =
        a.cutoffLinearMap ρ x ((u.linearEquiv x).symm w) := by
    classical
    by_cases hx : x ∈ a.control
    · have hx' : x ∈ (a.congr u v).control := hx
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hx', dite_eq_left hx,
        LinearMap.zero_apply, map_zero]
    · have hx' : x ∉ (a.congr u v).control := hx
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hx', dite_eq_right hx]
      change (v.linearEquiv x).symm
        ((ρ x : ℂ) • (v.linearEquiv x)
          (a.boundary.linearEquiv ⟨x, hx⟩ ((u.linearEquiv x).symm w))) = _
      rw [map_smul, LinearEquiv.symm_apply_apply]
      rfl
  have native_symbol_normalization {X : Type (max u_1 u_2)}
      {Z : Type (max (max u_1 u_2) u_3)}
      [TopologicalSpace X] [TopologicalSpace Z]
      (q : C(Z, X)) (F : X → Type (u_3))
      (A : X → Type (u_2))
      (B : X → Type (u_2))
      (J : X → Type (0))
      (K : X → Type (0))
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
      [∀ x, AddCommGroup (B x)] [∀ x, Module ℂ (B x)]
      [∀ x, AddCommGroup (J x)] [∀ x, Module ℂ (J x)]
      [∀ x, AddCommGroup (K x)] [∀ x, Module ℂ (K x)]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
      [TopologicalSpace (TotalSpace Unit A)] [IsFiniteRank A]
      [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B]
      [TopologicalSpace (TotalSpace Unit J)] [IsFiniteRank J]
      [TopologicalSpace (TotalSpace Unit K)] [IsFiniteRank K]
      (hF : ContinuousHermitianMetric F) (u : Iso J A) (v : Iso K B)
      (d : ∀ x, J x →ₗ[ℂ] K x) (d' : ∀ x, K x →ₗ[ℂ] J x)
      (e : ∀ x, A x →ₗ[ℂ] B x) (e' : ∀ x, B x →ₗ[ℂ] A x)
      (ν : ∀ z, F (q z))
      (hd : ∀ x w, v.linearEquiv x (d x w) = e x (u.linearEquiv x w))
      (hd' : ∀ x w, u.linearEquiv x (d' x w) = e' x (v.linearEquiv x w)) :
      let := fun x ↦ (hF.toCore x).toNormedAddCommGroup
      let := fun x ↦ InnerProductSpace.ofCore (hF.toCore x).toCore
      let P (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
      ∀ t : CompactSupportTriple
          (q *ᵖ fun x ↦ (J x ⊗[ℂ] P 0 x) × (K x ⊗[ℂ] P 1 x))
          (q *ᵖ fun x ↦ (K x ⊗[ℂ] P 0 x) × (J x ⊗[ℂ] P 1 x)),
        (∀ (z : (t.controlᶜ : Set Z)) w,
          t.boundary.linearEquiv z w = thomTensorSymbol (d (q z.val))
            (d' (q z.val)) (ν z.val) w) →
        ∃ N₀ : Iso (q *ᵖ fun x ↦ (J x ⊗[ℂ] P 0 x) × (K x ⊗[ℂ] P 1 x))
              (q *ᵖ fun x ↦ (A x ⊗[ℂ] P 0 x) × (B x ⊗[ℂ] P 1 x)),
          ∃ N₁ : Iso (q *ᵖ fun x ↦ (K x ⊗[ℂ] P 0 x) × (J x ⊗[ℂ] P 1 x))
              (q *ᵖ fun x ↦ (B x ⊗[ℂ] P 0 x) × (A x ⊗[ℂ] P 1 x)),
            ∀ (z : (t.controlᶜ : Set Z))
              (w : (A (q z.val) ⊗[ℂ] P 0 (q z.val)) ×
                (B (q z.val) ⊗[ℂ] P 1 (q z.val))),
              (t.congr N₀ N₁).boundary.linearEquiv z w =
                thomTensorSymbol (e (q z.val)) (e' (q z.val)) (ν z.val) w := by
    intro instNormed instInner P t ht
    let := instNormed
    let := instInner
    let P' (i : ZMod 2) : X → Type _ := fun x ↦ P i x
    let N₀ := ((u.tensor (Iso.refl (P' 0))).sum (v.tensor (Iso.refl (P' 1)))).pullback q
    let N₁ := ((v.tensor (Iso.refl (P' 0))).sum (u.tensor (Iso.refl (P' 1)))).pullback q
    refine ⟨N₀, N₁, ?_⟩
    intro z w
    refine (CompactSupportTriple.congr_apply t N₀ N₁ z w).trans ?_
    let w' := (N₀.linearEquiv z.val).symm w
    refine (congrArg (N₁.linearEquiv z.val) (ht z w')).trans ?_
    have hs := thom_symbol_intertwining
      (d (q z.val)) (d' (q z.val)) (e (q z.val)) (e' (q z.val))
      (u.linearEquiv (q z.val)).toLinearMap (v.linearEquiv (q z.val)).toLinearMap
      (ν z.val) (hd (q z.val)) (hd' (q z.val))
    refine (LinearMap.congr_fun hs w').trans ?_
    exact congrArg (thomTensorSymbol (e (q z.val)) (e' (q z.val)) (ν z.val))
      ((N₀.linearEquiv z.val).apply_symm_apply w)
  have cutoff_affine_bijective {A : Type _} {B : Type _} {V : Type _}
      [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (d : A →ₗ[ℂ] B) (g : B →ₗ[ℂ] A) (a : ℝ) (ψ τ : Set.Icc (0 : ℝ) 1) (v : V)
      (hnonneg : 0 ≤ a)
      (hsquare₀ : g.comp d = -(a : ℂ) • LinearMap.id)
      (hsquare₁ : d.comp g = -(a : ℂ) • LinearMap.id)
      (hpositive : 0 < (ψ : ℝ) * a + ‖v‖ ^ 2) :
      Function.Bijective
        (((1 - (τ : ℝ) : ℝ) : ℂ) •
            thomTensorSymbol ((ψ : ℂ) • d) ((((ψ : ℝ) / a : ℝ) : ℂ) • (-g)) v +
          ((τ : ℝ) : ℂ) • thomTensorSymbol d (-g) v).toFun := by
    have hscalar₀ : (-g).comp d = (a : ℂ) • LinearMap.id := by
      rw [LinearMap.neg_comp, hsquare₀]
      simp only [neg_smul, neg_neg]
    have hscalar₁ : d.comp (-g) = (a : ℂ) • LinearMap.id := by
      rw [LinearMap.comp_neg, hsquare₁]
      simp only [neg_smul, neg_neg]
    have hmix :
        (((1 - (τ : ℝ) : ℝ) : ℂ)) •
            thomTensorSymbol ((ψ : ℂ) • d) ((((ψ : ℝ) / a : ℝ) : ℂ) • (-g)) v +
          ((τ : ℝ) : ℂ) • thomTensorSymbol d (-g) v =
        thomTensorSymbol
          ((((1 - (τ : ℝ)) * (ψ : ℝ) + τ : ℝ) : ℂ) • d)
          ((((1 - (τ : ℝ)) * ((ψ : ℝ) / a) + τ : ℝ) : ℂ) • (-g)) v := by
      have hτ : (((1 - (τ : ℝ) : ℝ) : ℂ)) + ((τ : ℝ) : ℂ) = 1 := by
        push_cast
        ring
      refine (thom_symbol_affine ((ψ : ℂ) • d) d
        ((((ψ : ℝ) / a : ℝ) : ℂ) • (-g)) (-g) v _ _ hτ).symm.trans ?_
      congr 1 <;>
        simp only [smul_smul, ← add_smul, Complex.ofReal_add, Complex.ofReal_mul]
    rw [hmix]
    exact thomTensorSymbol_cutoff_homotopy_bijective d (-g) a ψ τ v
      hnonneg hscalar₀ hscalar₁ hpositive
  have affine_bijective_of_eq {A : Type _} {B : Type _}
      [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      (r s : ℂ) (f g f' g' : A →ₗ[ℂ] B) (hf : f = f') (hg : g = g')
      (h : Function.Bijective (r • f' + s • g').toFun) :
      Function.Bijective (r • f + s • g).toFun := by
    rw [hf, hg]
    exact h
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (hE.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (hE.toCore x).toCore
  let : ∀ x, NormedAddCommGroup (F x) := fun x ↦ (hF.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := fun x ↦
    InnerProductSpace.ofCore (hF.toCore x).toCore
  let : ∀ x, NormedAddCommGroup ((E ×ᵇ F) x) :=
    fun x ↦ ((hE.sum hF).toCore x).toNormedAddCommGroup
  let : ∀ x, SeminormedAddCommGroup ((E ×ᵇ F) x) :=
    fun x ↦ ((hE.sum hF).toCore x).toNormedAddCommGroup.toSeminormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ ((E ×ᵇ F) x) := fun x ↦
    InnerProductSpace.ofCore ((hE.sum hF).toCore x).toCore
  let Y := TotalSpace Unit E
  let p : C(Y, X) := ⟨π Unit E, continuous_proj⟩
  let Fp := p *ᵖ F
  let : IsFiniteRank Fp := isFiniteRank_pullback p
  let : ∀ y, NormedAddCommGroup (Fp y) :=
    fun y ↦ ((hF.pullback p).toCore y).toNormedAddCommGroup
  let : ∀ y, InnerProductSpace ℂ (Fp y) := fun y ↦
    InnerProductSpace.ofCore ((hF.pullback p).toCore y).toCore
  let Z := TotalSpace Unit Fp
  let : LocallyCompactSpace Z := locallyCompactSpace_totalSpace (E := Fp)
  let q : C(Z, Y) := ⟨π Unit Fp, continuous_proj⟩
  let s := sumTotalPullbackHomeomorph (E := E) (F := F)
  let r : C(Z, TotalSpace Unit (E ×ᵇ F)) := ⟨s.symm, s.symm.continuous⟩
  let P (i : ZMod 2) : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
  let Q (i : ZMod 2) : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
  let Qp (i : ZMod 2) : Y → Type _ := fun y ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (Fp y)) i
  let S (i : ZMod 2) : X → Type _ := fun x ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((E ×ᵇ F) x)) i
  apply AddMonoidHom.ext
  intro ξ
  obtain ⟨a, rfl⟩ := supportBundleTriple_compactSupportClass_surjective ξ
  -- The first representative uses one arbitrary admissible original base cutoff.
  obtain ⟨U, hU, ha, L, hL, hUL, ρ, hρzero, hρone⟩ :=
    exists_time_cutoff a.datum.control a.datum.isCompact_control
  let A := fun x ↦ (a.source.Fiber x ⊗[ℂ] P 0 x) × (a.target.Fiber x ⊗[ℂ] P 1 x)
  let B := fun x ↦ (a.target.Fiber x ⊗[ℂ] P 0 x) × (a.source.Fiber x ⊗[ℂ] P 1 x)
  let b₀ : CompactSupportTriple (p *ᵖ A) (p *ᵖ B) :=
    supportedThomTriple E hE.continuous_pairing a ρ U hU ha hρzero L hL hρone
  let b := b₀.toSupportBundleTriple
  have hfirst : hE.supportedThomHom a.compactSupportClass = b.compactSupportClass :=
    supportedThomHom_class E hE.continuous_pairing a ρ U hU ha hρzero L hL hρone
  -- The second cutoff vanishes near the entire first control, including any enlargement.
  obtain ⟨V, hV, hb, M, hM, hVM, ψ, hψzero, hψone⟩ :=
    exists_time_cutoff b.datum.control b.datum.isCompact_control
  let T₀ := fun y ↦ (b.source.Fiber y ⊗[ℂ] Qp 0 y) ×
    (b.target.Fiber y ⊗[ℂ] Qp 1 y)
  let T₁ := fun y ↦ (b.target.Fiber y ⊗[ℂ] Qp 0 y) ×
    (b.source.Fiber y ⊗[ℂ] Qp 1 y)
  let t : CompactSupportTriple (q *ᵖ T₀) (q *ᵖ T₁) :=
    supportedThomTriple Fp (hF.pullback p).continuous_pairing b
      ψ V hV hb hψzero M hM hψone
  have hsecond : (hF.pullback p).supportedThomHom b.compactSupportClass =
      t.compactSupportClass :=
    supportedThomHom_class Fp (hF.pullback p).continuous_pairing b
      ψ V hV hb hψzero M hM hψone
  let C₀ := fun x ↦ (a.source.Fiber x ⊗[ℂ] S 0 x) × (a.target.Fiber x ⊗[ℂ] S 1 x)
  let C₁ := fun x ↦ (a.target.Fiber x ⊗[ℂ] S 0 x) × (a.source.Fiber x ⊗[ℂ] S 1 x)
  let pS : C(TotalSpace Unit (E ×ᵇ F), X) := ⟨π Unit _, continuous_proj⟩
  let c₀ : CompactSupportTriple (pS *ᵖ C₀) (pS *ᵖ C₁) :=
    supportedThomTriple (E ×ᵇ F) (hE.sum hF).continuous_pairing a
      ρ U hU ha hρzero L hL hρone
  -- Save the original boundary formula before introducing any chosen comparison isomorphism.
  have hc₀value (z : (c₀.controlᶜ : Set (TotalSpace Unit (E ×ᵇ F))))
      (v : C₀ z.val.proj) : c₀.boundary.linearEquiv z v =
        thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
          (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd v := by
    rfl
  let c := c₀.pullback r s.symm.isProperMap
  have hsum : (hE.sum hF).supportedThomHom a.compactSupportClass =
      c₀.compactSupportClass :=
    supportedThomHom_class (E ×ᵇ F) (hE.sum hF).continuous_pairing a
      ρ U hU ha hρzero L hL hρone
  change compactSupportKZeroHomeomorph s
      ((hE.sum hF).supportedThomHom a.compactSupportClass) =
    (hF.pullback p).supportedThomHom (hE.supportedThomHom a.compactSupportClass)
  rw [hfirst, hsecond, hsum]
  change compactSupportKZeroPullback r s.symm.isProperMap c₀.compactSupportClass = _
  rw [← c₀.compactSupportClass_pullback r s.symm.isProperMap]
  change c.compactSupportClass = t.compactSupportClass
  -- Remove only the small-model resizing and pullback parentheses, keeping the vectors.
  let I₀ := fun x ↦ (A x ⊗[ℂ] Q 0 x) × (B x ⊗[ℂ] Q 1 x)
  let I₁ := fun x ↦ (B x ⊗[ℂ] Q 0 x) × (A x ⊗[ℂ] Q 1 x)
  let n₀ := smallBundleIso (p *ᵖ A)
  let n₁ := smallBundleIso (p *ᵖ B)
  let D (y : Y) : (p *ᵖ A) y →ₗ[ℂ] (p *ᵖ B) y :=
    thomTensorSymbol (a.datum.cutoffLinearMap ρ y.proj)
      (a.datum.inverse.cutoffLinearMap ρ y.proj) y.snd
  let G (y : Y) : (p *ᵖ B) y →ₗ[ℂ] (p *ᵖ A) y :=
    thomTensorSymbolReverse (a.datum.cutoffLinearMap ρ y.proj)
      (a.datum.inverse.cutoffLinearMap ρ y.proj) y.snd
  let aScalar (y : Y) : ℝ := (ρ y.proj : ℝ) ^ 2 + ‖y.snd‖ ^ 2
  have hd (y : Y) (v : b.source.Fiber y) :
      (n₁.linearEquiv y).symm (b.datum.cutoffLinearMap ψ y v) =
        (ψ y : ℂ) • D y ((n₀.linearEquiv y).symm v) := by
    have hc := cutoff_conjugation b₀ n₀ n₁ ψ y v
    change (n₁.linearEquiv y).symm (b.datum.cutoffLinearMap ψ y v) =
      b₀.cutoffLinearMap ψ y ((n₀.linearEquiv y).symm v) at hc
    rw [hc]
    by_cases hy : y ∈ b₀.control
    · have hψ : ψ y = 0 := hψzero y (hb hy)
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hy,
        LinearMap.zero_apply, hψ, Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul]
    · simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hy]
      rfl
  have hd' (y : Y) (v : b.target.Fiber y) :
      (n₀.linearEquiv y).symm (b.datum.inverse.cutoffLinearMap ψ y v) =
        (((ψ y : ℝ) / aScalar y : ℝ) : ℂ) • (-G y) ((n₁.linearEquiv y).symm v) := by
    have heq : b.datum.inverse = b₀.inverse.congr n₁ n₀ :=
      CompactSupportTriple.congr_inverse b₀ n₀ n₁
    rw [heq]
    refine (cutoff_conjugation b₀.inverse n₁ n₀ ψ y v).trans ?_
    by_cases hy : y ∈ b₀.inverse.control
    · have hψ : ψ y = 0 := hψzero y (hb hy)
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hy,
        LinearMap.zero_apply, hψ, Set.Icc.coe_zero, zero_div,
        Complex.ofReal_zero, zero_smul]
    · simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hy]
      change (ψ y : ℂ) • (-(aScalar y : ℂ)⁻¹ • G y ((n₁.linearEquiv y).symm v)) = _
      simp only [LinearMap.neg_apply, smul_neg, neg_smul, smul_smul, div_eq_mul_inv,
        Complex.ofReal_mul, Complex.ofReal_inv]
  -- Compare original-base and native pullback symbols before introducing chosen isomorphisms.
  let J₀ := fun y : Y ↦ ((p *ᵖ A) y ⊗[ℂ] Qp 0 y) × ((p *ᵖ B) y ⊗[ℂ] Qp 1 y)
  let J₁ := fun y : Y ↦ ((p *ᵖ B) y ⊗[ℂ] Qp 0 y) × ((p *ᵖ A) y ⊗[ℂ] Qp 1 y)
  let baseSymbol (z : Z) : I₀ z.proj.proj →ₗ[ℂ] I₁ z.proj.proj :=
    thomTensorSymbol (F := A z.proj.proj) (G := B z.proj.proj) (V := F z.proj.proj)
      (show A z.proj.proj →ₗ[ℂ] B z.proj.proj from D z.proj)
      (show B z.proj.proj →ₗ[ℂ] A z.proj.proj from -G z.proj)
      (show F z.proj.proj from z.snd)
  let finalSymbol (z : Z) : J₀ (q z) →ₗ[ℂ] J₁ (q z) :=
    thomTensorSymbol (F := (p *ᵖ A) z.proj) (G := (p *ᵖ B) z.proj)
      (V := Fp z.proj) (D z.proj) (-G z.proj) z.snd
  have hbaseNative (z : Z) (w : J₀ (q z)) : baseSymbol z w = finalSymbol z w := by
    -- Pullback evaluates the same metric core and inherits the original fiber structures.
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← goal.getType
      let some (_, lhs, _) := target.eq? | throwError "expected the original symbol equality"
      goal.assign (← Lean.Meta.mkEqRefl lhs)
      Lean.Elab.Tactic.replaceMainGoal []
  -- Reassociate the three ordered factors and then apply ordered exterior multiplication.
  obtain ⟨r₀, r₁, hr⟩ := exists_thom_sum_symbol_iso hE hF a.source a.target
  obtain ⟨K₀, hK₀⟩ := exists_thomTensor_unresized_pullback_iso p q F A B
  obtain ⟨K₁, hK₁⟩ := exists_thomTensor_unresized_pullback_iso p q F B A
  let F₀ : Iso ((p.comp q) *ᵖ I₀) (r *ᵖ (pS *ᵖ C₀)) :=
    (r₀.pullback (p.comp q)).trans (pullbackCompIso (E := C₀) pS r).symm
  let F₁ : Iso ((p.comp q) *ᵖ I₁) (r *ᵖ (pS *ᵖ C₁)) :=
    (r₁.pullback (p.comp q)).trans (pullbackCompIso (E := C₁) pS r).symm
  let R₀ : Iso (q *ᵖ J₀) (r *ᵖ (pS *ᵖ C₀)) := K₀.trans F₀
  let R₁ : Iso (q *ᵖ J₁) (r *ᵖ (pS *ᵖ C₁)) := K₁.trans F₁
  have hR₀ (z : Z) (w : J₀ (q z)) :
      R₀.linearEquiv z w = r₀.linearEquiv z.proj.proj (K₀.linearEquiv z w) := by
    change ((pullbackCompIso (E := C₀) pS r).linearEquiv z).symm
      (r₀.linearEquiv z.proj.proj (K₀.linearEquiv z w)) = _
    apply ((pullbackCompIso (E := C₀) pS r).linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
  have hR₁ (z : Z) (w : J₁ (q z)) :
      R₁.linearEquiv z w = r₁.linearEquiv z.proj.proj (K₁.linearEquiv z w) := by
    change ((pullbackCompIso (E := C₁) pS r).linearEquiv z).symm
      (r₁.linearEquiv z.proj.proj (K₁.linearEquiv z w)) = _
    apply ((pullbackCompIso (E := C₁) pS r).linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
  let d₂ (y : Y) : (p *ᵖ A) y →ₗ[ℂ] (p *ᵖ B) y := (ψ y : ℂ) • D y
  let d₂' (y : Y) : (p *ᵖ B) y →ₗ[ℂ] (p *ᵖ A) y :=
    (((ψ y : ℝ) / aScalar y : ℝ) : ℂ) • (-G y)
  obtain ⟨N₀, N₁, hT⟩ := native_symbol_normalization q Fp (p *ᵖ A) (p *ᵖ B)
    b.source.Fiber b.target.Fiber (hF.pullback p) n₀.symm n₁.symm
    (b.datum.cutoffLinearMap ψ) (b.datum.inverse.cutoffLinearMap ψ)
    d₂ d₂' (fun z : Z ↦ z.snd) hd hd' t (by intro z w; rfl)
  let c' := c.congr R₀.symm R₁.symm
  let t' := t.congr N₀ N₁
  have hC (z : (c'.controlᶜ : Set Z)) (w : J₀ (q z.val)) :
      c'.boundary.linearEquiv z w = finalSymbol z.val w := by
    refine (CompactSupportTriple.congr_apply c R₀.symm R₁.symm z w).trans ?_
    refine (congrArg (R₁.linearEquiv z.val).symm
      (RelativeTriple.pullback_apply c₀.boundary r z (R₀.linearEquiv z.val w))).trans ?_
    refine (R₁.linearEquiv z.val).symm_apply_eq.mpr ?_
    let direct : (r *ᵖ (pS *ᵖ C₀)) z.val →ₗ[ℂ] (r *ᵖ (pS *ᵖ C₁)) z.val :=
      thomTensorSymbol (a.datum.cutoffLinearMap ρ (r z.val).proj)
        (a.datum.inverse.cutoffLinearMap ρ (r z.val).proj) (r z.val).snd
    have hboundary := hc₀value ⟨r z.val, z.property⟩ (R₀.linearEquiv z.val w)
    -- Compose the specified vector identities with the ordered symbol-intertwining formula.
    have h₀ := congrArg direct (hR₀ z.val w)
    have h₁ := (LinearMap.congr_fun (hr z.val.proj.proj
      (a.datum.cutoffLinearMap ρ z.val.proj.proj)
      (a.datum.inverse.cutoffLinearMap ρ z.val.proj.proj)
      z.val.proj.snd z.val.snd) (K₀.linearEquiv z.val w)).symm
    let zValue : Z := z.val
    let nativeValue : J₁ (q zValue) := finalSymbol zValue w
    have h₂ : r₁.linearEquiv z.val.proj.proj (baseSymbol z.val (K₀.linearEquiv z.val w)) =
        r₁.linearEquiv z.val.proj.proj (K₁.linearEquiv z.val (finalSymbol z.val w)) := by
      let baseAction (v : I₀ z.val.proj.proj) : I₁ z.val.proj.proj := baseSymbol z.val v
      let transport (v : I₁ z.val.proj.proj) : C₁ z.val.proj.proj :=
        r₁.linearEquiv z.val.proj.proj v
      -- hleft: baseSymbol (K₀ w) = baseSymbol w; hmiddle: baseSymbol w = finalSymbol w.
      -- The inverse of hK₁ gives finalSymbol w = K₁ (finalSymbol w); then apply r₁.
      run_tac Lean.Elab.Tactic.withMainContext do
        let goal ← Lean.Elab.Tactic.getMainGoal
        let hk0 := (← Lean.Meta.getLocalDeclFromUserName `hK₀).toExpr
        let hk1 := (← Lean.Meta.getLocalDeclFromUserName `hK₁).toExpr
        let hm := (← Lean.Meta.getLocalDeclFromUserName `hbaseNative).toExpr
        let base := (← Lean.Meta.getLocalDeclFromUserName `baseAction).toExpr
        let zz := (← Lean.Meta.getLocalDeclFromUserName `zValue).toExpr
        let ww := (← Lean.Meta.getLocalDeclFromUserName `w).toExpr
        let vv := (← Lean.Meta.getLocalDeclFromUserName `nativeValue).toExpr
        let hl ← Lean.Meta.mkCongrArg base (Lean.mkApp2 hk0 zz ww)
        let hm := Lean.mkApp2 hm zz ww
        -- hK₁ identifies its native argument with the same original-base vector.
        let hr ← Lean.Meta.mkEqSymm (Lean.mkApp2 hk1 zz vv)
        let f := (← Lean.Meta.getLocalDeclFromUserName `transport).toExpr
        let h ← Lean.Meta.mkEqTrans hl (← Lean.Meta.mkEqTrans hm hr)
        goal.assign (← Lean.Meta.mkCongrArg f h)
        Lean.Elab.Tactic.replaceMainGoal []
    -- This is hboundary.trans (h₀.trans (h₁.trans (h₂.trans hfinish))).
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let hb := (← Lean.Meta.getLocalDeclFromUserName `hboundary).toExpr
      let h0 := (← Lean.Meta.getLocalDeclFromUserName `h₀).toExpr
      let h1 := (← Lean.Meta.getLocalDeclFromUserName `h₁).toExpr
      let h2 := (← Lean.Meta.getLocalDeclFromUserName `h₂).toExpr
      let hr1 := (← Lean.Meta.getLocalDeclFromUserName `hR₁).toExpr
      let zz := (← Lean.Meta.getLocalDeclFromUserName `zValue).toExpr
      let vv := (← Lean.Meta.getLocalDeclFromUserName `nativeValue).toExpr
      let hf ← Lean.Meta.mkEqSymm (Lean.mkApp2 hr1 zz vv)
      let h ← Lean.Meta.mkEqTrans h2 hf
      let h ← Lean.Meta.mkEqTrans h1 h
      let h ← Lean.Meta.mkEqTrans h0 h
      goal.assign (← Lean.Meta.mkEqTrans hb h)
      Lean.Elab.Tactic.replaceMainGoal []
  have hcclass : c'.compactSupportClass = c.compactSupportClass :=
    c.compactSupportClass_congr R₀.symm R₁.symm
  have htclass : t'.compactSupportClass = t.compactSupportClass :=
    t.compactSupportClass_congr N₀ N₁
  rw [← hcclass, ← htclass]
  apply Eq.symm
  apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
  have hct : c'.control ⊆ t'.control := by
    intro z hz
    change (r z).proj ∈ L ∧ (r z).snd = 0 at hz
    change z.proj ∈ M ∧ z.snd = 0
    have he : z.proj.snd = 0 := congrArg Prod.fst hz.2
    have hf : z.snd = 0 := congrArg Prod.snd hz.2
    have hbz : z.proj ∈ b.datum.control := by
      change z.proj.proj ∈ L ∧ z.proj.snd = 0
      exact ⟨hz.1, he⟩
    exact ⟨hVM (hb hbz), hf⟩
  apply CompactSupportTriple.homotopic_of_bijective_affine t' c'
    t'.control t'.isCompact_control (Set.Subset.refl _) hct
  intro τ z
  have hfirstSquare := a.datum.cutoffHom_inverse_comp ρ U hU ha hρzero z.val.proj.proj
  have hsquare := thomTensorSymbol_square
    (a.datum.cutoffLinearMap ρ z.val.proj.proj)
    (a.datum.inverse.cutoffLinearMap ρ z.val.proj.proj)
    (ρ z.val.proj.proj : ℝ) z.val.proj.snd hfirstSquare.1 hfirstSquare.2
  have hnonneg : 0 ≤ aScalar z.val.proj := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpositive : 0 < (ψ z.val.proj : ℝ) * aScalar z.val.proj + ‖z.val.snd‖ ^ 2 := by
    by_cases hv : z.val.snd = 0
    · have hyM : z.val.proj ∉ M := fun hy ↦ z.property ⟨hy, hv⟩
      have hy : z.val.proj ∉ b.datum.control := fun hy ↦ hyM (hVM (hb hy))
      have hn := (supportedThom_symbol_properties E hE.continuous_pairing a
        ρ U hU ha hρzero L hL hρone).1 ⟨z.val.proj, hy⟩
      have hp : 0 < aScalar z.val.proj := lt_of_le_of_ne hnonneg (Ne.symm hn)
      simpa only [hψone z.val.proj hyM, Set.Icc.coe_one, one_mul,
        hv, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using hp
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (ψ z.val.proj).property.1 hnonneg)
        (sq_pos_of_pos (norm_pos_iff.mpr hv))
  have ht : ((t'.enlarge t'.control t'.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv
       z).toLinearMap =
      thomTensorSymbol (d₂ z.val.proj)
        (d₂' z.val.proj)
        z.val.snd := by
    apply LinearMap.ext
    intro w
    have he := t'.enlarge_apply t'.control t'.isCompact_control (Set.Subset.refl _) z w
    let zt : (t.controlᶜ : Set Z) := ⟨z.val, z.property⟩
    -- Restriction preserves this boundary value; hT computes it on the same native fiber.
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let he := (← Lean.Meta.getLocalDeclFromUserName `he).toExpr
      let ht := (← Lean.Meta.getLocalDeclFromUserName `hT).toExpr
      let zz := (← Lean.Meta.getLocalDeclFromUserName `zt).toExpr
      let ww := (← Lean.Meta.getLocalDeclFromUserName `w).toExpr
      goal.assign (← Lean.Meta.mkEqTrans he (Lean.mkApp2 ht zz ww))
      Lean.Elab.Tactic.replaceMainGoal []
  have hc : ((c'.enlarge t'.control t'.isCompact_control hct).boundary.linearEquiv
       z).toLinearMap =
      thomTensorSymbol (D z.val.proj) (-G z.val.proj) z.val.snd := by
    apply LinearMap.ext
    intro w
    have he := c'.enlarge_apply t'.control t'.isCompact_control hct z w
    let zc : (c'.controlᶜ : Set Z) := ⟨z.val, fun hx ↦ z.property (hct hx)⟩
    -- Use the complement witness supplied by the same control inclusion as enlargement.
    run_tac Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let he := (← Lean.Meta.getLocalDeclFromUserName `he).toExpr
      let hc := (← Lean.Meta.getLocalDeclFromUserName `hC).toExpr
      let zz := (← Lean.Meta.getLocalDeclFromUserName `zc).toExpr
      let ww := (← Lean.Meta.getLocalDeclFromUserName `w).toExpr
      goal.assign (← Lean.Meta.mkEqTrans he (Lean.mkApp2 hc zz ww))
      Lean.Elab.Tactic.replaceMainGoal []
  -- The abstract calculation applies to the same two native blocks and cutoff values.
  have hbij := cutoff_affine_bijective (D z.val.proj) (G z.val.proj)
    (aScalar z.val.proj) (ψ z.val.proj) τ z.val.snd
    hnonneg hsquare.1 hsquare.2 hpositive
  let e₀ : J₀ (q z.val) →ₗ[ℂ] J₁ (q z.val) :=
    ((t'.enlarge t'.control t'.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv
      z).toLinearMap
  let e₁ : J₀ (q z.val) →ₗ[ℂ] J₁ (q z.val) :=
    ((c'.enlarge t'.control t'.isCompact_control hct).boundary.linearEquiv z).toLinearMap
  let s₀ : J₀ (q z.val) →ₗ[ℂ] J₁ (q z.val) :=
    thomTensorSymbol (d₂ z.val.proj) (d₂' z.val.proj) z.val.snd
  let s₁ : J₀ (q z.val) →ₗ[ℂ] J₁ (q z.val) := finalSymbol z.val
  have endpoints := affine_bijective_of_eq
    (((1 - (τ : ℝ) : ℝ) : ℂ)) ((τ : ℝ) : ℂ) e₀ e₁ s₀ s₁
  -- This is endpoints ht hc hbij, retaining the original restricted boundary maps.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    let endpoint := (← Lean.Meta.getLocalDeclFromUserName `endpoints).toExpr
    let ht := (← Lean.Meta.getLocalDeclFromUserName `ht).toExpr
    let hc := (← Lean.Meta.getLocalDeclFromUserName `hc).toExpr
    let hbij := (← Lean.Meta.getLocalDeclFromUserName `hbij).toExpr
    goal.assign (Lean.mkApp3 endpoint ht hc hbij)
    Lean.Elab.Tactic.replaceMainGoal []

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Normalize the zero exterior fibers and the original zero-section homeomorphism.
/-- A zero-rank Thom operator is transport by the original zero-section homeomorphism. -/
theorem supportedThomHom_zeroRank (h : ContinuousHermitianMetric E)
    [∀ x, Subsingleton (E x)] :
    h.supportedThomHom = compactSupportKZeroHomeomorph (zeroSectionHomeomorph (E := E)) := by
  /- The original zero fibers have the scalar unit as their even exterior part and zero
  odd part. Their continuous tensor identifications carry the same cutoff triple to the
  original input triple pulled back by the inverse zero-section homeomorphism. -/
  let : TopologicalSpace (TotalSpace Unit (Bundle.Trivial X ℂ)) :=
    modelTopology ℂ (Bundle.Trivial X ℂ)
  let : IsFiniteRank (Bundle.Trivial X ℂ) :=
    isFiniteRank_model ℂ (Bundle.Trivial X ℂ)
  have unit_tensor_sum {P Q : X → Type _}
      [∀ x, AddCommGroup (P x)] [∀ x, Module ℂ (P x)]
      [∀ x, AddCommGroup (Q x)] [∀ x, Module ℂ (Q x)] [∀ x, Subsingleton (Q x)]
      [TopologicalSpace (TotalSpace Unit P)] [IsFiniteRank P]
      [TopologicalSpace (TotalSpace Unit Q)] [IsFiniteRank Q]
      (u : Iso (Bundle.Trivial X ℂ) P) (J K : FiniteBundle X) :
      ∃ e : Iso J.Fiber (fun x ↦ (J.Fiber x ⊗[ℂ] P x) × (K.Fiber x ⊗[ℂ] Q x)),
        ∀ x w, e.linearEquiv x w = (w ⊗ₜ[ℂ] u.linearEquiv x 1, 0) := by
    let T : X → Type _ := fun x ↦ J.Fiber x ⊗[ℂ] P x
    let Z : X → Type _ := fun x ↦ K.Fiber x ⊗[ℂ] Q x
    let l (x : X) : J.Fiber x ≃ₗ[ℂ] T x :=
      (TensorProduct.rid ℂ (J.Fiber x)).symm.trans
        (TensorProduct.congr (LinearEquiv.refl ℂ (J.Fiber x)) (u.linearEquiv x))
    have hl (x : X) (w : J.Fiber x) : l x w = w ⊗ₜ[ℂ] u.linearEquiv x 1 := by
      change (TensorProduct.congr (LinearEquiv.refl ℂ (J.Fiber x)) (u.linearEquiv x))
        (w ⊗ₜ[ℂ] 1) = _
      rfl
    have hunit : Continuous (fun x : X ↦ (⟨x, u.linearEquiv x 1⟩ : TotalSpace Unit P)) := by
      have hscalar : Continuous (fun x : X ↦ (⟨x, (1 : ℂ)⟩ :
          TotalSpace Unit (Bundle.Trivial X ℂ))) := by
        apply (continuous_modelTotal_iff ℂ (Bundle.Trivial X ℂ) _).mpr
        exact (Bundle.Trivial.homeomorphProd X ℂ).symm.continuous.comp
          (continuous_id.prodMk continuous_const)
      exact u.continuous_total.comp hscalar
    have htensor : Continuous (fun z : TotalSpace Unit J.Fiber ↦
        (⟨z.proj, z.snd ⊗ₜ[ℂ] u.linearEquiv z.proj 1⟩ : TotalSpace Unit T)) := by
      let D := TotalSpace Unit (fun x ↦ (Fin 1 → J.Fiber x) × (Fin 1 → P x))
      let : TopologicalSpace D := TopologicalSpace.induced
        (fun z : D ↦ (z.proj,
          (fun i : Fin 1 ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit J.Fiber)),
          (fun i : Fin 1 ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit P)))) inferInstance
      let lift (z : TotalSpace Unit J.Fiber) : D :=
        ⟨z.proj, (fun _ ↦ z.snd, fun _ ↦ u.linearEquiv z.proj 1)⟩
      have hL : Continuous lift := by
        apply continuous_induced_rng.mpr
        exact continuous_proj.prodMk ((continuous_pi fun _ ↦ continuous_id).prodMk
          (continuous_pi fun _ ↦ hunit.comp continuous_proj))
      have hgen : Continuous (fun z : D ↦
          (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ : TotalSpace Unit T)) :=
        continuous_iSup_rng (i := 1) continuous_coinduced_rng
      simpa [lift, Function.comp_def] using hgen.comp hL
    let F : Hom J.Fiber (fun x ↦ T x × Z x) :=
      { linearMap x := (l x).toLinearMap.prod 0
        continuous_total := by
          have h := htensor.prodMk ((continuous_zero_section Z).comp continuous_proj)
          apply continuous_induced_rng.mpr
          exact h.congr (fun z ↦ by simp only [hl, LinearMap.prod_apply,
            LinearMap.zero_apply, Function.prod_apply, Function.comp_apply, LinearEquiv.coe_coe]) }
    have hbij (x : X) : Function.Bijective (F.linearMap x) := by
      constructor
      · intro v w h
        exact (l x).injective (congrArg Prod.fst h)
      · intro w
        refine ⟨(l x).symm w.1, ?_⟩
        exact Prod.ext ((l x).apply_symm_apply w.1) (Subsingleton.elim _ _)
    refine ⟨F.toIso hbij, ?_⟩
    intro x w
    change (l x w, 0) = _
    rw [hl]
  have support_square
      {X : Type _} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      {E F G H : X → Type _}
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
      [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
      [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
      [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]
      (a : CompactSupportTriple E F) (b : CompactSupportTriple G H)
      (u : Iso E G) (v : Iso F H) (K : Set X) (hK : IsCompact K)
      (ha : a.control ⊆ K) (hb : b.control ⊆ K)
      (hs : ∀ (x : (Kᶜ : Set X)) (w : E x.val),
        v.linearEquiv x.val ((a.enlarge K hK ha).boundary.linearEquiv x w) =
          (b.enlarge K hK hb).boundary.linearEquiv x (u.linearEquiv x.val w)) :
      a.compactSupportClass = b.compactSupportClass := by
    rw [← a.compactSupportClass_congr u v]
    apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
    have heq : ((a.congr u v).enlarge K hK ha).boundary =
        (b.enlarge K hK hb).boundary := by
      apply Iso.ext
      intro x
      apply LinearEquiv.ext
      intro w
      have h := hs x ((u.linearEquiv x.val).symm w)
      rw [LinearEquiv.apply_symm_apply] at h
      have hl := (a.congr u v).enlarge_apply K hK ha x w
      have hc := a.congr_apply u v ⟨x.val, fun hx ↦ x.property (ha hx)⟩ w
      have hv := a.enlarge_apply K hK ha x ((u.linearEquiv x.val).symm w)
      exact hl.trans (hc.trans ((congrArg (v.linearEquiv x.val) hv.symm).trans h))
    refine ⟨K, hK, ha, hb, ?_⟩
    rw [heq]
    exact IsoHomotopy.nonempty_refl _
  have hzeroParity :
      (∃ u : Iso (Bundle.Trivial X ℂ)
          (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0),
        ∀ x z, (u.linearEquiv x z).val = algebraMap ℂ (ExteriorAlgebra ℂ (E x)) z) ∧
      ∀ x, Subsingleton (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1) := by
    classical
    -- In a zero fiber every exterior generator vanishes, leaving exactly the scalar unit.
    have hsurj (x : X) : Function.Surjective (algebraMap ℂ (ExteriorAlgebra ℂ (E x))) := by
      intro a
      induction a using ExteriorAlgebra.induction with
      | algebraMap z => exact ⟨z, rfl⟩
      | ι v =>
        refine ⟨0, ?_⟩
        have hv : v = 0 := Subsingleton.elim _ _
        rw [hv, map_zero, map_zero]
      | mul a b ha hb =>
        obtain ⟨z, rfl⟩ := ha
        obtain ⟨w, rfl⟩ := hb
        exact ⟨z * w, map_mul _ _ _⟩
      | add a b ha hb =>
        obtain ⟨z, rfl⟩ := ha
        obtain ⟨w, rfl⟩ := hb
        exact ⟨z + w, map_add _ _ _⟩
    have hscalar (x : X) (z : ℂ) : algebraMap ℂ (ExteriorAlgebra ℂ (E x)) z ∈
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0 :=
      SetLike.algebraMap_mem_graded (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x))) z
    -- Complementarity of the original grading forces its odd summand to be zero.
    have hodd (x : X) :
        Subsingleton (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1) := by
      apply Submodule.subsingleton_iff_eq_bot.mpr
      have htop : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0 = ⊤ := by
        apply top_unique
        intro a _
        obtain ⟨z, rfl⟩ := hsurj x a
        exact hscalar x z
      have hc := (CliffordAlgebra.evenOdd_isCompl (0 : QuadraticForm ℂ (E x))).inf_eq_bot
      simpa only [htop, top_inf_eq] using hc
    let evenMap (x : X) : ℂ →ₗ[ℂ]
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0 :=
      (Algebra.linearMap ℂ (ExteriorAlgebra ℂ (E x))).codRestrict _ (hscalar x)
    have hbij (x : X) : Function.Bijective (evenMap x) := by
      constructor
      · intro z w h
        exact (ExteriorAlgebra.algebraMap_leftInverse (E x)).injective
          (congrArg Subtype.val h)
      · intro a
        obtain ⟨z, hz⟩ := hsurj x a.val
        exact ⟨z, Subtype.ext hz⟩
    -- The degree-zero monomial generator preserves the actual scalar total-space topology.
    let T := TotalSpace Unit (Bundle.Trivial X ℂ)
    let A := TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x))
    let D := TotalSpace Unit (fun x ↦ (Fin 1 → ℂ) × (∀ _ : Fin 1, Fin 0 → E x))
    let dtop : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj, z.snd.1,
        (fun (i : Fin 1) (j : Fin 0) ↦ (⟨z.proj, z.snd.2 i j⟩ : TotalSpace Unit E))))
      inferInstance
    let lift (z : T) : D := ⟨z.proj, (fun _ ↦ z.snd, fun _ j ↦ Fin.elim0 j)⟩
    have hcoords : Continuous (fun z : T ↦ (z.proj, z.snd)) :=
      ((unitTotalHomeomorph ℂ (Bundle.Trivial X ℂ)).trans
        (Bundle.Trivial.homeomorphProd X ℂ)).continuous
    have hlift : @Continuous T D _ dtop lift := by
      apply continuous_induced_rng.mpr
      apply hcoords.fst.prodMk
      apply Continuous.prodMk
      · exact continuous_pi (fun _ ↦ hcoords.snd)
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        exact Fin.elim0 j
    have hgen : @Continuous D A dtop exteriorTopology
        (fun z : D ↦ ⟨z.proj, ∑ i : Fin 1,
          z.snd.1 i • ExteriorAlgebra.ιMulti ℂ 0 (z.snd.2 i)⟩) :=
      continuous_iSup_rng (i := 1)
        (continuous_iSup_rng (i := fun _ : Fin 1 ↦ 0) continuous_coinduced_rng)
    have hunit : Continuous (fun z : T ↦
        (⟨z.proj, algebraMap ℂ (ExteriorAlgebra ℂ (E z.proj)) z.snd⟩ : A)) := by
      apply (hgen.comp hlift).congr
      intro z
      apply TotalSpace.ext
      · rfl
      apply heq_of_eq
      change (∑ i : Fin 1, z.snd • ExteriorAlgebra.ιMulti ℂ 0 _) = _
      simp [ExteriorAlgebra.ιMulti_zero_apply, Algebra.smul_def]
    -- Restrict the scalar map to even parity; finite-rank inverse continuity supplies the Iso.
    let f : Hom (Bundle.Trivial X ℂ)
        (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) :=
      { linearMap := evenMap
        continuous_total := by
          apply continuous_induced_rng.mpr
          exact hunit }
    exact ⟨⟨f.toIso hbij, fun _ _ ↦ rfl⟩, hodd⟩
  -- Retain the positive unit and the original odd-zero comparison on every fiber.
  obtain ⟨u, _hu⟩ := hzeroParity.1
  let : ∀ x, Subsingleton (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1) :=
    hzeroParity.2
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (h.toCore x).toCore
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  have hp : IsProperMap p := (zeroSectionHomeomorph (E := E)).symm.isProperMap
  -- Compare each original support representative along the same proper zero-section inverse.
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := supportBundleTriple_compactSupportClass_surjective x
  obtain ⟨U, hU, hcontrol, L, hL, hUL, ρ, hzero, hone⟩ :=
    exists_time_cutoff a.datum.control a.datum.isCompact_control
  change ComplexBundle.supportedThomHom E h.continuous_pairing a.compactSupportClass =
    compactSupportKZeroPullback p hp a.compactSupportClass
  rw [supportedThomHom_class E h.continuous_pairing a ρ U hU hcontrol hzero L hL hone]
  have ha : a.datum.compactSupportClass = a.compactSupportClass :=
    compactSupportTriple_compactSupportClass_ofBoundary a.source a.target a.datum
  rw [← ha, ← a.datum.compactSupportClass_pullback p hp]
  let S : X → Type _ := fun x ↦
    (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
      (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
  let T : X → Type _ := fun x ↦
    (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
      (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
  let : IsFiniteRank (p *ᵖ S) := isFiniteRank_pullback (E := S) p
  let : IsFiniteRank (p *ᵖ T) := isFiniteRank_pullback (E := T) p
  let A := supportedThomTriple E h.continuous_pairing a ρ U hU hcontrol hzero L hL hone
  let B := a.datum.pullback p hp
  change A.compactSupportClass = B.compactSupportClass
  -- Tensoring the unit line gives the original coefficient bundles in both parities.
  obtain ⟨es, hes⟩ := unit_tensor_sum (Q := fun x ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1) u a.source a.target
  obtain ⟨et, het⟩ := unit_tensor_sum (Q := fun x ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1) u a.target a.source
  let K : Set (TotalSpace Unit E) := A.control
  have hK : IsCompact K := A.isCompact_control
  have hB : B.control ⊆ K := by
    intro z hz
    exact ⟨hUL (hcontrol hz), Subsingleton.elim _ _⟩
  symm
  apply support_square B A (es.pullback p) (et.pullback p) K hK hB (Set.Subset.refl _)
  intro z w
  have hxL : z.val.proj ∉ L := fun hx ↦ z.property ⟨hx, Subsingleton.elim _ _⟩
  have hxa : z.val.proj ∉ a.datum.control := fun hx ↦ hxL (hUL (hcontrol hx))
  -- Off the common compact control rho is one, so the forward boundary is unchanged.
  have hsymbol : et.linearEquiv z.val.proj
      (a.datum.boundary.linearEquiv ⟨z.val.proj, hxa⟩ w) =
      A.boundary.linearEquiv ⟨z.val, z.property⟩ (es.linearEquiv z.val.proj w) := by
    change et.linearEquiv z.val.proj (a.datum.boundary.linearEquiv ⟨z.val.proj, hxa⟩ w) =
      thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
        (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd
          (es.linearEquiv z.val.proj w)
    rw [hes, het]
    apply Prod.ext
    · simp only [thomTensorSymbol, LinearMap.prod_apply, Function.prod, LinearMap.coprod_apply,
        TensorProduct.map_tmul, LinearMap.id_apply, map_zero,
        add_zero, CompactSupportTriple.cutoffLinearMap, dite_eq_right hxa,
        hone z.val.proj hxL, Set.Icc.coe_one,
        Complex.ofReal_one, one_smul]
      rfl
    · exact Subsingleton.elim _ _
  have hl := B.enlarge_apply K hK hB z w
  have hb := RelativeTriple.pullback_apply a.datum.boundary p
    ⟨z.val, hxa⟩ w
  have hr := A.enlarge_apply K hK (Set.Subset.refl _) z (es.linearEquiv z.val.proj w)
  exact (congrArg (et.linearEquiv z.val.proj) (hl.trans hb)).trans
    (hsymbol.trans hr.symm)


end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
