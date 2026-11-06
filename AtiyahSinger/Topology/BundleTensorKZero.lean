/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKZero
public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.KZeroProduct

/-!
# Tensor compatibility of geometric bundle classes

Public module ID: M1597.

D07/K02. This identifies the actual tensor bundle class with the Kronecker
product in the existing finite-projective model. Hatcher, Vector Bundles and
K-Theory, §1.1, pp.13–15 and §2.1, p.40, supplies the geometric tensor product
and its multiplication rule; the idempotent comparison is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

attribute [local instance] tensorTopology isFiniteRank_tensor

set_option maxHeartbeats 800000 in

set_option backward.isDefEq.respectTransparency.types false in
/-- Tensoring actual continuous bundles induces the specified multiplication on K⁰. -/
theorem kZeroClass_tensor :
    kZeroClass (fun x ↦ E x ⊗[ℂ] F x) =
      kZeroMul C(X, ℂ) (kZeroClass E) (kZeroClass F) := by
  /- Stage 1: choose the existing image-bundle presentations p and q of E
  and F. Tensor their actual bundle isomorphisms, keeping the total topologies.
  Stage 2: the prescribed finite-coordinate inclusion maps the tensor of the
  two image bundles into the image of p.tensor q. Test its continuity on the
  original finite-sum generators. Split inclusions prove injectivity, and the
  algebraic image comparison gives equal finite dimensions, hence bijectivity.
  The inverse-map theorem then gives continuity of this same map's inverse.
  Stage 3: presentation independence computes the class using this Kronecker
  idempotent. Apply kZeroMul_class to identify the two sides.
  No globally constant rank or connectedness assumption is required. -/
  classical
  let p := idempotentPresentation (E := E)
  let q := idempotentPresentation (E := F)
  let : TopologicalSpace (TotalSpace Unit (fun x ↦ p.fiber x)) := p.fiberTotalSpaceTopology
  let : TopologicalSpace (TotalSpace Unit (fun x ↦ q.fiber x)) := q.fiberTotalSpaceTopology
  let : TopologicalSpace (TotalSpace Unit (fun x ↦ (p.tensor q).fiber x)) :=
    (p.tensor q).fiberTotalSpaceTopology
  let := p.isFiniteRank_fiber
  let := q.isFiniteRank_fiber
  let := (p.tensor q).isFiniteRank_fiber
  let bp := Pi.basisFun ℂ (Fin p.size)
  let bq := Pi.basisFun ℂ (Fin q.size)
  let b := (bp.tensorProduct bq).reindex finProdFinEquiv
  let e := b.equivFun
  let P (x : X) := p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
  let Q (x : X) := q.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
  let T (x : X) := (p.tensor q).map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
  -- Scalar evaluation retains the actual Kronecker matrix and its prescribed Fin indexing.
  have htensor (x : X) : T x = (P x).tensor (Q x) := by
    rfl
  have hfix (a : IdempotentMatrix C(X, ℂ)) (x : X) (v : a.fiber x) :
      (a.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix.mulVecLin v.val = v.val := by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul]
    rw [(a.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self]
  have hcoord (x : X) (w : (Fin p.size → ℂ) ⊗[ℂ] (Fin q.size → ℂ)) :
      (T x).matrix.mulVecLin (e w) =
        e (TensorProduct.map (P x).matrix.mulVecLin (Q x).matrix.mulVecLin w) := by
    have hmat : LinearMap.toMatrix b b
        (TensorProduct.map (P x).matrix.mulVecLin (Q x).matrix.mulVecLin) =
        ((P x).tensor (Q x)).matrix := by
      ext i j
      simp only [b, LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
        Module.Basis.reindex_apply, Module.Basis.tensorProduct_apply', TensorProduct.map_tmul]
      change ((bp.tensorProduct bq).repr
        ((P x).matrix.mulVecLin (bp (finProdFinEquiv.symm j).1) ⊗ₜ[ℂ]
          (Q x).matrix.mulVecLin (bq (finProdFinEquiv.symm j).2)))
          ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm i).2) = _
      rw [Module.Basis.tensorProduct_repr_tmul_apply]
      simp only [bp, bq, Pi.basisFun_repr, Pi.basisFun_apply, Matrix.mulVecLin_apply,
        smul_eq_mul, IdempotentMatrix.tensor,
        IdempotentMatrix.tensorMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.kronecker, Matrix.kroneckerMap_apply]
      have hP (i j : Fin p.size) : (P x).matrix.mulVec (Pi.single j 1) i =
          (P x).matrix i j := congrFun (Matrix.mulVec_single_one (P x).matrix j) i
      have hQ (i j : Fin q.size) : (Q x).matrix.mulVec (Pi.single j 1) i =
          (Q x).matrix i j := congrFun (Matrix.mulVec_single_one (Q x).matrix j) i
      exact (congrArg₂ (fun a b : ℂ ↦ a * b)
        (hQ (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2)
        (hP (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1)).trans (mul_comm _ _)
    have h := LinearMap.toMatrix_mulVec_repr b b
      (TensorProduct.map (P x).matrix.mulVecLin (Q x).matrix.mulVecLin) w
    rw [hmat] at h
    exact h
  let I (x : X) : (p.fiber x ⊗[ℂ] q.fiber x) →ₗ[ℂ] (Fin (p.size * q.size) → ℂ) :=
    e.toLinearMap.comp (TensorProduct.map (p.fiber x).subtype (q.fiber x).subtype)
  have hIpure (x : X) (v : p.fiber x) (w : q.fiber x) (k : Fin (p.size * q.size)) :
      I x (v ⊗ₜ[ℂ] w) k =
        v.val (finProdFinEquiv.symm k).1 * w.val (finProdFinEquiv.symm k).2 := by
    change (b.repr (v.val ⊗ₜ[ℂ] w.val)) k = _
    rw [Module.Basis.repr_reindex_apply]
    calc
      _ = w.val (finProdFinEquiv.symm k).2 * v.val (finProdFinEquiv.symm k).1 :=
        bp.tensorProduct_repr_tmul_apply bq _ _ _ _
      _ = _ := mul_comm _ _
  have hmem (x : X) (w : p.fiber x ⊗[ℂ] q.fiber x) : I x w ∈ (p.tensor q).fiber x := by
    refine ⟨I x w, ?_⟩
    change (T x).matrix.mulVecLin (e
      (TensorProduct.map (p.fiber x).subtype (q.fiber x).subtype w)) = I x w
    rw [hcoord]
    have hp : (P x).matrix.mulVecLin.comp (p.fiber x).subtype = (p.fiber x).subtype := by
      apply LinearMap.ext
      intro v
      exact hfix p x v
    have hq : (Q x).matrix.mulVecLin.comp (q.fiber x).subtype = (q.fiber x).subtype := by
      apply LinearMap.ext
      intro v
      exact hfix q x v
    have hm : (TensorProduct.map (P x).matrix.mulVecLin (Q x).matrix.mulVecLin).comp
        (TensorProduct.map (p.fiber x).subtype (q.fiber x).subtype) =
        TensorProduct.map (p.fiber x).subtype (q.fiber x).subtype := by
      rw [← TensorProduct.map_comp, hp, hq]
      rfl
    exact congrArg e (DFunLike.congr_fun hm w)
  let J (x : X) : (p.fiber x ⊗[ℂ] q.fiber x) →ₗ[ℂ] (p.tensor q).fiber x :=
    (I x).codRestrict _ (hmem x)
  -- The continuous map is the prescribed coordinate tensor inclusion, not a chosen fiber iso.
  have hcontinuous : Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x ⊗[ℂ] q.fiber x) ↦
      (⟨z.proj, J z.proj z.snd⟩ : TotalSpace Unit (fun x ↦ (p.tensor q).fiber x))) := by
    apply continuous_induced_rng.mpr
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit (fun x ↦ (Fin m → p.fiber x) × (Fin m → q.fiber x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit (fun x ↦ p.fiber x))),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit (fun x ↦ q.fiber x))))) inferInstance
    have hd : Continuous (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit (fun x ↦ p.fiber x))),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit (fun x ↦ q.fiber x))))) :=
      continuous_induced_dom
    have hp : Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦
        (z.proj, z.snd.val)) := continuous_induced_dom
    have hq : Continuous (fun z : TotalSpace Unit (fun x ↦ q.fiber x) ↦
        (z.proj, z.snd.val)) := continuous_induced_dom
    have hs : Continuous (fun z : D ↦ (z.proj, fun k : Fin (p.size * q.size) ↦
        ∑ i : Fin m, (z.snd.1 i).val (finProdFinEquiv.symm k).1 *
          (z.snd.2 i).val (finProdFinEquiv.symm k).2)) := by
      refine hd.fst.prodMk (continuous_pi fun k ↦ ?_)
      apply continuous_finsetSum
      intro i _
      exact ((continuous_apply _).comp (hp.comp
        ((continuous_apply i).comp hd.snd.fst)).snd).mul
          ((continuous_apply _).comp (hq.comp
            ((continuous_apply i).comp hd.snd.snd)).snd)
    refine hs.congr ?_
    intro z
    apply Prod.ext
    · rfl
    · change (fun k : Fin (p.size * q.size) ↦ ∑ i : Fin m,
        (z.snd.1 i).val (finProdFinEquiv.symm k).1 *
          (z.snd.2 i).val (finProdFinEquiv.symm k).2) =
            I z.proj (∑ i : Fin m, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)
      funext k
      rw [map_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl (fun i _ ↦ (hIpure z.proj _ _ k).symm)
  let a : Hom (fun x ↦ p.fiber x ⊗[ℂ] q.fiber x) (fun x ↦ (p.tensor q).fiber x) :=
    ⟨J, hcontinuous⟩
  have hbijective (x : X) : Function.Bijective (a.linearMap x) := by
    -- Split inclusions give injectivity of this very map, without tensor exactness assumptions.
    let retract : (Fin (p.size * q.size) → ℂ) →ₗ[ℂ] (p.fiber x ⊗[ℂ] q.fiber x) :=
      (TensorProduct.map (P x).matrix.mulVecLin.rangeRestrict
        (Q x).matrix.mulVecLin.rangeRestrict).comp e.symm.toLinearMap
    have hleft (w : p.fiber x ⊗[ℂ] q.fiber x) : retract (I x w) = w := by
      change TensorProduct.map (P x).matrix.mulVecLin.rangeRestrict
        (Q x).matrix.mulVecLin.rangeRestrict (e.symm (e
          (TensorProduct.map (p.fiber x).subtype (q.fiber x).subtype w))) = w
      rw [e.symm_apply_apply]
      have hpfix : (P x).matrix.mulVecLin.rangeRestrict.comp (p.fiber x).subtype =
          LinearMap.id := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact hfix p x v
      have hqfix : (Q x).matrix.mulVecLin.rangeRestrict.comp (q.fiber x).subtype =
          LinearMap.id := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        exact hfix q x v
      have hm : (TensorProduct.map (P x).matrix.mulVecLin.rangeRestrict
          (Q x).matrix.mulVecLin.rangeRestrict).comp
          (TensorProduct.map (p.fiber x).subtype (q.fiber x).subtype) = LinearMap.id := by
        rw [← TensorProduct.map_comp, hpfix, hqfix]
        exact TensorProduct.map_id
      exact DFunLike.congr_fun hm w
    have hinj : Function.Injective (a.linearMap x) := by
      intro u v huv
      have hI : I x u = I x v := congrArg Subtype.val huv
      exact (hleft u).symm.trans ((congrArg retract hI).trans (hleft v))
    -- The existing algebraic image theorem is used only for dimension of the actual target.
    have hrank : Nonempty ((p.tensor q).fiber x ≃ₗ[ℂ] (p.fiber x ⊗[ℂ] q.fiber x)) := by
      change Nonempty ((T x).image ≃ₗ[ℂ] ((P x).image ⊗[ℂ] (Q x).image))
      rw [htensor]
      exact (P x).nonempty_tensor_image_linearEquiv (Q x)
    obtain ⟨d⟩ := hrank
    exact (LinearEquiv.ofInjectiveOfFinrankEq (K := ℂ)
      (V := p.fiber x ⊗[ℂ] q.fiber x) (V' := (p.tensor q).fiber x)
      (a.linearMap x) hinj (by exact d.finrank_eq.symm)).bijective
  -- Both continuity directions now belong to the same specified tensor-to-image map.
  let imageIso := a.toIso hbijective
  let tensorPresentation : Iso (fun x ↦ E x ⊗[ℂ] F x)
      (fun x ↦ (p.tensor q).fiber x) :=
    ((presentationIso (E := E)).tensor (presentationIso (E := F))).trans imageIso
  exact (kZeroClass_eq_of_presentation (p.tensor q) tensorPresentation).trans
    (kZeroMul_class p q).symm

end AtiyahSinger.ComplexBundle
