/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.ExteriorBundle
public import Mathlib.LinearAlgebra.CliffordAlgebra.Prod
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Exterior parity bundles of a direct sum

Public module ID: M1840.

The ordered exterior multiplication identifies the two parity tensor sums
with the original parity bundles of a direct sum, in their specified bundle
topologies. Local exterior charts establish continuity without a fixed-rank
hypothesis. This is the standard exterior direct-sum formula used in SG C.8
and KA IV.1.4--1.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exterior isFiniteRank_exteriorParity

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exterior functoriality is continuous in the original finite-wedge topology. -/
def Hom.exterior (e : Hom E F) :
    Hom (fun x ↦ ExteriorAlgebra ℂ (E x)) (fun x ↦ ExteriorAlgebra ℂ (F x)) where
  linearMap x := (ExteriorAlgebra.map (e.linearMap x)).toLinearMap
  continuous_total := by
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_iSup_dom.mpr
    intro k
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit (fun x : X ↦
      (Fin m → ℂ) × (∀ j : Fin m, Fin (k j) → E x))
    let D' := TotalSpace Unit (fun x : X ↦
      (Fin m → ℂ) × (∀ j : Fin m, Fin (k j) → F x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit E))) inferInstance
    let : TopologicalSpace D' := TopologicalSpace.induced
      (fun z : D' ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit F))) inferInstance
    have hd : Continuous (fun z : D ↦ (z.proj, z.snd.1,
        fun j l ↦ (⟨z.proj, z.snd.2 j l⟩ : TotalSpace Unit E))) :=
      continuous_induced_dom
    let lift : D → D' := fun z ↦
      ⟨z.proj, z.snd.1, fun j l ↦ e.linearMap z.proj (z.snd.2 j l)⟩
    have hlift : Continuous lift := by
      apply continuous_induced_rng.mpr
      exact hd.fst.prodMk (hd.snd.fst.prodMk
        (continuous_pi fun j ↦ continuous_pi fun l ↦
          e.continuous_total.comp
            ((continuous_apply l).comp ((continuous_apply j).comp hd.snd.snd))))
    have hwedge : Continuous (fun z : D' ↦ (⟨z.proj,
        ∑ j : Fin m, z.snd.1 j • ExteriorAlgebra.ιMulti ℂ (k j) (z.snd.2 j)⟩ :
          TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (F x)))) :=
      continuous_iSup_rng (i := m) (continuous_iSup_rng (i := k) continuous_coinduced_rng)
    convert hwedge.comp hlift using 1
    funext z
    simp [Function.comp_def, lift, map_sum, map_smul, ExteriorAlgebra.map_apply_ιMulti]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exterior multiplication is continuous for sections over a common varying base. -/
private theorem continuous_exterior_mul {Z : Type*} [TopologicalSpace Z]
    (f : C(Z, X)) (a b : ∀ z : Z, ExteriorAlgebra ℂ (E (f z)))
    (ha : Continuous (fun z ↦ (⟨f z, a z⟩ : TotalSpace Unit
      (fun x ↦ ExteriorAlgebra ℂ (E x)))))
    (hb : Continuous (fun z ↦ (⟨f z, b z⟩ : TotalSpace Unit
      (fun x ↦ ExteriorAlgebra ℂ (E x))))) :
    Continuous (fun z ↦ (⟨f z, a z * b z⟩ : TotalSpace Unit
      (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
  classical
  -- In one original linear chart the exterior product is a fixed bilinear map.
  rw [continuous_iff_continuousAt]
  intro z₀
  obtain ⟨r, e, he, hlinear⟩ :=
    IsFiniteRank.exists_linear_trivialization (E := E) (f z₀)
  obtain ⟨t, hbase, _, hformula⟩ := exists_exterior_trivialization e hlinear
  let N := Fintype.card (Finset (Fin r))
  let C := Fin N → ℂ
  let c : ExteriorAlgebra ℂ (Fin r → ℂ) ≃ₗ[ℂ] C :=
    ((Pi.basisFun ℂ (Fin r)).ExteriorAlgebra.reindex
      (Fintype.equivFin (Finset (Fin r)))).equivFun
  let m : C →ₗ[ℂ] C →ₗ[ℂ] C :=
    { toFun u := c.toLinearMap.comp
        ((LinearMap.mulLeft ℂ (c.symm u)).comp c.symm.toLinearMap)
      map_add' := by
        intro u v
        ext w
        simp [map_add, add_mul]
      map_smul' := by
        intro q u
        ext w
        simp [map_smul, Algebra.smul_mul_assoc] }
  let mc : C →ₗ[ℂ] C →L[ℂ] C :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp m
  have hm : Continuous (fun z : C × C ↦ m z.1 z.2) :=
    (mc.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd
  let A (z : Z) : C := (t (⟨f z, a z⟩ : TotalSpace Unit
    (fun x ↦ ExteriorAlgebra ℂ (E x)))).2
  let B (z : Z) : C := (t (⟨f z, b z⟩ : TotalSpace Unit
    (fun x ↦ ExteriorAlgebra ℂ (E x)))).2
  have ht : f z₀ ∈ t.baseSet := hbase.symm ▸ he
  have hA : ContinuousAt A z₀ :=
    ((t.continuousAt (t.mem_source.mpr ht)).comp ha.continuousAt).snd
  have hB : ContinuousAt B z₀ :=
    ((t.continuousAt (t.mem_source.mpr ht)).comp hb.continuousAt).snd
  -- Test the output in the same exterior chart, whose coordinates are bilinear.
  apply t.continuousAt_of_comp_left
    (f := fun z ↦ (⟨f z, a z * b z⟩ : TotalSpace Unit
      (fun x ↦ ExteriorAlgebra ℂ (E x)))) f.continuous.continuousAt ht
  apply (f.continuous.continuousAt.prodMk
    (hm.continuousAt.comp (hA.prodMk hB))).congr_of_eventuallyEq
  filter_upwards [f.continuous.continuousAt.preimage_mem_nhds
    (e.open_baseSet.mem_nhds he)] with z hz
  have htz : f z ∈ t.baseSet := hbase.symm ▸ hz
  have hp : t (⟨f z, a z * b z⟩ : TotalSpace Unit
      (fun x ↦ ExteriorAlgebra ℂ (E x))) = (f z, m (A z) (B z)) := by
    apply Prod.ext
    · exact t.proj_toFun _ (t.mem_source.mpr htz)
    · dsimp only [A, B]
      rw [hformula _ hz, hformula _ hz, hformula _ hz]
      change c (ExteriorAlgebra.map (IsLinearMap.mk' _ (hlinear (f z) hz))
          (a z * b z)) = c (c.symm (c _) * c.symm (c _))
      rw [map_mul, c.symm_apply_apply, c.symm_apply_apply]
  exact hp

/-- The ordered exterior multiplication map, before its bundle continuity certificate. -/
def exteriorSumTensorMap {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] :
    ExteriorAlgebra ℂ V ⊗[ℂ] ExteriorAlgebra ℂ W →ₗ[ℂ] ExteriorAlgebra ℂ (V × W) :=
  TensorProduct.lift ((LinearMap.mul ℂ (ExteriorAlgebra ℂ (V × W))).compl₁₂
    (ExteriorAlgebra.map (LinearMap.inl ℂ V W)).toLinearMap
    (ExteriorAlgebra.map (LinearMap.inr ℂ V W)).toLinearMap)

/-- The Clifford direct-sum equivalence gives exactly the prescribed ordered wedge map. -/
private theorem exteriorSumTensorMap_bijective {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    Function.Bijective (exteriorSumTensorMap (V := V) (W := W)) := by
  classical
  let q : ((0 : QuadraticForm ℂ V).prod (0 : QuadraticForm ℂ W)).IsometryEquiv
      (0 : QuadraticForm ℂ (V × W)) :=
    { LinearEquiv.refl ℂ (V × W) with map_app' := fun x ↦ by simp [QuadraticMap.prod_apply] }
  let B : ExteriorAlgebra ℂ V ⊗[ℂ] ExteriorAlgebra ℂ W ≃ₗ[ℂ] ExteriorAlgebra ℂ (V × W) :=
    (GradedTensorProduct.of ℂ (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V))
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W))).trans
      ((CliffordAlgebra.prodEquiv (0 : QuadraticForm ℂ V)
        (0 : QuadraticForm ℂ W)).symm.toLinearEquiv.trans
          (CliffordAlgebra.equivOfIsometry q).toLinearEquiv)
  have hF : (CliffordAlgebra.map q.toIsometry).comp
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl (0 : QuadraticForm ℂ V)
        (0 : QuadraticForm ℂ W))) = ExteriorAlgebra.map (LinearMap.inl ℂ V W) := by
    apply ExteriorAlgebra.hom_ext
    ext v
    simp [q]
    rfl
  have hG : (CliffordAlgebra.map q.toIsometry).comp
      (CliffordAlgebra.map (QuadraticMap.Isometry.inr (0 : QuadraticForm ℂ V)
        (0 : QuadraticForm ℂ W))) = ExteriorAlgebra.map (LinearMap.inr ℂ V W) := by
    apply ExteriorAlgebra.hom_ext
    ext w
    simp [q]
    rfl
  have hB : B.toLinearMap = exteriorSumTensorMap := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    change CliffordAlgebra.map q.toIsometry
      (CliffordAlgebra.toProd (0 : QuadraticForm ℂ V) (0 : QuadraticForm ℂ W)
        (a ᵍ⊗ₜ b)) = _
    simp only [CliffordAlgebra.toProd, GradedTensorProduct.lift_tmul, map_mul]
    exact congrArg₂ (· * ·) (AlgHom.congr_fun hF a) (AlgHom.congr_fun hG b)
  rw [← hB]
  exact B.bijective

/-- The ordered exterior equivalence restricts to its even and odd tensor summands. -/
private theorem exists_exteriorSumParity_equiv {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] :
    let PV := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
    let PW := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)
    let PS := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (V × W))
    ∃ L₀ : ((PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1)) ≃ₗ[ℂ] PS 0,
      ∃ L₁ : ((PV 1 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1)) ≃ₗ[ℂ] PS 1,
        (∀ z, (L₀ z).val = exteriorSumTensorMap
          (TensorProduct.map (PV 0).subtype (PW 0).subtype z.1 +
            TensorProduct.map (PV 1).subtype (PW 1).subtype z.2)) ∧
        ∀ z, (L₁ z).val = exteriorSumTensorMap
          (TensorProduct.map (PV 1).subtype (PW 0).subtype z.1 +
            TensorProduct.map (PV 0).subtype (PW 1).subtype z.2) := by
  classical
  let PV := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V)
  let PW := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)
  let PS := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (V × W))
  let T (i j : ZMod 2) : (PV i ⊗[ℂ] PW j) →ₗ[ℂ]
      ExteriorAlgebra ℂ V ⊗[ℂ] ExteriorAlgebra ℂ W :=
    TensorProduct.map (PV i).subtype (PW j).subtype
  let F := exteriorSumTensorMap (V := V) (W := W)
  have hgrade (i j : ZMod 2) (z : PV i ⊗[ℂ] PW j) :
      F (T i j z) ∈ PS (i + j) := by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      simpa only [map_add] using (PS (i + j)).add_mem hz hz'
    | tmul a b =>
      have hleft : ExteriorAlgebra.map (LinearMap.inl ℂ V W) a.val ∈ PS i := by
        have hle : (PV i).map
            (ExteriorAlgebra.map (LinearMap.inl ℂ V W)).toLinearMap ≤ PS i := by
          simp only [PV, PS, CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
          apply iSup_mono
          intro k
          gcongr
          rintro z ⟨w, ⟨v, rfl⟩, rfl⟩
          exact ⟨LinearMap.inl ℂ V W v, (ExteriorAlgebra.map_apply_ι _ v).symm⟩
        exact hle ⟨a.val, a.property, rfl⟩
      have hright : ExteriorAlgebra.map (LinearMap.inr ℂ V W) b.val ∈ PS j := by
        have hle : (PW j).map
            (ExteriorAlgebra.map (LinearMap.inr ℂ V W)).toLinearMap ≤ PS j := by
          simp only [PW, PS, CliffordAlgebra.evenOdd, Submodule.map_iSup, Submodule.map_pow]
          apply iSup_mono
          intro k
          gcongr
          rintro z ⟨w, ⟨v, rfl⟩, rfl⟩
          exact ⟨LinearMap.inr ℂ V W v, (ExteriorAlgebra.map_apply_ι _ v).symm⟩
        exact hle ⟨b.val, b.property, rfl⟩
      exact SetLike.mul_mem_graded hleft hright
  let M₀ := F.comp ((T 0 0).coprod (T 1 1))
  let M₁ := F.comp ((T 1 0).coprod (T 0 1))
  have hM₀ (z : (PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1)) : M₀ z ∈ PS 0 := by
    simpa only [M₀, LinearMap.comp_apply, LinearMap.coprod_apply, map_add] using
      (PS 0).add_mem (hgrade 0 0 z.1) (hgrade 1 1 z.2)
  have hM₁ (z : (PV 1 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1)) : M₁ z ∈ PS 1 := by
    simpa only [M₁, LinearMap.comp_apply, LinearMap.coprod_apply, map_add] using
      (PS 1).add_mem (hgrade 1 0 z.1) (hgrade 0 1 z.2)
  let J₀ := M₀.codRestrict (PS 0) hM₀
  let J₁ := M₁.codRestrict (PS 1) hM₁
  -- Decompose both original factors, distribute their tensor product, and retain its order.
  let dV : (PV 0 × PV 1) ≃ₗ[ℂ] ExteriorAlgebra ℂ V :=
    Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl _)
  let dW : (PW 0 × PW 1) ≃ₗ[ℂ] ExteriorAlgebra ℂ W :=
    Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl _)
  let dS : (PS 0 × PS 1) ≃ₗ[ℂ] ExteriorAlgebra ℂ (V × W) :=
    Submodule.prodEquivOfIsCompl _ _ (CliffordAlgebra.evenOdd_isCompl _)
  let R : (((PV 0 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1)) ×
      ((PV 1 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1))) ≃ₗ[ℂ]
        (((PV 0 ⊗[ℂ] PW 0) × (PV 0 ⊗[ℂ] PW 1)) ×
          ((PV 1 ⊗[ℂ] PW 0) × (PV 1 ⊗[ℂ] PW 1))) :=
    { toFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
      invFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let D := R.trans
    (((TensorProduct.prodRight ℂ ℂ (PV 0) (PW 0) (PW 1)).symm.prodCongr
        (TensorProduct.prodRight ℂ ℂ (PV 1) (PW 0) (PW 1)).symm).trans
      ((TensorProduct.prodLeft ℂ ℂ (PV 0) (PV 1) (PW 0 × PW 1)).symm.trans
        (TensorProduct.congr dV dW)))
  let B := LinearEquiv.ofBijective F exteriorSumTensorMap_bijective
  have hwhole : dS.toLinearMap.comp (J₀.prodMap J₁) = B.toLinearMap.comp D.toLinearMap := by
    apply LinearMap.prod_ext <;> apply LinearMap.prod_ext <;>
      apply TensorProduct.ext' <;> intro x y
    all_goals
      simp [J₀, J₁, M₀, M₁, T, B, D, R, dV, dW, dS,
        TensorProduct.prodRight, TensorProduct.prodLeft]
  have hjoint : Function.Bijective (J₀.prodMap J₁) := by
    have hcomp := B.bijective.comp D.bijective
    change Function.Bijective (B.toLinearMap.comp D.toLinearMap) at hcomp
    rw [← hwhole] at hcomp
    exact (Function.Bijective.of_comp_iff' dS.bijective (J₀.prodMap J₁)).mp hcomp
  -- The full graded equivalence is block diagonal, so each actual parity map is bijective.
  have h₀ : Function.Bijective J₀ := by
    constructor
    · intro x y h
      have heq : J₀.prodMap J₁ (x, 0) = J₀.prodMap J₁ (y, 0) := Prod.ext h rfl
      exact congrArg Prod.fst (hjoint.injective heq)
    · intro z
      obtain ⟨x, hx⟩ := hjoint.surjective (z, 0)
      exact ⟨x.1, congrArg Prod.fst hx⟩
  have h₁ : Function.Bijective J₁ := by
    constructor
    · intro x y h
      have heq : J₀.prodMap J₁ (0, x) = J₀.prodMap J₁ (0, y) := Prod.ext rfl h
      exact congrArg Prod.snd (hjoint.injective heq)
    · intro z
      obtain ⟨x, hx⟩ := hjoint.surjective (0, z)
      exact ⟨x.2, congrArg Prod.snd hx⟩
  exact ⟨LinearEquiv.ofBijective J₀ h₀, LinearEquiv.ofBijective J₁ h₁,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordered wedge map from the tensor of two exterior bundles to their direct sum. -/
def exteriorSumTensorHom :
    Hom (fun x ↦ ExteriorAlgebra ℂ (E x) ⊗[ℂ] ExteriorAlgebra ℂ (F x))
      (fun x ↦ ExteriorAlgebra ℂ ((E ×ᵇ F) x)) where
  linearMap _ := exteriorSumTensorMap
  continuous_total := by
    -- The two inclusions and their exterior maps use the original sum topology.
    let A := fun x ↦ ExteriorAlgebra ℂ (E x)
    let B := fun x ↦ ExteriorAlgebra ℂ (F x)
    let C := fun x ↦ ExteriorAlgebra ℂ ((E ×ᵇ F) x)
    let u : Hom A C := (sumInl (E := E) (F := F)).exterior
    let v : Hom B C := (sumInr (E := E) (F := F)).exterior
    -- Test the tensor topology on each finite pure-tensor sum at one common base.
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit (fun x ↦ (Fin m → A x) × (Fin m → B x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit B)))) inferInstance
    have hc : Continuous (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit B)))) := continuous_induced_dom
    let p : C(D, X) := ⟨fun z ↦ z.proj, hc.fst⟩
    let := isFiniteRank_pullback (E := C) p
    let w (i : Fin m) : continuousSections (p *ᵖ C) :=
      ⟨fun z ↦ u.linearMap z.proj (z.snd.1 i) * v.linearMap z.proj (z.snd.2 i), by
        have hu := u.continuous_total.comp ((continuous_apply i).comp hc.snd.fst)
        have hv := v.continuous_total.comp ((continuous_apply i).comp hc.snd.snd)
        have hm := continuous_exterior_mul (E := E ×ᵇ F) p
          (fun z ↦ u.linearMap z.proj (z.snd.1 i))
          (fun z ↦ v.linearMap z.proj (z.snd.2 i)) hu hv
        change Continuous (fun z : D ↦ (⟨z,
          u.linearMap z.proj (z.snd.1 i) * v.linearMap z.proj (z.snd.2 i)⟩ :
            TotalSpace Unit (p *ᵖ C)))
        rw [(inducing_pullbackTotalSpaceEmbedding Unit C p).continuous_iff]
        exact continuous_id.prodMk hm⟩
    let s : continuousSections (p *ᵖ C) := ∑ i : Fin m, w i
    have hs := (Pullback.continuous_lift Unit C p).comp s.property
    apply hs.congr
    intro z
    apply TotalSpace.ext
    · rfl
    apply heq_of_eq
    change (∑ i : Fin m, w i).val z = exteriorSumTensorMap
      (∑ i : Fin m, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)
    simp only [map_sum, Submodule.coe_sum, Finset.sum_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The two original parity bundles of a direct sum are their ordered parity tensor sums. -/
theorem exists_exteriorParity_sum_iso :
    let P (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
    let Q (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
    let S (i : ZMod 2) := fun x ↦
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((E ×ᵇ F) x)) i
    ∃ u₀ : Iso ((fun x ↦ P 0 x ⊗[ℂ] Q 0 x) ×ᵇ (fun x ↦ P 1 x ⊗[ℂ] Q 1 x)) (fun x ↦ S 0 x),
      ∃ u₁ : Iso ((fun x ↦ P 1 x ⊗[ℂ] Q 0 x) ×ᵇ (fun x ↦ P 0 x ⊗[ℂ] Q 1 x)) (fun x ↦ S 1 x),
        (∀ x z, (u₀.linearEquiv x z).val = exteriorSumTensorMap
          (TensorProduct.map (P 0 x).subtype (Q 0 x).subtype z.1 +
            TensorProduct.map (P 1 x).subtype (Q 1 x).subtype z.2)) ∧
        ∀ x z, (u₁.linearEquiv x z).val = exteriorSumTensorMap
          (TensorProduct.map (P 1 x).subtype (Q 0 x).subtype z.1 +
            TensorProduct.map (P 0 x).subtype (Q 1 x).subtype z.2) := by
  classical
  let P (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
  let Q (i : ZMod 2) := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (F x)) i
  let S (i : ZMod 2) := fun x ↦
    CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ ((E ×ᵇ F) x)) i
  let A₀ := (fun x ↦ P 0 x ⊗[ℂ] Q 0 x) ×ᵇ (fun x ↦ P 1 x ⊗[ℂ] Q 1 x)
  let A₁ := (fun x ↦ P 1 x ⊗[ℂ] Q 0 x) ×ᵇ (fun x ↦ P 0 x ⊗[ℂ] Q 1 x)
  -- The algebraic equivalences have a fixed, natural forward map in every original fiber.
  choose L₀ L₁ h₀ h₁ using fun x ↦
    exists_exteriorSumParity_equiv (V := E x) (W := F x)
  let p (i : ZMod 2) : Hom (fun x ↦ P i x) (fun x ↦ ExteriorAlgebra ℂ (E x)) :=
    { linearMap x := (P i x).subtype
      continuous_total := continuous_induced_dom }
  let q (i : ZMod 2) : Hom (fun x ↦ Q i x) (fun x ↦ ExteriorAlgebra ℂ (F x)) :=
    { linearMap x := (Q i x).subtype
      continuous_total := continuous_induced_dom }
  let T (i j : ZMod 2) := (p i).tensor (q j)
  -- Addition of the two tensor summands is continuous on the same base.
  let sumHom {U V W : X → Type _}
      [∀ x, AddCommGroup (U x)] [∀ x, Module ℂ (U x)]
      [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
      [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
      [TopologicalSpace (TotalSpace Unit U)] [IsFiniteRank U]
      [TopologicalSpace (TotalSpace Unit V)] [IsFiniteRank V]
      [TopologicalSpace (TotalSpace Unit W)] [IsFiniteRank W]
      (a : Hom U W) (b : Hom V W) : Hom (U ×ᵇ V) W := by
    refine ⟨fun x ↦ (a.linearMap x).coprod (b.linearMap x), ?_⟩
    let f : C(TotalSpace Unit (U ×ᵇ V), X) := ⟨π Unit (U ×ᵇ V), continuous_proj⟩
    let := isFiniteRank_pullback (E := W) f
    let c : ∀ z : TotalSpace Unit (U ×ᵇ V), (f *ᵖ W) z :=
      fun z ↦ a.linearMap z.proj z.snd.1
    let d : ∀ z : TotalSpace Unit (U ×ᵇ V), (f *ᵖ W) z :=
      fun z ↦ b.linearMap z.proj z.snd.2
    have hc : Continuous (fun z ↦ (⟨z, c z⟩ : TotalSpace Unit (f *ᵖ W))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit W f).continuous_iff]
      exact continuous_id.prodMk (a.continuous_total.comp continuous_sum_fst)
    have hd : Continuous (fun z ↦ (⟨z, d z⟩ : TotalSpace Unit (f *ᵖ W))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit W f).continuous_iff]
      exact continuous_id.prodMk (b.continuous_total.comp continuous_sum_snd)
    exact (Pullback.continuous_lift Unit W f).comp
      (continuous_add_section (f *ᵖ W) c d hc hd)
  let K₀ := (exteriorSumTensorHom (E := E) (F := F)).comp (sumHom (T 0 0) (T 1 1))
  let K₁ := (exteriorSumTensorHom (E := E) (F := F)).comp (sumHom (T 1 0) (T 0 1))
  -- The parity topology is induced by inclusion in the exterior total space.
  let H₀ : Hom A₀ (fun x ↦ S 0 x) :=
    { linearMap x := (L₀ x).toLinearMap
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply K₀.continuous_total.congr
        intro z
        apply TotalSpace.ext
        · rfl
        exact heq_of_eq (h₀ z.proj z.snd).symm }
  let H₁ : Hom A₁ (fun x ↦ S 1 x) :=
    { linearMap x := (L₁ x).toLinearMap
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply K₁.continuous_total.congr
        intro z
        apply TotalSpace.ext
        · rfl
        exact heq_of_eq (h₁ z.proj z.snd).symm }
  -- Finite-rank inverse continuity upgrades these precise maps to bundle isomorphisms.
  exact ⟨H₀.toIso (fun x ↦ (L₀ x).bijective), H₁.toIso (fun x ↦ (L₁ x).bijective), h₀, h₁⟩

end AtiyahSinger.ComplexBundle
