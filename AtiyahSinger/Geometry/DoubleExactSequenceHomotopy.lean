/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.Homotopy.Basic

/-!
# Three shears for two compatible split exact sequences

Public module ID: M1167.

A comparison of the two orders of splitting a commutative exact-sequence diagram
differs from the positive middle-factor shuffle by three real shears. Scaling their
coefficients gives actual invertible maps with explicit inverses at every parameter.
The four normalization identities below express the original injection/projection
squares; no determinant or orientation-only substitute is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [AddCommGroup A] [AddCommGroup B] [Module ℝ A] [Module ℝ B]
  [IsTopologicalAddGroup A] [IsTopologicalAddGroup B]
  [ContinuousSMul ℝ A] [ContinuousSMul ℝ B]

/-- The three-shear path runs from a normalized double splitting to the positive shuffle. -/
def doubleSplitShearPath (L : ((A × B) × (A × B)) ≃L[ℝ] ((A × A) × (B × B)))
    (t : ℝ) : ((A × B) × (A × B)) ≃L[ℝ] ((A × A) × (B × B)) := by
  let U := A × B
  let β : A →L[ℝ] U := (ContinuousLinearMap.snd ℝ U U).comp
    (L.symm.toContinuousLinearMap.comp ((ContinuousLinearMap.inl ℝ (A × A) (B × B)).comp
      (ContinuousLinearMap.inl ℝ A A)))
  let δ : B →L[ℝ] B := (ContinuousLinearMap.snd ℝ B B).comp
    ((ContinuousLinearMap.snd ℝ (A × A) (B × B)).comp (L.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inl ℝ U U).comp (ContinuousLinearMap.inr ℝ A B))))
  let υ : (B × B) →L[ℝ] (A × A) := (ContinuousLinearMap.fst ℝ (A × A) (B × B)).comp
    (L.toContinuousLinearMap.comp
      ((ContinuousLinearMap.inr ℝ A B).prodMap (ContinuousLinearMap.inr ℝ A B)))
  let Q := (ContinuousLinearEquiv.refl ℝ U).skewProd (ContinuousLinearEquiv.refl ℝ U)
    (-(1 - t) • β.comp (ContinuousLinearMap.fst ℝ A B))
  let J : (U × U) ≃L[ℝ] ((A × A) × (B × B)) :=
    { LinearEquiv.prodProdProdComm ℝ A B A B with
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let R := (ContinuousLinearEquiv.refl ℝ B).skewProd (ContinuousLinearEquiv.refl ℝ B)
    ((1 - t) • δ)
  let W := (ContinuousLinearEquiv.prodComm ℝ (A × A) (B × B)).trans
    (((ContinuousLinearEquiv.refl ℝ (B × B)).skewProd
      (ContinuousLinearEquiv.refl ℝ (A × A)) ((1 - t) • υ)).trans
        (ContinuousLinearEquiv.prodComm ℝ (B × B) (A × A)))
  exact ((Q.trans J).trans W).trans ((ContinuousLinearEquiv.refl ℝ (A × A)).prodCongr R)

/-- The four original exact-sequence squares identify both endpoints of the three-shear path. -/
theorem doubleSplitShearPath_endpoints
    (L : ((A × B) × (A × B)) ≃L[ℝ] ((A × A) × (B × B)))
    (hbase : ∀ a c : A, (L.symm ((a, c), 0)).1 = (a, 0))
    (hvertical : ∀ a : A, L.symm ((0, a), 0) = ((0, 0), (a, 0)))
    (hproj : ∀ z : (A × B) × (A × B), (L z).2.1 = z.1.2)
    (hprojVertical : ∀ y : A × B, (L (0, y)).2 = (0, y.2)) :
    (∀ z, doubleSplitShearPath L 0 z = L z) ∧
      (∀ z, doubleSplitShearPath L 1 z = ((z.1.1, z.2.1), (z.1.2, z.2.2))) := by
  let β (a : A) : A × B := (L.symm ((a, 0), 0)).2
  let δ (b : B) : B := (L ((0, b), 0)).2.2
  let υ (z : B × B) : A × A := (L ((0, z.1), (0, z.2))).1
  -- The injection differs from the standard injection only by its vertical coefficient.
  have hinj (a c : A) : L.symm ((a, c), 0) = ((a, 0), β a + (c, 0)) := by
    have hsplit : ((a, c), (0 : B × B)) = ((a, 0), 0) + ((0, c), 0) := by
      ext <;> simp
    rw [hsplit, map_add, hvertical]
    apply Prod.ext
    · change (L.symm ((a, 0), 0)).1 + 0 = (a, 0)
      rw [add_zero, hbase]
    · rfl
  -- On the complementary factors, the projection has one remaining lower shear.
  have hrest (b d : B) : (L ((0, b), (0, d))).2 = (b, δ b + d) := by
    have hsplit : (((0 : A), b), ((0 : A), d)) = ((0, b), 0) + (0, (0, d)) := by
      ext <;> simp
    apply Prod.ext
    · exact hproj _
    · rw [hsplit, map_add]
      change (L ((0, b), 0)).2.2 + (L (0, (0, d))).2.2 = δ b + d
      rw [hprojVertical]
  constructor
  · intro z
    have hdecomp : z = L.symm ((z.1.1, z.2.1 - (β z.1.1).1), 0) +
        ((0, z.1.2), (0, z.2.2 - (β z.1.1).2)) := by
      rw [hinj]
      ext <;> simp [sub_eq_add_neg]
    have hvalue : L z =
        ((z.1.1, z.2.1 - (β z.1.1).1) + υ (z.1.2, z.2.2 - (β z.1.1).2),
          (z.1.2, δ z.1.2 + (z.2.2 - (β z.1.1).2))) := by
      conv_lhs => rw [hdecomp, map_add, L.apply_symm_apply]
      apply Prod.ext
      · rfl
      · simpa using hrest z.1.2 (z.2.2 - (β z.1.1).2)
    rw [hvalue]
    simp [doubleSplitShearPath, β, δ, υ, sub_eq_add_neg, add_comm]
  · intro z
    simp [doubleSplitShearPath, ContinuousLinearEquiv.skewProd_apply]

private theorem continuous_bundle_pair {X Z F G : Type*} {V W : X → Type*}
    [TopologicalSpace Z] [TopologicalSpace (TotalSpace F V)]
    [TopologicalSpace (TotalSpace G W)]
    (b : Z → X) (u : ∀ z, V (b z)) (v : ∀ z, W (b z))
    (hu : Continuous (fun z ↦ (⟨b z, u z⟩ : TotalSpace F V)))
    (hv : Continuous (fun z ↦ (⟨b z, v z⟩ : TotalSpace G W))) :
    Continuous (fun z ↦ (⟨b z, u z, v z⟩ : TotalSpace (F × G) (V ×ᵇ W))) :=
  (FiberBundle.Prod.isInducing_diag F V G W).continuous_iff.mpr (hu.prodMk hv)

private theorem continuous_bundle_fst {X Z F G : Type*} {V W : X → Type*}
    [TopologicalSpace Z] [TopologicalSpace (TotalSpace F V)]
    [TopologicalSpace (TotalSpace G W)]
    {f : Z → TotalSpace (F × G) (V ×ᵇ W)} (hf : Continuous f) :
    Continuous (fun z ↦ (⟨(f z).proj, (f z).snd.1⟩ : TotalSpace F V)) :=
  ((FiberBundle.Prod.isInducing_diag F V G W).continuous.comp hf).fst

private theorem continuous_bundle_snd {X Z F G : Type*} {V W : X → Type*}
    [TopologicalSpace Z] [TopologicalSpace (TotalSpace F V)]
    [TopologicalSpace (TotalSpace G W)]
    {f : Z → TotalSpace (F × G) (V ×ᵇ W)} (hf : Continuous f) :
    Continuous (fun z ↦ (⟨(f z).proj, (f z).snd.2⟩ : TotalSpace G W)) :=
  ((FiberBundle.Prod.isInducing_diag F V G W).continuous.comp hf).snd

private theorem continuous_bundle_combination {X Z F : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : X → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (b : Z → X) (u v : ∀ z, V (b z)) (a c : Z → ℝ)
    (hu : Continuous (fun z ↦ (⟨b z, u z⟩ : TotalSpace F V)))
    (hv : Continuous (fun z ↦ (⟨b z, v z⟩ : TotalSpace F V)))
    (ha : Continuous a) (hc : Continuous c) :
    Continuous (fun z ↦ (⟨b z, a z • u z + c z • v z⟩ : TotalSpace F V)) := by
  have hb := (FiberBundle.continuous_proj F V).comp hu
  rw [continuous_iff_continuousAt]
  intro z
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hb.continuousAt, ?_⟩
  let e := trivializationAt F V (b z)
  have hu' := ((FiberBundle.continuousAt_totalSpace F _ (x₀ := z)).mp hu.continuousAt).2
  have hv' := ((FiberBundle.continuousAt_totalSpace F _ (x₀ := z)).mp hv.continuousAt).2
  have hn : ∀ᶠ y in 𝓝 z, b y ∈ e.baseSet :=
    hb.continuousAt (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt F V (b z)))
  apply ((ha.continuousAt.smul hu').add (hc.continuousAt.smul hv')).congr_of_eventuallyEq
  filter_upwards [hn] with y hy
  change (e ⟨b y, a y • u y + c y • v y⟩).2 =
    a y • (e ⟨b y, u y⟩).2 + c y • (e ⟨b y, v y⟩).2
  simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hy, map_add, map_smul]

section BundleCylinder

variable {X FA FB : Type*} [TopologicalSpace X]
  [NormedAddCommGroup FA] [NormedSpace ℝ FA]
  [NormedAddCommGroup FB] [NormedSpace ℝ FB]
  {V W : X → Type*}
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, TopologicalSpace (W x)] [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [∀ x, IsTopologicalAddGroup (W x)] [∀ x, ContinuousSMul ℝ (W x)]
  [TopologicalSpace (TotalSpace FA V)] [FiberBundle FA V] [VectorBundle ℝ FA V]
  [TopologicalSpace (TotalSpace FB W)] [FiberBundle FB W] [VectorBundle ℝ FB W]

local notation "UV" => (V ×ᵇ W)
local notation "XX" => TotalSpace ((FA × FB) × (FA × FB)) (UV ×ᵇ UV)
local notation "YY" => TotalSpace ((FA × FA) × (FB × FB)) ((V ×ᵇ V) ×ᵇ (W ×ᵇ W))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- Several native product-bundle coordinate maps are composed without changing their topologies.
/-- The three-shear path is a homeomorphism of whole native bundle cylinders. -/
theorem exists_doubleSplitShearCylinder
    (L : ∀ x, ((V x × W x) × (V x × W x)) ≃L[ℝ] ((V x × V x) × (W x × W x)))
    (hL : Continuous (fun z : XX ↦ (⟨z.proj, L z.proj z.snd⟩ : YY)))
    (hLi : Continuous (fun z : YY ↦ (⟨z.proj, (L z.proj).symm z.snd⟩ : XX))) :
    ∃ H : (ℝ × XX) ≃ₜ (ℝ × YY), ∀ (t : ℝ) (z : XX),
      H (t, z) = (t, (⟨z.proj, doubleSplitShearPath (L z.proj) t z.snd⟩ : YY)) := by
  classical
  let β (x : X) (a : V x) : V x × W x := ((L x).symm ((a, 0), 0)).2
  let δ (x : X) (b : W x) : W x := (L x ((0, b), 0)).2.2
  let υ (x : X) (w : W x × W x) : V x × V x := (L x ((0, w.1), (0, w.2))).1
  -- Each coefficient is extracted from the same original total map or its inverse.
  have hβ : Continuous (fun z : TotalSpace FA V ↦
      (⟨z.proj, β z.proj z.snd⟩ : TotalSpace (FA × FB) UV)) := by
    have hb := FiberBundle.continuous_proj FA V
    have h0V := (Bundle.Trivialization.continuous_zeroSection (F := FA) (E := V) ℝ).comp hb
    have h0W := (Bundle.Trivialization.continuous_zeroSection (F := FB) (E := W) ℝ).comp hb
    exact continuous_bundle_snd (hLi.comp
      (continuous_bundle_pair _ _ _
        (continuous_bundle_pair _ _ _ continuous_id h0V)
        (continuous_bundle_pair _ _ _ h0W h0W)))
  have hδ : Continuous (fun z : TotalSpace FB W ↦
      (⟨z.proj, δ z.proj z.snd⟩ : TotalSpace FB W)) := by
    have hb := FiberBundle.continuous_proj FB W
    have h0V := (Bundle.Trivialization.continuous_zeroSection (F := FA) (E := V) ℝ).comp hb
    have h0W := (Bundle.Trivialization.continuous_zeroSection (F := FB) (E := W) ℝ).comp hb
    exact continuous_bundle_snd (continuous_bundle_snd (hL.comp
      (continuous_bundle_pair _ _ _
        (continuous_bundle_pair _ _ _ h0V continuous_id)
        (continuous_bundle_pair _ _ _ h0V h0W))))
  have hυ : Continuous (fun z : TotalSpace (FB × FB) (W ×ᵇ W) ↦
      (⟨z.proj, υ z.proj z.snd⟩ : TotalSpace (FA × FA) (V ×ᵇ V))) := by
    have hb := FiberBundle.continuous_proj (FB × FB) (W ×ᵇ W)
    have h0V := (Bundle.Trivialization.continuous_zeroSection (F := FA) (E := V) ℝ).comp hb
    exact continuous_bundle_fst (hL.comp
      (continuous_bundle_pair _ _ _
        (continuous_bundle_pair _ _ _ h0V (continuous_bundle_fst continuous_id))
        (continuous_bundle_pair _ _ _ h0V (continuous_bundle_snd continuous_id))))
  -- Every shear and its inverse are continuous for an arbitrary continuous real coefficient.
  let q (a : ℝ) (z : XX) : XX :=
    ⟨z.proj, z.snd.1, z.snd.2 + a • β z.proj z.snd.1.1⟩
  have hq (a : ℝ → ℝ) (ha : Continuous a) :
      Continuous (fun p : ℝ × XX ↦ q (a p.1) p.2) := by
    have hx := continuous_bundle_fst (continuous_snd (X := ℝ) (Y := XX))
    have hy := continuous_bundle_snd (continuous_snd (X := ℝ) (Y := XX))
    have hβx := hβ.comp (continuous_bundle_fst hx)
    dsimp only [q]
    apply continuous_bundle_pair (F := FA × FB) (G := FA × FB) (V := UV) (W := UV) _ _ _ hx
    simpa only [one_smul] using continuous_bundle_combination (F := FA × FB) (V := UV)
      (fun p : ℝ × XX ↦ p.2.proj) (fun p ↦ p.2.snd.2)
      (fun p ↦ β p.2.proj p.2.snd.1.1) (fun _ ↦ (1 : ℝ)) (fun p ↦ a p.1)
      hy hβx continuous_const (ha.comp continuous_fst)
  let r (a : ℝ) (z : YY) : YY :=
    ⟨z.proj, z.snd.1, z.snd.2.1, z.snd.2.2 + a • δ z.proj z.snd.2.1⟩
  have hr (a : ℝ → ℝ) (ha : Continuous a) :
      Continuous (fun p : ℝ × YY ↦ r (a p.1) p.2) := by
    have hx := continuous_bundle_fst (continuous_snd (X := ℝ) (Y := YY))
    have hy := continuous_bundle_snd (continuous_snd (X := ℝ) (Y := YY))
    have hb := continuous_bundle_fst hy
    have hd := continuous_bundle_snd hy
    dsimp only [r]
    apply continuous_bundle_pair (F := FA × FA) (G := FB × FB)
      (V := V ×ᵇ V) (W := W ×ᵇ W) _ _ _ hx
    apply continuous_bundle_pair (F := FB) (G := FB) (V := W) (W := W) _ _ _ hb
    simpa only [one_smul] using continuous_bundle_combination
      (fun p : ℝ × YY ↦ p.2.proj) (fun p ↦ p.2.snd.2.2)
      (fun p ↦ δ p.2.proj p.2.snd.2.1) (fun _ ↦ (1 : ℝ)) (fun p ↦ a p.1)
      hd (hδ.comp hb) continuous_const (ha.comp continuous_fst)
  let u (a : ℝ) (z : YY) : YY := ⟨z.proj, z.snd.1 + a • υ z.proj z.snd.2, z.snd.2⟩
  have hu (a : ℝ → ℝ) (ha : Continuous a) :
      Continuous (fun p : ℝ × YY ↦ u (a p.1) p.2) := by
    have hx := continuous_bundle_fst (continuous_snd (X := ℝ) (Y := YY))
    have hy := continuous_bundle_snd (continuous_snd (X := ℝ) (Y := YY))
    dsimp only [u]
    apply continuous_bundle_pair (F := FA × FA) (G := FB × FB)
      (V := V ×ᵇ V) (W := W ×ᵇ W) _ _ _ _ hy
    simpa only [one_smul] using continuous_bundle_combination (F := FA × FA) (V := V ×ᵇ V)
      (fun p : ℝ × YY ↦ p.2.proj) (fun p ↦ p.2.snd.1)
      (fun p ↦ υ p.2.proj p.2.snd.2) (fun _ ↦ (1 : ℝ)) (fun p ↦ a p.1)
      hx (hυ.comp hy) continuous_const (ha.comp continuous_fst)
  let Q : (ℝ × XX) ≃ₜ (ℝ × XX) :=
    { toFun p := (p.1, q (-(1 - p.1)) p.2)
      invFun p := (p.1, q (1 - p.1) p.2)
      left_inv p := by
        rcases p with ⟨t, z, x, y⟩
        simp [q]
        module
      right_inv p := by
        rcases p with ⟨t, z, x, y⟩
        simp [q]
        module
      continuous_toFun := continuous_fst.prodMk (hq _ (continuous_const.sub continuous_id).neg)
      continuous_invFun := continuous_fst.prodMk (hq _ (continuous_const.sub continuous_id)) }
  let J : XX ≃ₜ YY :=
    { toFun z := ⟨z.proj, (z.snd.1.1, z.snd.2.1), (z.snd.1.2, z.snd.2.2)⟩
      invFun z := ⟨z.proj, (z.snd.1.1, z.snd.2.1), (z.snd.1.2, z.snd.2.2)⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by
        have hid : Continuous (id : XX → XX) := continuous_id
        have h1 := continuous_bundle_fst hid
        have h2 := continuous_bundle_snd hid
        have h11 := continuous_bundle_fst h1
        have h12 := continuous_bundle_snd h1
        have h21 := continuous_bundle_fst h2
        have h22 := continuous_bundle_snd h2
        apply (FiberBundle.Prod.isInducing_diag (FA × FA) (V ×ᵇ V)
          (FB × FB) (W ×ᵇ W)).continuous_iff.mpr
        apply Continuous.prodMk
        · apply (FiberBundle.Prod.isInducing_diag FA V FA V).continuous_iff.mpr
          exact h11.prodMk h21
        · apply (FiberBundle.Prod.isInducing_diag FB W FB W).continuous_iff.mpr
          exact h12.prodMk h22
      continuous_invFun := by
        have hid : Continuous (id : YY → YY) := continuous_id
        have h1 := continuous_bundle_fst hid
        have h2 := continuous_bundle_snd hid
        have h11 := continuous_bundle_fst h1
        have h12 := continuous_bundle_snd h1
        have h21 := continuous_bundle_fst h2
        have h22 := continuous_bundle_snd h2
        apply (FiberBundle.Prod.isInducing_diag (FA × FB) UV
          (FA × FB) UV).continuous_iff.mpr
        apply Continuous.prodMk
        · apply (FiberBundle.Prod.isInducing_diag FA V FB W).continuous_iff.mpr
          exact h11.prodMk h21
        · apply (FiberBundle.Prod.isInducing_diag FA V FB W).continuous_iff.mpr
          exact h12.prodMk h22 }
  let U : (ℝ × YY) ≃ₜ (ℝ × YY) :=
    { toFun p := (p.1, u (1 - p.1) p.2)
      invFun p := (p.1, u (-(1 - p.1)) p.2)
      left_inv p := by
        rcases p with ⟨t, z, x, y⟩
        simp [u]
        module
      right_inv p := by
        rcases p with ⟨t, z, x, y⟩
        simp [u]
        module
      continuous_toFun := continuous_fst.prodMk (hu _ (continuous_const.sub continuous_id))
      continuous_invFun := continuous_fst.prodMk (hu _ (continuous_const.sub continuous_id).neg) }
  let R : (ℝ × YY) ≃ₜ (ℝ × YY) :=
    { toFun p := (p.1, r (1 - p.1) p.2)
      invFun p := (p.1, r (-(1 - p.1)) p.2)
      left_inv p := by
        rcases p with ⟨t, z, x, b, d⟩
        simp [r]
        module
      right_inv p := by
        rcases p with ⟨t, z, x, b, d⟩
        simp [r]
        module
      continuous_toFun := continuous_fst.prodMk (hr _ (continuous_const.sub continuous_id))
      continuous_invFun := continuous_fst.prodMk (hr _ (continuous_const.sub continuous_id).neg) }
  -- Compose the three genuine cylinder homeomorphisms in their original mathematical order.
  refine ⟨((Q.trans ((Homeomorph.refl ℝ).prodCongr J)).trans U).trans R, ?_⟩
  intro t z
  simp [Q, J, U, R, q, u, r, doubleSplitShearPath, β, δ, υ]

end BundleCylinder

end AtiyahSinger
