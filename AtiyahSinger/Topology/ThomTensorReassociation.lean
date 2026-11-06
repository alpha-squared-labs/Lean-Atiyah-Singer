/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol
public import AtiyahSinger.Topology.SupportTensorAction

/-!
# Ordered tensor reassociation for the supported Thom comparison

Public module ID: M2253.

The finite-rank pullback/tensor comparison allows the third fiber vector to
be treated as a tautological section. This proves continuity of the actual
associator without replacing any native total-space topology. The four parity
blocks then regroup in the prescribed order and intertwine the three original
reciprocal tensor symbols.

These comparisons are used by the supported direct-sum construction in
`ThomDirectSum`, following Karoubi IV.1.7--1.10.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum
  isFiniteRank_pullback sectionModule

variable {X : Type*} [TopologicalSpace X]
  {E F G : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]


/-- The same sum vector identifies the sum of pullbacks with the pullback of the sum.
This native-topology adapter is used when assembling the iterated Thom representative. -/
private def sumPullbackFamilyIso {Y : Type*} [TopologicalSpace Y] (f : C(Y, X)) :
    Iso ((f *ᵖ E) ×ᵇ (f *ᵖ F)) (f *ᵖ (E ×ᵇ F)) where
  linearEquiv _ := LinearEquiv.refl ℂ _
  continuous_total := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit (E ×ᵇ F) f).continuous_iff]
    apply continuous_proj.prodMk
    apply continuous_induced_rng.mpr
    exact ((Pullback.continuous_lift Unit E f).comp
      (continuous_sum_fst (E := f *ᵖ E) (F := f *ᵖ F))).prodMk
        ((Pullback.continuous_lift Unit F f).comp
          (continuous_sum_snd (E := f *ᵖ E) (F := f *ᵖ F)))
  continuous_symm := continuous_induced_rng.mpr
    (((sumFst (E := E) (F := F)).pullback f).continuous_total.prodMk
      ((sumSnd (E := E) (F := F)).pullback f).continuous_total)


/-- The four tensor factors commute with pullback in their finite-rank sum topologies.
The fiber types may lie in arbitrary universes. -/
theorem tensorSum_pullback_comparison {Y : Type*} [TopologicalSpace Y]
    {H : X → Type*} [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
    [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H] (f : C(Y, X)) :
    ∃ e : Iso
      (fun y ↦ (((f *ᵖ E) y ⊗[ℂ] (f *ᵖ F) y) ×
        ((f *ᵖ G) y ⊗[ℂ] (f *ᵖ H) y)))
      (f *ᵖ fun x ↦ ((E x ⊗[ℂ] F x) × (G x ⊗[ℂ] H x))),
      ∀ y w, e.linearEquiv y w = w := by
  let e := ((pullbackTensorIso (E := E) (F := F) f).symm.sum
    (pullbackTensorIso (E := G) (F := H) f).symm).trans
      (sumPullbackFamilyIso (E := fun x ↦ E x ⊗[ℂ] F x)
        (F := fun x ↦ G x ⊗[ℂ] H x) f)
  exact ⟨e, fun _ _ ↦ rfl⟩

omit [IsFiniteRank E] [IsFiniteRank F] in
private theorem continuous_tmul_family {Y : Type*} [TopologicalSpace Y]
    (p : C(Y, X)) (u : ∀ y, E (p y)) (v : ∀ y, F (p y))
    (hu : Continuous (fun y ↦ (⟨p y, u y⟩ : TotalSpace Unit E)))
    (hv : Continuous (fun y ↦ (⟨p y, v y⟩ : TotalSpace Unit F))) :
    Continuous (fun y ↦ (⟨p y, u y ⊗ₜ[ℂ] v y⟩ :
      TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x))) := by
  let D := TotalSpace Unit (fun x ↦ (Fin 1 → E x) × (Fin 1 → F x))
  let : TopologicalSpace D := TopologicalSpace.induced
    (fun z : D ↦ (z.proj,
      (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
      (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit F)))) inferInstance
  let f (y : Y) : D := ⟨p y, (fun _ ↦ u y, fun _ ↦ v y)⟩
  have hf : Continuous f := continuous_induced_rng.mpr
    (p.continuous.prodMk ((continuous_pi fun _ ↦ hu).prodMk (continuous_pi fun _ ↦ hv)))
  have hg : Continuous (fun z : D ↦
      (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
        TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x))) :=
    continuous_iSup_rng (i := 1) continuous_coinduced_rng
  simpa only [Function.comp_def, f, Fin.sum_univ_one] using hg.comp hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsFiniteRank E] [IsFiniteRank F] in
private theorem continuous_tensor_lift
    (L : ∀ x, E x ⊗[ℂ] F x →ₗ[ℂ] G x)
    (hL : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z.proj, L z.proj (z.snd.1 ⊗ₜ[ℂ] z.snd.2)⟩ : TotalSpace Unit G))) :
    Continuous (fun z : TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x) ↦
      (⟨z.proj, L z.proj z.snd⟩ : TotalSpace Unit G)) := by
  apply continuous_iSup_dom.mpr
  intro m
  apply continuous_coinduced_dom.mpr
  let D := TotalSpace Unit (fun x ↦ (Fin m → E x) × (Fin m → F x))
  let : TopologicalSpace D := TopologicalSpace.induced
    (fun z : D ↦ (z.proj,
      (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
      (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit F)))) inferInstance
  have hc : Continuous (fun z : D ↦ (z.proj,
      (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
      (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit F)))) := continuous_induced_dom
  let p : C(D, X) := ⟨fun z ↦ z.proj, hc.fst⟩
  let s (i : Fin m) : continuousSections (p *ᵖ G) :=
    ⟨fun z ↦ L z.proj (z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i), by
      change Continuous (fun z : D ↦
        (⟨z, L z.proj (z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)⟩ : TotalSpace Unit (p *ᵖ G)))
      rw [(inducing_pullbackTotalSpaceEmbedding Unit G p).continuous_iff]
      let f (z : D) : TotalSpace Unit (E ×ᵇ F) := ⟨z.proj, z.snd.1 i, z.snd.2 i⟩
      have hf : Continuous f := continuous_induced_rng.mpr
        (((continuous_apply i).comp hc.snd.fst).prodMk
          ((continuous_apply i).comp hc.snd.snd))
      exact continuous_id.prodMk (hL.comp hf)⟩
  let S : continuousSections (p *ᵖ G) := ∑ i : Fin m, s i
  have hs := (Pullback.continuous_lift Unit G p).comp S.property
  apply hs.congr
  intro z
  change (⟨z.proj, S.val z⟩ : TotalSpace Unit G) =
    ⟨z.proj, L z.proj (∑ i : Fin m, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)⟩
  congr 1
  simp only [S, Submodule.coe_sum]
  rw [Finset.sum_apply, map_sum]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The standard associator is continuous in the original finite-rank tensor topologies. -/
theorem exists_tensor_assoc_iso :
    ∃ e : Iso (fun x ↦ (E x ⊗[ℂ] F x) ⊗[ℂ] G x)
      (fun x ↦ E x ⊗[ℂ] (F x ⊗[ℂ] G x)),
      ∀ x, e.linearEquiv x = TensorProduct.assoc ℂ (E x) (F x) (G x) := by
  let T := fun x ↦ E x ⊗[ℂ] (F x ⊗[ℂ] G x)
  let Y := TotalSpace Unit G
  let p : C(Y, X) := ⟨π Unit G, continuous_proj⟩
  let A := p *ᵖ E
  let B := p *ᵖ F
  let C := p *ᵖ T
  -- Over the third total space its vector is a continuous tautological section.
  let L (y : Y) : A y ⊗[ℂ] B y →ₗ[ℂ] C y :=
    (TensorProduct.assoc ℂ (E y.proj) (F y.proj) (G y.proj)).toLinearMap.comp
      ((TensorProduct.mk ℂ (E y.proj ⊗[ℂ] F y.proj) (G y.proj)).flip y.snd)
  have hL : Continuous (fun z : TotalSpace Unit (A ×ᵇ B) ↦
      (⟨z.proj, L z.proj (z.snd.1 ⊗ₜ[ℂ] z.snd.2)⟩ : TotalSpace Unit C)) := by
    let q : C(TotalSpace Unit (A ×ᵇ B), X) := p.comp ⟨π Unit _, continuous_proj⟩
    have hE : Continuous (fun z : TotalSpace Unit (A ×ᵇ B) ↦
        (⟨q z, z.snd.1⟩ : TotalSpace Unit E)) :=
      (Pullback.continuous_lift Unit E p).comp continuous_sum_fst
    have hF : Continuous (fun z : TotalSpace Unit (A ×ᵇ B) ↦
        (⟨q z, z.snd.2⟩ : TotalSpace Unit F)) :=
      (Pullback.continuous_lift Unit F p).comp continuous_sum_snd
    have hG : Continuous (fun z : TotalSpace Unit (A ×ᵇ B) ↦
        (⟨q z, z.proj.snd⟩ : TotalSpace Unit G)) := continuous_proj
    have hFG := continuous_tmul_family (E := F) (F := G) q
      (fun z ↦ z.snd.2) (fun z ↦ z.proj.snd) hF hG
    have hEFG := continuous_tmul_family (E := E) (F := fun x ↦ F x ⊗[ℂ] G x)
      q (fun z ↦ z.snd.1)
      (fun z ↦ z.snd.2 ⊗ₜ[ℂ] z.proj.snd) hE hFG
    rw [(inducing_pullbackTotalSpaceEmbedding Unit T p).continuous_iff]
    exact continuous_proj.prodMk hEFG
  let H : Hom (fun y ↦ A y ⊗[ℂ] B y) C :=
    ⟨L, continuous_tensor_lift L hL⟩
  let J : Hom (p *ᵖ (fun x ↦ E x ⊗[ℂ] F x)) C :=
    H.comp (pullbackTensorIso (E := E) (F := F) p).toHom
  -- The pullback comparison keeps the first two tensor vectors unchanged.
  let S := (fun x ↦ E x ⊗[ℂ] F x) ×ᵇ G
  have hpure : Continuous (fun z : TotalSpace Unit S ↦
      (⟨z.proj, TensorProduct.assoc ℂ (E z.proj) (F z.proj) (G z.proj)
        (z.snd.1 ⊗ₜ[ℂ] z.snd.2)⟩ : TotalSpace Unit T)) := by
    let f (z : TotalSpace Unit S) : TotalSpace Unit (p *ᵖ (fun x ↦ E x ⊗[ℂ] F x)) :=
      ⟨(⟨z.proj, z.snd.2⟩ : Y), z.snd.1⟩
    have hf : Continuous f := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit (fun x ↦ E x ⊗[ℂ] F x) p).continuous_iff]
      exact continuous_sum_snd.prodMk continuous_sum_fst
    exact (Pullback.continuous_lift Unit T p).comp (J.continuous_total.comp hf)
  let a : Hom (fun x ↦ (E x ⊗[ℂ] F x) ⊗[ℂ] G x) T :=
    ⟨fun x ↦ (TensorProduct.assoc ℂ (E x) (F x) (G x)).toLinearMap,
      continuous_tensor_lift (E := fun x ↦ E x ⊗[ℂ] F x) (F := G) (G := T)
        (fun x ↦ (TensorProduct.assoc ℂ (E x) (F x) (G x)).toLinearMap) hpure⟩
  exact ⟨a.toIso (fun x ↦ (TensorProduct.assoc ℂ (E x) (F x) (G x)).bijective),
    fun _ ↦ LinearEquiv.ext (fun _ ↦ rfl)⟩

private theorem exists_tensor_sum_left_iso :
    ∃ e : Iso (fun x ↦ (E x × F x) ⊗[ℂ] G x)
      (fun x ↦ (E x ⊗[ℂ] G x) × (F x ⊗[ℂ] G x)),
      ∀ x, e.linearEquiv x = TensorProduct.prodLeft ℂ ℂ (E x) (F x) (G x) := by
  let a := (sumFst (E := E) (F := F)).tensor (Hom.id G)
  let b := (sumSnd (E := E) (F := F)).tensor (Hom.id G)
  let D : Hom (fun x ↦ (E x × F x) ⊗[ℂ] G x)
      (fun x ↦ (E x ⊗[ℂ] G x) × (F x ⊗[ℂ] G x)) :=
    { linearMap x := (a.linearMap x).prod (b.linearMap x)
      continuous_total := continuous_induced_rng.mpr
        (a.continuous_total.prodMk b.continuous_total) }
  have hD (x : X) : D.linearMap x =
      (TensorProduct.prodLeft ℂ ℂ (E x) (F x) (G x)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    rfl
  refine ⟨D.toIso (fun x ↦ ?_), ?_⟩
  · rw [hD]
    exact (TensorProduct.prodLeft ℂ ℂ (E x) (F x) (G x)).bijective
  · intro x
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun (hD x) v

private theorem exists_tensor_sum_right_iso :
    ∃ e : Iso (fun x ↦ E x ⊗[ℂ] (F x × G x))
      (fun x ↦ (E x ⊗[ℂ] F x) × (E x ⊗[ℂ] G x)),
      ∀ x, e.linearEquiv x = TensorProduct.prodRight ℂ ℂ (E x) (F x) (G x) := by
  let a := (Hom.id E).tensor (sumFst (E := F) (F := G))
  let b := (Hom.id E).tensor (sumSnd (E := F) (F := G))
  let D : Hom (fun x ↦ E x ⊗[ℂ] (F x × G x))
      (fun x ↦ (E x ⊗[ℂ] F x) × (E x ⊗[ℂ] G x)) :=
    { linearMap x := (a.linearMap x).prod (b.linearMap x)
      continuous_total := continuous_induced_rng.mpr
        (a.continuous_total.prodMk b.continuous_total) }
  have hD (x : X) : D.linearMap x =
      (TensorProduct.prodRight ℂ ℂ (E x) (F x) (G x)).toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    rfl
  refine ⟨D.toIso (fun x ↦ ?_), ?_⟩
  · rw [hD]
    exact (TensorProduct.prodRight ℂ ℂ (E x) (F x) (G x)).bijective
  · intro x
    apply LinearEquiv.ext
    intro v
    exact LinearMap.congr_fun (hD x) v

/-- The ordered parity reassociation, using only the ordinary tensor associator and block swaps. -/
def gradedTensorAssocEquiv (A B P Q R S : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup R] [Module ℂ R] [AddCommGroup S] [Module ℂ S] :
    ((((A ⊗[ℂ] P) × (B ⊗[ℂ] Q)) ⊗[ℂ] R) ×
      (((B ⊗[ℂ] P) × (A ⊗[ℂ] Q)) ⊗[ℂ] S)) ≃ₗ[ℂ]
      ((A ⊗[ℂ] ((P ⊗[ℂ] R) × (Q ⊗[ℂ] S))) ×
        (B ⊗[ℂ] ((Q ⊗[ℂ] R) × (P ⊗[ℂ] S)))) :=
  (((TensorProduct.prodLeft ℂ ℂ (A ⊗[ℂ] P) (B ⊗[ℂ] Q) R).prodCongr
      (TensorProduct.prodLeft ℂ ℂ (B ⊗[ℂ] P) (A ⊗[ℂ] Q) S)).trans
    (((TensorProduct.assoc ℂ A P R).prodCongr (TensorProduct.assoc ℂ B Q R)).prodCongr
      ((TensorProduct.assoc ℂ B P S).prodCongr (TensorProduct.assoc ℂ A Q S)))).trans
    ((((LinearEquiv.refl ℂ ((A ⊗[ℂ] (P ⊗[ℂ] R)) × (B ⊗[ℂ] (Q ⊗[ℂ] R)))).prodCongr
        (LinearEquiv.prodComm ℂ (B ⊗[ℂ] (P ⊗[ℂ] S)) (A ⊗[ℂ] (Q ⊗[ℂ] S)))).trans
      (LinearEquiv.prodProdProdComm ℂ (A ⊗[ℂ] (P ⊗[ℂ] R)) (B ⊗[ℂ] (Q ⊗[ℂ] R))
        (A ⊗[ℂ] (Q ⊗[ℂ] S)) (B ⊗[ℂ] (P ⊗[ℂ] S)))).trans
      ((TensorProduct.prodRight ℂ ℂ A (P ⊗[ℂ] R) (Q ⊗[ℂ] S)).symm.prodCongr
        (TensorProduct.prodRight ℂ ℂ B (Q ⊗[ℂ] R) (P ⊗[ℂ] S)).symm))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_sum_reorder_iso {H : X → Type*}
    [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
    [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H] :
    ∃ e : Iso ((E ×ᵇ F) ×ᵇ (G ×ᵇ H)) ((E ×ᵇ H) ×ᵇ (F ×ᵇ G)),
      ∀ x, e.linearEquiv x =
        ((LinearEquiv.refl ℂ (E x × F x)).prodCongr
          (LinearEquiv.prodComm ℂ (G x) (H x))).trans
            (LinearEquiv.prodProdProdComm ℂ (E x) (F x) (H x) (G x)) := by
  let d (x : X) :=
    ((LinearEquiv.refl ℂ (E x × F x)).prodCongr
      (LinearEquiv.prodComm ℂ (G x) (H x))).trans
        (LinearEquiv.prodProdProdComm ℂ (E x) (F x) (H x) (G x))
  let f : Hom ((E ×ᵇ F) ×ᵇ (G ×ᵇ H)) ((E ×ᵇ H) ×ᵇ (F ×ᵇ G)) :=
    { linearMap x := (d x).toLinearMap
      continuous_total := by
        let T := TotalSpace Unit ((E ×ᵇ F) ×ᵇ (G ×ᵇ H))
        have h₁ : Continuous (fun z : T ↦ (⟨z.proj, z.snd.1.1⟩ : TotalSpace Unit E)) :=
          (continuous_sum_fst (E := E) (F := F)).comp
            (continuous_sum_fst (E := E ×ᵇ F) (F := G ×ᵇ H))
        have h₂ : Continuous (fun z : T ↦ (⟨z.proj, z.snd.1.2⟩ : TotalSpace Unit F)) :=
          (continuous_sum_snd (E := E) (F := F)).comp
            (continuous_sum_fst (E := E ×ᵇ F) (F := G ×ᵇ H))
        have h₃ : Continuous (fun z : T ↦ (⟨z.proj, z.snd.2.1⟩ : TotalSpace Unit G)) :=
          (continuous_sum_fst (E := G) (F := H)).comp
            (continuous_sum_snd (E := E ×ᵇ F) (F := G ×ᵇ H))
        have h₄ : Continuous (fun z : T ↦ (⟨z.proj, z.snd.2.2⟩ : TotalSpace Unit H)) :=
          (continuous_sum_snd (E := G) (F := H)).comp
            (continuous_sum_snd (E := E ×ᵇ F) (F := G ×ᵇ H))
        have h₁₄ : Continuous (fun z : T ↦
            (⟨z.proj, z.snd.1.1, z.snd.2.2⟩ : TotalSpace Unit (E ×ᵇ H))) :=
          continuous_induced_rng.mpr (h₁.prodMk h₄)
        have h₂₃ : Continuous (fun z : T ↦
            (⟨z.proj, z.snd.1.2, z.snd.2.1⟩ : TotalSpace Unit (F ×ᵇ G))) :=
          continuous_induced_rng.mpr (h₂.prodMk h₃)
        exact continuous_induced_rng.mpr (h₁₄.prodMk h₂₃) }
  exact ⟨f.toIso (fun x ↦ (d x).bijective), fun _ ↦ LinearEquiv.ext (fun _ ↦ rfl)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ordered parity reassociation retains the native sum and tensor total topologies. -/
theorem exists_graded_tensor_assoc_iso
    (A B P Q R S : X → Type*)
    [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
    [∀ x, AddCommGroup (B x)] [∀ x, Module ℂ (B x)]
    [∀ x, AddCommGroup (P x)] [∀ x, Module ℂ (P x)]
    [∀ x, AddCommGroup (Q x)] [∀ x, Module ℂ (Q x)]
    [∀ x, AddCommGroup (R x)] [∀ x, Module ℂ (R x)]
    [∀ x, AddCommGroup (S x)] [∀ x, Module ℂ (S x)]
    [TopologicalSpace (TotalSpace Unit A)] [IsFiniteRank A]
    [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B]
    [TopologicalSpace (TotalSpace Unit P)] [IsFiniteRank P]
    [TopologicalSpace (TotalSpace Unit Q)] [IsFiniteRank Q]
    [TopologicalSpace (TotalSpace Unit R)] [IsFiniteRank R]
    [TopologicalSpace (TotalSpace Unit S)] [IsFiniteRank S] :
    ∃ e : Iso
      (fun x ↦ ((((A x ⊗[ℂ] P x) × (B x ⊗[ℂ] Q x)) ⊗[ℂ] R x) ×
        (((B x ⊗[ℂ] P x) × (A x ⊗[ℂ] Q x)) ⊗[ℂ] S x)))
      (fun x ↦ ((A x ⊗[ℂ] ((P x ⊗[ℂ] R x) × (Q x ⊗[ℂ] S x))) ×
        (B x ⊗[ℂ] ((Q x ⊗[ℂ] R x) × (P x ⊗[ℂ] S x))))),
      ∀ x, e.linearEquiv x = gradedTensorAssocEquiv (A x) (B x) (P x) (Q x) (R x) (S x) := by
  -- Distribute first, reassociate each of the four genuine three-factor tensors.
  obtain ⟨d₀, hd₀⟩ := exists_tensor_sum_left_iso
    (E := fun x ↦ A x ⊗[ℂ] P x) (F := fun x ↦ B x ⊗[ℂ] Q x) (G := R)
  obtain ⟨d₁, hd₁⟩ := exists_tensor_sum_left_iso
    (E := fun x ↦ B x ⊗[ℂ] P x) (F := fun x ↦ A x ⊗[ℂ] Q x) (G := S)
  obtain ⟨a₀, ha₀⟩ := exists_tensor_assoc_iso (E := A) (F := P) (G := R)
  obtain ⟨a₁, ha₁⟩ := exists_tensor_assoc_iso (E := B) (F := Q) (G := R)
  obtain ⟨a₂, ha₂⟩ := exists_tensor_assoc_iso (E := B) (F := P) (G := S)
  obtain ⟨a₃, ha₃⟩ := exists_tensor_assoc_iso (E := A) (F := Q) (G := S)
  obtain ⟨s, hs⟩ := exists_sum_reorder_iso
    (E := fun x ↦ A x ⊗[ℂ] (P x ⊗[ℂ] R x))
    (F := fun x ↦ B x ⊗[ℂ] (Q x ⊗[ℂ] R x))
    (G := fun x ↦ B x ⊗[ℂ] (P x ⊗[ℂ] S x))
    (H := fun x ↦ A x ⊗[ℂ] (Q x ⊗[ℂ] S x))
  obtain ⟨r₀, hr₀⟩ := exists_tensor_sum_right_iso
    (E := A) (F := fun x ↦ P x ⊗[ℂ] R x) (G := fun x ↦ Q x ⊗[ℂ] S x)
  obtain ⟨r₁, hr₁⟩ := exists_tensor_sum_right_iso
    (E := B) (F := fun x ↦ Q x ⊗[ℂ] R x) (G := fun x ↦ P x ⊗[ℂ] S x)
  -- The prescribed block permutation is followed by inverse right distributivity.
  let e := ((d₀.sum d₁).trans ((a₀.sum a₁).sum (a₂.sum a₃))).trans
    (s.trans (r₀.symm.sum r₁.symm))
  refine ⟨e, ?_⟩
  intro x
  change (((d₀.linearEquiv x).prodCongr (d₁.linearEquiv x)).trans
    (((a₀.linearEquiv x).prodCongr (a₁.linearEquiv x)).prodCongr
      ((a₂.linearEquiv x).prodCongr (a₃.linearEquiv x)))).trans
        ((s.linearEquiv x).trans
          ((r₀.linearEquiv x).symm.prodCongr (r₁.linearEquiv x).symm)) = _
  rw [hd₀, hd₁, ha₀, ha₁, ha₂, ha₃, hs, hr₀, hr₁]
  rfl

private theorem tensorProdRight_symm_apply {U V W : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (x : U ⊗[ℂ] V) (y : U ⊗[ℂ] W) :
    (TensorProduct.prodRight ℂ ℂ U V W).symm (x, y) =
      TensorProduct.map LinearMap.id (LinearMap.inl ℂ V W) x +
        TensorProduct.map LinearMap.id (LinearMap.inr ℂ V W) y := rfl

set_option maxHeartbeats 1000000 in

/-- Reassociation intertwines the two orders of the same three reciprocal tensor blocks. -/
theorem reciprocalTensorSymbol_assoc (A B P Q R S : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    [AddCommGroup R] [Module ℂ R] [AddCommGroup S] [Module ℂ S]
    (d : A →ₗ[ℂ] B) (d' : B →ₗ[ℂ] A)
    (e : P →ₗ[ℂ] Q) (e' : Q →ₗ[ℂ] P)
    (f : R →ₗ[ℂ] S) (f' : S →ₗ[ℂ] R) :
    (gradedTensorAssocEquiv B A P Q R S).toLinearMap.comp
      (reciprocalTensorSymbol (reciprocalTensorSymbol d d' e e')
        (reciprocalTensorSymbolReverse d d' e e') f f') =
      (reciprocalTensorSymbol d d' (reciprocalTensorSymbol e e' f f')
        (reciprocalTensorSymbolReverse e e' f f')).comp
          (gradedTensorAssocEquiv A B P Q R S).toLinearMap := by
  -- Work on the four parity summands, then on their actual three pure vectors.
  apply LinearMap.prod_ext <;> apply TensorProduct.ext <;>
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
    intro a p <;> apply LinearMap.ext <;> intro r
  all_goals
    simp only [gradedTensorAssocEquiv, reciprocalTensorSymbol, reciprocalTensorSymbolReverse,
      LinearMap.coe_comp, LinearMap.coe_inl, Function.comp_apply, LinearMap.compr₂ₛₗ_apply,
      TensorProduct.mk_apply, LinearEquiv.coe_coe, LinearMap.prod_apply, Function.prod_apply,
      LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
      LinearMap.neg_apply, map_zero, neg_zero, add_comm, zero_add, LinearEquiv.trans_apply,
      LinearEquiv.prodCongr_apply, TensorProduct.prodLeft_tmul, TensorProduct.zero_tmul,
      TensorProduct.assoc_tmul, LinearEquiv.refl_apply, LinearEquiv.prodComm_apply,
      Prod.swap_prod_mk, LinearEquiv.prodProdProdComm_apply, tensorProdRight_symm_apply,
      TensorProduct.prodRight_symm_tmul, Prod.fst_zero, Prod.snd_zero, add_zero,
      LinearMap.coe_inr, TensorProduct.neg_tmul, map_neg, Prod.mk.injEq, and_true, Prod.neg_mk,
      true_and]
  all_goals
    apply (TensorProduct.prodRight ℂ ℂ _ _ _).injective
    simp only [map_add, map_neg, TensorProduct.prodRight_tmul, TensorProduct.tmul_zero,
      Prod.neg_mk, neg_zero, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.injEq, true_and,
      and_true]
  all_goals simp only [TensorProduct.tmul_neg, neg_neg]

end AtiyahSinger.ComplexBundle
