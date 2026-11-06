/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff
public import AtiyahSinger.Topology.ModelBundleTopology
public import AtiyahSinger.Topology.SupportTripleExternalProduct
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Trivial matrix representatives for the supported external product

Public module ID: M2266.

The reciprocal-cutoff external product is expressed on finite-dimensional
trivial tensor models. The comparison retains the specified small-bundle
isomorphisms, tensor final topologies and ordered parity sums. The four
coefficient spaces can have different dimensions and arbitrary universes.

A continuous matrix family invertible outside one compact set gives a
supported homotopy. The final positivity theorem interpolates each reverse
map from its Hermitian adjoint to its reciprocal partner. It assumes scalar
reciprocal compositions with positive sum and one bijective forward factor;
the adjoint compositions themselves need not be scalar. These are project
comparisons for SG III.13.5 and the Appendix C.1 product convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor isFiniteRank_pullback

/-- A fixed finite tensor operator acts continuously in the original external tensor topology. -/
def constantExternalTensorHom {X Y Z E F H : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [TopologicalSpace (TotalSpace Unit (Trivial Z H))]
    (hH : Continuous (fun p : Z × H ↦ (⟨p.1, p.2⟩ : TotalSpace Unit (Trivial Z H))))
    (f : C(X × Y, Z)) (L : E ⊗[ℂ] F →ₗ[ℂ] H) :
    letI := modelTopology E (Bundle.Trivial X E)
    letI := modelTopology F (Bundle.Trivial Y F)
    Hom (fun z : X × Y ↦ ((ContinuousMap.fst : C(X × Y, X)) *ᵖ (Bundle.Trivial X E)) z
      ⊗[ℂ] ((ContinuousMap.snd : C(X × Y, Y)) *ᵖ (Bundle.Trivial Y F)) z)
      (f *ᵖ (Bundle.Trivial Z H)) := by
  let := modelTopology E (Bundle.Trivial X E)
  let := modelTopology F (Bundle.Trivial Y F)
  let A := ((ContinuousMap.fst : C(X × Y, X)) *ᵖ (Bundle.Trivial X E))
  let B := ((ContinuousMap.snd : C(X × Y, Y)) *ᵖ (Bundle.Trivial Y F))
  let eE := (unitTotalHomeomorph E (Bundle.Trivial X E)).trans
    (Bundle.Trivial.homeomorphProd X E)
  let eF := (unitTotalHomeomorph F (Bundle.Trivial Y F)).trans
    (Bundle.Trivial.homeomorphProd Y F)
  have hE : Continuous (fun z : TotalSpace Unit A ↦ (z.snd : E)) :=
    eE.continuous.snd.comp
      (Pullback.continuous_lift Unit (Bundle.Trivial X E) ContinuousMap.fst)
  have hF : Continuous (fun z : TotalSpace Unit B ↦ (z.snd : F)) :=
    eF.continuous.snd.comp
      (Pullback.continuous_lift Unit (Bundle.Trivial Y F) ContinuousMap.snd)
  let l : E →ₗ[ℂ] F →L[ℂ] H :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (TensorProduct.curry L)
  have hl : Continuous (fun z : E × F ↦ L (z.1 ⊗ₜ[ℂ] z.2)) :=
    (l.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd
  refine { linearMap _ := L, continuous_total := ?_ }
  -- The tensor topology is final for its finite-sum maps, including the empty sum.
  apply continuous_iSup_dom.mpr
  intro m
  apply continuous_coinduced_dom.mpr
  let D := TotalSpace Unit (fun z : X × Y ↦ (Fin m → A z) × (Fin m → B z))
  let : TopologicalSpace D := TopologicalSpace.induced
    (fun z : D ↦ (z.proj,
      (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
      (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit B)))) inferInstance
  have hc : Continuous (fun z : D ↦ (z.proj,
      (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
      (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit B)))) := continuous_induced_dom
  have hs : Continuous (fun z : D ↦ ∑ i : Fin m, L (z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)) := by
    apply continuous_finsetSum
    intro i _
    exact hl.comp ((hE.comp ((continuous_apply i).comp hc.snd.fst)).prodMk
      (hF.comp ((continuous_apply i).comp hc.snd.snd)))
  rw [(inducing_pullbackTotalSpaceEmbedding Unit (Bundle.Trivial Z H) f).continuous_iff]
  have hout := hc.fst.prodMk (hH.comp
    ((f.continuous.comp hc.fst).prodMk hs))
  apply hout.congr
  intro z
  change (z.proj, (⟨f z.proj, ∑ i, L (z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)⟩ :
      TotalSpace Unit (Trivial Z H))) =
    (z.proj, (⟨f z.proj, L (∑ i, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)⟩ : TotalSpace Unit (Trivial Z H)))
  rw [map_sum]



attribute [local instance] sumTopology isFiniteRank_sum

set_option maxSynthPendingDepth 30

/-- The tensor sum of four prescribed trivializations retains the ordered original factors. -/
def externalTensorSumIso {X Y A B C D : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C] [FiniteDimensional ℂ C]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [FiniteDimensional ℂ D]
    (EA EB : FiniteBundle X) (EC ED : FiniteBundle Y) :
    letI := modelTopology A (Trivial X A)
    letI := modelTopology B (Trivial X B)
    letI := modelTopology C (Trivial Y C)
    letI := modelTopology D (Trivial Y D)
    letI := modelTopology ((A ⊗[ℂ] C) × (B ⊗[ℂ] D))
      (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D)))
    Iso EA.Fiber (Trivial X A) → Iso EB.Fiber (Trivial X B) →
    Iso EC.Fiber (Trivial Y C) → Iso ED.Fiber (Trivial Y D) →
    Iso (((EA.pullback ContinuousMap.fst).tensor (EC.pullback ContinuousMap.snd)).sum
      ((EB.pullback ContinuousMap.fst).tensor (ED.pullback ContinuousMap.snd))).Fiber
      (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D))) := by
  let := modelTopology A (Trivial X A)
  let := modelTopology B (Trivial X B)
  let := modelTopology C (Trivial Y C)
  let := modelTopology D (Trivial Y D)
  let := modelTopology ((A ⊗[ℂ] C) × (B ⊗[ℂ] D))
    (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D)))
  let := isFiniteRank_model A (Trivial X A)
  let := isFiniteRank_model B (Trivial X B)
  let := isFiniteRank_model C (Trivial Y C)
  let := isFiniteRank_model D (Trivial Y D)
  let := isFiniteRank_model ((A ⊗[ℂ] C) × (B ⊗[ℂ] D))
    (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D)))
  intro a b c d
  let S := (((EA.pullback ContinuousMap.fst).tensor (EC.pullback ContinuousMap.snd)).sum
    ((EB.pullback ContinuousMap.fst).tensor (ED.pullback ContinuousMap.snd))).Fiber
  let H := (A ⊗[ℂ] C) × (B ⊗[ℂ] D)
  let j : TotalSpace Unit (Bundle.Trivial (X × Y) H) ≃ₜ (X × Y) × H :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by
        have hd := (FiberBundle.Prod.isInducing_diag (A ⊗[ℂ] C)
          (Bundle.Trivial (X × Y) (A ⊗[ℂ] C)) (B ⊗[ℂ] D)
          (Bundle.Trivial (X × Y) (B ⊗[ℂ] D))).continuous.comp
            (continuous_unitTotalEquiv H (Bundle.Trivial (X × Y) H))
        have h₀ := (Bundle.Trivial.homeomorphProd (X × Y) (A ⊗[ℂ] C)).continuous.comp hd.fst
        have h₁ := (Bundle.Trivial.homeomorphProd (X × Y) (B ⊗[ℂ] D)).continuous.comp hd.snd
        exact h₀.fst.prodMk (h₀.snd.prodMk h₁.snd)
      continuous_invFun := by
        apply (continuous_modelTotal_iff H (Bundle.Trivial (X × Y) H) _).mpr
        apply (FiberBundle.Prod.isInducing_diag (A ⊗[ℂ] C)
          (Bundle.Trivial (X × Y) (A ⊗[ℂ] C)) (B ⊗[ℂ] D)
          (Bundle.Trivial (X × Y) (B ⊗[ℂ] D))).continuous_iff.mpr
        exact ((Bundle.Trivial.homeomorphProd (X × Y) (A ⊗[ℂ] C)).symm.continuous.comp
          (continuous_fst.prodMk continuous_snd.fst)).prodMk
            ((Bundle.Trivial.homeomorphProd (X × Y) (B ⊗[ℂ] D)).symm.continuous.comp
              (continuous_fst.prodMk continuous_snd.snd)) }
  let h₀ := (constantExternalTensorHom j.symm.continuous (ContinuousMap.id (X × Y))
    (LinearMap.inl ℂ (A ⊗[ℂ] C) (B ⊗[ℂ] D))).comp
      ((a.toHom.pullback ContinuousMap.fst).tensor
        (c.toHom.pullback ContinuousMap.snd))
  let h₁ := (constantExternalTensorHom j.symm.continuous (ContinuousMap.id (X × Y))
    (LinearMap.inr ℂ (A ⊗[ℂ] C) (B ⊗[ℂ] D))).comp
      ((b.toHom.pullback ContinuousMap.fst).tensor
        (d.toHom.pullback ContinuousMap.snd))
  have h₀c := j.continuous.snd.comp ((Pullback.continuous_lift Unit
    (Trivial (X × Y) H) (ContinuousMap.id (X × Y))).comp
      (h₀.continuous_total.comp (sumFst (E :=
        ((EA.pullback ContinuousMap.fst).tensor (EC.pullback ContinuousMap.snd)).Fiber)
        (F := ((EB.pullback ContinuousMap.fst).tensor
          (ED.pullback ContinuousMap.snd)).Fiber)).continuous_total))
  have h₁c := j.continuous.snd.comp ((Pullback.continuous_lift Unit
    (Trivial (X × Y) H) (ContinuousMap.id (X × Y))).comp
      (h₁.continuous_total.comp (sumSnd (E :=
        ((EA.pullback ContinuousMap.fst).tensor (EC.pullback ContinuousMap.snd)).Fiber)
        (F := ((EB.pullback ContinuousMap.fst).tensor
          (ED.pullback ContinuousMap.snd)).Fiber)).continuous_total))
  let f : Hom S (Trivial (X × Y) H) :=
    { linearMap z := (TensorProduct.map (a.linearEquiv z.1).toLinearMap
          (c.linearEquiv z.2).toLinearMap).prodMap
        (TensorProduct.map (b.linearEquiv z.1).toLinearMap (d.linearEquiv z.2).toLinearMap)
      continuous_total := by
        apply (j.symm.continuous.comp ((continuous_proj (E := S)).prodMk
          (h₀c.add h₁c))).congr
        intro z
        apply congrArg (TotalSpace.mk z.proj)
        exact Prod.ext (add_zero _) (zero_add _) }
  exact f.toIso (fun z ↦ ((TensorProduct.congr (a.linearEquiv z.1)
    (c.linearEquiv z.2)).prodCongr (TensorProduct.congr (b.linearEquiv z.1)
      (d.linearEquiv z.2))).bijective)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem cutoffLinearMap_congr_symm {X : Type*} [TopologicalSpace X]
    {E F G H : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
    [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
    [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
    [TopologicalSpace (TotalSpace Unit G)] [TopologicalSpace (TotalSpace Unit H)]
    (a : CompactSupportTriple E F) (e : Iso E G) (f : Iso F H)
    (ρ : C(X, unitInterval)) (x : X) (v : G x) :
    f.symm.linearEquiv x ((a.congr e f).cutoffLinearMap ρ x v) =
      a.cutoffLinearMap ρ x (e.symm.linearEquiv x v) := by
  classical
  by_cases hx : x ∈ a.control
  · simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.congr_control,
      dite_eq_left hx, LinearMap.zero_apply, map_zero]
  · dsimp only [CompactSupportTriple.cutoffLinearMap]
    have hxc : x ∉ (a.congr e f).control := hx
    rw [dite_eq_right hxc, dite_eq_right hx]
    change (f.linearEquiv x).symm
      (((ρ x : ℝ) : ℂ) • f.linearEquiv x
        (a.boundary.linearEquiv ⟨x, hx⟩ (e.symm.linearEquiv x v))) = _
    rw [map_smul, LinearEquiv.symm_apply_apply]
    rfl

open scoped unitInterval

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Original finite-dimensional trivial factors admit the prescribed reciprocal product matrix. -/
theorem exists_trivial_supportedExternalProduct {X Y A B C D : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C] [FiniteDimensional ℂ C]
    [NormedAddCommGroup D] [InnerProductSpace ℂ D] [FiniteDimensional ℂ D] :
    letI := modelTopology A (Trivial X A)
    letI := modelTopology B (Trivial X B)
    letI := modelTopology C (Trivial Y C)
    letI := modelTopology D (Trivial Y D)
    letI := isFiniteRank_model A (Trivial X A)
    letI := isFiniteRank_model B (Trivial X B)
    letI := isFiniteRank_model C (Trivial Y C)
    letI := isFiniteRank_model D (Trivial Y D)
    letI := modelTopology ((A ⊗[ℂ] C) × (B ⊗[ℂ] D))
      (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D)))
    letI := modelTopology ((B ⊗[ℂ] C) × (A ⊗[ℂ] D))
      (Trivial (X × Y) ((B ⊗[ℂ] C) × (A ⊗[ℂ] D)))
    letI := isFiniteRank_model ((A ⊗[ℂ] C) × (B ⊗[ℂ] D))
      (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D)))
    letI := isFiniteRank_model ((B ⊗[ℂ] C) × (A ⊗[ℂ] D))
      (Trivial (X × Y) ((B ⊗[ℂ] C) × (A ⊗[ℂ] D)))
    ∀ (a : CompactSupportTriple (Trivial X A) (Trivial X B))
      (b : CompactSupportTriple (Trivial Y C) (Trivial Y D))
      (ρ : C(X, I)) (U : Set X) (_hU : IsOpen U) (_hcontrol : a.control ⊆ U)
      (_hzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (_hL : IsCompact L)
      (_hone : ∀ x ∉ L, ρ x = 1)
      (τ : C(Y, I)) (V : Set Y) (_hV : IsOpen V) (_hbcontrol : b.control ⊆ V)
      (_hbzero : ∀ y ∈ V, τ y = 0) (M : Set Y) (_hM : IsCompact M)
      (_hbone : ∀ y ∉ M, τ y = 1),
      ∃ q : CompactSupportTriple
        (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D)))
        (Trivial (X × Y) ((B ⊗[ℂ] C) × (A ⊗[ℂ] D))),
        q.control = L ×ˢ M ∧
        (∀ (z : (q.controlᶜ : Set (X × Y))) v, q.boundary.linearEquiv z v =
          reciprocalTensorSymbol (a.cutoffLinearMap ρ z.val.1)
            (a.inverse.cutoffLinearMap ρ z.val.1) (b.cutoffLinearMap τ z.val.2)
            (b.inverse.cutoffLinearMap τ z.val.2) v) ∧
        q.compactSupportClass =
          compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass := by
  let := modelTopology A (Trivial X A)
  let := modelTopology B (Trivial X B)
  let := modelTopology C (Trivial Y C)
  let := modelTopology D (Trivial Y D)
  let := isFiniteRank_model A (Trivial X A)
  let := isFiniteRank_model B (Trivial X B)
  let := isFiniteRank_model C (Trivial Y C)
  let := isFiniteRank_model D (Trivial Y D)
  let := modelTopology ((A ⊗[ℂ] C) × (B ⊗[ℂ] D))
    (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D)))
  let := modelTopology ((B ⊗[ℂ] C) × (A ⊗[ℂ] D))
    (Trivial (X × Y) ((B ⊗[ℂ] C) × (A ⊗[ℂ] D)))
  let := isFiniteRank_model ((A ⊗[ℂ] C) × (B ⊗[ℂ] D))
    (Trivial (X × Y) ((A ⊗[ℂ] C) × (B ⊗[ℂ] D)))
  let := isFiniteRank_model ((B ⊗[ℂ] C) × (A ⊗[ℂ] D))
    (Trivial (X × Y) ((B ⊗[ℂ] C) × (A ⊗[ℂ] D)))
  intro a b ρ U hU hcontrol hzero L hL hone τ V hV hbcontrol hbzero M hM hbone
  let aₛ := a.toSupportBundleTriple
  let bₛ := b.toSupportBundleTriple
  let p := supportedExternalProductTriple aₛ bₛ ρ U hU hcontrol hzero L hL hone
    τ V hV hbcontrol hbzero M hM hbone
  let ea := (smallBundleIso (Trivial X A)).symm
  let eb := (smallBundleIso (Trivial X B)).symm
  let ec := (smallBundleIso (Trivial Y C)).symm
  let ed := (smallBundleIso (Trivial Y D)).symm
  -- These comparisons use the specified resizing maps and the original tensor-sum topology.
  let e := externalTensorSumIso aₛ.source aₛ.target bₛ.source bₛ.target ea eb ec ed
  let f := externalTensorSumIso aₛ.target aₛ.source bₛ.source bₛ.target eb ea ec ed
  let q := p.datum.congr e f
  refine ⟨q, rfl, ?_, ?_⟩
  · intro z v
    obtain ⟨w, rfl⟩ := (e.linearEquiv z.val).surjective v
    rw [show q.boundary.linearEquiv z (e.linearEquiv z.val w) =
      f.linearEquiv z.val (p.datum.boundary.linearEquiv z w) from by
        exact (p.datum.congr_apply e f z _).trans (congrArg
          (fun u ↦ f.linearEquiv z.val (p.datum.boundary.linearEquiv z u))
          ((e.linearEquiv z.val).symm_apply_apply w))]
    have ha₀ (v : aₛ.source.Fiber z.val.1) :
        eb.linearEquiv z.val.1 (aₛ.datum.cutoffLinearMap ρ z.val.1 v) =
          a.cutoffLinearMap ρ z.val.1 (ea.linearEquiv z.val.1 v) :=
      cutoffLinearMap_congr_symm a
        (smallBundleIso (Trivial X A)) (smallBundleIso (Trivial X B)) ρ z.val.1 v
    have ha₁ (v : aₛ.target.Fiber z.val.1) :
        ea.linearEquiv z.val.1 (aₛ.datum.inverse.cutoffLinearMap ρ z.val.1 v) =
          a.inverse.cutoffLinearMap ρ z.val.1 (eb.linearEquiv z.val.1 v) :=
      cutoffLinearMap_congr_symm a.inverse
        (smallBundleIso (Trivial X B)) (smallBundleIso (Trivial X A)) ρ z.val.1 v
    have hb₀ (v : bₛ.source.Fiber z.val.2) :
        ed.linearEquiv z.val.2 (bₛ.datum.cutoffLinearMap τ z.val.2 v) =
          b.cutoffLinearMap τ z.val.2 (ec.linearEquiv z.val.2 v) :=
      cutoffLinearMap_congr_symm b
        (smallBundleIso (Trivial Y C)) (smallBundleIso (Trivial Y D)) τ z.val.2 v
    have hb₁ (v : bₛ.target.Fiber z.val.2) :
        ec.linearEquiv z.val.2 (bₛ.datum.inverse.cutoffLinearMap τ z.val.2 v) =
          b.inverse.cutoffLinearMap τ z.val.2 (ed.linearEquiv z.val.2 v) :=
      cutoffLinearMap_congr_symm b.inverse
        (smallBundleIso (Trivial Y D)) (smallBundleIso (Trivial Y C)) τ z.val.2 v
    -- Naturality is checked on pure tensors in each original parity summand.
    change (TensorProduct.map (eb.linearEquiv z.val.1).toLinearMap
        (ec.linearEquiv z.val.2).toLinearMap).prodMap
      (TensorProduct.map (ea.linearEquiv z.val.1).toLinearMap
        (ed.linearEquiv z.val.2).toLinearMap)
      (reciprocalTensorSymbol (aₛ.datum.cutoffLinearMap ρ z.val.1)
        (aₛ.datum.inverse.cutoffLinearMap ρ z.val.1) (bₛ.datum.cutoffLinearMap τ z.val.2)
        (bₛ.datum.inverse.cutoffLinearMap τ z.val.2) w) =
      reciprocalTensorSymbol (a.cutoffLinearMap ρ z.val.1)
        (a.inverse.cutoffLinearMap ρ z.val.1) (b.cutoffLinearMap τ z.val.2)
        (b.inverse.cutoffLinearMap τ z.val.2)
        ((TensorProduct.map (ea.linearEquiv z.val.1).toLinearMap
          (ec.linearEquiv z.val.2).toLinearMap).prodMap
          (TensorProduct.map (eb.linearEquiv z.val.1).toLinearMap
            (ed.linearEquiv z.val.2).toLinearMap) w)
    have hmap :
        ((TensorProduct.map (eb.linearEquiv z.val.1).toLinearMap
          (ec.linearEquiv z.val.2).toLinearMap).prodMap
          (TensorProduct.map (ea.linearEquiv z.val.1).toLinearMap
            (ed.linearEquiv z.val.2).toLinearMap)).comp
          (reciprocalTensorSymbol (aₛ.datum.cutoffLinearMap ρ z.val.1)
            (aₛ.datum.inverse.cutoffLinearMap ρ z.val.1)
            (bₛ.datum.cutoffLinearMap τ z.val.2) (bₛ.datum.inverse.cutoffLinearMap τ z.val.2)) =
        (reciprocalTensorSymbol (a.cutoffLinearMap ρ z.val.1)
          (a.inverse.cutoffLinearMap ρ z.val.1) (b.cutoffLinearMap τ z.val.2)
          (b.inverse.cutoffLinearMap τ z.val.2)).comp
          ((TensorProduct.map (ea.linearEquiv z.val.1).toLinearMap
            (ec.linearEquiv z.val.2).toLinearMap).prodMap
            (TensorProduct.map (eb.linearEquiv z.val.1).toLinearMap
              (ed.linearEquiv z.val.2).toLinearMap)) := by
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro u v
      · simp only [reciprocalTensorSymbol, LinearMap.coe_comp, LinearMap.coe_inl,
          Function.comp_apply, LinearMap.prodMap_apply, LinearMap.prod_apply,
          Function.prod_apply, LinearMap.coprod_apply,
          TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
          map_zero, add_zero, Prod.mk.injEq]
        exact ⟨congrArg (fun q ↦ q ⊗ₜ[ℂ] ec.linearEquiv z.val.2 v) (ha₀ u),
          congrArg (fun q ↦ ea.linearEquiv z.val.1 u ⊗ₜ[ℂ] q) (hb₀ v)⟩
      · simp only [reciprocalTensorSymbol, LinearMap.coe_comp, LinearMap.coe_inr,
          Function.comp_apply, LinearMap.prodMap_apply, LinearMap.prod_apply,
          Function.prod_apply, LinearMap.coprod_apply, LinearMap.neg_apply,
          TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
          map_zero, map_neg, zero_add, Prod.mk.injEq, neg_inj]
        exact ⟨congrArg (fun q ↦ eb.linearEquiv z.val.1 u ⊗ₜ[ℂ] q) (hb₁ v),
          congrArg (fun q ↦ q ⊗ₜ[ℂ] ed.linearEquiv z.val.2 v) (ha₁ u)⟩
    exact LinearMap.congr_fun hmap w
  · exact (p.datum.compactSupportClass_congr e f).trans
      ((compactSupportTriple_compactSupportClass_ofBoundary p.source p.target p.datum).trans
        (supportedExternalProductTriple_compactSupportClass aₛ bₛ ρ U hU hcontrol hzero
          L hL hone τ V hV hbcontrol hbzero M hM hbone))

end AtiyahSinger


namespace AtiyahSinger

open Bundle ComplexBundle
open scoped unitInterval

variable {Z A B : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [TopologicalSpace (TotalSpace Unit (Trivial Z A))]
  [TopologicalSpace (TotalSpace Unit (Trivial Z B))]
  [IsFiniteRank (Trivial Z A)] [IsFiniteRank (Trivial Z B)]

/-- A matrix homotopy on one compact exterior identifies the prescribed endpoint triples. -/
theorem matrixFamily_compactSupportClass_eq
    (hA : Continuous (fun z : TotalSpace Unit (Trivial Z A) ↦ (z.snd : A)))
    (hB : Continuous (fun z : Z × B ↦ (⟨z.1, z.2⟩ : TotalSpace Unit (Trivial Z B))))
    (K : Set Z) (hK : IsCompact K)
    (Φ : C(I × Z, A →L[ℂ] B))
    (hΦ : ∀ (t : I) (z : (Kᶜ : Set Z)), Function.Bijective (Φ (t, z.val))) :
    ∀ (a b : CompactSupportTriple (Trivial Z A) (Trivial Z B))
      (ha : a.control ⊆ K) (hb : b.control ⊆ K),
      (∀ z v, Φ (0, z.val) v = (a.enlarge K hK ha).boundary.linearEquiv z v) →
      (∀ z v, Φ (1, z.val) v = (b.enlarge K hK hb).boundary.linearEquiv z v) →
      a.compactSupportClass = b.compactSupportClass := by
  intro a b ha hb hzero hone
  apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
  let p : C(I × (Kᶜ : Set Z), (Kᶜ : Set Z)) := ContinuousMap.snd
  let i : C((Kᶜ : Set Z), Z) := ⟨Subtype.val, continuous_subtype_val⟩
  let E := p *ᵖ (Restrict (Trivial Z A) Kᶜ)
  let F := p *ᵖ (Restrict (Trivial Z B) Kᶜ)
  let := isFiniteRank_pullback (E := Trivial Z A) i
  let := isFiniteRank_pullback (E := Trivial Z B) i
  let := isFiniteRank_pullback (E := Restrict (Trivial Z A) Kᶜ) p
  let := isFiniteRank_pullback (E := Restrict (Trivial Z B) Kᶜ) p
  have hbase : Continuous (π Unit E) := Pullback.continuous_proj Unit _ p
  have hvec : Continuous (fun z : TotalSpace Unit E ↦ (z.snd : A)) :=
    hA.comp ((Pullback.continuous_lift Unit (Trivial Z A) i).comp
      (Pullback.continuous_lift Unit (Restrict (Trivial Z A) Kᶜ) p))
  -- The same finite operator acts continuously over the original cylinder and restriction.
  let f : Hom E F :=
    { linearMap z := (Φ (z.1, z.2.val)).toLinearMap
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (Restrict (Trivial Z B) Kᶜ)
          p).continuous_iff]
        apply hbase.prodMk
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (Trivial Z B) i).continuous_iff]
        apply hbase.snd.prodMk
        have hΦbase := Φ.continuous.comp
          (hbase.fst.prodMk (continuous_subtype_val.comp hbase.snd))
        exact hB.comp ((continuous_subtype_val.comp hbase.snd).prodMk
          (hΦbase.clm_apply hvec)) }
  let e := f.toIso (fun z ↦ hΦ z.1 z.2)
  refine ⟨K, hK, ha, hb, ⟨{ iso := e, map_zero := ?_, map_one := ?_ }⟩⟩
  · intro z v
    exact hzero z v
  · intro z v
    exact hone z v

end AtiyahSinger


namespace AtiyahSinger

open scoped TensorProduct unitInterval

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [FiniteDimensional ℂ E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [FiniteDimensional ℂ E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [FiniteDimensional ℂ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [FiniteDimensional ℂ F₁]

/-- Interpolating the reverse maps from adjoints to reciprocal partners preserves
invertibility when their scalar composition sum is positive and one forward
factor is bijective. -/
theorem reciprocalTensorSymbol_adjoint_homotopy_bijective
    (d : E₀ →ₗ[ℂ] E₁) (d' : E₁ →ₗ[ℂ] E₀) (e : F₀ →ₗ[ℂ] F₁) (e' : F₁ →ₗ[ℂ] F₀)
    (r s : ℝ) (hr : 0 < r + s)
    (hd : d'.comp d = (r : ℂ) • LinearMap.id)
    (hd' : d.comp d' = (r : ℂ) • LinearMap.id)
    (he : e'.comp e = (s : ℂ) • LinearMap.id)
    (he' : e.comp e' = (s : ℂ) • LinearMap.id)
    (h : Function.Bijective d ∨ Function.Bijective e) (t : I) :
    Function.Bijective (reciprocalTensorSymbol d
      (((1 - (t : ℝ) : ℝ) : ℂ) • d.adjoint + ((t : ℝ) : ℂ) • d') e
      (((1 - (t : ℝ) : ℝ) : ℂ) • e.adjoint + ((t : ℝ) : ℂ) • e')) := by
  -- At zero this is exactly the already proved Hermitian graded matrix.
  by_cases ht : (t : ℝ) = 0
  · simpa [ht, weightedGradedTensorSymbol] using
      weightedGradedTensorSymbol_bijective d e 1 1
        (h.elim (fun hd ↦ Or.inl ⟨one_ne_zero, hd⟩) (fun he ↦ Or.inr ⟨one_ne_zero, he⟩))
  have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
  have hpositive : 0 < (t : ℝ) * (r + s) := mul_pos htpos hr
  have hnonneg : 0 ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.property.2
  let D₀ := TensorProduct.map d (LinearMap.id : F₀ →ₗ[ℂ] F₀)
  let D₁ := TensorProduct.map d.adjoint (LinearMap.id : F₁ →ₗ[ℂ] F₁)
  let e₀ := TensorProduct.map (LinearMap.id : E₀ →ₗ[ℂ] E₀) e
  let e₁ := TensorProduct.map (LinearMap.id : E₁ →ₗ[ℂ] E₁) e.adjoint
  let q : ℂ := ((1 - (t : ℝ) : ℝ) : ℂ)
  let p : ℂ := ((t : ℝ) : ℂ)
  let T := reciprocalTensorSymbol d (q • d.adjoint + p • d') e (q • e.adjoint + p • e')
  let S := reciprocalTensorSymbolReverse d (q • d.adjoint + p • d')
    e (q • e.adjoint + p • e')
  have hdx (x : E₀) : d' (d x) = (r : ℂ) • x := LinearMap.congr_fun hd x
  have hdx' (x : E₁) : d (d' x) = (r : ℂ) • x := LinearMap.congr_fun hd' x
  have hex (x : F₀) : e' (e x) = (s : ℂ) • x := LinearMap.congr_fun he x
  have hex' (x : F₁) : e (e' x) = (s : ℂ) • x := LinearMap.congr_fun he' x
  -- The mixed terms cancel; each diagonal is a nonnegative square plus a positive scalar.
  have hcomp : S.comp T =
      ((q • (D₀.adjoint.comp D₀ + e₀.adjoint.comp e₀) +
          (p * ((r : ℂ) + (s : ℂ))) • LinearMap.id).comp (LinearMap.fst ℂ _ _)).prod
        ((q • (D₁.adjoint.comp D₁ + e₁.adjoint.comp e₁) +
          (p * ((r : ℂ) + (s : ℂ))) • LinearMap.id).comp (LinearMap.snd ℂ _ _)) := by
    dsimp only [S, T, D₀, D₁, e₀, e₁]
    simp only [TensorProduct.adjoint_map, LinearMap.adjoint_id, LinearMap.adjoint_adjoint]
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
      intro x y <;> apply Prod.ext
    all_goals
      simp [reciprocalTensorSymbol, reciprocalTensorSymbolReverse, hdx, hdx', hex, hex']
    all_goals
      simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, TensorProduct.tmul_smul,
        ← TensorProduct.smul_tmul', RCLike.real_smul_eq_coe_smul (K := ℂ)]
      module
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro z hz
      change T z = 0 at hz
      have hc : (S.comp T) z = 0 := by simp only [LinearMap.comp_apply, hz, map_zero]
      rw [hcomp] at hc
      have hc₀ := congrArg Prod.fst hc
      have hc₁ := congrArg Prod.snd hc
      change q • (D₀.adjoint (D₀ z.1) + e₀.adjoint (e₀ z.1)) +
        (p * ((r : ℂ) + (s : ℂ))) • z.1 = 0 at hc₀
      change q • (D₁.adjoint (D₁ z.2) + e₁.adjoint (e₁ z.2)) +
        (p * ((r : ℂ) + (s : ℂ))) • z.2 = 0 at hc₁
      have hi₀ := congrArg (fun y ↦ (inner ℂ z.1 y).re) hc₀
      have hi₁ := congrArg (fun y ↦ (inner ℂ z.2 y).re) hc₁
      simp only [inner_add_right, inner_smul_right, LinearMap.adjoint_inner_right,
        inner_zero_right, Complex.zero_re, q, p, ← Complex.ofReal_add, ← Complex.ofReal_mul,
        Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero] at hi₀ hi₁
      rw [show (inner ℂ (D₀ z.1) (D₀ z.1)).re = ‖D₀ z.1‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (D₀ z.1),
        show (inner ℂ (e₀ z.1) (e₀ z.1)).re = ‖e₀ z.1‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (e₀ z.1),
        show (inner ℂ z.1 z.1).re = ‖z.1‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) z.1] at hi₀
      rw [show (inner ℂ (D₁ z.2) (D₁ z.2)).re = ‖D₁ z.2‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (D₁ z.2),
        show (inner ℂ (e₁ z.2) (e₁ z.2)).re = ‖e₁ z.2‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) (e₁ z.2),
        show (inner ℂ z.2 z.2).re = ‖z.2‖ ^ 2 from
          inner_self_eq_norm_sq (𝕜 := ℂ) z.2] at hi₁
      have hz₀ : z.1 = 0 := by
        apply norm_eq_zero.mp
        have hA := mul_nonneg hnonneg (add_nonneg (sq_nonneg ‖D₀ z.1‖)
          (sq_nonneg ‖e₀ z.1‖))
        have hle : (t : ℝ) * (r + s) * ‖z.1‖ ^ 2 ≤ 0 := by linarith only [hi₀, hA]
        have hsq : ‖z.1‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hle hpositive
        nlinarith only [hsq, norm_nonneg z.1]
      have hz₁ : z.2 = 0 := by
        apply norm_eq_zero.mp
        have hA := mul_nonneg hnonneg (add_nonneg (sq_nonneg ‖D₁ z.2‖)
          (sq_nonneg ‖e₁ z.2‖))
        have hle : (t : ℝ) * (r + s) * ‖z.2‖ ^ 2 ≤ 0 := by linarith only [hi₁, hA]
        have hsq : ‖z.2‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hle hpositive
        nlinarith only [hsq, norm_nonneg z.2]
      exact Prod.ext hz₀ hz₁
    · exact bot_le
  -- Either original invertible factor gives the equality of total parity dimensions.
  have hdim : Module.finrank ℂ ((E₀ ⊗[ℂ] F₀) × (E₁ ⊗[ℂ] F₁)) =
      Module.finrank ℂ ((E₁ ⊗[ℂ] F₀) × (E₀ ⊗[ℂ] F₁)) := by
    simp only [Module.finrank_prod, Module.finrank_tensorProduct]
    rcases h with hd | he
    · rw [(LinearEquiv.ofBijective d hd).finrank_eq]
    · rw [(LinearEquiv.ofBijective e he).finrank_eq]
      omega
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩

end AtiyahSinger
