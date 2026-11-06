/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ThomTensorSymbol
public import AtiyahSinger.Topology.ThomTensorReassociation

/-!
# Degree-zero coefficients and the original Thom tensor symbol

Public module ID: M2252.

The ordinary tensor associator and interchange move an ungraded coefficient
through both exterior parity blocks. Their continuity uses the native finite
rank tensor topologies. No graded sign is introduced by this coefficient.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor

variable {X : Type*} [TopologicalSpace X]

private theorem exists_tensor_comm_iso
    (A B : X → Type*)
    [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
    [∀ x, AddCommGroup (B x)] [∀ x, Module ℂ (B x)]
    [TopologicalSpace (TotalSpace Unit A)] [IsFiniteRank A]
    [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B] :
    ∃ e : Iso (fun x ↦ A x ⊗[ℂ] B x) (fun x ↦ B x ⊗[ℂ] A x),
      ∀ x, e.linearEquiv x = TensorProduct.comm ℂ (A x) (B x) := by
  let f : Hom (fun x ↦ A x ⊗[ℂ] B x) (fun x ↦ B x ⊗[ℂ] A x) :=
    { linearMap x := (TensorProduct.comm ℂ (A x) (B x)).toLinearMap
      continuous_total := by
        apply continuous_iSup_dom.mpr
        intro m
        apply continuous_coinduced_dom.mpr
        let D := TotalSpace Unit (fun x ↦ (Fin m → A x) × (Fin m → B x))
        let D' := TotalSpace Unit (fun x ↦ (Fin m → B x) × (Fin m → A x))
        let : TopologicalSpace D := TopologicalSpace.induced
          (fun z : D ↦ (z.proj,
            (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
            (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit B)))) inferInstance
        let : TopologicalSpace D' := TopologicalSpace.induced
          (fun z : D' ↦ (z.proj,
            (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit B)),
            (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit A)))) inferInstance
        have hd : Continuous (fun z : D ↦ (z.proj,
            (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit A)),
            (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit B)))) := continuous_induced_dom
        have hs : Continuous (fun z : D ↦ (⟨z.proj, z.snd.2, z.snd.1⟩ : D')) :=
          continuous_induced_rng.mpr (hd.fst.prodMk (hd.snd.snd.prodMk hd.snd.fst))
        have ht : Continuous (fun z : D' ↦
            (⟨z.proj, ∑ i, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
              TotalSpace Unit (fun x ↦ B x ⊗[ℂ] A x))) :=
          continuous_iSup_rng (i := m) continuous_coinduced_rng
        exact (ht.comp hs).congr (fun z ↦ by simp [map_sum]) }
  exact ⟨f.toIso (fun x ↦ (TensorProduct.comm ℂ (A x) (B x)).bijective),
    fun _ ↦ LinearEquiv.ext (fun _ ↦ rfl)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Moving a degree-zero coefficient through both parity blocks preserves each pure tensor. -/
theorem exists_thomTensorCoefficient_iso
    (A B P Q W : X → Type*)
    [∀ x, AddCommGroup (A x)] [∀ x, Module ℂ (A x)]
    [∀ x, AddCommGroup (B x)] [∀ x, Module ℂ (B x)]
    [∀ x, AddCommGroup (P x)] [∀ x, Module ℂ (P x)]
    [∀ x, AddCommGroup (Q x)] [∀ x, Module ℂ (Q x)]
    [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
    [TopologicalSpace (TotalSpace Unit A)] [IsFiniteRank A]
    [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B]
    [TopologicalSpace (TotalSpace Unit P)] [IsFiniteRank P]
    [TopologicalSpace (TotalSpace Unit Q)] [IsFiniteRank Q]
    [TopologicalSpace (TotalSpace Unit W)] [IsFiniteRank W] :
    ∃ e : Iso (fun x ↦ ((A x ⊗[ℂ] W x) ⊗[ℂ] P x) × ((B x ⊗[ℂ] W x) ⊗[ℂ] Q x))
        (fun x ↦ ((A x ⊗[ℂ] P x) × (B x ⊗[ℂ] Q x)) ⊗[ℂ] W x),
      (∀ (x : X) (a : A x) (w : W x) (p : P x),
        e.linearEquiv x ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] p, 0) = (a ⊗ₜ[ℂ] p, 0) ⊗ₜ[ℂ] w) ∧
      (∀ (x : X) (b : B x) (w : W x) (q : Q x),
        e.linearEquiv x (0, (b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] q) = (0, b ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] w) := by
  -- Move the coefficient through one exterior block using the ordinary associator and swap.
  obtain ⟨a₀, ha₀⟩ := exists_tensor_assoc_iso (E := A) (F := W) (G := P)
  obtain ⟨a₁, ha₁⟩ := exists_tensor_assoc_iso (E := B) (F := W) (G := Q)
  obtain ⟨c₀, hc₀⟩ := exists_tensor_comm_iso W P
  obtain ⟨c₁, hc₁⟩ := exists_tensor_comm_iso W Q
  obtain ⟨b₀, hb₀⟩ := exists_tensor_assoc_iso (E := A) (F := P) (G := W)
  obtain ⟨b₁, hb₁⟩ := exists_tensor_assoc_iso (E := B) (F := Q) (G := W)
  let s₀ := (a₀.trans ((Iso.refl A).tensor c₀)).trans b₀.symm
  let s₁ := (a₁.trans ((Iso.refl B).tensor c₁)).trans b₁.symm
  let U := fun x ↦ A x ⊗[ℂ] P x
  let V := fun x ↦ B x ⊗[ℂ] Q x
  let d₀ := (sumFst (E := U) (F := V)).tensor (Hom.id W)
  let d₁ := (sumSnd (E := U) (F := V)).tensor (Hom.id W)
  let d : Hom (fun x ↦ (U x × V x) ⊗[ℂ] W x)
      (fun x ↦ (U x ⊗[ℂ] W x) × (V x ⊗[ℂ] W x)) :=
    { linearMap x := (d₀.linearMap x).prod (d₁.linearMap x)
      continuous_total := continuous_induced_rng.mpr
        (d₀.continuous_total.prodMk d₁.continuous_total) }
  have hd (x : X) : d.linearMap x =
      (TensorProduct.prodLeft ℂ ℂ (U x) (V x) (W x)).toLinearMap := by
    apply TensorProduct.ext'
    intro u w
    rfl
  let D := d.toIso (fun x ↦ by
    rw [hd]
    exact (TensorProduct.prodLeft ℂ ℂ (U x) (V x) (W x)).bijective)
  let e := (s₀.sum s₁).trans D.symm
  refine ⟨e, ?_, ?_⟩
  · intro x a w p
    apply (D.linearEquiv x).injective
    change D.linearEquiv x ((D.linearEquiv x).symm
      (s₀.linearEquiv x ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] p), s₁.linearEquiv x 0)) = _
    rw [LinearEquiv.apply_symm_apply, map_zero]
    change (s₀.linearEquiv x ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] p), 0) =
      d.linearMap x ((a ⊗ₜ[ℂ] p, 0) ⊗ₜ[ℂ] w)
    rw [hd]
    change ((b₀.linearEquiv x).symm
      (TensorProduct.congr (LinearEquiv.refl ℂ (A x)) (c₀.linearEquiv x)
        (a₀.linearEquiv x ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] p))), 0) = _
    rw [ha₀, hb₀, hc₀]
    simp
  · intro x b w q
    apply (D.linearEquiv x).injective
    change D.linearEquiv x ((D.linearEquiv x).symm
      (s₀.linearEquiv x 0, s₁.linearEquiv x ((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] q))) = _
    rw [LinearEquiv.apply_symm_apply, map_zero]
    change (0, s₁.linearEquiv x ((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] q)) =
      d.linearMap x ((0, b ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] w)
    rw [hd]
    change (0, (b₁.linearEquiv x).symm
      (TensorProduct.congr (LinearEquiv.refl ℂ (B x)) (c₁.linearEquiv x)
        (a₁.linearEquiv x ((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] q)))) = _
    rw [ha₁, hb₁, hc₁]
    simp

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger

open scoped TensorProduct

/-- Ordinary coefficient interchange commutes with both blocks of the actual Thom symbol. -/
theorem thomTensorSymbol_tensorRight
    {A B W V : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (d : A →ₗ[ℂ] B) (d' : B →ₗ[ℂ] A) (z : V)
    (u : (((A ⊗[ℂ] W) ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0) ×
      ((B ⊗[ℂ] W) ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1)) ≃ₗ[ℂ]
      (((A ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0) ×
        (B ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1)) ⊗[ℂ] W))
    (v : (((B ⊗[ℂ] W) ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0) ×
      ((A ⊗[ℂ] W) ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1)) ≃ₗ[ℂ]
      (((B ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 0) ×
        (A ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) 1)) ⊗[ℂ] W))
    (hu₀ : ∀ a w p, u ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] p, 0) = (a ⊗ₜ[ℂ] p, 0) ⊗ₜ[ℂ] w)
    (hu₁ : ∀ b w q, u (0, (b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] q) = (0, b ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] w)
    (hv₀ : ∀ b w p, v ((b ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] p, 0) = (b ⊗ₜ[ℂ] p, 0) ⊗ₜ[ℂ] w)
    (hv₁ : ∀ a w q, v (0, (a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] q) = (0, a ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] w) :
    v.toLinearMap.comp (thomTensorSymbol (TensorProduct.map d LinearMap.id)
      (TensorProduct.map d' LinearMap.id) z) =
      (TensorProduct.map (thomTensorSymbol d d' z) (LinearMap.id : W →ₗ[ℂ] W)).comp
        u.toLinearMap := by
  have split r q : v (r, q) = v (r, 0) + v (0, q) := by
    simpa using v.map_add (r, 0) (0, q)
  -- The two pure parity inputs generate the full source, so ordinary tensor linearity suffices.
  apply LinearMap.prod_ext
  · apply TensorProduct.ext'
    intro aw e
    induction aw using TensorProduct.inductionOn with
    | tmul a w =>
      change v (thomTensorSymbol (TensorProduct.map d LinearMap.id)
        (TensorProduct.map d' LinearMap.id) z ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] e, 0)) =
        TensorProduct.map (thomTensorSymbol d d' z) LinearMap.id
          (u ((a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] e, 0))
      rw [hu₀]
      simp only [thomTensorSymbol, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        map_zero, add_zero]
      rw [split, hv₀, hv₁, ← TensorProduct.add_tmul]
      congr 1
    | add r t hr ht =>
      simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hr ht
  · apply TensorProduct.ext'
    intro aw e
    induction aw using TensorProduct.inductionOn with
    | tmul a w =>
      change v (thomTensorSymbol (TensorProduct.map d LinearMap.id)
        (TensorProduct.map d' LinearMap.id) z (0, (a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] e)) =
        TensorProduct.map (thomTensorSymbol d d' z) LinearMap.id
          (u (0, (a ⊗ₜ[ℂ] w) ⊗ₜ[ℂ] e))
      rw [hu₁]
      simp only [thomTensorSymbol, LinearMap.prod_apply, Function.prod_apply,
        LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        map_zero, zero_add, LinearMap.neg_apply]
      rw [show (-(a ⊗ₜ[ℂ] w ⊗ₜ[ℂ] cliffordSymbolParity z 1 e),
          -(d' a ⊗ₜ[ℂ] w ⊗ₜ[ℂ] e)) =
          -(a ⊗ₜ[ℂ] w ⊗ₜ[ℂ] cliffordSymbolParity z 1 e, d' a ⊗ₜ[ℂ] w ⊗ₜ[ℂ] e) from rfl,
        map_neg, split, hv₀, hv₁, ← TensorProduct.add_tmul, ← TensorProduct.neg_tmul]
      congr 1
    | add r t hr ht =>
      simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hr ht

end AtiyahSinger
