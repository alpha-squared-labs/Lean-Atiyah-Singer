/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SphereHodgeIndex
public import AtiyahSinger.Topology.EquivariantRepresentationAction

/-!
# Fixed coordinates for the original determinant twist of O(1)

Public module ID: M1982.

Tensoring a fixed finite representation with the original determinant line
has the same vector coordinates, with action `det(A) • ρ(A)`. The actual
tensor bundle is identified with these coordinates by the left tensor unitor.
Its pure-vector formula and its class in the original representation ring
are part of the same model theorem, so the coordinate action cannot be
substituted for an unrelated one-dimensional character.

This is the standard character-twist construction, specialized to the original
O(1) determinant representation for the direct conjugation argument.
The bundle and representation-ring comparisons are project supplements to
Atiyah--Singer I, Section 2. No Bott generation or conjugation formula is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

local notation "G" => Matrix.orthogonalGroup (Fin 1) ℝ

attribute [local instance] tensorTopology isFiniteRank_tensor trivialTopology isFiniteRank_trivial

set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original determinant tensor action in the same fixed vector coordinates as `ρ`. -/
def orthogonalLineDeterminantTwist (ρ : FiniteContinuousRepresentation G) :
    FiniteContinuousRepresentation G where
  dimension := ρ.dimension
  representation := ContRepresentation.ofMonoidHom
    { toFun A := (A.val.det : ℂ) • ρ.representation A
      map_one' := by
        ext v i
        simp
      map_mul' A B := by
        apply ContinuousLinearMap.ext
        intro v
        change ((A.val * B.val).det : ℂ) • ρ.representation (A * B) v =
          (A.val.det : ℂ) • ρ.representation A ((B.val.det : ℂ) • ρ.representation B v)
        rw [Matrix.det_mul, Complex.ofReal_mul, map_mul]
        change ((A.val.det : ℂ) * (B.val.det : ℂ)) •
          ρ.representation A (ρ.representation B v) =
            (A.val.det : ℂ) • ρ.representation A ((B.val.det : ℂ) • ρ.representation B v)
        rw [map_smul, smul_smul] }
  continuous_action :=
    (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst).matrix_det).smul ρ.continuous_action

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1200000 in

/-- The original determinant tensor bundle has the stated equivariant coordinates and K class. -/
theorem exists_orthogonalLineDeterminant_tensor_iso
    {X : Type*} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (ρ : FiniteContinuousRepresentation G) :
    ∃ e : Iso ((FiniteBundle.trivial X 1).tensor
        (FiniteBundle.trivial X ρ.dimension)).Fiber (FiniteBundle.trivial X ρ.dimension).Fiber,
      e.IsEquivariant
        ((EquivariantStructure.ofFiniteRepresentation
          (orthogonalDeterminantRepresentation 1)).tensor
          (EquivariantStructure.ofFiniteRepresentation ρ))
        (EquivariantStructure.ofFiniteRepresentation (orthogonalLineDeterminantTwist ρ)) ∧
      (∀ (x : X) (u : Fin 1 → ℂ) (v : Fin ρ.dimension → ℂ),
        e.linearEquiv x (u ⊗ₜ[ℂ] v) = u 0 • v) ∧
      finiteRepresentationClass (orthogonalLineDeterminantTwist ρ) =
        finiteRepresentationClass (orthogonalDeterminantRepresentation 1) *
          finiteRepresentationClass ρ := by
  classical
  let δ := orthogonalDeterminantRepresentation 1
  let σ := orthogonalLineDeterminantTwist ρ
  let J := FiniteBundle.trivial X ρ.dimension
  let T := (FiniteBundle.trivial X 1).tensor J
  let l : ((Fin 1 → ℂ) ⊗[ℂ] (Fin ρ.dimension → ℂ)) ≃ₗ[ℂ]
      (Fin ρ.dimension → ℂ) :=
    (TensorProduct.congr (LinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ))
      (LinearEquiv.refl ℂ (Fin ρ.dimension → ℂ))).trans
        (TensorProduct.lid ℂ (Fin ρ.dimension → ℂ))
  have hl (u : Fin 1 → ℂ) (v : Fin ρ.dimension → ℂ) :
      l (u ⊗ₜ[ℂ] v) = u 0 • v := rfl
  have hlinv (v : Fin ρ.dimension → ℂ) : l.symm v = (1 : Fin 1 → ℂ) ⊗ₜ[ℂ] v := rfl
  -- The same tensor unitor intertwines the actual determinant action, on all vectors.
  have hmap (A : G) :
      l.toLinearMap.comp
          (TensorProduct.map (δ.representation A).toLinearMap (ρ.representation A).toLinearMap) =
        (σ.representation A).toLinearMap.comp l.toLinearMap := by
    apply TensorProduct.ext'
    intro u v
    change l (δ.representation A u ⊗ₜ[ℂ] ρ.representation A v) =
      σ.representation A (l (u ⊗ₜ[ℂ] v))
    rw [hl, hl]
    change ((A.val.det : ℂ) * u (0 : Fin 1)) • ρ.representation A v =
      (A.val.det : ℂ) • ρ.representation A (u (0 : Fin 1) • v)
    rw [map_smul, smul_smul]
  -- Insertion is one pure-tensor generator in the original finite-sum total topology.
  have hins : Continuous (fun z : TotalSpace Unit J.Fiber ↦
      (⟨z.proj, l.symm z.snd⟩ : TotalSpace Unit T.Fiber)) := by
    let D := TotalSpace Unit (fun x : X ↦
      (Fin 1 → Fin 1 → ℂ) × (Fin 1 → J.Fiber x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun k ↦ (⟨z.proj, z.snd.1 k⟩ : TotalSpace Unit (FiniteBundle.trivial X 1).Fiber)),
        (fun k ↦ (⟨z.proj, z.snd.2 k⟩ : TotalSpace Unit J.Fiber)))) inferInstance
    have hsum : Continuous (fun z : D ↦
        (⟨z.proj, ∑ k : Fin 1, z.snd.1 k ⊗ₜ[ℂ] z.snd.2 k⟩ : TotalSpace Unit T.Fiber)) :=
      continuous_iSup_rng (i := 1) continuous_coinduced_rng
    let q (z : TotalSpace Unit J.Fiber) : D := ⟨z.proj, fun _ ↦ 1, fun _ ↦ z.snd⟩
    have hq : Continuous q := by
      apply continuous_induced_rng.mpr
      refine (continuous_proj (E := J.Fiber)).prodMk
        ((continuous_pi ?_).prodMk (continuous_pi (fun _ ↦ continuous_id)))
      intro _
      exact continuous_induced_rng.mpr
        ((continuous_proj (E := J.Fiber)).prodMk continuous_const)
    apply (hsum.comp hq).congr
    intro z
    simp only [Function.comp_apply, q, Fin.sum_univ_one, hlinv]
  let insert : Hom J.Fiber T.Fiber :=
    { linearMap _ := l.symm.toLinearMap, continuous_total := hins }
  let i := insert.toIso (fun _ ↦ l.symm.bijective)
  let e := i.symm
  have heval (x : X) (w : T.Fiber x) : e.linearEquiv x w = l w := by
    apply l.symm.injective
    change (i.linearEquiv x) ((i.linearEquiv x).symm w) = l.symm (l w)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  have he : e.IsEquivariant
      ((EquivariantStructure.ofFiniteRepresentation δ).tensor
        (EquivariantStructure.ofFiniteRepresentation ρ))
      (EquivariantStructure.ofFiniteRepresentation σ) := by
    intro A x w
    change e.linearEquiv (A • x)
      (TensorProduct.map (δ.representation A).toLinearMap (ρ.representation A).toLinearMap w) =
        σ.representation A (e.linearEquiv x w)
    rw [heval, heval]
    exact DFunLike.congr_fun (hmap A) w
  -- The identical unitor also identifies the actual finite tensor representation class.
  have hclass : finiteRepresentationClass (δ.tensor ρ) = finiteRepresentationClass σ := by
    apply finiteRepresentationClass_eq_of_isEquivalent
    let c := FiniteContinuousRepresentation.tensorCoordinates 1 ρ.dimension
    refine ⟨ContRepresentation.Equiv.mk (c.symm.trans l).toContinuousLinearEquiv ?_⟩
    intro A
    apply ContinuousLinearMap.ext
    intro w
    have hcoordinate (v : (Fin 1 → ℂ) ⊗[ℂ] (Fin ρ.dimension → ℂ)) :
        (δ.tensor ρ).representation A (c v) =
          c (TensorProduct.map (δ.representation A).toLinearMap
            (ρ.representation A).toLinearMap v) := by
      induction v using TensorProduct.inductionOn with
      | tmul u v => exact FiniteContinuousRepresentation.tensor_tmul δ ρ A u v
      | add u v hu hv => simp only [map_add, hu, hv]
    change l (c.symm ((δ.tensor ρ).representation A w)) = σ.representation A (l (c.symm w))
    have hw : (δ.tensor ρ).representation A w =
        c (TensorProduct.map (δ.representation A).toLinearMap
          (ρ.representation A).toLinearMap (c.symm w)) :=
      (congrArg ((δ.tensor ρ).representation A) (c.apply_symm_apply w)).symm.trans
        (hcoordinate (c.symm w))
    calc
      _ = l (c.symm (c (TensorProduct.map (δ.representation A).toLinearMap
          (ρ.representation A).toLinearMap (c.symm w)))) :=
        congrArg (fun v ↦ l (c.symm v)) hw
      _ = l (TensorProduct.map (δ.representation A).toLinearMap
          (ρ.representation A).toLinearMap (c.symm w)) :=
        congrArg l (c.symm_apply_apply _)
      _ = _ := DFunLike.congr_fun (hmap A) (c.symm w)
  refine ⟨e, he, ?_, ?_⟩
  · intro x u v
    rw [heval, hl]
  · change finiteRepresentationClass σ =
      representationMul G (finiteRepresentationClass δ) (finiteRepresentationClass ρ)
    rw [representationMul_finiteClass]
    exact hclass.symm

end AtiyahSinger
