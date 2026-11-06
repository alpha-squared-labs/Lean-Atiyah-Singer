/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.HermitianFixedRankModel

/-!
# Fixed complex models with the existing fiber norms

Public module ID: M1963.

An original locally finite-rank complex bundle of constant rank admits a
native Euclidean model with its supplied normed fibers. Only the phantom
model of the total space is retyped; neither the fibers nor their norms nor
the original Unit total-space topology are replaced. This is the complex
counterpart of the original real normed-fiber adapter.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

/-- Original linear charts give a fixed complex model using the existing fiber norms. -/
theorem exists_nativeFiberBundle_of_normedFibers [IsFiniteRank E] (r : ℕ)
    (hr : ∀ x : X, Module.finrank ℂ (E x) = r) :
    letI := nativeModelTopology E (EuclideanSpace ℂ (Fin r))
    ∃ b : FiberBundle (EuclideanSpace ℂ (Fin r)) E,
      letI := b
      VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E := by
  /- Original finite linear charts are retyped by the identity on vectors.
  Finite-dimensional uniqueness of the norm topology makes each original
  fiber inclusion inducing. The full atlas of linear charts then gives
  continuous native operator-valued coordinate changes. -/
  classical
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let V := EuclideanSpace ℂ (Fin r)
  let := nativeModelTopology E V
  -- Retype original charts and their fixed coordinates, keeping every underlying vector.
  have hcharts (x : X) : ∃ e : Trivialization V (π V E),
      x ∈ e.baseSet ∧ e.IsLinear ℂ := by
    obtain ⟨n, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
    let l : E x ≃ₗ[ℂ] (Fin n → ℂ) :=
      { toFun := fun v ↦ (e ⟨x, v⟩).2
        invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' hx))
          (e.toOpenPartialHomeomorph.symm (x, v)).snd
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
            (e.symm_apply_mk_proj (x := ⟨x, v⟩) (e.mem_source.mpr hx))
        right_inv := by
          intro v
          have hp := TotalSpace.mk_cast (F := Unit) (E := E)
            (e.proj_symm_apply' (x := v) hx) (e.toOpenPartialHomeomorph.symm (x, v)).snd
          exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hp).trans
            (congrArg Prod.snd (e.apply_symm_apply' hx))
        map_add' := (hlinear x hx).map_add
        map_smul' := (hlinear x hx).map_smul }
    have hdim : Module.finrank ℂ (E x) = n := by simpa using l.finrank_eq
    have hn : n = r := hdim.symm.trans (hr x)
    clear hdim
    subst n
    let c : (Fin r → ℂ) ≃L[ℂ] V := (EuclideanSpace.equiv (Fin r) ℂ).symm
    let e' : Trivialization V (π V E) :=
      (e.transFiberHomeomorph c.toHomeomorph).compHomeomorph (nativeModelTotalHomeomorph E V)
    refine ⟨e', hx, ⟨?_⟩⟩
    intro y hy
    constructor
    · intro v w
      change c (e ⟨y, v + w⟩).2 = c (e ⟨y, v⟩).2 + c (e ⟨y, w⟩).2
      rw [(hlinear y hy).map_add, map_add]
    · intro a v
      change c (e ⟨y, a • v⟩).2 = a • c (e ⟨y, v⟩).2
      rw [(hlinear y hy).map_smul, map_smul]
  choose chart hchart hlinear using hcharts
  -- The existing finite-dimensional norm gives the topology of each fiber inclusion.
  have hmk (x : X) : Topology.IsInducing (@TotalSpace.mk X V E x) := by
    let := hlinear x
    let c : E x ≃L[ℂ] V :=
      ((chart x).linearEquivAt ℂ x (hchart x)).toContinuousLinearEquiv
    let f : E x → ((π V E) ⁻¹' ({x} : Set X)) := fun v ↦ ⟨⟨x, v⟩, rfl⟩
    have hf : Topology.IsInducing f := by
      apply ((chart x).preimageSingletonHomeomorph (hchart x)).isInducing.of_comp_iff.mp
      exact c.toHomeomorph.isInducing
    exact Topology.IsInducing.subtypeVal.comp hf
  let b : FiberBundle V E :=
    { totalSpaceMk_isInducing' := hmk
      trivializationAtlas' := {e | e.IsLinear ℂ}
      trivializationAt' := chart
      mem_baseSet_trivializationAt' := hchart
      trivialization_mem_atlas' := hlinear }
  refine ⟨b, ?_⟩
  let := b
  refine { trivialization_linear' := fun e he ↦ he.out, continuousOn_coordChange' := ?_ }
  intro e e' he he'
  let : e.IsLinear ℂ := he.out
  let : e'.IsLinear ℂ := he'.out
  -- In the finite-dimensional model, continuous operator families are detected on vectors.
  apply continuousOn_clm_apply.mpr
  intro v
  have hin : ContinuousOn (fun y : X ↦ (y, v)) (e.baseSet ∩ e'.baseSet) :=
    continuousOn_id.prodMk continuousOn_const
  have hback := e.continuousOn_symm.comp hin fun y hy ↦ ⟨hy.1, Set.mem_univ v⟩
  have hout := e'.continuousOn.comp hback fun y hy ↦ by
    apply e'.mem_source.mpr
    exact hy.2
  apply hout.snd.congr
  intro y hy
  exact e.coordChangeL_apply e' hy v

end AtiyahSinger.ComplexBundle
