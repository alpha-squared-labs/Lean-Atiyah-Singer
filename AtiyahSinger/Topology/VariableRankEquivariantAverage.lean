/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantVectorBundle
public import AtiyahSinger.Topology.HermitianFixedRankModel

import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Haar averaging for bundles with locally varying finite rank

Public module ID: M2269.

For a compact Hausdorff group, the continuous Reynolds average acts on the
original fibers and total topologies. A supplied Hermitian metric gives norms for fiber integration;
local finite frames prove continuity independently of any fixed global rank.
At every base point where the original map intertwines along its whole orbit,
the average retains that same fiber map. This is the identity preservation
needed for near-diagonal equivariant transport on a paracompact cylinder.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle MeasureTheory Topology

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TopologicalSpace X]
  [MulAction G X] [ContinuousSMul G X]
  {E F : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

/-- A continuous bundle map has a continuous equivariant Reynolds average,
retaining its fiber map wherever the original map intertwines along the orbit. -/
theorem Hom.exists_equivariant_average_of_hermitian
    (a : Hom E F) (σ : EquivariantStructure G E) (τ : EquivariantStructure G F)
    (h : ContinuousHermitianMetric F) :
    ∃ b : Hom E F, b.IsEquivariant σ τ ∧
      ∀ x, (∀ (g : G) (v : E x),
        a.linearMap (g • x) (σ.linearMap g x v) = τ.linearMap g x (a.linearMap x v)) →
          b.linearMap x = a.linearMap x := by
  classical
  let : ∀ x, NormedAddCommGroup (F x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := h.fiberInnerProductSpace
  let : ∀ x, FiniteDimensional ℂ (F x) := fun x ↦ finite_fiber (E := F) x
  let : ∀ x, CompleteSpace (F x) := fun x ↦ FiniteDimensional.complete ℂ (F x)
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let ν : Measure G := Measure.haar
  let μ : Measure G := (ν Set.univ)⁻¹ • ν
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let : MulAction G (TotalSpace Unit F) := τ.toMulAction
  let Ψ (p : G × TotalSpace Unit E) : TotalSpace Unit F :=
    p.1 • a.totalMap (p.1⁻¹ • p.2)
  have hΨ : Continuous Ψ := τ.continuous_action.comp
    (continuous_fst.prodMk (a.continuous_total.comp
      (σ.continuous_action.comp (continuous_fst.inv.prodMk continuous_snd))))
  let L (g : G) (x : X) : E x →ₗ[ℂ] F x :=
    (LinearEquiv.cast (R := ℂ) (M := F) (smul_inv_smul g x)).toLinearMap.comp
      ((τ.linearMap g (g⁻¹ • x)).comp
        ((a.linearMap (g⁻¹ • x)).comp (σ.linearMap g⁻¹ x)))
  have hL (g : G) (x : X) (v : E x) :
      (⟨x, L g x v⟩ : TotalSpace Unit F) = Ψ (g, ⟨x, v⟩) :=
    TotalSpace.mk_cast (smul_inv_smul g x) _
  -- Finite chart coordinates are continuous linear equivalences for the chosen fiber norms.
  choose r d hd hlinear using (IsFiniteRank.exists_linear_trivialization (E := F))
  let coord (i x : X) (hx : x ∈ (d i).baseSet) : F x ≃ₗ[ℂ] (Fin (r i) → ℂ) := {
    toFun v := (d i ⟨x, v⟩).2
    invFun v := cast (congrArg F ((d i).proj_symm_apply' hx))
      ((d i).toOpenPartialHomeomorph.symm (x, v)).2
    left_inv := by
      intro v
      rw [cast_eq_iff_heq]
      exact congr_arg_heq (fun z : TotalSpace Unit F ↦ z.2)
        ((d i).symm_apply_mk_proj (x := ⟨x, v⟩) ((d i).mem_source.mpr hx))
    right_inv := by
      intro v
      have hp := TotalSpace.mk_cast (F := Unit) (E := F)
        ((d i).proj_symm_apply' (x := v) hx)
        ((d i).toOpenPartialHomeomorph.symm (x, v)).2
      exact (congrArg (fun z : TotalSpace Unit F ↦ (d i z).2) hp).trans
        (congrArg Prod.snd ((d i).apply_symm_apply' hx))
    map_add' := (hlinear i x hx).map_add
    map_smul' := (hlinear i x hx).map_smul }
  have hLc (x : X) (v : E x) : Continuous (fun g ↦ L g x v) := by
    have hc : Continuous (fun g ↦ (d x (Ψ (g, ⟨x, v⟩))).2) := by
      apply ((d x).toOpenPartialHomeomorph.continuousOn.comp_continuous
        (hΨ.comp (continuous_id.prodMk continuous_const)) ?_).snd
      intro g
      change Ψ (g, ⟨x, v⟩) ∈ (d x).source
      rw [← hL]
      exact (d x).mem_source.mpr (hd x)
    apply ((coord x x (hd x)).symm.toContinuousLinearEquiv.continuous.comp hc).congr
    intro g
    change (coord x x (hd x)).symm (d x (Ψ (g, ⟨x, v⟩))).2 = L g x v
    rw [← hL]
    exact (coord x x (hd x)).symm_apply_apply (L g x v)
  have hi (x : X) (v : E x) : Integrable (fun g ↦ L g x v) μ :=
    (hLc x v).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let B (x : X) : E x →ₗ[ℂ] F x := {
    toFun v := ∫ g, L g x v ∂μ
    map_add' v w := by
      simp only [map_add]
      exact integral_add (hi x v) (hi x w)
    map_smul' c v := by
      simp only [map_smul, RingHom.id_apply]
      exact integral_smul c (fun g ↦ L g x v) }
  have hB : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, B z.proj z.snd⟩ : TotalSpace Unit F)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    let i := z.proj
    let U : Set (TotalSpace Unit E) := {y | y.proj ∈ (d i).baseSet}
    have hU : IsOpen U := (d i).open_baseSet.preimage (continuous_proj (E := E))
    have hz : z ∈ U := hd i
    let Φ (p : G × TotalSpace Unit E) : Fin (r i) → ℂ := (d i (Ψ p)).2
    have hΦ : ContinuousOn Φ (Set.univ ×ˢ U) := by
      apply ((d i).toOpenPartialHomeomorph.continuousOn.comp hΨ.continuousOn ?_).snd
      intro p hp
      rw [← hL p.1 p.2.proj p.2.snd]
      exact (d i).mem_source.mpr hp.2
    have hint : ContinuousOn (fun y : TotalSpace Unit E ↦ ∫ g, Φ (g, y) ∂μ) U :=
      continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
        (hΦ.comp continuous_swap.continuousOn (fun p hp ↦ ⟨hp.2, hp.1⟩)) (by simp)
    have heq (y : TotalSpace Unit E) (hy : y ∈ U) :
        (d i ⟨y.proj, B y.proj y.snd⟩).2 = ∫ g, Φ (g, y) ∂μ := by
      change (coord i y.proj hy).toContinuousLinearEquiv
        (∫ g, L g y.proj y.snd ∂μ) = _
      rw [← (coord i y.proj hy).toContinuousLinearEquiv.integral_comp_comm]
      apply integral_congr_ae
      filter_upwards [] with g
      exact congrArg (fun w : TotalSpace Unit F ↦ (d i w).2) (hL g y.proj y.snd)
    apply (d i).continuousAt_of_comp_left
      (f := fun y : TotalSpace Unit E ↦
        (⟨y.proj, B y.proj y.snd⟩ : TotalSpace Unit F))
      (continuous_proj (E := E)).continuousAt hz
    apply ((continuous_proj (E := E)).continuousAt.prodMk
      (hint.continuousAt (hU.mem_nhds hz))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hz] with y hy
    exact Prod.ext ((d i).proj_toFun _ ((d i).mem_source.mpr hy)) (heq y hy)
  let b : Hom E F := ⟨B, hB⟩
  refine ⟨b, ?_, ?_⟩
  · intro g x v
    -- The action identity holds in the total spaces, including all base transports.
    have hconj (k : G) : L (g * k) (g • x) (σ.linearMap g x v) =
        τ.linearMap g x (L k x v) := by
      apply TotalSpace.mk_injective (F := Unit) (g • x)
      rw [hL]
      change Ψ (g * k, g • (⟨x, v⟩ : TotalSpace Unit E)) =
        g • (⟨x, L k x v⟩ : TotalSpace Unit F)
      rw [hL]
      dsimp only [Ψ]
      simp only [mul_inv_rev, mul_smul, inv_smul_smul]
    change (∫ k, L k (g • x) (σ.linearMap g x v) ∂μ) =
      τ.linearMap g x (∫ k, L k x v ∂μ)
    rw [← integral_mul_left_eq_self (μ := μ)
      (fun k ↦ L k (g • x) (σ.linearMap g x v)) g]
    simp_rw [hconj]
    let C : F x ≃L[ℂ] F (g • x) :=
      (LinearEquiv.ofBijective (τ.linearMap g x)
        (τ.linearMap_bijective g x)).toContinuousLinearEquiv
    exact C.integral_comp_comm (fun k ↦ L k x v)
  · intro x hx
    apply LinearMap.ext
    intro v
    have hfixed (g : G) : L g x v = a.linearMap x v := by
      apply TotalSpace.mk_injective (F := Unit) x
      rw [hL]
      change g • (⟨g⁻¹ • x, a.linearMap (g⁻¹ • x) (σ.linearMap g⁻¹ x v)⟩ :
        TotalSpace Unit F) = ⟨x, a.linearMap x v⟩
      rw [hx]
      exact smul_inv_smul g (⟨x, a.linearMap x v⟩ : TotalSpace Unit F)
    change (∫ g, L g x v ∂μ) = a.linearMap x v
    simp only [hfixed, integral_const, probReal_univ, one_smul]

end AtiyahSinger.ComplexBundle
