/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SmoothFiniteRepresentation
public import AtiyahSinger.Geometry.SmoothBundleMapContinuity
public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.EquivariantBundleTransport
public import AtiyahSinger.Topology.EquivariantTrivialBundle

/-!
# A smooth native bundle for the same finite representation

Public module ID: M1398.

The standard Euclidean coordinate equivalence gives a smooth product bundle
carrying precisely the original finite representation. The comparison retains
that action and a global smooth frame. This supplies the exterior frame used
after a single common equivariant stabilization in analytic excision.

Only automatic smoothness of the original finite representation is used;
no replacement by a representation of the same dimension is made.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

attribute [local instance] trivialTopology isFiniteRank_trivial

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The given representation has a native smooth product model retaining its global frame. -/
theorem exists_smooth_finiteRepresentation_bundle (ρ : FiniteContinuousRepresentation G) :
    IsSmoothComplexBundle (n := n) (r := ρ.dimension)
        (Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))) ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin ρ.dimension))
        (Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension)))
      ∃ σ : EquivariantStructure G (Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))),
        σ.IsSmooth (n := n) (r := ρ.dimension) 𝓘(ℝ, VG) ∧
        ∃ e : Iso (Bundle.Trivial M (Fin ρ.dimension → ℂ))
            (Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension))),
          e.IsEquivariant (EquivariantStructure.ofFiniteRepresentation ρ) σ ∧
          (∀ (x : M) (v : Fin ρ.dimension → ℂ),
            e.linearEquiv x v = (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm v) ∧
          IsSmoothBundleMap (n := n) (r := ρ.dimension) (q := ρ.dimension)
            (E := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension)))
            (F := Bundle.Trivial M (EuclideanSpace ℂ (Fin ρ.dimension)))
            (fun _ ↦ LinearMap.id) := by
  classical
  let V := EuclideanSpace ℂ (Fin ρ.dimension)
  let T := Bundle.Trivial M V
  let c : (Fin ρ.dimension → ℂ) ≃L[ℂ] V :=
    (EuclideanSpace.equiv (Fin ρ.dimension) ℂ).symm
  let t := Bundle.Trivial.trivialization M V
  have hT : IsSmoothComplexBundle (n := n) (r := ρ.dimension) T := by
    constructor
    intro d f hd hf
    obtain rfl := Bundle.Trivial.eq_trivialization M V d
    obtain rfl := Bundle.Trivial.eq_trivialization M V f
    change ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, V →L[ℂ] V) ∞
      (fun x : M ↦ ((Bundle.Trivial.trivialization M V).coordChangeL ℂ
        (Bundle.Trivial.trivialization M V) x : V →L[ℂ] V)) _
    simp only [Bundle.Trivial.trivialization.coordChangeL]
    exact contMDiffOn_const
  let := hT
  let E : SmoothFiniteComplexBundle (n := n) M :=
    { rank := ρ.dimension, Fiber := T }
  let := modelTopology V T
  let e : Iso (Bundle.Trivial M (Fin ρ.dimension → ℂ)) T := {
    linearEquiv _ := c.toLinearEquiv
    continuous_total := by
      apply continuous_induced_rng.mpr
      have hcoord : Continuous (fun z : TotalSpace Unit
          (Bundle.Trivial M (Fin ρ.dimension → ℂ)) ↦ (z.proj, z.snd)) :=
        continuous_induced_dom
      exact (Bundle.Trivial.homeomorphProd M V).symm.continuous.comp
        (hcoord.fst.prodMk (c.continuous.comp hcoord.snd))
    continuous_symm := by
      apply continuous_induced_rng.mpr
      have hcoord : Continuous (fun z : TotalSpace Unit T ↦ (z.proj, z.snd)) :=
        (Bundle.Trivial.homeomorphProd M V).continuous.comp (continuous_unitTotalEquiv V T)
      exact hcoord.fst.prodMk (c.symm.continuous.comp hcoord.snd) }
  obtain ⟨σ, he⟩ := (EquivariantStructure.ofFiniteRepresentation (X := M) ρ).exists_conjugate e
  have hσvalue (g : G) (x : M) (v : T x) :
      σ.linearMap g x v = c (ρ.representation g (c.symm v)) := by
    have h := he g x (c.symm v)
    change c (ρ.representation g (c.symm v)) = σ.linearMap g x (c (c.symm v)) at h
    rw [c.apply_symm_apply] at h
    exact h.symm
  have hσ : σ.IsSmooth (n := n) (r := ρ.dimension) 𝓘(ℝ, VG) := by
    intro d f hd hf j
    obtain rfl := Bundle.Trivial.eq_trivialization M V d
    obtain rfl := Bundle.Trivial.eq_trivialization M V f
    have hs : ContMDiff (𝓘(ℝ, VG).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, V) ∞
        (fun p : G × M ↦ c (ρ.representation p.1 (c.symm (EuclideanSpace.single j 1)))) :=
      (c.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp
        (ρ.contMDiff_action.comp (contMDiff_fst.prodMk contMDiff_const))
    apply hs.contMDiffOn.congr
    intro p hp
    change σ.linearMap p.1 p.2 (t.symmL ℂ p.2 (EuclideanSpace.single j 1)) = _
    rw [hσvalue, t.symmL_apply hp.1]
    rw [show t.symm p.2 (EuclideanSpace.single j 1) = EuclideanSpace.single j 1 from
      Bundle.Trivial.trivialization_symm_apply M V _ _]
  let j (x : M) : E.Fiber x ≃ₗ[ℂ] V := LinearEquiv.refl ℂ V
  have hj : IsSmoothBundleMap (n := n) (r := E.rank) (q := ρ.dimension)
      (E := E.Fiber) (F := Bundle.Trivial M V) (fun x ↦ (j x).toLinearMap) := by
    intro d hd f hf i
    obtain rfl := Bundle.Trivial.eq_trivialization M V d
    obtain rfl := Bundle.Trivial.eq_trivialization M V f
    apply (contMDiffOn_const (c := EuclideanSpace.single i (1 : ℂ))).congr
    intro x hx
    change t.symmL ℂ x (EuclideanSpace.single i 1) = EuclideanSpace.single i 1
    rw [t.symmL_apply hx.1]
    exact Bundle.Trivial.trivialization_symm_apply M V _ _
  exact ⟨hT, σ, hσ, e, he, fun _ _ ↦ rfl, hj⟩

end AtiyahSinger
