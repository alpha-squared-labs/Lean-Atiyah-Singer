/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SmoothFiniteRepresentation
public import AtiyahSinger.Geometry.OrthogonalSmoothAction
public import AtiyahSinger.Geometry.SmoothComplexBundleAtlas
public import AtiyahSinger.Geometry.SmoothOrthogonalPrincipalBundle
public import AtiyahSinger.Topology.AssociatedVectorCoordinates

/-!
# The original associated representation in the prescribed smooth principal atlas

Public module ID: M1060.

The principal charts give a smooth atlas on the actual associated coefficient
bundle. The finite representation is the specified one, on its original
coordinate vectors, and its automatic real smoothness gives the transition
law. This supplies the base coefficient in the sphere-bundle index argument
of SG III.13.6 without replacing it by a trivial bundle of the same rank.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "V" => Fin ρ.dimension → ℂ
local notation "E" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation

/-- The prescribed principal chart on the original associated coefficient fibers. -/
def associatedOrthogonalRepresentationChart (i : B) :
    Trivialization V (π Unit E) := by
  let : MulAction G V := associatedRepresentationAction ρ.representation
  let : ContinuousSMul G V := ⟨ρ.continuous_action⟩
  let H := associatedVectorTotalHomeomorph S.toIsPrincipalBundle ρ.representation
  let t := (exists_associatedBundleTrivialization (F := V) S.toIsPrincipalBundle
    (S.trivialization i) (S.equivariant i)).choose
  let t₀ := t.compHomeomorph H
  exact
    { toOpenPartialHomeomorph := t₀.toOpenPartialHomeomorph
      baseSet := t₀.baseSet
      open_baseSet := t₀.open_baseSet
      source_eq := by
        rw [t₀.source_eq]
        ext z
        change associatedBundleProjection (F := V) S.toIsPrincipalBundle (H z) ∈
          t₀.baseSet ↔ z.proj ∈ t₀.baseSet
        rw [show associatedBundleProjection (F := V) S.toIsPrincipalBundle (H z) =
          z.proj from z.snd.property]
      target_eq := t₀.target_eq
      proj_toFun := fun z hz ↦ (t₀.proj_toFun z hz).trans z.snd.property }

set_option backward.isDefEq.respectTransparency false in
/-- These coefficient charts retain the principal domain and every original representative. -/
theorem associatedOrthogonalRepresentationChart_properties (i : B) :
    (associatedOrthogonalRepresentationChart S ρ i).baseSet = (S.trivialization i).baseSet ∧
      ∀ (p : P) (b : B) (hp : projection p = b) (v : V),
        b ∈ (S.trivialization i).baseSet →
          (associatedOrthogonalRepresentationChart S ρ i
            ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp v⟩).2 =
              ρ.representation (S.trivialization i p).2 v := by
  let : MulAction G V := associatedRepresentationAction ρ.representation
  let : ContinuousSMul G V := ⟨ρ.continuous_action⟩
  let t := (exists_associatedBundleTrivialization (F := V) S.toIsPrincipalBundle
    (S.trivialization i) (S.equivariant i)).choose
  have ht := (exists_associatedBundleTrivialization (F := V) S.toIsPrincipalBundle
    (S.trivialization i) (S.equivariant i)).choose_spec
  refine ⟨ht.1, ?_⟩
  intro p b hp v hb
  change (t (associatedBundleMk G P V p v)).2 = _
  rw [ht.2.1 p v (hp ▸ hb)]
  rfl

set_option maxHeartbeats 800000 in
-- The original quotient charts and their dependent inverse coordinates are compared together.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The given orthogonal principal atlas makes the same associated representation smooth. -/
def associatedOrthogonalRepresentationAtlas : SmoothComplexBundleAtlas (n := n) E := by
  classical
  let := lieGroup_orthogonalGroup r
  let t := associatedOrthogonalRepresentationChart S ρ
  have hb (i : B) : (t i).baseSet = (S.trivialization i).baseSet :=
    (associatedOrthogonalRepresentationChart_properties S ρ i).1
  have hrep := fun i ↦ (associatedOrthogonalRepresentationChart_properties S ρ i).2
  have hlocal (i b : B) (h : b ∈ (S.trivialization i).baseSet) (v : V) :
      (t i ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation
        ((S.trivialization i).toPartialEquiv.symm (b, 1))
        ((S.trivialization i).proj_symm_apply' h) v⟩).2 = v := by
    rw [hrep i _ b _ v h]
    erw [(S.trivialization i).apply_symm_apply' (x := (1 : G)) h]
    simp
  have hinverse (i b : B) (h : b ∈ (S.trivialization i).baseSet) (v : V) :
      (t i).toPartialEquiv.symm (b, v) =
        ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation
          ((S.trivialization i).toPartialEquiv.symm (b, 1))
          ((S.trivialization i).proj_symm_apply' h) v⟩ := by
    let w : TotalSpace Unit E :=
      ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation
        ((S.trivialization i).toPartialEquiv.symm (b, 1))
        ((S.trivialization i).proj_symm_apply' h) v⟩
    have hw : (t i w).2 = v := hlocal i b h v
    calc
      (t i).toPartialEquiv.symm (b, v) =
          (t i).toPartialEquiv.symm (w.proj, (t i w).2) := by rw [hw]
      _ = w := (t i).symm_apply_mk_proj ((t i).mem_source.mpr ((hb i).symm ▸ h))
  refine
    { Index := B
      rank := fun _ ↦ ρ.dimension
      chart := t
      covers := fun b ↦ ⟨b, (hb b).symm ▸ S.mem_baseSet b⟩
      linear := ?_
      contMDiffOn_coordChange := ?_ }
  · intro i b h
    have hS := hb i ▸ h
    let e := associatedVectorFiberMkLinearEquiv S.toIsPrincipalBundle ρ.representation
      ((S.trivialization i).toPartialEquiv.symm (b, 1))
      ((S.trivialization i).proj_symm_apply' hS)
    constructor
    · intro u v
      obtain ⟨u, rfl⟩ := e.surjective u
      obtain ⟨v, rfl⟩ := e.surjective v
      rw [← e.map_add]
      exact (hlocal i b hS (u + v)).trans
        (congrArg₂ (· + ·) (hlocal i b hS u).symm (hlocal i b hS v).symm)
    · intro c v
      obtain ⟨v, rfl⟩ := e.surjective v
      rw [← e.map_smul]
      exact (hlocal i b hS (c • v)).trans (congrArg (c • ·) (hlocal i b hS v).symm)
  · intro i j k
    let τ (b : B) : G :=
      (S.trivialization j ((S.trivialization i).toPartialEquiv.symm (b, 1))).2
    let U : TopologicalSpace.Opens B :=
      ⟨_, (S.trivialization i).open_baseSet.inter (S.trivialization j).open_baseSet⟩
    -- The specified matrix transition is smooth in the original orthogonal Lie atlas.
    have hτ : ContMDiff (𝓡 n) 𝓘(ℝ, OrthogonalGroupModel r) ∞ (fun b : U ↦ τ b) := by
      apply (contMDiff_orthogonalGroup_iff (𝓡 n) r ∞ _).mpr
      intro a b
      have hs : ContMDiff (𝓡 n) 𝓘(ℝ, Fin r → Fin r → ℝ) ∞
          (fun x : U ↦ fun a b ↦ (τ x).val a b) := by
        intro x
        exact ((S.contMDiffOn_transition i j).contMDiffAt
          (U.isOpen.mem_nhds x.property)).comp x
          contMDiff_subtype_val.contMDiffAt
      exact contMDiff_pi_space.mp (contMDiff_pi_space.mp hs a) b
    have hs : ContMDiff (𝓡 n) 𝓘(ℝ, V) ∞
        (fun x : U ↦ ρ.representation (τ x) (Pi.single k 1)) :=
      ρ.contMDiff_action.comp (hτ.prodMk contMDiff_const)
    intro b h
    have hS : b ∈ U := ⟨hb i ▸ h.1, hb j ▸ h.2⟩
    have hcols : ContMDiffOn (𝓡 n) 𝓘(ℝ, V) ∞
        (fun b : B ↦ ρ.representation (τ b) (Pi.single k 1)) U := by
      intro x hx
      exact ((contMDiffAt_subtype_iff
        (f := fun b : B ↦ ρ.representation (τ b) (Pi.single k 1))
        (x := (⟨x, hx⟩ : U))).mp (hs ⟨x, hx⟩)).contMDiffWithinAt
    have hnear := hcols.contMDiffAt (U.isOpen.mem_nhds hS)
    apply (hnear.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [U.isOpen.mem_nhds hS] with x hx
    rw [hinverse i x hx.1 (Pi.single k 1)]
    exact hrep j _ x _ _ hx.2

end AtiyahSinger
