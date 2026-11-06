/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedGraphRepresentation
public import AtiyahSinger.Analysis.EquivariantFredholmCoordinates

/-!
# The original closed operator index on its Hilbert graph domain

Public module ID: M0336.

Projection from the actual graph has precisely the original kernel and range
quotient. Supplied finite equivariant coordinates therefore compute its full
bounded Fredholm index. This supplies the fixed Hilbert source for the product
cutoff norm comparison and preserves the original geometric representation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {G E F : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in

/-- The original finite closed-kernel and quotient coordinates compute the graph Fredholm index. -/
theorem LinearPMap.exists_graphFredholmIndex
    (D : E →ₗ.[ℂ] F) (hD : D.IsClosed) (hrange : IsClosed (D.toFun.range : Set F))
    (ρ : ContRepresentation ℂ G E) (τ : ContRepresentation ℂ G F)
    (hτ : Continuous (fun p : G × F ↦ τ p.1 p.2))
    (κ χ : FiniteContinuousRepresentation G)
    (e : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] D.ker)
    (f : (Fin χ.dimension → ℂ) ≃ₗ[ℂ] (F ⧸ D.toFun.range))
    (he : ∀ g v, (e (κ.representation g v)).val = ρ g (e v).val)
    (hf : ∀ g v, f (χ.representation g (f.symm (D.toFun.range.mkQ v))) =
      D.toFun.range.mkQ (τ g v)) :
    let S := D.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
    let T := (WithLp.sndL 2 ℂ E F).comp S.subtypeL
    ∀ (γ : ContRepresentation ℂ G S)
      (hγ : Continuous (fun p : G × S ↦ γ p.1 p.2))
      (_hγvalue : ∀ g v, (γ g v).val = WithLp.toLp 2
        (ρ g (WithLp.ofLp v.val).1, τ g (WithLp.ofLp v.val).2)),
      ∃ hTg : ∀ g, T.comp (γ g) = (τ g).comp T,
        ∃ hT : T.IsFredholm,
          equivariantFredholmIndex γ τ hγ hτ T hTg hT =
            finiteRepresentationClass κ - finiteRepresentationClass χ := by
  classical
  let S := D.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
  let T := (WithLp.sndL 2 ℂ E F).comp S.subtypeL
  have hS : IsClosed (S : Set (WithLp 2 (E × F))) :=
    hD.preimage (WithLp.prod_continuous_ofLp 2 E F)
  let : CompleteSpace S := hS.completeSpace_coe
  dsimp only
  intro γ hγ hγvalue
  -- Kernel vectors give their own zero-output graph points, with no coordinate choice.
  have hker (x : E) : x ∈ D.ker ↔ (x, 0) ∈ D.graph := by
    constructor
    · intro hx
      obtain ⟨u, rfl, hu⟩ := D.mem_ker_iff.mp hx
      exact D.mem_graph_iff'.mpr ⟨u, Prod.ext rfl hu⟩
    · intro hx
      obtain ⟨u, hu⟩ := D.mem_graph_iff'.mp hx
      exact D.mem_ker_iff.mpr ⟨u, (congrArg Prod.fst hu).symm, congrArg Prod.snd hu⟩
  let i : D.ker ≃ₗ[ℂ] T.ker := {
    toFun := fun v ↦ ⟨⟨WithLp.toLp 2 (v.val, 0), (hker v.val).mp v.property⟩, rfl⟩
    invFun := fun v ↦ ⟨(WithLp.ofLp v.val.val).1, (hker _).mpr (by
      have hzero : (WithLp.ofLp v.val.val).2 = 0 := v.property
      have hv := v.val.property
      change ((WithLp.ofLp v.val.val).1, (WithLp.ofLp v.val.val).2) ∈ D.graph at hv
      rwa [hzero] at hv)⟩
    left_inv := fun _ ↦ rfl
    right_inv := by
      intro v
      apply Subtype.ext
      apply Subtype.ext
      apply WithLp.ofLp_injective
      exact Prod.ext rfl (show 0 = (WithLp.ofLp v.val.val).2 from v.property.symm)
    map_add' := by
      intro v w
      apply Subtype.ext
      apply Subtype.ext
      apply WithLp.ofLp_injective
      change (v.val + w.val, (0 : F)) = (v.val + w.val, 0 + 0)
      rw [add_zero]
    map_smul' := by
      intro c v
      apply Subtype.ext
      apply Subtype.ext
      apply WithLp.ofLp_injective
      change (c • v.val, (0 : F)) = (c • v.val, c • (0 : F))
      rw [smul_zero] }
  have hR : T.range = D.toFun.range := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨u, hu⟩ := D.mem_graph_iff'.mp z.property
      exact ⟨u, congrArg Prod.snd hu⟩
    · rintro ⟨u, rfl⟩
      exact ⟨⟨WithLp.toLp 2 (u.val, D u), D.mem_graph_iff'.mpr ⟨u, rfl⟩⟩, rfl⟩
  let q := Submodule.quotEquivOfEq D.toFun.range T.range hR.symm
  have hq (v : F) : q (D.toFun.range.mkQ v) = T.range.mkQ v := rfl
  let e' := e.trans i
  let f' := f.trans q
  have hT : T.IsFredholm := by
    apply (isFredholm_iff_closed_range_finite T).mpr
    exact ⟨hR ▸ hrange, Module.Finite.equiv e', Module.Finite.equiv f'⟩
  have hTg (g : G) : T.comp (γ g) = (τ g).comp T := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun z : WithLp 2 (E × F) ↦ (WithLp.ofLp z).2) (hγvalue g v)
  refine ⟨hTg, hT, ?_⟩
  apply equivariantFredholmIndex_eq_of_coordinates γ τ hγ hτ T hTg hT κ χ e' f'
  · intro g v
    apply Subtype.ext
    rw [hγvalue]
    apply WithLp.ofLp_injective
    change ((e (κ.representation g v)).val, 0) = (ρ g (e v).val, τ g 0)
    rw [he, map_zero]
  · -- The original range quotient is unchanged by passing to the graph domain.
    intro g v
    have hv : f'.symm (T.range.mkQ v) = f.symm (D.toFun.range.mkQ v) := by
      rw [← hq]
      change f.symm (q.symm (q (D.toFun.range.mkQ v))) = _
      rw [q.symm_apply_apply]
    rw [hv]
    change q (f (χ.representation g (f.symm (D.toFun.range.mkQ v)))) = _
    rw [hf, hq]

end AtiyahSinger
