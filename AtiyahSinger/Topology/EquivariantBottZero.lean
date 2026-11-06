/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinorWeights
public import AtiyahSinger.Topology.EquivariantBottRepresentation
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality
public import AtiyahSinger.Topology.EquivariantSupportPoint

/-!
# The original equivariant Bott map in dimension zero

Public module ID: M1762.

The zero-dimensional exterior symbol has its actual even vacuum line and zero
odd space. Its original induced exterior action is trivial, because every
original action map on the zero vector space is the identity. Tensoring on the
left by a finite representation therefore gives that full representation on
the even part. The right scalar unitor identifies this triple with the proper
pullback of the existing representation point triple.

The resulting comparison is an equality of the original additive maps on all
virtual representation classes. The already proved point coefficient
isomorphism and proper pullback along the unique homeomorphism then give
bijectivity of this original zero-dimensional Bott map. No positive-dimensional
Bott theorem, forgetful injectivity, or dimension-only comparison is used.

Sources: Atiyah--Singer I, section 2, p.494, for the point coefficient model,
and Spin Geometry, Appendix C, for the specified exterior symbol. The direct
comparison below is the zero-dimensional normalization on the project's
original equivariant support-triple presentation. An arbitrary topological
group is allowed; the supplied unitary certificate remains the original one.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  trivialTopology isFiniteRank_trivial tensorTopology isFiniteRank_tensor isFiniteRank_pullback

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local notation "V₀" => EuclideanSpace ℂ (Fin 0)

variable [DistribMulAction G V₀] [SMulCommClass G ℂ V₀] [ContinuousSMul G V₀]
  (hunitary : ∀ (g : G) (u v : V₀), inner ℂ (g • u) (g • v) = inner ℂ u v)

set_option backward.isDefEq.respectTransparency.types false in
/-- The original zero-dimensional Bott map is the transported full point coefficient map. -/
theorem equivariantBottLinearMap_zero_eq_representationPointKZeroPullback :
    let e := Homeomorph.homeomorphOfUnique V₀ PUnit.{1}
    let q : C(V₀, PUnit.{1}) := ⟨e, e.continuous⟩
    let hq : ∀ (g : G) (x : V₀), q (g • x) = g • q x :=
      fun _ _ ↦ Subsingleton.elim _ _
    (equivariantBottLinearMap hunitary).toAddMonoidHom =
      (equivariantSupportTripleKZeroPullback q hq e.isProperMap).comp
        representationPointKZero := by
  classical
  dsimp only
  let e := Homeomorph.homeomorphOfUnique V₀ PUnit.{1}
  let q : C(V₀, PUnit.{1}) := ⟨e, e.continuous⟩
  let hq : ∀ (g : G) (x : V₀), q (g • x) = g • q x :=
    fun _ _ ↦ Subsingleton.elim _ _
  let P (i : ZMod 2) := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V₀) i
  let (i : ZMod 2) := modelTopology (P i) (Bundle.Trivial V₀ (P i))
  let (i : ZMod 2) := isFiniteRank_model (P i) (Bundle.Trivial V₀ (P i))
  -- The empty exterior monomial gives the scalar line; no odd monomial exists.
  let I := {s : Finset (Fin 0) // (s.card : ZMod 2) = 0}
  let : Unique I :=
    { default := ⟨∅, by simp⟩
      uniq := fun s ↦ Subtype.ext (Subsingleton.elim _ _) }
  let d₀ : P 0 ≃ₗ[ℂ] ℂ := ((complexSpinorParityBasis 0 0).equivFun.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin 1 ↦ ℂ) (Equiv.ofUnique I (Fin 1)))).trans
      (LinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ))
  let J := {s : Finset (Fin 0) // (s.card : ZMod 2) = 1}
  let : IsEmpty J := ⟨fun s ↦ by
    have hs : s.val = ∅ := Subsingleton.elim _ _
    have h := s.property
    simp [hs] at h⟩
  let d₁ : P 1 ≃ₗ[ℂ] (Fin 0 → ℂ) := (complexSpinorParityBasis 0 1).equivFun.trans
    (LinearEquiv.piCongrLeft ℂ (fun _ : Fin 0 ↦ ℂ) (Equiv.equivOfIsEmpty J (Fin 0)))
  let : Subsingleton (P 1) := ⟨fun u v ↦ d₁.injective (Subsingleton.elim _ _)⟩
  -- This checks the actual algebra action, not merely the dimension of the even space.
  have haction (g : G) (i : ZMod 2) (v : P i) : exteriorParityAction g i v = v := by
    have hmap : ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V₀ g) =
        AlgHom.id ℂ (ExteriorAlgebra ℂ V₀) := by
      apply ExteriorAlgebra.hom_ext
      ext x
      change ExteriorAlgebra.map (DistribSMul.toLinearMap ℂ V₀ g)
        (ExteriorAlgebra.ι ℂ x) = ExteriorAlgebra.ι ℂ x
      rw [ExteriorAlgebra.map_apply_ι]
      exact congrArg (ExteriorAlgebra.ι ℂ) (Subsingleton.elim _ _)
    apply Subtype.ext
    exact AlgHom.congr_fun hmap v.val
  have hgen (ρ : FiniteContinuousRepresentation G) :
      equivariantBottLinearMap hunitary (finiteRepresentationClass ρ) =
        equivariantSupportTripleKZeroPullback q hq e.isProperMap
          (representationPointKZero (finiteRepresentationClass ρ)) := by
    let R := FiniteBundle.trivial V₀ ρ.dimension
    let E := FiniteBundle.ofFamily (Bundle.Trivial V₀ (P 0))
    let F := FiniteBundle.ofFamily (Bundle.Trivial V₀ (P 1))
    let Z := FiniteBundle.trivial V₀ 0
    let a := (equivariantExteriorBottTriple hunitary).tensorRepresentation ρ
    let b := (representationPointTriple ρ).pullback q hq e.isProperMap
    -- Insert the fixed vacuum on the right in the original finite-sum tensor topology.
    let c : (Fin ρ.dimension → ℂ) ⊗[ℂ] P 0 ≃ₗ[ℂ] (Fin ρ.dimension → ℂ) :=
      (TensorProduct.congr (LinearEquiv.refl ℂ _) d₀).trans (TensorProduct.rid ℂ _)
    have hc (v : Fin ρ.dimension → ℂ) : c.symm v = v ⊗ₜ[ℂ] d₀.symm 1 := rfl
    have hunit : Continuous (fun x : V₀ ↦
        (⟨x, d₀.symm 1⟩ : TotalSpace Unit E.Fiber)) := by
      let t := (unitTotalHomeomorph (P 0) E.Fiber).trans
        (Bundle.Trivial.homeomorphProd V₀ (P 0))
      exact t.symm.continuous.comp (continuous_id.prodMk continuous_const)
    have hins : Continuous (fun z : TotalSpace Unit R.Fiber ↦
        (⟨z.proj, c.symm z.snd⟩ : TotalSpace Unit (R.tensor E).Fiber)) := by
      let D := TotalSpace Unit (fun x : V₀ ↦
        (Fin 1 → R.Fiber x) × (Fin 1 → E.Fiber x))
      let : TopologicalSpace D := TopologicalSpace.induced
        (fun z : D ↦ (z.proj,
          (fun i : Fin 1 ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit R.Fiber)),
          (fun i : Fin 1 ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit E.Fiber)))) inferInstance
      let f (z : TotalSpace Unit R.Fiber) : D :=
        ⟨z.proj, (fun _ ↦ z.snd, fun _ ↦ d₀.symm 1)⟩
      have hf : Continuous f := by
        apply continuous_induced_rng.mpr
        exact continuous_proj.prodMk ((continuous_pi fun _ ↦ continuous_id).prodMk
          (continuous_pi fun _ ↦ hunit.comp continuous_proj))
      have hsum : Continuous (fun z : D ↦
          (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
            TotalSpace Unit (R.tensor E).Fiber)) :=
        continuous_iSup_rng (i := 1) continuous_coinduced_rng
      simpa only [Function.comp_def, f, Fin.sum_univ_one, hc] using hsum.comp hf
    let insert : Hom R.Fiber (R.tensor E).Fiber := ⟨fun _ ↦ c.symm.toLinearMap, hins⟩
    let u : Iso (R.tensor E).Fiber R.Fiber :=
      (insert.toIso (fun _ ↦ c.symm.bijective)).symm
    have hu (x : V₀) (v : (Fin ρ.dimension → ℂ) ⊗[ℂ] P 0) :
        u.linearEquiv x v = c v := by
      apply c.symm.injective
      exact (((insert.toIso (fun _ ↦ c.symm.bijective)).linearEquiv x).apply_symm_apply v).trans
        (c.symm_apply_apply v).symm
    -- The odd tensor space is zero; the original zero target has its standard topology.
    have hz (v : (Fin ρ.dimension → ℂ) ⊗[ℂ] P 1) : v = 0 := by
      induction v using TensorProduct.inductionOn with
      | tmul v w =>
        rw [show w = 0 from Subsingleton.elim _ _, TensorProduct.tmul_zero]
      | add v w hv hw => rw [hv, hw, add_zero]
    let zmap : Hom (R.tensor F).Fiber Z.Fiber :=
      { linearMap _ := 0
        continuous_total := continuous_induced_rng.mpr
          (continuous_proj.prodMk continuous_const) }
    let v : Iso (R.tensor F).Fiber Z.Fiber := zmap.toIso (fun _ ↦
      ⟨fun s t _ ↦ (hz s).trans (hz t).symm,
        fun t ↦ ⟨0, by exact Subsingleton.elim _ _⟩⟩)
    -- The chosen pullback trivializations preserve every representation coordinate.
    let pu := pullbackTrivialIso q ρ.dimension
    let pv := pullbackTrivialIso q 0
    have hpu (x : V₀) (w : Fin ρ.dimension → ℂ) :
        (pu.linearEquiv x).symm w = w := by
      have h := pu.linearEquiv x |>.apply_symm_apply w
      rw [pullbackTrivialIso_apply] at h
      exact h
    let U : Iso a.1.source.Fiber b.1.source.Fiber := u.trans pu.symm
    let W : Iso a.1.target.Fiber b.1.target.Fiber := v.trans pv.symm
    have hU : U.IsEquivariant a.2.sourceAction b.2.sourceAction := by
      intro g x w
      have hm : (U.linearEquiv (g • x)).toLinearMap.comp
            (a.2.sourceAction.linearMap g x) =
          (b.2.sourceAction.linearMap g x).comp (U.linearEquiv x).toLinearMap := by
        apply TensorProduct.ext'
        intro r s
        change (pu.linearEquiv (g • x)).symm
            (u.linearEquiv (g • x)
              ((ρ.representation g r) ⊗ₜ[ℂ] exteriorParityAction g 0 s)) =
          ρ.representation g ((pu.linearEquiv x).symm (u.linearEquiv x (r ⊗ₜ[ℂ] s)))
        rw [hpu, hpu, hu, hu, haction]
        change d₀ s • ρ.representation g r = ρ.representation g (d₀ s • r)
        exact (map_smul (ρ.representation g) (d₀ s) r).symm
      exact DFunLike.congr_fun hm w
    have hW : W.IsEquivariant a.2.targetAction b.2.targetAction := by
      intro g x w
      funext i
      exact Fin.elim0 i
    have hclass : a.kZeroClass = b.kZeroClass := by
      apply equivariantSupportTripleKZero_generator_relations.1
      refine ⟨Set.univ, isCompact_univ, fun _ _ ↦ Iff.rfl,
        Set.subset_univ _, Set.subset_univ _, U, W, hU, hW, ?_⟩
      intro x
      exact (x.property (Set.mem_univ x.val)).elim
    change equivariantSupportRepresentationAction (finiteRepresentationClass ρ)
      (equivariantExteriorBottTriple hunitary).kZeroClass = _
    rw [equivariantSupportRepresentationAction_finiteClass,
      representationPointKZero_finiteClass, equivariantSupportTripleKZeroPullback_apply]
    exact hclass
  -- The two additive maps agree on the original generators, hence on all virtual classes.
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  exact hgen

/-- The original equivariant Bott map on the zero vector space is bijective. -/
theorem equivariantBottLinearMap_zero_bijective :
    Function.Bijective (equivariantBottLinearMap hunitary) := by
  let e := Homeomorph.homeomorphOfUnique V₀ PUnit.{1}
  let q : C(V₀, PUnit.{1}) := ⟨e, e.continuous⟩
  let p : C(PUnit.{1}, V₀) := ⟨e.symm, e.symm.continuous⟩
  let hq : ∀ (g : G) (x : V₀), q (g • x) = g • q x :=
    fun _ _ ↦ Subsingleton.elim _ _
  let hp : ∀ (g : G) (x : PUnit.{1}), p (g • x) = g • p x :=
    fun _ _ ↦ Subsingleton.elim _ _
  let Q := equivariantSupportTripleKZeroPullback q hq e.isProperMap
  let P := equivariantSupportTripleKZeroPullback p hp e.symm.isProperMap
  -- Both inverse identities are the original proper pullback composition identities.
  have hqp : q.comp p = ContinuousMap.id PUnit.{1} := by
    apply ContinuousMap.ext
    intro x
    exact e.apply_symm_apply x
  have hpq : p.comp q = ContinuousMap.id V₀ := by
    apply ContinuousMap.ext
    intro x
    exact e.symm_apply_apply x
  have hPQ : P.comp Q = AddMonoidHom.id (EquivariantSupportTripleKZero G PUnit.{1}) := by
    have h := equivariantSupportTripleKZeroPullback_comp q p hq hp
      e.isProperMap e.symm.isProperMap
    simpa only [hqp, equivariantSupportTripleKZeroPullback_id] using h.symm
  have hQP : Q.comp P = AddMonoidHom.id (EquivariantSupportTripleKZero G V₀) := by
    have h := equivariantSupportTripleKZeroPullback_comp p q hp hq
      e.symm.isProperMap e.isProperMap
    simpa only [hpq, equivariantSupportTripleKZeroPullback_id] using h.symm
  have hQ : Function.Bijective Q :=
    ⟨Function.LeftInverse.injective (fun x ↦ DFunLike.congr_fun hPQ x),
      Function.RightInverse.surjective (fun x ↦ DFunLike.congr_fun hQP x)⟩
  -- Transport the full representation coefficient bijection along this same homeomorphism.
  have hmap := equivariantBottLinearMap_zero_eq_representationPointKZeroPullback hunitary
  change (equivariantBottLinearMap hunitary).toAddMonoidHom =
    Q.comp representationPointKZero at hmap
  change Function.Bijective (equivariantBottLinearMap hunitary).toAddMonoidHom
  rw [hmap]
  exact hQ.comp representationPointKZero_bijective

end AtiyahSinger
