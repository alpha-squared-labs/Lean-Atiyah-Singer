/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantFredholmIndex

/-!
# Operations on the actual equivariant Fredholm index

Public module ID: M0528.

Direct sums and continuous equivariant changes of coordinates preserve the
actual kernel and quotient representations. The corresponding statements do
not need unitary actions. Compact perturbations and composition are treated
for fixed unitary Hilbert actions, using the existing norm-path stability.

The product action below is the usual block action on the native normed
product. In particular, no inner product is installed on its supremum norm.
Every index is evaluated on the original operator and its actual finite
kernel and quotient-cokernel; no dimension-only replacement is made.

Sources: SG III.5 Lemma 5.1, III.7 equation (7.5) and its projection proof,
and III.9 Proposition 9.4 and its composition note. The direct-sum and
coordinate-invariance formulations spell out standard representation maps.
The normed direct-sum and coordinate-invariance formulas, as well as the
Hilbert compact-perturbation and composition formulas, are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ContinuousLinearMap

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Normed

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [NormedAddCommGroup F'] [NormedSpace ℂ F']

/-- The usual block action on the native product of two normed representation spaces. -/
def continuousRepresentationProd
    (ρ : ContRepresentation ℂ G E) (ρ' : ContRepresentation ℂ G E') :
    ContRepresentation ℂ G (E × E') :=
  .ofMonoidHom
    { toFun := fun g ↦ (ρ g).prodMap (ρ' g)
      map_one' := by
        ext x <;> simp
      map_mul' := by
        intro g h
        ext x <;> simp [map_mul] }

/-- Direct sums of equivariant Fredholm operators have the sum of their full indices. -/
theorem equivariantFredholmIndex_prod
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (ρ' : ContRepresentation ℂ G E') (σ' : ContRepresentation ℂ G F')
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hρ' : Continuous (fun p : G × E' ↦ ρ' p.1 p.2))
    (hσ' : Continuous (fun p : G × F' ↦ σ' p.1 p.2))
    (T : E →L[ℂ] F) (T' : E' →L[ℂ] F')
    (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hT'g : ∀ g : G, T'.comp (ρ' g) = (σ' g).comp T')
    (hT : T.IsFredholm) (hT' : T'.IsFredholm) :
    ∃ hTT' : (T.prodMap T').IsFredholm,
      equivariantFredholmIndex (continuousRepresentationProd ρ ρ')
          (continuousRepresentationProd σ σ')
          ((hρ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
            (hρ'.comp (continuous_fst.prodMk continuous_snd.snd)))
          ((hσ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
            (hσ'.comp (continuous_fst.prodMk continuous_snd.snd)))
          (T.prodMap T') (by
            intro g
            apply ContinuousLinearMap.ext
            intro x
            exact Prod.ext
              (congrArg (fun A : E →L[ℂ] F ↦ A x.1) (hTg g))
              (congrArg (fun A : E' →L[ℂ] F' ↦ A x.2) (hT'g g))) hTT' =
        equivariantFredholmIndex ρ σ hρ hσ T hTg hT +
          equivariantFredholmIndex ρ' σ' hρ' hσ' T' hT'g hT' := by
  /- Stage 1: the block of the original continuous quasi-inverses has two
  finite-rank defects, each factoring through a product of the original
  finite-dimensional defect ranges. This proves Fredholmness in the native
  product topology. The actual block kernel is the product of the kernels,
  and its quotient-cokernel identifies with the product of the quotients.
  Stage 2: the kernel and quotient identifications intertwine the specified
  block actions. They are continuous linear equivalences on the actual
  carriers, so their finite representation classes are the corresponding
  direct sums. Apply the defining Grothendieck direct-sum relation through
  finite coordinates, then regroup the two kernel-minus-cokernel differences.
  No splitting of an arbitrary exact sequence, invariant metric, or Hilbert
  structure on the supremum-norm product is required. -/
  classical
  -- The block of the original quasi-inverses has finite-rank defects in both orders.
  have hU : (T.prodMap T').IsFredholm := by
    obtain ⟨S, hS⟩ := hT.exists_isQuasiInverse
    obtain ⟨S', hS'⟩ := hT'.exists_isQuasiInverse
    apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse (v := S.prodMap S')
    constructor
    · apply LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr
      have hd := LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.1
      have hd' := LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS'.1
      let d := S.toLinearMap.comp T.toLinearMap - LinearMap.id
      let d' := S'.toLinearMap.comp T'.toLinearMap - LinearMap.id
      let : FiniteDimensional ℂ d.range := Module.Finite.of_fg hd
      let : FiniteDimensional ℂ d'.range := Module.Finite.of_fg hd'
      let a := d.rangeRestrict.prodMap d'.rangeRestrict
      let b := d.range.subtype.prodMap d'.range.subtype
      exact (LinearMap.HasFiniteRange.of_finite_dom (f := b)).comp_right a
    · apply LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr
      have hd := LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.2
      have hd' := LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS'.2
      let d := T.toLinearMap.comp S.toLinearMap - LinearMap.id
      let d' := T'.toLinearMap.comp S'.toLinearMap - LinearMap.id
      let : FiniteDimensional ℂ d.range := Module.Finite.of_fg hd
      let : FiniteDimensional ℂ d'.range := Module.Finite.of_fg hd'
      let a := d.rangeRestrict.prodMap d'.rangeRestrict
      let b := d.range.subtype.prodMap d'.range.subtype
      exact (LinearMap.HasFiniteRange.of_finite_dom (f := b)).comp_right a
  refine ⟨hU, ?_⟩
  -- All three indices use their actual kernels and native quotient norms.
  let U := T.prodMap T'
  let ρU := continuousRepresentationProd ρ ρ'
  let σU := continuousRepresentationProd σ σ'
  have hUg (g : G) : U.comp (ρU g) = (σU g).comp U := by
    apply ContinuousLinearMap.ext
    intro x
    exact Prod.ext
      (congrArg (fun A : E →L[ℂ] F ↦ A x.1) (hTg g))
      (congrArg (fun A : E' →L[ℂ] F' ↦ A x.2) (hT'g g))
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ T'.ker := hT'.finite_ker
  let : FiniteDimensional ℂ U.ker := hU.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : FiniteDimensional ℂ (F' ⧸ T'.range) := hT'.finite_coker
  let : FiniteDimensional ℂ ((F × F') ⧸ U.range) := hU.finite_coker
  let : IsClosed (T.range : Set F) := hT.isClosed_range
  let : IsClosed (T'.range : Set F') := hT'.isClosed_range
  let : IsClosed (U.range : Set (F × F')) := hU.isClosed_range
  let κ := equivariantKernelRepresentation ρ σ T hTg
  let κ' := equivariantKernelRepresentation ρ' σ' T' hT'g
  let χ := equivariantCokernelRepresentation ρ σ T hTg
  let χ' := equivariantCokernelRepresentation ρ' σ' T' hT'g
  let hκ := continuous_equivariantKernelRepresentation ρ σ T hTg hρ
  let hκ' := continuous_equivariantKernelRepresentation ρ' σ' T' hT'g hρ'
  let hχ := continuous_equivariantCokernelRepresentation ρ σ T hTg hσ
  let hχ' := continuous_equivariantCokernelRepresentation ρ' σ' T' hT'g hσ'
  let hκp := (hκ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
    (hκ'.comp (continuous_fst.prodMk continuous_snd.snd))
  let hχp := (hχ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
    (hχ'.comp (continuous_fst.prodMk continuous_snd.snd))
  -- Restriction of the block action gives the product of the two original kernel actions.
  let k : U.ker ≃ₗ[ℂ] T.ker × T'.ker :=
    { toFun := fun x ↦ (⟨x.val.1, congrArg Prod.fst x.property⟩,
        ⟨x.val.2, congrArg Prod.snd x.property⟩)
      invFun := fun x ↦ ⟨(x.1.val, x.2.val), Prod.ext x.1.property x.2.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hk : ContRepresentation.Equiv
      (equivariantKernelRepresentation ρU σU U hUg)
      (continuousRepresentationProd κ κ') := by
    refine ContRepresentation.Equiv.mk k.toContinuousLinearEquiv ?_
    intro g
    rfl
  -- The product quotient map has kernel the original block range, before taking quotients.
  let q : (F × F') →ₗ[ℂ] (F ⧸ T.range) × (F' ⧸ T'.range) :=
    T.range.mkQ.prodMap T'.range.mkQ
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := T.range.mkQ_surjective y.1
    obtain ⟨x', hx'⟩ := T'.range.mkQ_surjective y.2
    exact ⟨(x, x'), Prod.ext hx hx'⟩
  have hqker : q.ker = U.range := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero T.range).mp (congrArg Prod.fst hy)
      obtain ⟨x', hx'⟩ := (Submodule.Quotient.mk_eq_zero T'.range).mp
        (congrArg Prod.snd hy)
      exact ⟨(x, x'), Prod.ext hx hx'⟩
    · rintro ⟨x, rfl⟩
      exact Prod.ext
        ((Submodule.Quotient.mk_eq_zero T.range).mpr ⟨x.1, rfl⟩)
        ((Submodule.Quotient.mk_eq_zero T'.range).mpr ⟨x.2, rfl⟩)
  let c : ((F × F') ⧸ U.range) ≃ₗ[ℂ] (F ⧸ T.range) × (F' ⧸ T'.range) :=
    (Submodule.quotEquivOfEq _ _ hqker.symm).trans (q.quotKerEquivOfSurjective hq)
  have hc_apply (y : F × F') : c (U.range.mkQ y) = q y := rfl
  have hc : ContRepresentation.Equiv
      (equivariantCokernelRepresentation ρU σU U hUg)
      (continuousRepresentationProd χ χ') := by
    refine ContRepresentation.Equiv.mk c.toContinuousLinearEquiv ?_
    intro g
    apply ContinuousLinearMap.ext
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change c (U.range.mkQ (σU g y)) =
        continuousRepresentationProd χ χ' g (c (U.range.mkQ y))
      rw [hc_apply, hc_apply]
      rfl
  -- Compare finite product coordinates with the specified ordered direct-sum coordinates.
  have hclassK : representationClass (continuousRepresentationProd κ κ') hκp =
      representationClass κ hκ + representationClass κ' hκ' := by
    let e₁ : T.ker ≃L[ℂ] (Fin (Module.finrank ℂ T.ker) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let e₂ : T'.ker ≃L[ℂ] (Fin (Module.finrank ℂ T'.ker) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let ν := FiniteContinuousRepresentation.ofEquiv κ hκ e₁
    let ν' := FiniteContinuousRepresentation.ofEquiv κ' hκ' e₂
    let e : (Fin (ν.dimension + ν'.dimension) → ℂ) ≃L[ℂ]
        (Fin ν.dimension → ℂ) × (Fin ν'.dimension → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ
        (fun _ : Fin ν.dimension ⊕ Fin ν'.dimension ↦ ℂ) finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ
          (Fin ν.dimension) (Fin ν'.dimension) (fun _ ↦ ℂ))
    let a := ((e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv).trans
      e.symm.toLinearEquiv).toContinuousLinearEquiv
    rw [representationClass_ofEquiv (continuousRepresentationProd κ κ') hκp a,
      representationClass_ofEquiv κ hκ e₁, representationClass_ofEquiv κ' hκ' e₂,
      ← finiteRepresentationClass_directSum]
    apply finiteRepresentationClass_eq_of_isEquivalent
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
    intro g
    rfl
  have hclassQ : representationClass (continuousRepresentationProd χ χ') hχp =
      representationClass χ hχ + representationClass χ' hχ' := by
    let e₁ : (F ⧸ T.range) ≃L[ℂ] (Fin (Module.finrank ℂ (F ⧸ T.range)) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let e₂ : (F' ⧸ T'.range) ≃L[ℂ] (Fin (Module.finrank ℂ (F' ⧸ T'.range)) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let ν := FiniteContinuousRepresentation.ofEquiv χ hχ e₁
    let ν' := FiniteContinuousRepresentation.ofEquiv χ' hχ' e₂
    let e : (Fin (ν.dimension + ν'.dimension) → ℂ) ≃L[ℂ]
        (Fin ν.dimension → ℂ) × (Fin ν'.dimension → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ
        (fun _ : Fin ν.dimension ⊕ Fin ν'.dimension ↦ ℂ) finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ
          (Fin ν.dimension) (Fin ν'.dimension) (fun _ ↦ ℂ))
    let a := ((e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv).trans
      e.symm.toLinearEquiv).toContinuousLinearEquiv
    rw [representationClass_ofEquiv (continuousRepresentationProd χ χ') hχp a,
      representationClass_ofEquiv χ hχ e₁, representationClass_ofEquiv χ' hχ' e₂,
      ← finiteRepresentationClass_directSum]
    apply finiteRepresentationClass_eq_of_isEquivalent
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
    intro g
    rfl
  -- The same kernel and quotient identifications give the two summands of the block index.
  have hkclass := representationClass_eq_of_equiv _ _
    (continuous_equivariantKernelRepresentation ρU σU U hUg
      ((hρ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
        (hρ'.comp (continuous_fst.prodMk continuous_snd.snd)))) hκp hk
  have hcclass := representationClass_eq_of_equiv _ _
    (continuous_equivariantCokernelRepresentation ρU σU U hUg
      ((hσ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
        (hσ'.comp (continuous_fst.prodMk continuous_snd.snd)))) hχp hc
  unfold equivariantFredholmIndex
  change representationClass _ _ - representationClass _ _ =
    representationClass κ hκ - representationClass χ hχ +
      (representationClass κ' hκ' - representationClass χ' hχ')
  rw [hkclass, hcclass, hclassK, hclassQ]
  abel

/-- Equivariant continuous linear coordinate equivalences preserve the actual index. -/
theorem equivariantFredholmIndex_eq_of_equiv
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (ρ' : ContRepresentation ℂ G E') (σ' : ContRepresentation ℂ G F')
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hρ' : Continuous (fun p : G × E' ↦ ρ' p.1 p.2))
    (hσ' : Continuous (fun p : G × F' ↦ σ' p.1 p.2))
    (u : ContRepresentation.Equiv ρ ρ') (v : ContRepresentation.Equiv σ σ')
    (T : E →L[ℂ] F) (T' : E' →L[ℂ] F')
    (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hT'g : ∀ g : G, T'.comp (ρ' g) = (σ' g).comp T')
    (hsquare : T'.comp u.toContinuousLinearEquiv.toContinuousLinearMap =
      v.toContinuousLinearEquiv.toContinuousLinearMap.comp T)
    (hT : T.IsFredholm) (hT' : T'.IsFredholm) :
    equivariantFredholmIndex ρ σ hρ hσ T hTg hT =
      equivariantFredholmIndex ρ' σ' hρ' hσ' T' hT'g hT' := by
  /- Stage 1: restrict u and its inverse to the original kernels, using
  the commuting square and injectivity of v. These are inverse continuous
  linear intertwiners. The same square identifies v(range T) with range T'.
  Stage 2: v and its inverse descend to the actual quotient-cokernels.
  The native quotient topology gives continuity, and equivariance descends
  from v. Thus both finite representation terms agree by actual isomorphisms.
  Substitute these equalities in the two index definitions. No isometry,
  unitarity, completeness, or compactness of the group is needed. -/
  -- The commuting square restricts the original coordinate map to the actual kernels.
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ T'.ker := hT'.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : FiniteDimensional ℂ (F' ⧸ T'.range) := hT'.finite_coker
  let : IsClosed (T.range : Set F) := hT.isClosed_range
  let : IsClosed (T'.range : Set F') := hT'.isClosed_range
  have hs (x : E) : T' (u.toContinuousLinearEquiv x) =
      v.toContinuousLinearEquiv (T x) :=
    congrArg (fun A : E →L[ℂ] F' ↦ A x) hsquare
  let k : T.ker ≃ₗ[ℂ] T'.ker :=
    { toFun := fun x ↦ ⟨u x, by
        change T' (u.toContinuousLinearEquiv x.val) = 0
        have hx : T x.val = 0 := x.property
        rw [hs, hx, map_zero]⟩
      invFun := fun y ↦ ⟨u.toContinuousLinearEquiv.symm y, by
        apply v.toContinuousLinearEquiv.injective
        change v.toContinuousLinearEquiv (T (u.toContinuousLinearEquiv.symm y.val)) =
          v.toContinuousLinearEquiv 0
        rw [← hs, u.toContinuousLinearEquiv.apply_symm_apply, map_zero]
        exact y.property⟩
      left_inv := fun x ↦ Subtype.ext (u.toContinuousLinearEquiv.symm_apply_apply x)
      right_inv := fun y ↦ Subtype.ext (u.toContinuousLinearEquiv.apply_symm_apply y)
      map_add' := fun x y ↦ Subtype.ext (map_add u.toContinuousLinearEquiv x.val y.val)
      map_smul' := fun a x ↦ Subtype.ext (map_smul u.toContinuousLinearEquiv a x.val) }
  have hk : ContRepresentation.Equiv
      (equivariantKernelRepresentation ρ σ T hTg)
      (equivariantKernelRepresentation ρ' σ' T' hT'g) := by
    refine ContRepresentation.Equiv.mk k.toContinuousLinearEquiv ?_
    intro g
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (u.isIntertwining g) x.val
  -- The same square identifies ranges, so the original target map descends to quotients.
  have hr : T.range.map v.toContinuousLinearEquiv.toLinearEquiv.toLinearMap = T'.range := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨u x, hs x⟩
    · rintro ⟨x, rfl⟩
      refine ⟨T (u.toContinuousLinearEquiv.symm x), ⟨_, rfl⟩, ?_⟩
      change v.toContinuousLinearEquiv (T (u.toContinuousLinearEquiv.symm x)) = T' x
      rw [← hs, u.toContinuousLinearEquiv.apply_symm_apply]
  let c : (F ⧸ T.range) ≃ₗ[ℂ] (F' ⧸ T'.range) :=
    Submodule.Quotient.equiv T.range T'.range v.toContinuousLinearEquiv.toLinearEquiv hr
  have hc_apply (y : F) : c (T.range.mkQ y) = T'.range.mkQ (v y) := rfl
  have hc : ContRepresentation.Equiv
      (equivariantCokernelRepresentation ρ σ T hTg)
      (equivariantCokernelRepresentation ρ' σ' T' hT'g) := by
    refine ContRepresentation.Equiv.mk c.toContinuousLinearEquiv ?_
    intro g
    apply ContinuousLinearMap.ext
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change c (T.range.mkQ (σ g y)) =
        equivariantCokernelRepresentation ρ' σ' T' hT'g g (c (T.range.mkQ y))
      rw [hc_apply, hc_apply]
      change T'.range.mkQ (v (σ g y)) = T'.range.mkQ (σ' g (v y))
      exact congrArg T'.range.mkQ (DFunLike.congr_fun (v.isIntertwining g) y)
  -- Both classes are transported by those actual intertwiners before taking their difference.
  unfold equivariantFredholmIndex
  congr 1
  · exact representationClass_eq_of_equiv _ _ _ _ hk
  · exact representationClass_eq_of_equiv _ _ _ _ hc

end Normed

section Hilbert

variable {E F H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An equivariant compact perturbation preserves the full virtual representation index. -/
theorem equivariantFredholmIndex_add_compact
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hρu : ∀ g : G, Isometry (ρ g)) (hσu : ∀ g : G, Isometry (σ g))
    (T K : E →L[ℂ] F)
    (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hKg : ∀ g : G, K.comp (ρ g) = (σ g).comp K)
    (hT : T.IsFredholm) (hK : IsCompactOperator K) :
    equivariantFredholmIndex ρ σ hρ hσ (T + K) (by
        intro g
        simp only [add_comp, comp_add, hTg g, hKg g])
        (isFredholm_add_compact T K hT hK) =
      equivariantFredholmIndex ρ σ hρ hσ T hTg hT := by
  /- Stage 1: use the actual affine path T+tK in the bounded-operator norm.
  Every real scalar multiple of K remains compact. The same parametrix for T
  is an inverse modulo compact operators along the path, as in SG III.5.1,
  so all path members are Fredholm. Equivariance of K as well as T keeps
  the path between the same fixed jointly continuous unitary actions.
  Stage 2: apply representation-valued norm-path invariance, then identify
  the endpoints with the original T and T+K. This equality takes place in
  the representation group before applying dimension. Compactness of G
  and averaging are not needed once the unitary actions are supplied. -/
  -- The affine norm path retains the same actions and is Fredholm at every parameter.
  let γ : Path T (T + K) :=
    { toFun := fun t ↦ T + (t : ℝ) • K
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  have hγg (t : unitInterval) (g : G) : (γ t).comp (ρ g) = (σ g).comp (γ t) := by
    change (T + (t : ℝ) • K).comp (ρ g) = (σ g).comp (T + (t : ℝ) • K)
    simp only [add_comp, comp_add, smul_comp, comp_smul, hTg g, hKg g]
  have hγ (t : unitInterval) : (γ t).IsFredholm :=
    isFredholm_add_compact T ((t : ℝ) • K) hT (hK.smul (t : ℝ))
  -- Apply representation-valued path invariance at both endpoints.
  exact (equivariantFredholmIndex_eq_of_path ρ σ hρ hσ hρu hσu
    γ hγg hγ hTg (by
      intro g
      simp only [add_comp, comp_add, hTg g, hKg g])
    hT (isFredholm_add_compact T K hT hK)).symm

/-- Composition adds the full indices for fixed unitary Hilbert representations. -/
theorem equivariantFredholmIndex_comp
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (τ : ContRepresentation ℂ G H)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hτ : Continuous (fun p : G × H ↦ τ p.1 p.2))
    (hρu : ∀ g : G, Isometry (ρ g)) (hσu : ∀ g : G, Isometry (σ g))
    (hτu : ∀ g : G, Isometry (τ g))
    (T : E →L[ℂ] F) (S : F →L[ℂ] H)
    (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hSg : ∀ g : G, S.comp (σ g) = (τ g).comp S)
    (hT : T.IsFredholm) (hS : S.IsFredholm) :
    equivariantFredholmIndex ρ τ hρ hτ (S.comp T) (by
        intro g
        rw [comp_assoc, hTg g, ← comp_assoc, hSg g, comp_assoc]) (hS.comp hT) =
      equivariantFredholmIndex ρ σ hρ hσ T hTg hT +
        equivariantFredholmIndex σ τ hσ hτ S hSg hS := by
  /- Follow SG's projection of T away from ker S. The finite-rank correction leaves
  its index unchanged and makes its kernel equal to ker(S ∘ T). On adjoint kernels,
  the restricted S adjoint has kernel ker(S adjoint) and quotient-cokernel ker S.
  Their actual equivariant identifications and finite-dimensional normalization
  give the required class cancellation, without nonsplit exact-sequence relations. -/
  classical
  -- The projection onto the original finite kernel intertwines the same middle action.
  let : FiniteDimensional ℂ S.ker := hS.finite_ker
  let κ := equivariantKernelRepresentation σ τ S hSg
  let hκ := continuous_equivariantKernelRepresentation σ τ S hSg hσ
  have hκu (g : G) : Isometry (κ g) := by
    intro x y
    exact hσu g x.val y.val
  have hinc (g : G) : S.ker.subtypeL.comp (κ g) = (σ g).comp S.ker.subtypeL := rfl
  have hp (g : G) : S.ker.orthogonalProjectionOnto.comp (σ g) =
      (κ g).comp S.ker.orthogonalProjectionOnto := by
    simpa only [Submodule.adjoint_subtypeL] using
      adjoint_intertwines_of_isometry κ σ hκu hσu S.ker.subtypeL hinc g
  -- Subtract the finite-rank kernel component; compact invariance retains the original index.
  let D : E →L[ℂ] F := -(S.ker.subtypeL.comp (S.ker.orthogonalProjectionOnto.comp T))
  let V : E →L[ℂ] F := T + D
  have hDg (g : G) : D.comp (ρ g) = (σ g).comp D := by
    ext x
    change -(S.ker.orthogonalProjectionOnto (T (ρ g x)) : F) =
      σ g (-(S.ker.orthogonalProjectionOnto (T x) : F))
    have hTx : T (ρ g x) = σ g (T x) := DFunLike.congr_fun (hTg g) x
    rw [map_neg, hTx]
    exact congrArg (fun k : S.ker ↦ -(k : F)) (DFunLike.congr_fun (hp g) (T x))
  have hVg (g : G) : V.comp (ρ g) = (σ g).comp V := by
    simp only [V, add_comp, comp_add, hTg g, hDg g]
  have hD : IsCompactOperator D :=
    ((isCompactOperator_of_locallyCompactSpace_rng S.ker.subtypeL).comp_clm
      (S.ker.orthogonalProjectionOnto.comp T)).neg
  have hV : V.IsFredholm := isFredholm_add_compact T D hT hD
  have hVi := equivariantFredholmIndex_add_compact ρ σ hρ hσ hρu hσu T D hTg hDg hT hD
  have hV_apply (x : E) : V x = T x - (S.ker.orthogonalProjectionOnto (T x) : F) := by
    simp [V, D, sub_eq_add_neg]
  -- The projected operator has the same composite and exactly the composite kernel.
  have hSV : S.comp V = S.comp T := by
    ext x
    change S (V x) = S (T x)
    have hSk : S (S.ker.orthogonalProjectionOnto (T x) : F) = 0 :=
      (S.ker.orthogonalProjectionOnto (T x)).property
    rw [hV_apply, map_sub, hSk, sub_zero]
  let U : E →L[ℂ] H := S.comp T
  have hU : U.IsFredholm := hS.comp hT
  have hUg (g : G) : U.comp (ρ g) = (τ g).comp U := by
    dsimp [U]
    rw [comp_assoc, hTg g, ← comp_assoc, hSg g, comp_assoc]
  have hker : V.ker = U.ker := by
    ext x
    constructor
    · intro hx
      change U x = 0
      change V x = 0 at hx
      change (S.comp T) x = 0
      rw [← hSV, comp_apply, hx, map_zero]
    · intro hx
      change V x = 0
      rw [hV_apply]
      have hxS : T x ∈ S.ker := hx
      exact sub_eq_zero.mpr (congrArg Subtype.val
        (S.ker.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T x, hxS⟩)).symm
  have hVSa : V.adjoint.comp S.adjoint = U.adjoint := by
    rw [← adjoint_comp, hSV]
  have hVad (y : F) : V.adjoint y =
      T.adjoint (y - (S.ker.orthogonalProjectionOnto y : F)) := by
    simp [V, D, adjoint_comp, Submodule.adjoint_subtypeL,
      Submodule.adjoint_orthogonalProjectionOnto, sub_eq_add_neg]
  have hVkill (k : S.ker) : V.adjoint k = 0 := by
    rw [hVad, S.ker.orthogonalProjectionOnto_mem_subspace_eq_self, sub_self, map_zero]
  let : FiniteDimensional ℂ U.adjoint.ker := (isFredholm_adjoint U hU).finite_ker
  let : FiniteDimensional ℂ V.adjoint.ker := (isFredholm_adjoint V hV).finite_ker
  -- Restrict the actual adjoint to the finite defects; projection realizes its cokernel.
  let R : U.adjoint.ker →L[ℂ] V.adjoint.ker :=
    (S.adjoint.comp U.adjoint.ker.subtypeL).codRestrict V.adjoint.ker (by
      intro y
      change V.adjoint (S.adjoint y.val) = 0
      rw [← comp_apply, hVSa]
      exact y.property)
  let q : V.adjoint.ker →L[ℂ] S.ker :=
    S.ker.orthogonalProjectionOnto.comp V.adjoint.ker.subtypeL
  have hqsurj : Function.Surjective q := by
    intro k
    exact ⟨⟨k.val, hVkill k⟩, S.ker.orthogonalProjectionOnto_mem_subspace_eq_self k⟩
  -- Closed range identifies the complement of ker S with range(S adjoint).
  have hqker : q.ker = R.range := by
    ext y
    constructor
    · intro hy
      have hyorth : y.val ∈ S.kerᗮ :=
        (S.ker.orthogonalProjectionOnto_eq_zero_iff).mp hy
      rw [S.orthogonal_ker,
        (isFredholm_adjoint S hS).isClosed_range.submodule_topologicalClosure_eq] at hyorth
      obtain ⟨z, hz⟩ := hyorth
      change S.adjoint z = y.val at hz
      have hzU : z ∈ U.adjoint.ker := by
        change U.adjoint z = 0
        rw [← hVSa, comp_apply, hz]
        exact y.property
      exact ⟨⟨z, hzU⟩, Subtype.ext hz⟩
    · rintro ⟨z, rfl⟩
      change S.ker.orthogonalProjectionOnto (S.adjoint z.val) = 0
      apply S.ker.orthogonalProjectionOnto_eq_zero_iff.mpr
      rw [S.orthogonal_ker]
      exact S.adjoint.range.le_topologicalClosure ⟨z.val, rfl⟩
  -- Every finite defect carries the action induced by the same original unitary actions.
  let hSag := adjoint_intertwines_of_isometry σ τ hσu hτu S hSg
  let hVag := adjoint_intertwines_of_isometry ρ σ hρu hσu V hVg
  let hUag := adjoint_intertwines_of_isometry ρ τ hρu hτu U hUg
  let ξ := equivariantKernelRepresentation τ ρ U.adjoint hUag
  let η := equivariantKernelRepresentation σ ρ V.adjoint hVag
  let χ := equivariantKernelRepresentation τ σ S.adjoint hSag
  let hξ := continuous_equivariantKernelRepresentation τ ρ U.adjoint hUag hτ
  let hη := continuous_equivariantKernelRepresentation σ ρ V.adjoint hVag hσ
  let hχ := continuous_equivariantKernelRepresentation τ σ S.adjoint hSag hτ
  have hξu (g : G) : Isometry (ξ g) := by
    intro x y
    exact hτu g x.val y.val
  have hηu (g : G) : Isometry (η g) := by
    intro x y
    exact hσu g x.val y.val
  have hRg (g : G) : R.comp (ξ g) = (η g).comp R := by
    apply ContinuousLinearMap.ext
    intro y
    apply Subtype.ext
    exact DFunLike.congr_fun (hSag g) y.val
  have hR : R.IsFredholm := by
    apply (isFredholm_iff_closed_range_finite R).mpr
    exact ⟨R.range.closed_of_finiteDimensional, inferInstance, inferInstance⟩
  let : FiniteDimensional ℂ R.ker := hR.finite_ker
  let : FiniteDimensional ℂ S.adjoint.ker := (isFredholm_adjoint S hS).finite_ker
  let : FiniteDimensional ℂ (V.adjoint.ker ⧸ R.range) := hR.finite_coker
  let : IsClosed (R.range : Set V.adjoint.ker) := hR.isClosed_range
  -- These explicit equivariant kernel and quotient maps identify both terms of the reduced index.
  let k : R.ker ≃ₗ[ℂ] S.adjoint.ker :=
    { toFun := fun z ↦ ⟨z.val.val, congrArg Subtype.val z.property⟩
      invFun := fun y ↦ ⟨⟨y.val, by
        change U.adjoint y.val = 0
        have hy : S.adjoint y.val = 0 := y.property
        rw [← hVSa, comp_apply, hy, map_zero]⟩, by
          apply Subtype.ext
          exact y.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hk : ContRepresentation.Equiv
      (equivariantKernelRepresentation ξ η R hRg) χ := by
    refine ContRepresentation.Equiv.mk k.toContinuousLinearEquiv ?_
    intro g
    rfl
  let c : (V.adjoint.ker ⧸ R.range) ≃ₗ[ℂ] S.ker :=
    (Submodule.quotEquivOfEq _ _ hqker.symm).trans
      (q.toLinearMap.quotKerEquivOfSurjective hqsurj)
  have hc_apply (y : V.adjoint.ker) : c (R.range.mkQ y) = q y := rfl
  have hc : ContRepresentation.Equiv
      (equivariantCokernelRepresentation ξ η R hRg) κ := by
    refine ContRepresentation.Equiv.mk c.toContinuousLinearEquiv ?_
    intro g
    apply ContinuousLinearMap.ext
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change c (R.range.mkQ (η g y)) = κ g (c (R.range.mkQ y))
      rw [hc_apply, hc_apply]
      exact DFunLike.congr_fun (hp g) y.val
  -- Finite-dimensional normalization supplies the class relation in the split representation group.
  have hRdef : equivariantFredholmIndex ξ η hξ hη R hRg hR =
      representationClass χ hχ - representationClass κ hκ := by
    unfold equivariantFredholmIndex
    rw [representationClass_eq_of_equiv _ _ _ _ hk,
      representationClass_eq_of_equiv _ _ _ _ hc]
  have hRnorm := equivariantFredholmIndex_eq_class_sub_class ξ η hξ hη hξu hηu R hRg hR
  have hrelation : representationClass ξ hξ - representationClass η hη =
      representationClass χ hχ - representationClass κ hκ := hRnorm.symm.trans hRdef
  -- Compare the same original kernels, apply the adjoint-kernel formulas, and cancel.
  let : FiniteDimensional ℂ V.ker := hV.finite_ker
  let : FiniteDimensional ℂ U.ker := hU.finite_ker
  have hkernel : ContRepresentation.Equiv
      (equivariantKernelRepresentation ρ σ V hVg)
      (equivariantKernelRepresentation ρ τ U hUg) := by
    refine ContRepresentation.Equiv.mk (LinearEquiv.ofEq _ _ hker).toContinuousLinearEquiv ?_
    intro g
    rfl
  have hclasses := representationClass_eq_of_equiv _ _
    (continuous_equivariantKernelRepresentation ρ σ V hVg hρ)
    (continuous_equivariantKernelRepresentation ρ τ U hUg hρ) hkernel
  have hUi := equivariantFredholmIndex_eq_ker_sub_ker_adjoint ρ τ hρ hτ hρu hτu U hUg hU
  have hVindex := equivariantFredholmIndex_eq_ker_sub_ker_adjoint ρ σ hρ hσ hρu hσu V hVg hV
  have hSi := equivariantFredholmIndex_eq_ker_sub_ker_adjoint σ τ hσ hτ hσu hτu S hSg hS
  change equivariantFredholmIndex ρ τ hρ hτ U hUg hU = _
  rw [← hVi, hUi, hVindex, hSi, hclasses]
  change _ - representationClass ξ hξ =
    (_ - representationClass η hη) + (representationClass κ hκ - representationClass χ hχ)
  have hrelation' := congrArg Neg.neg hrelation
  simp only [neg_sub] at hrelation'
  rw [← hrelation']
  abel

end Hilbert

end AtiyahSinger
