/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationGrothendieckGroup
public import AtiyahSinger.Analysis.EquivariantFredholmRepresentations
public import AtiyahSinger.Analysis.Fredholm

/-!
# The representation-valued index of an equivariant Fredholm operator

Public module ID: M0509.

The index is the difference of the actual finite kernel and quotient-cokernel
representations. Group actions are jointly continuous: mathlib's
`ContRepresentation` by itself only makes each individual linear operator
continuous. No operator-norm continuity of the group action is imposed.

For fixed unitary Hilbert actions, the index is locally constant among
equivariant Fredholm operators in operator norm. This is the stability part of
SG III.9.4, following the invariant fixed-complement argument of III.7.2.
Compactness of the group is unnecessary once unitary actions are supplied;
geometric averaging and equivariant elliptic realization are developed separately.
The additive Grothendieck group suffices for these stability arguments.

Sources: SG III.9, printed pp.211--213. Dimension forgetting, adjoint
equivariance, the actual adjoint-kernel formula, and finite-dimensional
normalization, local stability, and path invariance are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger


set_option linter.unusedSectionVars false

open ContinuousLinearMap

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The actual finite kernel class minus the actual quotient-cokernel class. -/
def equivariantFredholmIndex
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hT : T.IsFredholm) : RepresentationGrothendieckGroup G := by
  letI : FiniteDimensional ℂ T.ker := hT.finite_ker
  letI : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  letI : IsClosed (T.range : Set F) := hT.isClosed_range
  exact representationClass (equivariantKernelRepresentation ρ σ T hTg)
      (continuous_equivariantKernelRepresentation ρ σ T hTg hρ) -
    representationClass (equivariantCokernelRepresentation ρ σ T hTg)
      (continuous_equivariantCokernelRepresentation ρ σ T hTg hσ)

/-- Forgetting the group action recovers the original integer Fredholm index. -/
theorem representationDimension_equivariantFredholmIndex
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hT : T.IsFredholm) :
    representationDimension G (equivariantFredholmIndex ρ σ hρ hσ T hTg hT) =
      T.index := by
  /- Stage 1: apply the additive dimension homomorphism to the defining
  difference. Its value on each actual finite representation is the finrank
  of that same carrier, independent of the chosen finite coordinates.
  Stage 2: the two dimensions are those of T.ker and F modulo T.range.
  Their finiteness comes from the same hT. Substitute the library's algebraic
  kernel-minus-cokernel index formula. No representation class is replaced
  by its dimension until this explicit forgetting map is applied. -/
  -- Evaluate dimension on these same finite kernel and quotient representations.
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : IsClosed (T.range : Set F) := hT.isClosed_range
  unfold equivariantFredholmIndex
  rw [map_sub, representationDimension_class, representationDimension_class]
  -- The integer index is defined by the original kernel and cokernel dimensions.
  exact LinearMap.index_eq_finrank_sub.symm

end Normed

section Hilbert

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
  [CompleteSpace E] [CompleteSpace F]

/-- The Hilbert adjoint of an intertwiner also intertwines the supplied unitary actions. -/
theorem adjoint_intertwines_of_isometry
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρu : ∀ g : G, Isometry (ρ g)) (hσu : ∀ g : G, Isometry (σ g))
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T) :
    ∀ g : G, T.adjoint.comp (σ g) = (ρ g).comp T.adjoint := by
  /- Stage 1: a complex-linear isometry preserves the Hermitian form. The
  group inverse supplies its inverse operator, so its Hilbert adjoint is
  exactly the action of g inverse, not just an arbitrary left inverse.
  Stage 2: take adjoints in the intertwining equation at g inverse and
  reverse the composition order. Substitute these two inverse-action
  formulas to obtain the displayed equation at g. Continuity in the group,
  compactness of G and Fredholmness of T are not needed for this identity. -/
  -- A unitary action has adjoint equal to its actual inverse group action.
  have hρadj (g : G) : (ρ g).adjoint = ρ g⁻¹ := by
    apply Eq.symm
    apply (eq_adjoint_iff _ _).mpr
    intro x y
    let u : E →ₗᵢ[ℂ] E :=
      { toLinearMap := (ρ g).toLinearMap
        norm_map' := (hρu g).norm_map_of_map_zero (map_zero _) }
    have hcancel : ρ g (ρ g⁻¹ x) = x := by
      change ((ρ g) * (ρ g⁻¹)) x = x
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have hinner := u.inner_map_map (ρ g⁻¹ x) y
    change inner ℂ (ρ g (ρ g⁻¹ x)) (ρ g y) = inner ℂ (ρ g⁻¹ x) y at hinner
    rw [hcancel] at hinner
    exact hinner.symm
  have hσadj (g : G) : (σ g).adjoint = σ g⁻¹ := by
    apply Eq.symm
    apply (eq_adjoint_iff _ _).mpr
    intro x y
    let u : F →ₗᵢ[ℂ] F :=
      { toLinearMap := (σ g).toLinearMap
        norm_map' := (hσu g).norm_map_of_map_zero (map_zero _) }
    have hcancel : σ g (σ g⁻¹ x) = x := by
      change ((σ g) * (σ g⁻¹)) x = x
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    have hinner := u.inner_map_map (σ g⁻¹ x) y
    change inner ℂ (σ g (σ g⁻¹ x)) (σ g y) = inner ℂ (σ g⁻¹ x) y at hinner
    rw [hcancel] at hinner
    exact hinner.symm
  -- Take the adjoint of the supplied equation at the inverse group element.
  intro g
  have h := congrArg ContinuousLinearMap.adjoint (hTg g⁻¹)
  simpa only [adjoint_comp, hρadj, hσadj, inv_inv] using h.symm

/-- Unitary equivariance identifies the actual cokernel class with the adjoint-kernel class. -/
theorem equivariantFredholmIndex_eq_ker_sub_ker_adjoint
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hρu : ∀ g : G, Isometry (ρ g)) (hσu : ∀ g : G, Isometry (σ g))
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hT : T.IsFredholm) :
    letI : FiniteDimensional ℂ T.ker := hT.finite_ker
    letI : FiniteDimensional ℂ T.adjoint.ker := (isFredholm_adjoint T hT).finite_ker
    equivariantFredholmIndex ρ σ hρ hσ T hTg hT =
      representationClass (equivariantKernelRepresentation ρ σ T hTg)
          (continuous_equivariantKernelRepresentation ρ σ T hTg hρ) -
        representationClass
          (equivariantKernelRepresentation σ ρ T.adjoint
            (adjoint_intertwines_of_isometry ρ σ hρu hσu T hTg))
          (continuous_equivariantKernelRepresentation σ ρ T.adjoint
            (adjoint_intertwines_of_isometry ρ σ hρu hσu T hTg) hσ) := by
  /- Stage 1: closed range gives the original orthogonal decomposition of F
  into range(T) and its perpendicular, which is ker(T adjoint). Unitary
  equivariance makes the range and perpendicular invariant under σ.
  Stage 2: orthogonal projection descends to a continuous linear equivalence
  from the original quotient F/range(T) onto that adjoint kernel. Its inverse
  is inclusion followed by the original quotient map. Both intertwine σ;
  this upgrades the old nonequivariant cokernel equivalence to an actual
  representation equivalence, not merely equality of their dimensions.
  Stage 3: representationClass_eq_of_equiv equates their classes. Substitute
  into the defining index difference while retaining the original kernel term. -/
  -- Closed range supplies the original orthogonal quotient identification.
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : IsClosed (T.range : Set F) := hT.isClosed_range
  let : CompleteSpace T.range := hT.isClosed_range.completeSpace_coe
  let : FiniteDimensional ℂ T.adjoint.ker := (isFredholm_adjoint T hT).finite_ker
  let e₀ : (F ⧸ T.range) ≃ₗ[ℂ] T.adjoint.ker :=
    T.range.quotientEquivOrthogonal.toLinearEquiv.trans
      (LinearEquiv.ofEq _ _ T.orthogonal_range)
  let e : T.adjoint.ker ≃L[ℂ] (F ⧸ T.range) := e₀.symm.toContinuousLinearEquiv
  -- Its inverse direction is precisely inclusion followed by the original quotient map.
  have he_apply (x : T.adjoint.ker) : e x = T.range.mkQ x := by
    change T.range.quotientEquivOrthogonal.symm ⟨x.val, _⟩ = _
    exact T.range.quotientEquivOrthogonal_symm_eq_mk x.val _
  let ρa := equivariantKernelRepresentation σ ρ T.adjoint
    (adjoint_intertwines_of_isometry ρ σ hρu hσu T hTg)
  let σq := equivariantCokernelRepresentation ρ σ T hTg
  have he : ContRepresentation.Equiv ρa σq := by
    refine ContRepresentation.Equiv.mk e ?_
    intro g
    apply ContinuousLinearMap.ext
    intro x
    change e (ρa g x) = σq g (e x)
    simp only [he_apply]
    rfl
  -- Compare actual representations, then retain the unchanged original kernel term.
  have hclasses := representationClass_eq_of_equiv ρa σq
    (continuous_equivariantKernelRepresentation σ ρ T.adjoint
      (adjoint_intertwines_of_isometry ρ σ hρu hσu T hTg) hσ)
    (continuous_equivariantCokernelRepresentation ρ σ T hTg hσ) he
  unfold equivariantFredholmIndex
  rw [← hclasses]

/-- Finite-dimensional unitary representations have their representation-valued rank index. -/
theorem equivariantFredholmIndex_eq_class_sub_class
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hρu : ∀ g : G, Isometry (ρ g)) (hσu : ∀ g : G, Isometry (σ g))
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hT : T.IsFredholm) :
    equivariantFredholmIndex ρ σ hρ hσ T hTg hT =
      representationClass ρ hρ - representationClass σ hσ := by
  /- The original kernel projection and T form an augmented map
  E × ker(T adjoint) → ker(T) × F. Orthogonal decomposition proves it
  bijective, and the adjoint of the equivariant kernel inclusion makes the
  projection equivariant. Thus this is an actual representation equivalence.
  Apply the defining finite direct-sum relation to its two sides, use the
  already established adjoint-kernel formula, and cancel in the split group.
  This argument retains the actual actions, including zero-dimensional spaces;
  it uses no local stability or equality determined solely by dimension. -/
  classical
  let κ := equivariantKernelRepresentation ρ σ T hTg
  let hκ := continuous_equivariantKernelRepresentation ρ σ T hTg hρ
  let hTag := adjoint_intertwines_of_isometry ρ σ hρu hσu T hTg
  let χ := equivariantKernelRepresentation σ ρ T.adjoint hTag
  let hχ := continuous_equivariantKernelRepresentation σ ρ T.adjoint hTag hσ
  -- The orthogonal kernel projection intertwines by taking the adjoint of inclusion.
  have hκu (g : G) : Isometry (κ g) := by
    intro x y
    exact hρu g x.val y.val
  have hinc (g : G) : T.ker.subtypeL.comp (κ g) = (ρ g).comp T.ker.subtypeL := rfl
  have hp (g : G) : T.ker.orthogonalProjectionOnto.comp (ρ g) =
      (κ g).comp T.ker.orthogonalProjectionOnto := by
    simpa only [Submodule.adjoint_subtypeL] using
      adjoint_intertwines_of_isometry κ ρ hκu hρu T.ker.subtypeL hinc g
  -- The augmented operator identifies E plus the adjoint kernel with ker(T) plus F.
  let a : (E × T.adjoint.ker) →ₗ[ℂ] T.ker × F :=
    (T.ker.orthogonalProjectionOnto.toLinearMap.comp (LinearMap.fst ℂ E T.adjoint.ker)).prod
      (T.toLinearMap.coprod T.adjoint.ker.subtype)
  have ha : Function.Bijective a := by
    constructor
    · apply (injective_iff_map_eq_zero a).mpr
      rintro ⟨x, y⟩ h
      have hx : T.ker.orthogonalProjectionOnto x = 0 := congrArg Prod.fst h
      have hxy : T x + y.val = 0 := congrArg Prod.snd h
      have hy : y.val ∈ T.rangeᗮ := by
        rw [T.orthogonal_range]
        exact y.property
      have hTy : T x ∈ T.rangeᗮ := by
        rw [eq_neg_iff_add_eq_zero.mpr hxy]
        exact T.rangeᗮ.neg_mem hy
      have hTx : T x = 0 :=
        Submodule.disjoint_def.mp T.range.isCompl_orthogonal.disjoint (T x) ⟨x, rfl⟩ hTy
      have hxmem : x ∈ T.ker := hTx
      have hxzero : x = 0 := by
        have hself := T.ker.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hxmem⟩
        rw [hx] at hself
        exact (congrArg Subtype.val hself).symm
      have hyzero : y = 0 := by
        apply Subtype.ext
        simpa [hTx] using hxy
      exact Prod.ext hxzero hyzero
    · rintro ⟨k, z⟩
      let d := T.range.prodEquivOfIsCompl T.rangeᗮ T.range.isCompl_orthogonal
      obtain ⟨x, hx⟩ := (d.symm z).1.property
      change T x = (d.symm z).1.val at hx
      let y : T.adjoint.ker := ⟨(d.symm z).2.val, by
        rw [← T.orthogonal_range]
        exact (d.symm z).2.property⟩
      refine ⟨(k.val + (x - (T.ker.orthogonalProjectionOnto x).val), y), ?_⟩
      apply Prod.ext
      · change T.ker.orthogonalProjectionOnto
          (k.val + (x - (T.ker.orthogonalProjectionOnto x).val)) = k
        rw [map_add, map_sub, T.ker.orthogonalProjectionOnto_mem_subspace_eq_self,
          T.ker.orthogonalProjectionOnto_mem_subspace_eq_self, sub_self, add_zero]
      · change T (k.val + (x - (T.ker.orthogonalProjectionOnto x).val)) + y.val = z
        have hk : T k.val = 0 := k.property
        have hpker : T (T.ker.orthogonalProjectionOnto x).val = 0 :=
          (T.ker.orthogonalProjectionOnto x).property
        rw [map_add, map_sub, hk, hpker, sub_zero, zero_add, hx]
        exact d.apply_symm_apply z
  let e := (LinearEquiv.ofBijective a ha).toContinuousLinearEquiv
  let α : ContRepresentation ℂ G (E × T.adjoint.ker) := .ofMonoidHom
    { toFun := fun g ↦ (ρ g).prodMap (χ g)
      map_one' := by
        ext x <;> simp
      map_mul' := by
        intro g h
        ext x <;> simp [map_mul] }
  let β : ContRepresentation ℂ G (T.ker × F) := .ofMonoidHom
    { toFun := fun g ↦ (κ g).prodMap (σ g)
      map_one' := by
        ext x <;> simp
      map_mul' := by
        intro g h
        ext x <;> simp [map_mul] }
  let hα := (hρ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
    (hχ.comp (continuous_fst.prodMk continuous_snd.snd))
  let hβ := (hκ.comp (continuous_fst.prodMk continuous_snd.fst)).prodMk
    (hσ.comp (continuous_fst.prodMk continuous_snd.snd))
  have he : ContRepresentation.Equiv α β := by
    refine ContRepresentation.Equiv.mk e ?_
    intro g
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext
    · exact DFunLike.congr_fun (hp g) x
    · change T (ρ g x) + σ g y.val = σ g (T x + y.val)
      rw [map_add]
      exact congrArg (· + σ g y.val) (DFunLike.congr_fun (hTg g) x)
  -- Both products use the ordered finite coordinates in the defining direct-sum relation.
  have hprod {A : Type _} {B : Type _} [NormedAddCommGroup A] [NormedSpace ℂ A]
      [NormedAddCommGroup B] [NormedSpace ℂ B]
      [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
      (r : ContRepresentation ℂ G A) (s : ContRepresentation ℂ G B)
      (hr : Continuous (fun p : G × A ↦ r p.1 p.2))
      (hs : Continuous (fun p : G × B ↦ s p.1 p.2))
      (p : ContRepresentation ℂ G (A × B))
      (hp : ∀ g, p g = (r g).prodMap (s g))
      (hc : Continuous (fun q : G × (A × B) ↦ p q.1 q.2)) :
      representationClass p hc = representationClass r hr + representationClass s hs := by
    let e₁ : A ≃L[ℂ] (Fin (Module.finrank ℂ A) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let e₂ : B ≃L[ℂ] (Fin (Module.finrank ℂ B) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let ν := FiniteContinuousRepresentation.ofEquiv r hr e₁
    let ν' := FiniteContinuousRepresentation.ofEquiv s hs e₂
    let c : (Fin (ν.dimension + ν'.dimension) → ℂ) ≃L[ℂ]
        (Fin ν.dimension → ℂ) × (Fin ν'.dimension → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ
        (fun _ : Fin ν.dimension ⊕ Fin ν'.dimension ↦ ℂ) finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ
          (Fin ν.dimension) (Fin ν'.dimension) (fun _ ↦ ℂ))
    let b := ((e₁.toLinearEquiv.prodCongr e₂.toLinearEquiv).trans
      c.symm.toLinearEquiv).toContinuousLinearEquiv
    rw [representationClass_ofEquiv p hc b, representationClass_ofEquiv r hr e₁,
      representationClass_ofEquiv s hs e₂, ← finiteRepresentationClass_directSum]
    apply finiteRepresentationClass_eq_of_isEquivalent
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
    intro g
    change b.toContinuousLinearMap.comp ((p g).comp b.symm.toContinuousLinearMap) = _
    rw [hp g]
    rfl
  have hclasses := representationClass_eq_of_equiv α β hα hβ he
  rw [hprod ρ χ hρ hχ α (fun _ ↦ rfl) hα,
    hprod κ σ hκ hσ β (fun _ ↦ rfl) hβ] at hclasses
  -- Cancel the shared finite summands in the actual representation group.
  rw [equivariantFredholmIndex_eq_ker_sub_ker_adjoint ρ σ hρ hσ hρu hσu T hTg hT]
  change representationClass κ hκ - representationClass χ hχ = _
  exact sub_eq_sub_iff_add_eq_add.mpr hclasses.symm

/-- Small equivariant norm perturbations preserve the full virtual representation index. -/
theorem exists_radius_equivariantFredholmIndex_eq
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hρu : ∀ g : G, Isometry (ρ g)) (hσu : ∀ g : G, Isometry (σ g))
    (T₀ : E →L[ℂ] F) (hT₀g : ∀ g : G, T₀.comp (ρ g) = (σ g).comp T₀)
    (hT₀ : T₀.IsFredholm) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ T : E →L[ℂ] F, ‖T - T₀‖ < ε →
      ∀ hTg : (∀ g : G, T.comp (ρ g) = (σ g).comp T),
        ∃ hT : T.IsFredholm,
          equivariantFredholmIndex ρ σ hρ hσ T hTg hT =
            equivariantFredholmIndex ρ σ hρ hσ T₀ hT₀g hT₀ := by
  /- Use the same fixed finite defect spaces K = ker(T₀) and Q = ker(T₀ adjoint).
  The augmented map (x,q) ↦ (projection_K(x), T(x)+q) is invertible at T₀,
  hence throughout one operator-norm neighborhood. Its inverse's K → Q block
  is a finite-dimensional intertwiner. Restriction of projection_K identifies
  the actual kernel of T with its reduced kernel; inclusion Q → F identifies
  the reduced quotient-cokernel with the actual quotient-cokernel of T.
  Finite-dimensional normalization then gives the fixed class [K]-[Q].
  All block actions use the original unitary representations; neither a Hilbert
  norm on the native product nor compact-group averaging is needed. -/
  classical
  let : FiniteDimensional ℂ T₀.ker := hT₀.finite_ker
  let : FiniteDimensional ℂ T₀.adjoint.ker := (isFredholm_adjoint T₀ hT₀).finite_ker
  let : CompleteSpace T₀.range := hT₀.isClosed_range.completeSpace_coe
  let κ := equivariantKernelRepresentation ρ σ T₀ hT₀g
  let hκ := continuous_equivariantKernelRepresentation ρ σ T₀ hT₀g hρ
  let hT₀ag := adjoint_intertwines_of_isometry ρ σ hρu hσu T₀ hT₀g
  let χ := equivariantKernelRepresentation σ ρ T₀.adjoint hT₀ag
  let hχ := continuous_equivariantKernelRepresentation σ ρ T₀.adjoint hT₀ag hσ
  have hκu (g : G) : Isometry (κ g) := by
    intro x y
    exact hρu g x.val y.val
  have hχu (g : G) : Isometry (χ g) := by
    intro x y
    exact hσu g x.val y.val
  have hinc (g : G) : T₀.ker.subtypeL.comp (κ g) = (ρ g).comp T₀.ker.subtypeL := rfl
  have hp (g : G) : T₀.ker.orthogonalProjectionOnto.comp (ρ g) =
      (κ g).comp T₀.ker.orthogonalProjectionOnto := by
    simpa only [Submodule.adjoint_subtypeL] using
      adjoint_intertwines_of_isometry κ ρ hκu hρu T₀.ker.subtypeL hinc g
  -- Fix the two actual defect spaces; only the T block varies.
  let A (T : E →L[ℂ] F) : (E × T₀.adjoint.ker) →L[ℂ] T₀.ker × F :=
    (T₀.ker.orthogonalProjectionOnto.comp (ContinuousLinearMap.fst ℂ E T₀.adjoint.ker)).prod
      (T.coprod T₀.adjoint.ker.subtypeL)
  have hA₀bij : Function.Bijective (A T₀) := by
    constructor
    · apply (injective_iff_map_eq_zero (A T₀)).mpr
      rintro ⟨x, y⟩ h
      have hx : T₀.ker.orthogonalProjectionOnto x = 0 := congrArg Prod.fst h
      have hxy : T₀ x + y.val = 0 := congrArg Prod.snd h
      have hy : y.val ∈ T₀.rangeᗮ := by
        rw [T₀.orthogonal_range]
        exact y.property
      have hTy : T₀ x ∈ T₀.rangeᗮ := by
        rw [eq_neg_iff_add_eq_zero.mpr hxy]
        exact T₀.rangeᗮ.neg_mem hy
      have hTx : T₀ x = 0 :=
        Submodule.disjoint_def.mp T₀.range.isCompl_orthogonal.disjoint (T₀ x) ⟨x, rfl⟩ hTy
      have hxmem : x ∈ T₀.ker := hTx
      have hxzero : x = 0 := by
        have hself := T₀.ker.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hxmem⟩
        rw [hx] at hself
        exact (congrArg Subtype.val hself).symm
      have hyzero : y = 0 := by
        apply Subtype.ext
        simpa [hTx] using hxy
      exact Prod.ext hxzero hyzero
    · rintro ⟨k, z⟩
      let d := T₀.range.prodEquivOfIsCompl T₀.rangeᗮ T₀.range.isCompl_orthogonal
      obtain ⟨x, hx⟩ := (d.symm z).1.property
      change T₀ x = (d.symm z).1.val at hx
      let y : T₀.adjoint.ker := ⟨(d.symm z).2.val, by
        rw [← T₀.orthogonal_range]
        exact (d.symm z).2.property⟩
      refine ⟨(k.val + (x - (T₀.ker.orthogonalProjectionOnto x).val), y), ?_⟩
      apply Prod.ext
      · change T₀.ker.orthogonalProjectionOnto
          (k.val + (x - (T₀.ker.orthogonalProjectionOnto x).val)) = k
        rw [map_add, map_sub, T₀.ker.orthogonalProjectionOnto_mem_subspace_eq_self,
          T₀.ker.orthogonalProjectionOnto_mem_subspace_eq_self, sub_self, add_zero]
      · change T₀ (k.val + (x - (T₀.ker.orthogonalProjectionOnto x).val)) + y.val = z
        have hk : T₀ k.val = 0 := k.property
        have hpker : T₀ (T₀.ker.orthogonalProjectionOnto x).val = 0 :=
          (T₀.ker.orthogonalProjectionOnto x).property
        rw [map_add, map_sub, hk, hpker, sub_zero, zero_add, hx]
        exact d.apply_symm_apply z
  have hA₀ : (A T₀).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective (A T₀)
      (LinearMap.ker_eq_bot.mpr hA₀bij.injective)
      (LinearMap.range_eq_top.mpr hA₀bij.surjective), rfl⟩
  have hAcontinuous : Continuous A := by
    exact (prodL ℂ).continuous.comp
      (continuous_const.prodMk
        ((coprodEquivL ℂ).continuous.comp (continuous_id.prodMk continuous_const)))
  -- Intersect the ordinary Fredholm neighborhood with the augmented invertibility neighborhood.
  have hopen : IsOpen {T : E →L[ℂ] F | T.IsFredholm ∧ (A T).IsInvertible} :=
    ContinuousLinearMap.isOpen_setOfPred_isFredholm.inter
      (ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage hAcontinuous)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen T₀ ⟨hT₀, hA₀⟩
  refine ⟨ε, hε, ?_⟩
  intro T hdist hTg
  obtain ⟨hT, hA⟩ := hball (by simpa [Metric.mem_ball, dist_eq_norm] using hdist)
  refine ⟨hT, ?_⟩
  -- The finite inverse block retains the fixed actual unitary defect representations.
  let S := (A T).inverse
  have hAg (g : G) (x : E × T₀.adjoint.ker) :
      A T (ρ g x.1, χ g x.2) = (κ g (A T x).1, σ g (A T x).2) := by
    apply Prod.ext
    · exact DFunLike.congr_fun (hp g) x.1
    · change T (ρ g x.1) + σ g x.2.val = σ g (T x.1 + x.2.val)
      rw [map_add]
      exact congrArg (· + σ g x.2.val) (DFunLike.congr_fun (hTg g) x.1)
  have hSg (g : G) (z : T₀.ker × F) :
      S (κ g z.1, σ g z.2) = (ρ g (S z).1, χ g (S z).2) := by
    apply hA.bijective.injective
    rw [hAg, hA.self_apply_inverse, show A T (S z) = z from hA.self_apply_inverse z]
  let R : T₀.ker →L[ℂ] T₀.adjoint.ker :=
    (ContinuousLinearMap.snd ℂ E T₀.adjoint.ker).comp
      (S.comp (ContinuousLinearMap.inl ℂ T₀.ker F))
  have hRg (g : G) : R.comp (κ g) = (χ g).comp R := by
    apply ContinuousLinearMap.ext
    intro x
    change (S (κ g x, 0)).2 = χ g (S (x, 0)).2
    simpa only [map_zero] using congrArg Prod.snd (hSg g (x, 0))
  have hR : R.IsFredholm := by
    apply (isFredholm_iff_closed_range_finite R).mpr
    exact ⟨R.range.closed_of_finiteDimensional, inferInstance, inferInstance⟩
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : IsClosed (T.range : Set F) := hT.isClosed_range
  let : IsClosed (R.range : Set T₀.adjoint.ker) := hR.isClosed_range
  -- The fixed projection restricts to an equivalence of the actual two kernels.
  have hSker (x : T.ker) : S (T₀.ker.orthogonalProjectionOnto x.val, 0) = (x.val, 0) := by
    have hTx : T x.val = 0 := x.property
    have hAx : A T (x.val, 0) = (T₀.ker.orthogonalProjectionOnto x.val, 0) := by
      apply Prod.ext
      · rfl
      · change T x.val + (0 : T₀.adjoint.ker).val = 0
        simpa only [Submodule.coe_zero, add_zero] using hTx
    rw [← hAx]
    exact hA.inverse_apply_self (x.val, 0)
  let k : T.ker →ₗ[ℂ] R.ker :=
    (T₀.ker.orthogonalProjectionOnto.toLinearMap.comp T.ker.subtype).codRestrict _ (by
      intro x
      change (S (T₀.ker.orthogonalProjectionOnto x.val, 0)).2 = 0
      rw [hSker])
  have hkbij : Function.Bijective k := by
    constructor
    · intro x y hxy
      have hp' : T₀.ker.orthogonalProjectionOnto x.val =
          T₀.ker.orthogonalProjectionOnto y.val := congrArg Subtype.val hxy
      have hs := congrArg (fun z ↦ S (z, 0)) hp'
      rw [hSker, hSker] at hs
      exact Subtype.ext (congrArg Prod.fst hs)
    · intro z
      have hz : (S (z.val, 0)).2 = 0 := z.property
      have heq := hA.self_apply_inverse (z.val, 0)
      have hx : T (S (z.val, 0)).1 = 0 := by
        have h := congrArg Prod.snd heq
        change T (S (z.val, 0)).1 + ((S (z.val, 0)).2).val = 0 at h
        simpa only [hz, Submodule.coe_zero, add_zero] using h
      refine ⟨⟨(S (z.val, 0)).1, hx⟩, ?_⟩
      apply Subtype.ext
      exact congrArg Prod.fst heq
  let ke := (LinearEquiv.ofBijective k hkbij).toContinuousLinearEquiv
  have hke : ContRepresentation.Equiv
      (equivariantKernelRepresentation ρ σ T hTg)
      (equivariantKernelRepresentation κ χ R hRg) := by
    refine ContRepresentation.Equiv.mk ke ?_
    intro g
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact DFunLike.congr_fun (hp g) x.val
  -- Inclusion of the fixed adjoint kernel descends to the actual quotient-cokernels.
  let q : T₀.adjoint.ker →ₗ[ℂ] (F ⧸ T.range) := T.range.mkQ.comp T₀.adjoint.ker.subtype
  have hkill : R.range ≤ q.ker := by
    rintro y ⟨x, rfl⟩
    change T.range.mkQ (R x).val = 0
    apply (Submodule.Quotient.mk_eq_zero T.range).mpr
    refine ⟨-(S (x, 0)).1, ?_⟩
    have h := congrArg Prod.snd (hA.self_apply_inverse (x, 0))
    change T (S (x, 0)).1 + (R x).val = 0 at h
    rw [map_neg]
    exact neg_eq_iff_add_eq_zero.mpr h
  let c : (T₀.adjoint.ker ⧸ R.range) →ₗ[ℂ] (F ⧸ T.range) := R.range.liftQ q hkill
  have hc_apply (y : T₀.adjoint.ker) : c (R.range.mkQ y) = T.range.mkQ y.val := rfl
  have hcbij : Function.Bijective c := by
    constructor
    · apply (injective_iff_map_eq_zero c).mpr
      intro y hy
      obtain ⟨q', rfl⟩ := R.range.mkQ_surjective y
      have hq' : q'.val ∈ T.range := (Submodule.Quotient.mk_eq_zero T.range).mp hy
      obtain ⟨x, hx⟩ := hq'
      change T x = q'.val at hx
      apply (Submodule.Quotient.mk_eq_zero R.range).mpr
      refine ⟨-T₀.ker.orthogonalProjectionOnto x, ?_⟩
      have hAx : A T (-x, q') = (-T₀.ker.orthogonalProjectionOnto x, 0) := by
        apply Prod.ext
        · change T₀.ker.orthogonalProjectionOnto (-x) =
            -T₀.ker.orthogonalProjectionOnto x
          exact map_neg _ _
        · change T (-x) + q'.val = 0
          rw [map_neg, hx, neg_add_cancel]
      have hs := hA.inverse_apply_self (-x, q')
      rw [hAx] at hs
      exact congrArg Prod.snd hs
    · intro y
      obtain ⟨z, rfl⟩ := T.range.mkQ_surjective y
      refine ⟨R.range.mkQ (S (0, z)).2, ?_⟩
      rw [hc_apply]
      have heq := congrArg Prod.snd (hA.self_apply_inverse (0, z))
      change T (S (0, z)).1 + ((S (0, z)).2).val = z at heq
      have hclass := congrArg T.range.mkQ heq
      have hzero : T.range.mkQ (T (S (0, z)).1) = 0 :=
        (Submodule.Quotient.mk_eq_zero T.range).mpr ⟨_, rfl⟩
      simpa only [map_add, hzero, zero_add] using hclass
  let ce := (LinearEquiv.ofBijective c hcbij).toContinuousLinearEquiv
  have hce : ContRepresentation.Equiv
      (equivariantCokernelRepresentation κ χ R hRg)
      (equivariantCokernelRepresentation ρ σ T hTg) := by
    refine ContRepresentation.Equiv.mk ce ?_
    intro g
    apply ContinuousLinearMap.ext
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change c (R.range.mkQ (χ g y)) =
        equivariantCokernelRepresentation ρ σ T hTg g (c (R.range.mkQ y))
      rw [hc_apply, hc_apply]
      rfl
  -- Both representation terms agree through these specified maps before normalization.
  have hindex : equivariantFredholmIndex ρ σ hρ hσ T hTg hT =
      equivariantFredholmIndex κ χ hκ hχ R hRg hR := by
    unfold equivariantFredholmIndex
    congr 1
    · exact representationClass_eq_of_equiv _ _ _ _ hke
    · exact (representationClass_eq_of_equiv _ _ _ _ hce).symm
  rw [hindex, equivariantFredholmIndex_eq_class_sub_class κ χ hκ hχ hκu hχu R hRg hR]
  exact (equivariantFredholmIndex_eq_ker_sub_ker_adjoint
    ρ σ hρ hσ hρu hσu T₀ hT₀g hT₀).symm

/-- Operator-norm-continuous equivariant Fredholm paths preserve the representation-valued index. -/
theorem equivariantFredholmIndex_eq_of_path
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (hρu : ∀ g : G, Isometry (ρ g)) (hσu : ∀ g : G, Isometry (σ g))
    {T₀ T₁ : E →L[ℂ] F} (γ : Path T₀ T₁)
    (hγg : ∀ t, ∀ g : G, (γ t).comp (ρ g) = (σ g).comp (γ t))
    (hγ : ∀ t, (γ t).IsFredholm)
    (hT₀g : ∀ g : G, T₀.comp (ρ g) = (σ g).comp T₀)
    (hT₁g : ∀ g : G, T₁.comp (ρ g) = (σ g).comp T₁)
    (hT₀ : T₀.IsFredholm) (hT₁ : T₁.IsFredholm) :
    equivariantFredholmIndex ρ σ hρ hσ T₀ hT₀g hT₀ =
      equivariantFredholmIndex ρ σ hρ hσ T₁ hT₁g hT₁ := by
  /- Stage 1: apply the equivariant fixed-complement radius theorem at each
  γ(t). Norm continuity of this actual path makes its virtual representation
  index locally constant on the parameter interval. The two group actions
  and their Hilbert norms are fixed throughout the path.
  Stage 2: a locally constant map on a connected interval is constant,
  regardless of whether the target group is finitely generated. Evaluate
  at the endpoints and use γ.source/γ.target. Proof irrelevance identifies
  the endpoint equivariance and Fredholm certificates with the supplied ones.
  Strong continuity of the group action is sufficient, whereas pointwise
  continuity of the operator path alone would not supply this norm argument. -/
  -- Give the unchanged representation group the discrete topology only for this argument.
  let : TopologicalSpace (RepresentationGrothendieckGroup G) := ⊥
  let : DiscreteTopology (RepresentationGrothendieckGroup G) := ⟨rfl⟩
  let f : unitInterval → RepresentationGrothendieckGroup G :=
    fun t ↦ equivariantFredholmIndex ρ σ hρ hσ (γ t) (hγg t) (hγ t)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨ε, hε, hlocal⟩ := exists_radius_equivariantFredholmIndex_eq
      ρ σ hρ hσ hρu hσu (γ t) (hγg t) (hγ t)
    apply continuousAt_const.congr_of_eventuallyEq
    have hnear : ∀ᶠ s in nhds t, γ s ∈ Metric.ball (γ t) ε :=
      γ.continuous.continuousAt (Metric.ball_mem_nhds _ hε)
    filter_upwards [hnear] with s hs
    have hnorm : ‖γ s - γ t‖ < ε := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hs
    obtain ⟨hTs, hindex⟩ := hlocal (γ s) hnorm (hγg s)
    exact hindex
  -- Connectedness fixes the virtual class; endpoint certificates agree by proof irrelevance.
  have hconstant := TotallyDisconnectedSpace.eq_of_continuous f hf 0 1
  simpa only [f, γ.source, γ.target] using hconstant


end Hilbert

end AtiyahSinger
