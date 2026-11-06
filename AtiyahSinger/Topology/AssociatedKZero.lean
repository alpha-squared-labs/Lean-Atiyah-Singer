/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRing
public import AtiyahSinger.Topology.AssociatedVectorDescent
public import AtiyahSinger.Topology.BundleTensorKZero
public import AtiyahSinger.Topology.KZeroRing

/-!
# The associated-bundle map from representations to K theory

Public module ID: M1541.

For a fixed locally trivial right principal G-bundle P over a compact Hausdorff
base, send a finite complex representation to the K class of its actual
associated quotient vector bundle. Isomorphism, direct sum, tensor product and
the trivial line give a unique ring map on the existing split representation
Grothendieck group. Both the source and target retain their previous additive
groups and their specified tensor products.

Source: SG III.13 (13.17), printed p.252 / PDF p.264, together with the complex
representation ring of SG III.9 and the associated vector bundles of SG II.3.
The nearby orthogonal representation example is real: applying this complex
version to that example requires complexification. No real bundle is silently
used as a complex bundle. Group compactness is not needed for this construction;
compact Hausdorffness of the base is used by the existing Serre--Swan K model.
This is ordinary K theory, not the compactly supported equivariant K product
of SG (13.16). The proofs retain the original quotient maps and tensor topology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

variable {G P B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [CompactSpace B] [T2Space B]

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology

/-- The K class of the same principal bundle associated to the specified complex representation. -/
def associatedKZeroClass (hP : IsPrincipalBundle G projection)
    (ρ : FiniteContinuousRepresentation G) : ComplexKZero B :=
  letI := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
  ComplexBundle.kZeroClass (AssociatedVectorFiber hP ρ.representation)

/-- The associated-class construction preserves the defining relations and tensor unit/product. -/
theorem associatedKZeroClass_relations (hP : IsPrincipalBundle G projection) :
    (∀ ρ σ : FiniteContinuousRepresentation G,
      ρ.IsEquivalent σ → associatedKZeroClass hP ρ = associatedKZeroClass hP σ) ∧
    (∀ ρ σ : FiniteContinuousRepresentation G,
      associatedKZeroClass hP (ρ.directSum σ) =
        associatedKZeroClass hP ρ + associatedKZeroClass hP σ) ∧
    (∀ ρ σ : FiniteContinuousRepresentation G,
      associatedKZeroClass hP (ρ.tensor σ) =
        associatedKZeroClass hP ρ * associatedKZeroClass hP σ) ∧
    associatedKZeroClass hP (FiniteContinuousRepresentation.trivial (G := G)) = 1 := by
  /- For isomorphic representations, the continuous linear intertwiner and
  representative quotient maps satisfy the covariant descent criterion.
  The resulting bundle isomorphism preserves kZeroClass.
  For direct sums, the specified Fin-addition coordinates and the two
  representative maps at the same p give the sum-bundle isomorphism.
  For tensor products, tensorCoordinates.symm followed by TensorProduct.congr
  sends the associated tensor-representation fiber to the tensor product
  of the two associated fibers. The same group element acts on both factors.
  Expand in the finite tensor basis to factor the total map through the
  defining finite-sum final topology; this proves its continuity.
  Covariant descent and kZeroClass_tensor give the displayed product law.
  For the trivial line, the identity vector coordinate descends independently
  of p and identifies its class with the free rank-one unit. -/
  classical
  have hmk (ρ : FiniteContinuousRepresentation G) :
      Continuous (fun z : P × (Fin ρ.dimension → ℂ) ↦
        (⟨projection z.1, associatedVectorFiberMk hP ρ.representation z.1 rfl z.2⟩ :
          Bundle.TotalSpace Unit (AssociatedVectorFiber hP ρ.representation))) :=
    (associatedVectorTotalHomeomorph hP ρ.representation).symm.continuous.comp continuous_quot_mk
  have hcov (ρ : FiniteContinuousRepresentation G) (b : B) (p : P)
      (hp : projection p = b) (g : G) (v) :
      associatedVectorFiberMkLinearEquiv hP ρ.representation (MulOpposite.op g • p)
          ((hP.projection_smul g p).trans hp) v =
        associatedVectorFiberMkLinearEquiv hP ρ.representation p hp (ρ.representation g v) := by
    let := associatedRepresentationAction ρ.representation
    apply Subtype.ext
    exact associatedBundleMk_smul p g v
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Intertwiners descend on the same quotient, with their specified action conventions.
    rintro ρ σ ⟨e⟩
    let := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
    let := isFiniteRank_associatedVector hP σ.representation σ.continuous_action
    obtain ⟨a, _⟩ := exists_associatedVector_iso_of_covariant_equiv hP ρ
      (AssociatedVectorFiber hP σ.representation)
      (fun b p hp ↦ e.toContinuousLinearEquiv.toLinearEquiv.trans
        (associatedVectorFiberMkLinearEquiv hP σ.representation p hp))
      ((hmk σ).comp (continuous_fst.prodMk (e.continuous.comp continuous_snd)))
      (by
        intro b p hp g v
        change associatedVectorFiberMkLinearEquiv hP σ.representation
          (MulOpposite.op g • p) _ (e v) =
          associatedVectorFiberMkLinearEquiv hP σ.representation p hp (e (ρ.representation g v))
        rw [hcov]
        exact congrArg (associatedVectorFiberMkLinearEquiv hP σ.representation p hp)
          (DFunLike.congr_fun (e.isIntertwining g) v).symm)
    exact ComplexBundle.kZeroClass_eq_of_iso a
  · -- The ordered finite coordinates and both quotient factors use one principal point.
    intro ρ σ
    let := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
    let := isFiniteRank_associatedVector hP σ.representation σ.continuous_action
    let := isFiniteRank_associatedVector hP (ρ.directSum σ).representation
      (ρ.directSum σ).continuous_action
    let := ComplexBundle.sumTopology (E := AssociatedVectorFiber hP ρ.representation)
      (F := AssociatedVectorFiber hP σ.representation)
    let := ComplexBundle.isFiniteRank_sum (E := AssociatedVectorFiber hP ρ.representation)
      (F := AssociatedVectorFiber hP σ.representation)
    let c : (Fin (ρ.dimension + σ.dimension) → ℂ) ≃L[ℂ]
        (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) :=
      (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin ρ.dimension ⊕ Fin σ.dimension ↦ ℂ)
        finSumFinEquiv.symm).trans
        (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin ρ.dimension) (Fin σ.dimension) (fun _ ↦ ℂ))
    have haction (g : G) (v) : c ((ρ.directSum σ).representation g v) =
        (ρ.representation g (c v).1, σ.representation g (c v).2) := by
      change c (c.symm (ρ.representation g (c v).1, σ.representation g (c v).2)) = _
      exact c.apply_symm_apply _
    obtain ⟨a, _⟩ := exists_associatedVector_iso_of_covariant_equiv hP (ρ.directSum σ)
      (fun b ↦ AssociatedVectorFiber hP ρ.representation b ×
        AssociatedVectorFiber hP σ.representation b)
      (fun b p hp ↦ c.toLinearEquiv.trans
        ((associatedVectorFiberMkLinearEquiv hP ρ.representation p hp).prodCongr
          (associatedVectorFiberMkLinearEquiv hP σ.representation p hp)))
      (by
        apply continuous_induced_rng.mpr
        exact ((hmk ρ).comp (continuous_fst.prodMk (c.continuous.comp continuous_snd).fst)).prodMk
          ((hmk σ).comp (continuous_fst.prodMk (c.continuous.comp continuous_snd).snd)))
      (by
        intro b p hp g v
        change
          (associatedVectorFiberMkLinearEquiv hP ρ.representation (MulOpposite.op g • p)
              _ (c v).1,
            associatedVectorFiberMkLinearEquiv hP σ.representation (MulOpposite.op g • p)
              _ (c v).2) =
          (associatedVectorFiberMkLinearEquiv hP ρ.representation p hp
              (c ((ρ.directSum σ).representation g v)).1,
            associatedVectorFiberMkLinearEquiv hP σ.representation p hp
              (c ((ρ.directSum σ).representation g v)).2)
        rw [haction]
        exact Prod.ext (hcov ρ b p hp g (c v).1) (hcov σ b p hp g (c v).2))
    exact (ComplexBundle.kZeroClass_eq_of_iso a).trans ComplexBundle.kZeroClass_sum
  · -- Tensor every pair of coordinates at the same principal point, then descend.
    intro ρ σ
    let := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
    let := isFiniteRank_associatedVector hP σ.representation σ.continuous_action
    let := isFiniteRank_associatedVector hP (ρ.tensor σ).representation
      (ρ.tensor σ).continuous_action
    let E := AssociatedVectorFiber hP ρ.representation
    let F := AssociatedVectorFiber hP σ.representation
    let := ComplexBundle.tensorTopology (E := E) (F := F)
    let := ComplexBundle.isFiniteRank_tensor (E := E) (F := F)
    let c := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
    let a (b : B) (p : P) (hp : projection p = b) := c.symm.trans
      (TensorProduct.congr (associatedVectorFiberMkLinearEquiv hP ρ.representation p hp)
        (associatedVectorFiberMkLinearEquiv hP σ.representation p hp))
    have ha (b : B) (p : P) (hp : projection p = b) (g : G) (v) :
        a b (MulOpposite.op g • p) ((hP.projection_smul g p).trans hp) v =
          a b p hp ((ρ.tensor σ).representation g v) := by
      have haction : c.symm ((ρ.tensor σ).representation g v) =
          TensorProduct.map (ρ.representation g).toLinearMap (σ.representation g).toLinearMap
            (c.symm v) := by
        change c.symm (c _) = _
        exact c.symm_apply_apply _
      change TensorProduct.congr _ _ (c.symm v) =
        TensorProduct.congr _ _ (c.symm ((ρ.tensor σ).representation g v))
      rw [haction]
      generalize c.symm v = t
      induction t using TensorProduct.inductionOn with
      | tmul x y =>
        simp only [TensorProduct.congr_tmul, TensorProduct.map_tmul]
        rw [hcov ρ b p hp g x, hcov σ b p hp g y]
        rfl
      | add t u ht hu => simp only [map_add, ht, hu]
    -- The actual finite-sum final topology makes the representative tensor map continuous.
    let bp := Pi.basisFun ℂ (Fin ρ.dimension)
    let bq := Pi.basisFun ℂ (Fin σ.dimension)
    let basis := (bp.tensorProduct bq).reindex finProdFinEquiv
    let m := ρ.dimension * σ.dimension
    let D := Bundle.TotalSpace Unit (fun b ↦ (Fin m → E b) × (Fin m → F b))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun k ↦ (⟨z.proj, z.snd.1 k⟩ : Bundle.TotalSpace Unit E)),
        (fun k ↦ (⟨z.proj, z.snd.2 k⟩ : Bundle.TotalSpace Unit F)))) inferInstance
    let gen (z : D) : Bundle.TotalSpace Unit (fun b ↦ E b ⊗[ℂ] F b) :=
      ⟨z.proj, ∑ k : Fin m, z.snd.1 k ⊗ₜ[ℂ] z.snd.2 k⟩
    have hgen : Continuous gen := continuous_iSup_rng (i := m) continuous_coinduced_rng
    let lift (z : P × (Fin m → ℂ)) : D :=
      ⟨projection z.1,
        (fun k ↦ associatedVectorFiberMk hP ρ.representation z.1 rfl
          (basis.repr (c.symm z.2) k • bp (finProdFinEquiv.symm k).1)),
        (fun k ↦ associatedVectorFiberMk hP σ.representation z.1 rfl
          (bq (finProdFinEquiv.symm k).2))⟩
    have hlift : Continuous lift := by
      apply continuous_induced_rng.mpr
      refine (hP.projection_properties.1.comp continuous_fst).prodMk ?_
      apply Continuous.prodMk
      · apply continuous_pi
        intro k
        have hcoef : Continuous (fun z : P × (Fin m → ℂ) ↦ basis.repr (c.symm z.2) k) :=
          ((basis.coord k).comp c.symm.toLinearMap).continuous_of_finiteDimensional.comp
            continuous_snd
        exact (hmk ρ).comp (continuous_fst.prodMk (hcoef.smul continuous_const))
      · apply continuous_pi
        intro k
        exact (hmk σ).comp (continuous_fst.prodMk continuous_const)
    have hc : Continuous (fun z : P × (Fin m → ℂ) ↦
        (⟨projection z.1, a (projection z.1) z.1 rfl z.2⟩ :
          Bundle.TotalSpace Unit (fun b ↦ E b ⊗[ℂ] F b))) := by
      apply (hgen.comp hlift).congr
      intro z
      apply Bundle.TotalSpace.mk_inj.mpr
      change (∑ k : Fin m,
        associatedVectorFiberMkLinearEquiv hP ρ.representation z.1 rfl
            (basis.repr (c.symm z.2) k • bp (finProdFinEquiv.symm k).1) ⊗ₜ[ℂ]
          associatedVectorFiberMkLinearEquiv hP σ.representation z.1 rfl
            (bq (finProdFinEquiv.symm k).2)) = a (projection z.1) z.1 rfl z.2
      let A := TensorProduct.congr
        (associatedVectorFiberMkLinearEquiv hP ρ.representation z.1 rfl)
        (associatedVectorFiberMkLinearEquiv hP σ.representation z.1 rfl)
      calc
        _ = A (∑ k : Fin m, basis.repr (c.symm z.2) k • basis k) := by
          simp only [map_sum, map_smul, basis, Module.Basis.reindex_apply,
            Module.Basis.tensorProduct_apply', A, TensorProduct.congr_tmul,
            TensorProduct.smul_tmul']
        _ = a (projection z.1) z.1 rfl z.2 := by rw [basis.sum_repr]; rfl
    obtain ⟨e, _⟩ := exists_associatedVector_iso_of_covariant_equiv hP (ρ.tensor σ)
      (fun b ↦ E b ⊗[ℂ] F b) a hc ha
    exact (ComplexBundle.kZeroClass_eq_of_iso e).trans ComplexBundle.kZeroClass_tensor
  · -- The trivial action leaves the actual vector coordinate unchanged under every transition.
    let := ComplexBundle.trivialTopology (X := B) 1
    let := ComplexBundle.isFiniteRank_trivial (X := B) 1
    let := isFiniteRank_associatedVector hP
      (FiniteContinuousRepresentation.trivial (G := G)).representation
      (FiniteContinuousRepresentation.trivial (G := G)).continuous_action
    obtain ⟨a, _⟩ := exists_associatedVector_iso_of_covariant_equiv hP
      (FiniteContinuousRepresentation.trivial (G := G))
      (Bundle.Trivial B (Fin 1 → ℂ))
      (fun _ _ _ ↦ LinearEquiv.refl ℂ (Fin 1 → ℂ))
      (by
        apply continuous_induced_rng.mpr
        change Continuous (fun z : P × (Fin 1 → ℂ) ↦ (projection z.1, z.2))
        exact (hP.projection_properties.1.comp continuous_fst).prodMk continuous_snd)
      (by intros; rfl)
    exact (ComplexBundle.kZeroClass_eq_of_iso a).trans (ComplexBundle.kZeroClass_trivial 1)

/-- The fixed associated-bundle classes determine a unique unital ring homomorphism. -/
theorem existsUnique_associatedRepresentationKZero (hP : IsPrincipalBundle G projection) :
    ∃! a : RepresentationGrothendieckGroup G →+* ComplexKZero B,
      ∀ ρ : FiniteContinuousRepresentation G,
        a (finiteRepresentationClass ρ) = associatedKZeroClass hP ρ := by
  /- Stage 1: the isomorphism and direct-sum parts of associatedKZeroClass_relations
  meet exactly the hypotheses of representationGrothendieckGroup_universal_property.
  Obtain the unique additive map whose values are the actual associated classes.
  Stage 2: tensor compatibility proves multiplicativity on pairs of representation
  generators. Both products are the existing biadditive tensor maps, so extend
  through the additive quotient in each variable. The trivial-line clause proves
  preservation of the specified unit. Package this same additive map as a ring map.
  Stage 3: two such ring maps agree on every generator and hence, by the same
  additive universal property, agree everywhere. No irreducible decomposition,
  cancellation of unstabilized representations, or dimension-only invariant is used. -/
  classical
  obtain ⟨hiso, hadd, hmul, hone⟩ := associatedKZeroClass_relations hP
  obtain ⟨a, ha, hunique⟩ := representationGrothendieckGroup_universal_property
    (associatedKZeroClass hP) hiso hadd
  have hext (f g : RepresentationGrothendieckGroup G →+ ComplexKZero B)
      (h : ∀ ρ, f (finiteRepresentationClass ρ) = g (finiteRepresentationClass ρ)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- Extend tensor compatibility through the original additive presentation in both arguments.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      a.comp (representationMul G (finiteRepresentationClass ρ)) =
        { toFun := fun y ↦ associatedKZeroClass hP ρ * a y
          map_zero' := by simp
          map_add' := by intro y z; simp [mul_add] } := by
    apply hext
    intro σ
    simpa only [AddMonoidHom.comp_apply, representationMul_finiteClass, ha,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hmul ρ σ
  have ha_mul (x y : RepresentationGrothendieckGroup G) : a (x * y) = a x * a y := by
    have h : a.comp ((representationMul G).flip y) =
        { toFun := fun z ↦ a z * a y
          map_zero' := by simp
          map_add' := by intro z w; simp [add_mul] } := by
      apply hext
      intro ρ
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply, ha,
        AddMonoidHom.coe_mk, ZeroHom.coe_mk] using DFunLike.congr_fun (hρ ρ) y
    exact DFunLike.congr_fun h x
  let A : RepresentationGrothendieckGroup G →+* ComplexKZero B :=
    { a with
      map_one' := (ha (FiniteContinuousRepresentation.trivial (G := G))).trans hone
      map_mul' := ha_mul }
  refine ⟨A, ha, ?_⟩
  intro c hc
  apply RingHom.toAddMonoidHom_injective
  exact hunique c.toAddMonoidHom hc

/-- SG's a_P, chosen by its unique value on every actual representation generator. -/
def associatedRepresentationKZero (hP : IsPrincipalBundle G projection) :
    RepresentationGrothendieckGroup G →+* ComplexKZero B :=
  Classical.choose (existsUnique_associatedRepresentationKZero hP).exists

/-- The selected map sends each representation to the K class of its original associated bundle. -/
theorem associatedRepresentationKZero_finiteClass (hP : IsPrincipalBundle G projection)
    (ρ : FiniteContinuousRepresentation G) :
    associatedRepresentationKZero hP (finiteRepresentationClass ρ) =
      associatedKZeroClass hP ρ := by
  /- Evaluate the specification of the uniquely characterized selected ring map.
  Its generator value uses exactly the original hP, representation and quotient
  vector bundle; no unrelated bundle or abstract class was chosen instead. -/
  exact (Classical.choose_spec
    (existsUnique_associatedRepresentationKZero hP).exists) ρ

/-- Fiber rank of the associated virtual bundle equals the original dimension augmentation. -/
theorem rankAt_associatedRepresentationKZero (hP : IsPrincipalBundle G projection)
    (b : B) (x : RepresentationGrothendieckGroup G) :
    complexKZeroRankAt b (associatedRepresentationKZero hP x) =
      representationDimension G x := by
  /- Compare the two additive maps on representation generators. For a generator
  ρ, associatedVectorFiberLinearEquiv identifies the actual quotient fiber
  at b with Fin ρ.dimension → ℂ. Its finrank equality gives the rank formula
  after the specified associated-class and rankAt_kZeroClass rewrites.
  Agreement on generators extends through the original additive presentation.
  Fiber rank alone does not determine the associated K class. -/
  -- Compare the actual additive maps on their original representation generators.
  have h : (complexKZeroRankAt b).comp (associatedRepresentationKZero hP).toAddMonoidHom =
      representationDimension G := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    let := isFiniteRank_associatedVector hP ρ.representation ρ.continuous_action
    change complexKZeroRankAt b
      (associatedRepresentationKZero hP (finiteRepresentationClass ρ)) =
      representationDimension G (finiteRepresentationClass ρ)
    rw [associatedRepresentationKZero_finiteClass, associatedKZeroClass,
      ComplexBundle.rankAt_kZeroClass, representationDimension_finiteClass]
    congr 1
    -- The specified quotient fiber has the coordinates of the same representation.
    simpa using (associatedVectorFiberLinearEquiv hP ρ.representation b).finrank_eq
  exact DFunLike.congr_fun h x

end AtiyahSinger
