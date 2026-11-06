/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRing
public import AtiyahSinger.Topology.EquivariantSupportTensor
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import AtiyahSinger.Topology.EquivariantTrivialBundle

/-!
# The representation-ring action on the original equivariant support group

Public module ID: M1805.

A finite representation acts by tensoring its actual diagonal product bundle
with the original support triple. The original control is unchanged and its
boundary is identity on the representation factor tensored with the old map.
Both quotient presentations are retained. The unique biadditive descent and its
unit and associativity laws assemble the usual R(G)-module structure.

The coefficient is a representation class, not its dimension. Arbitrary
specified equivariant identity stabilizers are allowed in the support group.
No compact group, invariant metric or locally compact base is needed for this
presentation-level action. Local finite rank is already part of its bundles.

Sources: SG III.9 and III.13.6, ASI I section 2, and the ordinary relative-triple
tensor construction. General-group descent is an explicit project supplement.
This does not construct a product of two compactly supported equivariant classes.
The proofs use the specified geometric maps before descending to either quotient;
continuity is checked in the existing finite-rank total-space topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

attribute [local instance] tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum
  trivialTopology isFiniteRank_trivial isFiniteRank_pullback sectionModule

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]

set_option backward.isDefEq.respectTransparency.types false in
/-- Standard coefficient slices test continuity in the original finite tensor topology. -/
private theorem continuous_trivial_tensor_map (n : ℕ) (E F : FiniteBundle X)
    (L : ∀ x, (Fin n → ℂ) ⊗[ℂ] E.Fiber x →ₗ[ℂ] F.Fiber x)
    (hL : ∀ i : Fin n, Continuous (fun z : TotalSpace Unit E.Fiber ↦
      (⟨z.proj, L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd)⟩ : TotalSpace Unit F.Fiber))) :
    Continuous (fun z : TotalSpace Unit ((FiniteBundle.trivial X n).tensor E).Fiber ↦
      (⟨z.proj, L z.proj z.snd⟩ : TotalSpace Unit F.Fiber)) := by
  classical
  -- Test each actual finite-sum generator of the original tensor topology.
  apply continuous_iSup_dom.mpr
  intro m
  apply continuous_coinduced_dom.mpr
  let D := TotalSpace Unit (fun x ↦ (Fin m → Fin n → ℂ) × (Fin m → E.Fiber x))
  let : TopologicalSpace D := TopologicalSpace.induced
    (fun z : D ↦ (z.proj,
      (fun j ↦ (⟨z.proj, z.snd.1 j⟩ :
        TotalSpace Unit (FiniteBundle.trivial X n).Fiber)),
      (fun j ↦ (⟨z.proj, z.snd.2 j⟩ : TotalSpace Unit E.Fiber)))) inferInstance
  have hc : Continuous (fun z : D ↦ (z.proj,
      (fun j ↦ (⟨z.proj, z.snd.1 j⟩ :
        TotalSpace Unit (FiniteBundle.trivial X n).Fiber)),
      (fun j ↦ (⟨z.proj, z.snd.2 j⟩ : TotalSpace Unit E.Fiber)))) := continuous_induced_dom
  let b : C(D, X) := ⟨fun z ↦ z.proj, hc.fst⟩
  have ht : Continuous (fun z : TotalSpace Unit (FiniteBundle.trivial X n).Fiber ↦
      (z.proj, z.snd)) := continuous_induced_dom
  -- Pull the target to the generating domain so its existing section module handles finite sums.
  let σ (j : Fin m) (i : Fin n) : continuousSections ((b : D → X) *ᵖ F.Fiber) :=
    ⟨fun z ↦ L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j), by
      change Continuous (fun z : D ↦
        (⟨z, L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)⟩ :
          TotalSpace Unit ((b : D → X) *ᵖ F.Fiber)))
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber b).continuous_iff]
      exact continuous_id.prodMk ((hL i).comp ((continuous_apply j).comp hc.snd.snd))⟩
  let c (j : Fin m) (i : Fin n) : C(D, ℂ) :=
    ⟨fun z ↦ z.snd.1 j i, (continuous_apply i).comp
      (ht.snd.comp ((continuous_apply j).comp hc.snd.fst))⟩
  let sectionSum : continuousSections ((b : D → X) *ᵖ F.Fiber) :=
    ∑ j : Fin m, ∑ i : Fin n, c j i • σ j i
  have hsum := (Pullback.continuous_lift Unit F.Fiber b).comp sectionSum.property
  apply hsum.congr
  intro z
  change (⟨z.proj, sectionSum.val z⟩ : TotalSpace Unit F.Fiber) =
    ⟨z.proj, L z.proj (∑ j : Fin m, z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j)⟩
  apply congrArg (fun w : F.Fiber z.proj ↦ (⟨z.proj, w⟩ : TotalSpace Unit F.Fiber))
  simp only [sectionSum, Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply]
  change (∑ j : Fin m, ∑ i : Fin n,
    z.snd.1 j i • L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)) =
      L z.proj (∑ j : Fin m, z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j)
  -- Standard finite coordinates reconstruct every coefficient, including rank zero.
  have hcoord (u : Fin n → ℂ) : ∑ i : Fin n, u i • Pi.single i 1 = u := by
    ext i
    simp [Pi.single_apply]
  have hpure (j : Fin m) : ∑ i : Fin n,
      z.snd.1 j i • (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j) =
        z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j := by
    simpa only [TensorProduct.sum_tmul, TensorProduct.smul_tmul'] using
      congrArg (fun u ↦ u ⊗ₜ[ℂ] z.snd.2 j) (hcoord (z.snd.1 j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (by rw [map_sum]; simp only [map_smul] :
    (∑ i : Fin n, z.snd.1 j i • L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)) =
      L z.proj (∑ i : Fin n, z.snd.1 j i • (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j))).trans
        (congrArg (L z.proj) (hpure j))

/-- Tensor the original triple on the left by the given representation's diagonal product bundle. -/
def EquivariantSupportBundleTriple.tensorRepresentation
    (a : EquivariantSupportBundleTriple G X) (ρ : FiniteContinuousRepresentation G) :
    EquivariantSupportBundleTriple G X :=
  EquivariantSupportBundleTriple.tensorLeft (FiniteBundle.trivial X ρ.dimension)
    (EquivariantStructure.ofFiniteRepresentation ρ) a

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual representation tensor construction descends uniquely through both presentations. -/
theorem existsUnique_equivariantSupportRepresentationAction :
    ∃! μ : RepresentationGrothendieckGroup G →+
        EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G X,
      ∀ (ρ : FiniteContinuousRepresentation G) (a : EquivariantSupportBundleTriple G X),
        μ (finiteRepresentationClass ρ) a.kZeroClass =
          (a.tensorRepresentation ρ).kZeroClass := by
  /- Stage 1: fix the original representation rho and its diagonal product
  bundle. tensorLeft_relations preserves the actual equivariant isomorphism,
  sum and identity relations. Descend to the existing support presentation.
  Stage 2: an original equivariant continuous linear equivalence between finite
  representations induces a global bundle isomorphism, tensored with identity
  on the old triple. The same boundary square proves equality of their maps.
  The ordered direct-sum coordinates give a tensor distributivity isomorphism
  commuting with the original boundary, so direct sum acts additively.
  Stage 3: apply the representation group's universal property with the additive
  group of support-group endomorphisms as target. The resulting biadditive map
  has precisely the stated values. Uniqueness in each presentation proves its
  uniqueness on virtual classes. No dimension reduction, semisimplicity or
  assertion that stable classes already form a group is used. -/
  classical
  -- A fixed pure coefficient is one actual generator of the original tensor topology.
  have hpure (n : ℕ) (J : FiniteBundle X) (u : Fin n → ℂ) :
      Continuous (fun z : TotalSpace Unit J.Fiber ↦
        (⟨z.proj, u ⊗ₜ[ℂ] z.snd⟩ :
          TotalSpace Unit ((FiniteBundle.trivial X n).tensor J).Fiber)) := by
    let D := TotalSpace Unit (fun x ↦ (Fin 1 → Fin n → ℂ) × (Fin 1 → J.Fiber x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ :
          TotalSpace Unit (FiniteBundle.trivial X n).Fiber)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit J.Fiber)))) inferInstance
    have hg : Continuous (fun z : D ↦
        (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
          TotalSpace Unit ((FiniteBundle.trivial X n).tensor J).Fiber)) :=
      continuous_iSup_rng (i := 1) continuous_coinduced_rng
    let f (z : TotalSpace Unit J.Fiber) : D := ⟨z.proj, fun _ ↦ u, fun _ ↦ z.snd⟩
    have hf : Continuous f := by
      apply continuous_induced_rng.mpr
      refine (continuous_proj (E := J.Fiber)).prodMk
        ((continuous_pi ?_).prodMk (continuous_pi (fun _ ↦ continuous_id)))
      intro _
      exact continuous_induced_rng.mpr ((continuous_proj (E := J.Fiber)).prodMk continuous_const)
    apply (hg.comp hf).congr
    intro z
    simp only [Function.comp_apply, f, Fin.sum_univ_one]
  have hboundary (ρ : FiniteContinuousRepresentation G)
      (a : EquivariantSupportBundleTriple G X) (K : Set X) (hK : IsCompact K)
      (ha : a.1.datum.control ⊆ K) (x : (Kᶜ : Set X))
      (u : Fin ρ.dimension → ℂ) (v : a.1.source.Fiber x) :
      (((a.tensorRepresentation ρ).1.datum).enlarge K hK ha).boundary.linearEquiv x
          (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] (a.1.datum.enlarge K hK ha).boundary.linearEquiv x v := by
    have hl := (a.tensorRepresentation ρ).1.datum.enlarge_apply K hK ha x (u ⊗ₜ[ℂ] v)
    have hp := RelativeTriple.tensorLeft_tmul
      (FiniteBundle.trivial X ρ.dimension).Fiber a.1.datum.boundary
      ⟨x.val, fun h ↦ x.property (ha h)⟩ u v
    have hr := a.1.datum.enlarge_apply K hK ha x v
    exact hl.trans (hp.trans (congrArg (fun v : a.1.target.Fiber x ↦ u ⊗ₜ[ℂ] v) hr).symm)
  -- Equivalent representations give a genuine equivariant boundary square.
  have hiso (ρ σ : FiniteContinuousRepresentation G) (h : ρ.IsEquivalent σ)
      (a : EquivariantSupportBundleTriple G X) :
      (a.tensorRepresentation ρ).kZeroClass = (a.tensorRepresentation σ).kZeroClass := by
    obtain ⟨e⟩ := h
    -- The actual representation intertwiner acts on the original product bundle coordinates.
    let c : Iso (FiniteBundle.trivial X ρ.dimension).Fiber
        (FiniteBundle.trivial X σ.dimension).Fiber :=
      { linearEquiv _ := e.toContinuousLinearEquiv.toLinearEquiv
        continuous_total := by
          have hc : Continuous (fun z : TotalSpace Unit
              (FiniteBundle.trivial X ρ.dimension).Fiber ↦ (z.proj, z.snd)) :=
            continuous_induced_dom
          exact continuous_induced_rng.mpr
            (hc.fst.prodMk (e.toContinuousLinearEquiv.continuous.comp hc.snd))
        continuous_symm := by
          have hc : Continuous (fun z : TotalSpace Unit
              (FiniteBundle.trivial X σ.dimension).Fiber ↦ (z.proj, z.snd)) :=
            continuous_induced_dom
          exact continuous_induced_rng.mpr
            (hc.fst.prodMk (e.toContinuousLinearEquiv.symm.continuous.comp hc.snd)) }
    have hc : c.IsEquivariant (EquivariantStructure.ofFiniteRepresentation ρ)
        (EquivariantStructure.ofFiniteRepresentation σ) := by
      intro g x v
      exact DFunLike.congr_fun (e.isIntertwining g) v
    apply equivariantSupportTripleKZero_generator_relations.1
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, Set.Subset.refl _, Set.Subset.refl _,
      c.tensor (Iso.refl a.1.source.Fiber), c.tensor (Iso.refl a.1.target.Fiber),
      (EquivariantStructure.tensor_maps _ _ _ _).2 c (Iso.refl a.1.source.Fiber)
        hc (fun _ _ _ ↦ rfl),
      (EquivariantStructure.tensor_maps _ _ _ _).2 c (Iso.refl a.1.target.Fiber)
        hc (fun _ _ _ ↦ rfl), ?_⟩
    intro x w
    have hm : ((c.tensor (Iso.refl a.1.target.Fiber)).linearEquiv x).toLinearMap.comp
          (((a.tensorRepresentation ρ).1.datum.enlarge a.1.datum.control
            a.1.datum.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap =
        (((a.tensorRepresentation σ).1.datum.enlarge a.1.datum.control
          a.1.datum.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap.comp
          ((c.tensor (Iso.refl a.1.source.Fiber)).linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro u v
      exact (congrArg ((c.tensor (Iso.refl a.1.target.Fiber)).linearEquiv x)
        (hboundary ρ a _ _ (Set.Subset.refl _) x u v)).trans
          (hboundary σ a a.1.datum.control a.1.datum.isCompact_control
            (Set.Subset.refl _) x (e.toContinuousLinearEquiv u) v).symm
    exact DFunLike.congr_fun hm w
  -- Keep the exact ordered direct-sum coordinate equivalence used by the representation ring.
  let d (ρ σ : FiniteContinuousRepresentation G) :
      (Fin (ρ.dimension + σ.dimension) → ℂ) ≃ₗ[ℂ]
        (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) :=
    ((ContinuousLinearEquiv.piCongrLeft ℂ
      (fun _ : Fin ρ.dimension ⊕ Fin σ.dimension ↦ ℂ) finSumFinEquiv.symm).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin ρ.dimension) (Fin σ.dimension)
        (fun _ ↦ ℂ))).toLinearEquiv
  have hd (ρ σ : FiniteContinuousRepresentation G) (g : G)
      (v : Fin (ρ.dimension + σ.dimension) → ℂ) :
      d ρ σ ((ρ.directSum σ).representation g v) =
        (ρ.representation g (d ρ σ v).1, σ.representation g (d ρ σ v).2) := by
    change d ρ σ ((d ρ σ).symm _) = _
    exact (d ρ σ).apply_symm_apply _
  have compare (ρ σ : FiniteContinuousRepresentation G)
      (J : FiniteBundle X) (τ : EquivariantStructure G J.Fiber) :
      ∃ e : Iso ((FiniteBundle.trivial X (ρ.directSum σ).dimension).tensor J).Fiber
          (((FiniteBundle.trivial X ρ.dimension).tensor J).sum
            ((FiniteBundle.trivial X σ.dimension).tensor J)).Fiber,
        (∀ x u v, e.linearEquiv x (u ⊗ₜ[ℂ] v) =
          ((d ρ σ u).1 ⊗ₜ[ℂ] v, (d ρ σ u).2 ⊗ₜ[ℂ] v)) ∧
        e.IsEquivariant ((EquivariantStructure.ofFiniteRepresentation (ρ.directSum σ)).tensor τ)
          (((EquivariantStructure.ofFiniteRepresentation ρ).tensor τ).sum
            ((EquivariantStructure.ofFiniteRepresentation σ).tensor τ)) := by
    let c (x : X) := (TensorProduct.congr (d ρ σ) (LinearEquiv.refl ℂ (J.Fiber x))).trans
      (TensorProduct.prodLeft ℂ ℂ _ _ _)
    let B := ((FiniteBundle.trivial X ρ.dimension).tensor J).sum
      ((FiniteBundle.trivial X σ.dimension).tensor J)
    let f : Hom ((FiniteBundle.trivial X (ρ.directSum σ).dimension).tensor J).Fiber B.Fiber :=
      { linearMap x := (c x).toLinearMap
        continuous_total := by
          apply continuous_trivial_tensor_map (ρ.directSum σ).dimension J B
            (fun x ↦ (c x).toLinearMap)
          intro i
          exact continuous_induced_rng.mpr
            ((hpure ρ.dimension J (d ρ σ (Pi.single i 1)).1).prodMk
              (hpure σ.dimension J (d ρ σ (Pi.single i 1)).2)) }
    let e := f.toIso (fun x ↦ (c x).bijective)
    refine ⟨e, (fun _ _ _ ↦ rfl), ?_⟩
    intro g x w
    have hm : (e.linearEquiv (g • x)).toLinearMap.comp
          (((EquivariantStructure.ofFiniteRepresentation (ρ.directSum σ)).tensor τ).linearMap
            g x) =
        ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor τ).sum
          ((EquivariantStructure.ofFiniteRepresentation σ).tensor τ)).linearMap g x).comp
            (e.linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro u v
      change ((d ρ σ ((ρ.directSum σ).representation g u)).1 ⊗ₜ[ℂ] τ.linearMap g x v,
        (d ρ σ ((ρ.directSum σ).representation g u)).2 ⊗ₜ[ℂ] τ.linearMap g x v) = _
      rw [hd]
      rfl
    exact DFunLike.congr_fun hm w
  have hadd (ρ σ : FiniteContinuousRepresentation G) (a : EquivariantSupportBundleTriple G X) :
      (a.tensorRepresentation (ρ.directSum σ)).kZeroClass =
        (a.tensorRepresentation ρ).kZeroClass + (a.tensorRepresentation σ).kZeroClass := by
    obtain ⟨u, hu, hueq⟩ := compare ρ σ a.1.source a.2.sourceAction
    obtain ⟨v, hv, hveq⟩ := compare ρ σ a.1.target a.2.targetAction
    have hi : (a.tensorRepresentation (ρ.directSum σ)).IsIsomorphic
        ((a.tensorRepresentation ρ).sum (a.tensorRepresentation σ)) := by
      let K := a.1.datum.control
      have hK : IsCompact K := a.1.datum.isCompact_control
      refine ⟨K, hK, a.2.isEquivariant.invariant_control, Set.Subset.refl _,
        Set.union_subset (Set.Subset.refl _) (Set.Subset.refl _), u, v, hueq, hveq, ?_⟩
      intro x w
      have hm : (v.linearEquiv x).toLinearMap.comp
            (((a.tensorRepresentation (ρ.directSum σ)).1.datum.enlarge K hK
              (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap =
          ((((a.tensorRepresentation ρ).sum (a.tensorRepresentation σ)).1.datum.enlarge K hK
            (Set.union_subset (Set.Subset.refl _) (Set.Subset.refl _))).boundary.linearEquiv
              x).toLinearMap.comp (u.linearEquiv x).toLinearMap := by
        apply TensorProduct.ext'
        intro e w
        have hl := (congrArg (v.linearEquiv x)
          (hboundary (ρ.directSum σ) a K hK (Set.Subset.refl _) x e w)).trans (hv x e _)
        have ha := hboundary ρ a K hK (Set.Subset.refl _) x (d ρ σ e).1 w
        have hb := hboundary σ a K hK (Set.Subset.refl _) x (d ρ σ e).2 w
        have hr : (((a.tensorRepresentation ρ).sum (a.tensorRepresentation σ)).1.datum.enlarge
            K hK (Set.union_subset (Set.Subset.refl _) (Set.Subset.refl _))).boundary.linearEquiv
            x (u.linearEquiv x (e ⊗ₜ[ℂ] w)) =
          ((((a.tensorRepresentation ρ).1.datum.enlarge K hK
            (Set.Subset.refl _)).boundary.linearEquiv x ((d ρ σ e).1 ⊗ₜ[ℂ] w)),
           (((a.tensorRepresentation σ).1.datum.enlarge K hK
            (Set.Subset.refl _)).boundary.linearEquiv x ((d ρ σ e).2 ⊗ₜ[ℂ] w))) := by
          rw [hu]
          simp only [EquivariantSupportBundleTriple.sum, SupportBundleTriple.sum,
            SupportBundleTriple.ofBoundary, CompactSupportTriple.enlarge,
            CompactSupportTriple.sum, Iso.restrictTo_apply, RelativeTriple.sum_apply]
          rfl
        exact hl.trans ((congrArg₂ Prod.mk ha hb).symm.trans hr.symm)
      exact DFunLike.congr_fun hm w
    exact (equivariantSupportTripleKZero_generator_relations.1 _ _ hi).trans
      (equivariantSupportTripleKZero_generator_relations.2.1 _ _)
  have hext
      (f g : EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G X)
      (h : ∀ a : EquivariantSupportBundleTriple G X, f a.kZeroClass = g a.kZeroClass) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- First descend the actual tensor triple in its support argument.
  have hrelations (ρ : FiniteContinuousRepresentation G) :=
    EquivariantSupportBundleTriple.tensorLeft_relations
      (FiniteBundle.trivial X ρ.dimension) (EquivariantStructure.ofFiniteRepresentation ρ)
  have hvIso (ρ : FiniteContinuousRepresentation G) (a b : EquivariantSupportBundleTriple G X)
      (h : a.IsIsomorphic b) :
      (a.tensorRepresentation ρ).kZeroClass = (b.tensorRepresentation ρ).kZeroClass :=
    equivariantSupportTripleKZero_generator_relations.1 _ _ ((hrelations ρ).1 a b h)
  have hvAdd (ρ : FiniteContinuousRepresentation G) (a b : EquivariantSupportBundleTriple G X) :
      ((a.sum b).tensorRepresentation ρ).kZeroClass =
        (a.tensorRepresentation ρ).kZeroClass + (b.tensorRepresentation ρ).kZeroClass :=
    (equivariantSupportTripleKZero_generator_relations.1 _ _
      ((hrelations ρ).2.2.1 a b)).trans
        (equivariantSupportTripleKZero_generator_relations.2.1 _ _)
  have hvZero (ρ : FiniteContinuousRepresentation G)
      (E : FiniteBundle X) (τ : EquivariantStructure G E.Fiber) :
      ((EquivariantSupportBundleTriple.identity E τ).tensorRepresentation ρ).kZeroClass = 0 :=
    (equivariantSupportTripleKZero_generator_relations.1 _ _
      ((hrelations ρ).2.2.2 E τ)).trans
        (equivariantSupportTripleKZero_generator_relations.2.2 _ _)
  let v (ρ : FiniteContinuousRepresentation G) :
      EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G X :=
    (equivariantSupportTripleKZero_universal_property
      (fun a ↦ (a.tensorRepresentation ρ).kZeroClass) (hvIso ρ) (hvAdd ρ) (hvZero ρ)).choose
  have hv (ρ : FiniteContinuousRepresentation G) (a : EquivariantSupportBundleTriple G X) :
      v ρ a.kZeroClass = (a.tensorRepresentation ρ).kZeroClass :=
    (equivariantSupportTripleKZero_universal_property
      (fun a ↦ (a.tensorRepresentation ρ).kZeroClass)
      (hvIso ρ) (hvAdd ρ) (hvZero ρ)).choose_spec.1 a
  have hviso (ρ σ : FiniteContinuousRepresentation G) (h : ρ.IsEquivalent σ) : v ρ = v σ := by
    apply hext
    intro a
    exact (hv ρ a).trans ((hiso ρ σ h a).trans (hv σ a).symm)
  have hvadd (ρ σ : FiniteContinuousRepresentation G) : v (ρ.directSum σ) = v ρ + v σ := by
    apply hext
    intro a
    exact (hv (ρ.directSum σ) a).trans
      ((hadd ρ σ a).trans (congrArg₂ (· + ·) (hv ρ a) (hv σ a)).symm)
  -- Then descend in the representation argument through its original split presentation.
  obtain ⟨μ, hμ, hμunique⟩ := representationGrothendieckGroup_universal_property v hviso hvadd
  refine ⟨μ, ?_, ?_⟩
  · intro ρ a
    rw [hμ]
    exact hv ρ a
  · intro ν hν
    apply hμunique
    intro ρ
    apply hext
    intro a
    exact (hν ρ a).trans (hv ρ a).symm

/-- The specified biadditive action on the two existing quotient groups. -/
def equivariantSupportRepresentationAction :
    RepresentationGrothendieckGroup G →+
      EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G X :=
  Classical.choose (existsUnique_equivariantSupportRepresentationAction (G := G) (X := X)).exists

/-- On generators the action is the original tensor triple with the entire representation action. -/
theorem equivariantSupportRepresentationAction_finiteClass
    (ρ : FiniteContinuousRepresentation G) (a : EquivariantSupportBundleTriple G X) :
    equivariantSupportRepresentationAction (finiteRepresentationClass ρ) a.kZeroClass =
      (a.tensorRepresentation ρ).kZeroClass := by
  /- Read the generator equation from the same unique biadditive witness used
  in the definition. The representation factor keeps its original dimension,
  continuous action and product topology; its action is not replaced by trivial
  scalar multiplicity merely because the underlying bundle is trivial. -/
  exact (Classical.choose_spec
    (existsUnique_equivariantSupportRepresentationAction (G := G) (X := X)).exists) ρ a

set_option backward.isDefEq.respectTransparency.types false in
/-- Tensor associativity and the trivial-line unitor give the module laws for this same action. -/
theorem equivariantSupportRepresentationAction_laws :
    (∀ a : EquivariantSupportTripleKZero G X,
      equivariantSupportRepresentationAction (1 : RepresentationGrothendieckGroup G) a = a) ∧
    ∀ (r s : RepresentationGrothendieckGroup G) (a : EquivariantSupportTripleKZero G X),
      equivariantSupportRepresentationAction (r * s) a =
        equivariantSupportRepresentationAction r (equivariantSupportRepresentationAction s a) := by
  /- Stage 1: for actual representations rho and sigma, the canonical tensor
  associator identifies (V_rho tensor V_sigma) tensor E with V_rho tensor
  (V_sigma tensor E). Use the same tensorCoordinates from the representation
  ring to identify its finite tensor model. The tensor_tmul formula makes
  these actual global maps equivariant; they preserve the original boundary
  and compact control, so the two support generators agree.
  Stage 2: the ring unit is the one-dimensional trivial representation. Its
  scalar unitor is equivariant and carries identity tensor boundary to the
  old boundary. This identifies the unit-twisted generator with the original.
  Stage 3: the specified generator formula and additivity extend both laws
  through all three input groups. Finite-sum tensor generators give forward
  continuity; the existing finite-rank inverse theorem gives continuity of
  the inverse, including zero and varying finite ranks. The two laws give
  the module structure without adding quotient relations. -/
  classical
  -- A fixed pure coefficient is one actual generator of the original tensor topology.
  have hpure (n : ℕ) (J : FiniteBundle X) (u : Fin n → ℂ) :
      Continuous (fun z : TotalSpace Unit J.Fiber ↦
        (⟨z.proj, u ⊗ₜ[ℂ] z.snd⟩ :
          TotalSpace Unit ((FiniteBundle.trivial X n).tensor J).Fiber)) := by
    let D := TotalSpace Unit (fun x ↦ (Fin 1 → Fin n → ℂ) × (Fin 1 → J.Fiber x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ :
          TotalSpace Unit (FiniteBundle.trivial X n).Fiber)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit J.Fiber)))) inferInstance
    have hg : Continuous (fun z : D ↦
        (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
          TotalSpace Unit ((FiniteBundle.trivial X n).tensor J).Fiber)) :=
      continuous_iSup_rng (i := 1) continuous_coinduced_rng
    let f (z : TotalSpace Unit J.Fiber) : D := ⟨z.proj, fun _ ↦ u, fun _ ↦ z.snd⟩
    have hf : Continuous f := by
      apply continuous_induced_rng.mpr
      refine (continuous_proj (E := J.Fiber)).prodMk
        ((continuous_pi ?_).prodMk (continuous_pi (fun _ ↦ continuous_id)))
      intro _
      exact continuous_induced_rng.mpr ((continuous_proj (E := J.Fiber)).prodMk continuous_const)
    apply (hg.comp hf).congr
    intro z
    simp only [Function.comp_apply, f, Fin.sum_univ_one]
  have hboundary (ρ : FiniteContinuousRepresentation G)
      (a : EquivariantSupportBundleTriple G X) (K : Set X) (hK : IsCompact K)
      (ha : a.1.datum.control ⊆ K) (x : (Kᶜ : Set X))
      (u : Fin ρ.dimension → ℂ) (v : a.1.source.Fiber x) :
      (((a.tensorRepresentation ρ).1.datum).enlarge K hK ha).boundary.linearEquiv x
          (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] (a.1.datum.enlarge K hK ha).boundary.linearEquiv x v := by
    have hl := (a.tensorRepresentation ρ).1.datum.enlarge_apply K hK ha x (u ⊗ₜ[ℂ] v)
    have hp := RelativeTriple.tensorLeft_tmul
      (FiniteBundle.trivial X ρ.dimension).Fiber a.1.datum.boundary
      ⟨x.val, fun h ↦ x.property (ha h)⟩ u v
    have hr := a.1.datum.enlarge_apply K hK ha x v
    exact hl.trans (hp.trans (congrArg (fun v : a.1.target.Fiber x ↦ u ⊗ₜ[ℂ] v) hr).symm)
  -- Construct the scalar unitor on the same total spaces and diagonal actions.
  have unitCompare (J : FiniteBundle X) (τ : EquivariantStructure G J.Fiber) :
      ∃ e : Iso ((FiniteBundle.trivial X 1).tensor J).Fiber J.Fiber,
        (∀ x u v, e.linearEquiv x (u ⊗ₜ[ℂ] v) = u 0 • v) ∧
        e.IsEquivariant ((EquivariantStructure.ofFiniteRepresentation
          (FiniteContinuousRepresentation.trivial (G := G))).tensor τ) τ := by
    let c (x : X) := (TensorProduct.congr
      (LinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ))
      (LinearEquiv.refl ℂ (J.Fiber x))).trans (TensorProduct.lid ℂ (J.Fiber x))
    let f : Hom ((FiniteBundle.trivial X 1).tensor J).Fiber J.Fiber :=
      { linearMap x := (c x).toLinearMap
        continuous_total := by
          apply continuous_trivial_tensor_map 1 J J (fun x ↦ (c x).toLinearMap)
          intro i
          convert (continuous_id : Continuous (fun z : TotalSpace Unit J.Fiber ↦ z)) using 1
          funext z
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          simp [c, LinearEquiv.piUnique] }
    let e := f.toIso (fun x ↦ (c x).bijective)
    refine ⟨e, (fun _ _ _ ↦ rfl), ?_⟩
    intro g x w
    have hm : (e.linearEquiv (g • x)).toLinearMap.comp
          (((EquivariantStructure.ofFiniteRepresentation
            (FiniteContinuousRepresentation.trivial (G := G))).tensor τ).linearMap g x) =
        (τ.linearMap g x).comp (e.linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro u v
      change Fin 1 → ℂ at u
      change u 0 • τ.linearMap g x v = τ.linearMap g x (u 0 • v)
      exact (map_smul (τ.linearMap g x) (u 0) v).symm
    exact DFunLike.congr_fun hm w
  have hone (a : EquivariantSupportBundleTriple G X) :
      (a.tensorRepresentation (FiniteContinuousRepresentation.trivial (G := G))).kZeroClass =
        a.kZeroClass := by
    obtain ⟨u, hu, hueq⟩ := unitCompare a.1.source a.2.sourceAction
    obtain ⟨v, hv, hveq⟩ := unitCompare a.1.target a.2.targetAction
    apply equivariantSupportTripleKZero_generator_relations.1
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, Set.Subset.refl _, Set.Subset.refl _,
      u, v, hueq, hveq, ?_⟩
    intro x w
    let b := (a.1.datum.enlarge a.1.datum.control
      a.1.datum.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv x
    have hm : (v.linearEquiv x).toLinearMap.comp
          (((a.tensorRepresentation
            (FiniteContinuousRepresentation.trivial (G := G))).1.datum.enlarge
            a.1.datum.control a.1.datum.isCompact_control
            (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap =
        b.toLinearMap.comp (u.linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro t z
      change Fin 1 → ℂ at t
      have hb := hboundary (FiniteContinuousRepresentation.trivial (G := G)) a
        a.1.datum.control a.1.datum.isCompact_control (Set.Subset.refl _) x t z
      exact (congrArg (v.linearEquiv x) hb).trans
        ((hv x t (b z)).trans ((map_smul b (t 0) z).symm.trans
          (congrArg b (hu x t z)).symm))
    exact DFunLike.congr_fun hm w
  -- Tensor coordinates and the canonical associator identify the actual iterated bundle.
  have assocCompare (ρ σ : FiniteContinuousRepresentation G)
      (J : FiniteBundle X) (τ : EquivariantStructure G J.Fiber) :
      ∃ e : Iso ((FiniteBundle.trivial X (ρ.tensor σ).dimension).tensor J).Fiber
          ((FiniteBundle.trivial X ρ.dimension).tensor
            ((FiniteBundle.trivial X σ.dimension).tensor J)).Fiber,
        (∀ x u v w, e.linearEquiv x
          (FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
            (u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)) ∧
        e.IsEquivariant ((EquivariantStructure.ofFiniteRepresentation (ρ.tensor σ)).tensor τ)
          ((EquivariantStructure.ofFiniteRepresentation ρ).tensor
            ((EquivariantStructure.ofFiniteRepresentation σ).tensor τ)) := by
    let d := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
    let B := (FiniteBundle.trivial X ρ.dimension).tensor
      ((FiniteBundle.trivial X σ.dimension).tensor J)
    let c (x : X) := (TensorProduct.congr d.symm (LinearEquiv.refl ℂ (J.Fiber x))).trans
      (TensorProduct.assoc ℂ _ _ _)
    have hcoord (i : Fin (ρ.dimension * σ.dimension)) :
        d.symm (Pi.single i 1) =
          Pi.single (finProdFinEquiv.symm i).1 1 ⊗ₜ[ℂ]
            Pi.single (finProdFinEquiv.symm i).2 1 := by
      apply d.injective
      rw [d.apply_symm_apply]
      ext j
      simp only [d, FiniteContinuousRepresentation.tensorCoordinates,
        LinearEquiv.trans_apply, Module.Basis.equivFun_apply]
      change (Pi.single i (1 : ℂ) : Fin (ρ.dimension * σ.dimension) → ℂ) j =
        (Equiv.piCongrLeft (fun _ : Fin (ρ.dimension * σ.dimension) ↦ ℂ) finProdFinEquiv)
          (((Pi.basisFun ℂ (Fin ρ.dimension)).tensorProduct (Pi.basisFun ℂ (Fin σ.dimension))).repr
            (Pi.single (finProdFinEquiv.symm i).1 1 ⊗ₜ[ℂ]
              Pi.single (finProdFinEquiv.symm i).2 1)) j
      simp [Equiv.piCongrLeft_apply, Module.Basis.tensorProduct_repr_tmul_apply,
        Pi.basisFun_repr, Pi.single_apply]
      by_cases h : j = i
      · subst j
        simp
      · have hpair : finProdFinEquiv.symm j ≠ finProdFinEquiv.symm i :=
          fun he ↦ h (finProdFinEquiv.symm.injective he)
        by_cases h₁ : j.divNat = i.divNat
        · have h₂ : j.modNat ≠ i.modNat := fun h₂ ↦ hpair (Prod.ext h₁ h₂)
          simp [h, h₁, h₂]
        · simp [h, h₁]
    let f : Hom ((FiniteBundle.trivial X (ρ.tensor σ).dimension).tensor J).Fiber B.Fiber :=
      { linearMap x := (c x).toLinearMap
        continuous_total := by
          apply continuous_trivial_tensor_map (ρ.tensor σ).dimension J B
            (fun x ↦ (c x).toLinearMap)
          intro i
          change Fin (ρ.dimension * σ.dimension) at i
          have h := (hpure ρ.dimension ((FiniteBundle.trivial X σ.dimension).tensor J)
            (Pi.single (finProdFinEquiv.symm i).1 1)).comp
              (hpure σ.dimension J (Pi.single (finProdFinEquiv.symm i).2 1))
          apply h.congr
          intro z
          apply congrArg (fun t : B.Fiber z.proj ↦
            (⟨z.proj, t⟩ : TotalSpace Unit B.Fiber))
          change _ = c z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd)
          simp only [c, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
            LinearEquiv.refl_apply, hcoord, TensorProduct.assoc_tmul] }
    let e := f.toIso (fun x ↦ (c x).bijective)
    have heval (x : X) (u : Fin ρ.dimension → ℂ) (v : Fin σ.dimension → ℂ)
        (w : J.Fiber x) : e.linearEquiv x (d (u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) =
          u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
      change c x (d (u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = _
      simp only [c, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
        LinearEquiv.symm_apply_apply, LinearEquiv.refl_apply, TensorProduct.assoc_tmul]
    refine ⟨e, heval, ?_⟩
    intro g x w
    have hm : (e.linearEquiv (g • x)).toLinearMap.comp
          (((EquivariantStructure.ofFiniteRepresentation (ρ.tensor σ)).tensor τ).linearMap g x) =
        (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
          ((EquivariantStructure.ofFiniteRepresentation σ).tensor τ)).linearMap g x).comp
            (e.linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro t z
      change Fin (ρ.dimension * σ.dimension) → ℂ at t
      let A : B.Fiber x →ₗ[ℂ] B.Fiber (g • x) :=
        ((EquivariantStructure.ofFiniteRepresentation ρ).tensor
          ((EquivariantStructure.ofFiniteRepresentation σ).tensor τ)).linearMap g x
      simp only [LinearMap.comp_apply, EquivariantStructure.tensor, TensorProduct.map_tmul,
        EquivariantStructure.ofFiniteRepresentation]
      change e.linearEquiv (g • x)
        ((ρ.tensor σ).representation g t ⊗ₜ[ℂ] τ.linearMap g x z) =
          A (e.linearEquiv x (t ⊗ₜ[ℂ] z))
      let L : (Fin (ρ.dimension * σ.dimension) → ℂ) →ₗ[ℂ] B.Fiber (g • x) :=
        (e.linearEquiv (g • x)).toLinearMap.comp
        (((TensorProduct.mk ℂ (Fin (ρ.dimension * σ.dimension) → ℂ)
          (J.Fiber (g • x))).flip (τ.linearMap g x z)).comp
            ((ρ.tensor σ).representation g).toLinearMap)
      let R : (Fin (ρ.dimension * σ.dimension) → ℂ) →ₗ[ℂ] B.Fiber (g • x) :=
        A.comp ((e.linearEquiv x).toLinearMap.comp
          ((TensorProduct.mk ℂ (Fin (ρ.dimension * σ.dimension) → ℂ) (J.Fiber x)).flip z))
      have hinner : L.comp d.toLinearMap = R.comp d.toLinearMap := by
        apply TensorProduct.ext'
        intro u v
        dsimp only [L, R, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
        have hd := FiniteContinuousRepresentation.tensor_tmul ρ σ g u v
        change (ρ.tensor σ).representation g (d (u ⊗ₜ[ℂ] v)) =
          d (ρ.representation g u ⊗ₜ[ℂ] σ.representation g v) at hd
        exact (congrArg (fun t : Fin (ρ.dimension * σ.dimension) → ℂ ↦
          e.linearEquiv (g • x) (t ⊗ₜ[ℂ] τ.linearMap g x z)) hd).trans
            ((heval (g • x) (ρ.representation g u) (σ.representation g v)
              (τ.linearMap g x z)).trans (congrArg A (heval x u v z)).symm)
      have hLR : L = R := (LinearMap.cancel_right d.surjective).mp hinner
      have h := DFunLike.congr_fun hLR t
      dsimp only [L, R, LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply] at h
      exact h
    exact DFunLike.congr_fun hm w
  have hassoc (ρ σ : FiniteContinuousRepresentation G) (a : EquivariantSupportBundleTriple G X) :
      (a.tensorRepresentation (ρ.tensor σ)).kZeroClass =
        ((a.tensorRepresentation σ).tensorRepresentation ρ).kZeroClass := by
    obtain ⟨u, hu, hueq⟩ := assocCompare ρ σ a.1.source a.2.sourceAction
    obtain ⟨v, hv, hveq⟩ := assocCompare ρ σ a.1.target a.2.targetAction
    apply equivariantSupportTripleKZero_generator_relations.1
    refine ⟨a.1.datum.control, a.1.datum.isCompact_control,
      a.2.isEquivariant.invariant_control, Set.Subset.refl _, Set.Subset.refl _,
      u, v, hueq, hveq, ?_⟩
    intro x w
    let K := a.1.datum.control
    have hK : IsCompact K := a.1.datum.isCompact_control
    let d := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
    let b := (a.1.datum.enlarge K hK (Set.Subset.refl _)).boundary.linearEquiv x
    have hm : (v.linearEquiv x).toLinearMap.comp
          (((a.tensorRepresentation (ρ.tensor σ)).1.datum.enlarge K hK
            (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap =
        ((((a.tensorRepresentation σ).tensorRepresentation ρ).1.datum.enlarge K hK
          (Set.Subset.refl _)).boundary.linearEquiv x).toLinearMap.comp
            (u.linearEquiv x).toLinearMap := by
      apply TensorProduct.ext'
      intro t z
      change Fin (ρ.dimension * σ.dimension) → ℂ at t
      let bL := ((a.tensorRepresentation (ρ.tensor σ)).1.datum.enlarge K hK
        (Set.Subset.refl _)).boundary.linearEquiv x
      let bR := (((a.tensorRepresentation σ).tensorRepresentation ρ).1.datum.enlarge K hK
        (Set.Subset.refl _)).boundary.linearEquiv x
      change v.linearEquiv x (bL (t ⊗ₜ[ℂ] z)) = bR (u.linearEquiv x (t ⊗ₜ[ℂ] z))
      obtain ⟨y, rfl⟩ := d.surjective t
      induction y using TensorProduct.inductionOn with
      | tmul p q =>
        have h₁ := hboundary (ρ.tensor σ) a K hK (Set.Subset.refl _) x (d (p ⊗ₜ[ℂ] q)) z
        have h₂ := hboundary ρ (a.tensorRepresentation σ) K hK (Set.Subset.refl _)
          x p (q ⊗ₜ[ℂ] z)
        have h₃ := hboundary σ a K hK (Set.Subset.refl _) x q z
        have hright := h₂.trans (congrArg (fun t :
          ((FiniteBundle.trivial X σ.dimension).tensor a.1.target).Fiber x ↦
            p ⊗ₜ[ℂ] t) h₃)
        exact (congrArg (v.linearEquiv x) h₁).trans
          ((hv x p q (b z)).trans (hright.symm.trans
            (congrArg bR (hu x p q z)).symm))
      | add y₁ y₂ h₁ h₂ =>
        let L := (v.linearEquiv x).toLinearMap.comp bL.toLinearMap
        let R := bR.toLinearMap.comp (u.linearEquiv x).toLinearMap
        have hsum : d (y₁ + y₂) ⊗ₜ[ℂ] z = d y₁ ⊗ₜ[ℂ] z + d y₂ ⊗ₜ[ℂ] z :=
          (congrArg (fun t : Fin (ρ.dimension * σ.dimension) → ℂ ↦ t ⊗ₜ[ℂ] z)
            (d.map_add y₁ y₂)).trans (TensorProduct.add_tmul _ _ _)
        exact ((congrArg L hsum).trans (L.map_add _ _)).trans
          ((congrArg₂ (· + ·) h₁ h₂).trans
            ((congrArg R hsum).trans (R.map_add _ _)).symm)
    exact DFunLike.congr_fun hm w
  have hext (f g : EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G X)
      (h : ∀ a : EquivariantSupportBundleTriple G X, f a.kZeroClass = g a.kZeroClass) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  have hrext (f g : RepresentationGrothendieckGroup G →+ EquivariantSupportTripleKZero G X)
      (h : ∀ ρ, f (finiteRepresentationClass ρ) = g (finiteRepresentationClass ρ)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  let μ := equivariantSupportRepresentationAction (G := G) (X := X)
  -- Extend the geometric equations through the existing presentations, one argument at a time.
  refine ⟨?_, ?_⟩
  · intro a
    have h : μ (1 : RepresentationGrothendieckGroup G) =
        AddMonoidHom.id (EquivariantSupportTripleKZero G X) := by
      apply hext
      intro t
      change equivariantSupportRepresentationAction
        (finiteRepresentationClass (FiniteContinuousRepresentation.trivial (G := G)))
          t.kZeroClass = t.kZeroClass
      rw [equivariantSupportRepresentationAction_finiteClass]
      exact hone t
    exact DFunLike.congr_fun h a
  · intro r s a
    have h₃ (ρ σ : FiniteContinuousRepresentation G) :
        μ (representationMul G (finiteRepresentationClass ρ) (finiteRepresentationClass σ)) =
          (μ (finiteRepresentationClass ρ)).comp (μ (finiteRepresentationClass σ)) := by
      apply hext
      intro t
      simpa only [μ, AddMonoidHom.comp_apply, representationMul_finiteClass,
        equivariantSupportRepresentationAction_finiteClass] using hassoc ρ σ t
    have h₂ (ρ : FiniteContinuousRepresentation G) :
        (μ.flip a).comp (representationMul G (finiteRepresentationClass ρ)) =
          (μ (finiteRepresentationClass ρ)).comp (μ.flip a) := by
      apply hrext
      intro σ
      exact DFunLike.congr_fun (h₃ ρ σ) a
    have h₁ : (μ.flip a).comp ((representationMul G).flip s) = μ.flip (μ s a) := by
      apply hrext
      intro ρ
      exact DFunLike.congr_fun (h₂ ρ) s
    exact DFunLike.congr_fun h₁ r


/-- The usual R(G)-module structure keeps the existing addition and specified tensor action. -/
instance moduleEquivariantSupportTripleKZero :
    Module (RepresentationGrothendieckGroup G) (EquivariantSupportTripleKZero G X) where
  smul r a := equivariantSupportRepresentationAction r a
  one_smul := equivariantSupportRepresentationAction_laws.1
  mul_smul := equivariantSupportRepresentationAction_laws.2
  smul_add r := (equivariantSupportRepresentationAction r).map_add
  smul_zero r := (equivariantSupportRepresentationAction r).map_zero
  add_smul r s a := congrArg
    (fun f : EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G X ↦ f a)
    (equivariantSupportRepresentationAction.map_add r s)
  zero_smul a := congrArg
    (fun f : EquivariantSupportTripleKZero G X →+ EquivariantSupportTripleKZero G X ↦ f a)
    equivariantSupportRepresentationAction.map_zero

end AtiyahSinger.ComplexBundle
