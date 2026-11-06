/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationGrothendieckGroup
public import AtiyahSinger.Topology.EquivariantSupportTripleKZero
public import AtiyahSinger.Topology.EquivariantTrivialBundle
public import Mathlib.Algebra.Module.PUnit

/-!
# Equivariant supported K theory of a point

Public module ID: M1813.

The original support-triple group over `PUnit` is the representation
Grothendieck group. A finite representation gives its actual product bundle,
zero target bundle and full-point compact control. Conversely, a local linear
trivialization at the unique point is global and transports the original joint
action to a finite continuous representation.

The two presentations impose actual equivariant isomorphism and direct-sum
relations. In particular they do not impose a relation from an arbitrary
family of changing representations. The boundary homotopies in the support
model keep the two equivariant bundles fixed. The point comparison therefore
needs no compactness assumption on the group. It is the coefficient model for
the zero-dimensional equivariant Bott statement, not a positive-dimensional
Bott inverse.

Sources: Atiyah--Singer I, section 2, p.494, and Spin Geometry III.9,
pp.211--212, for the identification of equivariant K theory of a point with
the complex representation ring. The proof below retains the project's
existing two quotient presentations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

-- The existing standard action on PUnit is constant and hence jointly continuous.
private instance pointContinuousSMul : ContinuousSMul G PUnit.{1} where
  continuous_smul := continuous_const

attribute [local instance] trivialTopology isFiniteRank_trivial sumTopology isFiniteRank_sum

/-- Every original equivariant bundle on a point is an actual representation bundle. -/
theorem ComplexBundle.EquivariantStructure.exists_pointRepresentation
    (E : FiniteBundle PUnit.{1}) (σ : EquivariantStructure G E.Fiber) :
    ∃ ρ : FiniteContinuousRepresentation G,
      ∃ e : Iso E.Fiber (FiniteBundle.trivial PUnit.{1} ρ.dimension).Fiber,
        e.IsEquivariant σ (EquivariantStructure.ofFiniteRepresentation ρ) := by
  classical
  -- The given local chart contains the only point, so both chart domains are global.
  obtain ⟨n, t, ht, hlinear⟩ :=
    IsFiniteRank.exists_linear_trivialization (E := E.Fiber) PUnit.unit
  have hbase (x : PUnit.{1}) : x ∈ t.baseSet := by
    cases x
    exact ht
  have htc : Continuous t := continuous_iff_continuousAt.mpr fun z ↦
    t.continuousAt (t.mem_source.mpr (hbase z.proj))
  have hti : Continuous t.toOpenPartialHomeomorph.symm :=
    continuous_iff_continuousAt.mpr fun z ↦
      t.toOpenPartialHomeomorph.symm.continuousAt (t.mem_target.mpr (hbase z.1))
  let e : Iso E.Fiber (FiniteBundle.trivial PUnit.{1} n).Fiber :=
    { linearEquiv x :=
        { toFun := fun v ↦ (t ⟨x, v⟩).2
          invFun := fun v ↦ cast (congrArg E.Fiber (t.proj_symm_apply' (hbase x)))
            (t.toOpenPartialHomeomorph.symm (x, v)).snd
          left_inv := by
            intro v
            rw [cast_eq_iff_heq]
            exact congr_arg_heq (fun z : TotalSpace Unit E.Fiber ↦ z.snd)
              (t.symm_apply_mk_proj (x := ⟨x, v⟩) (t.mem_source.mpr (hbase x)))
          right_inv := by
            intro v
            have hp := TotalSpace.mk_cast (F := Unit) (E := E.Fiber)
              (t.proj_symm_apply' (x := v) (hbase x))
              (t.toOpenPartialHomeomorph.symm (x, v)).snd
            exact (congrArg (fun z : TotalSpace Unit E.Fiber ↦ (t z).2) hp).trans
              (congrArg Prod.snd (t.apply_symm_apply' (hbase x)))
          map_add' := (hlinear x (hbase x)).map_add
          map_smul' := (hlinear x (hbase x)).map_smul }
      continuous_total := by
        apply continuous_induced_rng.mpr
        exact (continuous_proj (E := E.Fiber)).prodMk htc.snd
      continuous_symm := by
        have hc : Continuous (fun z : TotalSpace Unit
            (FiniteBundle.trivial PUnit.{1} n).Fiber ↦ (z.proj, z.snd)) :=
          continuous_induced_dom
        apply (hti.comp hc).congr
        intro z
        exact (TotalSpace.mk_cast (F := Unit) (E := E.Fiber)
          (t.proj_symm_apply' (x := z.snd) (hbase z.proj))
          (t.toOpenPartialHomeomorph.symm (z.proj, z.snd)).snd).symm }
  -- Conjugate the specified action in this same global chart, including the group parameter.
  let q := e.linearEquiv PUnit.unit
  let L (g : G) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    q.toLinearMap.comp ((σ.linearMap g PUnit.unit).comp q.symm.toLinearMap)
  have hσone (v : E.Fiber PUnit.unit) : σ.linearMap 1 PUnit.unit v = v :=
    TotalSpace.mk_injective PUnit.unit (σ.one_map PUnit.unit v)
  have hσmul (g h : G) (v : E.Fiber PUnit.unit) :
      σ.linearMap (g * h) PUnit.unit v =
        σ.linearMap g PUnit.unit (σ.linearMap h PUnit.unit v) :=
    TotalSpace.mk_injective PUnit.unit (σ.mul_map g h PUnit.unit v)
  let a : G →* (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    { toFun g := (L g).toContinuousLinearMap
      map_one' := by
        apply ContinuousLinearMap.ext
        intro v
        change q (σ.linearMap 1 PUnit.unit (q.symm v)) = v
        rw [hσone, q.apply_symm_apply]
      map_mul' := by
        intro g h
        apply ContinuousLinearMap.ext
        intro v
        change q (σ.linearMap (g * h) PUnit.unit (q.symm v)) =
          q (σ.linearMap g PUnit.unit (q.symm (q (σ.linearMap h PUnit.unit (q.symm v)))))
        rw [q.symm_apply_apply, hσmul] }
  have hcoords : Continuous (fun z : TotalSpace Unit
      (FiniteBundle.trivial PUnit.{1} n).Fiber ↦ z.snd) :=
    (show Continuous (fun z : TotalSpace Unit
        (FiniteBundle.trivial PUnit.{1} n).Fiber ↦ (z.proj, z.snd)) from
      continuous_induced_dom).snd
  have hmake : Continuous (fun v : Fin n → ℂ ↦
      (⟨PUnit.unit, v⟩ : TotalSpace Unit (FiniteBundle.trivial PUnit.{1} n).Fiber)) :=
    continuous_induced_rng.mpr (continuous_const.prodMk continuous_id)
  have hjoint : Continuous (fun p : G × (Fin n → ℂ) ↦ a p.1 p.2) :=
    hcoords.comp (e.continuous_total.comp (σ.continuous_action.comp
      (continuous_fst.prodMk ((e.continuous_symm.comp hmake).comp continuous_snd))))
  let ρ : FiniteContinuousRepresentation G :=
    { dimension := n
      representation := .ofMonoidHom a
      continuous_action := hjoint }
  refine ⟨ρ, e, ?_⟩
  intro g x v
  cases x
  change q (σ.linearMap g PUnit.unit v) =
    q (σ.linearMap g PUnit.unit (q.symm (q v)))
  rw [q.symm_apply_apply]

/-- A representation as the original supported triple on a point with zero target bundle. -/
def representationPointTriple (ρ : FiniteContinuousRepresentation G) :
    EquivariantSupportBundleTriple G PUnit.{1} := by
  let E := FiniteBundle.trivial PUnit.{1} ρ.dimension
  let F := FiniteBundle.trivial PUnit.{1} 0
  let z : FiniteContinuousRepresentation G :=
    { dimension := 0
      representation := .ofMonoidHom 1
      continuous_action := continuous_snd }
  let a : CompactSupportTriple E.Fiber F.Fiber :=
    { control := Set.univ
      isCompact_control := isCompact_univ
      boundary :=
        { linearEquiv x := (x.property (Set.mem_univ x.val)).elim
          continuous_total := continuous_of_const fun x _ ↦
            (x.proj.property (Set.mem_univ x.proj.val)).elim
          continuous_symm := continuous_of_const fun x _ ↦
            (x.proj.property (Set.mem_univ x.proj.val)).elim } }
  exact EquivariantSupportBundleTriple.ofBoundary E F a
    (EquivariantStructure.ofFiniteRepresentation ρ)
    (EquivariantStructure.ofFiniteRepresentation z)
    ⟨fun _ _ ↦ Iff.rfl, fun _ x ↦ (x.property (Set.mem_univ x.val)).elim⟩

-- These three adapters retain standard finite coordinate spaces and their original topologies.
private def pointModelIso {m n : ℕ}
    (e : (Fin m → ℂ) ≃L[ℂ] (Fin n → ℂ)) :
    Iso (FiniteBundle.trivial PUnit.{1} m).Fiber
      (FiniteBundle.trivial PUnit.{1} n).Fiber where
  linearEquiv _ := e.toLinearEquiv
  continuous_total := by
    have hc : Continuous (fun z : TotalSpace Unit
        (FiniteBundle.trivial PUnit.{1} m).Fiber ↦ (z.proj, z.snd)) :=
      continuous_induced_dom
    exact continuous_induced_rng.mpr (hc.fst.prodMk (e.continuous.comp hc.snd))
  continuous_symm := by
    have hc : Continuous (fun z : TotalSpace Unit
        (FiniteBundle.trivial PUnit.{1} n).Fiber ↦ (z.proj, z.snd)) :=
      continuous_induced_dom
    exact continuous_induced_rng.mpr (hc.fst.prodMk (e.symm.continuous.comp hc.snd))

private theorem exists_representationPointSumIso (ρ τ : FiniteContinuousRepresentation G) :
    ∃ e : Iso (FiniteBundle.trivial PUnit.{1} (ρ.directSum τ).dimension).Fiber
        ((FiniteBundle.trivial PUnit.{1} ρ.dimension).sum
          (FiniteBundle.trivial PUnit.{1} τ.dimension)).Fiber,
      e.IsEquivariant (EquivariantStructure.ofFiniteRepresentation (ρ.directSum τ))
        ((EquivariantStructure.ofFiniteRepresentation ρ).sum
          (EquivariantStructure.ofFiniteRepresentation τ)) := by
  let c : (Fin (ρ.dimension + τ.dimension) → ℂ) ≃L[ℂ]
      (Fin ρ.dimension → ℂ) × (Fin τ.dimension → ℂ) :=
    (ContinuousLinearEquiv.piCongrLeft ℂ
      (fun _ : Fin ρ.dimension ⊕ Fin τ.dimension ↦ ℂ) finSumFinEquiv.symm).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℂ
        (Fin ρ.dimension) (Fin τ.dimension) (fun _ ↦ ℂ))
  let E := FiniteBundle.trivial PUnit.{1} ρ.dimension
  let F := FiniteBundle.trivial PUnit.{1} τ.dimension
  let H := FiniteBundle.trivial PUnit.{1} (ρ.directSum τ).dimension
  have hE : Continuous (fun z : TotalSpace Unit E.Fiber ↦ (z.proj, z.snd)) :=
    continuous_induced_dom
  have hF : Continuous (fun z : TotalSpace Unit F.Fiber ↦ (z.proj, z.snd)) :=
    continuous_induced_dom
  have hH : Continuous (fun z : TotalSpace Unit H.Fiber ↦ (z.proj, z.snd)) :=
    continuous_induced_dom
  let e : Iso H.Fiber (E.sum F).Fiber :=
    { linearEquiv _ := c.toLinearEquiv
      continuous_total := by
        apply continuous_induced_rng.mpr
        exact (continuous_induced_rng.mpr
          (hH.fst.prodMk ((c.continuous.comp hH.snd).fst))).prodMk
            (continuous_induced_rng.mpr
              (hH.fst.prodMk ((c.continuous.comp hH.snd).snd)))
      continuous_symm := by
        have hp := hE.comp (continuous_sum_fst (E := E.Fiber) (F := F.Fiber))
        have hq := hF.comp (continuous_sum_snd (E := E.Fiber) (F := F.Fiber))
        exact continuous_induced_rng.mpr
          (hp.fst.prodMk (c.symm.continuous.comp (hp.snd.prodMk hq.snd))) }
  refine ⟨e, ?_⟩
  intro g x v
  change c (c.symm (ρ.representation g (c v).1, τ.representation g (c v).2)) = _
  exact c.apply_symm_apply _

private theorem representation_isEquivalent_of_point_iso
    (ρ τ : FiniteContinuousRepresentation G)
    (e : Iso (FiniteBundle.trivial PUnit.{1} ρ.dimension).Fiber
      (FiniteBundle.trivial PUnit.{1} τ.dimension).Fiber)
    (he : e.IsEquivariant (EquivariantStructure.ofFiniteRepresentation ρ)
      (EquivariantStructure.ofFiniteRepresentation τ)) : ρ.IsEquivalent τ := by
  refine ⟨ContRepresentation.Equiv.mk
    (e.linearEquiv PUnit.unit).toContinuousLinearEquiv ?_⟩
  intro g
  apply ContinuousLinearMap.ext
  intro v
  exact he g PUnit.unit v

-- On the compact one-point base, the common full control removes only the exterior condition.
private theorem point_class_eq_of_iso (a b : EquivariantSupportBundleTriple G PUnit.{1})
    (u : Iso a.1.source.Fiber b.1.source.Fiber)
    (v : Iso a.1.target.Fiber b.1.target.Fiber)
    (hu : u.IsEquivariant a.2.sourceAction b.2.sourceAction)
    (hv : v.IsEquivariant a.2.targetAction b.2.targetAction) :
    a.kZeroClass = b.kZeroClass := by
  apply (equivariantSupportTripleKZero_generator_relations (G := G) (X := PUnit.{1})).1
  exact ⟨Set.univ, isCompact_univ, fun _ _ ↦ Iff.rfl,
    Set.subset_univ _, Set.subset_univ _, u, v, hu, hv,
    fun x ↦ (x.property (Set.mem_univ x.val)).elim⟩

/-- The actual representation point triples determine a unique additive coefficient map. -/
theorem existsUnique_representationPointKZero :
    ∃! f : RepresentationGrothendieckGroup G →+
        EquivariantSupportTripleKZero G PUnit.{1},
      ∀ ρ : FiniteContinuousRepresentation G,
        f (finiteRepresentationClass ρ) = (representationPointTriple ρ).kZeroClass := by
  -- Descend the actual representation-bundle construction through its two defining relations.
  apply representationGrothendieckGroup_universal_property
    (fun ρ ↦ (representationPointTriple ρ).kZeroClass)
  · intro ρ τ h
    obtain ⟨e⟩ := h
    apply point_class_eq_of_iso (representationPointTriple ρ) (representationPointTriple τ)
      (pointModelIso e.toContinuousLinearEquiv) (Iso.refl _)
    · intro g x v
      exact DFunLike.congr_fun (e.isIntertwining g) v
    · intro _ _ _
      rfl
  · intro ρ τ
    obtain ⟨e, he⟩ := exists_representationPointSumIso ρ τ
    let Z := FiniteBundle.trivial PUnit.{1} 0
    have h := point_class_eq_of_iso (representationPointTriple (ρ.directSum τ))
      ((representationPointTriple ρ).sum (representationPointTriple τ))
      e Z.sumZeroIso.symm he (by
        intro g x v
        apply Prod.ext
        · funext i
          exact Fin.elim0 (show Fin 0 from i)
        · funext i
          exact Fin.elim0 (show Fin 0 from i))
    exact h.trans
      ((equivariantSupportTripleKZero_generator_relations (G := G) (X := PUnit.{1})).2.1 _ _)

/-- The coefficient map sends each representation to its original supported triple on a point. -/
def representationPointKZero : RepresentationGrothendieckGroup G →+
    EquivariantSupportTripleKZero G PUnit.{1} :=
  Classical.choose (existsUnique_representationPointKZero (G := G)).exists

/-- The coefficient map preserves the actual representation bundle and full-point control. -/
theorem representationPointKZero_finiteClass (ρ : FiniteContinuousRepresentation G) :
    representationPointKZero (finiteRepresentationClass ρ) =
      (representationPointTriple ρ).kZeroClass :=
  (Classical.choose_spec (existsUnique_representationPointKZero (G := G)).exists) ρ

/-- Evaluation of the two original equivariant fibers is inverse to the point coefficient map. -/
theorem representationPointKZero_bijective :
    Function.Bijective (representationPointKZero (G := G)) := by
  classical
  /- Choose finite coordinates for each original point bundle, then show that
  its representation class is independent of those coordinates. Evaluation of
  a triple is the difference of these two classes. The two universal properties
  produce the actual inverse, and global equivariant bundle isomorphisms prove
  both identities on the original generators. -/
  have htrans (E F H : FiniteBundle PUnit.{1})
      (σ : EquivariantStructure G E.Fiber) (τ : EquivariantStructure G F.Fiber)
      (η : EquivariantStructure G H.Fiber) (u : Iso E.Fiber F.Fiber)
      (v : Iso F.Fiber H.Fiber) (hu : u.IsEquivariant σ τ) (hv : v.IsEquivariant τ η) :
      (u.trans v).IsEquivariant σ η := by
    intro g x w
    exact (congrArg (v.linearEquiv (g • x)) (hu g x w)).trans
      (hv g x (u.linearEquiv x w))
  have hsymm (E F : FiniteBundle PUnit.{1})
      (σ : EquivariantStructure G E.Fiber) (τ : EquivariantStructure G F.Fiber)
      (u : Iso E.Fiber F.Fiber) (hu : u.IsEquivariant σ τ) :
      u.symm.IsEquivariant τ σ := by
    intro g x w
    cases x
    apply (u.linearEquiv PUnit.unit).injective
    change u.linearEquiv PUnit.unit ((u.linearEquiv PUnit.unit).symm
        (τ.linearMap g PUnit.unit w)) =
      u.linearEquiv PUnit.unit (σ.linearMap g PUnit.unit
        ((u.linearEquiv PUnit.unit).symm w))
    rw [LinearEquiv.apply_symm_apply]
    have h := hu g PUnit.unit ((u.linearEquiv PUnit.unit).symm w)
    change u.linearEquiv PUnit.unit (σ.linearMap g PUnit.unit
        ((u.linearEquiv PUnit.unit).symm w)) =
      τ.linearMap g PUnit.unit (u.linearEquiv PUnit.unit
        ((u.linearEquiv PUnit.unit).symm w)) at h
    simpa only [LinearEquiv.apply_symm_apply] using h.symm
  choose R e he using fun (E : FiniteBundle PUnit.{1})
    (σ : EquivariantStructure G E.Fiber) ↦
      ComplexBundle.EquivariantStructure.exists_pointRepresentation E σ
  have hmodel (E : FiniteBundle PUnit.{1}) (σ : EquivariantStructure G E.Fiber)
      (ρ : FiniteContinuousRepresentation G)
      (p : Iso E.Fiber (FiniteBundle.trivial PUnit.{1} ρ.dimension).Fiber)
      (hp : p.IsEquivariant σ (EquivariantStructure.ofFiniteRepresentation ρ)) :
      finiteRepresentationClass (R E σ) = finiteRepresentationClass ρ := by
    apply finiteRepresentationClass_eq_of_isEquivalent
    apply representation_isEquivalent_of_point_iso _ _ ((e E σ).symm.trans p)
    exact htrans _ _ _ _ _ _ _ _ (hsymm _ _ _ _ _ (he E σ)) hp
  have hiso (E F : FiniteBundle PUnit.{1})
      (σ : EquivariantStructure G E.Fiber) (τ : EquivariantStructure G F.Fiber)
      (u : Iso E.Fiber F.Fiber) (hu : u.IsEquivariant σ τ) :
      finiteRepresentationClass (R E σ) = finiteRepresentationClass (R F τ) := by
    exact hmodel E σ (R F τ) (u.trans (e F τ))
      (htrans _ _ _ _ _ _ _ _ hu (he F τ))
  have hadd (E F : FiniteBundle PUnit.{1})
      (σ : EquivariantStructure G E.Fiber) (τ : EquivariantStructure G F.Fiber) :
      finiteRepresentationClass (R (E.sum F) (σ.sum τ)) =
        finiteRepresentationClass (R E σ) + finiteRepresentationClass (R F τ) := by
    obtain ⟨p, hp⟩ := exists_representationPointSumIso (R E σ) (R F τ)
    have hsum : (Iso.sum (e E σ) (e F τ)).IsEquivariant (σ.sum τ)
        ((EquivariantStructure.ofFiniteRepresentation (R E σ)).sum
          (EquivariantStructure.ofFiniteRepresentation (R F τ))) := by
      intro g x w
      exact Prod.ext (he E σ g x w.1) (he F τ g x w.2)
    have h := hmodel (E.sum F) (σ.sum τ) ((R E σ).directSum (R F τ))
      ((Iso.sum (e E σ) (e F τ)).trans p.symm)
      (htrans _ _ _ _ _ _ _ _ hsum (hsymm _ _ _ _ _ hp))
    exact h.trans (finiteRepresentationClass_directSum _ _)
  -- The inverse evaluates the two actual fibers and respects exactly the original relations.
  let value (a : EquivariantSupportBundleTriple G PUnit.{1}) :
      RepresentationGrothendieckGroup G :=
    finiteRepresentationClass (R a.1.source a.2.sourceAction) -
      finiteRepresentationClass (R a.1.target a.2.targetAction)
  have hvalue_iso (a b : EquivariantSupportBundleTriple G PUnit.{1})
      (h : a.IsIsomorphic b) : value a = value b := by
    obtain ⟨_, _, _, _, _, u, v, hu, hv, _⟩ := h
    exact congrArg₂ (fun x y : RepresentationGrothendieckGroup G ↦ x - y)
      (hiso _ _ _ _ u hu) (hiso _ _ _ _ v hv)
  have hvalue_sum (a b : EquivariantSupportBundleTriple G PUnit.{1}) :
      value (a.sum b) = value a + value b := by
    change finiteRepresentationClass
        (R (a.1.source.sum b.1.source) (a.2.sourceAction.sum b.2.sourceAction)) -
      finiteRepresentationClass
        (R (a.1.target.sum b.1.target) (a.2.targetAction.sum b.2.targetAction)) = _
    rw [hadd, hadd]
    dsimp only [value]
    abel
  have hvalue_zero (E : FiniteBundle PUnit.{1}) (σ : EquivariantStructure G E.Fiber) :
      value (EquivariantSupportBundleTriple.identity E σ) = 0 := sub_self _
  obtain ⟨inverse, hinverse, _⟩ :=
    equivariantSupportTripleKZero_universal_property value hvalue_iso hvalue_sum hvalue_zero
  let z : FiniteContinuousRepresentation G :=
    { dimension := 0
      representation := .ofMonoidHom 1
      continuous_action := continuous_snd }
  have hz : finiteRepresentationClass z = 0 := by
    have heq : z.IsEquivalent (z.directSum z) := by
      refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
      intro g
      apply ContinuousLinearMap.ext
      intro v
      funext i
      exact Fin.elim0 (show Fin 0 from i)
    have h := finiteRepresentationClass_eq_of_isEquivalent z (z.directSum z) heq
    rw [finiteRepresentationClass_directSum] at h
    exact (add_left_cancel (show finiteRepresentationClass z + 0 =
      finiteRepresentationClass z + finiteRepresentationClass z by simpa using h)).symm
  have hpoint (ρ : FiniteContinuousRepresentation G) :
      value (representationPointTriple ρ) = finiteRepresentationClass ρ := by
    change finiteRepresentationClass
        (R (FiniteBundle.trivial PUnit.{1} ρ.dimension)
          (EquivariantStructure.ofFiniteRepresentation ρ)) -
      finiteRepresentationClass (R (FiniteBundle.trivial PUnit.{1} 0)
        (EquivariantStructure.ofFiniteRepresentation z)) = _
    rw [hmodel _ _ ρ (Iso.refl _) (fun _ _ _ ↦ rfl),
      hmodel _ _ z (Iso.refl _) (fun _ _ _ ↦ rfl), hz, sub_zero]
  have hleft : inverse.comp (representationPointKZero (G := G)) =
      AddMonoidHom.id (RepresentationGrothendieckGroup G) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro ρ
    change inverse (representationPointKZero (finiteRepresentationClass ρ)) =
      finiteRepresentationClass ρ
    rw [representationPointKZero_finiteClass, hinverse, hpoint]
  -- Adding the target-fiber point class recovers the source-fiber point class.
  have hrecover (a : EquivariantSupportBundleTriple G PUnit.{1}) :
      representationPointKZero (value a) = a.kZeroClass := by
    let E := a.1.source
    let F := a.1.target
    let σ := a.2.sourceAction
    let τ := a.2.targetAction
    let p := representationPointTriple (R E σ)
    let q := representationPointTriple (R F τ)
    let i := EquivariantSupportBundleTriple.identity F τ
    have h := point_class_eq_of_iso (a.sum q) (p.sum i)
      (Iso.sum (e E σ) (e F τ).symm)
      (sumCommIso (E := F.Fiber) (F := (FiniteBundle.trivial PUnit.{1} 0).Fiber))
      (by
        intro g x w
        exact Prod.ext (he E σ g x w.1)
          (hsymm _ _ _ _ _ (he F τ) g x w.2))
      (by intro _ _ _; rfl)
    obtain ⟨_, hsum, hidentity⟩ :=
      equivariantSupportTripleKZero_generator_relations (G := G) (X := PUnit.{1})
    rw [hsum, hsum, hidentity, add_zero] at h
    change representationPointKZero
      (finiteRepresentationClass (R E σ) - finiteRepresentationClass (R F τ)) = _
    rw [map_sub, representationPointKZero_finiteClass, representationPointKZero_finiteClass]
    exact (eq_sub_iff_add_eq.mpr h).symm
  have hright : (representationPointKZero (G := G)).comp inverse =
      AddMonoidHom.id (EquivariantSupportTripleKZero G PUnit.{1}) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro a
    change representationPointKZero (inverse a.kZeroClass) = a.kZeroClass
    rw [hinverse]
    exact hrecover a
  exact ⟨(show Function.LeftInverse inverse representationPointKZero from
    fun x ↦ DFunLike.congr_fun hleft x).injective,
    (show Function.RightInverse inverse representationPointKZero from
      fun x ↦ DFunLike.congr_fun hright x).surjective⟩

/-- The coefficient identification on the original equivariant supported K group of a point. -/
def equivariantSupportTripleKZeroPointEquiv :
    EquivariantSupportTripleKZero G PUnit.{1} ≃+ RepresentationGrothendieckGroup G :=
  (AddEquiv.ofBijective (representationPointKZero (G := G))
    representationPointKZero_bijective).symm

/-- The point equivalence recovers the specified representation, not only its dimension. -/
theorem equivariantSupportTripleKZeroPointEquiv_representationPointTriple
    (ρ : FiniteContinuousRepresentation G) :
    equivariantSupportTripleKZeroPointEquiv (representationPointTriple ρ).kZeroClass =
      finiteRepresentationClass ρ := by
  rw [← representationPointKZero_finiteClass]
  exact (AddEquiv.ofBijective (representationPointKZero (G := G))
    representationPointKZero_bijective).symm_apply_apply _

end AtiyahSinger
