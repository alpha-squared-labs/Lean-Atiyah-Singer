/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleThom
public import AtiyahSinger.Topology.KTheoryLocalToGlobal
public import AtiyahSinger.Topology.ThomNaturality
public import AtiyahSinger.Topology.TrivialBundleThom
public import Mathlib.Topology.ShrinkingLemma

/-!
# K-orientations and the Bott periodicity property

Public module ID: M1914.

SG C.2 and C.6 concern one specified degree-zero class on a bundle over a compact
base. It must give the prescribed multiplication isomorphism in every nonpositive
degree. The predicates below express these componentwise isomorphisms using the
actual suspended graph action. They do not replace the original class with a
chosen generator or identify all degrees with degree zero.

The Bott property tests every closed subset over which the original bundle is
trivial. The class restricts along the actual closed total-space inclusion. We use
the inverse-image subtype of the original total space, canonically homeomorphic
to the total space of the restricted bundle, to keep the restriction map literal.

SG C.7 is the one-generator case of KA IV.1.3. SG C.8 applies it to the original
exterior Thom class, and the degree-zero comparison returns the specified
compact-base Thom homomorphism. The C.7 criterion is proved below from
the completed finite closed descent theorem, using the same class in every degree.
The actual exterior class satisfies the Bott property in every nonpositive degree.
The resulting graded equivalence recovers the specified compact-base homomorphism.
Noncompact-base Thom bijectivity remains separate from this compact-base comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] trivialTopology t2Space_totalSpace locallyCompactSpace_totalSpace

section FiniteBundle

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- SG C.2: the same class generates the prescribed Thom isomorphism in every degree -n. -/
def IsKOrientation (u : CompactSupportKZero (TotalSpace Unit E)) : Prop :=
  ∀ n : ℕ, Function.Bijective
    ((compactSupportKAction n (⟨π Unit E, continuous_proj (E := E)⟩ :
      C(TotalSpace Unit E, X))).flip u)

/-- SG C.6: the restricted class is an orientation on every closed trivializing subset. -/
def HasBottPeriodicityProperty (u : CompactSupportKZero (TotalSpace Unit E)) : Prop :=
  ∀ (C : Set X) (hC : IsClosed C),
    (∃ r : ℕ, Nonempty (Iso (Restrict E C) (Bundle.Trivial C (Fin r → ℂ)))) →
    letI := hC.locallyCompactSpace
    letI := (hC.preimage (continuous_proj (E := E))).locallyCompactSpace
    ∀ n : ℕ, Function.Bijective
      ((compactSupportKAction n
        (preimageSubspaceMap C ⟨π Unit E, continuous_proj (E := E)⟩)).flip
          (compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
            (hC.preimage (continuous_proj (E := E))).isProperMap_subtypeVal u))

/-- SG C.7: the Bott periodicity property makes the specified class a K-orientation. -/
theorem isKOrientation_of_hasBottPeriodicityProperty
    (u : CompactSupportKZero (TotalSpace Unit E)) (hu : HasBottPeriodicityProperty E u) :
    IsKOrientation E u := by
  /- Stage 1: compact Hausdorff X is normal. Shrink a finite cover by original
  finite linear bundle charts to a finite closed cover subordinate to those
  charts. On each closed cover member the restricted bundle is trivial, and the
  same remains true on every closed subset, including rank-zero chart domains.
  Stage 2: apply the one-generator case of
  compactSupportKLerayHirschMap_bijective_of_closed_cover. The actual closed
  total-space inclusion restricts u, and the restricted projection is exactly
  preimageSubspaceMap in the Bott property. Thus hu supplies every local degree.
  Stage 3: evaluation on the unique index identifies the one-generator source
  with CompactSupportK n X, and its finite sum is the prescribed action on u.
  The conclusion for every n is precisely IsKOrientation E u. The descent theorem uses full graded
  Mayer--Vietoris exactness and compatibility with the specified boundary maps. -/
  classical
  -- Choose a finite cover by the original linear charts, retaining their local ranks.
  choose r e he hlinear using IsFiniteRank.exists_linear_trivialization (E := E)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (e x).baseSet) (fun x ↦ (e x).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, he x⟩)
  let index : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  let U (i : Fin (Fintype.card t)) : Set X := (e (index i).val).baseSet
  have hU (i : Fin (Fintype.card t)) : IsOpen (U i) := (e (index i).val).open_baseSet
  have hcoverU : ⋃ i, U i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    refine Set.mem_iUnion.mpr ⟨index.symm ⟨j, hj⟩, ?_⟩
    change x ∈ (e (index (index.symm ⟨j, hj⟩)).val).baseSet
    rw [index.apply_symm_apply]
    exact hx
  -- Normality supplies a closed refinement; every closed subset stays in the same chart.
  obtain ⟨W, hcoverW, hW, hWU⟩ := exists_iUnion_eq_closed_subset hU
    (fun _ ↦ Set.toFinite _) hcoverU
  have trivial_on_subset (i : Fin (Fintype.card t)) (C : Set X) (hCW : C ⊆ W i) :
      ∃ s : ℕ, Nonempty (Iso (Restrict E C) (Bundle.Trivial C (Fin s → ℂ))) := by
    let j : X := (index i).val
    have hchart (x : C) : x.val ∈ (e j).baseSet := hWU i (hCW x.property)
    -- The actual chart and its inverse provide linear coordinates in each original fiber.
    let coord (x : C) : E x.val ≃ₗ[ℂ] (Fin (r j) → ℂ) :=
      { toFun := fun v ↦ ((e j) ⟨x.val, v⟩).2
        invFun := fun w ↦ cast (congrArg E ((e j).proj_symm_apply' (hchart x)))
          ((e j).toOpenPartialHomeomorph.symm (x.val, w)).2
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.2)
            ((e j).symm_apply_mk_proj (x := ⟨x.val, v⟩)
              ((e j).mem_source.mpr (hchart x)))
        right_inv := by
          intro w
          have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
            ((e j).proj_symm_apply' (x := w) (hchart x))
            ((e j).toOpenPartialHomeomorph.symm (x.val, w)).2
          exact (congrArg (fun z : TotalSpace Unit E ↦ ((e j) z).2) hpoint).trans
            (congrArg Prod.snd ((e j).apply_symm_apply' (hchart x)))
        map_add' := (hlinear j x.val (hchart x)).map_add
        map_smul' := (hlinear j x.val (hchart x)).map_smul }
    let q : Hom (Restrict E C) (Bundle.Trivial C (Fin (r j) → ℂ)) :=
      { linearMap x := (coord x).toLinearMap
        continuous_total := by
          have hc : Continuous (fun z : TotalSpace Unit (Restrict E C) ↦
              (e j) ⟨z.proj.val, z.snd⟩) := by
            apply continuous_iff_continuousAt.mpr
            intro z
            exact ((e j).continuousAt ((e j).mem_source.mpr (hchart z.proj))).comp
              (Pullback.continuous_lift Unit E (Subtype.val : C → X)).continuousAt
          apply continuous_induced_rng.mpr
          exact (Pullback.continuous_proj Unit E (Subtype.val : C → X)).prodMk hc.snd }
    -- Finite-rank inversion proves continuity on the unchanged restricted topology.
    let := isFiniteRank_restrict (E := E) C
    let := isFiniteRank_trivial (X := C) (r j)
    exact ⟨r j, ⟨q.toIso (fun x ↦ (coord x).bijective)⟩⟩
  -- Evaluation at the only index identifies the original finite sum with this graph action.
  have one_generator {P Q : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      (k : ℕ) (v : C(Q, P)) (b : CompactSupportKZero Q) :
      Function.Bijective (compactSupportKLerayHirschMap k v (fun _ : Fin 1 ↦ b)) ↔
        Function.Bijective ((compactSupportKAction k v).flip b) := by
    have hsum (a : Fin 1 → CompactSupportK k P) :
        compactSupportKLerayHirschMap k v (fun _ : Fin 1 ↦ b) a =
          ((compactSupportKAction k v).flip b) (a 0) := by
      change (∑ i : Fin 1, compactSupportKAction k v (a i) b) =
        compactSupportKAction k v (a 0) b
      simp
    constructor
    · intro h
      constructor
      · intro a a' haa'
        have hconst : (fun _ : Fin 1 ↦ a) = (fun _ : Fin 1 ↦ a') :=
          h.injective (by simpa only [hsum] using haa')
        exact congrFun hconst 0
      · intro z
        obtain ⟨a, ha⟩ := h.surjective z
        exact ⟨a 0, (hsum a).symm.trans ha⟩
    · intro h
      constructor
      · intro a a' haa'
        have hzero : a 0 = a' 0 :=
          h.injective (by simpa only [hsum] using haa')
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        simpa only [hj] using hzero
      · intro z
        obtain ⟨a, ha⟩ := h.surjective z
        exact ⟨fun _ ↦ a, (hsum (fun _ ↦ a)).trans ha⟩
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj (E := E)⟩
  have hlocal (i : Fin (Fintype.card t)) (C : Set X) (hC : IsClosed C)
      (hCW : C ⊆ W i) :
      letI := hC.locallyCompactSpace
      letI := (hC.preimage p.continuous).locallyCompactSpace
      ∀ k : ℕ, Function.Bijective
        (compactSupportKLerayHirschMap k (preimageSubspaceMap C p)
          (fun _ : Fin 1 ↦ compactSupportKZeroPullback
            ⟨Subtype.val, continuous_subtype_val⟩
            (hC.preimage p.continuous).isProperMap_subtypeVal u)) := by
    let := hC.locallyCompactSpace
    let := (hC.preimage p.continuous).locallyCompactSpace
    intro k
    exact (one_generator k (preimageSubspaceMap C p) _).mpr
      (hu C hC (trivial_on_subset i C hCW) k)
  intro n
  exact (one_generator n p u).mp
    (compactSupportKLerayHirschMap_bijective_of_closed_cover
      p (fun _ : Fin 1 ↦ u) W hW hcoverW hlocal n)

end FiniteBundle

section Hermitian

attribute [local instance] sumTopology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Compare the same supported operators under restriction and arbitrary bundle isomorphism.
/-- The original exterior Thom class has SG C.6's Bott property in all nonpositive degrees. -/
theorem exteriorThomClass_hasBottPeriodicityProperty :
    HasBottPeriodicityProperty E (exteriorThomClass E hinner) := by
  /- Restrict the actual supported operator to the closed base, and transport it
  through the supplied linear trivialization. Metric independence permits that
  trivialization without assuming it is unitary. On the standard Hermitian
  model, the original suspended graph is precisely the exterior Bott product. -/
  classical
  let one (Y : Type _) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] :
      CompactSupportKZero Y :=
    (compactSupportKZeroCompactEquiv Y).symm
      (AtiyahSinger.kZeroClass C(Y, ℂ) (IdempotentMatrix.identity C(Y, ℂ) 1))
  -- Compact-unit pullback is computed by the original finite-point restriction.
  have unit_pullback {Y W : Type _} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
      [TopologicalSpace W] [CompactSpace W] [T2Space W]
      (f : C(Y, W)) (hf : IsProperMap f) :
      compactSupportKZeroPullback f hf (one W) = one Y := by
    have finite_pullback (a : CompactSupportKZero W) :
        compactSupportKZeroToAbsolute (compactSupportKZeroPullback f hf a) =
          complexKZeroPullback f (compactSupportKZeroToAbsolute a) := by
      change complexKZeroPullback
        ⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩
          (complexKZeroPullback (properOnePointMap f hf) a.val) =
        complexKZeroPullback f (complexKZeroPullback
          ⟨((↑) : W → OnePoint W), OnePoint.continuous_coe⟩ a.val)
      simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      rfl
    apply (compactSupportKZeroCompactEquiv Y).injective
    change compactSupportKZeroToAbsolute (compactSupportKZeroPullback f hf (one W)) =
      (compactSupportKZeroCompactEquiv Y) (one Y)
    rw [finite_pullback]
    change complexKZeroPullback f ((compactSupportKZeroCompactEquiv W) (one W)) =
      (compactSupportKZeroCompactEquiv Y) (one Y)
    simp only [one, AddEquiv.apply_symm_apply]
    change kZeroMap _ (AtiyahSinger.kZeroClass _ _) = _
    rw [kZeroMap_class]
    congr 1
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
    congr 1
    exact map_one _
  -- On compact bases, the supported operator evaluated at this unit is the actual class.
  have thom_unit {Y : Type _} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
      (F : Y → Type _) [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
      (hh : Continuous (fun z : TotalSpace Unit (F ×ᵇ F) ↦ inner ℂ z.snd.1 z.snd.2)) :
      (ContinuousHermitianMetric.ofInnerProduct F hh).supportedThomHom (one Y) =
        exteriorThomClass F hh := by
    rw [ContinuousHermitianMetric.supportedThomHom_ofInnerProduct, supportedThomHom_compact]
    change exteriorThomHom F hh ((compactSupportKZeroCompactEquiv Y) (one Y)) = _
    simp only [one, AddEquiv.apply_symm_apply]
    exact complexKZeroCompactSupportAction_one _ _
  intro C hC htriv
  let := hC.isClosedEmbedding_subtypeVal.compactSpace
  let := hC.locallyCompactSpace
  let Z := TotalSpace Unit E
  let D := (π Unit E) ⁻¹' C
  have hD : IsClosed D := hC.preimage (continuous_proj (E := E))
  let := hD.locallyCompactSpace
  let R := Restrict E C
  let := isFiniteRank_restrict (E := E) C
  let f : C(C, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : IsProperMap f := hC.isClosedEmbedding_subtypeVal.isProperMap
  let hE := ContinuousHermitianMetric.ofInnerProduct E hinner
  let hR := hE.pullback f
  obtain ⟨r, ⟨e₀⟩⟩ := htriv
  let V := EuclideanSpace ℂ (Fin r)
  let T := Bundle.Trivial C V
  let := modelTopology V T
  let := isFiniteRank_model V T
  let eT := (unitTotalHomeomorph V T).trans (Bundle.Trivial.homeomorphProd C V)
  have hT : Continuous (fun z : TotalSpace Unit (T ×ᵇ T) ↦ inner ℂ z.snd.1 z.snd.2) :=
    (eT.continuous.snd.comp (continuous_sum_fst (E := T) (F := T))).inner
      (eT.continuous.snd.comp (continuous_sum_snd (E := T) (F := T)))
  let metricT := ContinuousHermitianMetric.ofInnerProduct T hT
  let := isFiniteRank_trivial (X := C) r
  let coord : (Fin r → ℂ) ≃L[ℂ] V := (EuclideanSpace.equiv (Fin r) ℂ).symm
  let toModel : Hom (Bundle.Trivial C (Fin r → ℂ)) T :=
    { linearMap := fun _ ↦ coord.toLinearMap
      continuous_total := by
        have hc : Continuous (fun z : TotalSpace Unit (Bundle.Trivial C (Fin r → ℂ)) ↦
            (z.proj, z.snd)) := continuous_induced_dom
        exact eT.symm.continuous.comp (hc.fst.prodMk (coord.continuous.comp hc.snd)) }
  let e₁ := toModel.toIso (fun _ ↦ coord.bijective)
  let e := e₀.trans e₁
  -- This homeomorphism retains every original base point and vector in the restricted bundle.
  let j : TotalSpace Unit R ≃ₜ D :=
    { toFun z := ⟨⟨z.proj.val, z.snd⟩, z.proj.property⟩
      invFun z := ⟨⟨z.val.proj, z.property⟩, z.val.snd⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun :=
        (Pullback.continuous_lift Unit E (Subtype.val : C → X)).subtype_mk _
      continuous_invFun := by
        apply (inducing_pullbackTotalSpaceEmbedding Unit E (Subtype.val : C → X)).continuous_iff.mpr
        exact (((continuous_proj (E := E)).comp continuous_subtype_val).subtype_mk _).prodMk
          continuous_subtype_val }
  let H := e.totalHomeomorph.symm.trans j
  let i : C(D, Z) := ⟨Subtype.val, continuous_subtype_val⟩
  have hi : IsProperMap i := hD.isClosedEmbedding_subtypeVal.isProperMap
  let μ := pullbackTotalMap E f
  have hμ : IsProperMap μ := (pullbackTotalMap_properties E f).1 hf
  let ψ : C(TotalSpace Unit T, TotalSpace Unit R) :=
    ⟨e.totalHomeomorph.symm, e.totalHomeomorph.symm.continuous⟩
  let η : C(TotalSpace Unit T, D) := ⟨H, H.continuous⟩
  have hsource : hE.supportedThomHom (one X) = exteriorThomClass E hinner :=
    thom_unit E hinner
  have hrestricted : hR.supportedThomHom (one C) =
      compactSupportKZeroPullback μ hμ (exteriorThomClass E hinner) := by
    have h := DFunLike.congr_fun (hE.supportedThomHom_pullback f hf) (one X)
    change hR.supportedThomHom (compactSupportKZeroPullback f hf (one X)) =
      compactSupportKZeroPullback μ hμ (hE.supportedThomHom (one X)) at h
    rw [unit_pullback f hf, hsource] at h
    exact h
  have hmodel : metricT.supportedThomHom (one C) = exteriorThomClass T hT := by
    rw [ContinuousHermitianMetric.supportedThomHom_ofInnerProduct, supportedThomHom_compact]
    change exteriorThomHom T hT ((compactSupportKZeroCompactEquiv C) (one C)) = _
    simp only [one, AddEquiv.apply_symm_apply]
    exact complexKZeroCompactSupportAction_one _ _
  have hiso : compactSupportKZeroPullback ψ e.totalHomeomorph.symm.isProperMap
      (hR.supportedThomHom (one C)) = metricT.supportedThomHom (one C) :=
    DFunLike.congr_fun (ContinuousHermitianMetric.supportedThomHom_iso hR metricT e) (one C)
  let u := compactSupportKZeroPullback i hi (exteriorThomClass E hinner)
  have hclass : compactSupportKZeroPullback η H.isProperMap u = exteriorThomClass T hT := by
    -- Compose the two actual restrictions, then use the same base-change and bundle-iso squares.
    change compactSupportKZeroPullback η H.isProperMap
      (compactSupportKZeroPullback i hi (exteriorThomClass E hinner)) = _
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    have hcomp := DFunLike.congr_fun
      (compactSupportKZeroPullback_comp ψ μ e.totalHomeomorph.symm.isProperMap hμ)
        (exteriorThomClass E hinner)
    -- Both composites carry (x,v) to the same original vector over x.
    have hfirst : compactSupportKZeroPullback (i.comp η) (hi.comp H.isProperMap)
        (exteriorThomClass E hinner) =
      compactSupportKZeroPullback ψ e.totalHomeomorph.symm.isProperMap
        (compactSupportKZeroPullback μ hμ (exteriorThomClass E hinner)) := by
      exact hcomp
    exact hfirst.trans ((congrArg
      (compactSupportKZeroPullback ψ e.totalHomeomorph.symm.isProperMap) hrestricted.symm).trans
        (hiso.trans hmodel))
  let p : C(D, C) := preimageSubspaceMap C ⟨π Unit E, continuous_proj (E := E)⟩
  let pT : C(TotalSpace Unit T, C) := ⟨π Unit T, continuous_proj⟩
  have hbase : p.comp η = pT := by
    apply ContinuousMap.ext
    intro z
    rfl
  intro n
  let G := compactSupportKHomeomorphEquiv n H.symm
  have hbij : Function.Bijective ((compactSupportKAction n pT).flip
      (exteriorThomClass T hT)) := exteriorThomClass_trivial_action_bijective (X := C) V hT n
  have hsquare (a : CompactSupportK n C) :
      G (compactSupportKAction n p a u) =
        compactSupportKAction n pT a (exteriorThomClass T hT) := by
    change compactSupportKPullback n η H.isProperMap
      (compactSupportKAction n p a u) = _
    rw [compactSupportKPullback_action, hclass, hbase]
  -- A homeomorphism detects equality and transports surjectivity of the actual suspended action.
  constructor
  · intro a b hab
    apply hbij.injective
    exact (hsquare a).symm.trans ((congrArg G hab).trans (hsquare b))
  · intro b
    obtain ⟨a, ha⟩ := hbij.surjective (G b)
    refine ⟨a, G.injective ?_⟩
    exact (hsquare a).trans ha

/-- SG C.8: the specified exterior class is a complex K-theory orientation. -/
theorem exteriorThomClass_isKOrientation :
    IsKOrientation E (exteriorThomClass E hinner) := by
  /- Apply SG C.7 to exteriorThomClass_hasBottPeriodicityProperty. Both predicates
  retain the identical exterior class and graph action in every degree -n.
  This is the full nonpositive-degree conclusion of C.8 for the given metric,
  including the original fixed degree-zero comparison. -/
  exact isKOrientation_of_hasBottPeriodicityProperty E _
    (exteriorThomClass_hasBottPeriodicityProperty E hinner)

/-- The graded Thom equivalence has the actual suspended graph action as its forward map. -/
def exteriorThomGradedEquiv (n : ℕ) :
    CompactSupportK n X ≃+ CompactSupportK n (TotalSpace Unit E) :=
  AddEquiv.ofBijective
    ((compactSupportKAction n ⟨π Unit E, continuous_proj (E := E)⟩).flip
      (exteriorThomClass E hinner))
    (exteriorThomClass_isKOrientation E hinner n)

/-- The fixed zero-degree coordinates recover the original compact-base Thom homomorphism. -/
theorem exteriorThomGradedEquiv_zero (a : CompactSupportK 0 X) :
    compactSupportKZeroDegreeEquiv (TotalSpace Unit E) (exteriorThomGradedEquiv E hinner 0 a) =
      exteriorThomHom E hinner
        (compactSupportKZeroCompactEquiv X (compactSupportKZeroDegreeEquiv X a)) := by
  /- Stage 1: expand exteriorThomGradedEquiv only to its specified forward map.
  Apply compactSupportKAction_zero to the same projection and exterior class.
  The result is the original unsuspended compact-support graph action.
  Stage 2: exteriorThomHom uses the compact-to-absolute comparison in the other
  direction to define its K(X) action. Cancel that comparison with its inverse.
  The resulting value is the displayed Thom homomorphism on the same input.
  No Bott generator or coordinate equivalence is chosen independently. -/
  change compactSupportKZeroDegreeEquiv (TotalSpace Unit E)
      (compactSupportKAction 0 ⟨π Unit E, continuous_proj (E := E)⟩ a
        (exteriorThomClass E hinner)) = _
  rw [compactSupportKAction_zero]
  change compactSupportKZeroAction _ (compactSupportKZeroDegreeEquiv X a) _ =
    compactSupportKZeroAction _
      ((compactSupportKZeroCompactEquiv X).symm
        ((compactSupportKZeroCompactEquiv X) (compactSupportKZeroDegreeEquiv X a))) _
  rw [AddEquiv.symm_apply_apply]

end Hermitian

section CompactThom

attribute [local instance] sumTopology


variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]
  (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2))
  [CompactSpace X] [T2Space X]

/-- The compact-base complex Thom theorem for the prescribed exterior-symbol homomorphism. -/
theorem exteriorThomHom_bijective : Function.Bijective (exteriorThomHom E hinner) := by
  /- The graded Thom equivalence already uses the actual exterior class and graph
  action. Its degree-zero comparison identifies it with this prescribed map
  through the fixed source and target coordinates. Transport its bijectivity
  through those exact coordinates; no new Thom class or inverse is chosen. -/
  let source := (compactSupportKZeroDegreeEquiv X).trans (compactSupportKZeroCompactEquiv X)
  let target := compactSupportKZeroDegreeEquiv (TotalSpace Unit E)
  let thom := exteriorThomGradedEquiv E hinner 0
  have hcompare (a : CompactSupportK 0 X) :
      target (thom a) = exteriorThomHom E hinner (source a) :=
    exteriorThomGradedEquiv_zero E hinner a
  constructor
  · -- The same source coordinate and the graded equivalence detect equality.
    intro a b hab
    apply source.symm.injective
    apply thom.injective
    apply target.injective
    simpa only [hcompare, AddEquiv.apply_symm_apply] using hab
  · -- Lift through the target coordinate, then the graded equivalence.
    intro b
    obtain ⟨a, ha⟩ := thom.surjective (target.symm b)
    refine ⟨source a, ?_⟩
    rw [← hcompare, ha, AddEquiv.apply_symm_apply]

/-- The compact-base Thom equivalence retains the specified exterior-symbol map as forward map. -/
def exteriorThomEquiv : ComplexKZero X ≃+ CompactSupportKZero (TotalSpace Unit E) :=
  AddEquiv.ofBijective (exteriorThomHom E hinner) (exteriorThomHom_bijective E hinner)

end CompactThom

end AtiyahSinger.ComplexBundle
