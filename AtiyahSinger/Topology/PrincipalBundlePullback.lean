/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedBundle

/-!
# Actual pullbacks of principal and associated bundles

Public module ID: M2001.

The principal pullback is the subtype of X times the original P cut out by
f(x)=projection(p), with its native subspace topology. The original right
action fixes x and acts on p. Both projections are actual coordinate maps.
Local triviality is pulled back from the original principal charts.

The associated comparison is the actual quotient map
[ ((x,p),v) ] ↦ (x,[p,v]) into the ordinary fiber-product subtype for the
original associated bundle. It is a homeomorphism over X. Its construction
uses the unchanged right/left action convention and quotient topologies.

HU IV.4 Proposition 4.1, printed p.44 / PDF p.65, constructs the principal
fiber product with this action. HU IV.6 Proposition 6.3, printed p.47 / PDF p.68,
gives the inverse associated comparison (x,[p,v]) ↦ [((x,p),v)]. The locally
trivial principal-bundle convention is SG Appendix A, pp.370--372. No global
Hausdorffness, paracompactness or group compactness is needed by these local
constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y P : Type*}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace P]

/-- The actual fiber product of the original principal projection with a continuous base map. -/
abbrev PrincipalBundlePullback (f : C(X, Y)) (projection : P → Y) : Type _ :=
  {z : X × P // f z.1 = projection z.2}

/-- The pullback projection is the first coordinate, with the original subtype topology. -/
def principalBundlePullbackProjection (f : C(X, Y)) (projection : P → Y) :
    C(PrincipalBundlePullback f projection, X) where
  toFun z := z.1.1
  continuous_toFun := continuous_subtype_val.fst

/-- The canonical map to the original principal total space is the second coordinate. -/
def principalBundlePullbackLift (f : C(X, Y)) (projection : P → Y) :
    C(PrincipalBundlePullback f projection, P) where
  toFun z := z.1.2
  continuous_toFun := continuous_subtype_val.snd

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P]
  {projection : P → Y} [hP : IsPrincipalBundle G projection]

/-- The original right principal action on the fiber product, leaving its base coordinate fixed. -/
instance principalBundlePullbackMulAction (f : C(X, Y)) :
    MulAction Gᵐᵒᵖ (PrincipalBundlePullback f projection) where
  smul g z :=
    ⟨(z.1.1, g • z.1.2),
      z.2.trans (hP.projection_smul (MulOpposite.unop g) z.1.2).symm⟩
  one_smul z := by
    apply Subtype.ext
    exact Prod.ext rfl (one_smul Gᵐᵒᵖ z.1.2)
  mul_smul g h z := by
    apply Subtype.ext
    exact Prod.ext rfl (mul_smul g h z.1.2)

/-- The pullback right action is jointly continuous for the unchanged subtype topology. -/
instance principalBundlePullbackContinuousSMul (f : C(X, Y)) :
    ContinuousSMul Gᵐᵒᵖ (PrincipalBundlePullback f projection) where
  continuous_smul :=
    (continuous_snd.subtype_val.fst.prodMk
      (continuous_fst.smul continuous_snd.subtype_val.snd)).subtype_mk _

/-- Pulling back the actual principal projection gives a locally trivial principal bundle. -/
theorem isPrincipalBundle_pullback (f : C(X, Y)) :
    IsPrincipalBundle G (principalBundlePullbackProjection f projection) := by
  /- Stage 1: the original right action leaves the x coordinate fixed, hence
  preserves the displayed pullback projection. At x choose an original
  principal chart e whose base contains f(x), and pull back its base to f⁻¹(U).
  Stage 2: the actual local coordinates send (x,p) to (x,(e p).2). Their
  inverse sends (x,g) to (x,e inverse(f(x),g)); the chart identities put this
  pair in the original fiber-product subtype. These maps are continuous for
  the subtype topology, and have exactly f⁻¹(U) as base set. The right-action
  identity of e gives the same right multiplication in the new G coordinate.
  Stage 3: these charts cover X and supply the required principal structure
  on the existing projection. Totalizing inverse charts outside their domain
  can use a lift of each f(x), provided by original projection surjectivity;
  it does not alter any prescribed on-domain formula. An empty X causes no
  additional nonemptiness assumption. No replacement topology is selected. -/
  classical
  constructor
  · intro g z
    rfl
  · intro x
    obtain ⟨e, hx, he⟩ := hP.exists_trivialization (f x)
    -- Totalize only the off-domain inverse by an original point over f(y).
    let lift (y : X) : P := ((hP.projection_properties).2.2 (f y)).choose
    have hlift (y : X) : projection (lift y) = f y :=
      ((hP.projection_properties).2.2 (f y)).choose_spec
    let inverse (y : X × G) : PrincipalBundlePullback f projection :=
      if hy : f y.1 ∈ e.baseSet then
        ⟨(y.1, e.toOpenPartialHomeomorph.symm (f y.1, y.2)),
          (e.proj_symm_apply' hy).symm⟩
      else ⟨(y.1, lift y.1), (hlift y.1).symm⟩
    have hinverse (y : X × G) (hy : f y.1 ∈ e.baseSet) :
        (inverse y).val = (y.1, e.toOpenPartialHomeomorph.symm (f y.1, y.2)) := by
      dsimp only [inverse]
      rw [dite_eq_left hy]
    let t : Bundle.Trivialization G (principalBundlePullbackProjection f projection) :=
      { toFun := fun z ↦ (z.val.1, (e z.val.2).2)
        invFun := inverse
        source := (principalBundlePullbackProjection f projection) ⁻¹' (f ⁻¹' e.baseSet)
        target := (f ⁻¹' e.baseSet) ×ˢ Set.univ
        baseSet := f ⁻¹' e.baseSet
        map_source' := fun _ h ↦ ⟨h, Set.mem_univ _⟩
        map_target' := by
          intro y hy
          change f (inverse y).val.1 ∈ e.baseSet
          rw [hinverse y hy.1]
          exact hy.1
        left_inv' := by
          intro z hz
          apply Subtype.ext
          rw [hinverse (z.val.1, (e z.val.2).2) hz]
          apply Prod.ext
          · rfl
          · change e.toOpenPartialHomeomorph.symm (f z.val.1, (e z.val.2).2) = z.val.2
            rw [z.property]
            exact e.symm_apply_mk_proj (e.mem_source.mpr (z.property ▸ hz))
        right_inv' := by
          intro y hy
          rw [hinverse y hy.1]
          rw [e.apply_symm_apply' hy.1]
        open_source := (e.open_baseSet.preimage f.continuous).preimage
          (principalBundlePullbackProjection f projection).continuous
        open_target := (e.open_baseSet.preimage f.continuous).prod isOpen_univ
        open_baseSet := e.open_baseSet.preimage f.continuous
        continuousOn_toFun :=
          (principalBundlePullbackProjection f projection).continuous.continuousOn.prodMk
            (continuous_snd.comp_continuousOn
              (e.toOpenPartialHomeomorph.continuousOn.comp
                (principalBundlePullbackLift f projection).continuous.continuousOn
                (fun z hz ↦ e.mem_source.mpr (z.property ▸ hz))))
        continuousOn_invFun := by
          apply (Topology.IsInducing.subtypeVal
            (t := {z : X × P | f z.1 = projection z.2})).continuousOn_iff.mpr
          have hc : ContinuousOn (fun y : X × G ↦
              (y.1, e.toOpenPartialHomeomorph.symm (f y.1, y.2)))
              ((f ⁻¹' e.baseSet) ×ˢ Set.univ) :=
            continuous_fst.continuousOn.prodMk
              (e.toOpenPartialHomeomorph.continuousOn_symm.comp
                ((f.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
                (fun y hy ↦ e.mem_target.mpr hy.1))
          apply hc.congr
          intro y hy
          exact hinverse y hy.1
        source_eq := rfl
        target_eq := rfl
        proj_toFun := fun _ _ ↦ rfl }
    refine ⟨t, hx, ?_⟩
    intro g z hz
    change (e (MulOpposite.op g • z.val.2)).2 = (e z.val.2).2 * g
    exact he g z.val.2 (z.property ▸ hz)

variable {F : Type*} [MulAction G F] [TopologicalSpace F] [ContinuousSMul G F]

/-- The ordinary pullback subtype of the original associated bundle over the same base map. -/
abbrev AssociatedBundlePullback (f : C(X, Y)) : Type _ :=
  {z : X × AssociatedBundle G P F //
    f z.1 = associatedBundleProjection (F := F) hP z.2}

/-- The actual associated quotient comparison sends [((x,p),v)] to (x,[p,v]). -/
def associatedBundlePullbackMap (f : C(X, Y)) :
    C(AssociatedBundle G (PrincipalBundlePullback f projection) F,
      AssociatedBundlePullback (G := G) (F := F) (projection := projection) f) where
  toFun := Quotient.lift
    (fun z : PrincipalBundlePullback f projection × F ↦
      ⟨(z.1.1.1, associatedBundleMk G P F z.1.1.2 z.2), z.1.2⟩) (by
        intro x y hxy
        rcases hxy with ⟨g, rfl⟩
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact Quotient.sound ⟨g, rfl⟩)
  continuous_toFun := continuous_quot_lift _
    ((continuous_fst.subtype_val.fst.prodMk
      (continuous_quot_mk.comp
        (continuous_fst.subtype_val.snd.prodMk continuous_snd))).subtype_mk _)

/-- The fixed associated quotient comparison is a homeomorphism and preserves the original base. -/
theorem associatedBundlePullbackMap_properties (f : C(X, Y)) :
    IsHomeomorph (associatedBundlePullbackMap (G := G) (F := F) (projection := projection) f) ∧
      ∀ q : AssociatedBundle G (PrincipalBundlePullback f projection) F,
        (associatedBundlePullbackMap (G := G) (F := F) (projection := projection) f q).1.1 =
          associatedBundleProjection (F := F) (isPrincipalBundle_pullback (G := G) f) q := by
  /- Stage 1: surjectivity chooses a representative (p,v) of the given
  associated class; the target subtype equation places (x,p) in the original
  principal pullback. If two such representatives have the same image, their
  base coordinates agree and the original associated orbit relation gives
  exactly the same diagonal group relation in the pulled-back total space.
  This proves bijectivity of the specified map, including empty fibers.
  Stage 2: continuity is already part of this actual quotient lift. Above
  an original principal chart U, use its associated chart to read off the
  fiber coordinate, and choose the original principal point with group
  coordinate one. This gives a continuous local inverse on the open set
  f⁻¹(U). Bijectivity identifies it with the global inverse, which is therefore
  continuous for the existing subtype and quotient topologies. This does not assume
  that pulling back an arbitrary quotient map preserves its quotient topology.
  Stage 3: on [((x,p),v)] both base maps are x. Quotient induction gives the
  displayed base square for every original quotient element. The comparison
  is the inverse of the map written in HU IV.6 Proposition 6.3. -/
  classical
  let m := associatedBundlePullbackMap (G := G) (F := F) (projection := projection) f
  -- Stage 1: the original quotient relation gives exactly the fibers of this comparison.
  have hbij : Function.Bijective m := by
    constructor
    · intro q₁ q₂ hq
      induction q₁ using Quotient.inductionOn with
      | h a =>
        induction q₂ using Quotient.inductionOn with
        | h b =>
          have hx : a.1.val.1 = b.1.val.1 :=
            congrArg (fun z ↦ z.val.1) hq
          have hc : associatedBundleMk G P F a.1.val.2 a.2 =
              associatedBundleMk G P F b.1.val.2 b.2 :=
            congrArg (fun z ↦ z.val.2) hq
          obtain ⟨g, hg⟩ := Quotient.exact hc
          apply Quotient.sound
          refine ⟨g, ?_⟩
          apply Prod.ext
          · apply Subtype.ext
            exact Prod.ext hx.symm (congrArg Prod.fst hg)
          · exact congrArg (fun z : P × F ↦ z.2) hg
    · intro z
      obtain ⟨⟨p, v⟩, hrep⟩ := Quotient.exists_rep z.val.2
      have hp : f z.val.1 = projection p := by
        have hbase := z.property
        rw [← hrep] at hbase
        exact hbase
      refine ⟨associatedBundleMk G (PrincipalBundlePullback f projection) F
        ⟨(z.val.1, p), hp⟩ v, ?_⟩
      apply Subtype.ext
      exact Prod.ext rfl hrep
  let eComp := Equiv.ofBijective m hbij
  have hinvContinuous : Continuous eComp.symm := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    obtain ⟨e, he₀, he⟩ := hP.exists_trivialization (f z₀.val.1)
    obtain ⟨eA, hbase, hformula, hinverse⟩ := exists_associatedBundleTrivialization
      (F := F) hP e he
    let W : Set (AssociatedBundlePullback (G := G) (F := F)
        (projection := projection) f) := {z | f z.val.1 ∈ e.baseSet}
    have hW : IsOpen W := e.open_baseSet.preimage
      (f.continuous.comp continuous_subtype_val.fst)
    -- Stage 2: over this open set, the original principal chart gives an explicit inverse.
    let localInv (z : W) : AssociatedBundle G (PrincipalBundlePullback f projection) F :=
      associatedBundleMk G (PrincipalBundlePullback f projection) F
        ⟨(z.val.val.1, e.toOpenPartialHomeomorph.symm (f z.val.val.1, 1)),
          (e.proj_symm_apply' z.property).symm⟩ (eA z.val.val.2).2
    have hsource (z : W) : z.val.val.2 ∈ eA.source := by
      apply eA.mem_source.mpr
      rw [hbase, ← z.val.property]
      exact z.property
    have hlocalContinuous : Continuous localInv := by
      have hp : Continuous (fun z : W ↦
          (⟨(z.val.val.1, e.toOpenPartialHomeomorph.symm (f z.val.val.1, 1)),
            (e.proj_symm_apply' z.property).symm⟩ : PrincipalBundlePullback f projection)) :=
        (continuous_subtype_val.subtype_val.fst.prodMk
          (e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
            ((f.continuous.comp continuous_subtype_val.subtype_val.fst).prodMk
              (continuous_const (y := (1 : G))))
            (fun z : W ↦ e.mem_target.mpr z.property))).subtype_mk _
      have hv : Continuous (fun z : W ↦ (eA z.val.val.2).2) :=
        continuous_snd.comp (eA.toOpenPartialHomeomorph.continuousOn.comp_continuous
          continuous_subtype_val.subtype_val.snd hsource)
      exact continuous_quot_mk.comp (hp.prodMk hv)
    have hlocalInverse (z : W) : m (localInv z) = z.val := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change associatedBundleMk G P F
          (e.toOpenPartialHomeomorph.symm (f z.val.val.1, 1)) (eA z.val.val.2).2 = z.val.val.2
        rw [← hinverse _ _ z.property, z.val.property]
        exact eA.symm_apply_mk_proj (hsource z)
    have hinvOn : ContinuousOn eComp.symm W := by
      rw [continuousOn_iff_continuous_domRestrict]
      apply hlocalContinuous.congr
      intro z
      apply eComp.injective
      change m (localInv z) = eComp (eComp.symm z.val)
      rw [Equiv.apply_symm_apply]
      exact hlocalInverse z
    exact hinvOn.continuousAt (hW.mem_nhds he₀)
  let comparison : AssociatedBundle G (PrincipalBundlePullback f projection) F ≃ₜ
      AssociatedBundlePullback (G := G) (F := F) (projection := projection) f :=
    { toEquiv := eComp
      continuous_toFun := m.continuous
      continuous_invFun := hinvContinuous }
  refine ⟨comparison.isHomeomorph, ?_⟩
  -- Both original base maps send a representative [((x,p),v)] to exactly x.
  intro q
  induction q using Quotient.inductionOn with
  | h z => rfl

/-- The canonical homeomorphism comparing principal and associated bundle pullbacks. -/
def associatedBundlePullbackHomeomorph (f : C(X, Y)) :
    AssociatedBundle G (PrincipalBundlePullback f projection) F ≃ₜ
      AssociatedBundlePullback (G := G) (F := F) (projection := projection) f :=
  IsHomeomorph.homeomorph
    (associatedBundlePullbackMap (G := G) (F := F) (projection := projection) f)
    (associatedBundlePullbackMap_properties (G := G) (F := F) (projection := projection) f).1

end AtiyahSinger
