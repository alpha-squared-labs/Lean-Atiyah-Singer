/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.DifferenceBundle

/-!
# Comparison of geometric triples with the quotient-space relative group

Public module ID: M2259.

D07/K02. The forward homomorphism sends each generator to its difference
class, constructed following SG I.9.25. The stable extension criterion and
reduced quotient representatives prove bijectivity of this specified map
for one-step complexes on compact Hausdorff closed pairs. Composing with
the open-complement comparison gives the compact-support equivalence and
its extension formula. General supported representatives are treated in
`SupportTripleRealization`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] [hX : CompactSpace X] [hT : T2Space X]
  {A : Set X}

include hX hT

attribute [local instance] sumTopology isFiniteRank_sum trivialTopology isFiniteRank_trivial
  isFiniteRank_restrict IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber


/-- Descend the actual difference classes through the explicit triple relations. -/
def tripleKZeroToRelative (A : Set X) (hA : IsClosed A) : TripleKZero A →+ RelativeKZero A hA :=
  (tripleKZero_universal_property A (fun a ↦ a.relativeClass hA)
    (fun a b h ↦ a.relativeClass_eq_of_isIsomorphic hA b h)
    (fun a b ↦ a.relativeClass_sum hA b)
    (fun E ↦ BundleTriple.relativeClass_identity hA E)).exists.choose

/-- The comparison has the constructed difference class on each generator. -/
theorem tripleKZeroToRelative_apply (hA : IsClosed A) (a : BundleTriple A) :
    tripleKZeroToRelative A hA a.kZeroClass = a.relativeClass hA := by
  /- The map was selected from the universal property with its value fixed
  on every generator. Apply that characterization to a. Thus this is the actual
  gluing comparison rather than an unspecified isomorphism of abstract groups. -/
  exact (tripleKZero_universal_property A (fun b ↦ b.relativeClass hA)
    (fun b c h ↦ b.relativeClass_eq_of_isIsomorphic hA c h)
    (fun b c ↦ b.relativeClass_sum hA c)
    (fun E ↦ BundleTriple.relativeClass_identity hA E)).exists.choose_spec a

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of the constructed class is extension after stabilization. -/
theorem BundleTriple.relativeClass_eq_zero_iff (hA : IsClosed A) (a : BundleTriple A) :
    a.relativeClass hA = 0 ↔ ∃ G : FiniteBundle X,
      ∃ e : Iso (a.source.sum G).Fiber (a.target.sum G).Fiber,
        e.restrict A = a.boundary.stabilize G.Fiber := by
  /- By double excision, a zero left relative class has zero relative lift
  on the double, so the glued bundle and target projection pullback have equal
  K classes. Stabilize their isomorphism by a trivial bundle using complements.
  Its restrictions on the two copies differ by the given boundary map; composing
  the left restriction with the inverse right restriction extends the stabilized
  boundary to X. Conversely an extension makes the triple stably elementary,
  whose constructed difference class is zero. -/
  classical
  let := DoubleSpace.t2Space A hA
  constructor
  · intro ha
    -- Excision and the original forgetful lift give the same stabilized gluing equation.
    have hlift : a.differenceLift hA = 0 := by
      apply (DoubleSpace.relativeRestriction_bijective A hA).injective
      simpa only [BundleTriple.relativeClass, map_zero] using ha
    have hdifference : a.doubleDifference hA = 0 := by
      rw [← a.forget_differenceLift hA, hlift, map_zero]
    let W := clutchingBundle hA a
    let P := a.target.pullback (DoubleSpace.projMap A)
    let := W.isFiniteRank
    let := P.isFiniteRank
    have hclass : W.kZeroClass = P.kZeroClass := by
      rw [FiniteBundle.kZeroClass_pullback]
      exact sub_eq_zero.mp hdifference
    obtain ⟨n, ⟨e⟩⟩ := (kZeroClass_eq_iff_stable_iso
      (E := W.Fiber) (F := P.Fiber)).mp hclass
    let G := FiniteBundle.trivial X n
    let T := FiniteBundle.trivial (DoubleSpace A) n
    let WS := W.sum T
    let PS := P.sum T
    let b := a.sum (BundleTriple.identity A G)
    -- Pullback commutes with the actual sum topology and keeps every fiber pair fixed.
    let compare (U V : FiniteBundle (DoubleSpace A)) (f : C(X, DoubleSpace A)) :
        Iso ((U.sum V).pullback f).Fiber ((U.pullback f).sum (V.pullback f)).Fiber :=
      { linearEquiv x := LinearEquiv.refl ℂ (U.Fiber (f x) × V.Fiber (f x))
        continuous_total := by
          apply continuous_induced_rng.mpr
          apply Continuous.prodMk
          · rw [(inducing_pullbackTotalSpaceEmbedding Unit U.Fiber f).continuous_iff]
            exact (Pullback.continuous_proj Unit (U.sum V).Fiber f).prodMk
              (continuous_sum_fst.comp (Pullback.continuous_lift Unit (U.sum V).Fiber f))
          · rw [(inducing_pullbackTotalSpaceEmbedding Unit V.Fiber f).continuous_iff]
            exact (Pullback.continuous_proj Unit (U.sum V).Fiber f).prodMk
              (continuous_sum_snd.comp (Pullback.continuous_lift Unit (U.sum V).Fiber f))
        continuous_symm := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (U.sum V).Fiber f).continuous_iff]
          apply ((Pullback.continuous_proj Unit U.Fiber f).comp continuous_sum_fst).prodMk
          apply continuous_induced_rng.mpr
          exact ((Pullback.continuous_lift Unit U.Fiber f).comp continuous_sum_fst).prodMk
            ((Pullback.continuous_lift Unit V.Fiber f).comp continuous_sum_snd) }
    let l := DoubleSpace.leftMap A
    let r := DoubleSpace.rightMap A
    let WL : Iso (WS.pullback l).Fiber b.source.Fiber :=
      (compare W T l).trans ((clutchingLeftIso hA a).sum (pullbackTrivialIso l n))
    let WR : Iso (WS.pullback r).Fiber b.target.Fiber :=
      (compare W T r).trans ((clutchingRightIso hA a).sum (pullbackTrivialIso r n))
    let pL : Iso (P.pullback l).Fiber a.target.Fiber :=
      (pullbackCompIso (E := a.target.Fiber) (DoubleSpace.projMap A) l).trans
        (pullbackIdIso (E := a.target.Fiber))
    let pR : Iso (P.pullback r).Fiber a.target.Fiber :=
      (pullbackCompIso (E := a.target.Fiber) (DoubleSpace.projMap A) r).trans
        (pullbackIdIso (E := a.target.Fiber))
    let PL : Iso (PS.pullback l).Fiber b.target.Fiber :=
      (compare P T l).trans (pL.sum (pullbackTrivialIso l n))
    let PR : Iso (PS.pullback r).Fiber b.target.Fiber :=
      (compare P T r).trans (pR.sum (pullbackTrivialIso r n))
    have hWL (x : X) (v : WS.Fiber (l x)) :
        WL.linearEquiv x v = ((clutchingLeftIso hA a).linearEquiv x v.1, v.2) := by
      change (_, (pullbackTrivialIso l n).linearEquiv x v.2) = _
      rw [pullbackTrivialIso_apply]
      rfl
    have hWR (x : X) (v : WS.Fiber (r x)) :
        WR.linearEquiv x v = ((clutchingRightIso hA a).linearEquiv x v.1, v.2) := by
      change (_, (pullbackTrivialIso r n).linearEquiv x v.2) = _
      rw [pullbackTrivialIso_apply]
      rfl
    have hWLi (x : X) (v : b.source.Fiber x) :
        (WL.linearEquiv x).symm v =
          (((clutchingLeftIso hA a).linearEquiv x).symm v.1, v.2) := by
      apply (WL.linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, hWL, LinearEquiv.apply_symm_apply]
    have hPL (x : X) (v : PS.Fiber (l x)) : PL.linearEquiv x v = v := by
      change (pL.linearEquiv x v.1, (pullbackTrivialIso l n).linearEquiv x v.2) = v
      change ((pullbackIdIso (E := a.target.Fiber)).linearEquiv x
        ((pullbackCompIso (E := a.target.Fiber) (DoubleSpace.projMap A) l).linearEquiv
          x v.1), (pullbackTrivialIso l n).linearEquiv x v.2) = v
      rw [pullbackCompIso_apply, pullbackIdIso_apply, pullbackTrivialIso_apply]
      rfl
    have hPR (x : X) (v : PS.Fiber (r x)) : PR.linearEquiv x v = v := by
      change (pR.linearEquiv x v.1, (pullbackTrivialIso r n).linearEquiv x v.2) = v
      change ((pullbackIdIso (E := a.target.Fiber)).linearEquiv x
        ((pullbackCompIso (E := a.target.Fiber) (DoubleSpace.projMap A) r).linearEquiv
          x v.1), (pullbackTrivialIso r n).linearEquiv x v.2) = v
      rw [pullbackCompIso_apply, pullbackIdIso_apply, pullbackTrivialIso_apply]
      rfl
    have hcast {z w : DoubleSpace A} (h : z = w) (v : W.Fiber z) (t : Fin n → ℂ) :
        cast (congrArg WS.Fiber h) (v, t) = (cast (congrArg W.Fiber h) v, t) := by
      cases h
      rfl
    have hseamW : ClutchingCompatible b WS WL WR := by
      intro x v
      change WR.linearEquiv x
        (cast (congrArg WS.Fiber (DoubleSpace.left_eq_right A x))
          ((WL.linearEquiv x).symm v)) = b.boundary.linearEquiv x v
      rw [hWLi, hcast (DoubleSpace.left_eq_right A x), hWR]
      change _ =
        (RelativeTriple.sum a.boundary (RelativeTriple.identity G.Fiber A)).linearEquiv x v
      rw [RelativeTriple.sum_apply]
      change ((clutchingRightIso hA a).linearEquiv x
        (cast (congrArg W.Fiber (DoubleSpace.left_eq_right A x))
          (((clutchingLeftIso hA a).linearEquiv x).symm v.1)), v.2) =
        (a.boundary.linearEquiv x v.1, v.2)
      exact Prod.ext (clutching_seam_apply hA a x v.1) rfl
    have hseamP : ClutchingCompatible (BundleTriple.identity A b.target) PS PL PR := by
      intro x v
      have hPLi : (PL.linearEquiv x).symm v = v := by
        apply (PL.linearEquiv x).injective
        rw [LinearEquiv.apply_symm_apply, hPL]
      change PR.linearEquiv x
        (cast (congrArg PS.Fiber (DoubleSpace.left_eq_right A x))
          ((PL.linearEquiv x).symm v)) = v
      rw [hPLi, hPR]
      rfl
    -- Compare the two restrictions of the same global stabilized gluing isomorphism.
    let u : Iso b.source.Fiber b.target.Fiber :=
      WL.symm.trans ((e.pullback l).trans PL)
    let v : Iso b.target.Fiber b.target.Fiber :=
      WR.symm.trans ((e.pullback r).trans PR)
    have natural {z w : DoubleSpace A} (h : z = w) (t : WS.Fiber z) :
        cast (congrArg PS.Fiber h) (e.linearEquiv z t) =
          e.linearEquiv w (cast (congrArg WS.Fiber h) t) := by
      cases h
      rfl
    have huv (x : A) (t : b.source.Fiber x) :
        u.linearEquiv x t = v.linearEquiv x (b.boundary.linearEquiv x t) := by
      have hw : cast (congrArg WS.Fiber (DoubleSpace.left_eq_right A x))
          ((WL.linearEquiv x).symm t) =
            (WR.linearEquiv x).symm (b.boundary.linearEquiv x t) := by
        apply (WR.linearEquiv x).injective
        exact (hseamW x t).trans ((WR.linearEquiv x).apply_symm_apply _).symm
      have hp (s : PS.Fiber (l x)) :
          PR.linearEquiv x (cast (congrArg PS.Fiber (DoubleSpace.left_eq_right A x)) s) =
            PL.linearEquiv x s := by
        have h := hseamP x (PL.linearEquiv x s)
        change PR.linearEquiv x
          (cast (congrArg PS.Fiber (DoubleSpace.left_eq_right A x))
            ((PL.linearEquiv x).symm (PL.linearEquiv x s))) = PL.linearEquiv x s at h
        rw [LinearEquiv.symm_apply_apply] at h
        exact h
      change PL.linearEquiv x (e.linearEquiv (l x) ((WL.linearEquiv x).symm t)) =
        PR.linearEquiv x (e.linearEquiv (r x)
          ((WR.linearEquiv x).symm (b.boundary.linearEquiv x t)))
      calc
        _ = PR.linearEquiv x
            (cast (congrArg PS.Fiber (DoubleSpace.left_eq_right A x))
              (e.linearEquiv (l x) ((WL.linearEquiv x).symm t))) := (hp _).symm
        _ = PR.linearEquiv x (e.linearEquiv (r x)
            (cast (congrArg WS.Fiber (DoubleSpace.left_eq_right A x))
              ((WL.linearEquiv x).symm t))) :=
          congrArg (PR.linearEquiv x) (natural (DoubleSpace.left_eq_right A x) _)
        _ = _ := congrArg (fun s ↦ PR.linearEquiv x (e.linearEquiv (r x) s)) hw
    refine ⟨G, u.trans v.symm, ?_⟩
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro t
    change (v.linearEquiv x).symm (u.linearEquiv x t) = b.boundary.linearEquiv x t
    rw [huv, LinearEquiv.symm_apply_apply]
  · rintro ⟨G, e, he⟩
    -- The supplied extension compares the stabilized triple with an identity triple.
    have hi : (a.sum (BundleTriple.identity A G)).IsIsomorphic
        (BundleTriple.identity A (a.source.sum G)) := by
      refine ⟨Iso.refl (a.source.sum G).Fiber, e.symm, ?_⟩
      intro x v
      have hv := congrArg (fun q : RelativeTriple (a.source.sum G).Fiber
        (a.target.sum G).Fiber A ↦ q.linearEquiv x v) he
      change (e.linearEquiv x).symm ((a.boundary.stabilize G.Fiber).linearEquiv x v) = v
      exact (congrArg (e.linearEquiv x).symm hv.symm).trans
        ((e.linearEquiv x).symm_apply_apply v)
    have hh := BundleTriple.relativeClass_eq_of_isIsomorphic hA _ _ hi
    simpa only [BundleTriple.relativeClass_sum, BundleTriple.relativeClass_identity,
      add_zero] using hh

/-- The constructed comparison is injective. -/
theorem tripleKZeroToRelative_injective (A : Set X) (hA : IsClosed A) :
    Function.Injective (tripleKZeroToRelative A hA) := by
  /- Represent an element of the kernel by a single triple. The comparison
  formula and relative zero criterion supply a stabilized global extension.
  The corresponding zero criterion in the presented triple group makes this
  generator zero. An additive homomorphism with trivial kernel is injective. -/
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc

  obtain ⟨a, rfl⟩ := bundleTriple_kZeroClass_surjective A hA c
  rw [tripleKZeroToRelative_apply] at hc
  -- Both zero criteria retain the same stabilizing bundle and extension map.
  exact (a.kZeroClass_eq_zero_iff A hA).mpr ((a.relativeClass_eq_zero_iff hA).mp hc)

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
/-- Every reduced quotient class comes from the constructed difference class. -/
theorem tripleKZeroToRelative_surjective (A : Set X) (hA : IsClosed A) :
    Function.Surjective (tripleKZeroToRelative A hA) := by
  /- Represent the original reduced quotient class by a bundle minus a trivial bundle.
  Zero evaluation equates their classes on the distinguished singleton; stabilization
  supplies a boundary isomorphism there. That triple's relative difference forgets to
  the original reduced class. Pull it back along X's original quotient map: the induced
  pointed quotient map is exactly the singleton quotient map, so naturality recovers
  the same class. The extra basepoint also covers empty A and empty X. -/
  classical
  let Z := PointedQuotient A
  let : CompactSpace Z := PointedQuotient.compactSpace A
  let : T2Space Z := PointedQuotient.t2Space A hA
  let z₀ : Z := PointedQuotient.basepoint A
  let S : Set Z := {z₀}
  have hS : IsClosed S := isClosed_singleton
  let := hS.isClosedEmbedding_subtypeVal.compactSpace
  let := PointedQuotient.t2Space S hS
  let q : C(X, Z) := ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩
  let i : C(S, Z) := ⟨Subtype.val, continuous_subtype_val⟩
  intro c
  -- Represent the actual reduced quotient class by one image bundle minus a trivial bundle.
  obtain ⟨p, n, hp⟩ := exists_class_sub_trivial c.val
  let E := FiniteBundle.ofFamily (fun z : Z ↦ p.fiber z)
  let F := FiniteBundle.trivial Z n
  have hEF : c.val = E.kZeroClass - F.kZeroClass := hp
  -- Restriction to the distinguished singleton factors through its original evaluation.
  have hrestriction : complexKZeroRestriction S hS c.val = 0 := by
    let ev := (ContinuousMap.evalAlgHom ℂ ℂ z₀).toRingHom
    have hfactor : (ContinuousMap.compRightAlgHom ℂ ℂ i).toRingHom =
        (algebraMap ℂ C(S, ℂ)).comp ev := by
      ext f z
      change f z.val = f z₀
      exact congrArg f (Set.mem_singleton_iff.mp z.property)
    change kZeroMap (ContinuousMap.compRightAlgHom ℂ ℂ i).toRingHom c.val = 0
    rw [hfactor, kZeroMap_comp, AddMonoidHom.comp_apply, c.property, map_zero]
  have hboundaryClass : kZeroClass (Restrict E.Fiber S) =
      kZeroClass (Restrict F.Fiber S) := by
    have h := hrestriction
    rw [hEF, map_sub] at h
    change complexKZeroPullback i E.kZeroClass - complexKZeroPullback i F.kZeroClass = 0 at h
    change complexKZeroPullback i (kZeroClass E.Fiber) -
      complexKZeroPullback i (kZeroClass F.Fiber) = 0 at h
    rw [← kZeroClass_pullback (V := E.Fiber) i,
      ← kZeroClass_pullback (V := F.Fiber) i] at h
    exact sub_eq_zero.mp h
  obtain ⟨m, ⟨e⟩⟩ := (kZeroClass_eq_iff_stable_iso
    (E := Restrict E.Fiber S) (F := Restrict F.Fiber S)).mp hboundaryClass
  let G := FiniteBundle.trivial Z m
  let E' := E.sum G
  let F' := F.sum G
  let cE : Iso (Restrict E'.Fiber S)
      (Restrict E.Fiber S ×ᵇ Bundle.Trivial S (Fin m → ℂ)) :=
    (restrictSumIso (E := E.Fiber) (F := G.Fiber) S).trans
      ((Iso.refl (Restrict E.Fiber S)).sum (pullbackTrivialIso i m))
  let cF : Iso (Restrict F'.Fiber S)
      (Restrict F.Fiber S ×ᵇ Bundle.Trivial S (Fin m → ℂ)) :=
    (restrictSumIso (E := F.Fiber) (F := G.Fiber) S).trans
      ((Iso.refl (Restrict F.Fiber S)).sum (pullbackTrivialIso i m))
  let b : BundleTriple S := BundleTriple.ofBoundary E' F' (cE.trans (e.trans cF.symm))
  have hb : relativeKZeroForget S hS (b.relativeClass hS) = c.val := by
    rw [BundleTriple.relativeClass_forget]
    change E'.kZeroClass - F'.kZeroClass = c.val
    dsimp only [E', F']
    rw [FiniteBundle.kZeroClass_sum, FiniteBundle.kZeroClass_sum, hEF]
    abel
  -- On the original quotient, the induced map is precisely the singleton quotient map.
  have hpre : q ⁻¹' S = A := by
    ext x
    exact PointedQuotient.of_eq_basepoint_iff A x
  have hmaps : Set.MapsTo q A S := by
    intro x hx
    exact (PointedQuotient.of_eq_basepoint_iff A x).mpr hx
  let qS : C(Z, PointedQuotient S) :=
    ⟨PointedQuotient.of S, PointedQuotient.continuous_of S⟩
  have hmap : PointedQuotient.mapContinuous A S q hmaps = qS := by
    ext z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => rfl
      | inr u =>
        exact ((PointedQuotient.of_eq_basepoint_iff S z₀).mpr (Set.mem_singleton z₀)).symm
  let a : BundleTriple A := hpre ▸ b.pullback q
  refine ⟨a.kZeroClass, ?_⟩
  rw [tripleKZeroToRelative_apply]
  have alongValue (B : Set X) (hB : IsClosed B) (hf : Set.MapsTo q B S)
      (heq : q ⁻¹' S = B) :
      letI := PointedQuotient.t2Space B hB
      (BundleTriple.relativeClass hB (heq ▸ b.pullback q)).val =
        complexKZeroPullback (PointedQuotient.mapContinuous B S q hf)
          (b.relativeClass hS).val := by
    subst B
    exact congrArg Subtype.val (b.relativeClass_pullback hS q)
  have hval : (a.relativeClass hA).val =
      complexKZeroPullback (PointedQuotient.mapContinuous A S q hmaps)
        (b.relativeClass hS).val := alongValue A hA hmaps hpre
  apply Subtype.ext
  rw [hval, hmap]
  exact hb

/-- SG I.9.25 for one-step complexes: the specified comparison is bijective. -/
theorem tripleKZeroToRelative_bijective (A : Set X) (hA : IsClosed A) :
    Function.Bijective (tripleKZeroToRelative A hA) := by
  /- Combine injectivity, proved by the stable extension criterion, with
  surjectivity, proved by pulling back reduced quotient bundles. Both statements
  concern the same generator-wise difference map with the same closed-pair hypotheses. -/
  exact ⟨tripleKZeroToRelative_injective A hA, tripleKZeroToRelative_surjective A hA⟩

/-- Identify the two models through the specified difference homomorphism. -/
def tripleKZeroRelativeEquiv (A : Set X) (hA : IsClosed A) :
    TripleKZero A ≃+ RelativeKZero A hA :=
  AddEquiv.ofBijective _ (tripleKZeroToRelative_bijective A hA)

/-- The equivalence keeps the specified class of every geometric triple. -/
theorem tripleKZeroRelativeEquiv_apply (hA : IsClosed A) (a : BundleTriple A) :
    tripleKZeroRelativeEquiv A hA a.kZeroClass = a.relativeClass hA := by
  /- The additive equivalence uses the original comparison homomorphism as
  its forward map. Its generator formula is therefore the previously stated
  formula for that same homomorphism, with no new choice on the forward side. -/
  exact tripleKZeroToRelative_apply hA a

/-- Two constructed relative classes agree exactly under stable isomorphism. -/
theorem BundleTriple.relativeClass_eq_iff_stable (hA : IsClosed A) (a b : BundleTriple A) :
    a.relativeClass hA = b.relativeClass hA ↔ a.IsStablyIsomorphic b := by
  /- Injectivity of the comparison converts equality of the two constructed
  relative classes to equality of their triple-group generators. Apply the exact
  stable-isomorphism criterion for those generators. The converse follows by stability. -/
  constructor
  · intro h
    apply (a.kZeroClass_eq_iff_stable A hA b).mp
    apply tripleKZeroToRelative_injective A hA
    simpa only [tripleKZeroToRelative_apply] using h
  · exact a.relativeClass_eq_of_isStablyIsomorphic hA b

/-- The original geometric triple map is surjective onto the relative group. -/
theorem bundleTriple_relativeClass_surjective (A : Set X) (hA : IsClosed A) :
    Function.Surjective (BundleTriple.relativeClass hA) := by
  /- First lift a relative class through the comparison homomorphism. Then
  represent the lifted triple-group class by a single triple. The generator
  formula identifies the constructed relative class of that triple with the target. -/
  intro c
  obtain ⟨b, hb⟩ := tripleKZeroToRelative_surjective A hA c
  obtain ⟨a, rfl⟩ := bundleTriple_kZeroClass_surjective A hA b
  exact ⟨a, (tripleKZeroToRelative_apply hA a).symm.trans hb⟩

/-- The empty-pair normalization is source minus target. -/
theorem tripleKZeroToRelative_empty_forget (a : BundleTriple (∅ : Set X)) :
    relativeKZeroEmptyEquiv (tripleKZeroToRelative ∅ isClosed_empty a.kZeroClass) =
      a.source.kZeroClass - a.target.kZeroClass := by
  /- For the empty pair the canonical equivalence is the forgetful map.
  Apply the comparison generator formula and then the forgetful image formula
  for the constructed difference class. This gives precisely SG equation (9.7) for n=1. -/
  rw [tripleKZeroToRelative_apply]
  exact a.relativeClass_forget isClosed_empty

/-- Compose the actual difference map with the open-complement comparison. -/
def tripleKZeroToCompactSupport (A : Set X) (hA : IsClosed A) :
    letI := hA.isOpen_compl.locallyCompactSpace
    TripleKZero A →+ CompactSupportKZero (Aᶜ : Set X) :=
  letI := hA.isOpen_compl.locallyCompactSpace
  (relativeKZeroToCompactSupport.{_, 0} A hA).comp (tripleKZeroToRelative A hA)

/-- The complement class retains the specified geometric difference class. -/
theorem tripleKZeroToCompactSupport_apply (hA : IsClosed A) (a : BundleTriple A) :
    tripleKZeroToCompactSupport A hA a.kZeroClass =
      relativeKZeroToCompactSupport.{_, 0} A hA (a.relativeClass hA) := by
  /- Unfold the composite and evaluate the triple comparison on its
  generator. The second map is pullback by the actual pointed homeomorphism
  from the complement compactification to the quotient of the original pair. -/
  change relativeKZeroToCompactSupport A hA
    (tripleKZeroToRelative A hA a.kZeroClass) = _
  rw [tripleKZeroToRelative_apply]

/-- The constructed complement comparison is bijective. -/
theorem tripleKZeroToCompactSupport_bijective (A : Set X) (hA : IsClosed A) :
    Function.Bijective (tripleKZeroToCompactSupport A hA) := by
  /- The first map is the bijective difference comparison. The second is
  the bijective pullback by the complement compactification homeomorphism.
  The composite of these two bijections is the stated additive map. -/
  exact (relativeKZeroToCompactSupport_bijective A hA).comp
    (tripleKZeroToRelative_bijective A hA)

/-- The compact-support equivalence has the actual composite as forward map. -/
def tripleKZeroCompactSupportEquiv (A : Set X) (hA : IsClosed A) :
    letI := hA.isOpen_compl.locallyCompactSpace
    TripleKZero A ≃+ CompactSupportKZero (Aᶜ : Set X) :=
  letI := hA.isOpen_compl.locallyCompactSpace
  AddEquiv.ofBijective _ (tripleKZeroToCompactSupport_bijective A hA)

/-- Extending the complement class back to X recovers the absolute difference. -/
theorem tripleKZeroToCompactSupport_extension (hA : IsClosed A) (a : BundleTriple A) :
    compactSupportKZeroToAbsolute
      (compactSupportKZeroOpenExtension (Aᶜ : Set X) hA.isOpen_compl
        (tripleKZeroToCompactSupport A hA a.kZeroClass)) = a.absoluteClass := by
  /- Use the complement generator formula. Extension followed by the
  compact-to-absolute comparison agrees with relative forgetting. The forgotten
  image of the constructed difference class is the original absolute difference. -/
  rw [tripleKZeroToCompactSupport_apply, relativeKZeroToCompactSupport_extension,
    BundleTriple.relativeClass_forget]

end AtiyahSinger.ComplexBundle
