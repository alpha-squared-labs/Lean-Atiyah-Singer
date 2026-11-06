/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportHomotopy
public import AtiyahSinger.Topology.CompactSupportProductLaws
public import AtiyahSinger.Topology.CompactSupportProductNaturality

/-!
# The compact-support module action along a continuous map

Public module ID: M1679.

SG Appendix C.1: a continuous map f : Y → X between locally compact Hausdorff
spaces defines Kc(X) × Kc(Y) → Kc(Y). The actual construction takes the existing
external product and pulls it back along y ↦ (f(y), y). This graph map is proper
even when f is not proper; no pullback of a compact-support class along f alone
is used. For compact X, the original compact-to-absolute comparison makes this
the usual unital K(X)-module action on Kc(Y).

The graph's properness is a direct application of mathlib's proper-composite
criterion: projection to Y retracts the graph, and the product is Hausdorff.
Associativity, proper-pullback naturality, and the compact-base unit and product
laws are the standard module properties needed for the Thom homomorphism.
All four laws are proved below.

Sources: Lawson--Michelsohn, Spin Geometry, Appendix C.1; Karoubi, K-Theory,
IV.1.2. The module action does not itself assert a Thom isomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y Z : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]

/-- SG C.1: pull back the external product along the proper graph of a continuous map. -/
def compactSupportKZeroAction (f : C(Y, X)) :
    CompactSupportKZero X →+ CompactSupportKZero Y →+ CompactSupportKZero Y :=
  compactSupportKZeroExternalProduct.compr₂
    (compactSupportKZeroPullback (f.prodMk (ContinuousMap.id Y))
      (isProperMap_of_comp_of_t2 (f.continuous.prodMk continuous_id)
        continuous_snd isProperMap_id))

/-- The compact-support actions compose associatively along consecutive continuous maps. -/
theorem compactSupportKZeroAction_assoc (f : C(Y, X)) (g : C(Z, Y))
    (a : CompactSupportKZero X) (b : CompactSupportKZero Y) (c : CompactSupportKZero Z) :
    compactSupportKZeroAction g (compactSupportKZeroAction f a b) c =
      compactSupportKZeroAction (f.comp g) a (compactSupportKZeroAction g b c) := by
  /- Stage 1: expand each action as the specified graph pullback of the actual
  external product. Proper pullback commutes with external product by comparing
  their extensions to the one-point compactifications and the same smash collapse.
  Stage 2: apply the existing external-product associativity and proper-pullback
  composition. Both constructions restrict the threefold external product to
  z ↦ (f(g(z)), g(z), z), with only the displayed product associator intervening.
  Stage 3: that threefold graph is proper because projection to Z retracts it.
  All pullbacks used here are along these graphs or their products with identities;
  neither f nor g is assumed proper. The common formula gives the asserted equality. -/
  let F : C(Y, X × Y) := f.prodMk (ContinuousMap.id Y)
  let G : C(Z, Y × Z) := g.prodMk (ContinuousMap.id Z)
  let H : C(Z, X × Z) := (f.comp g).prodMk (ContinuousMap.id Z)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous continuous_snd isProperMap_id
  have hG : IsProperMap G :=
    isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_t2 H.continuous continuous_snd isProperMap_id
  have hIX : IsProperMap (ContinuousMap.id X) := isProperMap_id
  have hIZ : IsProperMap (ContinuousMap.id Z) := isProperMap_id
  -- Move the two actual graph pullbacks through the corresponding outer products.
  have hleft := compactSupportKZeroExternalProduct_properPullback F hF
    (ContinuousMap.id Z) hIZ (compactSupportKZeroExternalProduct a b) c
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hleft
  have hright := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id X) hIX G hG a (compactSupportKZeroExternalProduct b c)
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hright
  change compactSupportKZeroPullback G hG
      (compactSupportKZeroExternalProduct
        (compactSupportKZeroPullback F hF (compactSupportKZeroExternalProduct a b)) c) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroExternalProduct a
        (compactSupportKZeroPullback G hG (compactSupportKZeroExternalProduct b c)))
  rw [← hleft, ← hright, ← compactSupportKZeroExternalProduct_assoc a b c]
  -- Reassociate the common threefold product and compose the original proper maps.
  let L : C(Y × Z, (X × Y) × Z) := F.prodMap (ContinuousMap.id Z)
  let R : C(X × Z, X × (Y × Z)) := (ContinuousMap.id X).prodMap G
  let r : C(X × (Y × Z), (X × Y) × Z) :=
    ⟨(Homeomorph.prodAssoc X Y Z).symm, (Homeomorph.prodAssoc X Y Z).symm.continuous⟩
  have hL : IsProperMap L := hF.prodMap hIZ
  have hR : IsProperMap R := hIX.prodMap hG
  have hr : IsProperMap r := (Homeomorph.prodAssoc X Y Z).symm.isProperMap
  let t : CompactSupportKZero ((X × Y) × Z) :=
    compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct a b) c
  change compactSupportKZeroPullback G hG (compactSupportKZeroPullback L hL t) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroPullback R hR (compactSupportKZeroPullback r hr t))
  calc
    compactSupportKZeroPullback G hG (compactSupportKZeroPullback L hL t) =
        compactSupportKZeroPullback (L.comp G) (hL.comp hG) t :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp G L hG hL) t).symm
    _ = compactSupportKZeroPullback (r.comp (R.comp H)) (hr.comp (hR.comp hH)) t := by
      -- Both maps retain z and send it to ((f(g(z)), g(z)), z).
      rfl
    _ = compactSupportKZeroPullback H hH
        (compactSupportKZeroPullback R hR (compactSupportKZeroPullback r hr t)) := by
      rw [compactSupportKZeroPullback_comp (R.comp H) r (hR.comp hH) hr,
        AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp H R hH hR,
        AddMonoidHom.comp_apply]

/-- Proper pullback on the module space commutes with the action of the same base class. -/
theorem compactSupportKZeroPullback_action (f : C(Y, X)) (g : C(Z, Y))
    (hg : IsProperMap g) (a : CompactSupportKZero X) (b : CompactSupportKZero Y) :
    compactSupportKZeroPullback g hg (compactSupportKZeroAction f a b) =
      compactSupportKZeroAction (f.comp g) a (compactSupportKZeroPullback g hg b) := by
  /- Stage 1: the product map id_X × g is proper. The square consisting of this
  product map, g, and the two graph maps commutes on the nose at each z.
  Stage 2: external product commutes with these proper pullbacks, as seen from
  its unique reduced lift under the smash collapse. Proper-pullback composition
  then identifies both sides along the same composite graph. Properness is needed
  only for g and is not imposed on f or on the projections from the product. -/
  let F : C(Y, X × Y) := f.prodMk (ContinuousMap.id Y)
  let H : C(Z, X × Z) := (f.comp g).prodMk (ContinuousMap.id Z)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous continuous_snd isProperMap_id
  have hH : IsProperMap H :=
    isProperMap_of_comp_of_t2 H.continuous continuous_snd isProperMap_id
  have hIX : IsProperMap (ContinuousMap.id X) := isProperMap_id
  -- Only g is assumed proper; the two graph maps are proper independently of f.
  have hproduct := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id X) hIX g hg a b
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
  change compactSupportKZeroPullback g hg
      (compactSupportKZeroPullback F hF (compactSupportKZeroExternalProduct a b)) =
    compactSupportKZeroPullback H hH
      (compactSupportKZeroExternalProduct a (compactSupportKZeroPullback g hg b))
  rw [← hproduct]
  -- The original square commutes at every z: (f(g(z)), g(z)) on both sides.
  let L : C(X × Z, X × Y) := (ContinuousMap.id X).prodMap g
  have hL : IsProperMap L := hIX.prodMap hg
  let t : CompactSupportKZero (X × Y) := compactSupportKZeroExternalProduct a b
  calc
    compactSupportKZeroPullback g hg (compactSupportKZeroPullback F hF t) =
        compactSupportKZeroPullback (F.comp g) (hF.comp hg) t :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp g F hg hF) t).symm
    _ = compactSupportKZeroPullback (L.comp H) (hL.comp hH) t := by rfl
    _ = compactSupportKZeroPullback H hH (compactSupportKZeroPullback L hL t) :=
      DFunLike.congr_fun (compactSupportKZeroPullback_comp H L hH hL) t

/-- The usual K(X)-action on compactly supported K(Y), for compact X and continuous f. -/
def complexKZeroCompactSupportAction [CompactSpace X] (f : C(Y, X)) :
    ComplexKZero X →+ CompactSupportKZero Y →+ CompactSupportKZero Y :=
  (compactSupportKZeroAction f).comp
    (compactSupportKZeroCompactEquiv X).symm.toAddMonoidHom

/-- The compact-base action respects the prescribed tensor multiplication on K(X). -/
theorem complexKZeroCompactSupportAction_mul [CompactSpace X] (f : C(Y, X))
    (a b : ComplexKZero X) (c : CompactSupportKZero Y) :
    complexKZeroCompactSupportAction f (kZeroMul C(X, ℂ) a b) c =
      complexKZeroCompactSupportAction f a (complexKZeroCompactSupportAction f b c) := by
  /- Stage 1: on the compact space X, restriction from X⁺ identifies the product
  obtained by the diagonal graph with the original tensor product kZeroMul.
  Indeed, restrict the defining smash identity to finite points and use absolute
  external-product naturality. The compact-to-absolute equivalence is injective.
  Stage 2: apply compactSupportKZeroAction_assoc to id_X and f. Substitute the
  preceding identification for the two compactly supported representatives of
  a and b. This gives precisely the displayed action, including its fixed
  compact-to-absolute comparison and its original tensor multiplication. -/
  let e : CompactSupportKZero X ≃+ ComplexKZero X := compactSupportKZeroCompactEquiv X
  let δ : C(X, X × X) := (ContinuousMap.id X).prodMk (ContinuousMap.id X)
  have hδ : IsProperMap δ :=
    isProperMap_of_comp_of_t2 δ.continuous continuous_snd isProperMap_id
  -- Finite-point restriction commutes with this same proper diagonal pullback.
  have hfinite (q : CompactSupportKZero (X × X)) :
      compactSupportKZeroToAbsolute (compactSupportKZeroPullback δ hδ q) =
        complexKZeroPullback δ (compactSupportKZeroToAbsolute q) := by
    change complexKZeroPullback
        ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap δ hδ) q.val) =
      complexKZeroPullback δ
        (complexKZeroPullback
          ⟨((↑) : X × X → OnePoint (X × X)), OnePoint.continuous_coe⟩ q.val)
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  have hdiagonal (u v : CompactSupportKZero X) :
      compactSupportKZeroToAbsolute (compactSupportKZeroAction (ContinuousMap.id X) u v) =
        kZeroMul C(X, ℂ) (compactSupportKZeroToAbsolute u)
          (compactSupportKZeroToAbsolute v) := by
    change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback δ hδ (compactSupportKZeroExternalProduct u v)) = _
    rw [hfinite, compactSupportKZeroToAbsolute_externalProduct]
    -- Absolute diagonal pullback is the original tensor multiplication.
    change kZeroMap _ (kZeroMul _ _ _) = _
    rw [kZeroMap_mul]
    change kZeroMul C(X, ℂ)
      (complexKZeroPullback δ
        (complexKZeroPullback ContinuousMap.fst (compactSupportKZeroToAbsolute u)))
      (complexKZeroPullback δ
        (complexKZeroPullback ContinuousMap.snd (compactSupportKZeroToAbsolute v))) = _
    have hfst : (ContinuousMap.fst : C(X × X, X)).comp δ = ContinuousMap.id X := rfl
    have hsnd : (ContinuousMap.snd : C(X × X, X)).comp δ = ContinuousMap.id X := rfl
    have hid : complexKZeroPullback (ContinuousMap.id X) =
        AddMonoidHom.id (ComplexKZero X) := by
      change kZeroMap (RingHom.id C(X, ℂ)) = _
      exact kZeroMap_id
    have hfstPullback : complexKZeroPullback δ
        (complexKZeroPullback ContinuousMap.fst (compactSupportKZeroToAbsolute u)) =
          compactSupportKZeroToAbsolute u := by
      have h := DFunLike.congr_fun
        (complexKZeroPullback_comp δ (ContinuousMap.fst : C(X × X, X)))
        (compactSupportKZeroToAbsolute u)
      simpa only [hfst, hid, AddMonoidHom.id_apply, AddMonoidHom.comp_apply] using h.symm
    have hsndPullback : complexKZeroPullback δ
        (complexKZeroPullback ContinuousMap.snd (compactSupportKZeroToAbsolute v)) =
          compactSupportKZeroToAbsolute v := by
      have h := DFunLike.congr_fun
        (complexKZeroPullback_comp δ (ContinuousMap.snd : C(X × X, X)))
        (compactSupportKZeroToAbsolute v)
      simpa only [hsnd, hid, AddMonoidHom.id_apply, AddMonoidHom.comp_apply] using h.symm
    rw [hfstPullback, hsndPullback]
  have hrepresentative : e.symm (kZeroMul C(X, ℂ) a b) =
      compactSupportKZeroAction (ContinuousMap.id X) (e.symm a) (e.symm b) := by
    apply e.injective
    change e (e.symm (kZeroMul C(X, ℂ) a b)) =
      compactSupportKZeroToAbsolute
        (compactSupportKZeroAction (ContinuousMap.id X) (e.symm a) (e.symm b))
    rw [hdiagonal]
    change e (e.symm (kZeroMul C(X, ℂ) a b)) =
      kZeroMul C(X, ℂ) (e (e.symm a)) (e (e.symm b))
    simp only [e.apply_symm_apply]
  -- Apply graph associativity to id_X followed by the original f.
  change compactSupportKZeroAction f (e.symm (kZeroMul C(X, ℂ) a b)) c =
    compactSupportKZeroAction f (e.symm a)
      (compactSupportKZeroAction f (e.symm b) c)
  rw [hrepresentative]
  simpa only [ContinuousMap.id_comp] using
    compactSupportKZeroAction_assoc (ContinuousMap.id X) f (e.symm a) (e.symm b) c

/-- The original rank-one trivial class acts as the identity on compactly supported K(Y). -/
theorem complexKZeroCompactSupportAction_one [CompactSpace X] (f : C(Y, X))
    (b : CompactSupportKZero Y) :
    complexKZeroCompactSupportAction f
      (kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)) b = b := by
  /- Stage 1: compare the compact-to-absolute inverse of the rank-one class
  with proper pullback of the positive point unit along X → PUnit. Finite
  restriction and the original compact equivalence identify these classes.
  Stage 2: proper-product naturality moves this pullback through the
  external product with b. Compose with the actual graph of f: the result
  is y ↦ (point,y), the inverse of the point-product projection. The
  existing left unit law for that product gives b. This proves the unit
  law for the specified graph action over a compact base. -/
  let e : CompactSupportKZero X ≃+ ComplexKZero X := compactSupportKZeroCompactEquiv X
  let p : C(X, PUnit.{1}) := ContinuousMap.const X PUnit.unit
  have hp : IsProperMap p := p.continuous.isProperMap
  let F : C(Y, X × Y) := f.prodMk (ContinuousMap.id Y)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous continuous_snd isProperMap_id
  have hIY : IsProperMap (ContinuousMap.id Y) := isProperMap_id
  -- Compare the actual compact-base unit with pullback of the positive point unit.
  have hfinite :
      compactSupportKZeroToAbsolute
          (compactSupportKZeroPullback p hp compactSupportKZeroPointOne) =
        complexKZeroPullback p (compactSupportKZeroToAbsolute compactSupportKZeroPointOne) := by
    change complexKZeroPullback
        ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap p hp) compactSupportKZeroPointOne.val) =
      complexKZeroPullback p
        (complexKZeroPullback
          ⟨((↑) : PUnit.{1} → OnePoint PUnit.{1}), OnePoint.continuous_coe⟩
          compactSupportKZeroPointOne.val)
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  have hpoint : compactSupportKZeroToAbsolute compactSupportKZeroPointOne =
      kZeroClass C(PUnit.{1}, ℂ) (IdempotentMatrix.identity C(PUnit.{1}, ℂ) 1) :=
    (compactSupportKZeroCompactEquiv PUnit.{1}).apply_symm_apply _
  have hunit : e.symm
      (kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)) =
        compactSupportKZeroPullback p hp compactSupportKZeroPointOne := by
    apply e.injective
    change e (e.symm
        (kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1))) =
      compactSupportKZeroToAbsolute
        (compactSupportKZeroPullback p hp compactSupportKZeroPointOne)
    rw [e.apply_symm_apply, hfinite, hpoint]
    symm
    change kZeroMap _ (kZeroClass _ _) = _
    rw [kZeroMap_class]
    congr 1
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
    congr 1
    exact (ContinuousMap.compRightAlgHom ℂ ℂ p).toRingHom.mapMatrix.map_one
  have hproduct := compactSupportKZeroExternalProduct_properPullback p hp
    (ContinuousMap.id Y) hIY compactSupportKZeroPointOne b
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
  change compactSupportKZeroAction f
    (e.symm (kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1))) b = b
  rw [hunit]
  change compactSupportKZeroPullback F hF
    (compactSupportKZeroExternalProduct
      (compactSupportKZeroPullback p hp compactSupportKZeroPointOne) b) = b
  rw [← hproduct]
  -- The graph composite forgets only X, retaining the original point and Y coordinate.
  calc
    compactSupportKZeroPullback F hF
        (compactSupportKZeroPullback (p.prodMap (ContinuousMap.id Y)) (hp.prodMap hIY)
          (compactSupportKZeroExternalProduct compactSupportKZeroPointOne b)) =
        compactSupportKZeroPullback ((p.prodMap (ContinuousMap.id Y)).comp F)
          ((hp.prodMap hIY).comp hF)
          (compactSupportKZeroExternalProduct compactSupportKZeroPointOne b) :=
      (DFunLike.congr_fun
        (compactSupportKZeroPullback_comp F (p.prodMap (ContinuousMap.id Y)) hF
          (hp.prodMap hIY)) (compactSupportKZeroExternalProduct compactSupportKZeroPointOne b)).symm
    _ = b := compactSupportKZeroExternalProduct_one_left b

end AtiyahSinger
