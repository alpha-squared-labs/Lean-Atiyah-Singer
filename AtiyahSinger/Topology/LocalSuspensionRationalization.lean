/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EuclideanLocalHomology
public import AtiyahSinger.Topology.SingularHomology

import AtiyahSinger.Topology.SimplexLocalHomology

/-!
# Rationalization and the original local homology suspension

Public module ID: M1947.

Coefficient inclusion commutes with the actual relative triple boundary and
with the specified local suspension. The proof uses the same integral cycle,
its lift in the same short exact sequence, and their rational images. The
excision inverse and transverse projection are the original selected maps.

Source: naturality of the relative homology exact sequence under coefficient
change, Hatcher, Algebraic Topology, Sections 2.1 and 3.A.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits Opposite
open scoped Simplicial

universe u

local notation "ℚRes" => ModuleCat.restrictScalars (Int.castRingHom ℚ)
local notation "ℚResC" => Functor.mapHomologicalComplex
  (ModuleCat.restrictScalars (Int.castRingHom ℚ)) (ComplexShape.down ℕ)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original relative triple boundary commutes with inclusion of integer coefficients. -/
theorem relativeSingularHomologyTripleBoundary_rationalization
    {X : Type u} [TopologicalSpace X] (A B : Set X) (hAB : A ⊆ B) (n : ℕ)
    (c : relativeSingularHomology ℤ B (n + 1)) :
    (shortExact_relativeSingularTripleSequence ℚ A B hAB).δ (n + 1) n rfl
        (relativeSingularHomologyRationalization B (n + 1) c) =
      relativeSingularHomologyRationalization ((Subtype.val : B → X) ⁻¹' A) n
        ((shortExact_relativeSingularTripleSequence ℤ A B hAB).δ (n + 1) n rfl c) := by
  -- The coefficient maps commute on each original simplex and hence on each relative quotient.
  have hordinarySquare {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
      (g : C(Y, Z)) :
      (singularChainsFunctor ℤ).map (TopCat.ofHom g) ≫ singularChainsRationalization Z =
        singularChainsRationalization Y ≫ (ℚResC).map
          ((singularChainsFunctor ℚ).map (TopCat.ofHom g)) := by
    have heval (W : Type u) [TopologicalSpace W] :=
      Classical.choose_spec (existsUnique_singularChainsRationalization W).exists
    have hmap (R : Type) [CommRing R] (n : ℕ)
        (σ : (TopCat.toSSet.obj (TopCat.of Y)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
        ((singularChainsFunctor R).map (TopCat.ofHom g)).f n
          ((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
            (R := singularCoefficient R) σ a) =
          (TopCat.toSSet.obj (TopCat.of Z)).ιChainComplex
            (R := singularCoefficient R)
            ((TopCat.toSSet.map (TopCat.ofHom g)).app (op ⦋n⦌) σ) a := by
      change ((TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex σ ≫
        (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom g))
          (singularCoefficient R)).f n) a = _
      rw [SSet.ι_chainComplexMap_f]
    apply HomologicalComplex.Hom.ext
    funext n
    apply Sigma.hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    let τ := (TopCat.toSSet.map (TopCat.ofHom g)).app (op ⦋n⦌) σ
    have h₁ := congrArg ((singularChainsRationalization Z).f n) (hmap ℤ n σ a)
    have h₂ := heval Z n τ a.down
    have h₃ := hmap ℚ n σ (ULift.up (a.down : ℚ))
    have h₄ := congrArg (((singularChainsFunctor ℚ).map (TopCat.ofHom g)).f n)
      (heval Y n σ a.down)
    exact h₁.trans (h₂.trans (h₃.symm.trans h₄.symm))
  have hrelativeSquare {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
      (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) :
      relativeSingularChainsMap ℤ f hf ≫ relativeSingularChainsRationalization B =
        relativeSingularChainsRationalization A ≫
          (ℚResC).map (relativeSingularChainsMap ℚ f hf) := by
    let PZ := relativeSingularChainsMap ℤ f hf
    let PQ := relativeSingularChainsMap ℚ f hf
    let FA := relativeSingularChainsRationalization A
    let FB := relativeSingularChainsRationalization B
    have hprojection (R : Type) [CommRing R] :
        relativeSingularChainsProjection R A ≫ relativeSingularChainsMap R f hf =
          (singularChainsFunctor R).map (TopCat.ofHom f) ≫
            relativeSingularChainsProjection R B := by
      simp [relativeSingularChainsProjection, relativeSingularChainsMap]
    have hFA : relativeSingularChainsProjection ℤ A ≫ FA =
        singularChainsRationalization X ≫ (ℚResC).map (relativeSingularChainsProjection ℚ A) :=
      Classical.choose_spec (existsUnique_relativeSingularChainsRationalization A).exists
    have hFB : relativeSingularChainsProjection ℤ B ≫ FB =
        singularChainsRationalization Y ≫ (ℚResC).map (relativeSingularChainsProjection ℚ B) :=
      Classical.choose_spec (existsUnique_relativeSingularChainsRationalization B).exists
    have hsquare : PZ ≫ FB = FA ≫ (ℚResC).map PQ := by
      apply (cancel_epi (relativeSingularChainsProjection ℤ A)).mp
      rw [← Category.assoc, hprojection ℤ, Category.assoc, hFB, ← Category.assoc,
        hordinarySquare f, Category.assoc, ← Functor.map_comp, ← hprojection ℚ,
        Functor.map_comp, ← Category.assoc, ← hFA, Category.assoc]
    exact hsquare
  -- The scalar-restriction comparison sends each cycle class to its actual coefficient image.
  have hclass (R S : Type) [CommRing R] [CommRing S] (ι : R →+* S)
      {shape : ComplexShape ℕ}
      (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (D : HomologicalComplex (ModuleCat.{u} S) shape)
      (F : C ⟶ (Functor.mapHomologicalComplex (ModuleCat.restrictScalars ι)
        shape).obj D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K)
      (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
      ((D.sc n).mapHomologyIso (ModuleCat.restrictScalars ι)).hom
        (HomologicalComplex.homologyMap F n
          ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a))) =
        (D.sc n).moduleCatHomologyIso.inv ((D.sc n).moduleCatToCycles.range.mkQ b) := by
    let S := (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      shape n).map F
    let G := ShortComplex.leftHomologyMapData S
      (C.sc n).moduleCatLeftHomologyData
        ((D.sc n).moduleCatLeftHomologyData.map (ModuleCat.restrictScalars ι))
    have hcycles : G.φK a = b := by
      apply Subtype.ext
      exact (congrArg (fun f ↦ f a) G.commi).trans h
    have hquot := congrArg (fun f ↦ f a) G.commπ
    change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
      (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
    rw [hcycles] at hquot
    have hmap := G.homologyMap_eq
    change HomologicalComplex.homologyMap F n = _ at hmap
    rw [hmap, (D.sc n).moduleCatLeftHomologyData.mapHomologyIso_eq (ModuleCat.restrictScalars ι)]
    let J := ((D.sc n).moduleCatLeftHomologyData.map (ModuleCat.restrictScalars ι)).homologyIso
    change (D.sc n).moduleCatHomologyIso.inv
      (J.hom (J.inv (G.φH ((C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)))))) = _
    have hcancel : (C.sc n).moduleCatHomologyIso.hom
        ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)) =
          (C.sc n).moduleCatToCycles.range.mkQ a :=
      congrArg (fun f ↦ f ((C.sc n).moduleCatToCycles.range.mkQ a))
        (C.sc n).moduleCatHomologyIso.inv_hom_id
    rw [hcancel]
    have hJ : J.hom (J.inv (G.φH ((C.sc n).moduleCatToCycles.range.mkQ a))) =
        G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) :=
      congrArg (fun f ↦ f (G.φH ((C.sc n).moduleCatToCycles.range.mkQ a))) J.inv_hom_id
    rw [hJ, hquot]
  have hrep (R : Type) [CommRing R] {shape : ComplexShape ℕ}
      (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (n : ℕ) (x : C.homology n) :
      ∃ a : (C.sc n).moduleCatLeftHomologyData.K,
        (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x := by
    obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
      ((C.sc n).moduleCatHomologyIso.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact congrArg (fun f ↦ f x) (C.sc n).moduleCatHomologyIso.hom_inv_id
  have hcycles (R S : Type) [CommRing R] [CommRing S] (ι : R →+* S)
      {shape : ComplexShape ℕ}
      (C : HomologicalComplex (ModuleCat.{u} R) shape)
      (D : HomologicalComplex (ModuleCat.{u} S) shape)
      (F : C ⟶ (Functor.mapHomologicalComplex (ModuleCat.restrictScalars ι)
        shape).obj D) (n : ℕ)
      (a : (C.sc n).moduleCatLeftHomologyData.K) :
      ∃ b : (D.sc n).moduleCatLeftHomologyData.K, b.val = F.f n a.val := by
    refine ⟨⟨F.f n a.val, ?_⟩, rfl⟩
    change D.dFrom n (F.f n a.val) = 0
    have heq := congrArg (fun f ↦ f a.val) (F.comm_from n)
    change D.dFrom n (F.f n a.val) = F.next n (C.dFrom n a.val) at heq
    rw [heq]
    have hz : C.dFrom n a.val = 0 := a.property
    rw [hz, map_zero]
  let S := relativeSingularTripleSequence ℤ A B hAB
  let T := relativeSingularTripleSequence ℚ A B hAB
  let hS := shortExact_relativeSingularTripleSequence ℤ A B hAB
  let hT := shortExact_relativeSingularTripleSequence ℚ A B hAB
  let F₁ := relativeSingularChainsRationalization ((Subtype.val : B → X) ⁻¹' A)
  let F₂ := relativeSingularChainsRationalization A
  let F₃ := relativeSingularChainsRationalization B
  have hfirst : S.f ≫ F₂ = F₁ ≫ (ℚResC).map T.f :=
    hrelativeSquare (⟨Subtype.val, continuous_subtype_val⟩ : C(B, X)) (fun _ hx ↦ hx)
  have hsecond : S.g ≫ F₃ = F₂ ≫ (ℚResC).map T.g :=
    hrelativeSquare (ContinuousMap.id X) (fun _ hx ↦ hAB hx)
  have hSn (j : ℕ) :
      (S.map (eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) j)).ShortExact :=
    hS.map_of_exact _
  -- Lift the original integral cycle and its boundary through this exact triple.
  obtain ⟨c₃, rfl⟩ := hrep ℤ S.X₃ (n + 1) c
  obtain ⟨c₂, hc₂⟩ := (hSn (n + 1)).moduleCat_surjective_g c₃.val
  change S.g.f (n + 1) c₂ = c₃.val at hc₂
  have hdc : S.g.f n (S.X₂.d (n + 1) n c₂) = 0 := by
    have h := congrArg (fun f ↦ f c₂) (S.g.comm (n + 1) n)
    change S.X₃.d (n + 1) n (S.g.f (n + 1) c₂) =
      S.g.f n (S.X₂.d (n + 1) n c₂) at h
    rw [← h, hc₂]
    have hc : S.X₃.d (n + 1) ((ComplexShape.down ℕ).next (n + 1)) c₃.val = 0 :=
      c₃.property
    exact (congrArg (fun j ↦ S.X₃.d (n + 1) j c₃.val = 0)
      (ChainComplex.next_nat_succ n)).mp hc
  obtain ⟨b₁, hb₁⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hSn n).exact (S.X₂.d (n + 1) n c₂) hdc
  change S.f.f n b₁ = S.X₂.d (n + 1) n c₂ at hb₁
  have hbclosed : S.X₁.d n ((ComplexShape.down ℕ).next n) b₁ = 0 := by
    apply (hSn ((ComplexShape.down ℕ).next n)).moduleCat_injective_f
    rw [map_zero]
    change S.f.f ((ComplexShape.down ℕ).next n)
      (S.X₁.d n ((ComplexShape.down ℕ).next n) b₁) = 0
    have h := congrArg (fun f ↦ f b₁) (S.f.comm n ((ComplexShape.down ℕ).next n))
    change S.X₂.d n ((ComplexShape.down ℕ).next n) (S.f.f n b₁) =
      S.f.f ((ComplexShape.down ℕ).next n) (S.X₁.d n ((ComplexShape.down ℕ).next n) b₁)
      at h
    rw [← h, hb₁]
    exact congrArg (fun f : S.X₂.X (n + 1) ⟶ S.X₂.X ((ComplexShape.down ℕ).next n) ↦
      f c₂) (S.X₂.d_comp_d (n + 1) n ((ComplexShape.down ℕ).next n))
  let c₁ : (S.X₁.sc n).moduleCatLeftHomologyData.K := ⟨b₁, hbclosed⟩
  have hδZ := homologyConnecting_cycleClass ℤ S hS n c₃ c₂ hc₂ c₁ hb₁
  -- The coefficient images of these same chains are valid rational connecting representatives.
  obtain ⟨c₃Q, hc₃Q⟩ := hcycles ℤ ℚ (Int.castRingHom ℚ) S.X₃ T.X₃ F₃ (n + 1) c₃
  obtain ⟨c₁Q, hc₁Q⟩ := hcycles ℤ ℚ (Int.castRingHom ℚ) S.X₁ T.X₁ F₁ n c₁
  let c₂Q := F₂.f (n + 1) c₂
  have hQc₂ : T.g.f (n + 1) c₂Q = c₃Q.val := by
    have h := congrArg (fun f ↦ f.f (n + 1) c₂) hsecond
    change F₃.f (n + 1) (S.g.f (n + 1) c₂) = T.g.f (n + 1) c₂Q at h
    rw [hc₂] at h
    exact h.symm.trans hc₃Q.symm
  have hQb₁ : T.f.f n c₁Q.val = T.X₂.d (n + 1) n c₂Q := by
    have h := congrArg (fun f ↦ f.f n c₁.val) hfirst
    change F₂.f n (S.f.f n c₁.val) = T.f.f n (F₁.f n c₁.val) at h
    calc
      T.f.f n c₁Q.val = T.f.f n (F₁.f n c₁.val) := congrArg (T.f.f n) hc₁Q
      _ = F₂.f n (S.f.f n c₁.val) := h.symm
      _ = F₂.f n (S.X₂.d (n + 1) n c₂) := congrArg (F₂.f n) hb₁
      _ = T.X₂.d (n + 1) n c₂Q :=
        (congrArg (fun f ↦ f c₂) (F₂.comm (n + 1) n)).symm
  have hδQ := homologyConnecting_cycleClass ℚ T hT n c₃Q c₂Q hQc₂ c₁Q hQb₁
  have hclass₃ := hclass ℤ ℚ (Int.castRingHom ℚ) S.X₃ T.X₃ F₃
    (n + 1) c₃ c₃Q hc₃Q.symm
  have hclass₁ := hclass ℤ ℚ (Int.castRingHom ℚ) S.X₁ T.X₁ F₁ n c₁ c₁Q hc₁Q.symm
  change relativeSingularHomologyRationalization B (n + 1) _ = _ at hclass₃
  change relativeSingularHomologyRationalization ((Subtype.val : B → X) ⁻¹' A) n _ = _
    at hclass₁
  rw [hclass₃, hδZ]
  exact hδQ.trans hclass₁.symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified local suspension commutes with the original
integer-to-rational coefficient map. -/
theorem euclideanLocalSuspensionIso_rationalization
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (c : relativeSingularHomology ℤ (Set.ofPred (fun z : ℝ × E ↦ z ≠ 0)) (k + 1)) :
    (euclideanLocalSuspensionIso ℚ E k).hom
        (relativeSingularHomologyRationalization (Set.ofPred (fun z : ℝ × E ↦ z ≠ 0)) (k + 1) c) =
      relativeSingularHomologyRationalization (Set.ofPred (fun y : E ↦ y ≠ 0)) k
        ((euclideanLocalSuspensionIso ℤ E k).hom c) := by
  let A := (Subtype.val : euclideanPuncturedHalfSpace E 1 → ℝ × E) ⁻¹'
    euclideanPuncturedHalfSpace E (-1)
  let B := (Subtype.val : (Set.ofPred (fun z : ℝ × E ↦ z ≠ 0)) → ℝ × E) ⁻¹'
    euclideanPuncturedHalfSpace E (-1)
  let JZ := relativeSingularHomologyMap ℤ (euclideanLocalSuspensionInclusion E)
    (A := A) (B := B) (fun _ hx ↦ hx) k
  let JQ := relativeSingularHomologyMap ℚ (euclideanLocalSuspensionInclusion E)
    (A := A) (B := B) (fun _ hx ↦ hx) k
  let : IsIso JZ := isIso_euclideanLocalSuspensionExcision ℤ E k
  let : IsIso JQ := isIso_euclideanLocalSuspensionExcision ℚ E k
  let dZ := (euclideanLocalSuspensionBoundaryIso ℤ E k).hom c
  let dQ := (euclideanLocalSuspensionBoundaryIso ℚ E k).hom
    (relativeSingularHomologyRationalization (Set.ofPred (fun z : ℝ × E ↦ z ≠ 0)) (k + 1) c)
  have hδ : dQ = relativeSingularHomologyRationalization B k dZ :=
    relativeSingularHomologyTripleBoundary_rationalization
      (euclideanPuncturedHalfSpace E (-1)) (Set.ofPred (fun z : ℝ × E ↦ z ≠ 0))
      (euclideanPuncturedHalfSpace_subset E (-1)) k c
  -- Excision uses the inverse of the same map on the same connecting class.
  let zZ := (asIso JZ).inv dZ
  have hJZ : JZ zZ = dZ := Iso.inv_hom_id_apply (asIso JZ) dZ
  have hJQ : JQ (relativeSingularHomologyRationalization A k zZ) = dQ := by
    have h := relativeSingularHomologyRationalization_naturality
      (euclideanLocalSuspensionInclusion E) (A := A) (B := B) (fun _ hx ↦ hx) k zZ
    exact h.symm.trans ((congrArg (relativeSingularHomologyRationalization B k) hJZ).trans
      hδ.symm)
  have hzinv : (asIso JQ).inv dQ = relativeSingularHomologyRationalization A k zZ := by
    apply (ConcreteCategory.isIso_iff_bijective JQ).mp inferInstance |>.injective
    exact (Iso.inv_hom_id_apply (asIso JQ) dQ).trans hJQ.symm
  -- Naturality of the actual transverse projection completes the composite.
  change relativeSingularHomologyMap ℚ (euclideanLocalSuspensionProjection E)
      (euclideanLocalSuspensionProjection_mapsTo E) k ((asIso JQ).inv dQ) =
    relativeSingularHomologyRationalization (Set.ofPred (fun y : E ↦ y ≠ 0)) k
      (relativeSingularHomologyMap ℤ (euclideanLocalSuspensionProjection E)
        (euclideanLocalSuspensionProjection_mapsTo E) k zZ)
  rw [hzinv]
  exact (relativeSingularHomologyRationalization_naturality
    (euclideanLocalSuspensionProjection E) (euclideanLocalSuspensionProjection_mapsTo E)
    k zZ).symm

end AtiyahSinger
