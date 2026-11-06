/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCohomologySequenceCup
public import AtiyahSinger.Topology.SingularCohomologyUnits
public import AtiyahSinger.Topology.TrivialCohomologyThom

/-!
# The actual cup map for a trivial real bundle

Public module ID: M2262.

Relative suspension is compatible with the original ordinary-relative cup
action, with the sign supplied by its connecting homomorphism. Iterating this
comparison identifies the Thom map with its prescribed factor order. Cup
with any top-degree class that generates every fiber is therefore bijective.

Source: Hatcher, Algebraic Topology, Sections 3.2 and 4.D; the arbitrary-base
calculation is performed directly on the original relative pairs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits Opposite Topology

universe u

variable (R : Type) [CommRing R]
  (X : Type u) [TopologicalSpace X]
  (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Suspension and the base cup action satisfy the connecting-map degree sign. -/
theorem relativeSingularCohomologyProdSuspensionIso_action (p q : ℕ)
    (a : singularCohomology R X p)
    (b : relativeSingularCohomology R {z : X × E | z.2 ≠ 0} q) :
    (relativeSingularCohomologyProdSuspensionIso R X E (p + q)).hom
        (relativeSingularCohomologyAction R {z : X × E | z.2 ≠ 0} p q
          (singularCohomologyPullback R (⟨Prod.fst, continuous_fst⟩ : C(X × E, X)) p a) b) =
      (-1 : R) ^ p • relativeSingularCohomologyAction R
        {z : X × (ℝ × E) | z.2 ≠ 0} p (q + 1)
        (singularCohomologyPullback R (⟨Prod.fst, continuous_fst⟩ : C(X × (ℝ × E), X)) p a)
        ((relativeSingularCohomologyProdSuspensionIso R X E q).hom b) := by
  let L : Set (X × (ℝ × E)) := {z | z.2 ∈ euclideanPuncturedHalfSpace E (-1)}
  let P : Set (X × (ℝ × E)) := {z | z.2 ≠ 0}
  let U : Set (X × (ℝ × E)) := {z | z.2 ∈ euclideanPuncturedHalfSpace E 1}
  let B : Set P := (Subtype.val : P → X × (ℝ × E)) ⁻¹' L
  let A : Set U := (Subtype.val : U → X × (ℝ × E)) ⁻¹' L
  let Q : Set (X × E) := {z | z.2 ≠ 0}
  have hLP : L ⊆ P := fun _ hz ↦ euclideanPuncturedHalfSpace_subset E (-1) hz
  let inc : C(U, P) := ⟨fun z ↦
    ⟨z.val, euclideanPuncturedHalfSpace_subset E 1 z.property⟩, by fun_prop⟩
  let pr : C(U, X × E) := ⟨fun z ↦ (z.val.1, z.val.2.2), by fun_prop⟩
  have hpr : Set.MapsTo pr A Q := by
    intro z hz
    exact euclideanLocalSuspensionProjection_mapsTo E (x := ⟨z.val.2, z.property⟩) hz
  let exc (k : ℕ) := relativeSingularCohomologyPullback R inc
    (A := A) (B := B) (fun _ hz ↦ hz) k
  let proj (k : ℕ) := relativeSingularCohomologyPullback R pr hpr k
  let δ (k : ℕ) :=
    (shortExact_relativeSingularCochainTripleSequence R L P hLP).δ k (k + 1) rfl
  -- Excision identifies the two original transverse pairs in both relevant degrees.
  have hexc (k : ℕ) : IsIso (exc k) := by
    have hB : IsOpen B := ((isOpen_euclideanPuncturedHalfSpace E (-1)).preimage
      continuous_snd).preimage continuous_subtype_val
    have hi : IsOpenEmbedding inc := by
      apply IsOpenEmbedding.of_comp inc
        (isOpen_ne_fun continuous_snd continuous_const).isOpenEmbedding_subtypeVal
      exact ((isOpen_euclideanPuncturedHalfSpace E 1).preimage
        continuous_snd).isOpenEmbedding_subtypeVal
    have hrange : Bᶜ ⊆ Set.range inc := by
      intro z hz
      have hy : z.val.2.2 = 0 := by
        by_contra h
        exact hz (Or.inr h)
      have ht : z.val.2.1 ≠ 0 := fun h ↦ z.property (Prod.ext h hy)
      have hpos : 0 < z.val.2.1 := by
        by_contra h
        have hneg : z.val.2.1 < 0 := lt_of_le_of_ne (le_of_not_gt h) ht
        apply hz
        left
        linarith
      exact ⟨⟨z.val, Or.inl (by simpa using hpos)⟩, rfl⟩
    have hchain {A' : Set U} {B' : Set P}
        (hA : A' = (inc ⁻¹' Bᶜ)ᶜ) (hBB : B' = Bᶜᶜ)
        (hf : Set.MapsTo inc A' B') :
        homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
          (relativeSingularChainsMap R inc hf) := by
      subst A' B'
      exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R inc
        hi Bᶜ hB.isClosed_compl hrange
    exact isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R _
      (hchain (A' := A) (B' := B)
        (by simp only [Set.preimage_compl, compl_compl]; rfl)
        (compl_compl B).symm (fun _ hz ↦ hz)) k
  let := hexc q
  let := hexc (p + q)
  let π₀ : C(X × E, X) := ⟨Prod.fst, continuous_fst⟩
  let π₁ : C(X × (ℝ × E), X) := ⟨Prod.fst, continuous_fst⟩
  let i : C(P, X × (ℝ × E)) := ⟨Subtype.val, continuous_subtype_val⟩
  let a₀ := singularCohomologyPullback R π₀ p a
  let a₁ := singularCohomologyPullback R π₁ p a
  let aP := singularCohomologyPullback R i p a₁
  let c := inv (exc q) (proj q b)
  have hbase : singularCohomologyPullback R inc p aP =
      singularCohomologyPullback R pr p a₀ := by
    have hmaps : singularCohomologyPullback R π₁ p ≫
        singularCohomologyPullback R i p ≫ singularCohomologyPullback R inc p =
      singularCohomologyPullback R π₀ p ≫ singularCohomologyPullback R pr p := by
      simp only [singularCohomologyPullback, ← Functor.map_comp, ← op_comp]
      rfl
    exact congrArg (fun f ↦ f a) hmaps
  -- Pullback of the same base cocycle identifies the lifted product before applying δ.
  have hproduct : inv (exc (p + q))
      (proj (p + q) (relativeSingularCohomologyAction R Q p q a₀ b)) =
        relativeSingularCohomologyAction R B p q aP c := by
    apply ((ConcreteCategory.isIso_iff_bijective (exc (p + q))).mp inferInstance).injective
    have hinv (k : ℕ) [IsIso (exc k)] (z : relativeSingularCohomology R A k) :
        exc k (inv (exc k) z) = z :=
      congrArg (fun f ↦ f z) (IsIso.inv_hom_id (exc k))
    rw [hinv]
    have hinc := relativeSingularCohomologyPullback_action R inc
      (A := A) (B := B) (fun _ hz ↦ hz) p q aP c
    have hproj := relativeSingularCohomologyPullback_action R pr hpr p q a₀ b
    change exc (p + q) (relativeSingularCohomologyAction R B p q aP c) =
      relativeSingularCohomologyAction R A p q
        (singularCohomologyPullback R inc p aP) (exc q c) at hinc
    change proj (p + q) (relativeSingularCohomologyAction R Q p q a₀ b) =
      relativeSingularCohomologyAction R A p q
        (singularCohomologyPullback R pr p a₀) (proj q b) at hproj
    rw [hinc, hbase]
    change _ = relativeSingularCohomologyAction R A p q
      (singularCohomologyPullback R pr p a₀) (exc q (inv (exc q) (proj q b)))
    rw [hinv]
    exact hproj
  have hδ := relativeSingularCohomologyTripleBoundary_action R L P hLP p q a₁ c
  change δ (p + q) (inv (exc (p + q))
      (proj (p + q) (relativeSingularCohomologyAction R Q p q a₀ b))) =
    (-1 : R) ^ p • relativeSingularCohomologyAction R P p (q + 1) a₁ (δ q c)
  rw [hproduct]
  exact hδ

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pointed fiber-coordinate change preserves the same base cup action. -/
theorem relativeSingularCohomologyProdHomeomorphIso_action
    {V W : Type} [TopologicalSpace V] [TopologicalSpace W] [Zero V] [Zero W]
    (e : V ≃ₜ W) (he : e 0 = 0) (p q : ℕ)
    (a : singularCohomology R X p)
    (b : relativeSingularCohomology R {z : X × W | z.2 ≠ 0} q) :
    (relativeSingularCohomologyProdHomeomorphIso R X e he (p + q)).hom
        (relativeSingularCohomologyAction R {z : X × W | z.2 ≠ 0} p q
          (singularCohomologyPullback R (⟨Prod.fst, continuous_fst⟩ : C(X × W, X)) p a) b) =
      relativeSingularCohomologyAction R {z : X × V | z.2 ≠ 0} p q
        (singularCohomologyPullback R (⟨Prod.fst, continuous_fst⟩ : C(X × V, X)) p a)
        ((relativeSingularCohomologyProdHomeomorphIso R X e he q).hom b) := by
  let f : C(X × V, X × W) :=
    ⟨(Homeomorph.refl X).prodCongr e, (Homeomorph.refl X).continuous.prodMap e.continuous⟩
  have hf : Set.MapsTo f {z | z.2 ≠ 0} {z | z.2 ≠ 0} := by
    intro z hz h
    exact hz (e.injective (h.trans he.symm))
  let πV : C(X × V, X) := ⟨Prod.fst, continuous_fst⟩
  let πW : C(X × W, X) := ⟨Prod.fst, continuous_fst⟩
  have hbase : singularCohomologyPullback R πW p ≫ singularCohomologyPullback R f p =
      singularCohomologyPullback R πV p := by
    simp only [singularCohomologyPullback, ← Functor.map_comp, ← op_comp]
    rfl
  have h := relativeSingularCohomologyPullback_action R f hf p q
    (singularCohomologyPullback R πW p a) b
  change (relativeSingularCohomologyProdHomeomorphIso R X e he (p + q)).hom _ =
    relativeSingularCohomologyAction R {z : X × V | z.2 ≠ 0} p q
      (singularCohomologyPullback R f p (singularCohomologyPullback R πW p a))
      ((relativeSingularCohomologyProdHomeomorphIso R X e he q).hom b) at h
  have ha := congrArg (fun t ↦ t a) hbase
  change singularCohomologyPullback R f p (singularCohomologyPullback R πW p a) =
    singularCohomologyPullback R πV p a at ha
  rw [ha] at h
  exact h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In rank zero the original empty-pair comparison transports the ordinary cup product. -/
theorem relativeSingularCohomologyProdPiIso_zero_action (p : ℕ)
    (a : singularCohomology R X p) (c : singularCohomology R X 0) :
    (relativeSingularCohomologyProdPiIso R X 0 p).hom (singularCohomologyCup R X p 0 a c) =
      relativeSingularCohomologyAction R {z : X × (Fin 0 → ℝ) | z.2 ≠ 0} p 0
        (singularCohomologyPullback R (⟨Prod.fst, continuous_fst⟩ : C(X × (Fin 0 → ℝ), X)) p a)
        ((relativeSingularCohomologyProdPiIso R X 0 0).hom c) := by
  let Q : Set (X × (Fin 0 → ℝ)) := {z | z.2 ≠ 0}
  have hQ : Q = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz (Subsingleton.elim _ _)
  let j (k : ℕ) := relativeSingularCohomologyToOrdinary R Q k
  have hj (k : ℕ) : IsIso (j k) := by
    dsimp only [j]
    rw [hQ]
    exact isIso_relativeSingularCohomologyToOrdinary_empty R _ k
  let := hj p
  let := hj 0
  let π : C(X × (Fin 0 → ℝ), X) := ⟨Prod.fst, continuous_fst⟩
  have hcomp (k : ℕ) : (relativeSingularCohomologyProdPiIso R X 0 k).hom ≫ j k =
      singularCohomologyPullback R π k := by
    let := hj k
    change (singularCohomologyPullback R π k ≫ inv (j k)) ≫ j k = _
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply ((ConcreteCategory.isIso_iff_bijective (j p)).mp inferInstance).injective
  have hleft := congrArg (fun f ↦ f (singularCohomologyCup R X p 0 a c)) (hcomp p)
  have hright := congrArg (fun f ↦ f c) (hcomp 0)
  change j p ((relativeSingularCohomologyProdPiIso R X 0 p).hom
    (singularCohomologyCup R X p 0 a c)) = _ at hleft
  change j 0 ((relativeSingularCohomologyProdPiIso R X 0 0).hom c) = _ at hright
  rw [hleft]
  have h := relativeSingularCohomologyToOrdinary_action R Q p 0
    (singularCohomologyPullback R π p a) ((relativeSingularCohomologyProdPiIso R X 0 0).hom c)
  change j p _ = singularCohomologyCup R (X × (Fin 0 → ℝ)) p 0
    (singularCohomologyPullback R π p a)
    (j 0 ((relativeSingularCohomologyProdPiIso R X 0 0).hom c)) at h
  rw [h, hright]
  exact singularCohomologyPullback_cup R π p 0 a c

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Cup with any fiberwise generator is a Thom isomorphism on a trivial real bundle. -/
theorem relativeSingularCohomologyAction_prod_pi_bijective (n : ℕ)
    (U : relativeSingularCohomology R {z : X × (Fin n → ℝ) | z.2 ≠ 0} n)
    (hU : ∀ x : X, Function.Bijective (fun r : R ↦ r •
      relativeSingularCohomologyPullback R
        ((ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id (Fin n → ℝ)))
        (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) n U)) (p : ℕ) :
    Function.Bijective (fun a : singularCohomology R X p ↦
      relativeSingularCohomologyAction R {z : X × (Fin n → ℝ) | z.2 ≠ 0} p n
        (singularCohomologyPullback R
          (⟨Prod.fst, continuous_fst⟩ : C(X × (Fin n → ℝ), X)) p a) U) := by
  let Q (Z : Type u) (n : ℕ) : Set (Z × (Fin n → ℝ)) := {z | z.2 ≠ 0}
  have hgenerator {M N : ModuleCat.{u} R} (iso : M ≅ N) (x : M) (y : N)
      (hxy : iso.hom x = y) (hy : Function.Bijective (fun r : R ↦ r • y)) :
      Function.Bijective (fun r : R ↦ r • x) := by
    have hcomp : Function.Bijective (iso.hom ∘ fun r : R ↦ r • x) := by
      simpa only [Function.comp_def, map_smul, hxy] using hy
    exact hcomp.of_comp_left
      ((ConcreteCategory.isIso_iff_bijective iso.hom).mp inferInstance).injective
  revert p
  revert U
  induction n with
  | zero =>
    intro U hU p
    let iso (Z : Type u) [TopologicalSpace Z] (k : ℕ) :=
      relativeSingularCohomologyProdPiIso R Z 0 k
    let c := (iso X 0).inv U
    have hpoint (x : X) : Function.Bijective (fun r : R ↦ r •
        singularCohomologyPullback R (ContinuousMap.const PUnit.{u + 1} x) 0 c) := by
      let f : C(PUnit.{u + 1}, X) := ContinuousMap.const _ x
      let pull := relativeSingularCohomologyPullback R
        (f.prodMap (ContinuousMap.id (Fin 0 → ℝ)))
        (A := Q PUnit.{u + 1} 0) (B := Q X 0) (fun _ hz ↦ hz) 0
      have hn : (iso X 0).hom ≫ pull =
          singularCohomologyPullback R f 0 ≫ (iso PUnit 0).hom :=
        relativeSingularCohomologyProdPiIso_natural R PUnit f 0 0
      have hc : (iso X 0).hom c = U := Iso.inv_hom_id_apply _ _
      have hv := congrArg (fun g ↦ g c) hn
      change pull ((iso X 0).hom c) =
        (iso PUnit 0).hom (singularCohomologyPullback R f 0 c) at hv
      rw [hc] at hv
      exact hgenerator (iso PUnit 0) _ (pull U) hv.symm (hU x)
    -- The zero-dimensional pair is the empty pair, with an arbitrary degree-zero unit class.
    have hc := singularCohomologyCup_bijective_of_pointwise_generator R X c hpoint p
    have hb := ((ConcreteCategory.isIso_iff_bijective (iso X p).hom).mp inferInstance).comp hc
    have hformula (a : singularCohomology R X p) :
        (iso X p).hom (singularCohomologyCup R X p 0 a c) =
      relativeSingularCohomologyAction R (Q X 0) p 0
        (singularCohomologyPullback R
          (⟨Prod.fst, continuous_fst⟩ : C(X × (Fin 0 → ℝ), X)) p a) U := by
      have h := relativeSingularCohomologyProdPiIso_zero_action R X p a c
      have hu : (iso X 0).hom c = U := Iso.inv_hom_id_apply _ _
      change (iso X p).hom (singularCohomologyCup R X p 0 a c) =
        relativeSingularCohomologyAction R (Q X 0) p 0
          (singularCohomologyPullback R
            (⟨Prod.fst, continuous_fst⟩ : C(X × (Fin 0 → ℝ), X)) p a) ((iso X 0).hom c) at h
      rw [hu] at h
      exact h
    exact (congrArg (fun f ↦ Function.Bijective f) (funext hformula)).mp hb
  | succ n ih =>
    intro U hU p
    let e : (Fin (n + 1) → ℝ) ≃ₜ ℝ × (Fin n → ℝ) :=
      Homeomorph.ulift.symm.trans ((euclideanLocalCoordinateSplit.{0} n).trans
        ((Homeomorph.refl ℝ).prodCongr Homeomorph.ulift))
    have he : e 0 = 0 := rfl
    let iso (Z : Type u) [TopologicalSpace Z] (k : ℕ) :
        relativeSingularCohomology R (Q Z n) k ≅
          relativeSingularCohomology R (Q Z (n + 1)) (k + 1) :=
      relativeSingularCohomologyProdSuspensionIso R Z (Fin n → ℝ) k ≪≫
        relativeSingularCohomologyProdHomeomorphIso R Z e he (k + 1)
    let c := (iso X n).inv U
    have hpoint (x : X) : Function.Bijective (fun r : R ↦ r •
      relativeSingularCohomologyPullback R
        ((ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id (Fin n → ℝ)))
        (A := Q PUnit.{u + 1} n) (B := Q X n) (fun _ hz ↦ hz) n c) := by
      let f : C(PUnit.{u + 1}, X) := ContinuousMap.const _ x
      let pull (m : ℕ) := relativeSingularCohomologyPullback R
        (f.prodMap (ContinuousMap.id (Fin m → ℝ)))
        (A := Q PUnit.{u + 1} m) (B := Q X m) (fun _ hz ↦ hz) m
      have hn : (iso X n).hom ≫ pull (n + 1) = pull n ≫ (iso PUnit n).hom :=
        (CommSq.horiz_comp
          ⟨relativeSingularCohomologyProdSuspensionIso_natural R PUnit (Fin n → ℝ) f n⟩
          ⟨relativeSingularCohomologyProdHomeomorphIso_natural R PUnit f e he (n + 1)⟩).w
      have hc : (iso X n).hom c = U := Iso.inv_hom_id_apply _ _
      have hv := congrArg (fun g ↦ g c) hn
      change pull (n + 1) ((iso X n).hom c) = (iso PUnit n).hom (pull n c) at hv
      rw [hc] at hv
      exact hgenerator (iso PUnit n) _ (pull (n + 1) U) hv.symm (hU x)
    have hc := ih c hpoint p
    have hb := ((ConcreteCategory.isIso_iff_bijective (iso X (p + n)).hom).mp
      inferInstance).comp hc
    -- One more suspension conjugates the two actual cup maps, up to the invertible sign.
    have hformula (a : singularCohomology R X p) :
        (iso X (p + n)).hom (relativeSingularCohomologyAction R (Q X n) p n
          (singularCohomologyPullback R
            (⟨Prod.fst, continuous_fst⟩ : C(X × (Fin n → ℝ), X)) p a) c) =
      (-1 : R) ^ p • relativeSingularCohomologyAction R (Q X (n + 1)) p (n + 1)
        (singularCohomologyPullback R
          (⟨Prod.fst, continuous_fst⟩ : C(X × (Fin (n + 1) → ℝ), X)) p a) U := by
      change (relativeSingularCohomologyProdHomeomorphIso R X e he (p + n + 1)).hom
        ((relativeSingularCohomologyProdSuspensionIso R X (Fin n → ℝ) (p + n)).hom
          (relativeSingularCohomologyAction R (Q X n) p n _ c)) = _
      rw [relativeSingularCohomologyProdSuspensionIso_action, map_smul]
      have hh := relativeSingularCohomologyProdHomeomorphIso_action R X e he p (n + 1) a
        ((relativeSingularCohomologyProdSuspensionIso R X (Fin n → ℝ) n).hom c)
      have hu : (relativeSingularCohomologyProdHomeomorphIso R X e he (n + 1)).hom
          ((relativeSingularCohomologyProdSuspensionIso R X (Fin n → ℝ) n).hom c) = U :=
        Iso.inv_hom_id_apply (iso X n) U
      rw [hu] at hh
      exact congrArg (fun z ↦ (-1 : R) ^ p • z) hh
    have hscaled : Function.Bijective (fun a : singularCohomology R X p ↦
        (-1 : R) ^ p • relativeSingularCohomologyAction R (Q X (n + 1)) p (n + 1)
          (singularCohomologyPullback R
            (⟨Prod.fst, continuous_fst⟩ : C(X × (Fin (n + 1) → ℝ), X)) p a) U) := by
      exact (congrArg (fun f ↦ Function.Bijective f) (funext hformula)).mp hb
    exact hscaled.of_comp_left ((isUnit_neg_one.pow p).smul_bijective).injective

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified fiberwise generator gives the actual Thom bijection in the Euclidean model. -/
theorem relativeSingularCohomologyAction_prod_euclidean_bijective (n : ℕ)
    (U : relativeSingularCohomology R
      {z : X × EuclideanSpace ℝ (Fin n) | z.2 ≠ 0} n)
    (hU : ∀ x : X, Function.Bijective (fun r : R ↦ r •
      relativeSingularCohomologyPullback R
        ((ContinuousMap.const PUnit.{u + 1} x).prodMap
          (ContinuousMap.id (EuclideanSpace ℝ (Fin n))))
        (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) n U)) (p : ℕ) :
    Function.Bijective (fun a : singularCohomology R X p ↦
      relativeSingularCohomologyAction R
        {z : X × EuclideanSpace ℝ (Fin n) | z.2 ≠ 0} p n
        (singularCohomologyPullback R
          (⟨Prod.fst, continuous_fst⟩ : C(X × EuclideanSpace ℝ (Fin n), X)) p a) U) := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  have he : e 0 = 0 := (EuclideanSpace.equiv (Fin n) ℝ).map_zero
  let iso (Z : Type u) [TopologicalSpace Z] (k : ℕ) :=
    relativeSingularCohomologyProdHomeomorphIso R Z e he k
  let c := (iso X n).inv U
  have hpoint (x : X) : Function.Bijective (fun r : R ↦ r •
      relativeSingularCohomologyPullback R
        ((ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id (Fin n → ℝ)))
        (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) n c) := by
    let f : C(PUnit.{u + 1}, X) := ContinuousMap.const _ x
    let pullPi := relativeSingularCohomologyPullback R (f.prodMap (ContinuousMap.id (Fin n → ℝ)))
      (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) n
    let pullE := relativeSingularCohomologyPullback R
      (f.prodMap (ContinuousMap.id (EuclideanSpace ℝ (Fin n))))
      (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) n
    have hn : (iso X n).hom ≫ pullE = pullPi ≫ (iso PUnit n).hom :=
      relativeSingularCohomologyProdHomeomorphIso_natural R PUnit f e he n
    have hc : (iso X n).hom c = U := Iso.inv_hom_id_apply _ _
    have hv := congrArg (fun g ↦ g c) hn
    change pullE ((iso X n).hom c) = (iso PUnit n).hom (pullPi c) at hv
    rw [hc] at hv
    have hcomp : Function.Bijective ((iso PUnit n).hom ∘ fun r : R ↦ r • pullPi c) := by
      simpa only [Function.comp_def, map_smul, hv.symm] using hU x
    exact hcomp.of_comp_left
      ((ConcreteCategory.isIso_iff_bijective (iso PUnit n).hom).mp inferInstance).injective
  have hc := relativeSingularCohomologyAction_prod_pi_bijective R X n c hpoint p
  have hb := ((ConcreteCategory.isIso_iff_bijective (iso X (p + n)).hom).mp inferInstance).comp hc
  -- The model change is its actual pair pullback and preserves both factors of the cup formula.
  have hformula (a : singularCohomology R X p) :
      (iso X (p + n)).hom
        (relativeSingularCohomologyAction R {z : X × (Fin n → ℝ) | z.2 ≠ 0} p n
          (singularCohomologyPullback R
            (⟨Prod.fst, continuous_fst⟩ : C(X × (Fin n → ℝ), X)) p a) c) =
    relativeSingularCohomologyAction R {z : X × EuclideanSpace ℝ (Fin n) | z.2 ≠ 0} p n
      (singularCohomologyPullback R
        (⟨Prod.fst, continuous_fst⟩ : C(X × EuclideanSpace ℝ (Fin n), X)) p a) U := by
    have h := relativeSingularCohomologyProdHomeomorphIso_action R X e he p n a c
    have hu : (iso X n).hom c = U := Iso.inv_hom_id_apply _ _
    change (iso X (p + n)).hom _ = relativeSingularCohomologyAction R
      {z : X × EuclideanSpace ℝ (Fin n) | z.2 ≠ 0} p n
      (singularCohomologyPullback R
        (⟨Prod.fst, continuous_fst⟩ : C(X × EuclideanSpace ℝ (Fin n), X)) p a)
      ((iso X n).hom c) at h
    rw [hu] at h
    exact h
  exact (congrArg (fun f ↦ Function.Bijective f) (funext hformula)).mp hb

end AtiyahSinger
