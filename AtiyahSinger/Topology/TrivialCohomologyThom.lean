/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EuclideanLocalHomology
public import AtiyahSinger.Topology.RelativeCohomologySequence
public import AtiyahSinger.Topology.SingularCohomologyCup

/-!
# Relative cohomology suspension with an arbitrary base parameter

Public module ID: M2261.

The original pair over `X × (ℝ × E)` is suspended using the two complementary
half axes. The base coordinate remains fixed throughout the excision and
homotopies. The short exact sequence is degreewise split before dualization,
so the coefficient ring and the base space are arbitrary.

This is the relative suspension calculation underlying the trivial-bundle
Thom theorem in Hatcher, Sections 3.1 and 4.D. Its connecting map is the actual
one of the original relative cochain sequence.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits Opposite Topology
open scoped unitInterval

universe u v

variable (R : Type) [CommRing R]
  (X : Type u) [TopologicalSpace X]
  (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open scoped Simplicial in
/-- Degree-zero singular cohomology is detected by its actual pullbacks to all points. -/
theorem singularCohomology_zero_ext (a b : singularCohomology R X 0)
    (h : ∀ x : X, singularCohomologyPullback R
      (ContinuousMap.const PUnit.{u + 1} x) 0 a =
        singularCohomologyPullback R (ContinuousMap.const PUnit.{u + 1} x) 0 b) : a = b := by
  let J (Z : Type u) [TopologicalSpace Z] :
      singularCohomology R Z 0 ⟶ (singularCochains R Z).X 0 :=
    (singularCochains R Z).isoHomologyπ₀.inv ≫ (singularCochains R Z).iCycles 0
  have hJ {Z W : Type u} [TopologicalSpace Z] [TopologicalSpace W] (f : C(Z, W)) :
      singularCohomologyPullback R f 0 ≫ J Z =
        J W ≫ ((singularCochainsFunctor R).map (TopCat.ofHom f).op).f 0 := by
    dsimp [J, singularCohomologyPullback]
    rw [CochainComplex.isoHomologyπ₀_inv_naturality_assoc, cyclesMap_i]
    simp only [Category.assoc]
  have hmono : Mono (J X) := by dsimp [J]; infer_instance
  apply (ModuleCat.mono_iff_injective (J X)).mp hmono
  apply (singularCochainEquiv R X 0).injective
  funext s
  -- Every original zero-simplex is the image of the point sitting at its only vertex.
  let τ := ((TopCat.of PUnit.{u + 1}).toSSetObjEquiv (op ⦋0⦌)).symm
    (ContinuousMap.const _ PUnit.unit)
  let x : X := ((TopCat.of X).toSSetObjEquiv (op ⦋0⦌) s)
    (Convexity.StdSimplex.single 0)
  let f := ContinuousMap.const PUnit.{u + 1} x
  let g := TopCat.toSSet.map (TopCat.ofHom f)
  have hg : g.app (op ⦋0⦌) τ = s := by
    apply ULift.ext
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    change x = s.down.hom z
    have hz : (ULift.up (Convexity.StdSimplex.single 0) :
        ULift.{u} (Convexity.StdSimplex ℝ (Fin 1))) = z := Subsingleton.elim _ _
    exact congrArg s.down.hom hz
  let F := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  have heval (c : (singularCochains R X).X 0) :
      singularCochainEquiv R PUnit.{u + 1} 0 (F.f 0 c) τ =
        singularCochainEquiv R X 0 c s := by
    change (show (singularChains R X).X 0 ⟶ singularCoefficient R from c)
      (((TopCat.toSSet.obj (TopCat.of PUnit.{u + 1})).ιChainComplex τ ≫
        (SSet.chainComplexMap g (singularCoefficient R)).f 0) (ULift.up 1)) = _
    rw [SSet.ι_chainComplexMap_f, hg]
    rfl
  have hab : F.f 0 (J X a) = F.f 0 (J X b) := by
    have ha := congrArg (fun t ↦ t a) (hJ f)
    have hb := congrArg (fun t ↦ t b) (hJ f)
    change J PUnit.{u + 1} (singularCohomologyPullback R f 0 a) = F.f 0 (J X a) at ha
    change J PUnit.{u + 1} (singularCohomologyPullback R f 0 b) = F.f 0 (J X b) at hb
    rw [← ha, ← hb, h x]
  rw [← heval, ← heval, hab]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- With a nonzero fiber vector, the punctured product pair has zero degree-zero cohomology. -/
theorem subsingleton_relativeSingularCohomology_prod_zero (e : E) (he : e ≠ 0) :
    Subsingleton (relativeSingularCohomology R {z : X × E | z.2 ≠ 0} 0) := by
  let P : Set (X × E) := {z | z.2 ≠ 0}
  let i : C(P, X × E) := ⟨Subtype.val, continuous_subtype_val⟩
  let s : C(X × E, P) := ⟨fun z ↦ ⟨(z.1, e), he⟩, by fun_prop⟩
  let H : (i.comp s).Homotopy (ContinuousMap.id (X × E)) :=
    { toFun z := (z.2.1, (1 - (z.1 : ℝ)) • e + (z.1 : ℝ) • z.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := by intro z; simp [i, s]
      map_one_left := by intro z; simp }
  have hcomp : singularCohomologyPullback R i 0 ≫
      singularCohomologyPullback R s 0 = 𝟙 _ := by
    let F := singularCohomologyFunctor R 0
    change F.map (TopCat.ofHom i).op ≫ F.map (TopCat.ofHom s).op = _
    rw [← F.map_comp, ← op_comp]
    change singularCohomologyPullback R (i.comp s) 0 = _
    rw [singularCohomologyPullback_homotopic R H]
    exact F.map_id _
  have hmono : Mono (singularCohomologyPullback R i 0) := mono_of_mono_fac hcomp
  -- At degree zero the pair injects into ambient cohomology; the next map is injective too.
  have hzero := (shortExact_singularSubspaceCochains R P).exactAt_X₁ 0 hmono
    (fun j hj ↦ by simp at hj)
  exact ModuleCat.isZero_iff_subsingleton.mp
    ((exactAt_iff_isZero_homology _ 0).mp hzero)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Suspension of the original punctured product pair, retaining every base point. -/
def relativeSingularCohomologyProdSuspensionIso (k : ℕ) :
    relativeSingularCohomology R {z : X × E | z.2 ≠ 0} k ≅
      relativeSingularCohomology R {z : X × (ℝ × E) | z.2 ≠ 0} (k + 1) := by
  let L : Set (X × (ℝ × E)) := {z | z.2 ∈ euclideanPuncturedHalfSpace E (-1)}
  let P : Set (X × (ℝ × E)) := {z | z.2 ≠ 0}
  let U : Set (X × (ℝ × E)) := {z | z.2 ∈ euclideanPuncturedHalfSpace E 1}
  have hLP : L ⊆ P := fun _ hz ↦ euclideanPuncturedHalfSpace_subset E (-1) hz
  let S := relativeSingularCochainTripleSequence R L P hLP
  have hS : S.ShortExact := shortExact_relativeSingularCochainTripleSequence R L P hLP
  -- The middle pair vanishes: the complement of the nonnegative half axis is contractible.
  have hzero (j : ℕ) : Subsingleton (relativeSingularCohomology R L j) := by
    let V := euclideanPuncturedHalfSpace E (-1)
    let : ContractibleSpace V := contractibleSpace_euclideanPuncturedHalfSpace E (-1)
      (by norm_num)
    obtain ⟨v, ⟨H⟩⟩ := id_nullhomotopic V
    let i : C(L, X × (ℝ × E)) := ⟨Subtype.val, continuous_subtype_val⟩
    let s : C(X × (ℝ × E), L) := ⟨fun z ↦ ⟨(z.1, v.val), v.property⟩, by fun_prop⟩
    have hsi : (s.comp i).Homotopic (ContinuousMap.id L) := by
      refine ⟨{ toFun z := ⟨(z.2.val.1,
                  (H.symm (z.1, ⟨z.2.val.2, z.2.property⟩)).val),
                  (H.symm (z.1, ⟨z.2.val.2, z.2.property⟩)).property⟩
                continuous_toFun := by fun_prop
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · intro z
        apply Subtype.ext
        exact congrArg (fun w : V ↦ (z.val.1, w.val)) (H.symm.map_zero_left _)
      · intro z
        apply Subtype.ext
        exact congrArg (fun w : V ↦ (z.val.1, w.val)) (H.symm.map_one_left _)
    have his : (i.comp s).Homotopic (ContinuousMap.id (X × (ℝ × E))) := by
      refine ⟨{ toFun z := (z.2.1, (1 - (z.1 : ℝ)) • v.val + (z.1 : ℝ) • z.2.2)
                continuous_toFun := by fun_prop
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · intro z
        simp [i, s]
      · intro z
        simp
    exact subsingleton_relativeSingularCohomology_of_isIso_inclusion R L
      (fun n ↦ isIso_singularCohomologyPullback_of_homotopyInverse R i s hsi his n) j
  let boundaryIso :
      relativeSingularCohomology R ((Subtype.val : P → X × (ℝ × E)) ⁻¹' L) k ≅
        relativeSingularCohomology R P (k + 1) :=
    hS.δIso k (k + 1) rfl
      (ModuleCat.isZero_iff_subsingleton.mpr (hzero k))
      (ModuleCat.isZero_iff_subsingleton.mpr (hzero (k + 1)))
  -- Excision removes the lower half axis while retaining the original punctured-pair map.
  let B : Set P := (Subtype.val : P → X × (ℝ × E)) ⁻¹' L
  let A : Set U := (Subtype.val : U → X × (ℝ × E)) ⁻¹' L
  let inc : C(U, P) := ⟨fun z ↦
    ⟨z.val, euclideanPuncturedHalfSpace_subset E 1 z.property⟩, by fun_prop⟩
  have hB : IsOpen B := ((isOpen_euclideanPuncturedHalfSpace E (-1)).preimage
    continuous_snd).preimage continuous_subtype_val
  have hinc : IsOpenEmbedding inc := by
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
  have hexc {A' : Set U} {B' : Set P}
      (hA : A' = (inc ⁻¹' Bᶜ)ᶜ) (hBB : B' = Bᶜᶜ)
      (hf : Set.MapsTo inc A' B') :
      homotopyEquivalences (ModuleCat.{max u v} R) (ComplexShape.down ℕ)
        (relativeSingularChainsMap R inc hf) := by
    subst A' B'
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R inc
      hinc Bᶜ hB.isClosed_compl hrange
  let exc := relativeSingularCohomologyPullback R inc (A := A) (B := B) (fun _ hx ↦ hx) k
  have : IsIso exc :=
    isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R _
      (hexc (A' := A) (B' := B)
        (by simp only [Set.preimage_compl, compl_compl]; rfl)
        (compl_compl B).symm (fun _ hx ↦ hx)) k
  -- Projection forgets only the first fiber coordinate; the transverse puncture is fixed.
  let Q : Set (X × E) := {z | z.2 ≠ 0}
  let f : C(U, X × E) := ⟨fun z ↦ (z.val.1, z.val.2.2), by fun_prop⟩
  let g : C(X × E, U) :=
    ⟨fun z ↦ ⟨(z.1, (1, z.2)), Or.inl (by norm_num)⟩, by fun_prop⟩
  have hf : Set.MapsTo f A Q := by
    intro z hz
    exact euclideanLocalSuspensionProjection_mapsTo E
      (x := ⟨z.val.2, z.property⟩) hz
  have hupper (z : U) (t : unitInterval) :
      ((1 - (t : ℝ)) + (t : ℝ) * z.val.2.1, z.val.2.2) ∈
        euclideanPuncturedHalfSpace E 1 := by
    rcases z.property with hz | hz
    · left
      have hz' : 0 < z.val.2.1 := by simpa using hz
      change 0 < 1 * ((1 - (t : ℝ)) + (t : ℝ) * z.val.2.1)
      have ht0 := t.property.1
      have ht1 := t.property.2
      have hmul := mul_nonneg ht0 (le_of_lt hz')
      by_cases h : (t : ℝ) = 1
      · simpa [h] using hz'
      · nlinarith
    · exact Or.inr hz
  have hgf : (g.comp f).Homotopic (ContinuousMap.id U) := by
    refine ⟨{ toFun z := ⟨(z.2.val.1,
                ((1 - (z.1 : ℝ)) + (z.1 : ℝ) * z.2.val.2.1, z.2.val.2.2)),
                hupper z.2 z.1⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      simp [g, f]
    · intro z
      apply Subtype.ext
      simp
  have hfg : (f.comp g).Homotopic (ContinuousMap.id (X × E)) := by
    have h : f.comp g = ContinuousMap.id (X × E) := rfl
    rw [h]
  let fA : C(A, Q) := ⟨fun z ↦ ⟨f z.val, hf z.property⟩,
    (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let gA : C(Q, A) := ⟨fun z ↦ ⟨g z.val, Or.inr z.property⟩, by fun_prop⟩
  have hgfA : (gA.comp fA).Homotopic (ContinuousMap.id A) := by
    refine ⟨{ toFun z := ⟨⟨(z.2.val.val.1,
                ((1 - (z.1 : ℝ)) + (z.1 : ℝ) * z.2.val.val.2.1, z.2.val.val.2.2)),
                hupper z.2.val z.1⟩, Or.inr (hf z.2.property)⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      simp [gA, fA, g, f]
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      simp
  have hfgA : (fA.comp gA).Homotopic (ContinuousMap.id Q) := by
    have h : fA.comp gA = ContinuousMap.id Q := rfl
    rw [h]
  let proj := relativeSingularCohomologyPullback R f hf k
  have : IsIso proj := isIso_relativeSingularCohomologyPullback_of_absolute R f hf
    (fun j ↦ isIso_singularCohomologyPullback_of_homotopyInverse R f g hgf hfg j)
    (fun j ↦ isIso_singularCohomologyPullback_of_homotopyInverse R fA gA hgfA hfgA j) k
  exact asIso proj ≪≫ (asIso exc).symm ≪≫ boundaryIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Suspension commutes with the actual pullback of every map of base spaces. -/
theorem relativeSingularCohomologyProdSuspensionIso_natural
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (k : ℕ) :
    (relativeSingularCohomologyProdSuspensionIso R Y E k).hom ≫
        relativeSingularCohomologyPullback R (f.prodMap (ContinuousMap.id (ℝ × E)))
          (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) (k + 1) =
      relativeSingularCohomologyPullback R (f.prodMap (ContinuousMap.id E))
          (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) k ≫
        (relativeSingularCohomologyProdSuspensionIso R X E k).hom := by
  let L (Z : Type u) : Set (Z × (ℝ × E)) :=
    {z | z.2 ∈ euclideanPuncturedHalfSpace E (-1)}
  let P (Z : Type u) : Set (Z × (ℝ × E)) := {z | z.2 ≠ 0}
  let U (Z : Type u) : Set (Z × (ℝ × E)) :=
    {z | z.2 ∈ euclideanPuncturedHalfSpace E 1}
  let B (Z : Type u) : Set (P Z) := (Subtype.val : P Z → Z × (ℝ × E)) ⁻¹' L Z
  let A (Z : Type u) : Set (U Z) := (Subtype.val : U Z → Z × (ℝ × E)) ⁻¹' L Z
  let Q (Z : Type u) : Set (Z × E) := {z | z.2 ≠ 0}
  have hLP (Z : Type u) : L Z ⊆ P Z :=
    fun _ hz ↦ euclideanPuncturedHalfSpace_subset E (-1) hz
  let inc (Z : Type u) [TopologicalSpace Z] : C(U Z, P Z) := ⟨fun z ↦
    ⟨z.val, euclideanPuncturedHalfSpace_subset E 1 z.property⟩, by fun_prop⟩
  let pr (Z : Type u) [TopologicalSpace Z] : C(U Z, Z × E) :=
    ⟨fun z ↦ (z.val.1, z.val.2.2), by fun_prop⟩
  have hpr (Z : Type u) [TopologicalSpace Z] : Set.MapsTo (pr Z) (A Z) (Q Z) := by
    intro z hz
    exact euclideanLocalSuspensionProjection_mapsTo E
      (x := ⟨z.val.2, z.property⟩) hz
  let exc (Z : Type u) [TopologicalSpace Z] :=
    relativeSingularCohomologyPullback R (inc Z) (A := A Z) (B := B Z) (fun _ hz ↦ hz) k
  let proj (Z : Type u) [TopologicalSpace Z] :=
    relativeSingularCohomologyPullback R (pr Z) (hpr Z) k
  let δ (Z : Type u) [TopologicalSpace Z] :=
    (shortExact_relativeSingularCochainTripleSequence R (L Z) (P Z) (hLP Z)).δ
      k (k + 1) rfl
  -- The two excision maps are the same open-embedding maps used in the suspension.
  have hexc (Z : Type u) [TopologicalSpace Z] : IsIso (exc Z) := by
    have hB : IsOpen (B Z) := ((isOpen_euclideanPuncturedHalfSpace E (-1)).preimage
      continuous_snd).preimage continuous_subtype_val
    have hi : IsOpenEmbedding (inc Z) := by
      apply IsOpenEmbedding.of_comp (inc Z)
        (isOpen_ne_fun continuous_snd continuous_const).isOpenEmbedding_subtypeVal
      exact ((isOpen_euclideanPuncturedHalfSpace E 1).preimage
        continuous_snd).isOpenEmbedding_subtypeVal
    have hrange : (B Z)ᶜ ⊆ Set.range (inc Z) := by
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
    have hchain {A' : Set (U Z)} {B' : Set (P Z)}
        (hA : A' = (inc Z ⁻¹' (B Z)ᶜ)ᶜ) (hBB : B' = (B Z)ᶜᶜ)
        (hf : Set.MapsTo (inc Z) A' B') :
        homotopyEquivalences (ModuleCat.{max u v} R) (ComplexShape.down ℕ)
          (relativeSingularChainsMap R (inc Z) hf) := by
      subst A' B'
      exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R (inc Z)
        hi (B Z)ᶜ hB.isClosed_compl hrange
    exact isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R _
      (hchain (A' := A Z) (B' := B Z)
        (by simp only [Set.preimage_compl, compl_compl]; rfl)
        (compl_compl (B Z)).symm (fun _ hz ↦ hz)) k
  let := hexc X
  let := hexc Y
  let fU : C(U X, U Y) := ⟨fun z ↦ ⟨(f z.val.1, z.val.2), z.property⟩, by fun_prop⟩
  let fP : C(P X, P Y) := ⟨fun z ↦ ⟨(f z.val.1, z.val.2), z.property⟩, by fun_prop⟩
  let u := relativeSingularCohomologyPullback R fU
    (A := A X) (B := A Y) (fun _ hz ↦ hz) k
  let b := relativeSingularCohomologyPullback R fP
    (A := B X) (B := B Y) (fun _ hz ↦ hz) k
  let q := relativeSingularCohomologyPullback R (f.prodMap (ContinuousMap.id E))
    (A := Q X) (B := Q Y) (fun _ hz ↦ hz) k
  let t := relativeSingularCohomologyPullback R (f.prodMap (ContinuousMap.id (ℝ × E)))
    (A := P X) (B := P Y) (fun _ hz ↦ hz) (k + 1)
  -- Projection, open inclusion, and the triple boundary all preserve the base map.
  have hproj : proj Y ≫ u = q ≫ proj X := by
    dsimp [proj, u, q]
    rw [← relativeSingularCohomologyPullback_comp, ← relativeSingularCohomologyPullback_comp]
    rfl
  have hinc : exc Y ≫ u = b ≫ exc X := by
    dsimp [exc, u, b]
    rw [← relativeSingularCohomologyPullback_comp, ← relativeSingularCohomologyPullback_comp]
    rfl
  have hδ : δ Y ≫ t = b ≫ δ X :=
    relativeSingularCohomologyTripleBoundary_natural R
      (f.prodMap (ContinuousMap.id (ℝ × E))) (hLP X) (hLP Y)
      (fun _ hz ↦ hz) (fun _ hz ↦ hz) k
  have hinv : inv (exc Y) ≫ b = u ≫ inv (exc X) := by
    have h := congrArg (fun g ↦ inv (exc Y) ≫ g ≫ inv (exc X)) hinc
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id,
      Category.comp_id] using h.symm
  change (proj Y ≫ inv (exc Y) ≫ δ Y) ≫ t = q ≫ (proj X ≫ inv (exc X) ≫ δ X)
  calc
    (proj Y ≫ inv (exc Y) ≫ δ Y) ≫ t =
        proj Y ≫ (inv (exc Y) ≫ b) ≫ δ X := by
          simp only [Category.assoc, hδ]
    _ = (proj Y ≫ u) ≫ inv (exc X) ≫ δ X := by rw [hinv]; simp only [Category.assoc]
    _ = q ≫ (proj X ≫ inv (exc X) ≫ δ X) := by rw [hproj]; simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A pointed fiber homeomorphism acts by its actual pullback on the same punctured product. -/
def relativeSingularCohomologyProdHomeomorphIso
    {V W : Type v} [TopologicalSpace V] [TopologicalSpace W] [Zero V] [Zero W]
    (e : V ≃ₜ W) (he : e 0 = 0) (k : ℕ) :
    relativeSingularCohomology R {z : X × W | z.2 ≠ 0} k ≅
      relativeSingularCohomology R {z : X × V | z.2 ≠ 0} k := by
  let eX := (Homeomorph.refl X).prodCongr e
  let f : C(X × V, X × W) := ⟨eX, eX.continuous⟩
  let g : C(X × W, X × V) := ⟨eX.symm, eX.symm.continuous⟩
  have hf : Set.MapsTo f {z | z.2 ≠ 0} {z | z.2 ≠ 0} := by
    intro z hz h
    exact hz (e.injective (h.trans he.symm))
  have hg : Set.MapsTo g {z | z.2 ≠ 0} {z | z.2 ≠ 0} := by
    intro z hz h
    apply hz
    simpa [g, eX, he] using congrArg e h
  have hgf : g.comp f = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro z
    exact eX.symm_apply_apply z
  have hfg : f.comp g = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro z
    exact eX.apply_symm_apply z
  have : IsIso (relativeSingularCohomologyPullback R f hf k) :=
    isIso_relativeSingularCohomologyPullback_of_inverse R f g hf hg hgf hfg k
  exact asIso (relativeSingularCohomologyPullback R f hf k)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Fiber-coordinate change commutes with pullback in the base. -/
theorem relativeSingularCohomologyProdHomeomorphIso_natural
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    {V W : Type v} [TopologicalSpace V] [TopologicalSpace W] [Zero V] [Zero W]
    (e : V ≃ₜ W) (he : e 0 = 0) (k : ℕ) :
    (relativeSingularCohomologyProdHomeomorphIso R Y e he k).hom ≫
        relativeSingularCohomologyPullback R (f.prodMap (ContinuousMap.id V))
          (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) k =
      relativeSingularCohomologyPullback R (f.prodMap (ContinuousMap.id W))
          (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) k ≫
        (relativeSingularCohomologyProdHomeomorphIso R X e he k).hom := by
  change relativeSingularCohomologyPullback R _ _ k ≫
      relativeSingularCohomologyPullback R _ _ k =
    relativeSingularCohomologyPullback R _ _ k ≫
      relativeSingularCohomologyPullback R _ _ k
  rw [← relativeSingularCohomologyPullback_comp, ← relativeSingularCohomologyPullback_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Iterated original suspension computes the relative cohomology of a trivial real bundle. -/
def relativeSingularCohomologyProdPiIso : (n p : ℕ) →
    singularCohomology R X p ≅
      relativeSingularCohomology R {z : X × (Fin n → ℝ) | z.2 ≠ 0} (p + n)
  | 0, p => by
    let Q : Set (X × (Fin 0 → ℝ)) := {z | z.2 ≠ 0}
    let e : X × (Fin 0 → ℝ) ≃ₜ X :=
      { toFun := Prod.fst
        invFun x := (x, 0)
        left_inv z := Prod.ext rfl (Subsingleton.elim _ _)
        right_inv _ := rfl
        continuous_toFun := continuous_fst
        continuous_invFun := by fun_prop }
    have hQ : Q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hz (Subsingleton.elim _ _)
    have : IsIso (relativeSingularCohomologyToOrdinary R Q p) := by
      rw [hQ]
      exact isIso_relativeSingularCohomologyToOrdinary_empty R _ p
    -- The zero-dimensional fiber is the actual point, with the empty relative subspace.
    exact (singularCohomologyFunctor R p).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of (X × (Fin 0 → ℝ))) e).op ≪≫
        (asIso (relativeSingularCohomologyToOrdinary R Q p)).symm
  | n + 1, p => by
    let e₀ : (Fin (n + 1) → ℝ) ≃ₜ ℝ × (Fin n → ℝ) :=
      Homeomorph.ulift.symm.trans ((euclideanLocalCoordinateSplit.{0} n).trans
        ((Homeomorph.refl ℝ).prodCongr Homeomorph.ulift))
    -- Split one fiber coordinate, then use the same connecting map as in the one-step case.
    exact relativeSingularCohomologyProdPiIso n p ≪≫
      relativeSingularCohomologyProdSuspensionIso R X (Fin n → ℝ) (p + n) ≪≫
        relativeSingularCohomologyProdHomeomorphIso R X e₀ rfl ((p + n) + 1)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Iterated suspension retains the original pullbacks on the arbitrary base parameter. -/
theorem relativeSingularCohomologyProdPiIso_natural
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (n p : ℕ) :
    (relativeSingularCohomologyProdPiIso R Y n p).hom ≫
        relativeSingularCohomologyPullback R (f.prodMap (ContinuousMap.id (Fin n → ℝ)))
          (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) (p + n) =
      singularCohomologyPullback R f p ≫ (relativeSingularCohomologyProdPiIso R X n p).hom := by
  induction n with
  | zero =>
    let Q (Z : Type u) : Set (Z × (Fin 0 → ℝ)) := {z | z.2 ≠ 0}
    have hQ (Z : Type u) : Q Z = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hz (Subsingleton.elim _ _)
    have hIso (Z : Type u) [TopologicalSpace Z] :
        IsIso (relativeSingularCohomologyToOrdinary R (Q Z) p) := by
      rw [hQ]
      exact isIso_relativeSingularCohomologyToOrdinary_empty R _ p
    let := hIso X
    let := hIso Y
    let pr (Z : Type u) [TopologicalSpace Z] : C(Z × (Fin 0 → ℝ), Z) :=
      ⟨Prod.fst, continuous_fst⟩
    let g := f.prodMap (ContinuousMap.id (Fin 0 → ℝ))
    have hf := relativeSingularCohomologyPullback_toOrdinary R g
      (A := Q X) (B := Q Y) (fun _ hz ↦ hz) p
    have hbase : singularCohomologyPullback R (pr Y) p ≫
        singularCohomologyPullback R g p =
      singularCohomologyPullback R f p ≫ singularCohomologyPullback R (pr X) p := by
      simp only [singularCohomologyPullback, ← Functor.map_comp, ← op_comp]
      rfl
    -- The rank-zero comparison is the genuine empty-pair comparison and product projection.
    change (singularCohomologyPullback R (pr Y) p ≫
        inv (relativeSingularCohomologyToOrdinary R (Q Y) p)) ≫
          relativeSingularCohomologyPullback R g (fun _ hz ↦ hz) p =
      singularCohomologyPullback R f p ≫ (singularCohomologyPullback R (pr X) p ≫
        inv (relativeSingularCohomologyToOrdinary R (Q X) p))
    apply (cancel_mono (relativeSingularCohomologyToOrdinary R (Q X) p)).mp
    simp only [Category.assoc, hf, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id,
      Category.comp_id]
    exact hbase
  | succ n ih =>
    let e₀ : (Fin (n + 1) → ℝ) ≃ₜ ℝ × (Fin n → ℝ) :=
      Homeomorph.ulift.symm.trans ((euclideanLocalCoordinateSplit.{0} n).trans
        ((Homeomorph.refl ℝ).prodCongr Homeomorph.ulift))
    have he₀ : e₀ 0 = 0 := rfl
    have hcoord := relativeSingularCohomologyProdHomeomorphIso_natural R X f e₀ he₀
      (p + n + 1)
    have hsusp := relativeSingularCohomologyProdSuspensionIso_natural R X
      (Fin n → ℝ) f (p + n)
    -- Naturality composes in the same order as the original coordinatewise suspension.
    exact (CommSq.horiz_comp ⟨ih⟩ (CommSq.horiz_comp ⟨hsusp⟩ ⟨hcoord⟩)).w

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Relative cohomology of a trivial rank-n real bundle vanishes below the fiber dimension. -/
theorem subsingleton_relativeSingularCohomology_prod_pi_below_dim (n k : ℕ) (hk : k < n) :
    Subsingleton (relativeSingularCohomology R {z : X × (Fin n → ℝ) | z.2 ≠ 0} k) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      let e : Fin (n + 1) → ℝ := fun _ ↦ 1
      have he : e ≠ 0 := by
        intro h
        have h₀ := congrFun h 0
        norm_num [e] at h₀
      exact subsingleton_relativeSingularCohomology_prod_zero R X _ e he
    | succ k =>
      have := ih k (by omega)
      let e₀ : (Fin (n + 1) → ℝ) ≃ₜ ℝ × (Fin n → ℝ) :=
        Homeomorph.ulift.symm.trans ((euclideanLocalCoordinateSplit.{0} n).trans
          ((Homeomorph.refl ℝ).prodCongr Homeomorph.ulift))
      let iso := relativeSingularCohomologyProdSuspensionIso R X (Fin n → ℝ) k ≪≫
        relativeSingularCohomologyProdHomeomorphIso R X e₀ rfl (k + 1)
      exact ((ConcreteCategory.isIso_iff_bijective iso.hom).mp
        inferInstance).surjective.subsingleton

/-- The same suspension calculation in the Euclidean model used by real vector bundles. -/
def relativeSingularCohomologyProdEuclideanIso (n p : ℕ) :
    singularCohomology R X p ≅
      relativeSingularCohomology R {z : X × EuclideanSpace ℝ (Fin n) | z.2 ≠ 0} (p + n) :=
  relativeSingularCohomologyProdPiIso R X n p ≪≫
    relativeSingularCohomologyProdHomeomorphIso R X
      (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
      (EuclideanSpace.equiv (Fin n) ℝ).map_zero (p + n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The Euclidean calculation is natural for the original maps of base spaces. -/
theorem relativeSingularCohomologyProdEuclideanIso_natural
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) (n p : ℕ) :
    (relativeSingularCohomologyProdEuclideanIso R Y n p).hom ≫
        relativeSingularCohomologyPullback R
          (f.prodMap (ContinuousMap.id (EuclideanSpace ℝ (Fin n))))
          (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) (p + n) =
      singularCohomologyPullback R f p ≫
        (relativeSingularCohomologyProdEuclideanIso R X n p).hom := by
  exact (CommSq.horiz_comp
    ⟨relativeSingularCohomologyProdPiIso_natural R X f n p⟩
    ⟨relativeSingularCohomologyProdHomeomorphIso_natural R X f
      (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
      (EuclideanSpace.equiv (Fin n) ℝ).map_zero (p + n)⟩).w

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A top-degree class of the trivial Euclidean pair is determined by all fiber restrictions. -/
theorem relativeSingularCohomology_prod_euclidean_ext (n : ℕ)
    (a b : relativeSingularCohomology R
      {z : X × EuclideanSpace ℝ (Fin n) | z.2 ≠ 0} n)
    (h : ∀ x : X, relativeSingularCohomologyPullback R
      ((ContinuousMap.const PUnit.{u + 1} x).prodMap
        (ContinuousMap.id (EuclideanSpace ℝ (Fin n))))
      (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) n a =
        relativeSingularCohomologyPullback R
          ((ContinuousMap.const PUnit.{u + 1} x).prodMap
            (ContinuousMap.id (EuclideanSpace ℝ (Fin n))))
          (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) n b) : a = b := by
  let V := EuclideanSpace ℝ (Fin n)
  let Q (Z : Type u) : Set (Z × V) := {z | z.2 ≠ 0}
  -- Work at the literal degree 0+n of the suspension, and only then transport the degree.
  have hcore (k : ℕ) (hk : 0 + n = k) (a b : relativeSingularCohomology R (Q X) k)
      (h : ∀ x : X, relativeSingularCohomologyPullback R
        ((ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id V))
        (A := Q PUnit.{u + 1}) (B := Q X) (fun _ hz ↦ hz) k a =
          relativeSingularCohomologyPullback R
            ((ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id V))
            (A := Q PUnit.{u + 1}) (B := Q X) (fun _ hz ↦ hz) k b) : a = b := by
    subst k
    let iso (Z : Type u) [TopologicalSpace Z] :=
      relativeSingularCohomologyProdEuclideanIso R Z n 0
    apply ((ConcreteCategory.isIso_iff_bijective (iso X).inv).mp inferInstance).injective
    apply singularCohomology_zero_ext R X
    intro x
    let f : C(PUnit.{u + 1}, X) := ContinuousMap.const _ x
    let g := f.prodMap (ContinuousMap.id V)
    let pull := relativeSingularCohomologyPullback R g
      (A := Q PUnit.{u + 1}) (B := Q X) (fun _ hz ↦ hz) (0 + n)
    have hab : pull a = pull b := h x
    have hnat : (iso X).hom ≫ pull = singularCohomologyPullback R f 0 ≫ (iso PUnit).hom :=
      relativeSingularCohomologyProdEuclideanIso_natural R PUnit f n 0
    apply ((ConcreteCategory.isIso_iff_bijective (iso PUnit).hom).mp inferInstance).injective
    have ha := congrArg (fun t ↦ t ((iso X).inv a)) hnat
    have hb := congrArg (fun t ↦ t ((iso X).inv b)) hnat
    have hia : (iso X).hom ((iso X).inv a) = a :=
      congrArg (fun t ↦ t a) (iso X).inv_hom_id
    have hib : (iso X).hom ((iso X).inv b) = b :=
      congrArg (fun t ↦ t b) (iso X).inv_hom_id
    simp only [ModuleCat.comp_apply, hia, hib] at ha hb
    exact ha.symm.trans (hab.trans hb)
  exact hcore n (Nat.zero_add n) a b h

/-- The original Euclidean product pair has no cohomology below its fiber dimension. -/
theorem subsingleton_relativeSingularCohomology_prod_euclidean_below_dim
    (n k : ℕ) (hk : k < n) :
    Subsingleton (relativeSingularCohomology R
      {z : X × EuclideanSpace ℝ (Fin n) | z.2 ≠ 0} k) := by
  let := subsingleton_relativeSingularCohomology_prod_pi_below_dim R X n k hk
  let iso := relativeSingularCohomologyProdHomeomorphIso R X
    (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
    (EuclideanSpace.equiv (Fin n) ℝ).map_zero k
  exact ((ConcreteCategory.isIso_iff_bijective iso.hom).mp inferInstance).surjective.subsingleton

end AtiyahSinger
