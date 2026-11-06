/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EuclideanLocalHomology
public import AtiyahSinger.Topology.LocalHomologyChart
public import AtiyahSinger.Topology.LocalOrientationTransport
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local homology of a product with a real coordinate

Public module ID: M1941.

The suspension isomorphism is constructed from the actual relative triple,
open excision, and transverse projection. The transverse space is arbitrary:
the lower half-axis complement retracts onto a copy of that same space, so
its inclusion into the ambient product is a homotopy equivalence. In particular,
this construction applies to open chart sources without extending a local
homeomorphism to the whole Euclidean space or assuming differentiability.

Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, the local suspension
calculation. The explicit naturality retains the maps needed to compare local
product orientations in topological vector-bundle charts.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Topology
open scoped unitInterval

universe u

variable (R : Type) [CommRing R]
variable {X : Type u} [TopologicalSpace X] [T2Space X] (x : X)

/-- The complement of the locus with s*t ≤ 0 and transverse coordinate x.
For s = 0 this removes the whole axis through x. -/
def localHomologyHalfAxisComplement (s : ℝ) : Set (ℝ × X) :=
  {z | 0 < s * z.1 ∨ z.2 ≠ x}

/-- Each half-axis complement is open in the original product topology. -/
theorem isOpen_localHomologyHalfAxisComplement (s : ℝ) :
    IsOpen (localHomologyHalfAxisComplement x s) :=
  (isOpen_lt continuous_const (continuous_const.mul continuous_fst)).union
    (isOpen_ne_fun continuous_snd continuous_const)

omit [TopologicalSpace X] [T2Space X] in
/-- The half-axis complement avoids the distinguished product point. -/
theorem localHomologyHalfAxisComplement_subset (s : ℝ) :
    localHomologyHalfAxisComplement x s ⊆ ({(0, x)}ᶜ : Set (ℝ × X)) := by
  intro z hz hzero
  change z = (0, x) at hzero
  rcases hz with hpos | hne
  · simp [hzero] at hpos
  · exact hne (congrArg Prod.snd hzero)

/-- The lower half-axis complement and punctured product form the actual relative triple. -/
def localHomologySuspensionTriple : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  relativeSingularTripleSequence R (localHomologyHalfAxisComplement x (-1))
    ({(0, x)}ᶜ : Set (ℝ × X)) (localHomologyHalfAxisComplement_subset x (-1))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The triple boundary is invertible without any contractibility assumption on the base. -/
def localHomologySuspensionBoundaryIso (k : ℕ) :
    relativeSingularHomology R ({(0, x)}ᶜ : Set (ℝ × X)) (k + 1) ≅
      relativeSingularHomology R
        ((Subtype.val : ({(0, x)}ᶜ : Set (ℝ × X)) → ℝ × X) ⁻¹'
          localHomologyHalfAxisComplement x (-1)) k := by
  let L := localHomologyHalfAxisComplement x (-1)
  let i : C(L, ℝ × X) := ⟨Subtype.val, continuous_subtype_val⟩
  let g : C(ℝ × X, L) := ⟨fun z ↦ ⟨(-1, z.2), Or.inl (by norm_num)⟩, by fun_prop⟩
  -- Move only the real coordinate. Non-distinguished transverse points stay in L,
  -- and negative real coordinates remain negative throughout this straight homotopy.
  have hsegment (t : unitInterval) (z : L) :
      ((1 - (t : ℝ)) * (-1) + (t : ℝ) * z.val.1, z.val.2) ∈ L := by
    rcases z.property with hz | hz
    · left
      change 0 < (-1 : ℝ) * ((1 - (t : ℝ)) * (-1) + (t : ℝ) * z.val.1)
      have hz' : z.val.1 < 0 := by linarith
      have ht0 := t.property.1
      have ht1 := t.property.2
      by_cases h : (t : ℝ) = 0
      · simp [h]
      · have ht : 0 < (t : ℝ) := lt_of_le_of_ne ht0 (Ne.symm h)
        have hmul := mul_neg_of_pos_of_neg ht hz'
        nlinarith
    · exact Or.inr hz
  have hLi : (g.comp i).Homotopic (ContinuousMap.id L) := by
    refine ⟨{ toFun p := ⟨((1 - (p.1 : ℝ)) * (-1) + (p.1 : ℝ) * p.2.val.1,
                p.2.val.2), hsegment p.1 p.2⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      simp [g, i]
    · intro z
      apply Subtype.ext
      simp
  have hiL : (i.comp g).Homotopic (ContinuousMap.id (ℝ × X)) := by
    refine ⟨{ toFun p := ((1 - (p.1 : ℝ)) * (-1) + (p.1 : ℝ) * p.2.1, p.2.2)
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      simp [g, i]
    · intro z
      simp
  have hquasi : QuasiIso (singularSubspaceChains R L) := by
    rw [quasiIso_iff]
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_singularHomologyMap_of_homotopyInverse R i g hLi hiL j
  have hacyclic := (shortExact_singularSubspaceChains R L).acyclic_X₃ hquasi
  have hzero (j : ℕ) : IsZero ((localHomologySuspensionTriple R x).X₂.homology j) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ j).mp (hacyclic j)
  exact (shortExact_relativeSingularTripleSequence R _ _ _).δIso (k + 1) k rfl
    (hzero (k + 1)) (hzero k)

/-- The original inclusion of the upper half-axis complement into the punctured product. -/
def localHomologySuspensionInclusion :
    C(localHomologyHalfAxisComplement x 1, ({(0, x)}ᶜ : Set (ℝ × X))) :=
  ⟨fun z ↦ ⟨z.val, localHomologyHalfAxisComplement_subset x 1 z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Open excision on the two original half-axis complements gives this specified map. -/
theorem isIso_localHomologySuspensionExcision (k : ℕ) :
    IsIso (relativeSingularHomologyMap R (localHomologySuspensionInclusion x)
      (A := (Subtype.val : localHomologyHalfAxisComplement x 1 → ℝ × X) ⁻¹'
        localHomologyHalfAxisComplement x (-1))
      (B := (Subtype.val : ({(0, x)}ᶜ : Set (ℝ × X)) → ℝ × X) ⁻¹'
        localHomologyHalfAxisComplement x (-1)) (fun _ hz ↦ hz) k) := by
  let P := ({(0, x)}ᶜ : Set (ℝ × X))
  let B : Set P := (Subtype.val : P → ℝ × X) ⁻¹'
    localHomologyHalfAxisComplement x (-1)
  let f := localHomologySuspensionInclusion x
  have hf : IsOpenEmbedding f := by
    apply IsOpenEmbedding.of_comp f
      (isClosed_singleton.isOpen_compl.isOpenEmbedding_subtypeVal)
    exact isOpen_localHomologyHalfAxisComplement x 1 |>.isOpenEmbedding_subtypeVal
  have hB : IsOpen B := (isOpen_localHomologyHalfAxisComplement x (-1)).preimage
    continuous_subtype_val
  have hrange : Bᶜ ⊆ Set.range f := by
    intro z hz
    have hy : z.val.2 = x := by
      by_contra h
      exact hz (Or.inr h)
    have ht : z.val.1 ≠ 0 := fun h ↦ z.property (Prod.ext h hy)
    have hpos : 0 < z.val.1 := by
      by_contra h
      have hneg : z.val.1 < 0 := lt_of_le_of_ne (le_of_not_gt h) ht
      apply hz
      left
      linarith
    exact ⟨⟨z.val, Or.inl (by simpa using hpos)⟩, rfl⟩
  have hexc {A' : Set (localHomologyHalfAxisComplement x 1)} {B' : Set P}
      (hA : A' = (f ⁻¹' Bᶜ)ᶜ) (hBB : B' = Bᶜᶜ) (hf' : Set.MapsTo f A' B') :
      homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
        (relativeSingularChainsMap R f hf') := by
    subst A' B'
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R f hf Bᶜ
      hB.isClosed_compl hrange
  obtain ⟨e, he⟩ := hexc
    (A' := (Subtype.val : localHomologyHalfAxisComplement x 1 → ℝ × X) ⁻¹'
      localHomologyHalfAxisComplement x (-1)) (B' := B)
    (by simp only [Set.preimage_compl, compl_compl]; rfl) (compl_compl B).symm
    (fun _ hz ↦ hz)
  change IsIso (homologyMap _ k)
  rw [← he]
  change IsIso (e.toHomologyIso k).hom
  infer_instance

/-- Projection from the upper half-axis complement to the original transverse space. -/
def localHomologySuspensionProjection : C(localHomologyHalfAxisComplement x 1, X) :=
  ⟨fun z ↦ z.val.2, continuous_snd.comp continuous_subtype_val⟩

omit [T2Space X] in
/-- The common part of the half-axis complements projects away from the specified point. -/
theorem localHomologySuspensionProjection_mapsTo :
    Set.MapsTo (localHomologySuspensionProjection x)
      ((Subtype.val : localHomologyHalfAxisComplement x 1 → ℝ × X) ⁻¹'
        localHomologyHalfAxisComplement x (-1)) ({x}ᶜ : Set X) := by
  intro z hz hzero
  change z.val.2 = x at hzero
  have hpos : 0 < z.val.1 := by
    simpa [localHomologyHalfAxisComplement, hzero] using z.property
  have hneg : z.val.1 < 0 := by
    change 0 < (-1 : ℝ) * z.val.1 ∨ z.val.2 ≠ x at hz
    simpa [hzero] using hz
  exact lt_asymm hpos hneg

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
omit [T2Space X] in
/-- The transverse projection induces the original pair homology isomorphism. -/
theorem isIso_localHomologySuspensionProjection (k : ℕ) :
    IsIso (relativeSingularHomologyMap R (localHomologySuspensionProjection x)
      (localHomologySuspensionProjection_mapsTo x) k) := by
  let U := localHomologyHalfAxisComplement x 1
  let A : Set U := (Subtype.val : U → ℝ × X) ⁻¹' localHomologyHalfAxisComplement x (-1)
  let f := localHomologySuspensionProjection x
  let g : C(X, U) := ⟨fun y ↦ ⟨(1, y), Or.inl (by norm_num)⟩, by fun_prop⟩
  have hupper (z : U) (t : unitInterval) :
      ((1 - (t : ℝ)) + (t : ℝ) * z.val.1, z.val.2) ∈ U := by
    rcases z.property with hz | hz
    · left
      have hz' : 0 < z.val.1 := by simpa using hz
      change 0 < 1 * ((1 - (t : ℝ)) + (t : ℝ) * z.val.1)
      have ht0 := t.property.1
      have ht1 := t.property.2
      have hmul := mul_nonneg ht0 (le_of_lt hz')
      by_cases h : (t : ℝ) = 1
      · simpa [h] using hz'
      · nlinarith
    · exact Or.inr hz
  -- Contract only the real coordinate, also on the punctured transverse subspace.
  have hgf : (g.comp f).Homotopic (ContinuousMap.id U) := by
    refine ⟨{ toFun p := ⟨((1 - (p.1 : ℝ)) + (p.1 : ℝ) * p.2.val.1, p.2.val.2),
                hupper p.2 p.1⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      simp [g, f, localHomologySuspensionProjection]
    · intro z
      apply Subtype.ext
      change ((1 - (1 : ℝ)) + (1 : ℝ) * z.val.1, z.val.2) = z.val
      simp
  have hfg : (f.comp g).Homotopic (ContinuousMap.id X) := by
    have h : f.comp g = ContinuousMap.id X := rfl
    rw [h]
  let fA : C(A, ({x}ᶜ : Set X)) :=
    ⟨fun z ↦ ⟨f z.val, localHomologySuspensionProjection_mapsTo x z.property⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let gA : C(({x}ᶜ : Set X), A) := ⟨fun y ↦ ⟨g y.val, Or.inr y.property⟩, by fun_prop⟩
  have hgfA : (gA.comp fA).Homotopic (ContinuousMap.id A) := by
    refine ⟨{ toFun p := ⟨⟨((1 - (p.1 : ℝ)) + (p.1 : ℝ) * p.2.val.val.1,
                p.2.val.val.2), hupper p.2.val p.1⟩,
                Or.inr (localHomologySuspensionProjection_mapsTo x p.2.property)⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      simp [gA, fA, g, f, localHomologySuspensionProjection]
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      simp
  have hfgA : (fA.comp gA).Homotopic (ContinuousMap.id ({x}ᶜ : Set X)) := by
    have h : fA.comp gA = ContinuousMap.id ({x}ᶜ : Set X) := rfl
    rw [h]
  exact isIso_relativeSingularHomologyMap_of_absolute R f
    (localHomologySuspensionProjection_mapsTo x)
    (fun j ↦ isIso_singularHomologyMap_of_homotopyInverse R f g hgf hfg j)
    (fun j ↦ isIso_singularHomologyMap_of_homotopyInverse R fA gA hgfA hfgA j) k

/-- The local homology suspension through the triple boundary, excision and projection. -/
def localHomologySuspensionIso (k : ℕ) :
    relativeSingularHomology R ({(0, x)}ᶜ : Set (ℝ × X)) (k + 1) ≅
      relativeSingularHomology R ({x}ᶜ : Set X) k := by
  let j := relativeSingularHomologyMap R (localHomologySuspensionInclusion x)
    (A := (Subtype.val : localHomologyHalfAxisComplement x 1 → ℝ × X) ⁻¹'
      localHomologyHalfAxisComplement x (-1))
    (B := (Subtype.val : ({(0, x)}ᶜ : Set (ℝ × X)) → ℝ × X) ⁻¹'
      localHomologyHalfAxisComplement x (-1)) (fun _ hz ↦ hz) k
  let p := relativeSingularHomologyMap R (localHomologySuspensionProjection x)
    (localHomologySuspensionProjection_mapsTo x) k
  let : IsIso j := isIso_localHomologySuspensionExcision R x k
  let : IsIso p := isIso_localHomologySuspensionProjection R x k
  exact localHomologySuspensionBoundaryIso R x k ≪≫ (asIso j).symm ≪≫ asIso p

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Local suspension commutes with any actual map of punctured pairs.
In particular it commutes with inclusions of open chart sources and their homeomorphisms. -/
theorem localHomologySuspensionIso_naturality
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] (f : C(X, Y)) (y : Y)
    (hf : Set.MapsTo f ({x}ᶜ : Set X) ({y}ᶜ : Set Y)) (k : ℕ) :
    relativeSingularHomologyMap R
        (⟨fun z : ℝ × X ↦ (z.1, f z.2), by fun_prop⟩ : C(ℝ × X, ℝ × Y))
        (A := ({(0, x)}ᶜ : Set (ℝ × X)))
        (B := ({(0, y)}ᶜ : Set (ℝ × Y)))
        (by
          intro z hz heq
          apply hz
          apply Prod.ext
          · exact congrArg (fun p : ℝ × Y ↦ p.1) heq
          · by_contra h
            exact hf h (congrArg Prod.snd heq)) (k + 1) ≫
      (localHomologySuspensionIso R y k).hom =
        (localHomologySuspensionIso R x k).hom ≫ relativeSingularHomologyMap R f hf k := by
  let g : C(ℝ × X, ℝ × Y) := ⟨fun z ↦ (z.1, f z.2), by fun_prop⟩
  have hgL (s : ℝ) : Set.MapsTo g (localHomologyHalfAxisComplement x s)
      (localHomologyHalfAxisComplement y s) := by
    intro z hz
    exact hz.elim Or.inl (fun h ↦ Or.inr (hf h))
  have hgP : Set.MapsTo g ({(0, x)}ᶜ : Set (ℝ × X))
      ({(0, y)}ᶜ : Set (ℝ × Y)) := by
    intro z hz heq
    apply hz
    apply Prod.ext
    · exact congrArg (fun p : ℝ × Y ↦ p.1) heq
    · by_contra h
      exact hf h (congrArg Prod.snd heq)
  let gP : C(({(0, x)}ᶜ : Set (ℝ × X)), ({(0, y)}ᶜ : Set (ℝ × Y))) :=
    ⟨fun z ↦ ⟨g z.val, hgP z.property⟩,
      (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let gU : C(localHomologyHalfAxisComplement x 1,
      localHomologyHalfAxisComplement y 1) :=
    ⟨fun z ↦ ⟨g z.val, hgL 1 z.property⟩,
      (g.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let S := localHomologySuspensionTriple R x
  let T := localHomologySuspensionTriple R y
  -- Naturality of the boundary is obtained on the same triple of chain quotients.
  let φ : S ⟶ T :=
    { τ₁ := relativeSingularChainsMap R gP (fun _ hz ↦ hgL (-1) hz)
      τ₂ := relativeSingularChainsMap R g (hgL (-1))
      τ₃ := relativeSingularChainsMap R g hgP
      comm₁₂ := by
        dsimp [S, T, localHomologySuspensionTriple, relativeSingularTripleSequence]
        rw [← relativeSingularChainsMap_comp, ← relativeSingularChainsMap_comp]
        rfl
      comm₂₃ := by
        dsimp [S, T, localHomologySuspensionTriple, relativeSingularTripleSequence]
        rw [← relativeSingularChainsMap_comp, ← relativeSingularChainsMap_comp]
        rfl }
  let D := localHomologySuspensionBoundaryIso R x k
  let D' := localHomologySuspensionBoundaryIso R y k
  let F := relativeSingularHomologyMap R g hgP (k + 1)
  let P := homologyMap φ.τ₁ k
  let U := relativeSingularHomologyMap R gU
    (A := (Subtype.val : localHomologyHalfAxisComplement x 1 → ℝ × X) ⁻¹'
      localHomologyHalfAxisComplement x (-1))
    (B := (Subtype.val : localHomologyHalfAxisComplement y 1 → ℝ × Y) ⁻¹'
      localHomologyHalfAxisComplement y (-1)) (fun _ hz ↦ hgL (-1) hz) k
  let J := relativeSingularHomologyMap R (localHomologySuspensionInclusion x)
    (A := (Subtype.val : localHomologyHalfAxisComplement x 1 → ℝ × X) ⁻¹'
      localHomologyHalfAxisComplement x (-1))
    (B := (Subtype.val : ({(0, x)}ᶜ : Set (ℝ × X)) → ℝ × X) ⁻¹'
      localHomologyHalfAxisComplement x (-1)) (fun _ hz ↦ hz) k
  let J' := relativeSingularHomologyMap R (localHomologySuspensionInclusion y)
    (A := (Subtype.val : localHomologyHalfAxisComplement y 1 → ℝ × Y) ⁻¹'
      localHomologyHalfAxisComplement y (-1))
    (B := (Subtype.val : ({(0, y)}ᶜ : Set (ℝ × Y)) → ℝ × Y) ⁻¹'
      localHomologyHalfAxisComplement y (-1)) (fun _ hz ↦ hz) k
  let p := relativeSingularHomologyMap R (localHomologySuspensionProjection x)
    (localHomologySuspensionProjection_mapsTo x) k
  let p' := relativeSingularHomologyMap R (localHomologySuspensionProjection y)
    (localHomologySuspensionProjection_mapsTo y) k
  let : IsIso J := isIso_localHomologySuspensionExcision R x k
  let : IsIso J' := isIso_localHomologySuspensionExcision R y k
  have hδ : F ≫ D'.hom = D.hom ≫ P :=
    (HomologySequence.δ_naturality φ
      (shortExact_relativeSingularTripleSequence R _ _ _)
      (shortExact_relativeSingularTripleSequence R _ _ _) (k + 1) k rfl).symm
  -- The excision and projection squares already commute as actual continuous pair maps.
  have hJ : J ≫ P = U ≫ J' := by
    change homologyMap _ k ≫ homologyMap _ k = homologyMap _ k ≫ homologyMap _ k
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
      ← homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have hp : U ≫ p' = p ≫ relativeSingularHomologyMap R f hf k := by
    change homologyMap _ k ≫ homologyMap _ k = homologyMap _ k ≫ homologyMap _ k
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
      ← homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have hJinv : P ≫ inv J' = inv J ≫ U := by
    apply (cancel_epi J).mp
    rw [← Category.assoc, hJ]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  change F ≫ (D'.hom ≫ inv J' ≫ p') =
    (D.hom ≫ inv J ≫ p) ≫ relativeSingularHomologyMap R f hf k
  rw [← Category.assoc F, hδ]
  simp only [Category.assoc]
  rw [← Category.assoc P, hJinv]
  simp only [Category.assoc]
  rw [hp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A scalar comparison of local maps is unchanged after adjoining a real coordinate.
This compares the actual maps and therefore does not choose a suspension generator. -/
theorem relativeSingularHomologyMap_realProd_smul
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] (f g : C(X, Y)) (y : Y)
    (hf : Set.MapsTo f ({x}ᶜ : Set X) ({y}ᶜ : Set Y))
    (hg : Set.MapsTo g ({x}ᶜ : Set X) ({y}ᶜ : Set Y)) (k : ℕ) (s : R)
    (h : relativeSingularHomologyMap R f hf k = s • relativeSingularHomologyMap R g hg k) :
    relativeSingularHomologyMap R
        (⟨fun z : ℝ × X ↦ (z.1, f z.2), by fun_prop⟩ : C(ℝ × X, ℝ × Y))
        (A := ({(0, x)}ᶜ : Set (ℝ × X))) (B := ({(0, y)}ᶜ : Set (ℝ × Y)))
        (by
          intro z hz heq
          apply hz
          apply Prod.ext
          · exact congrArg (fun p : ℝ × Y ↦ p.1) heq
          · by_contra hne
            exact hf hne (congrArg Prod.snd heq)) (k + 1) =
      s • relativeSingularHomologyMap R
        (⟨fun z : ℝ × X ↦ (z.1, g z.2), by fun_prop⟩ : C(ℝ × X, ℝ × Y))
        (A := ({(0, x)}ᶜ : Set (ℝ × X))) (B := ({(0, y)}ᶜ : Set (ℝ × Y)))
        (by
          intro z hz heq
          apply hz
          apply Prod.ext
          · exact congrArg (fun p : ℝ × Y ↦ p.1) heq
          · by_contra hne
            exact hg hne (congrArg Prod.snd heq)) (k + 1) := by
  -- Both maps commute with the same invertible suspension on the target.
  apply (cancel_mono (localHomologySuspensionIso R y k).hom).mp
  rw [Linear.smul_comp, localHomologySuspensionIso_naturality R x f y hf k,
    localHomologySuspensionIso_naturality R x g y hg k, h, Linear.comp_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Adjoining any finite ordered list of real coordinates preserves a scalar comparison
of the original local homology maps. The comparison includes fiber rank zero. -/
theorem relativeSingularHomologyMap_finProd_smul
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] (f g : C(X, Y)) (y : Y)
    (hf : Set.MapsTo f ({x}ᶜ : Set X) ({y}ᶜ : Set Y))
    (hg : Set.MapsTo g ({x}ᶜ : Set X) ({y}ᶜ : Set Y)) (k r : ℕ) (s : R)
    (h : relativeSingularHomologyMap R f hf k = s • relativeSingularHomologyMap R g hg k) :
    relativeSingularHomologyMap R
        (⟨fun z : (Fin r → ℝ) × X ↦ (z.1, f z.2), by fun_prop⟩ :
          C((Fin r → ℝ) × X, (Fin r → ℝ) × Y))
        (A := ({(0, x)}ᶜ : Set ((Fin r → ℝ) × X)))
        (B := ({(0, y)}ᶜ : Set ((Fin r → ℝ) × Y)))
        (by
          intro z hz heq
          apply hz
          apply Prod.ext
          · exact congrArg (fun p : (Fin r → ℝ) × Y ↦ p.1) heq
          · by_contra hne
            exact hf hne (congrArg Prod.snd heq)) (k + r) =
      s • relativeSingularHomologyMap R
        (⟨fun z : (Fin r → ℝ) × X ↦ (z.1, g z.2), by fun_prop⟩ :
          C((Fin r → ℝ) × X, (Fin r → ℝ) × Y))
        (A := ({(0, x)}ᶜ : Set ((Fin r → ℝ) × X)))
        (B := ({(0, y)}ᶜ : Set ((Fin r → ℝ) × Y)))
        (by
          intro z hz heq
          apply hz
          apply Prod.ext
          · exact congrArg (fun p : (Fin r → ℝ) × Y ↦ p.1) heq
          · by_contra hne
            exact hg hne (congrArg Prod.snd heq)) (k + r) := by
  have hiso {A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
      (e : A ≃ₜ B) (a : A) (b : B) (heb : e a = b)
      (he : Set.MapsTo e ({a}ᶜ : Set A) ({b}ᶜ : Set B)) (m : ℕ) :
      IsIso (relativeSingularHomologyMap R (⟨e, e.continuous⟩ : C(A, B)) he m) := by
    have hei : Set.MapsTo e.symm ({b}ᶜ : Set B) ({a}ᶜ : Set A) := by
      intro z hz heq
      apply hz
      calc
        z = e (e.symm z) := (e.apply_symm_apply z).symm
        _ = b := by rw [show e.symm z = a from heq, heb]
    exact isIso_relativeSingularHomologyMap_of_inverse R
      (⟨e, e.continuous⟩ : C(A, B)) (⟨e.symm, e.symm.continuous⟩ : C(B, A)) he hei
      (by apply ContinuousMap.ext; intro z; exact e.symm_apply_apply z)
      (by apply ContinuousMap.ext; intro z; exact e.apply_symm_apply z) m
  let F (r : ℕ) : C((Fin r → ℝ) × X, (Fin r → ℝ) × Y) :=
    ⟨fun z ↦ (z.1, f z.2), by fun_prop⟩
  let G (r : ℕ) : C((Fin r → ℝ) × X, (Fin r → ℝ) × Y) :=
    ⟨fun z ↦ (z.1, g z.2), by fun_prop⟩
  have hF (r : ℕ) : Set.MapsTo (F r) ({(0, x)}ᶜ : Set ((Fin r → ℝ) × X))
      ({(0, y)}ᶜ : Set ((Fin r → ℝ) × Y)) := by
    intro z hz heq
    apply hz
    apply Prod.ext
    · exact congrArg (fun q : (Fin r → ℝ) × Y ↦ q.1) heq
    · by_contra hne
      exact hf hne (congrArg Prod.snd heq)
  have hG (r : ℕ) : Set.MapsTo (G r) ({(0, x)}ᶜ : Set ((Fin r → ℝ) × X))
      ({(0, y)}ᶜ : Set ((Fin r → ℝ) × Y)) := by
    intro z hz heq
    apply hz
    apply Prod.ext
    · exact congrArg (fun q : (Fin r → ℝ) × Y ↦ q.1) heq
    · by_contra hne
      exact hg hne (congrArg Prod.snd heq)
  change relativeSingularHomologyMap R (F r) (hF r) (k + r) =
    s • relativeSingularHomologyMap R (G r) (hG r) (k + r)
  induction r with
  | zero =>
    change relativeSingularHomologyMap R (F 0) (hF 0) k =
      s • relativeSingularHomologyMap R (G 0) (hG 0) k
    -- The empty coordinate list is a single point, with its actual projection to the base.
    let eX := Homeomorph.uniqueProd (Fin 0 → ℝ) X
    let eY := Homeomorph.uniqueProd (Fin 0 → ℝ) Y
    let pX : C((Fin 0 → ℝ) × X, X) := ⟨eX, eX.continuous⟩
    let pY : C((Fin 0 → ℝ) × Y, Y) := ⟨eY, eY.continuous⟩
    have hpX : Set.MapsTo pX ({(0, x)}ᶜ : Set ((Fin 0 → ℝ) × X)) ({x}ᶜ : Set X) :=
      fun z hz heq ↦ hz (eX.injective heq)
    have hpY : Set.MapsTo pY ({(0, y)}ᶜ : Set ((Fin 0 → ℝ) × Y)) ({y}ᶜ : Set Y) :=
      fun z hz heq ↦ hz (eY.injective heq)
    let P := relativeSingularHomologyMap R pX hpX k
    let Q := relativeSingularHomologyMap R pY hpY k
    let : IsIso Q := hiso eY (0, y) y rfl hpY k
    have hFQ : relativeSingularHomologyMap R (F 0) (hF 0) k ≫ Q =
        P ≫ relativeSingularHomologyMap R f hf k := by
      change homologyMap _ k ≫ homologyMap _ k = homologyMap _ k ≫ homologyMap _ k
      rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
        ← homologyMap_comp, ← relativeSingularChainsMap_comp]
      rfl
    have hGQ : relativeSingularHomologyMap R (G 0) (hG 0) k ≫ Q =
        P ≫ relativeSingularHomologyMap R g hg k := by
      change homologyMap _ k ≫ homologyMap _ k = homologyMap _ k ≫ homologyMap _ k
      rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
        ← homologyMap_comp, ← relativeSingularChainsMap_comp]
      rfl
    apply (cancel_mono Q).mp
    rw [Linear.smul_comp, hFQ, hGQ, h, Linear.comp_smul]
  | succ r ih =>
    change relativeSingularHomologyMap R (F (r + 1)) (hF (r + 1)) (k + r + 1) =
      s • relativeSingularHomologyMap R (G (r + 1)) (hG (r + 1)) (k + r + 1)
    -- Split off the first coordinate and apply the preceding real-suspension comparison.
    let e (Z : Type u) [TopologicalSpace Z] :
        ((Fin (r + 1) → ℝ) × Z) ≃ₜ ℝ × ((Fin r → ℝ) × Z) :=
      { toFun z := (z.1 0, (fun i ↦ z.1 i.succ, z.2))
        invFun z := (Fin.cases z.1 z.2.1, z.2.2)
        left_inv z := by
          apply Prod.ext
          · funext i
            exact Fin.cases rfl (fun _ ↦ rfl) i
          · rfl
        right_inv _ := rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by
          apply Continuous.prodMk _ continuous_snd.snd
          apply continuous_pi
          intro i
          exact Fin.cases continuous_fst
            (fun i ↦ (continuous_apply i).comp continuous_snd.fst) i }
    let pX : C((Fin (r + 1) → ℝ) × X, ℝ × ((Fin r → ℝ) × X)) :=
      ⟨e X, (e X).continuous⟩
    let pY : C((Fin (r + 1) → ℝ) × Y, ℝ × ((Fin r → ℝ) × Y)) :=
      ⟨e Y, (e Y).continuous⟩
    have hpX : Set.MapsTo pX ({(0, x)}ᶜ : Set ((Fin (r + 1) → ℝ) × X))
        ({(0, (0, x))}ᶜ : Set (ℝ × ((Fin r → ℝ) × X))) :=
      fun z hz heq ↦ hz ((e X).injective heq)
    have hpY : Set.MapsTo pY ({(0, y)}ᶜ : Set ((Fin (r + 1) → ℝ) × Y))
        ({(0, (0, y))}ᶜ : Set (ℝ × ((Fin r → ℝ) × Y))) :=
      fun z hz heq ↦ hz ((e Y).injective heq)
    let P := relativeSingularHomologyMap R pX hpX (k + r + 1)
    let Q := relativeSingularHomologyMap R pY hpY (k + r + 1)
    let : IsIso Q := hiso (e Y) (0, y) (0, (0, y)) rfl hpY (k + r + 1)
    have hreal := relativeSingularHomologyMap_realProd_smul R (0, x)
      (F r) (G r) (0, y) (hF r) (hG r) (k + r) s ih
    generalize hfreal : relativeSingularHomologyMap R
      (X := ℝ × ((Fin r → ℝ) × X)) (Y := ℝ × ((Fin r → ℝ) × Y))
      (A := ({(0, (0, x))}ᶜ : Set (ℝ × ((Fin r → ℝ) × X))))
      (B := ({(0, (0, y))}ᶜ : Set (ℝ × ((Fin r → ℝ) × Y))))
      _ _ (k + r + 1) = FR at hreal
    generalize hgreal : relativeSingularHomologyMap R
      (X := ℝ × ((Fin r → ℝ) × X)) (Y := ℝ × ((Fin r → ℝ) × Y))
      (A := ({(0, (0, x))}ᶜ : Set (ℝ × ((Fin r → ℝ) × X))))
      (B := ({(0, (0, y))}ᶜ : Set (ℝ × ((Fin r → ℝ) × Y))))
      _ _ (k + r + 1) = GR at hreal
    have hFQ : relativeSingularHomologyMap R (F (r + 1)) (hF (r + 1))
        (k + r + 1) ≫ Q = P ≫ FR := by
      rw [← hfreal]
      change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
      rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
        ← homologyMap_comp, ← relativeSingularChainsMap_comp]
      rfl
    have hGQ : relativeSingularHomologyMap R (G (r + 1)) (hG (r + 1))
        (k + r + 1) ≫ Q = P ≫ GR := by
      rw [← hgreal]
      change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
      rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
        ← homologyMap_comp, ← relativeSingularChainsMap_comp]
      rfl
    apply (cancel_mono Q).mp
    rw [Linear.smul_comp, hFQ, hGQ, hreal, Linear.comp_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Suspension also commutes with the original local-homology transport through an
open partial homeomorphism. This is the chart-source form of product naturality. -/
theorem localHomologySuspensionIso_chart
    {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (hx : x ∈ e.source) (k : ℕ) :
    ModuleCat.ofHom (localHomologyChartEquiv
        ((OpenPartialHomeomorph.refl ℝ).prod e) (0, x) ⟨Set.mem_univ 0, hx⟩
        (k + 1)).toLinearMap ≫ (localHomologySuspensionIso ℤ (e x) k).hom =
      (localHomologySuspensionIso ℤ x k).hom ≫
        ModuleCat.ofHom (localHomologyChartEquiv e x hx k).toLinearMap := by
  let xS : e.source := ⟨x, hx⟩
  let j : C(e.source, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let p : C(e.source, Y) := ⟨fun z ↦ e z.val, e.continuousOn.domRestrict⟩
  have hj : Set.MapsTo j ({xS}ᶜ : Set e.source) ({x}ᶜ : Set X) :=
    fun z hz heq ↦ hz (Subtype.ext heq)
  have hp : Set.MapsTo p ({xS}ᶜ : Set e.source) ({e x}ᶜ : Set Y) :=
    fun z hz heq ↦ hz (Subtype.ext (e.injOn z.property hx heq))
  let jP : C(ℝ × e.source, ℝ × X) := ⟨fun z ↦ (z.1, j z.2), by fun_prop⟩
  let pP : C(ℝ × e.source, ℝ × Y) := ⟨fun z ↦ (z.1, p z.2), by fun_prop⟩
  have hjP : Set.MapsTo jP ({(0, xS)}ᶜ : Set (ℝ × e.source))
      ({(0, x)}ᶜ : Set (ℝ × X)) := by
    intro z hz heq
    apply hz
    apply Prod.ext
    · exact congrArg (fun q : ℝ × X ↦ q.1) heq
    · exact Subtype.ext (congrArg (fun q : ℝ × X ↦ q.2) heq)
  have hpP : Set.MapsTo pP ({(0, xS)}ᶜ : Set (ℝ × e.source))
      ({(0, e x)}ᶜ : Set (ℝ × Y)) := by
    intro z hz heq
    apply hz
    apply Prod.ext
    · exact congrArg (fun q : ℝ × Y ↦ q.1) heq
    · exact Subtype.ext (e.injOn z.2.property hx
        (congrArg (fun q : ℝ × Y ↦ q.2) heq))
  let J := relativeSingularHomologyMap ℤ j hj k
  let P := relativeSingularHomologyMap ℤ p hp k
  let JP := relativeSingularHomologyMap ℤ jP hjP (k + 1)
  let PP := relativeSingularHomologyMap ℤ pP hpP (k + 1)
  let C := ModuleCat.ofHom (localHomologyChartEquiv e x hx k).toLinearMap
  let CP := ModuleCat.ofHom (localHomologyChartEquiv
    ((OpenPartialHomeomorph.refl ℝ).prod e) (0, x) ⟨Set.mem_univ 0, hx⟩
    (k + 1)).toLinearMap
  -- Open excision makes the original product inclusion invertible at its distinguished point.
  have hOpen : IsOpenEmbedding jP :=
    IsOpenEmbedding.id.prodMap e.open_source.isOpenEmbedding_subtypeVal
  have hA : (jP ⁻¹' ({(0, x)} : Set (ℝ × X)))ᶜ =
      ({(0, xS)}ᶜ : Set (ℝ × e.source)) := by
    apply congrArg (fun A : Set (ℝ × e.source) ↦ Aᶜ)
    ext z
    change (z.1, z.2.val) = (0, x) ↔ z = (0, xS)
    simp only [Prod.ext_iff, Subtype.ext_iff, xS]
  let : IsIso JP := by
    have hexc {A : Set (ℝ × e.source)}
        (hAA : A = (jP ⁻¹' ({(0, x)} : Set (ℝ × X)))ᶜ)
        (hmap : Set.MapsTo jP A ({(0, x)}ᶜ : Set (ℝ × X))) :
        homotopyEquivalences (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
          (relativeSingularChainsMap ℤ jP hmap) := by
      subst A
      exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding ℤ jP
        hOpen ({(0, x)} : Set (ℝ × X)) isClosed_singleton
        (Set.singleton_subset_iff.mpr ⟨(0, xS), rfl⟩)
    obtain ⟨q', hq'⟩ := hexc hA.symm hjP
    change IsIso (homologyMap _ (k + 1))
    rw [← hq']
    change IsIso (q'.toHomologyIso (k + 1)).hom
    infer_instance
  have hC : J ≫ C = P := localHomologyChartEquiv_naturality e x hx j
    (fun z ↦ z.property) hj k
  have hCP : JP ≫ CP = PP := localHomologyChartEquiv_naturality
    ((OpenPartialHomeomorph.refl ℝ).prod e) (0, x) ⟨Set.mem_univ 0, hx⟩ jP
    (fun z ↦ ⟨Set.mem_univ _, z.2.property⟩) hjP (k + 1)
  have hJ : JP ≫ (localHomologySuspensionIso ℤ x k).hom =
      (localHomologySuspensionIso ℤ xS k).hom ≫ J :=
    localHomologySuspensionIso_naturality ℤ xS j x hj k
  have hP : PP ≫ (localHomologySuspensionIso ℤ (e x) k).hom =
      (localHomologySuspensionIso ℤ xS k).hom ≫ P :=
    localHomologySuspensionIso_naturality ℤ xS p (e x) hp k
  -- Cancel that same inclusion; no extension of the partial homeomorphism is used.
  change CP ≫ _ = _ ≫ C
  apply (cancel_epi JP).mp
  rw [← Category.assoc, hCP, hP, ← hC, ← Category.assoc, ← hJ]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
omit [T2Space X] in
/-- A continuous family of fiber-linear maps has the same local homology map as its
value over the distinguished base point. The base map only needs to preserve the
punctured pair; no derivative or invertibility of the interpolated matrices is used. -/
theorem relativeSingularHomologyMap_fiberLinear_eq_const
    {Y V W : Type u} [TopologicalSpace Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : C(X, Y)) (y : Y) (hf : Set.MapsTo f ({x}ᶜ : Set X) ({y}ᶜ : Set Y))
    (A : C(X, V →L[ℝ] W)) (hA : Function.Injective (A x)) (v : V) (k : ℕ) :
    relativeSingularHomologyMap R
        (⟨fun z : X × V ↦ (f z.1, A z.1 z.2), by fun_prop⟩ : C(X × V, Y × W))
        (A := ({(x, v)}ᶜ : Set (X × V))) (B := ({(y, A x v)}ᶜ : Set (Y × W)))
        (by
          intro z hz heq
          have hx : z.1 = x := by
            by_contra hne
            exact hf hne (congrArg Prod.fst heq)
          have hv : z.2 = v := hA (by
            have h := congrArg Prod.snd heq
            change A z.1 z.2 = A x v at h
            rwa [hx] at h)
          exact hz (Prod.ext hx hv)) k =
      relativeSingularHomologyMap R
        (⟨fun z : X × V ↦ (f z.1, A x z.2), by fun_prop⟩ : C(X × V, Y × W))
        (A := ({(x, v)}ᶜ : Set (X × V))) (B := ({(y, A x v)}ᶜ : Set (Y × W)))
        (by
          intro z hz heq
          have hx : z.1 = x := by
            by_contra hne
            exact hf hne (congrArg Prod.fst heq)
          exact hz (Prod.ext hx (hA (congrArg Prod.snd heq)))) k := by
  let p : C(X × V, Y × W) := ⟨fun z ↦ (f z.1, A z.1 z.2), by fun_prop⟩
  let q : C(X × V, Y × W) := ⟨fun z ↦ (f z.1, A x z.2), by fun_prop⟩
  -- Keep the base map fixed. Only the fiber-linear map is interpolated.
  let H : p.Homotopy q :=
    { toFun z := (f z.2.1,
        (1 - (z.1 : ℝ)) • A z.2.1 z.2.2 + (z.1 : ℝ) • A x z.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := by intro z; simp [p]
      map_one_left := by intro z; simp [q] }
  apply relativeSingularHomologyMap_eq_of_homotopy R _ _ H
  intro t z hz heq
  -- Away from x the base coordinate avoids y. Over x the fiber map remains A(x).
  have hx : z.1 = x := by
    by_contra hne
    exact hf hne (congrArg Prod.fst heq)
  have hv : z.2 = v := hA (by
    have hh := congrArg Prod.snd heq
    change (1 - (t : ℝ)) • A z.1 z.2 + (t : ℝ) • A x z.2 = A x v at hh
    rw [hx, ← add_smul, sub_add_cancel, one_smul] at hh
    exact hh)
  exact hz (Prod.ext hx hv)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A scalar local-map comparison is preserved by a finite Euclidean factor at any point,
using its original topology. Translation does not introduce an orientation convention. -/
theorem relativeSingularHomologyMap_euclideanProd_smul
    {Y : Type u} [TopologicalSpace Y] [T2Space Y] (f g : C(X, Y)) (y : Y)
    (hf : Set.MapsTo f ({x}ᶜ : Set X) ({y}ᶜ : Set Y))
    (hg : Set.MapsTo g ({x}ᶜ : Set X) ({y}ᶜ : Set Y))
    (k r : ℕ) (a : EuclideanSpace ℝ (Fin r)) (s : R)
    (h : relativeSingularHomologyMap R f hf k = s • relativeSingularHomologyMap R g hg k) :
    relativeSingularHomologyMap R
        (⟨fun z : EuclideanSpace ℝ (Fin r) × X ↦ (z.1, f z.2), by fun_prop⟩ :
          C(EuclideanSpace ℝ (Fin r) × X, EuclideanSpace ℝ (Fin r) × Y))
        (A := ({(a, x)}ᶜ : Set (EuclideanSpace ℝ (Fin r) × X)))
        (B := ({(a, y)}ᶜ : Set (EuclideanSpace ℝ (Fin r) × Y)))
        (by
          intro z hz heq
          apply hz
          apply Prod.ext
          · exact congrArg (fun p : EuclideanSpace ℝ (Fin r) × Y ↦ p.1) heq
          · by_contra hne
            exact hf hne (congrArg Prod.snd heq)) (k + r) =
      s • relativeSingularHomologyMap R
        (⟨fun z : EuclideanSpace ℝ (Fin r) × X ↦ (z.1, g z.2), by fun_prop⟩ :
          C(EuclideanSpace ℝ (Fin r) × X, EuclideanSpace ℝ (Fin r) × Y))
        (A := ({(a, x)}ᶜ : Set (EuclideanSpace ℝ (Fin r) × X)))
        (B := ({(a, y)}ᶜ : Set (EuclideanSpace ℝ (Fin r) × Y)))
        (by
          intro z hz heq
          apply hz
          apply Prod.ext
          · exact congrArg (fun p : EuclideanSpace ℝ (Fin r) × Y ↦ p.1) heq
          · by_contra hne
            exact hg hne (congrArg Prod.snd heq)) (k + r) := by
  let V := EuclideanSpace ℝ (Fin r)
  let e : V ≃ₜ (Fin r → ℝ) :=
    (Homeomorph.addRight (-a)).trans (PiLp.homeomorph 2 (fun _ : Fin r ↦ ℝ))
  have hea : e a = 0 := by
    change (PiLp.homeomorph 2 (fun _ : Fin r ↦ ℝ)) (a + -a) = 0
    rw [add_neg_cancel]
    rfl
  let eX := e.prodCongr (Homeomorph.refl X)
  let eY := e.prodCongr (Homeomorph.refl Y)
  let pX : C(V × X, (Fin r → ℝ) × X) := ⟨eX, eX.continuous⟩
  let pY : C(V × Y, (Fin r → ℝ) × Y) := ⟨eY, eY.continuous⟩
  have heX : eX (a, x) = (0, x) := by
    change (e a, x) = (0, x)
    rw [hea]
  have heY : eY (a, y) = (0, y) := by
    change (e a, y) = (0, y)
    rw [hea]
  have hpX : Set.MapsTo pX ({(a, x)}ᶜ : Set (V × X))
      ({(0, x)}ᶜ : Set ((Fin r → ℝ) × X)) := by
    intro z hz heq
    apply hz
    apply eX.injective
    exact heq.trans heX.symm
  have hpY : Set.MapsTo pY ({(a, y)}ᶜ : Set (V × Y))
      ({(0, y)}ᶜ : Set ((Fin r → ℝ) × Y)) := by
    intro z hz heq
    apply hz
    apply eY.injective
    exact heq.trans heY.symm
  have hpYi : Set.MapsTo eY.symm ({(0, y)}ᶜ : Set ((Fin r → ℝ) × Y))
      ({(a, y)}ᶜ : Set (V × Y)) := by
    intro z hz heq
    apply hz
    calc
      z = eY (eY.symm z) := (eY.apply_symm_apply z).symm
      _ = eY (a, y) := congrArg eY heq
      _ = (0, y) := heY
  let P := relativeSingularHomologyMap R pX hpX (k + r)
  let Q := relativeSingularHomologyMap R pY hpY (k + r)
  let : IsIso Q := isIso_relativeSingularHomologyMap_of_inverse R pY
    (⟨eY.symm, eY.symm.continuous⟩ : C((Fin r → ℝ) × Y, V × Y)) hpY hpYi
    (by apply ContinuousMap.ext; intro z; exact eY.symm_apply_apply z)
    (by apply ContinuousMap.ext; intro z; exact eY.apply_symm_apply z) (k + r)
  have hfin := relativeSingularHomologyMap_finProd_smul R x f g y hf hg k r s h
  generalize hF : relativeSingularHomologyMap R
    (X := (Fin r → ℝ) × X) (Y := (Fin r → ℝ) × Y)
    (A := ({(0, x)}ᶜ : Set ((Fin r → ℝ) × X)))
    (B := ({(0, y)}ᶜ : Set ((Fin r → ℝ) × Y))) _ _ (k + r) = F at hfin
  generalize hG : relativeSingularHomologyMap R
    (X := (Fin r → ℝ) × X) (Y := (Fin r → ℝ) × Y)
    (A := ({(0, x)}ᶜ : Set ((Fin r → ℝ) × X)))
    (B := ({(0, y)}ᶜ : Set ((Fin r → ℝ) × Y))) _ _ (k + r) = G at hfin
  apply (cancel_mono Q).mp
  rw [Linear.smul_comp]
  -- Both coordinate squares commute before taking chains or homology.
  have hFQ : relativeSingularHomologyMap R
      (⟨fun z : V × X ↦ (z.1, f z.2), by fun_prop⟩ : C(V × X, V × Y))
      (A := ({(a, x)}ᶜ : Set (V × X))) (B := ({(a, y)}ᶜ : Set (V × Y)))
      (by
        intro z hz heq
        apply hz
        apply Prod.ext
        · exact congrArg (fun p : V × Y ↦ p.1) heq
        · by_contra hne
          exact hf hne (congrArg Prod.snd heq)) (k + r) ≫ Q = P ≫ F := by
    rw [← hF]
    change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
      ← homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have hGQ : relativeSingularHomologyMap R
      (⟨fun z : V × X ↦ (z.1, g z.2), by fun_prop⟩ : C(V × X, V × Y))
      (A := ({(a, x)}ᶜ : Set (V × X))) (B := ({(a, y)}ᶜ : Set (V × Y)))
      (by
        intro z hz heq
        apply hz
        apply Prod.ext
        · exact congrArg (fun p : V × Y ↦ p.1) heq
        · by_contra hne
          exact hg hne (congrArg Prod.snd heq)) (k + r) ≫ Q = P ≫ G := by
    rw [← hG]
    change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
      ← homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  rw [hFQ, hGQ, hfin, Linear.comp_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The local map of a continuous fiber-linear coordinate change has the product of
the base and fiber scalars, in base-first order. The comparison uses only the two
specified local maps, and does not assume a total-space orientation or a Gysin formula. -/
theorem relativeSingularHomologyMap_fiberLinear_eq_smul_prod
    (n r : ℕ) {B : Type} [TopologicalSpace B] [T2Space B] (b : B)
    (p q : C(B, EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n))
    (hp : Set.MapsTo p ({b}ᶜ : Set B) ({c}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
    (hq : Set.MapsTo q ({b}ᶜ : Set B) ({c}ᶜ : Set (EuclideanSpace ℝ (Fin n))))
    (A : C(B, EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)))
    (hA : Function.Injective (A b)) (v : EuclideanSpace ℝ (Fin r))
    (t : C(EuclideanSpace ℝ (Fin r), EuclideanSpace ℝ (Fin r)))
    (ht : Set.MapsTo t ({v}ᶜ : Set (EuclideanSpace ℝ (Fin r)))
      ({A b v}ᶜ : Set (EuclideanSpace ℝ (Fin r))))
    (s₁ s₂ : R)
    (hbase : relativeSingularHomologyMap R p hp n =
      s₁ • relativeSingularHomologyMap R q hq n)
    (hfiber : relativeSingularHomologyMap R
      (⟨A b, (A b).continuous⟩ : C(EuclideanSpace ℝ (Fin r), EuclideanSpace ℝ (Fin r)))
      (A := ({v}ᶜ : Set (EuclideanSpace ℝ (Fin r))))
      (B := ({A b v}ᶜ : Set (EuclideanSpace ℝ (Fin r))))
      (fun _ hz heq ↦ hz (hA heq)) r = s₂ • relativeSingularHomologyMap R t ht r)
    (hvar : Set.MapsTo
      (⟨fun z : B × EuclideanSpace ℝ (Fin r) ↦ (p z.1, A z.1 z.2), by fun_prop⟩ :
        C(B × EuclideanSpace ℝ (Fin r),
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin r)))
      ({(b, v)}ᶜ : Set (B × EuclideanSpace ℝ (Fin r)))
      ({(c, A b v)}ᶜ : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin r))))
    (href : Set.MapsTo
      (⟨fun z : B × EuclideanSpace ℝ (Fin r) ↦ (q z.1, t z.2), by fun_prop⟩ :
        C(B × EuclideanSpace ℝ (Fin r),
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin r)))
      ({(b, v)}ᶜ : Set (B × EuclideanSpace ℝ (Fin r)))
      ({(c, A b v)}ᶜ : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin r)))) :
    relativeSingularHomologyMap R
      (⟨fun z : B × EuclideanSpace ℝ (Fin r) ↦ (p z.1, A z.1 z.2), by fun_prop⟩ :
        C(B × EuclideanSpace ℝ (Fin r),
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin r))) hvar (n + r) =
      (s₁ * s₂) • relativeSingularHomologyMap R
        (⟨fun z : B × EuclideanSpace ℝ (Fin r) ↦ (q z.1, t z.2), by fun_prop⟩ :
          C(B × EuclideanSpace ℝ (Fin r),
            EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin r))) href (n + r) := by
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin r)
  let P : C(B × F, E × F) := ⟨fun z ↦ (p z.1, z.2), by fun_prop⟩
  let Q : C(B × F, E × F) := ⟨fun z ↦ (q z.1, z.2), by fun_prop⟩
  let L : C(E × F, E × F) := ⟨fun z ↦ (z.1, A b z.2), by fun_prop⟩
  let T : C(E × F, E × F) := ⟨fun z ↦ (z.1, t z.2), by fun_prop⟩
  have hP : Set.MapsTo P ({(b, v)}ᶜ : Set (B × F)) ({(c, v)}ᶜ : Set (E × F)) := by
    intro z hz heq
    apply hz
    apply Prod.ext
    · by_contra hne
      exact hp hne (congrArg Prod.fst heq)
    · exact congrArg (fun z : E × F ↦ z.2) heq
  have hQ : Set.MapsTo Q ({(b, v)}ᶜ : Set (B × F)) ({(c, v)}ᶜ : Set (E × F)) := by
    intro z hz heq
    apply hz
    apply Prod.ext
    · by_contra hne
      exact hq hne (congrArg Prod.fst heq)
    · exact congrArg (fun z : E × F ↦ z.2) heq
  have hL : Set.MapsTo L ({(c, v)}ᶜ : Set (E × F))
      ({(c, A b v)}ᶜ : Set (E × F)) := by
    intro z hz heq
    have hh := Prod.mk.inj (show (z.1, A b z.2) = (c, A b v) from heq)
    exact hz (Prod.ext hh.1 (hA hh.2))
  have hT : Set.MapsTo T ({(c, v)}ᶜ : Set (E × F))
      ({(c, A b v)}ᶜ : Set (E × F)) := by
    intro z hz heq
    have hh := Prod.mk.inj (show (z.1, t z.2) = (c, A b v) from heq)
    apply hz
    apply Prod.ext
    · exact hh.1
    · by_contra hne
      exact ht hne hh.2
  let PH := relativeSingularHomologyMap R P hP (n + r)
  let QH := relativeSingularHomologyMap R Q hQ (n + r)
  let LH := relativeSingularHomologyMap R L hL (n + r)
  let TH := relativeSingularHomologyMap R T hT (n + r)
  -- Lift the base comparison, then undo the two actual swaps to retain base-first order.
  have hleft := relativeSingularHomologyMap_euclideanProd_smul R b p q c hp hq
    n r v s₁ hbase
  generalize hPL : relativeSingularHomologyMap R
    (X := F × B) (Y := F × E) (A := ({(v, b)}ᶜ : Set (F × B)))
    (B := ({(v, c)}ᶜ : Set (F × E))) _ _ (n + r) = PL at hleft
  generalize hQL : relativeSingularHomologyMap R
    (X := F × B) (Y := F × E) (A := ({(v, b)}ᶜ : Set (F × B)))
    (B := ({(v, c)}ᶜ : Set (F × E))) _ _ (n + r) = QL at hleft
  let j : C(B × F, F × B) := ⟨Prod.swap, continuous_swap⟩
  let d : C(E × F, F × E) := ⟨Prod.swap, continuous_swap⟩
  let di : C(F × E, E × F) := ⟨Prod.swap, continuous_swap⟩
  have hj : Set.MapsTo j ({(b, v)}ᶜ : Set (B × F)) ({(v, b)}ᶜ : Set (F × B)) :=
    fun _ hz heq ↦ hz ((Homeomorph.prodComm B F).injective heq)
  have hd : Set.MapsTo d ({(c, v)}ᶜ : Set (E × F)) ({(v, c)}ᶜ : Set (F × E)) :=
    fun _ hz heq ↦ hz ((Homeomorph.prodComm E F).injective heq)
  have hdi : Set.MapsTo di ({(v, c)}ᶜ : Set (F × E)) ({(c, v)}ᶜ : Set (E × F)) :=
    fun _ hz heq ↦ hz ((Homeomorph.prodComm F E).injective heq)
  let J := relativeSingularHomologyMap R j hj (n + r)
  let D := relativeSingularHomologyMap R d hd (n + r)
  let : IsIso D := isIso_relativeSingularHomologyMap_of_inverse R d di hd hdi
    (by apply ContinuousMap.ext; intro z; rfl)
    (by apply ContinuousMap.ext; intro z; rfl) (n + r)
  have hPD : PH ≫ D = J ≫ PL := by
    rw [← hPL]
    change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
      ← homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have hQD : QH ≫ D = J ≫ QL := by
    rw [← hQL]
    change homologyMap _ _ ≫ homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp,
      ← homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have hbaseProd : PH = s₁ • QH := by
    apply (cancel_mono D).mp
    rw [Linear.smul_comp, hPD, hQD, hleft, Linear.comp_smul]
  -- Lift the fiber comparison with the base as the unchanged Euclidean factor.
  have hfiberProd : LH = s₂ • TH := by
    have hright := relativeSingularHomologyMap_euclideanProd_smul R v
      (⟨A b, (A b).continuous⟩ : C(F, F)) t (A b v)
      (fun _ hz heq ↦ hz (hA heq)) ht r n c s₂ hfiber
    rw [Nat.add_comm r n] at hright
    exact hright
  have hvarComp : relativeSingularHomologyMap R
      (⟨fun z : B × F ↦ (p z.1, A z.1 z.2), by fun_prop⟩ : C(B × F, E × F))
      hvar (n + r) = PH ≫ LH := by
    rw [relativeSingularHomologyMap_fiberLinear_eq_const R b p c hp A hA v]
    change homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  have hrefComp : relativeSingularHomologyMap R
      (⟨fun z : B × F ↦ (q z.1, t z.2), by fun_prop⟩ : C(B × F, E × F))
      href (n + r) = QH ≫ TH := by
    change homologyMap _ _ = homologyMap _ _ ≫ homologyMap _ _
    rw [← homologyMap_comp, ← relativeSingularChainsMap_comp]
    rfl
  -- The two independent scalar factors multiply in the original ordered product.
  rw [hvarComp, hrefComp, hbaseProd, hfiberProd, Linear.smul_comp,
    Linear.comp_smul, smul_smul]

end AtiyahSinger
