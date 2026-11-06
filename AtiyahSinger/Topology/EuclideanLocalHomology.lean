/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EuclideanRelativeHomology
public import AtiyahSinger.Topology.RelativeSingularTriple

/-!
# Euclidean local homology via the actual relative connecting map

Public module ID: M1822.

Cover punctured `ℝ × E` by the complements of its two opposite closed half axes.
The lower member and the ambient product are contractible. The connecting map
of their triple is therefore an isomorphism in every degree. Open excision and
the transverse projection identify its target with the local pair of `E`.
This includes the bottom degree without replacing ordinary chains by a reduced model.

Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, the suspension calculation
of Euclidean local homology. The displayed connecting map fixes the recursion used
to compare the original orientation simplex in a separate module.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Topology
open scoped unitInterval

universe u

variable (R : Type) [CommRing R]

/-- The half-axis complement for s ≠ 0; at s = 0 it is the full-axis complement. -/
def euclideanPuncturedHalfSpace (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] (s : ℝ) : Set (ℝ × E) :=
  {z | 0 < s * z.1 ∨ z.2 ≠ 0}

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The defining set is open for every real parameter. -/
theorem isOpen_euclideanPuncturedHalfSpace (s : ℝ) :
    IsOpen (euclideanPuncturedHalfSpace E s) :=
  (isOpen_lt continuous_const (continuous_const.mul continuous_fst)).union
    (isOpen_ne_fun continuous_snd continuous_const)

/-- The defining set lies in the original punctured product. -/
theorem euclideanPuncturedHalfSpace_subset (s : ℝ) :
    euclideanPuncturedHalfSpace E s ⊆ {z : ℝ × E | z ≠ 0} := by
  intro z hz hzero
  rcases hz with hpos | hne
  · simp [hzero] at hpos
  · exact hne (congrArg Prod.snd hzero)

/-- Straight segments to the corresponding axis point contract each half-axis complement. -/
theorem contractibleSpace_euclideanPuncturedHalfSpace (s : ℝ) (hs : s ≠ 0) :
    ContractibleSpace (euclideanPuncturedHalfSpace E s) := by
  have hstar : StarConvex ℝ (s, (0 : E)) (euclideanPuncturedHalfSpace E s) := by
    intro z hz a b ha hb hab
    change 0 < s * (a * s + b * z.1) ∨ a • (0 : E) + b • z.2 ≠ 0
    by_cases hzero : b = 0
    · left
      have ha' : a = 1 := by linarith
      simpa only [ha', hzero, one_mul, zero_mul, add_zero] using mul_self_pos.mpr hs
    · have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hzero)
      rcases hz with hz | hz
      · left
        have hsq : 0 ≤ a * s ^ 2 := mul_nonneg ha (sq_nonneg s)
        have hp : 0 < b * (s * z.1) := mul_pos hb' hz
        nlinarith
      · right
        simpa using smul_ne_zero hzero hz
  exact hstar.contractibleSpace
    ⟨(s, 0), Or.inl (by simpa [pow_two] using sq_pos_of_ne_zero hs)⟩

/-- The exact triple consisting of the lower half-axis complement and punctured product. -/
def euclideanLocalSuspensionTriple : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  relativeSingularTripleSequence R (euclideanPuncturedHalfSpace E (-1))
    {z : ℝ × E | z ≠ 0} (euclideanPuncturedHalfSpace_subset E (-1))

/-- The displayed Euclidean triple is short exact on the original chain quotients. -/
theorem shortExact_euclideanLocalSuspensionTriple :
    (euclideanLocalSuspensionTriple R E).ShortExact :=
  shortExact_relativeSingularTripleSequence R _ _ _

/-- The triple connecting map is invertible, including the degree-one to degree-zero step. -/
def euclideanLocalSuspensionBoundaryIso (k : ℕ) :
    relativeSingularHomology R {z : ℝ × E | z ≠ 0} (k + 1) ≅
      relativeSingularHomology R
        ((Subtype.val : {z : ℝ × E | z ≠ 0} → ℝ × E) ⁻¹'
          euclideanPuncturedHalfSpace E (-1)) k := by
  let := contractibleSpace_euclideanPuncturedHalfSpace E (-1) (by norm_num)
  have hzero (j : ℕ) : IsZero ((euclideanLocalSuspensionTriple R E).X₂.homology j) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      (subsingleton_relativeSingularHomology_of_contractible R
        (euclideanPuncturedHalfSpace E (-1)) j)
  exact (shortExact_euclideanLocalSuspensionTriple R E).δIso (k + 1) k rfl
    (hzero (k + 1)) (hzero k)

/-- The upper half-axis complement as an open subspace of the punctured product. -/
def euclideanLocalSuspensionInclusion :
    C(euclideanPuncturedHalfSpace E 1, {z : ℝ × E | z ≠ 0}) :=
  ⟨fun z ↦ ⟨z.val, euclideanPuncturedHalfSpace_subset E 1 z.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- This actual inclusion is open, as needed for the original excision map. -/
theorem isOpenEmbedding_euclideanLocalSuspensionInclusion :
    IsOpenEmbedding (euclideanLocalSuspensionInclusion E) := by
  apply IsOpenEmbedding.of_comp (euclideanLocalSuspensionInclusion E)
    (isOpen_ne_fun continuous_id continuous_const).isOpenEmbedding_subtypeVal
  exact isOpen_euclideanPuncturedHalfSpace E 1 |>.isOpenEmbedding_subtypeVal

/-- Projection to the transverse vector identifies the upper pair with the smaller local pair. -/
def euclideanLocalSuspensionProjection : C(euclideanPuncturedHalfSpace E 1, E) :=
  ⟨fun z ↦ z.val.2, continuous_snd.comp continuous_subtype_val⟩

/-- On the intersection of the two half-axis complements, the transverse vector is nonzero. -/
theorem euclideanLocalSuspensionProjection_mapsTo :
    Set.MapsTo (euclideanLocalSuspensionProjection E)
      ((Subtype.val : euclideanPuncturedHalfSpace E 1 → ℝ × E) ⁻¹'
        euclideanPuncturedHalfSpace E (-1)) {x : E | x ≠ 0} := by
  intro z hz hzero
  change z.val.2 = 0 at hzero
  have hpos : 0 < z.val.1 := by
    simpa [euclideanPuncturedHalfSpace, hzero] using z.property
  have hneg : z.val.1 < 0 := by
    change 0 < (-1 : ℝ) * z.val.1 ∨ z.val.2 ≠ 0 at hz
    simpa [hzero] using hz
  exact lt_asymm hpos hneg

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Excision identifies the upper pair with the punctured product modulo the lower part. -/
theorem isIso_euclideanLocalSuspensionExcision (k : ℕ) :
    IsIso (relativeSingularHomologyMap R (euclideanLocalSuspensionInclusion E)
      (A := (Subtype.val : euclideanPuncturedHalfSpace E 1 → ℝ × E) ⁻¹'
        euclideanPuncturedHalfSpace E (-1))
      (B := (Subtype.val : {z : ℝ × E | z ≠ 0} → ℝ × E) ⁻¹'
        euclideanPuncturedHalfSpace E (-1)) (fun _ hx ↦ hx) k) := by
  let P := {z : ℝ × E | z ≠ 0}
  let B : Set P := (Subtype.val : P → ℝ × E) ⁻¹' euclideanPuncturedHalfSpace E (-1)
  let f := euclideanLocalSuspensionInclusion E
  have hB : IsOpen B := (isOpen_euclideanPuncturedHalfSpace E (-1)).preimage
    continuous_subtype_val
  have hrange : Bᶜ ⊆ Set.range f := by
    intro z hz
    have hy : z.val.2 = 0 := by
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
  have hexc {A' : Set (euclideanPuncturedHalfSpace E 1)} {B' : Set P}
      (hA : A' = (f ⁻¹' Bᶜ)ᶜ) (hBB : B' = Bᶜᶜ) (hf : Set.MapsTo f A' B') :
      homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
        (relativeSingularChainsMap R f hf) := by
    subst A' B'
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R f
      (isOpenEmbedding_euclideanLocalSuspensionInclusion E) Bᶜ hB.isClosed_compl hrange
  obtain ⟨e, he⟩ := hexc
    (A' := (Subtype.val : euclideanPuncturedHalfSpace E 1 → ℝ × E) ⁻¹'
      euclideanPuncturedHalfSpace E (-1)) (B' := B)
    (by simp only [Set.preimage_compl, compl_compl]; rfl) (compl_compl B).symm
    (fun _ hx ↦ hx)
  change IsIso (homologyMap _ k)
  rw [← he]
  change IsIso (e.toHomologyIso k).hom
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original transverse pair projection induces isomorphisms in every degree. -/
theorem isIso_euclideanLocalSuspensionProjection (k : ℕ) :
    IsIso (relativeSingularHomologyMap R (euclideanLocalSuspensionProjection E)
      (euclideanLocalSuspensionProjection_mapsTo E) k) := by
  let U := euclideanPuncturedHalfSpace E 1
  let A : Set U := (Subtype.val : U → ℝ × E) ⁻¹' euclideanPuncturedHalfSpace E (-1)
  let f := euclideanLocalSuspensionProjection E
  let g : C(E, U) := ⟨fun y ↦ ⟨(1, y), Or.inl (by norm_num)⟩, by fun_prop⟩
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
  -- Contract only the first coordinate, keeping the nonzero transverse coordinate unchanged.
  have hgf : (g.comp f).Homotopic (ContinuousMap.id U) := by
    refine ⟨{ toFun p := ⟨((1 - (p.1 : ℝ)) + (p.1 : ℝ) * p.2.val.1, p.2.val.2),
                hupper p.2 p.1⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      simp [g, f, euclideanLocalSuspensionProjection]
    · intro z
      apply Subtype.ext
      change ((1 - (1 : ℝ)) + (1 : ℝ) * z.val.1, z.val.2) = z.val
      simp
  have hfg : (f.comp g).Homotopic (ContinuousMap.id E) := by
    have h : f.comp g = ContinuousMap.id E := rfl
    rw [h]
  let fA : C(A, {y : E | y ≠ 0}) :=
    ⟨fun z ↦ ⟨f z.val, euclideanLocalSuspensionProjection_mapsTo E z.property⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let gA : C({y : E | y ≠ 0}, A) :=
    ⟨fun y ↦ ⟨g y.val, Or.inr y.property⟩, by fun_prop⟩
  have hgfA : (gA.comp fA).Homotopic (ContinuousMap.id A) := by
    refine ⟨{ toFun p := ⟨⟨((1 - (p.1 : ℝ)) + (p.1 : ℝ) * p.2.val.val.1,
                p.2.val.val.2), hupper p.2.val p.1⟩,
                Or.inr (euclideanLocalSuspensionProjection_mapsTo E p.2.property)⟩
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      simp [gA, fA, g, f, euclideanLocalSuspensionProjection]
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      simp
  have hfgA : (fA.comp gA).Homotopic (ContinuousMap.id {y : E | y ≠ 0}) := by
    have h : fA.comp gA = ContinuousMap.id {y : E | y ≠ 0} := rfl
    rw [h]
  exact isIso_relativeSingularHomologyMap_of_absolute R f
    (euclideanLocalSuspensionProjection_mapsTo E)
    (fun j ↦ isIso_singularHomologyMap_of_homotopyInverse R f g hgf hfg j)
    (fun j ↦ isIso_singularHomologyMap_of_homotopyInverse R fA gA hgfA hfgA j) k

/-- Local homology suspension using precisely the triple boundary, excision, and projection. -/
def euclideanLocalSuspensionIso (k : ℕ) :
    relativeSingularHomology R {z : ℝ × E | z ≠ 0} (k + 1) ≅
      relativeSingularHomology R {x : E | x ≠ 0} k := by
  let j := relativeSingularHomologyMap R (euclideanLocalSuspensionInclusion E)
    (A := (Subtype.val : euclideanPuncturedHalfSpace E 1 → ℝ × E) ⁻¹'
      euclideanPuncturedHalfSpace E (-1))
    (B := (Subtype.val : {z : ℝ × E | z ≠ 0} → ℝ × E) ⁻¹'
      euclideanPuncturedHalfSpace E (-1)) (fun _ hx ↦ hx) k
  let p := relativeSingularHomologyMap R (euclideanLocalSuspensionProjection E)
    (euclideanLocalSuspensionProjection_mapsTo E) k
  let : IsIso j := isIso_euclideanLocalSuspensionExcision R E k
  let : IsIso p := isIso_euclideanLocalSuspensionProjection R E k
  exact euclideanLocalSuspensionBoundaryIso R E k ≪≫ (asIso j).symm ≪≫ asIso p

/-- The first-coordinate splitting in one fixed universe, used for local-homology induction. -/
def euclideanLocalCoordinateSplit (n : ℕ) :
    ULift.{u} (Fin (n + 1) → ℝ) ≃ₜ ℝ × ULift.{u} (Fin n → ℝ) where
  toFun x := (x.down 0, ULift.up (fun i ↦ x.down i.succ))
  invFun z := ULift.up (Fin.cases z.1 z.2.down)
  left_inv x := by
    apply ULift.ext
    funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply continuous_uliftUp.comp
    apply continuous_pi
    intro i
    exact Fin.cases continuous_fst
      (fun i ↦ (continuous_apply i).comp (continuous_uliftDown.comp continuous_snd)) i

/-- The actual first-coordinate homeomorphism induces the corresponding local-pair isomorphism. -/
def euclideanLocalCoordinateSplitHomologyIso (n k : ℕ) :
    relativeSingularHomology R {x : ULift.{u} (Fin (n + 1) → ℝ) | x ≠ 0} k ≅
      relativeSingularHomology R {z : ℝ × ULift.{u} (Fin n → ℝ) | z ≠ 0} k := by
  let e := euclideanLocalCoordinateSplit.{u} n
  let f : C(ULift.{u} (Fin (n + 1) → ℝ), ℝ × ULift.{u} (Fin n → ℝ)) :=
    ⟨e, e.continuous⟩
  let g : C(ℝ × ULift.{u} (Fin n → ℝ), ULift.{u} (Fin (n + 1) → ℝ)) :=
    ⟨e.symm, e.symm.continuous⟩
  have hzero : e 0 = 0 := rfl
  have hf : Set.MapsTo f {x | x ≠ 0} {z | z ≠ 0} := by
    intro x hx h
    exact hx (e.injective (h.trans hzero.symm))
  have hg : Set.MapsTo g {z | z ≠ 0} {x | x ≠ 0} := by
    intro z hz h
    change e.symm z = 0 at h
    apply hz
    calc
      z = e (e.symm z) := (e.apply_symm_apply z).symm
      _ = 0 := by rw [h, hzero]
  let : IsIso (relativeSingularHomologyMap R f hf k) :=
    isIso_relativeSingularHomologyMap_of_inverse R f g hf hg
      (by apply ContinuousMap.ext; intro x; exact e.symm_apply_apply x)
      (by apply ContinuousMap.ext; intro z; exact e.apply_symm_apply z) k
  exact asIso (relativeSingularHomologyMap R f hf k)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In dimension zero, the original quotient inverse followed by the point augmentation. -/
def euclideanLocalZeroIso :
    relativeSingularHomology R {x : ULift.{u} (Fin 0 → ℝ) | x ≠ 0} 0 ≅
      singularCoefficient.{u} R := by
  let V := ULift.{u} (Fin 0 → ℝ)
  let A : Set V := {x | x ≠ 0}
  let : PathConnectedSpace V := by
    dsimp [V]
    infer_instance
  let : IsEmpty A := ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
  let : IsIso (relativeSingularChainsProjection R A) :=
    isIso_relativeSingularChainsProjection_of_isEmpty R A
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) 0
  exact (H.mapIso (asIso (relativeSingularChainsProjection R A))).symm ≪≫
    asIso ((TopCat.of V).singularHomology₀ε (singularCoefficient R))

/-- Euclidean top local homology is freely generated over the coefficient ring.
The selected basis follows the original triple boundary and the positive point augmentation. -/
def euclideanLocalHomologyEquiv (n : ℕ) :
    R ≃ₗ[R] relativeSingularHomology R {x : ULift.{u} (Fin n → ℝ) | x ≠ 0} n := by
  induction n with
  | zero =>
    exact ULift.moduleEquiv.symm.trans (euclideanLocalZeroIso.{u} R).symm.toLinearEquiv
  | succ n ih =>
    let e := euclideanLocalCoordinateSplitHomologyIso.{u} R n (n + 1) ≪≫
      euclideanLocalSuspensionIso R (ULift.{u} (Fin n → ℝ)) n
    exact ih.trans e.symm.toLinearEquiv

/-- Euclidean local homology vanishes below its dimension, on the original lifted local pair. -/
theorem subsingleton_relativeSingularHomology_ulift_pi_below_dim
    (n k : ℕ) (hk : k < n) :
    Subsingleton (relativeSingularHomology R {x : ULift.{u} (Fin n → ℝ) | x ≠ 0} k) := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero =>
      -- A positive-dimensional coordinate space has a point in its punctured subspace.
      apply subsingleton_relativeSingularHomology_zero R _
      refine ⟨ULift.up (fun _ ↦ 1), ?_⟩
      intro h
      have hz := congrArg (fun x : ULift.{u} (Fin (n + 1) → ℝ) ↦ x.down 0) h
      norm_num at hz
    | succ k =>
      let := ih k (by omega)
      let e := euclideanLocalCoordinateSplitHomologyIso.{u} R n (k + 1) ≪≫
        euclideanLocalSuspensionIso R (ULift.{u} (Fin n → ℝ)) k
      exact ((ConcreteCategory.isIso_iff_bijective e.hom).mp inferInstance).injective.subsingleton

/-- Below-dimensional vanishing transports through a specified continuous linear chart.
No norm or inner product is required on the original topological module. -/
theorem subsingleton_relativeSingularHomology_below_dim_of_continuousLinearEquiv
    {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] {n : ℕ}
    (e : V ≃L[ℝ] (Fin n → ℝ)) (k : ℕ) (hk : k < n) :
    Subsingleton (relativeSingularHomology R {v : V | v ≠ 0} k) := by
  let f : C(V, ULift.{u} (Fin n → ℝ)) :=
    ⟨fun v ↦ ULift.up (e v), continuous_uliftUp.comp e.continuous⟩
  let g : C(ULift.{u} (Fin n → ℝ), V) :=
    ⟨fun x ↦ e.symm x.down, e.symm.continuous.comp continuous_uliftDown⟩
  have hf : Set.MapsTo f {v | v ≠ 0} {x | x ≠ 0} := by
    intro v hv h
    apply hv
    apply e.injective
    simpa [f] using congrArg ULift.down h
  have hg : Set.MapsTo g {x | x ≠ 0} {v | v ≠ 0} := by
    intro x hx h
    apply hx
    apply ULift.ext
    simpa [g] using congrArg e h
  have hiso : IsIso (relativeSingularHomologyMap R f hf k) :=
    isIso_relativeSingularHomologyMap_of_inverse R f g hf hg
      (by apply ContinuousMap.ext; intro v; exact e.symm_apply_apply v)
      (by apply ContinuousMap.ext; intro x; exact congrArg ULift.up (e.apply_symm_apply x.down)) k
  let := subsingleton_relativeSingularHomology_ulift_pi_below_dim.{u} R n k hk
  exact ((ConcreteCategory.isIso_iff_bijective _).mp hiso).injective.subsingleton

end AtiyahSinger
