/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundlePullback
public import AtiyahSinger.Topology.ComplexLineThomModel
public import AtiyahSinger.Topology.ComplexOrientationClass
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The normalized integral first Chern class of an actual complex line bundle

Public module ID: M1708.

C02: the original complex line fibers determine their positive real orientation.
The unique integral Thom class is normalized on every original fiber by every
complex-linear coordinate. Its image in ordinary total-space cohomology is
pulled back by the actual zero section to define the first Chern class.
Neither an arbitrary cohomological orientation nor a proposed Chern class is
an input. The normalized class on the complex plane fixes the sign (1, i).

The total space remains TotalSpace Unit E with its original topology. The
finite-rank condition supplies original local linear charts; the explicit
dimension-one condition makes these genuine line bundles. Auxiliary fiber
norms are used only to express continuous linear coordinates. Finite-dimensional
norm equivalence compares them with the original fiber subspace topology;
they need not vary continuously over the base. ULift preserves arbitrary
universes in the actual relative cohomology pullbacks.

Sources: Milnor--Stasheff, Characteristic Classes, Theorem 9.1 (p.97),
Theorem 10.4 (p.110), Property 9.7 (p.101), Lemma 14.1 (p.155), the definition
of Chern classes (p.158), and Lemma 14.2 (p.158). These give the normalized integral Thom
class, positive complex orientation, c_1(L)=e(L_R), and naturality.
Hatcher, Algebraic Topology, Theorem 4D.10, supplies the integral Thom-class
existence argument, including its CW-approximation reduction. No smoothness,
compactness or chosen metric on the base is assumed. Continuity of the original
fiber map, normalized Thom class and Chern properties are proved using those
original charts and the actual relative cohomology functors.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : ComplexBundle.IsFiniteRank E]

include hE in
/-- A complex coordinate gives a continuous map into the original fiber in the total space.
This is an implementation certificate for the actual map used in the Thom normalization. -/
theorem continuous_complexLineFiberMap (x : X) (e : E x ≃L[ℂ] ℂ) :
    Continuous (fun z : ULift.{u} ℂ ↦ (⟨x, e.symm z.down⟩ : TotalSpace Unit E)) := by
  /- Stage 1: choose an original finite linear bundle chart around x. Its
  inverse maps (x,w) continuously to the original total space. In this chart
  the displayed map is the chart inverse composed with the fixed base x and
  a linear map from C into its finite-dimensional coordinate space.
  Stage 2: that coordinate linear map is continuous by finite dimension.
  Its chart inverse has precisely the original value e.symm z.down. Compose
  with the continuous ULift projection. This proves continuity for the given
  total topology; no continuity of the auxiliary norms over X is required. -/
  obtain ⟨r, c, hx, hlinear⟩ :=
    ComplexBundle.IsFiniteRank.exists_linear_trivialization (E := E) x
  let := ComplexBundle.finite_fiber (E := E) x
  let L : E x →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun v ↦ (c ⟨x, v⟩).2
      map_add' := (hlinear x hx).map_add
      map_smul' := (hlinear x hx).map_smul }
  -- The specified fiber coordinate is continuous in its finite-dimensional original norms.
  have hcoords : Continuous (fun z : ULift.{u} ℂ ↦ (x, L (e.symm z.down))) :=
    continuous_const.prodMk (L.continuous_of_finiteDimensional.comp
      (e.symm.continuous.comp continuous_uliftDown))
  have htotal := c.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous hcoords
    (fun _ ↦ c.mem_target.mpr hx)
  -- The inverse chart returns exactly the original vector, in the original total topology.
  apply htotal.congr
  intro z
  have hsource : (⟨x, e.symm z.down⟩ : TotalSpace Unit E) ∈ c.source := c.mem_source.mpr hx
  have heq : (x, L (e.symm z.down)) = c ⟨x, e.symm z.down⟩ := by
    apply Prod.ext
    · exact (c.proj_toFun ⟨x, e.symm z.down⟩ hsource).symm
    · rfl
  change c.toOpenPartialHomeomorph.symm (x, L (e.symm z.down)) = ⟨x, e.symm z.down⟩
  rw [heq]
  exact c.left_inv hsource

/-- Include the positively coordinated complex plane into an original line fiber. -/
def complexLineFiberMap (x : X) (e : E x ≃L[ℂ] ℂ) :
    C(ULift.{u} ℂ, TotalSpace Unit E) :=
  ⟨fun z ↦ ⟨x, e.symm z.down⟩, continuous_complexLineFiberMap E x e⟩

variable (hline : ∀ x : X, Module.finrank ℂ (E x) = 1)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hline in
/-- Every complex line bundle has a unique Thom class with the positive complex normalization. -/
theorem existsUnique_complexLineThomClass :
    ∃! U : relativeSingularCohomology ℤ {z : TotalSpace Unit E | z.snd ≠ 0} 2,
      ∀ (x : X) (e : E x ≃L[ℂ] ℂ),
        relativeSingularCohomologyPullback ℤ (complexLineFiberMap E x e)
          (A := {z : ULift.{u} ℂ | z ≠ 0})
          (B := {z : TotalSpace Unit E | z.snd ≠ 0})
          (by
            intro z hz hzero
            apply hz
            apply ULift.ext
            change e.symm z.down = 0 at hzero
            have hz' : z.down = 0 := e.symm.injective (by simpa using hzero)
            exact hz') 2 U = complexOrientationClass.{u} := by
  /- Use the existing identity-on-vectors topology to expose the real rank-two
  model. Its canonical complex fiber classes extend locally in the original
  complex charts, with no global metric. The already proved relative Thom
  theorem supplies the unique class. Transport through the same total-space
  homeomorphism and check each original complex coordinate explicitly. -/
  classical
  let F := EuclideanSpace ℝ (Fin 2)
  let := ComplexBundle.nativeModelTopology E F
  obtain ⟨b, v⟩ := ComplexBundle.exists_realNativeFiberBundle_of_normedFibers E 1 hline
  let := b
  let := v
  obtain ⟨o, ho⟩ := ComplexBundle.exists_complexLineCohomologyOrientation E hline
  let H := ComplexBundle.nativeModelTotalHomeomorph E F
  let f : C(TotalSpace F E, TotalSpace Unit E) := ⟨H, H.continuous⟩
  let g : C(TotalSpace Unit E, TotalSpace F E) := ⟨H.symm, H.symm.continuous⟩
  let A := bundleNonzero 2 E
  let B : Set (TotalSpace Unit E) := {z | z.snd ≠ 0}
  have hf : Set.MapsTo f A B := fun _ hz ↦ hz
  have hg : Set.MapsTo g B A := fun _ hz ↦ hz
  let := isIso_relativeSingularCohomologyPullback_of_inverse ℤ f g hf hg
    (by rfl) (by rfl) 2
  let T := cohomologyThomClass ℤ 2 E o
  have hT (x : X) : relativeSingularCohomologyPullback ℤ (bundleFiberInclusion 2 E x)
      (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) 2 T = o.fiberClass x :=
    (existsUnique_cohomologyThomClass ℤ 2 E o).exists.choose_spec x
  let I := asIso (relativeSingularCohomologyPullback ℤ f hf 2)
  refine ⟨I.inv T, ?_, ?_⟩
  · intro x e
    let d : E x ≃L[ℂ] ULift.{u} ℂ := e.trans ContinuousLinearEquiv.ulift.symm
    let j : C(ULift.{u} ℂ, E x) := ⟨d.symm, d.symm.continuous⟩
    have hj : Set.MapsTo j {z : ULift.{u} ℂ | z ≠ 0} {v : E x | v ≠ 0} :=
      fun _ hz hv ↦ hz (d.symm.injective (hv.trans d.symm.map_zero.symm))
    have hcomp : (f.comp (bundleFiberInclusion 2 E x)).comp j =
        complexLineFiberMap E x e := rfl
    let i := bundleFiberInclusion 2 E x
    have hi : Set.MapsTo i {v : E x | v ≠ 0} A := fun _ hv ↦ hv
    have hfirst := relativeSingularCohomologyPullback_comp ℤ i f hi hf 2
    have hsecond := relativeSingularCohomologyPullback_comp ℤ j (f.comp i)
      hj (hf.comp hi) 2
    have hmap : relativeSingularCohomologyPullback ℤ (complexLineFiberMap E x e)
        ((hf.comp hi).comp hj) 2 =
        relativeSingularCohomologyPullback ℤ f hf 2 ≫
          relativeSingularCohomologyPullback ℤ i hi 2 ≫
            relativeSingularCohomologyPullback ℤ j hj 2 := by
      rw [hfirst, Category.assoc] at hsecond
      dsimp only [i] at hsecond
      simpa only [hcomp] using hsecond
    rw [hmap]
    change relativeSingularCohomologyPullback ℤ j hj 2
      (relativeSingularCohomologyPullback ℤ (bundleFiberInclusion 2 E x)
        (A := {v : E x | v ≠ 0}) (B := A)
        (fun _ hv ↦ hv) 2 (I.hom (I.inv T))) = _
    rw [CategoryTheory.Iso.inv_hom_id_apply, hT]
    exact ho x d
  · intro w hw
    apply (ConcreteCategory.bijective_of_isIso
      (relativeSingularCohomologyPullback ℤ f hf 2)).injective
    change I.hom w = I.hom (I.inv T)
    rw [CategoryTheory.Iso.inv_hom_id_apply]
    apply (existsUnique_cohomologyThomClass ℤ 2 E o).unique
    · intro x
      let := ComplexBundle.finite_fiber (E := E) x
      let e : E x ≃L[ℂ] ℂ :=
        (LinearEquiv.ofFinrankEq (E x) ℂ (by simpa using hline x)).toContinuousLinearEquiv
      let d : E x ≃L[ℂ] ULift.{u} ℂ := e.trans ContinuousLinearEquiv.ulift.symm
      let j : C(ULift.{u} ℂ, E x) := ⟨d.symm, d.symm.continuous⟩
      let k : C(E x, ULift.{u} ℂ) := ⟨d, d.continuous⟩
      have hj : Set.MapsTo j {z : ULift.{u} ℂ | z ≠ 0} {v : E x | v ≠ 0} :=
        fun _ hz hv ↦ hz (d.symm.injective (hv.trans d.symm.map_zero.symm))
      have hk : Set.MapsTo k {v : E x | v ≠ 0} {z : ULift.{u} ℂ | z ≠ 0} :=
        fun _ hv hz ↦ hv (d.injective (hz.trans d.map_zero.symm))
      let := isIso_relativeSingularCohomologyPullback_of_inverse ℤ j k hj hk
        (by apply ContinuousMap.ext; intro z; exact d.apply_symm_apply z)
        (by apply ContinuousMap.ext; intro z; exact d.symm_apply_apply z) 2
      apply (ConcreteCategory.bijective_of_isIso
        (relativeSingularCohomologyPullback ℤ j hj 2)).injective
      have h := hw x e
      have hcomp : (f.comp (bundleFiberInclusion 2 E x)).comp j =
          complexLineFiberMap E x e := rfl
      let i := bundleFiberInclusion 2 E x
      have hi : Set.MapsTo i {v : E x | v ≠ 0} A := fun _ hv ↦ hv
      have hfirst := relativeSingularCohomologyPullback_comp ℤ i f hi hf 2
      have hsecond := relativeSingularCohomologyPullback_comp ℤ j (f.comp i)
        hj (hf.comp hi) 2
      have hmap : relativeSingularCohomologyPullback ℤ (complexLineFiberMap E x e)
        ((hf.comp hi).comp hj) 2 =
          relativeSingularCohomologyPullback ℤ f hf 2 ≫
            relativeSingularCohomologyPullback ℤ i hi 2 ≫
              relativeSingularCohomologyPullback ℤ j hj 2 := by
        rw [hfirst, Category.assoc] at hsecond
        dsimp only [i] at hsecond
        simpa only [hcomp] using hsecond
      rw [hmap] at h
      exact h.trans (ho x d).symm
    · exact hT

/-- The integral Thom class selected solely by its original complex fiber normalization. -/
def complexLineThomClass :
    relativeSingularCohomology ℤ {z : TotalSpace Unit E | z.snd ≠ 0} 2 :=
  (existsUnique_complexLineThomClass E hline).exists.choose

/-- The chosen class restricts to the same positive generator in every complex fiber coordinate. -/
theorem complexLineThomClass_fiber (x : X) (e : E x ≃L[ℂ] ℂ) :
    relativeSingularCohomologyPullback ℤ (complexLineFiberMap E x e)
      (A := {z : ULift.{u} ℂ | z ≠ 0})
      (B := {z : TotalSpace Unit E | z.snd ≠ 0})
      (by
        intro z hz hzero
        apply hz
        apply ULift.ext
        change e.symm z.down = 0 at hzero
        have hz' : z.down = 0 := e.symm.injective (by simpa using hzero)
        exact hz') 2 (complexLineThomClass E hline) = complexOrientationClass.{u} := by
  /- Use the specification of the exact witness selected by
  existsUnique_complexLineThomClass. It retains the original fiber, the
  supplied complex coordinate and the fixed positive integral generator. -/
  exact (existsUnique_complexLineThomClass E hline).exists.choose_spec x e

/-- The first Chern class is the Euler class of the positively oriented underlying real plane. -/
def firstChernClass : singularCohomology ℤ X 2 :=
  singularCohomologyPullback ℤ
    ⟨fun x ↦ (⟨x, 0⟩ : TotalSpace Unit E), ComplexBundle.continuous_zero_section E⟩ 2
    (relativeSingularCohomologyToOrdinary ℤ {z : TotalSpace Unit E | z.snd ≠ 0} 2
      (complexLineThomClass E hline))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The first Chern class is preserved by an actual complex-linear bundle isomorphism. -/
theorem firstChernClass_eq_of_iso
    {F : X → Type u} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [ComplexBundle.IsFiniteRank F]
    (hF : ∀ x : X, Module.finrank ℂ (F x) = 1) (e : ComplexBundle.Iso E F) :
    firstChernClass E hline = firstChernClass F hF := by
  /- Pull back the target Thom class along the actual total-space isomorphism.
  Every source complex coordinate becomes a target complex coordinate through
  its inverse fiber map, so uniqueness identifies the class. The same map
  commutes with zero sections; relative-to-ordinary naturality finishes. -/
  let f : C(TotalSpace Unit E, TotalSpace Unit F) :=
    ⟨e.totalHomeomorph, e.totalHomeomorph.continuous⟩
  let A : Set (TotalSpace Unit E) := {z | z.snd ≠ 0}
  let B : Set (TotalSpace Unit F) := {z | z.snd ≠ 0}
  have hf : Set.MapsTo f A B := by
    intro z hz hzero
    exact hz ((e.linearEquiv z.proj).injective
      (hzero.trans (e.linearEquiv z.proj).map_zero.symm))
  have hthom : relativeSingularCohomologyPullback ℤ f hf 2
      (complexLineThomClass F hF) = complexLineThomClass E hline := by
    apply (existsUnique_complexLineThomClass E hline).unique
    · intro x c
      let := ComplexBundle.finite_fiber (E := E) x
      let := ComplexBundle.finite_fiber (E := F) x
      let d : F x ≃L[ℂ] ℂ :=
        ((e.linearEquiv x).symm.trans c.toLinearEquiv).toContinuousLinearEquiv
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      exact complexLineThomClass_fiber F hF x d
    · exact (existsUnique_complexLineThomClass E hline).exists.choose_spec
  let zE : C(X, TotalSpace Unit E) :=
    ⟨fun x ↦ ⟨x, 0⟩, ComplexBundle.continuous_zero_section E⟩
  let zF : C(X, TotalSpace Unit F) :=
    ⟨fun x ↦ ⟨x, 0⟩, ComplexBundle.continuous_zero_section F⟩
  have hz : f.comp zE = zF := by
    apply ContinuousMap.ext
    intro x
    exact congrArg (TotalSpace.mk x) (e.linearEquiv x).map_zero
  have hsq : singularCohomologyPullback ℤ f 2 ≫ singularCohomologyPullback ℤ zE 2 =
      singularCohomologyPullback ℤ zF 2 := by
    let C := singularCohomologyFunctor ℤ 2
    change C.map (TopCat.ofHom f).op ≫ C.map (TopCat.ofHom zE).op = _
    rw [← C.map_comp, ← op_comp]
    change singularCohomologyPullback ℤ (f.comp zE) 2 = _
    rw [hz]
  change singularCohomologyPullback ℤ zE 2
    (relativeSingularCohomologyToOrdinary ℤ A 2 (complexLineThomClass E hline)) = _
  rw [← hthom]
  change (relativeSingularCohomologyPullback ℤ f hf 2 ≫
    relativeSingularCohomologyToOrdinary ℤ A 2 ≫ singularCohomologyPullback ℤ zE 2)
      (complexLineThomClass F hF) = _
  rw [← Category.assoc, relativeSingularCohomologyPullback_toOrdinary, Category.assoc, hsq]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullback preserves the first Chern class with the original fibers and pullback topology. -/
theorem firstChernClass_pullback {Y : Type u} [TopologicalSpace Y] (f : C(Y, X)) :
    letI : ∀ y : Y, NormedAddCommGroup (((f : Y → X) *ᵖ E) y) :=
      fun y ↦ inferInstanceAs (NormedAddCommGroup (E (f y)))
    letI : ∀ y : Y, NormedSpace ℂ (((f : Y → X) *ᵖ E) y) :=
      fun y ↦ inferInstanceAs (NormedSpace ℂ (E (f y)))
    letI := ComplexBundle.isFiniteRank_pullback (E := E) f
    firstChernClass ((f : Y → X) *ᵖ E) (fun y ↦ hline (f y)) =
      singularCohomologyPullback ℤ f 2 (firstChernClass E hline) := by
  /- The native pullback lift preserves the original nonzero fibers. Its Thom
  pullback has exactly the normalization at f(y), and hence is the selected
  source Thom class. The lift/zero-section square then gives the Chern equality. -/
  let : ∀ y : Y, NormedAddCommGroup (((f : Y → X) *ᵖ E) y) :=
    fun y ↦ inferInstanceAs (NormedAddCommGroup (E (f y)))
  let : ∀ y : Y, NormedSpace ℂ (((f : Y → X) *ᵖ E) y) :=
    fun y ↦ inferInstanceAs (NormedSpace ℂ (E (f y)))
  let := ComplexBundle.isFiniteRank_pullback (E := E) f
  let F := (f : Y → X) *ᵖ E
  let hF : ∀ y : Y, Module.finrank ℂ (F y) = 1 := fun y ↦ hline (f y)
  let g : C(TotalSpace Unit F, TotalSpace Unit E) :=
    ⟨Bundle.Pullback.lift f, _root_.Pullback.continuous_lift Unit E f⟩
  let A : Set (TotalSpace Unit F) := {z | z.snd ≠ 0}
  let B : Set (TotalSpace Unit E) := {z | z.snd ≠ 0}
  have hg : Set.MapsTo g A B := fun _ hz ↦ hz
  have hthom : relativeSingularCohomologyPullback ℤ g hg 2
      (complexLineThomClass E hline) = complexLineThomClass F hF := by
    apply (existsUnique_complexLineThomClass F hF).unique
    · intro y c
      rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
      exact complexLineThomClass_fiber E hline (f y) c
    · exact (existsUnique_complexLineThomClass F hF).exists.choose_spec
  let zE : C(X, TotalSpace Unit E) :=
    ⟨fun x ↦ ⟨x, 0⟩, ComplexBundle.continuous_zero_section E⟩
  let zF : C(Y, TotalSpace Unit F) :=
    ⟨fun y ↦ ⟨y, 0⟩, ComplexBundle.continuous_zero_section F⟩
  have hsq : singularCohomologyPullback ℤ g 2 ≫ singularCohomologyPullback ℤ zF 2 =
      singularCohomologyPullback ℤ zE 2 ≫ singularCohomologyPullback ℤ f 2 := by
    let C := singularCohomologyFunctor ℤ 2
    change C.map (TopCat.ofHom g).op ≫ C.map (TopCat.ofHom zF).op =
      C.map (TopCat.ofHom zE).op ≫ C.map (TopCat.ofHom f).op
    rw [← C.map_comp, ← C.map_comp, ← op_comp, ← op_comp]
    rfl
  change singularCohomologyPullback ℤ zF 2
    (relativeSingularCohomologyToOrdinary ℤ A 2 (complexLineThomClass F hF)) = _
  rw [← hthom]
  change (relativeSingularCohomologyPullback ℤ g hg 2 ≫
    relativeSingularCohomologyToOrdinary ℤ A 2 ≫ singularCohomologyPullback ℤ zF 2)
      (complexLineThomClass E hline) = _
  rw [← Category.assoc, relativeSingularCohomologyPullback_toOrdinary, Category.assoc, hsq]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A nowhere-vanishing continuous section forces the integral first Chern class to vanish. -/
theorem firstChernClass_eq_zero_of_nonvanishing_section (s : ∀ x : X, E x)
    (hs : Continuous (fun x ↦ (⟨x, s x⟩ : TotalSpace Unit E)))
    (hne : ∀ x : X, s x ≠ 0) : firstChernClass E hline = 0 := by
  /- The section factors through the original nonzero subspace, so its
  pullback kills the ordinary image of every relative class. Scalar
  multiplication in the original complex charts gives a homotopy from
  the zero section to this section. Apply that homotopy to the same Thom class. -/
  let A : Set (TotalSpace Unit E) := {z | z.snd ≠ 0}
  let z : C(X, TotalSpace Unit E) :=
    ⟨fun x ↦ ⟨x, 0⟩, ComplexBundle.continuous_zero_section E⟩
  let σ : C(X, TotalSpace Unit E) := ⟨fun x ↦ ⟨x, s x⟩, hs⟩
  let j : C(A, TotalSpace Unit E) := ⟨Subtype.val, continuous_subtype_val⟩
  let q : C(X, A) := ⟨fun x ↦ ⟨⟨x, s x⟩, hne x⟩, hs.subtype_mk _⟩
  have hzero : relativeSingularCohomologyToOrdinary ℤ A 2 ≫
      singularCohomologyPullback ℤ j 2 = 0 := by
    -- The quotient projection after the actual subspace inclusion is zero on chains.
    exact ((singularSubspaceCochainsSequence ℤ A).map
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.up ℕ) 2)).zero
  have hcomp : singularCohomologyPullback ℤ σ 2 =
      singularCohomologyPullback ℤ j 2 ≫ singularCohomologyPullback ℤ q 2 := by
    let C := singularCohomologyFunctor ℤ 2
    change _ = C.map (TopCat.ofHom j).op ≫ C.map (TopCat.ofHom q).op
    rw [← C.map_comp, ← op_comp]
    rfl
  have hsection : singularCohomologyPullback ℤ σ 2
      (relativeSingularCohomologyToOrdinary ℤ A 2 (complexLineThomClass E hline)) = 0 := by
    change (relativeSingularCohomologyToOrdinary ℤ A 2 ≫
      singularCohomologyPullback ℤ σ 2) (complexLineThomClass E hline) = 0
    rw [hcomp, ← Category.assoc, hzero, Limits.zero_comp]
    rfl
  have hcontinuous : Continuous (fun p : unitInterval × X ↦
      (⟨p.2, ((p.1 : ℝ) : ℂ) • s p.2⟩ : TotalSpace Unit E)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨r, t, hp, ht⟩ :=
      ComplexBundle.IsFiniteRank.exists_linear_trivialization (E := E) p.2
    have hσ := (t.toOpenPartialHomeomorph.continuousAt (t.mem_source.mpr hp)).comp
      (hs.continuousAt.comp continuousAt_snd)
    have hscalar : Continuous (fun a : unitInterval × X ↦ ((a.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    apply t.continuousAt_of_comp_left
      (f := fun a : unitInterval × X ↦
        (⟨a.2, ((a.1 : ℝ) : ℂ) • s a.2⟩ : TotalSpace Unit E)) continuousAt_snd hp
    apply (continuousAt_snd.prodMk (hscalar.continuousAt.smul hσ.snd)).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually (t.open_baseSet.mem_nhds hp)] with a ha
    exact Prod.ext (t.proj_toFun _ (t.mem_source.mpr ha))
      ((ht a.2 ha).map_smul ((a.1 : ℝ) : ℂ) (s a.2))
  let H : ContinuousMap.Homotopy z σ :=
    { toFun := fun p ↦ ⟨p.2, ((p.1 : ℝ) : ℂ) • s p.2⟩
      continuous_toFun := hcontinuous
      map_zero_left := by
        intro x
        change (⟨x, ((0 : unitInterval) : ℝ) • s x⟩ : TotalSpace Unit E) = ⟨x, 0⟩
        simp
      map_one_left := by
        intro x
        change (⟨x, ((1 : unitInterval) : ℝ) • s x⟩ : TotalSpace Unit E) = ⟨x, s x⟩
        simp }
  change singularCohomologyPullback ℤ z 2
    (relativeSingularCohomologyToOrdinary ℤ A 2 (complexLineThomClass E hline)) = 0
  rw [singularCohomologyPullback_homotopic ℤ H]
  exact hsection

end AtiyahSinger
