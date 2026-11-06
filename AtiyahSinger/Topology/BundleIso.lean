/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleMap
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Continuous bundle isomorphisms

Public module ID: M1577.

D07/K01. Inverse continuity is part of the standard isomorphism structure.
For finite locally trivial bundles it follows separately from fiberwise bijectivity.
The constructions here require no compactness of the base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : X → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]

/-- An isomorphism of continuous complex vector bundles over one base. -/
structure Iso (E F : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)] where
  /-- The linear equivalence on each fiber. -/
  linearEquiv : ∀ x, E x ≃ₗ[ℂ] F x
  /-- Continuity of the forward total-space map. -/
  continuous_total : Continuous (fun z : TotalSpace Unit E ↦
    (⟨z.proj, linearEquiv z.proj z.snd⟩ : TotalSpace Unit F))
  /-- Continuity of the inverse total-space map. -/
  continuous_symm : Continuous (fun z : TotalSpace Unit F ↦
    (⟨z.proj, (linearEquiv z.proj).symm z.snd⟩ : TotalSpace Unit E))

/-- Forget only invertibility of a bundle isomorphism. -/
def Iso.toHom (e : Iso E F) : Hom E F where
  linearMap x := (e.linearEquiv x).toLinearMap
  continuous_total := e.continuous_total

/-- Reverse the fiber equivalences and exchange the continuity certificates. -/
def Iso.symm (e : Iso E F) : Iso F E where
  linearEquiv x := (e.linearEquiv x).symm
  continuous_total := e.continuous_symm
  continuous_symm := e.continuous_total

/-- Identity isomorphism of a continuous bundle. -/
def Iso.refl (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] : Iso E E where
  linearEquiv x := LinearEquiv.refl ℂ (E x)
  continuous_total := continuous_id
  continuous_symm := continuous_id

/-- Composition of bundle isomorphisms, first e and then f. -/
def Iso.trans (e : Iso E F) (f : Iso F G) : Iso E G where
  linearEquiv x := (e.linearEquiv x).trans (f.linearEquiv x)
  continuous_total := f.continuous_total.comp e.continuous_total
  continuous_symm := e.continuous_symm.comp f.continuous_symm

set_option linter.unusedSectionVars false in
/-- Isomorphisms are determined by their forward fiber maps. -/
@[ext]
theorem Iso.ext (e f : Iso E F)
    (h : ∀ x, e.linearEquiv x = f.linearEquiv x) : e = f := by
  /- The forward linear equivalences agree by function extensionality. All other
  fields assert continuity and agree by proof irrelevance, giving equality of structures. -/
  cases e
  cases f
  congr
  exact funext h

set_option linter.unusedSectionVars false in
/-- The inverse followed by the forward fiber equivalence is identity. -/
theorem Iso.apply_symm_apply (e : Iso E F) (x : X) (v : F x) :
    e.linearEquiv x ((e.linearEquiv x).symm v) = v := by
  /- Apply the inverse law of the linear equivalence e at x. Both operations stay
  in the fibers over x, so no base change or local trivialization is needed. -/
  exact (e.linearEquiv x).apply_symm_apply v

set_option linter.unusedSectionVars false in
/-- The forward followed by the inverse fiber equivalence is identity. -/
theorem Iso.symm_apply_apply (e : Iso E F) (x : X) (v : E x) :
    (e.linearEquiv x).symm (e.linearEquiv x v) = v := by
  /- Use the other inverse law of the linear equivalence at x. This is a fiberwise
  algebraic assertion, independent of finite rank or topological assumptions on X. -/
  exact (e.linearEquiv x).symm_apply_apply v

/-- The induced homeomorphism retains the original total spaces and their topologies. -/
def Iso.totalHomeomorph (e : Iso E F) : TotalSpace Unit E ≃ₜ TotalSpace Unit F where
  toFun := e.toHom.totalMap
  invFun := e.symm.toHom.totalMap
  left_inv z := congrArg (TotalSpace.mk z.proj)
    ((e.linearEquiv z.proj).symm_apply_apply z.snd)
  right_inv z := congrArg (TotalSpace.mk z.proj)
    ((e.linearEquiv z.proj).apply_symm_apply z.snd)
  continuous_toFun := e.continuous_total
  continuous_invFun := e.continuous_symm

/-- Finite local rank is preserved under actual bundle isomorphism. -/
theorem Iso.isFiniteRank (e : Iso E F) [IsFiniteRank E] : IsFiniteRank F := by
  /- Compose local linear charts of E with the continuous inverse total map of e.
  The chart inverses compose with the forward map. The same open base sets and finite
  dimensions then furnish local linear trivializations of F. -/
  constructor
  intro x
  obtain ⟨r, t, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
  -- Precompose the same chart with the actual inverse homeomorphism of total spaces.
  let t' : Trivialization (Fin r → ℂ) (π Unit F) :=
    t.compHomeomorph e.totalHomeomorph.symm
  refine ⟨r, t', hx, ?_⟩
  intro y hy
  constructor
  · intro v w
    change (t ⟨y, (e.linearEquiv y).symm (v + w)⟩).2 = _
    rw [map_add]
    exact (hlinear y hy).map_add _ _
  · intro a v
    change (t ⟨y, (e.linearEquiv y).symm (a • v)⟩).2 = _
    rw [map_smul]
    exact (hlinear y hy).map_smul a _

attribute [local instance] sectionModule

variable [hE : IsFiniteRank E] [hF : IsFiniteRank F]

/-- The induced section map of an isomorphism is bijective. -/
theorem Iso.sectionMap_bijective (e : Iso E F) : Function.Bijective e.toHom.sectionMap := by
  /- The section map induced by the inverse bundle isomorphism is a two-sided inverse.
  Evaluate the composites on arbitrary sections and use the two fiber inverse laws. -/
  -- The original inverse bundle map acts pointwise as the inverse on every section.
  have hleft : Function.LeftInverse e.symm.toHom.sectionMap e.toHom.sectionMap := by
    intro s
    apply Subtype.ext
    funext x
    exact (e.linearEquiv x).symm_apply_apply (s.val x)
  have hright : Function.RightInverse e.symm.toHom.sectionMap e.toHom.sectionMap := by
    intro s
    apply Subtype.ext
    funext x
    exact (e.linearEquiv x).apply_symm_apply (s.val x)
  exact ⟨hleft.injective, hright.surjective⟩

/-- The actual section-module equivalence induced by a bundle isomorphism. -/
def Iso.sectionLinearEquiv (e : Iso E F) :
    continuousSections E ≃ₗ[C(X, ℂ)] continuousSections F :=
  LinearEquiv.ofBijective e.toHom.sectionMap e.sectionMap_bijective

/-- The section equivalence is characterized by its original fiber action. -/
theorem Iso.sectionLinearEquiv_apply (e : Iso E F) (s : continuousSections E) (x : X) :
    (e.sectionLinearEquiv s).val x = e.linearEquiv x (s.val x) := by
  /- The equivalence was made from the actual section map by a bijectivity certificate.
  Its forward function is unchanged; apply the section map evaluation formula. -/
  rfl

include hE hF

/-- A bijective finite-rank bundle map has continuous pointwise inverse. -/
theorem Hom.continuous_inverse (f : Hom E F)
    (h : ∀ x, Function.Bijective (f.linearMap x)) :
    Continuous (fun z : TotalSpace Unit F ↦
      (⟨z.proj, (LinearEquiv.ofBijective (f.linearMap z.proj) (h z.proj)).symm z.snd⟩ :
        TotalSpace Unit E)) := by
  /- Near each point choose finite linear trivializations of both bundles. The original
  fiberwise bijection gives linear equivalences between their finite coordinate spaces.
  The coordinate operators vary continuously, and inversion is continuous on their
  invertible locus. Transport back through the same charts and use locality of
  continuity on the original total space. No identification of coordinate types is needed. -/
  classical
  apply continuous_iff_continuousAt.mpr
  intro z₀
  obtain ⟨r, e, he, hlinearE⟩ :=
    IsFiniteRank.exists_linear_trivialization (E := E) z₀.proj
  obtain ⟨s, d, hd, hlinearF⟩ :=
    IsFiniteRank.exists_linear_trivialization (E := F) z₀.proj
  -- Stage 1: keep the original chart maps and their actual inverse fiber vectors.
  let eLin (y : X) (hy : y ∈ e.baseSet) : E y ≃ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun v ↦ (e ⟨y, v⟩).2
      invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' hy))
        (e.toOpenPartialHomeomorph.symm (y, v)).snd
      left_inv := by
        intro v
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
          (e.symm_apply_mk_proj (x := ⟨y, v⟩) (e.mem_source.mpr hy))
      right_inv := by
        intro v
        have hp := TotalSpace.mk_cast (F := Unit) (E := E)
          (e.proj_symm_apply' (x := v) hy) (e.toOpenPartialHomeomorph.symm (y, v)).snd
        exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hp).trans
          (congrArg Prod.snd (e.apply_symm_apply' hy))
      map_add' := (hlinearE y hy).map_add
      map_smul' := (hlinearE y hy).map_smul }
  let dLin (y : X) (hy : y ∈ d.baseSet) : F y ≃ₗ[ℂ] (Fin s → ℂ) :=
    { toFun := fun v ↦ (d ⟨y, v⟩).2
      invFun := fun v ↦ cast (congrArg F (d.proj_symm_apply' hy))
        (d.toOpenPartialHomeomorph.symm (y, v)).snd
      left_inv := by
        intro v
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun z : TotalSpace Unit F ↦ z.snd)
          (d.symm_apply_mk_proj (x := ⟨y, v⟩) (d.mem_source.mpr hy))
      right_inv := by
        intro v
        have hp := TotalSpace.mk_cast (F := Unit) (E := F)
          (d.proj_symm_apply' (x := v) hy) (d.toOpenPartialHomeomorph.symm (y, v)).snd
        exact (congrArg (fun z : TotalSpace Unit F ↦ (d z).2) hp).trans
          (congrArg Prod.snd (d.apply_symm_apply' hy))
      map_add' := (hlinearF y hy).map_add
      map_smul' := (hlinearF y hy).map_smul }
  have hpointE (y : X) (hy : y ∈ e.baseSet) (v : Fin r → ℂ) :
      (⟨y, (eLin y hy).symm v⟩ : TotalSpace Unit E) = e.toOpenPartialHomeomorph.symm (y, v) :=
    TotalSpace.mk_cast (F := Unit) (E := E) (e.proj_symm_apply' hy) _
  let U : Set X := e.baseSet ∩ d.baseSet
  let A (y : U) : (Fin r → ℂ) ≃L[ℂ] (Fin s → ℂ) :=
    (((eLin y.val y.property.1).symm.trans
      (LinearEquiv.ofBijective (f.linearMap y.val) (h y.val))).trans
        (dLin y.val y.property.2)).toContinuousLinearEquiv
  -- Stage 2: the original total map gives continuity on each fixed coordinate vector.
  have hA : Continuous (fun y : U ↦ (A y : (Fin r → ℂ) →L[ℂ] (Fin s → ℂ))) := by
    apply continuous_clm_apply.mpr
    intro v
    have heinv : Continuous (fun y : U ↦
        (⟨y.val, (eLin y.val y.property.1).symm v⟩ : TotalSpace Unit E)) := by
      have hc := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
        (continuous_subtype_val.prodMk (continuous_const (y := v)))
        (fun y : U ↦ e.mem_target.mpr y.property.1)
      apply hc.congr
      intro y
      exact (hpointE y.val y.property.1 v).symm
    have hf : Continuous (fun y : U ↦
        (⟨y.val, f.linearMap y.val ((eLin y.val y.property.1).symm v)⟩ :
          TotalSpace Unit F)) := f.continuous_total.comp heinv
    exact continuous_snd.comp
      (d.toOpenPartialHomeomorph.continuousOn.comp_continuous hf
        (fun y : U ↦ d.mem_source.mpr y.property.2))
  -- Inversion on the invertible operator locus is continuous, including rank zero.
  have hB : Continuous (fun y : U ↦ ((A y).symm : (Fin s → ℂ) →L[ℂ] (Fin r → ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hAy : ContinuousAt
        (fun y : U ↦ (A y : (Fin r → ℂ) →L[ℂ] (Fin s → ℂ))) y := hA.continuousAt
    have hi : ContinuousAt (fun y : U ↦
        ContinuousLinearMap.inverse (A y : (Fin r → ℂ) →L[ℂ] (Fin s → ℂ))) y :=
      (contDiffAt_map_inverse (n := 0) (A y)).continuousAt.comp_of_eq hAy rfl
    simpa only [ContinuousLinearMap.inverse_equiv] using hi
  -- Stage 3: transfer the inverse family through these same charts on their open overlap.
  let W : Set (TotalSpace Unit F) := π Unit F ⁻¹' U
  have hW : IsOpen W := (e.open_baseSet.inter d.open_baseSet).preimage
    (continuous_proj (E := F))
  have hinv : ContinuousOn (fun z : TotalSpace Unit F ↦
      (⟨z.proj, (LinearEquiv.ofBijective (f.linearMap z.proj) (h z.proj)).symm z.snd⟩ :
        TotalSpace Unit E)) W := by
    rw [continuousOn_iff_continuous_domRestrict]
    let base : W → U := fun z ↦ ⟨z.val.proj, z.property⟩
    have hbase : Continuous base :=
      ((continuous_proj (E := F)).comp continuous_subtype_val).subtype_mk _
    have hcoords : Continuous (fun z : W ↦ (d z.val).2) :=
      continuous_snd.comp (d.toOpenPartialHomeomorph.continuousOn.comp_continuous
        continuous_subtype_val (fun z : W ↦ d.mem_source.mpr z.property.2))
    have hvalues : Continuous (fun z : W ↦ (A (base z)).symm (d z.val).2) :=
      (hB.comp hbase).clm_apply hcoords
    have hc := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (((continuous_proj (E := F)).comp continuous_subtype_val).prodMk hvalues)
      (fun z : W ↦ e.mem_target.mpr z.property.1)
    apply hc.congr
    intro z
    have hinverse : (A (base z)).symm (d z.val).2 =
        eLin z.val.proj z.property.1
          ((LinearEquiv.ofBijective (f.linearMap z.val.proj) (h z.val.proj)).symm z.val.snd) := by
      apply (A (base z)).injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change (d z.val).2 = dLin z.val.proj z.property.2
        ((LinearEquiv.ofBijective (f.linearMap z.val.proj) (h z.val.proj))
          ((eLin z.val.proj z.property.1).symm
            (eLin z.val.proj z.property.1
              ((LinearEquiv.ofBijective (f.linearMap z.val.proj) (h z.val.proj)).symm
                z.val.snd))))
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
      rfl
    change e.toOpenPartialHomeomorph.symm (z.val.proj, (A (base z)).symm (d z.val).2) = _
    rw [hinverse, ← hpointE z.val.proj z.property.1, LinearEquiv.symm_apply_apply]
    rfl
  exact hinv.continuousAt (hW.mem_nhds ⟨he, hd⟩)

/-- A fiberwise bijective continuous map, with inverse continuity proved separately. -/
def Hom.toIso (f : Hom E F) (h : ∀ x, Function.Bijective (f.linearMap x)) : Iso E F where
  linearEquiv x := LinearEquiv.ofBijective (f.linearMap x) (h x)
  continuous_total := f.continuous_total
  continuous_symm := f.continuous_inverse h

/-- Conversion to an isomorphism retains the original bundle map. -/
theorem Hom.toIso_toHom (f : Hom E F) (h : ∀ x, Function.Bijective (f.linearMap x)) :
    (f.toIso h).toHom = f := by
  /- The conversion uses ofBijective on each fiber, whose forward linear map is f.
  Apply bundle-map extensionality; its continuity certificate has no effect on equality. -/
  apply Hom.ext
  intro x
  rfl

end AtiyahSinger.ComplexBundle
