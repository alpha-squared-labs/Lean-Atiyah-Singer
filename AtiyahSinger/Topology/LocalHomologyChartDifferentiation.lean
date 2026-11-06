/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocalHomologyLinearization
public import AtiyahSinger.Topology.LocalOrientationTransport
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Derivatives and the actual local homology of chart transitions

Public module ID: M1939.

Translate the source coordinate to the origin and restrict both charts to their
common domain. Local linearization compares the transition with its derivative;
chart naturality and actual open excision then identify the original transport
maps. No orientation, generator, or derivative sign is assumed.

This is the local degree comparison used in the tangent orientation construction;
see Hatcher, section 3.3, and Milnor--Stasheff, section 9.
-/

@[expose] public noncomputable section
namespace AtiyahSinger
open CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A differentiable chart transition acts on local homology by its invertible derivative. -/
theorem localHomologyChartEquiv_transition_derivative
    {X V W : Type u} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (e : OpenPartialHomeomorph X V) (f : OpenPartialHomeomorph X W)
    (x : X) (he : x ∈ e.source) (hf : x ∈ f.source)
    (L : V ≃L[ℝ] W) (hL : HasFDerivAt (fun v ↦ f (e.symm v))
      L.toContinuousLinearMap (e x)) (k : ℕ) :
    relativeSingularHomologyMap ℤ
      (⟨fun v : V ↦ e x + v, continuous_const.add continuous_id⟩ : C(V, V))
      (A := Set.ofPred (fun v : V ↦ v ≠ 0)) (B := ({e x}ᶜ : Set V))
      (fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero _).symm))) k ≫
        (localHomologyChartEquiv e x he k).toModuleIso.inv ≫
          (localHomologyChartEquiv f x hf k).toModuleIso.hom =
      relativeSingularHomologyMap ℤ (⟨L, L.continuous⟩ : C(V, W))
        (A := Set.ofPred (fun v : V ↦ v ≠ 0)) (B := Set.ofPred (fun w : W ↦ w ≠ 0))
        (fun _ hv h ↦ hv (L.injective (h.trans (map_zero L).symm))) k ≫
          relativeSingularHomologyMap ℤ
            (⟨fun w : W ↦ f x + w, continuous_const.add continuous_id⟩ : C(W, W))
            (A := Set.ofPred (fun w : W ↦ w ≠ 0)) (B := ({f x}ᶜ : Set W))
            (fun _ hw h ↦ hw (add_left_cancel (h.trans (add_zero _).symm))) k := by
  let U : Set V := (fun v ↦ e x + v) ⁻¹' (e.symm.trans f).source
  have hU : IsOpen U := (e.symm.trans f).open_source.preimage
    (continuous_const.add continuous_id)
  have h0 : (0 : V) ∈ U := by
    change e x + 0 ∈ e.target ∧ e.symm (e x + 0) ∈ f.source
    simpa only [add_zero, e.left_inv he] using And.intro (e.map_source he) hf
  let A : Set U := {v | v.val ≠ 0}
  let i : C(U, V) := ⟨Subtype.val, continuous_subtype_val⟩
  have hi : Set.MapsTo i A {v | v ≠ 0} := fun _ hv ↦ hv
  let j : C(U, X) := ⟨fun v ↦ e.symm (e x + v.val),
    e.symm.continuousOn.comp_continuous
      (continuous_const.add continuous_subtype_val) (fun v ↦ v.property.1)⟩
  have hje : ∀ v, j v ∈ e.source := fun v ↦ e.symm.map_source v.property.1
  have hjf : ∀ v, j v ∈ f.source := fun v ↦ v.property.2
  have hj : Set.MapsTo j A ({x}ᶜ : Set X) := by
    intro v hv hz
    have h := congrArg e hz
    change e (e.symm (e x + v.val)) = e x at h
    rw [e.right_inv v.property.1] at h
    exact hv (add_left_cancel (h.trans (add_zero _).symm))
  let ta : C(V, V) := ⟨fun v ↦ e x + v, continuous_const.add continuous_id⟩
  let tb : C(W, W) := ⟨fun w ↦ f x + w, continuous_const.add continuous_id⟩
  have hta : Set.MapsTo ta {v | v ≠ 0} ({e x}ᶜ : Set V) :=
    fun _ hv h ↦ hv (add_left_cancel (h.trans (add_zero _).symm))
  have htb : Set.MapsTo tb {w | w ≠ 0} ({f x}ᶜ : Set W) :=
    fun _ hw h ↦ hw (add_left_cancel (h.trans (add_zero _).symm))
  let l : C(V, W) := ⟨L, L.continuous⟩
  have hl : Set.MapsTo l {v | v ≠ 0} {w | w ≠ 0} :=
    fun _ hv h ↦ hv (L.injective (h.trans (map_zero L).symm))
  let q : V → W := fun v ↦ f (e.symm (e x + v))
  have hq : ContinuousOn q U := (e.symm.trans f).continuousOn.comp
    (continuous_const.add continuous_id).continuousOn (fun _ hv ↦ hv)
  have hq0 : q 0 = f x := by dsimp [q]; rw [add_zero, e.left_inv he]
  have hqin : ∀ v ∈ U, v ≠ 0 → q v ≠ q 0 := by
    intro v hv hv0 h
    have hv' : e x + v = e x + 0 := (e.symm.trans f).injOn hv h0 h
    exact hv0 (add_left_cancel hv')
  have hder : HasFDerivAt q L.toContinuousLinearMap 0 := by
    have hL' : HasFDerivAt (fun v ↦ f (e.symm v)) L.toContinuousLinearMap
        (e x + (0 : V)) := by simpa only [add_zero] using hL
    simpa only [q, Function.comp_def, ContinuousLinearMap.comp_id] using
      hL'.comp 0 ((hasFDerivAt_id (0 : V)).const_add (e x))
  let d : C(U, W) := ⟨fun v ↦ q v.val - q 0, hq.domRestrict.sub continuous_const⟩
  have hd : Set.MapsTo d A {w | w ≠ 0} :=
    fun v hv ↦ sub_ne_zero.mpr (hqin v.val v.property hv)
  let I := relativeSingularHomologyMap ℤ i hi k
  let J := relativeSingularHomologyMap ℤ j hj k
  let Ta := relativeSingularHomologyMap ℤ ta hta k
  let Tb := relativeSingularHomologyMap ℤ tb htb k
  let Lh := relativeSingularHomologyMap ℤ l hl k
  let E := (localHomologyChartEquiv e x he k).toModuleIso
  let F := (localHomologyChartEquiv f x hf k).toModuleIso
  have hcomp {Z₁ Z₂ Z₃ : Type u} [TopologicalSpace Z₁] [TopologicalSpace Z₂]
      [TopologicalSpace Z₃] (a : C(Z₁, Z₂)) (b : C(Z₂, Z₃))
      {S₁ : Set Z₁} {S₂ : Set Z₂} {S₃ : Set Z₃}
      (ha : Set.MapsTo a S₁ S₂) (hb : Set.MapsTo b S₂ S₃) :
      relativeSingularHomologyMap ℤ (b.comp a) (hb.comp ha) k =
        relativeSingularHomologyMap ℤ a ha k ≫ relativeSingularHomologyMap ℤ b hb k := by
    change HomologicalComplex.homologyMap _ k =
      HomologicalComplex.homologyMap _ k ≫ HomologicalComplex.homologyMap _ k
    rw [← HomologicalComplex.homologyMap_comp, relativeSingularChainsMap_comp]
  have hcongr {Z₁ Z₂ : Type u} [TopologicalSpace Z₁] [TopologicalSpace Z₂]
      {a b : C(Z₁, Z₂)} {S₁ : Set Z₁} {S₂ : Set Z₂}
      (ha : Set.MapsTo a S₁ S₂) (hb : Set.MapsTo b S₁ S₂) (h : a = b) :
      relativeSingularHomologyMap ℤ a ha k = relativeSingularHomologyMap ℤ b hb k := by
    subst b
    rfl
  have hE : J ≫ E.hom = I ≫ Ta := by
    rw [show J ≫ E.hom = _ from localHomologyChartEquiv_naturality e x he j hje hj k]
    rw [← hcomp i ta hi hta]
    apply hcongr
    ext v
    exact e.right_inv v.property.1
  have hF : J ≫ F.hom = I ≫ Lh ≫ Tb := by
    have hderh := relativeSingularHomologyMap_eq_derivative ℤ q U hU h0 hq hqin L hder k
    change relativeSingularHomologyMap ℤ d hd k = I ≫ Lh at hderh
    rw [show J ≫ F.hom = _ from localHomologyChartEquiv_naturality f x hf j hjf hj k]
    rw [← Category.assoc, ← hderh, ← hcomp d tb hd htb]
    apply hcongr
    ext v
    change f (e.symm (e x + v.val)) = f x + (q v.val - q 0)
    rw [hq0]
    dsimp [q]
    abel
  -- The source neighborhood can be canceled by the original open-excision isomorphism.
  let : IsIso I := by
    obtain ⟨a, ha⟩ := homotopyEquivalences_relativeSingularChainsMap_openEmbedding ℤ i
      hU.isOpenEmbedding_subtypeVal {0} isClosed_singleton
      (by rintro _ rfl; exact ⟨⟨0, h0⟩, rfl⟩)
    change IsIso (HomologicalComplex.homologyMap (relativeSingularChainsMap ℤ i hi) k)
    erw [← ha]
    exact inferInstanceAs (IsIso (a.toHomologyIso k).hom)
  change Ta ≫ E.inv ≫ F.hom = Lh ≫ Tb
  apply (cancel_epi I).mp
  calc
    I ≫ Ta ≫ E.inv ≫ F.hom = (I ≫ Ta) ≫ E.inv ≫ F.hom := by simp only [Category.assoc]
    _ = (J ≫ E.hom) ≫ E.inv ≫ F.hom := by rw [hE]
    _ = J ≫ F.hom := by simp only [Category.assoc, E.hom_inv_id_assoc]
    _ = I ≫ Lh ≫ Tb := hF

end AtiyahSinger
