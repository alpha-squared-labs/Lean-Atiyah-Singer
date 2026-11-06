/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleOrientationChartSign
public import AtiyahSinger.Topology.FiberBundleTopology
public import AtiyahSinger.Topology.HomologicalOrientationChartSign
public import AtiyahSinger.Topology.LocalHomologyProductOrientation

/-!
# Local homology transport between original vector-bundle charts

Public module ID: M1110.

The same native inverse trivialization parametrizes a common open neighborhood.
The two actual chart maps then have coordinates `(c(x), v)` and `(d(x), A(x)v)`.
The proved product calculation identifies their local homology maps using the
base signs and the evaluations of the same prescribed fiber class. Open
excision cancels precisely this common source map.

This is the local orientation calculation from Hatcher, section 3.3, and
Milnor--Stasheff, section 9. The base is only topological; no derivative or
total-space orientation is supplied as an assumption.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory HomologicalComplex Topology

variable (n r : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
  (E : M → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin r)
local notation "W" => EuclideanSpace ℝ (Fin (n + r))
local notation "TE" => TotalSpace F E

attribute [local instance] t2Space_fiberBundleTotal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual local homology maps of two native charts differ by their base and fiber signs. -/
theorem localHomologyChartEquiv_bundle_eq_sign_smul
    (O : HomologicalOrientation n M) (o : CohomologyOrientation ℤ r E)
    (c d : OpenPartialHomeomorph M V)
    (t t' : Trivialization F (π F E)) [MemTrivializationAtlas t] [MemTrivializationAtlas t']
    (g : (V × F) ≃L[ℝ] W) (z : TE)
    (hc : z.proj ∈ c.source) (hd : z.proj ∈ d.source)
    (ht : z.proj ∈ t.baseSet) (ht' : z.proj ∈ t'.baseSet) :
    let C := (t.toOpenPartialHomeomorph.trans (c.prod (OpenPartialHomeomorph.refl F))).trans
      g.toHomeomorph.toOpenPartialHomeomorph
    let D := (t'.toOpenPartialHomeomorph.trans (d.prod (OpenPartialHomeomorph.refl F))).trans
      g.toHomeomorph.toOpenPartialHomeomorph
    ∀ (hC : z ∈ C.source) (hD : z ∈ D.source),
      (localHomologyChartEquiv D z hD (n + r)).toModuleIso.hom =
        ((homologicalOrientationChartSign O d z.proj hd *
          homologicalOrientationChartSign O c z.proj hc) *
          (bundleFiberChartSign r E o t z.proj ht *
            bundleFiberChartSign r E o t' z.proj ht')) •
          ((localHomologyChartEquiv C z hC (n + r)).toModuleIso.hom ≫
            relativeSingularHomologyMap ℤ
              (⟨fun w : W ↦ D z + (w - C z),
                continuous_const.add (continuous_id.sub continuous_const)⟩ : C(W, W))
              (A := ({C z}ᶜ : Set W)) (B := ({D z}ᶜ : Set W))
              (fun _ hw heq ↦ hw (sub_eq_zero.mp
                (add_left_cancel (heq.trans (add_zero _).symm)))) (n + r)) := by
  dsimp only
  intro hC hD
  let C := (t.toOpenPartialHomeomorph.trans (c.prod (OpenPartialHomeomorph.refl F))).trans
    g.toHomeomorph.toOpenPartialHomeomorph
  let D := (t'.toOpenPartialHomeomorph.trans (d.prod (OpenPartialHomeomorph.refl F))).trans
    g.toHomeomorph.toOpenPartialHomeomorph
  let U : Set M := (c.source ∩ d.source) ∩ (t.baseSet ∩ t'.baseSet)
  have hU : IsOpen U := (c.open_source.inter d.open_source).inter
    (t.open_baseSet.inter t'.open_baseSet)
  have hzU : z.proj ∈ U := ⟨⟨hc, hd⟩, ht, ht'⟩
  have hUc : U ⊆ c.source := fun _ hu ↦ hu.1.1
  have hUd : U ⊆ d.source := fun _ hu ↦ hu.1.2
  have hUt : U ⊆ t.baseSet := fun _ hu ↦ hu.2.1
  let a : U := ⟨z.proj, hzU⟩
  let v₀ : F := (t z).2
  let H := t.preimageHomeomorph hUt
  let j : C(U × F, TE) :=
    ⟨fun w ↦ (H.symm w).val, continuous_subtype_val.comp H.symm.continuous⟩
  have hjval (w : U × F) : j w = t.toOpenPartialHomeomorph.symm (w.1.val, w.2) := rfl
  have hjcenter : j (a, v₀) = z := by
    change (H.symm (a, v₀)).val = z
    have hpoint : H ⟨z, hzU⟩ = (a, v₀) := t.preimageHomeomorph_apply hUt ⟨z, hzU⟩
    have h := congrArg (fun w ↦ (H.symm w).val) hpoint
    simpa only [H.symm_apply_apply] using h.symm
  have hjopen : IsOpenEmbedding j :=
    (hU.preimage (FiberBundle.continuous_proj F E)).isOpenEmbedding_subtypeVal.comp
      H.symm.isOpenEmbedding
  have hj : Set.MapsTo j ({(a, v₀)}ᶜ : Set (U × F)) ({z}ᶜ : Set TE) :=
    fun w hw heq ↦ hw (hjopen.injective (heq.trans hjcenter.symm))
  have hjbase (w : U × F) : (j w).proj = w.1.val :=
    t.proj_symm_apply (t.mem_target.mpr (hUt w.1.property))
  have hjC (w : U × F) : j w ∈ C.source := by
    refine ⟨⟨t.map_target (t.mem_target.mpr (hUt w.1.property)), ?_⟩, Set.mem_univ _⟩
    change (t (j w)).1 ∈ c.source ∧ (t (j w)).2 ∈ Set.univ
    rw [hjval, t.apply_symm_apply (t.mem_target.mpr (hUt w.1.property))]
    exact ⟨hUc w.1.property, Set.mem_univ _⟩
  have hjD (w : U × F) : j w ∈ D.source := by
    have htj : j w ∈ t'.source := t'.mem_source.mpr (hjbase w ▸ w.1.property.2.2)
    refine ⟨⟨htj, ?_⟩, Set.mem_univ _⟩
    change (t' (j w)).1 ∈ d.source ∧ (t' (j w)).2 ∈ Set.univ
    rw [t'.coe_fst htj, hjbase]
    exact ⟨hUd w.1.property, Set.mem_univ _⟩
  let A : C(U, F →L[ℝ] F) :=
    ⟨fun w ↦ (t.coordChangeL ℝ t' w.val).toContinuousLinearMap,
      (continuousOn_coordChange ℝ t t').comp_continuous continuous_subtype_val
        (fun w ↦ w.property.2)⟩
  let L := t.coordChangeL ℝ t' z.proj
  have hA : Function.Injective (A a) := L.injective
  have hCcoord (w : U × F) : C (j w) = g (c w.1.val, w.2) := by
    change g (c (t (j w)).1, (t (j w)).2) = _
    rw [hjval, t.apply_symm_apply (t.mem_target.mpr (hUt w.1.property))]
  have hDcoord (w : U × F) : D (j w) = g (d w.1.val, A w.1 w.2) := by
    change g (d (t' (j w)).1, (t' (j w)).2) = _
    rw [hjval, t.apply_symm_apply_eq_coordChangeL (R := ℝ) t' w.1.property.2]
    rfl
  have hCcenter : g (c z.proj, v₀) = C z := by
    exact (hCcoord (a, v₀)).symm.trans (congrArg C hjcenter)
  have hDcenter : g (d z.proj, A a v₀) = D z := by
    exact (hDcoord (a, v₀)).symm.trans (congrArg D hjcenter)
  -- In common base coordinates the two factors are exactly the already proved scalar comparisons.
  let p : C(U, V) := ⟨fun w ↦ d w.val, d.continuousOn.comp_continuous
    continuous_subtype_val (fun w ↦ hUd w.property)⟩
  let q : C(U, V) := ⟨fun w ↦ d z.proj + (c w.val - c z.proj),
    continuous_const.add ((c.continuousOn.comp_continuous continuous_subtype_val
      (fun w ↦ hUc w.property)).sub continuous_const)⟩
  have hp : Set.MapsTo p ({a}ᶜ : Set U) ({d z.proj}ᶜ : Set V) :=
    fun w hw heq ↦ hw (Subtype.ext (d.injOn (hUd w.property) hd heq))
  have hq : Set.MapsTo q ({a}ᶜ : Set U) ({d z.proj}ᶜ : Set V) :=
    fun w hw heq ↦ hw (Subtype.ext (c.injOn (hUc w.property) hc
      (sub_eq_zero.mp (add_left_cancel (heq.trans (add_zero _).symm)))))
  let τ : C(F, F) := ⟨fun v ↦ A a v₀ + (v - v₀),
    continuous_const.add (continuous_id.sub continuous_const)⟩
  have hτ : Set.MapsTo τ ({v₀}ᶜ : Set F) ({A a v₀}ᶜ : Set F) :=
    fun _ hv heq ↦ hv (sub_eq_zero.mp (add_left_cancel (heq.trans (add_zero _).symm)))
  let s₁ := homologicalOrientationChartSign O d z.proj hd *
    homologicalOrientationChartSign O c z.proj hc
  let s₂ := bundleFiberChartSign r E o t z.proj ht * bundleFiberChartSign r E o t' z.proj ht'
  have hbase : relativeSingularHomologyMap ℤ p hp n =
      s₁ • relativeSingularHomologyMap ℤ q hq n :=
    relativeSingularHomologyMap_chart_eq_sign_smul O c d U hU hUc hUd a
  have hfiber : relativeSingularHomologyMap ℤ
      (⟨A a, (A a).continuous⟩ : C(F, F))
      (A := ({v₀}ᶜ : Set F)) (B := ({A a v₀}ᶜ : Set F))
      (fun _ hv heq ↦ hv (hA heq)) r = s₂ • relativeSingularHomologyMap ℤ τ hτ r := by
    have ho := o.is_generator z.proj
    change Function.Bijective (fun m : ℤ ↦
      (relativeSingularCohomology ℤ {v : E z.proj | v ≠ 0} r).isModule.smul
        m (o.fiberClass z.proj)) at ho
    simp_rw [int_smul_eq_zsmul] at ho
    have h := relativeSingularHomologyMap_linearCoordChange_eq_smul
      (EuclideanSpace.basisFun (Fin r) ℝ).toBasis
      (t.continuousLinearEquivAt ℝ z.proj ht) (t'.continuousLinearEquivAt ℝ z.proj ht')
      (o.fiberClass z.proj) ho v₀
    let K := (t.continuousLinearEquivAt ℝ z.proj ht).symm.trans
      (t'.continuousLinearEquivAt ℝ z.proj ht')
    change relativeSingularHomologyMap ℤ (⟨K, K.continuous⟩ : C(F, F))
      (A := ({v₀}ᶜ : Set F)) (B := ({K v₀}ᶜ : Set F))
      (fun _ hv heq ↦ hv (K.injective heq)) r = s₂ •
        relativeSingularHomologyMap ℤ
          (⟨fun v : F ↦ K v₀ + (v - v₀),
            continuous_const.add (continuous_id.sub continuous_const)⟩ : C(F, F))
          (A := ({v₀}ᶜ : Set F)) (B := ({K v₀}ᶜ : Set F))
          (fun _ hv heq ↦ hv (sub_eq_zero.mp
            (add_left_cancel (heq.trans (add_zero _).symm)))) r at h
    have hK : K = L := t.comp_continuousLinearEquivAt_eq_coord_change t' ⟨ht, ht'⟩
    rw [hK] at h
    exact h
  let fvar : C(U × F, V × F) := ⟨fun w ↦ (p w.1, A w.1 w.2), by fun_prop⟩
  let fref : C(U × F, V × F) := ⟨fun w ↦ (q w.1, τ w.2), by fun_prop⟩
  have hvar : Set.MapsTo fvar ({(a, v₀)}ᶜ : Set (U × F))
      ({(d z.proj, A a v₀)}ᶜ : Set (V × F)) := by
    intro w hw heq
    have hwa : w.1 = a := by
      by_contra hne
      exact hp hne (congrArg Prod.fst heq)
    have hwv : w.2 = v₀ := hA (by
      have h := congrArg Prod.snd heq
      change A w.1 w.2 = A a v₀ at h
      rwa [hwa] at h)
    exact hw (Prod.ext hwa hwv)
  have href : Set.MapsTo fref ({(a, v₀)}ᶜ : Set (U × F))
      ({(d z.proj, A a v₀)}ᶜ : Set (V × F)) := by
    intro w hw heq
    have hwa : w.1 = a := by
      by_contra hne
      exact hq hne (congrArg Prod.fst heq)
    have hwv : w.2 = v₀ := by
      by_contra hne
      exact hτ hne (congrArg Prod.snd heq)
    exact hw (Prod.ext hwa hwv)
  have hprod := relativeSingularHomologyMap_fiberLinear_eq_smul_prod ℤ n r a p q
    (d z.proj) hp hq A hA v₀ τ hτ s₁ s₂
    (by
      apply ModuleCat.hom_ext
      ext v
      have hv := congrArg (fun f ↦ f.hom v) hbase
      simp only [ModuleCat.hom_zsmul] at hv
      change _ = (relativeSingularHomology ℤ ({d z.proj}ᶜ : Set V) n).isModule.smul s₁ _
      rw [int_smul_eq_zsmul]
      exact hv)
    (by
      apply ModuleCat.hom_ext
      ext v
      have hv := congrArg (fun f ↦ f.hom v) hfiber
      simp only [ModuleCat.hom_zsmul] at hv
      change _ = (relativeSingularHomology ℤ ({A a v₀}ᶜ : Set F) r).isModule.smul s₂ _
      rw [int_smul_eq_zsmul]
      exact hv) hvar href
  have hprod' : relativeSingularHomologyMap ℤ fvar hvar (n + r) =
      (s₁ * s₂) • relativeSingularHomologyMap ℤ fref href (n + r) := by
    apply ModuleCat.hom_ext
    ext v
    have hv := congrArg (fun f ↦ f.hom v) hprod
    change _ = (relativeSingularHomology ℤ
      ({(d z.proj, A a v₀)}ᶜ : Set (V × F)) (n + r)).isModule.smul (s₁ * s₂) _ at hv
    rw [int_smul_eq_zsmul] at hv
    exact hv
  let G : C(V × F, W) := ⟨g, g.continuous⟩
  have hG : Set.MapsTo G ({(d z.proj, A a v₀)}ᶜ : Set (V × F)) ({D z}ᶜ : Set W) :=
    fun _ hw heq ↦ hw (g.injective (heq.trans hDcenter.symm))
  let σ : C(W, W) := ⟨fun w ↦ D z + (w - C z),
    continuous_const.add (continuous_id.sub continuous_const)⟩
  have hσ : Set.MapsTo σ ({C z}ᶜ : Set W) ({D z}ᶜ : Set W) :=
    fun _ hw heq ↦ hw (sub_eq_zero.mp (add_left_cancel (heq.trans (add_zero _).symm)))
  let J := relativeSingularHomologyMap ℤ j hj (n + r)
  let GH := relativeSingularHomologyMap ℤ G hG (n + r)
  let S := relativeSingularHomologyMap ℤ σ hσ (n + r)
  let CH := (localHomologyChartEquiv C z hC (n + r)).toModuleIso.hom
  let DH := (localHomologyChartEquiv D z hD (n + r)).toModuleIso.hom
  have hcomp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
      (f : C(X, Y)) (g : C(Y, Z)) {A : Set X} {B : Set Y} {C : Set Z}
      (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
      relativeSingularHomologyMap ℤ (g.comp f) (hg.comp hf) (n + r) =
        relativeSingularHomologyMap ℤ f hf (n + r) ≫
          relativeSingularHomologyMap ℤ g hg (n + r) := by
    change HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp, relativeSingularChainsMap_comp]
  have hcongr {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
      {f g : C(X, Y)} {A : Set X} {B : Set Y}
      (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B) (heq : f = g) :
      relativeSingularHomologyMap ℤ f hf (n + r) =
        relativeSingularHomologyMap ℤ g hg (n + r) := by
    subst g
    rfl
  have hJD : J ≫ DH = relativeSingularHomologyMap ℤ fvar hvar (n + r) ≫ GH := by
    rw [show J ≫ DH = _ from localHomologyChartEquiv_naturality D z hD j hjD hj (n + r)]
    rw [← hcomp fvar G hvar hG]
    apply hcongr
    apply ContinuousMap.ext
    exact hDcoord
  have hJC : J ≫ CH ≫ S = relativeSingularHomologyMap ℤ fref href (n + r) ≫ GH := by
    rw [← Category.assoc, show J ≫ CH = _ from
      localHomologyChartEquiv_naturality C z hC j hjC hj (n + r)]
    rw [← hcomp, ← hcomp fref G href hG]
    apply hcongr
    apply ContinuousMap.ext
    intro w
    change D z + (C (j w) - C z) = g (q w.1, τ w.2)
    rw [hCcoord, ← hDcenter, ← hCcenter, ← map_sub, ← map_add]
    congr 1
  -- The common source is an actual open chart neighborhood, so its local map is invertible.
  let : IsIso J := by
    have hA : ({(a, v₀)}ᶜ : Set (U × F)) = (j ⁻¹' ({z} : Set TE))ᶜ := by
      ext w
      change (w ≠ (a, v₀)) ↔ j w ≠ z
      rw [← hjcenter, hjopen.injective.ne_iff]
    have hexc {A : Set (U × F)} (heq : A = (j ⁻¹' ({z} : Set TE))ᶜ)
        (hmap : Set.MapsTo j A ({z}ᶜ : Set TE)) :
        homotopyEquivalences (ModuleCat ℤ) (ComplexShape.down ℕ)
          (relativeSingularChainsMap ℤ j hmap) := by
      subst A
      exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding ℤ j hjopen {z}
        isClosed_singleton (Set.singleton_subset_iff.mpr ⟨(a, v₀), hjcenter⟩)
    obtain ⟨K, hK⟩ := hexc hA hj
    change IsIso (HomologicalComplex.homologyMap _ (n + r))
    rw [← hK]
    change IsIso (K.toHomologyIso (n + r)).hom
    infer_instance
  change DH = (s₁ * s₂) • (CH ≫ S)
  apply (cancel_epi J).mp
  rw [Preadditive.comp_zsmul, hJD, hprod', Preadditive.zsmul_comp, hJC]

end AtiyahSinger
