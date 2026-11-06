/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyThomNaturality
public import AtiyahSinger.Topology.CompactSupportCohomologyThom
public import AtiyahSinger.Topology.CompactSupportOpenExtension

/-!
# Open-extension naturality of the original supported Thom map

Public module ID: M2206.

An oriented bundle isomorphism over an open base embedding sends the original
zero-section support onto the corresponding compact-image support. Excision
extends the original relative coefficient, and the same normalized Thom class
pulls back to the specified source Thom class. This proves naturality of the
actual support-colimit map without properness of the open embedding.

Sources: Hatcher, Algebraic Topology, Section 3.3; Milnor--Stasheff, Section 9.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R] (r : ℕ)
  {X Y : Type u} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  (F : Y → Type u) [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℝ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) F)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) F]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) F]
  (oE : CohomologyOrientation R r E) (oF : CohomologyOrientation R r F)
  (f : C(X, Y)) (hf : IsOpenEmbedding f)
  (g : C(TotalSpace (EuclideanSpace ℝ (Fin r)) E,
    TotalSpace (EuclideanSpace ℝ (Fin r)) F)) (hgOpen : IsOpenEmbedding g)
  (hN : Set.MapsTo g (bundleNonzero r E) (bundleNonzero r F))
  (e : ∀ x, E x ≃L[ℝ] F (f x))
  (hg : ∀ x, g.comp (bundleFiberInclusion r E x) =
    (bundleFiberInclusion r F (f x)).comp ⟨e x, (e x).continuous⟩)
  (ho : ∀ x, relativeSingularCohomologyPullback R
    (⟨e x, (e x).continuous⟩ : C(E x, F (f x)))
      (show Set.MapsTo (e x) {v : E x | v ≠ 0} {v : F (f x) | v ≠ 0} from
        fun _ hv hz ↦ hv ((e x).injective (hz.trans (e x).map_zero.symm))) r
      (oF.fiberClass (f x)) = oE.fiberClass x)

attribute [local instance] t2Space_fiberBundleTotal

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

include hg ho hN in
/-- The original supported Thom map commutes with actual oriented open extension. -/
theorem compactSupportCohomologyThomMap_openExtension (p : ℕ)
    (a : compactSupportCohomology R X p) :
    compactSupportCohomologyThomMap R r F oF p
        (compactSupportCohomologyOpenExtension R f hf p a) =
      compactSupportCohomologyOpenExtension R g hgOpen (p + r)
        (compactSupportCohomologyThomMap R r E oE p a) := by
  let TE := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let TF := TotalSpace (EuclideanSpace ℝ (Fin r)) F
  have hvalue (z : TE) : g z = ⟨f z.proj, e z.proj z.snd⟩ :=
    congrArg (fun t ↦ t z.snd) (hg z.proj)
  have hbase : (bundleProjection r F).comp g = f.comp (bundleProjection r E) := by
    apply ContinuousMap.ext
    intro z
    exact congrArg Bundle.TotalSpace.proj (hvalue z)
  obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R X p a
  let L := openEmbeddingCompactImage f K
  let ZE := supportedCohomologyThomSupport r E K
  let ZF := supportedCohomologyThomSupport r F L
  let Z := openEmbeddingCompactImage g ZE
  have hZ : Z = ZF := by
    apply Compacts.ext
    ext z
    change (∃ w ∈ (ZE : Set TE), g w = z) ↔
      ∃ y ∈ (L : Set Y), bundleZeroSection r F y = z
    constructor
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
      rw [hvalue]
      change (⟨f x, 0⟩ : TF) = ⟨f x, e x 0⟩
      rw [(e x).map_zero]
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨bundleZeroSection r E x, ⟨x, hx, rfl⟩, ?_⟩
      rw [hvalue]
      change (⟨f x, e x 0⟩ : TF) = ⟨f x, 0⟩
      rw [(e x).map_zero]
  let PX := openEmbeddingCohomologySupportPullback R f hf K p
  let PZ := openEmbeddingCohomologySupportPullback R g hgOpen ZE (p + r)
  let : IsIso PX := isIso_openEmbeddingCohomologySupportPullback R f hf K p
  let : IsIso PZ := isIso_openEmbeddingCohomologySupportPullback R g hgOpen ZE (p + r)
  let β := (asIso PX).inv α
  have hβ : PX β = α := (asIso PX).inv_hom_id_apply α
  let A := (bundleProjection r E) ⁻¹' ((K : Set X)ᶜ)
  let B := bundleNonzero r E
  let C := (bundleProjection r F) ⁻¹' ((L : Set Y)ᶜ)
  let D := bundleNonzero r F
  have hfK : Set.MapsTo f ((K : Set X)ᶜ) ((L : Set Y)ᶜ) := by
    rintro x hx ⟨y, hy, hyx⟩
    exact hx ((hf.injective hyx) ▸ hy)
  have hAC : Set.MapsTo g A C := by
    intro z hz
    change (g z).proj ∉ (L : Set Y)
    rw [hvalue]
    exact hfK hz
  have hsup : Set.MapsTo g ((ZE : Set TE)ᶜ) ((ZF : Set TF)ᶜ) := by
    intro z hz
    change g z ∉ (ZF : Set TF)
    rw [← hZ]
    rintro ⟨w, hw, hwz⟩
    exact hz ((hgOpen.injective hwz) ▸ hw)
  let PE := relativeSingularCohomologyPullback R g hsup (p + r)
  have hThom : PE (supportedCohomologyThomMap R r F oF L p β) =
      supportedCohomologyThomMap R r E oE K p α := by
    have hE := isOpen_supportedCohomologyThomSubspaces r E K
    have hF := isOpen_supportedCohomologyThomSubspaces r F L
    have htransport (A' B' : Set TE) (hE' : A' = B')
        (C' D' : Set TF) (hF' : C' = D')
        (h₁ : Set.MapsTo g A' C') (h₂ : Set.MapsTo g B' D')
        (c : relativeSingularCohomology R C' (p + r)) :
        relativeSingularCohomologyPullback R g h₂ (p + r)
            ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r)) hF')).hom c) =
          (eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r)) hE')).hom
            (relativeSingularCohomologyPullback R g h₁ (p + r) c) := by
      subst B'
      subst D'
      rfl
    change PE ((eqToIso (congrArg
      (fun S ↦ relativeSingularCohomology R S (p + r))
        (supportedCohomologyThomSupport_compl r F L))).hom
      (relativeSingularCohomologyUnionCup R C D hF.1 hF.2 p r
        (relativeSingularCohomologyPullback R (bundleProjection r F)
          (fun _ hz ↦ hz) p β) (cohomologyThomClass R r F oF))) = _
    rw [htransport (A ∪ B) ((ZE : Set TE)ᶜ)
      (supportedCohomologyThomSupport_compl r E K) (C ∪ D) ((ZF : Set TF)ᶜ)
      (supportedCohomologyThomSupport_compl r F L)
      (fun _ hz ↦ hz.elim (fun h ↦ Or.inl (hAC h)) (fun h ↦ Or.inr (hN h)))]
    rw [relativeSingularCohomologyPullback_unionCup R g
      hE.1 hE.2 hF.1 hF.2 hAC hN]
    rw [cohomologyThomClass_pullback R r E F oE oF f g hN e hg ho]
    have hπF : Set.MapsTo (bundleProjection r F) C ((L : Set Y)ᶜ) := fun _ hz ↦ hz
    have hπE : Set.MapsTo (bundleProjection r E) A ((K : Set X)ᶜ) := fun _ hz ↦ hz
    have hcomm : relativeSingularCohomologyPullback R (bundleProjection r F) hπF p ≫
        relativeSingularCohomologyPullback R g hAC p =
      relativeSingularCohomologyPullback R f hfK p ≫
        relativeSingularCohomologyPullback R (bundleProjection r E) hπE p := by
      rw [← relativeSingularCohomologyPullback_comp,
        ← relativeSingularCohomologyPullback_comp]
      congr 1
    have hcoeff : relativeSingularCohomologyPullback R g hAC p
        (relativeSingularCohomologyPullback R (bundleProjection r F) hπF p β) =
        relativeSingularCohomologyPullback R (bundleProjection r E) hπE p α := by
      have hc := congrArg (fun t ↦ t β) hcomm
      change _ = relativeSingularCohomologyPullback R (bundleProjection r E) hπE p (PX β) at hc
      exact hc.trans (congrArg (relativeSingularCohomologyPullback R
        (bundleProjection r E) hπE p) hβ)
    exact congrArg (fun c : relativeSingularCohomology R A p ↦
      (eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r))
        (supportedCohomologyThomSupport_compl r E K))).hom
          (relativeSingularCohomologyUnionCup R A B hE.1 hE.2 p r c
            (cohomologyThomClass R r E oE))) hcoeff
  -- Invert exactly the total-space excision restriction, retaining its compact-image support.
  let T := eqToIso (congrArg
    (fun K : Compacts TF ↦ relativeSingularCohomology R ((K : Set TF)ᶜ) (p + r)) hZ)
  have hcast (U W : Compacts TF) (h : U = W)
      (hU : Set.MapsTo g ((ZE : Set TE)ᶜ) ((U : Set TF)ᶜ))
      (hW : Set.MapsTo g ((ZE : Set TE)ᶜ) ((W : Set TF)ᶜ))
      (b : relativeSingularCohomology R ((W : Set TF)ᶜ) (p + r)) :
      relativeSingularCohomologyPullback R g hU (p + r)
          ((eqToIso (congrArg
            (fun K : Compacts TF ↦ relativeSingularCohomology R ((K : Set TF)ᶜ) (p + r))
              h)).inv b) = relativeSingularCohomologyPullback R g hW (p + r) b := by
    subst W
    rfl
  have hpre : (asIso PZ).inv (supportedCohomologyThomMap R r E oE K p α) =
      T.inv (supportedCohomologyThomMap R r F oF L p β) := by
    apply (ConcreteCategory.isIso_iff_bijective PZ).mp inferInstance |>.injective
    exact ((asIso PZ).inv_hom_id_apply _).trans
      ((hcast Z ZF hZ _ hsup _).trans hThom).symm
  have hclass (U W : Compacts TF) (h : U = W)
      (b : relativeSingularCohomology R ((W : Set TF)ᶜ) (p + r)) :
      compactSupportCohomologyClass R TF U (p + r)
          ((eqToIso (congrArg
            (fun K : Compacts TF ↦ relativeSingularCohomology R ((K : Set TF)ᶜ) (p + r))
              h)).inv b) = compactSupportCohomologyClass R TF W (p + r) b := by
    subst W
    rfl
  rw [compactSupportCohomologyOpenExtension_representative]
  change compactSupportCohomologyThomMap R r F oF p
      (compactSupportCohomologyClass R Y L p β) = _
  rw [compactSupportCohomologyThomMap_representative,
    compactSupportCohomologyThomMap_representative,
    compactSupportCohomologyOpenExtension_representative]
  change compactSupportCohomologyClass R TF ZF (p + r)
      (supportedCohomologyThomMap R r F oF L p β) =
    compactSupportCohomologyClass R TF Z (p + r)
      ((asIso PZ).inv (supportedCohomologyThomMap R r E oE K p α))
  rw [hpre]
  exact (hclass Z ZF hZ _).symm

end AtiyahSinger
