/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportFunctoriality
public import AtiyahSinger.Topology.SupportKZeroComparison

/-!
Public module ID: M1753.

# Compactly supported K theory of finite disjoint unions

D07/K02: Karoubi II.1.26, pp.56--57, states the absolute compact-space result.
The compact-support extension here uses the existing support-triple comparison:
restriction and gluing on clopen summands preserve one compact control when
there are finitely many summands. The forward map is the actual proper pullback
along each inclusion. No compactness or connectedness of a summand is required.
The local-compactness certificate is a standard topological prerequisite absent
from the currently imported mathlib interfaces, not a new K-theory object.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology

variable {ι : Type*} (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  [∀ i, LocallyCompactSpace (X i)] [∀ i, T2Space (X i)]

-- Keep the original Hausdorff context, although the neighborhood argument uses less.
set_option linter.unusedSectionVars false in
/-- A disjoint union of locally compact Hausdorff spaces is locally compact. -/
theorem locallyCompactSpace_sigma : LocallyCompactSpace (Σ i, X i) := by
  -- Pull the given neighborhood into the point's own summand.
  refine ⟨?_⟩
  rintro ⟨i, x⟩ U hU
  have hpre : Sigma.mk i ⁻¹' U ∈ 𝓝 x := continuous_sigmaMk.continuousAt hU
  obtain ⟨K, hKnhds, hKU, hKcompact⟩ := local_compact_nhds hpre
  -- The open inclusion preserves neighborhoods; continuity preserves compactness.
  refine ⟨Sigma.mk i '' K, isOpenMap_sigmaMk.image_mem_nhds hKnhds, ?_,
    hKcompact.image continuous_sigmaMk⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hKU hy

attribute [local instance] locallyCompactSpace_sigma

/-- Restrict a compactly supported class to every clopen summand by proper pullback. -/
def compactSupportKZeroSigmaRestrict :
    CompactSupportKZero (Σ i, X i) →+ (∀ i, CompactSupportKZero (X i)) :=
  AddMonoidHom.pi fun i ↦
    compactSupportKZeroPullback ⟨Sigma.mk i, continuous_sigmaMk⟩
      IsClosedEmbedding.sigmaMk.isProperMap

/-- Finite disjoint unions split compactly supported K theory by their actual restrictions. -/
theorem compactSupportKZeroSigmaRestrict_bijective [Finite ι] :
    Function.Bijective (compactSupportKZeroSigmaRestrict X) := by
  /- Stage 1: represent each summand class by a support triple. Glue its two
  bundles and exterior isomorphism on the clopen summands. The finite union
  of the images of their compact controls is compact. This produces a class
  whose proper restrictions are the prescribed ones, proving surjectivity.
  Stage 2: if all restrictions of a class vanish, the stable-germ zero
  criterion gives trivializations after stabilization on each summand.
  Glue the stabilizers and comparison maps, enlarging to the finite union
  of the compact controls. The same criterion makes the original class zero.
  This proves injectivity. Empty summands and an empty index set are allowed.
  For an infinite index set arbitrary component classes need not have a
  common compact control, so no product-surjectivity claim is made there. -/
  exact (open Bundle ComplexBundle in by
    classical
    let globalSumTopology {E F : (Σ i, X i) → Type}
        [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
        [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
        [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)] :
        TopologicalSpace (TotalSpace Unit (E ×ᵇ F)) := sumTopology
    let summandSumTopology (i : ι) {E F : X i → Type}
        [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
        [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
        [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)] :
        TopologicalSpace (TotalSpace Unit (E ×ᵇ F)) := sumTopology
    -- Stage 1: glue the original fibers and their local finite linear charts on clopen pieces.
    -- Keep the bundle family explicit while inferring each transported total topology.
    let +zeta fiber (A : ∀ i, FiniteBundle (X i)) : (Σ i, X i) → Type :=
      fun x ↦ Function.uncurry
        (fun (B : ∀ i, FiniteBundle (X i)) (y : Σ i, X i) ↦ (B y.1).Fiber y.2) (A, x)
    let fiberGroup (A : ∀ i, FiniteBundle (X i)) (x : Σ i, X i) :
        AddCommGroup (fiber A x) :=
      (A x.1).addCommGroup x.2
    let fiberModule (A : ∀ i, FiniteBundle (X i)) (x : Σ i, X i) :
        Module ℂ (fiber A x) :=
      (A x.1).module x.2
    let totalEquiv (A : ∀ i, FiniteBundle (X i)) :
        TotalSpace Unit (fiber A) ≃ Σ i, TotalSpace Unit (A i).Fiber :=
      { toFun z := ⟨z.proj.1, ⟨z.proj.2, z.snd⟩⟩
        invFun z := ⟨⟨z.1, z.2.proj⟩, z.2.snd⟩
        left_inv := by rintro ⟨⟨i, x⟩, v⟩; rfl
        right_inv := by rintro ⟨i, x, v⟩; rfl }
    let totalTopology (A : ∀ i, FiniteBundle (X i)) :
        TopologicalSpace (TotalSpace Unit (fiber A)) :=
      TopologicalSpace.induced (totalEquiv A) inferInstance
    let totalHomeomorph (A : ∀ i, FiniteBundle (X i)) :
        TotalSpace Unit (fiber A) ≃ₜ Σ i, TotalSpace Unit (A i).Fiber :=
      (totalEquiv A).toHomeomorphOfIsInducing ⟨rfl⟩
    have finiteRank (A : ∀ i, FiniteBundle (X i)) : IsFiniteRank (fiber A) := by
      classical
      constructor
      rintro ⟨i, x⟩
      obtain ⟨r, e, hx, hlinear⟩ :=
        IsFiniteRank.exists_linear_trivialization (E := (A i).Fiber) x
      let : Nonempty (X i) := ⟨x⟩
      let j : TotalSpace Unit (A i).Fiber → TotalSpace Unit (fiber A) :=
        fun z ↦ ⟨⟨i, z.proj⟩, z.snd⟩
      have hj : IsOpenEmbedding j :=
        (totalHomeomorph A).symm.isOpenEmbedding.comp IsOpenEmbedding.sigmaMk
      let c : X i × (Fin r → ℂ) → (Σ i, X i) × (Fin r → ℂ) :=
        Prod.map (Sigma.mk i) id
      have hc : IsOpenEmbedding c := IsOpenEmbedding.sigmaMk.prodMap IsOpenEmbedding.id
      let h := e.toOpenPartialHomeomorph.lift_openEmbedding hj
      let k := hc.toOpenPartialHomeomorph c
      let t : Trivialization (Fin r → ℂ) (TotalSpace.proj (F := Unit) (E := fiber A)) :=
        { toOpenPartialHomeomorph := h.trans k
          baseSet := Sigma.mk i '' e.baseSet
          open_baseSet := isOpenMap_sigmaMk _ e.open_baseSet
          source_eq := by
            ext z
            change (z ∈ j '' e.source ∧ h z ∈ Set.univ) ↔
              z.proj ∈ Sigma.mk i '' e.baseSet
            simp only [Set.mem_univ, and_true]
            constructor
            · rintro ⟨w, hw, rfl⟩
              exact ⟨w.proj, e.mem_source.mp hw, rfl⟩
            · rintro ⟨y, hy, heq⟩
              cases z with
              | mk p v =>
                cases heq
                exact ⟨⟨y, v⟩, e.mem_source.mpr hy, rfl⟩
          target_eq := by
            ext z
            change (z ∈ c '' Set.univ ∧ k.symm z ∈ e.target) ↔
              z.1 ∈ Sigma.mk i '' e.baseSet ∧ z.2 ∈ Set.univ
            simp only [Set.image_univ, Set.mem_univ, and_true]
            constructor
            · rintro ⟨⟨w, rfl⟩, hw⟩
              rw [hc.toOpenPartialHomeomorph_left_inv] at hw
              exact ⟨w.1, e.mem_target.mp hw, rfl⟩
            · rintro ⟨y, hy, heq⟩
              cases z with
              | mk p v =>
                cases heq
                refine ⟨⟨(y, v), rfl⟩, ?_⟩
                change k.symm (c (y, v)) ∈ e.target
                rw [hc.toOpenPartialHomeomorph_left_inv]
                exact e.mem_target.mpr hy
          proj_toFun := by
            rintro z ⟨⟨w, hw, rfl⟩, _⟩
            change Sigma.mk i (h (j w)).1 = Sigma.mk i w.proj
            rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
            exact congrArg (Sigma.mk i) (e.proj_toFun w hw) }
      refine ⟨r, t, ⟨x, hx, rfl⟩, ?_⟩
      rintro y ⟨w, hw, rfl⟩
      change IsLinearMap ℂ (fun v ↦ (h (j ⟨w, v⟩)).2)
      simp only [h, OpenPartialHomeomorph.lift_openEmbedding_apply]
      exact hlinear w hw
    let glued (A : ∀ i, FiniteBundle (X i)) : FiniteBundle (Σ i, X i) :=
      { Fiber := fiber A
        totalTopology := totalTopology A
        isFiniteRank := finiteRank A }
    let sigmaIso (P Q : FiniteBundle (Σ i, X i)) : Type _ :=
      @Iso _ P.Fiber Q.Fiber P.addCommGroup P.module Q.addCommGroup Q.module
        P.totalTopology Q.totalTopology
    -- Stage 2: keep vectors fixed in component pullbacks and in reconstruction.
    let componentIso (A : ∀ i, FiniteBundle (X i)) (i : ι) :
        Iso (((glued A).pullback ⟨Sigma.mk i, continuous_sigmaMk⟩).Fiber) (A i).Fiber :=
      { linearEquiv x := LinearEquiv.refl ℂ ((A i).Fiber x)
        continuous_total := by
          have hi : IsEmbedding (@Sigma.mk ι (fun i ↦ TotalSpace Unit (A i).Fiber) i) :=
            IsEmbedding.sigmaMk
          apply hi.continuous_iff.mpr
          exact (totalHomeomorph A).continuous.comp
            (Pullback.continuous_lift Unit (fiber A) (Sigma.mk i))
        continuous_symm := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit (fiber A) (Sigma.mk i)).continuous_iff]
          exact (continuous_proj (E := (A i).Fiber)).prodMk
            ((totalHomeomorph A).symm.continuous.comp continuous_sigmaMk) }
    have componentLiftInducing (E : FiniteBundle (Σ i, X i)) (i : ι) :
        IsInducing (@Pullback.lift (Σ i, X i) Unit E.Fiber (X i) (Sigma.mk i)) := by
      have hpair := (IsEmbedding.sigmaMk.isInducing.prodMap IsInducing.id).comp
        (inducing_pullbackTotalSpaceEmbedding Unit E.Fiber (Sigma.mk i))
      exact IsInducing.of_comp (Pullback.continuous_lift Unit E.Fiber (Sigma.mk i))
        ((continuous_proj (E := E.Fiber)).prodMk continuous_id) hpair
    have summandExteriorLiftInducing (i : ι) (E : FiniteBundle (X i)) (K : Set (X i)) :
        IsInducing (@Pullback.lift (X i) Unit E.Fiber ↥(Kᶜ) Subtype.val) := by
      have hpair := (IsInducing.subtypeVal.prodMap IsInducing.id).comp
        (inducing_pullbackTotalSpaceEmbedding Unit E.Fiber (Subtype.val : ↥(Kᶜ) → X i))
      exact IsInducing.of_comp (Pullback.continuous_lift Unit E.Fiber Subtype.val)
        ((continuous_proj (E := E.Fiber)).prodMk continuous_id) hpair
    have exteriorLiftInducing (E : FiniteBundle (Σ i, X i)) (K : Set (Σ i, X i)) :
        IsInducing (@Pullback.lift (Σ i, X i) Unit E.Fiber ↥(Kᶜ) Subtype.val) := by
      have hpair := (IsInducing.subtypeVal.prodMap IsInducing.id).comp
        (inducing_pullbackTotalSpaceEmbedding Unit E.Fiber (Subtype.val : ↥(Kᶜ) → _))
      exact IsInducing.of_comp (Pullback.continuous_lift Unit E.Fiber Subtype.val)
        ((continuous_proj (E := E.Fiber)).prodMk continuous_id) hpair
    let splitEquiv (E : FiniteBundle (Σ i, X i)) :
        (Σ i, TotalSpace Unit ((E.pullback ⟨Sigma.mk i, continuous_sigmaMk⟩).Fiber)) ≃
          TotalSpace Unit E.Fiber :=
      { toFun z := ⟨⟨z.1, z.2.proj⟩, z.2.snd⟩
        invFun z := ⟨z.proj.1, ⟨z.proj.2, z.snd⟩⟩
        left_inv := by rintro ⟨i, x, v⟩; rfl
        right_inv := by rintro ⟨⟨i, x⟩, v⟩; rfl }
    let splitHomeomorph (E : FiniteBundle (Σ i, X i)) :
        (Σ i, TotalSpace Unit ((E.pullback ⟨Sigma.mk i, continuous_sigmaMk⟩).Fiber)) ≃ₜ
          TotalSpace Unit E.Fiber :=
      (splitEquiv E).toHomeomorphOfIsInducing (by
        apply inducing_sigma.mpr
        refine ⟨fun i ↦ componentLiftInducing E i, ?_⟩
        intro i
        refine ⟨(TotalSpace.proj (F := Unit) (E := E.Fiber)) ⁻¹' Set.range (Sigma.mk i),
          isOpen_range_sigmaMk.preimage (continuous_proj (E := E.Fiber)), ?_⟩
        rintro ⟨j, z⟩
        constructor
        · rintro ⟨x, hx⟩
          exact (congrArg Sigma.fst hx).symm
        · intro h
          change j = i at h
          subst j
          exact ⟨z.proj, rfl⟩)
    let originalIso (E : FiniteBundle (Σ i, X i)) :
        sigmaIso E (glued (fun i ↦ E.pullback ⟨Sigma.mk i, continuous_sigmaMk⟩)) :=
      { linearEquiv x := LinearEquiv.refl ℂ (E.Fiber x)
        continuous_total :=
          (totalHomeomorph _).symm.continuous.comp (splitHomeomorph E).symm.continuous
        continuous_symm :=
          (splitHomeomorph E).continuous.comp (totalHomeomorph _).continuous }
    -- Stage 3: glue the exact exterior maps and the same stabilizing bundle maps.
    let control (K : ∀ i, Set (X i)) : Set (Σ i, X i) :=
      {x | x.2 ∈ K x.1}
    let exteriorTotalEquiv (A : ∀ i, FiniteBundle (X i)) (K : ∀ i, Set (X i)) :
        (Σ i, TotalSpace Unit ((A i).restrict (K i)ᶜ).Fiber) ≃
          TotalSpace Unit (Restrict (glued A).Fiber (control K)ᶜ) :=
      { toFun z := ⟨⟨⟨z.1, z.2.proj.val⟩, z.2.proj.property⟩, z.2.snd⟩
        invFun z := ⟨z.proj.val.1, ⟨⟨z.proj.val.2, z.proj.property⟩, z.snd⟩⟩
        left_inv := by rintro ⟨i, ⟨x, hx⟩, v⟩; rfl
        right_inv := by rintro ⟨⟨⟨i, x⟩, hx⟩, v⟩; rfl }
    let exteriorTotalHomeomorph (A : ∀ i, FiniteBundle (X i)) (K : ∀ i, Set (X i)) :
        (Σ i, TotalSpace Unit ((A i).restrict (K i)ᶜ).Fiber) ≃ₜ
          TotalSpace Unit (Restrict (glued A).Fiber (control K)ᶜ) :=
      (exteriorTotalEquiv A K).toHomeomorphOfIsInducing (by
        have hσ : IsInducing (Sigma.map
            (β₁ := fun i ↦ TotalSpace Unit ((A i).restrict (K i)ᶜ).Fiber)
            (β₂ := fun i ↦ TotalSpace Unit (A i).Fiber) id
            (fun i ↦ @Pullback.lift (X i) Unit (A i).Fiber ↥((K i)ᶜ) Subtype.val)) :=
          by
            rw [isInducing_sigmaMap Function.injective_id]
            intro i
            exact summandExteriorLiftInducing i (A i) (K i)
        have htotal := (totalHomeomorph A).symm.isInducing.comp hσ
        exact (exteriorLiftInducing (glued A) (control K)).of_comp_iff.mp htotal)
    let exteriorIso (A B : ∀ i, FiniteBundle (X i)) (K : ∀ i, Set (X i))
        (e : ∀ i, Iso (Restrict (A i).Fiber (K i)ᶜ) (Restrict (B i).Fiber (K i)ᶜ)) :
        Iso (Restrict (glued A).Fiber (control K)ᶜ)
          (Restrict (glued B).Fiber (control K)ᶜ) :=
      { linearEquiv x := (e x.val.1).linearEquiv ⟨x.val.2, x.property⟩
        continuous_total := by
          change Continuous ((exteriorTotalHomeomorph B K) ∘ Sigma.map id
            (fun i z ↦ (⟨z.proj, (e i).linearEquiv z.proj z.snd⟩ :
              TotalSpace Unit ((B i).restrict (K i)ᶜ).Fiber)) ∘
            (exteriorTotalHomeomorph A K).symm)
          exact (exteriorTotalHomeomorph B K).continuous.comp
            ((Continuous.sigma_map (fun i ↦ (e i).continuous_total)).comp
              (exteriorTotalHomeomorph A K).symm.continuous)
        continuous_symm := by
          change Continuous ((exteriorTotalHomeomorph A K) ∘ Sigma.map id
            (fun i z ↦ (⟨z.proj, ((e i).linearEquiv z.proj).symm z.snd⟩ :
              TotalSpace Unit ((A i).restrict (K i)ᶜ).Fiber)) ∘
            (exteriorTotalHomeomorph B K).symm)
          exact (exteriorTotalHomeomorph A K).continuous.comp
            ((Continuous.sigma_map (fun i ↦ (e i).continuous_symm)).comp
              (exteriorTotalHomeomorph B K).symm.continuous) }
    let gluedIso (A B : ∀ i, FiniteBundle (X i)) (e : ∀ i, Iso (A i).Fiber (B i).Fiber) :
        sigmaIso (glued A) (glued B) :=
      { linearEquiv x := (e x.1).linearEquiv x.2
        continuous_total := by
          change Continuous ((totalHomeomorph B).symm ∘ Sigma.map id
            (fun i z ↦ (⟨z.proj, (e i).linearEquiv z.proj z.snd⟩ :
              TotalSpace Unit (B i).Fiber)) ∘ (totalHomeomorph A))
          exact (totalHomeomorph B).symm.continuous.comp
            ((Continuous.sigma_map (fun i ↦ (e i).continuous_total)).comp
              (totalHomeomorph A).continuous)
        continuous_symm := by
          change Continuous ((totalHomeomorph A).symm ∘ Sigma.map id
            (fun i z ↦ (⟨z.proj, ((e i).linearEquiv z.proj).symm z.snd⟩ :
              TotalSpace Unit (A i).Fiber)) ∘ (totalHomeomorph B))
          exact (totalHomeomorph A).symm.continuous.comp
            ((Continuous.sigma_map (fun i ↦ (e i).continuous_symm)).comp
              (totalHomeomorph B).continuous) }
    let sumCompare (A G : ∀ i, FiniteBundle (X i)) :
        sigmaIso ((glued A).sum (glued G)) (glued (fun i ↦ (A i).sum (G i))) := by
      let E := (glued A).sum (glued G)
      let B := fun i ↦ (A i).sum (G i)
      let e (i : ι) : Iso (E.pullback ⟨Sigma.mk i, continuous_sigmaMk⟩).Fiber (B i).Fiber :=
        { linearEquiv x := LinearEquiv.refl ℂ ((A i).Fiber x × (G i).Fiber x)
          continuous_total := by
            apply continuous_induced_rng.mpr
            exact ((componentIso A i).continuous_total.comp
              ((sumFst (E := (glued A).Fiber) (F := (glued G).Fiber)).continuous_pullback
                ⟨Sigma.mk i, continuous_sigmaMk⟩)).prodMk
              ((componentIso G i).continuous_total.comp
                ((sumSnd (E := (glued A).Fiber) (F := (glued G).Fiber)).continuous_pullback
                  ⟨Sigma.mk i, continuous_sigmaMk⟩))
          continuous_symm := by
            rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber (Sigma.mk i)).continuous_iff]
            refine ((continuous_proj (E := (A i).Fiber)).comp
              (continuous_sum_fst (E := (A i).Fiber) (F := (G i).Fiber))).prodMk ?_
            apply continuous_induced_rng.mpr
            exact (((totalHomeomorph A).symm.continuous.comp continuous_sigmaMk).comp
              (continuous_sum_fst (E := (A i).Fiber) (F := (G i).Fiber))).prodMk
              (((totalHomeomorph G).symm.continuous.comp continuous_sigmaMk).comp
                (continuous_sum_snd (E := (A i).Fiber) (F := (G i).Fiber))) }
      exact
        { linearEquiv x := LinearEquiv.refl ℂ ((A x.1).Fiber x.2 × (G x.1).Fiber x.2)
          continuous_total := by
            exact (totalHomeomorph B).symm.continuous.comp
              ((Continuous.sigma_map (fun i ↦ (e i).continuous_total)).comp
                (splitHomeomorph E).symm.continuous)
          continuous_symm := by
            exact (splitHomeomorph E).continuous.comp
              ((Continuous.sigma_map (fun i ↦ (e i).continuous_symm)).comp
                (totalHomeomorph B).continuous) }
    -- Stage 4: finiteness gives a single compact control for the glued triples.
    have controlCompact (K : ∀ i, Set (X i)) (hK : ∀ i, IsCompact (K i)) :
        IsCompact (control K) := by
      convert Set.isCompact_sigma (t := K) (Set.toFinite (Set.univ : Set ι))
        (fun i _ ↦ hK i) using 1
      ext x
      simp [control]
    let triple (a : ∀ i, SupportBundleTriple (X i)) :
        SupportBundleTriple (Σ i, X i) := by
      let P := glued (fun i ↦ (a i).source)
      let Q := glued (fun i ↦ (a i).target)
      let : TopologicalSpace (TotalSpace Unit P.Fiber) := P.totalTopology
      let : TopologicalSpace (TotalSpace Unit Q.Fiber) := Q.totalTopology
      exact
        { source := P
          target := Q
          datum :=
            { control := control (fun i ↦ (a i).datum.control)
              isCompact_control := controlCompact _ (fun i ↦ (a i).datum.isCompact_control)
              boundary := exteriorIso _ _ _ (fun i ↦ (a i).datum.boundary) } }
    have tripleRestrict (a : ∀ i, SupportBundleTriple (X i)) (i : ι) :
        ((triple a).pullback ⟨Sigma.mk i, continuous_sigmaMk⟩
          IsClosedEmbedding.sigmaMk.isProperMap).IsIsomorphic (a i) := by
      let b := triple a
      let f : C(X i, Σ i, X i) := ⟨Sigma.mk i, continuous_sigmaMk⟩
      have hf : IsProperMap f := IsClosedEmbedding.sigmaMk.isProperMap
      refine ⟨(a i).datum.control, (a i).datum.isCompact_control, Set.Subset.refl _,
        Set.Subset.refl _, componentIso (fun i ↦ (a i).source) i,
        componentIso (fun i ↦ (a i).target) i, ?_⟩
      intro x v
      change (((b.pullback f hf).datum.enlarge (a i).datum.control
        (a i).datum.isCompact_control (Set.Subset.refl _)).boundary.linearEquiv x v) = _
      have hl := (b.datum.pullback f hf).enlarge_apply (a i).datum.control
        (a i).datum.isCompact_control (Set.Subset.refl _) x v
      have hp := RelativeTriple.pullback_apply b.datum.boundary f x v
      have hr := (a i).datum.enlarge_apply (a i).datum.control
        (a i).datum.isCompact_control (Set.Subset.refl _) x v
      exact hl.trans (hp.trans hr.symm)
    -- Stage 5: recover the original triple and glue its stable-zero extensions.
    have reconstruct (a : SupportBundleTriple (Σ i, X i)) :
        a.IsIsomorphic (triple (fun i ↦ a.pullback ⟨Sigma.mk i, continuous_sigmaMk⟩
          IsClosedEmbedding.sigmaMk.isProperMap)) := by
      let b (i : ι) := a.pullback ⟨Sigma.mk i, continuous_sigmaMk⟩
        IsClosedEmbedding.sigmaMk.isProperMap
      let K := control (fun i ↦ (b i).datum.control)
      have hK : IsCompact K := controlCompact _ (fun i ↦ (b i).datum.isCompact_control)
      have haK : a.datum.control ⊆ K := by rintro ⟨i, x⟩ hx; exact hx
      refine ⟨K, hK, haK, Set.Subset.refl _, originalIso a.source, originalIso a.target, ?_⟩
      intro x v
      change ((a.datum.enlarge K hK haK).boundary.linearEquiv x v) =
        (((triple b).datum.enlarge K hK (Set.Subset.refl _)).boundary.linearEquiv x v)
      have hl := a.datum.enlarge_apply K hK haK x v
      have hr := (triple b).datum.enlarge_apply K hK (Set.Subset.refl _) x v
      have hp := RelativeTriple.pullback_apply a.datum.boundary
        (⟨Sigma.mk x.val.1, continuous_sigmaMk⟩ : C(X x.val.1, Σ i, X i))
        ⟨x.val.2, x.property⟩ v
      exact hl.trans (hp.symm.trans hr.symm)
    have tripleZero (a : ∀ i, SupportBundleTriple (X i))
        (hzero : ∀ i, (a i).compactSupportClass = 0) :
        (triple a).compactSupportClass = 0 := by
      classical
      choose G L hL haL e he using
        (fun i ↦ (a i).compactSupportClass_eq_zero_iff.mp (hzero i))
      let : TopologicalSpace (TotalSpace Unit (triple a).source.Fiber) :=
        (triple a).source.totalTopology
      let : TopologicalSpace (TotalSpace Unit (triple a).target.Fiber) :=
        (triple a).target.totalTopology
      let H := glued G
      let : TopologicalSpace (TotalSpace Unit H.Fiber) := H.totalTopology
      let K := control L
      have hK : IsCompact K := controlCompact L hL
      have haK : (triple a).datum.control ⊆ K := by
        rintro ⟨i, x⟩ hx
        exact haL i hx
      let c : sigmaIso ((triple a).source.sum H) ((triple a).target.sum H) :=
        (sumCompare (fun i ↦ (a i).source) G).trans
          ((gluedIso (fun i ↦ (a i).source.sum (G i))
            (fun i ↦ (a i).target.sum (G i)) e).trans
              (sumCompare (fun i ↦ (a i).target) G).symm)
      apply (triple a).compactSupportClass_eq_zero_iff.mpr
      refine ⟨H, K, hK, haK, c, ?_⟩
      apply Iso.ext
      intro x
      apply LinearEquiv.ext
      intro v
      let y : ↥((L x.val.1)ᶜ) := ⟨x.val.2, x.property⟩
      have heval := congrArg (fun d ↦ d.linearEquiv y v) (he x.val.1)
      have hsum := RelativeTriple.sum_apply
        ((a x.val.1).datum.enlarge (L x.val.1) (hL x.val.1) (haL x.val.1)).boundary
        (RelativeTriple.identity (G x.val.1).Fiber (L x.val.1)ᶜ) y v
      have hlocal := (a x.val.1).datum.enlarge_apply
        (L x.val.1) (hL x.val.1) (haL x.val.1) y v.1
      have hglobal := (triple a).datum.enlarge_apply K hK haK x v.1
      have hstable := RelativeTriple.sum_apply ((triple a).datum.enlarge K hK haK).boundary
        (RelativeTriple.identity H.Fiber Kᶜ) x v
      change (e x.val.1).linearEquiv y.val v = _
      have hpair := congrArg (fun w ↦ (w, v.2)) (hlocal.trans hglobal.symm)
      exact (heval.trans hsum).trans (hpair.trans hstable.symm)
    -- Stage 6: apply these same constructions to the actual proper restriction homomorphism.
    constructor
    · intro u v huv
      apply sub_eq_zero.mp
      obtain ⟨a, ha⟩ := supportBundleTriple_compactSupportClass_surjective (u - v)
      let b (i : ι) := a.pullback ⟨Sigma.mk i, continuous_sigmaMk⟩
        IsClosedEmbedding.sigmaMk.isProperMap
      have hb (i : ι) : (b i).compactSupportClass = 0 := by
        rw [SupportBundleTriple.compactSupportClass_pullback, ha, map_sub]
        have hi := congrFun huv i
        change compactSupportKZeroPullback ⟨Sigma.mk i, continuous_sigmaMk⟩
          IsClosedEmbedding.sigmaMk.isProperMap u =
          compactSupportKZeroPullback ⟨Sigma.mk i, continuous_sigmaMk⟩
            IsClosedEmbedding.sigmaMk.isProperMap v at hi
        exact sub_eq_zero.mpr hi
      have hrec := a.compactSupportClass_eq_of_isIsomorphic _ (reconstruct a)
      exact ha.symm.trans (hrec.trans (tripleZero b hb))
    · intro z
      choose a ha using (fun i ↦ supportBundleTriple_compactSupportClass_surjective (z i))
      refine ⟨(triple a).compactSupportClass, ?_⟩
      funext i
      change compactSupportKZeroPullback ⟨Sigma.mk i, continuous_sigmaMk⟩
        IsClosedEmbedding.sigmaMk.isProperMap (triple a).compactSupportClass = z i
      rw [← SupportBundleTriple.compactSupportClass_pullback]
      exact (((triple a).pullback ⟨Sigma.mk i, continuous_sigmaMk⟩
        IsClosedEmbedding.sigmaMk.isProperMap).compactSupportClass_eq_of_isIsomorphic _
          (tripleRestrict a i)).trans (ha i) )

/-- The canonical finite-disjoint-union equivalence, with proper restriction as forward map. -/
def compactSupportKZeroSigmaEquiv [Finite ι] :
    CompactSupportKZero (Σ i, X i) ≃+ (∀ i, CompactSupportKZero (X i)) :=
  AddEquiv.ofBijective _ (compactSupportKZeroSigmaRestrict_bijective X)

end AtiyahSinger
