/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportChernAction

/-!
# Chern character and coefficients on real bundle total spaces

Public module ID: M2034.

Cofinal disks in the original real metric supply detection in the relative
one-point pair, including the product used by the graph action. The same
proper graph then identifies the compact-base K action with the finite cup
convolution. Support is retained until this relative detection is applied.

Source: SG III.11--12. The comparison between the specified support colimit
and relative singular model is the project's explicit model implementation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory OnePoint Opposite TopologicalSpace

attribute [local instance] t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

universe u

variable (r : ℕ) {B : Type u} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  (E : B → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  [hMetric : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) E]

/-- The same positive-radius real metric disks have cofinal contractible infinity complements. -/
theorem cofinal_contractible_onePoint_complements_realBundle :
    ∀ K : Compacts (TotalSpace (EuclideanSpace ℝ (Fin r)) E),
      ∃ L : Compacts (TotalSpace (EuclideanSpace ℝ (Fin r)) E), K ≤ L ∧
        ContractibleSpace ((((↑) : TotalSpace (EuclideanSpace ℝ (Fin r)) E →
          OnePoint (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) ''
          (L : Set (TotalSpace (EuclideanSpace ℝ (Fin r)) E)))ᶜ :
            Set (OnePoint (TotalSpace (EuclideanSpace ℝ (Fin r)) E))) := by
  intro K
  let F := EuclideanSpace ℝ (Fin r)
  let T := TotalSpace F E
  have hnorm : Continuous (fun v : T ↦ ‖v.snd‖) :=
    Poincare.VectorBundle.continuous_fiber_norm
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove_image hnorm.continuousOn
  let a : ℝ := max b 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdisk : IsCompact {v : T | ‖v.snd‖ ≤ a} := by
    simpa using Poincare.VectorBundle.isCompact_disk_over
      (F := F) (E := E) (K := Set.univ) isCompact_univ a
  -- Compactness bounds the original norm; the original radial homotopy contracts the complement.
  refine ⟨⟨{v | ‖v.snd‖ ≤ a}, hdisk⟩, ?_, ?_⟩
  · intro v hv
    exact (hb (Set.mem_image_of_mem _ hv)).trans (le_max_left _ _)
  · exact contractibleSpace_bundleInfinityNeighborhood F E a ha

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original real-bundle supported character sends graph action to the cup convolution. -/
theorem bundleCompactSupportChernCharacterComponent_action
    (f : C(TotalSpace (EuclideanSpace ℝ (Fin r)) E, X)) (u : ComplexKZero X)
    (a : CompactSupportKZero (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) (k : ℕ) :
    bundleCompactSupportChernCharacterComponent r E k
        (complexKZeroCompactSupportAction f u a) =
      ∑ i : Fin (k + 1),
        (eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace (EuclideanSpace ℝ (Fin r)) E)
              (2 * i.val + 2 * (k - i.val)) ≅
              compactSupportCohomology ℚ
                (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (2 * k)).hom
          (compactSupportCohomologyAction ℚ
            (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (2 * i.val) (2 * (k - i.val))
            (singularCohomologyPullback ℚ f (2 * i.val)
              (chernCharacterKZeroComponent X i.val u))
            (bundleCompactSupportChernCharacterComponent r E (k - i.val) a)) := by
  classical
  -- The product is the total space of the same bundle pulled back by the second projection.
  let V := EuclideanSpace ℝ (Fin r)
  let p : C(X × B, B) := ContinuousMap.snd
  let P := (p : X × B → B) *ᵖ E
  let : ∀ z, NormedAddCommGroup (((p : X × B → B) *ᵖ E) z) :=
    fun z ↦ inferInstanceAs (NormedAddCommGroup (E (p z)))
  let : ∀ z, InnerProductSpace ℝ (((p : X × B → B) *ᵖ E) z) :=
    fun z ↦ inferInstanceAs (InnerProductSpace ℝ (E (p z)))
  let : FiberBundle V P := FiberBundle.pullback (F := V) (E := E) p
  let : VectorBundle ℝ V P := VectorBundle.pullback ℝ (F := V) (E := E) p
  let : IsContinuousRiemannianBundle V P := by
    obtain ⟨g, hg, hinner⟩ := hMetric.exists_continuous
    refine ⟨⟨fun z ↦ g (p z), ?_, fun z v w ↦ hinner (p z) v w⟩⟩
    apply continuous_iff_continuousAt.mpr
    intro z
    apply (FiberBundle.continuousAt_totalSpace (V →L[ℝ] V →L[ℝ] ℝ) _).mpr
    refine ⟨continuousAt_id, ?_⟩
    have hc := ((FiberBundle.continuousAt_totalSpace
      (V →L[ℝ] V →L[ℝ] ℝ) _).mp (hg.continuousAt (x := p z))).2
    convert hc.comp (continuous_snd.continuousAt) using 1
    ext x v w
    change (ContinuousLinearMap.inCoordinates V P (V →L[ℝ] ℝ)
      (fun x ↦ P x →L[ℝ] ℝ) z x z x (g (p x))) v w =
      (ContinuousLinearMap.inCoordinates V E (V →L[ℝ] ℝ)
        (fun x ↦ E x →L[ℝ] ℝ) (p z) (p x) (p z) (p x) (g (p x))) v w
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
    have hsym (a : V) : (trivializationAt V P z).symmL ℝ x a =
        (trivializationAt V E (p z)).symmL ℝ (p x) a := by
      by_cases hx : p x ∈ (trivializationAt V E (p z)).baseSet
      · have hx' : x ∈ (trivializationAt V P z).baseSet := hx
        rw [(trivializationAt V P z).symmL_apply hx',
          (trivializationAt V E (p z)).symmL_apply hx]
        apply ((trivializationAt V E (p z)).linearEquivAt ℝ (p x) hx).injective
        change (trivializationAt V E (p z)
          ⟨p x, (trivializationAt V P z).symm x a⟩).2 =
          (trivializationAt V E (p z)
            ⟨p x, (trivializationAt V E (p z)).symm (p x) a⟩).2
        exact (congrArg Prod.snd ((trivializationAt V P z).apply_mk_symm hx' a)).trans
          (congrArg Prod.snd ((trivializationAt V E (p z)).apply_mk_symm hx a)).symm
      · have hx' : x ∉ (trivializationAt V P z).baseSet := hx
        rw [(trivializationAt V P z).symmL_apply_of_notMem hx',
          (trivializationAt V E (p z)).symmL_apply_of_notMem hx]
    erw [hsym v]
    simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply]
    erw [hom_trivializationAt_baseSet, hom_trivializationAt_baseSet]
    erw [hom_trivializationAt_apply, hom_trivializationAt_apply]
    have htP : (trivializationAt ℝ (fun _ : X × B ↦ ℝ) z).baseSet = Set.univ := rfl
    have htE : (trivializationAt ℝ (fun _ : B ↦ ℝ) (p z)).baseSet = Set.univ := rfl
    rw [htP, htE]
    by_cases hx : p x ∈ (trivializationAt V E (p z)).baseSet
    · have hx' : x ∈ (trivializationAt V P z).baseSet := hx
      simp only [Set.mem_inter_iff, Set.mem_univ, and_true, hx, hx', ite_true,
        ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
      erw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt ℝ (fun _ : X × B ↦ ℝ) z) (htP ▸ Set.mem_univ x),
        Trivialization.continuousLinearMapAt_apply_of_mem ℝ
          (trivializationAt ℝ (fun _ : B ↦ ℝ) (p z)) (htE ▸ Set.mem_univ (p x))]
      change ((g (p x)) ((trivializationAt V E (p z)).symmL ℝ (p x) v))
        ((trivializationAt V P z).symmL ℝ x w) =
        ((g (p x)) ((trivializationAt V E (p z)).symmL ℝ (p x) v))
          ((trivializationAt V E (p z)).symmL ℝ (p x) w)
      rw [hsym w]
    · have hx' : x ∉ (trivializationAt V P z).baseSet := hx
      simp only [Set.mem_inter_iff, Set.mem_univ, and_true, hx, hx', ite_false]
  let e : TotalSpace V P ≃ₜ X × TotalSpace V E :=
    { toFun := fun z ↦ (z.proj.1, ⟨z.proj.2, z.snd⟩)
      invFun := fun z ↦ ⟨(z.1, z.2.proj), z.2.snd⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun :=
        (continuous_fst.comp (Pullback.continuous_proj V E p)).prodMk
          (Pullback.continuous_lift V E p)
      continuous_invFun := by
        apply (inducing_pullbackTotalSpaceEmbedding V E p).continuous_iff.mpr
        exact (continuous_fst.prodMk
          ((FiberBundle.continuous_proj V E).comp continuous_snd)).prodMk continuous_snd }
  have hdetect (n : ℕ) : Function.Injective (relativeSingularCohomologyPullback ℚ
      (compactSupportSliceCollapse X (TotalSpace V E))
      (compactSupportSliceCollapse_mapsTo X (TotalSpace V E)) n) := by
    apply relativeSingularCohomologyPullback_sliceCollapse_injective ℚ X (TotalSpace V E)
      (cofinal_contractible_onePoint_complements_realBundle r E) n
    exact (compactSupportCohomologyToOnePoint_bijective_of_contractible_complements ℚ
      (cofinal_contractible_onePoint_complements_of_homeomorph e
        (cofinal_contractible_onePoint_complements_realBundle r P)) n).surjective
  let Y := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let G := f.prodMk (ContinuousMap.id Y)
  let hG : IsProperMap G := isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
  let s : C(X × Y, Y) := ContinuousMap.snd
  let hs : IsProperMap s := isProperMap_snd_of_compactSpace
  let u₀ := (compactSupportKZeroCompactEquiv X).symm u
  let β (n : ℕ) := bundleCompactSupportChernCharacterComponent r E n a
  let C : compactSupportCohomology ℚ (X × Y) (2 * k) :=
    ∑ i : Fin (k + 1),
      (eqToIso (by congr 1; omega) :
          compactSupportCohomology ℚ (X × Y) (2 * i.val + 2 * (k - i.val)) ≅
            compactSupportCohomology ℚ (X × Y) (2 * k)).hom
        (compactSupportCohomologyAction ℚ (X × Y) (2 * i.val) (2 * (k - i.val))
          (singularCohomologyPullback ℚ ContinuousMap.fst (2 * i.val)
            (chernCharacterKZeroComponent X i.val (compactSupportKZeroToAbsolute u₀)))
          (compactSupportCohomologyProperPullback ℚ s hs (2 * (k - i.val)) (β (k - i.val))))
  have hC : compactSupportCohomologyToOnePoint ℚ (X × Y) (2 * k) C =
      reducedChernCharacterComponent (∞ : OnePoint (X × Y)) k
        (compactSupportKZeroExternalProduct u₀ a) :=
    compactSupportChernCharacter_externalProduct_toOnePoint
      hdetect
      u₀ a β (fun n ↦ bundleCompactSupportChernCharacterComponent_toOnePoint r E n a) k
  -- The same proper graph pulls back both original reduced classes and the cohomological product.
  have hmain : bundleCompactSupportChernCharacterComponent r E k
      (complexKZeroCompactSupportAction f u a) =
      compactSupportCohomologyProperPullback ℚ G hG (2 * k) C := by
    apply (compactSupportCohomologyToOnePoint_bundle_bijective ℚ r E (2 * k)).injective
    rw [bundleCompactSupportChernCharacterComponent_toOnePoint,
      compactSupportCohomologyProperPullback_toOnePoint, hC]
    exact (reducedChernCharacterComponent_pullback (∞ : OnePoint Y)
      (∞ : OnePoint (X × Y)) (properOnePointMap G hG) rfl
      (compactSupportKZeroExternalProduct u₀ a) k).symm
  have hroundtrip (n : ℕ) (c : compactSupportCohomology ℚ Y n) :
      compactSupportCohomologyProperPullback ℚ G hG n
        (compactSupportCohomologyProperPullback ℚ s hs n c) = c := by
    -- On the original representative the twice-pulled support is literally K, since snd ∘ G = id.
    obtain ⟨K, γ, rfl⟩ := compactSupportCohomology_exists_representative ℚ Y n c
    rw [compactSupportCohomologyProperPullback_representative,
      compactSupportCohomologyProperPullback_representative]
    have hsK : Set.MapsTo s ((properCompactPreimage s hs K : Set (X × Y))ᶜ)
        ((K : Set Y)ᶜ) := fun _ hx ↦ hx
    have hGK : Set.MapsTo G ((K : Set Y)ᶜ)
        ((properCompactPreimage s hs K : Set (X × Y))ᶜ) := fun _ hx ↦ hx
    have hcomp := congrArg (fun t ↦ t γ)
      (relativeSingularCohomologyPullback_comp ℚ G s hGK hsK n)
    simp only [ModuleCat.comp_apply] at hcomp
    change compactSupportCohomologyClass ℚ Y K n
      (relativeSingularCohomologyPullback ℚ G hGK n
        (relativeSingularCohomologyPullback ℚ s hsK n γ)) =
      compactSupportCohomologyClass ℚ Y K n γ
    rw [← hcomp]
    change compactSupportCohomologyClass ℚ Y K n
      ((relativeSingularCohomologyFunctor ℚ Y n).map (𝟙 (op ((K : Set Y)ᶜ))) γ) = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hcast {p q : ℕ} (hpq : p = q) (c : compactSupportCohomology ℚ (X × Y) p) :
      compactSupportCohomologyProperPullback ℚ G hG q
        ((eqToIso (by rw [hpq]) : compactSupportCohomology ℚ (X × Y) p ≅
          compactSupportCohomology ℚ (X × Y) q).hom c) =
      (eqToIso (by rw [hpq]) : compactSupportCohomology ℚ Y p ≅
        compactSupportCohomology ℚ Y q).hom
        (compactSupportCohomologyProperPullback ℚ G hG p c) := by
    subst q
    rfl
  have hu : compactSupportKZeroToAbsolute u₀ = u :=
    (compactSupportKZeroCompactEquiv X).apply_symm_apply u
  rw [hmain]
  dsimp only [C]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcast (by omega), compactSupportCohomologyProperPullback_action, hroundtrip, hu]
  have hfst : singularCohomologyPullback ℚ G (2 * i.val)
      (singularCohomologyPullback ℚ (ContinuousMap.fst : C(X × Y, X)) (2 * i.val)
        (chernCharacterKZeroComponent X i.val u)) =
      singularCohomologyPullback ℚ f (2 * i.val) (chernCharacterKZeroComponent X i.val u) := by
    change (((singularCohomologyFunctor ℚ (2 * i.val)).map _ ≫
      (singularCohomologyFunctor ℚ (2 * i.val)).map _) _) = _
    rw [← Functor.map_comp]
    rfl
  rw [hfst]

end AtiyahSinger
