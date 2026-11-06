/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexBundleInfinityCofinality
public import AtiyahSinger.Topology.CompactSupportCohomologyProperPullback
public import AtiyahSinger.Topology.CompactSupportModule
public import AtiyahSinger.Topology.ReducedChernCharacterNaturality

/-!
# Chern character and the original compact-base support action

Public module ID: M1652.

The actual finite-product collapse compares the supported external product
with ordinary multiplication on the compact slice. The proven relative
detection and the original proper-pullback square then recover the supported
identity, before any support is forgotten. The finite convolution retains the
original ordering and exact even-degree transports.

Source: SG III.11 and III.12 for Chern-character multiplication and Thom
coefficients. The explicit comparison of these singular and K models is a
project supplement to that standard argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits OnePoint TopologicalSpace

universe u

variable {X Y : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original supported external product has the finite Chern convolution in its point pair. -/
theorem compactSupportChernCharacter_externalProduct_toOnePoint
    (hdetect : ∀ n, Function.Injective (relativeSingularCohomologyPullback ℚ
      (compactSupportSliceCollapse X Y) (compactSupportSliceCollapse_mapsTo X Y) n))
    (a : CompactSupportKZero X) (b : CompactSupportKZero Y)
    (β : ∀ k, compactSupportCohomology ℚ Y (2 * k))
    (hβ : ∀ k, compactSupportCohomologyToOnePoint ℚ Y (2 * k) (β k) =
      reducedChernCharacterComponent (∞ : OnePoint Y) k b) (k : ℕ) :
    compactSupportCohomologyToOnePoint ℚ (X × Y) (2 * k)
        (∑ i : Fin (k + 1),
          (eqToIso (by congr 1; omega) :
              compactSupportCohomology ℚ (X × Y) (2 * i.val + 2 * (k - i.val)) ≅
                compactSupportCohomology ℚ (X × Y) (2 * k)).hom
            (compactSupportCohomologyAction ℚ (X × Y) (2 * i.val) (2 * (k - i.val))
              (singularCohomologyPullback ℚ ContinuousMap.fst (2 * i.val)
                (chernCharacterKZeroComponent X i.val (compactSupportKZeroToAbsolute a)))
              (compactSupportCohomologyProperPullback ℚ (ContinuousMap.snd : C(X × Y, Y))
                isProperMap_snd_of_compactSpace (2 * (k - i.val)) (β (k - i.val))))) =
      reducedChernCharacterComponent (∞ : OnePoint (X × Y)) k
        (compactSupportKZeroExternalProduct a b) := by
  let Z := X × OnePoint Y
  let q := compactSupportSliceCollapse X Y
  let j := compactSupportSliceInclusion X Y
  let A : Set Z := (Set.range j)ᶜ
  let s : C(X × Y, Y) := ContinuousMap.snd
  let hs : IsProperMap s := isProperMap_snd_of_compactSpace
  let t : C(Z, OnePoint X × OnePoint Y) :=
    (⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩ : C(X, OnePoint X)).prodMap
      (ContinuousMap.id (OnePoint Y))
  let D (n : ℕ) := relativeSingularCohomologyPullback ℚ q
    (compactSupportSliceCollapse_mapsTo X Y) n ≫ relativeSingularCohomologyToOrdinary ℚ A n
  -- The original product K class has its prescribed ordinary product on this same slice.
  have hK : complexKZeroPullback q (compactSupportKZeroExternalProduct a b).val =
      complexKZeroPullback (ContinuousMap.fst : C(Z, X)) (compactSupportKZeroToAbsolute a) *
        complexKZeroPullback (ContinuousMap.snd : C(Z, OnePoint Y)) b.val := by
    change complexKZeroPullback (onePointProductCollapseMap.comp t)
      (compactSupportKZeroExternalProduct a b).val = _
    rw [complexKZeroPullback_comp, AddMonoidHom.comp_apply,
      compactSupportKZeroExternalProduct_pullback, complexKZeroExternalProduct_natural]
    rw [show complexKZeroPullback (ContinuousMap.id (OnePoint Y)) b.val = b.val from by
      change kZeroMap (RingHom.id _) b.val = b.val
      rw [kZeroMap_id]
      rfl]
    rfl
  have hsquare : (properOnePointMap s hs).comp q = (ContinuousMap.snd : C(Z, OnePoint Y)) := by
    ext z
    cases heq : z.2 using OnePoint.rec with
    | infty => simp [q, compactSupportSliceCollapse, onePointProductCollapseMap,
        onePointProductCollapse, heq, properOnePointMap]
    | coe y => simp [q, compactSupportSliceCollapse, onePointProductCollapseMap,
        onePointProductCollapse, heq, properOnePointMap, s]
  -- Proper projection retains the same second-factor supported class before ordinary comparison.
  have hsecond (n : ℕ) (c : compactSupportCohomology ℚ Y n) :
      D n (compactSupportCohomologyToOnePoint ℚ (X × Y) n
        (compactSupportCohomologyProperPullback ℚ s hs n c)) =
      singularCohomologyPullback ℚ (ContinuousMap.snd : C(Z, OnePoint Y)) n
        (relativeSingularCohomologyToOrdinary ℚ ({∞} : Set (OnePoint Y)) n
          (compactSupportCohomologyToOnePoint ℚ Y n c)) := by
    rw [compactSupportCohomologyProperPullback_toOnePoint]
    change relativeSingularCohomologyToOrdinary ℚ A n
      (relativeSingularCohomologyPullback ℚ q _ n
        (relativeSingularCohomologyPullback ℚ (properOnePointMap s hs) _ n _)) = _
    have hInf : Set.MapsTo (properOnePointMap s hs) ({∞} : Set (OnePoint (X × Y)))
        ({∞} : Set (OnePoint Y)) := by
      rintro z rfl
      rfl
    have hcomp := congrArg (fun f ↦ f (compactSupportCohomologyToOnePoint ℚ Y n c))
      (relativeSingularCohomologyPullback_comp ℚ q (properOnePointMap s hs)
        (compactSupportSliceCollapse_mapsTo X Y) hInf n)
    simp only [ModuleCat.comp_apply] at hcomp
    rw [← hcomp]
    have hnat := relativeSingularCohomologyPullback_toOrdinary ℚ
      ((properOnePointMap s hs).comp q)
      (show Set.MapsTo ((properOnePointMap s hs).comp q) A {∞} from
        fun z hz ↦ by
          have hz' := compactSupportSliceCollapse_mapsTo X Y hz
          change q z = ∞ at hz'
          change properOnePointMap s hs (q z) = ∞
          rw [hz']
          rfl) n
    have heq := congrArg (fun f ↦ f (compactSupportCohomologyToOnePoint ℚ Y n c)) hnat
    simpa only [ModuleCat.comp_apply, hsquare] using heq
  have hterm (p r : ℕ) (c : singularCohomology ℚ X p)
      (d : compactSupportCohomology ℚ Y r) :
      D (p + r) (compactSupportCohomologyToOnePoint ℚ (X × Y) (p + r)
        (compactSupportCohomologyAction ℚ (X × Y) p r
          (singularCohomologyPullback ℚ ContinuousMap.fst p c)
          (compactSupportCohomologyProperPullback ℚ s hs r d))) =
      singularCohomologyCup ℚ Z p r
        (singularCohomologyPullback ℚ ContinuousMap.fst p c)
        (singularCohomologyPullback ℚ ContinuousMap.snd r
          (relativeSingularCohomologyToOrdinary ℚ ({∞} : Set (OnePoint Y)) r
            (compactSupportCohomologyToOnePoint ℚ Y r d))) := by
    have hfst : singularCohomologyPullback ℚ j p
        (singularCohomologyPullback ℚ (ContinuousMap.fst : C(Z, X)) p c) =
        singularCohomologyPullback ℚ (ContinuousMap.fst : C(X × Y, X)) p c := by
      change (((singularCohomologyFunctor ℚ p).map _ ≫
        (singularCohomologyFunctor ℚ p).map _) c) = _
      rw [← Functor.map_comp]
      rfl
    change relativeSingularCohomologyToOrdinary ℚ A (p + r)
      (relativeSingularCohomologyPullback ℚ q _ (p + r) _) = _
    rw [compactSupportCohomologyToSlice_onePoint]
    change relativeSingularCohomologyToOrdinary ℚ A (p + r)
      (compactSupportCohomologyToCompactification ℚ j
        (isOpenEmbedding_compactSupportSliceInclusion X Y) (p + r) _) = _
    rw [← hfst, compactSupportCohomologyToCompactification_action,
      relativeSingularCohomologyToOrdinary_action]
    have hd := hsecond r d
    change relativeSingularCohomologyToOrdinary ℚ A r
      (relativeSingularCohomologyPullback ℚ q _ r _) = _ at hd
    rw [compactSupportCohomologyToSlice_onePoint] at hd
    exact congrArg (singularCohomologyCup ℚ Z p r
      (singularCohomologyPullback ℚ ContinuousMap.fst p c)) hd
  have hcast {p r : ℕ} (hpr : p = r) (c : compactSupportCohomology ℚ (X × Y) p) :
      D r (compactSupportCohomologyToOnePoint ℚ (X × Y) r
        ((eqToIso (by rw [hpr]) : compactSupportCohomology ℚ (X × Y) p ≅
          compactSupportCohomology ℚ (X × Y) r).hom c)) =
      (eqToIso (by rw [hpr]) : singularCohomology ℚ Z p ≅ singularCohomology ℚ Z r).hom
        (D p (compactSupportCohomologyToOnePoint ℚ (X × Y) p c)) := by
    subst r
    rfl
  -- Detection occurs in the original relative pair; its retraction permits ordinary multiplication.
  apply hdetect (2 * k)
  apply relativeSingularCohomologyToOrdinary_slice_injective ℚ X Y (2 * k)
  change D (2 * k) (compactSupportCohomologyToOnePoint ℚ (X × Y) (2 * k) _) =
    D (2 * k) (reducedChernCharacterComponent (∞ : OnePoint (X × Y)) k _)
  have hright : D (2 * k) (reducedChernCharacterComponent (∞ : OnePoint (X × Y)) k
        (compactSupportKZeroExternalProduct a b)) =
      chernCharacterKZeroComponent Z k
        (complexKZeroPullback ContinuousMap.fst (compactSupportKZeroToAbsolute a) *
          complexKZeroPullback ContinuousMap.snd b.val) := by
    have hnat := relativeSingularCohomologyPullback_toOrdinary ℚ q
      (compactSupportSliceCollapse_mapsTo X Y) (2 * k)
    have heq := congrArg (fun f ↦ f (reducedChernCharacterComponent
      (∞ : OnePoint (X × Y)) k (compactSupportKZeroExternalProduct a b))) hnat
    change D (2 * k) _ = singularCohomologyPullback ℚ q (2 * k)
      (relativeSingularCohomologyToOrdinary ℚ {∞} (2 * k) _) at heq
    rw [heq, reducedChernCharacterComponent_toOrdinary,
      ← chernCharacterKZeroComponent_pullback, hK]
  rw [hright, chernCharacterKZeroComponent_mul]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcast (by omega), hterm, hβ, reducedChernCharacterComponent_toOrdinary,
    chernCharacterKZeroComponent_pullback, chernCharacterKZeroComponent_pullback]
  let c := singularCohomologyCup ℚ Z (2 * i.val) (2 * (k - i.val))
      (singularCohomologyPullback ℚ ContinuousMap.fst (2 * i.val)
        (chernCharacterKZeroComponent X i.val (compactSupportKZeroToAbsolute a)))
      (singularCohomologyPullback ℚ ContinuousMap.snd (2 * (k - i.val))
        (chernCharacterKZeroComponent (OnePoint Y) (k - i.val) b.val))
  change (eqToHom (by congr 1; omega) :
    singularCohomology ℚ Z (2 * i.val + 2 * (k - i.val)) ⟶
      singularCohomology ℚ Z (2 * k)) c =
    (eqToHom (by congr 1; omega) : singularCohomology ℚ Z (2 * (i.val + (k - i.val))) ⟶
      singularCohomology ℚ Z (2 * k))
      ((eqToHom (by congr 1; omega) : singularCohomology ℚ Z (2 * i.val + 2 * (k - i.val)) ⟶
        singularCohomology ℚ Z (2 * (i.val + (k - i.val)))) c)
  rw [← ModuleCat.comp_apply, eqToHom_trans]

namespace ComplexBundle.ContinuousHermitianMetric

open Bundle Opposite

attribute [local instance] ComplexBundle.t2Space_totalSpace
  ComplexBundle.locallyCompactSpace_totalSpace

variable {B : Type u} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  {E : B → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [ComplexBundle.IsFiniteRank E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original supported character sends the compact-base graph action to cup convolution. -/
theorem compactSupportChernCharacterComponent_action
    (h : ContinuousHermitianMetric E) (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r)
    (f : C(TotalSpace Unit E, X)) (u : ComplexKZero X)
    (a : CompactSupportKZero (TotalSpace Unit E)) (k : ℕ) :
    h.compactSupportChernCharacterComponent r hr k (complexKZeroCompactSupportAction f u a) =
      ∑ i : Fin (k + 1),
        (eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace Unit E) (2 * i.val + 2 * (k - i.val)) ≅
              compactSupportCohomology ℚ (TotalSpace Unit E) (2 * k)).hom
          (compactSupportCohomologyAction ℚ (TotalSpace Unit E) (2 * i.val) (2 * (k - i.val))
            (singularCohomologyPullback ℚ f (2 * i.val) (chernCharacterKZeroComponent X i.val u))
            (h.compactSupportChernCharacterComponent r hr (k - i.val) a)) := by
  let Y := TotalSpace Unit E
  let G := f.prodMk (ContinuousMap.id Y)
  let hG : IsProperMap G := isProperMap_of_comp_of_t2 G.continuous continuous_snd isProperMap_id
  let s : C(X × Y, Y) := ContinuousMap.snd
  let hs : IsProperMap s := isProperMap_snd_of_compactSpace
  let u₀ := (compactSupportKZeroCompactEquiv X).symm u
  let β (n : ℕ) := h.compactSupportChernCharacterComponent r hr n a
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
      (h.relativeSingularCohomologyPullback_sliceCollapse_injective X ℚ r hr)
      u₀ a β (fun n ↦ h.compactSupportChernCharacterComponent_toOnePoint r hr n a) k
  -- The same proper graph pulls back both original reduced classes and the cohomological product.
  have hmain : h.compactSupportChernCharacterComponent r hr k
      (complexKZeroCompactSupportAction f u a) =
      compactSupportCohomologyProperPullback ℚ G hG (2 * k) C := by
    apply (h.compactSupportCohomologyToOnePoint_bijective ℚ r hr (2 * k)).injective
    rw [h.compactSupportChernCharacterComponent_toOnePoint,
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

end ComplexBundle.ContinuousHermitianMetric

end AtiyahSinger
