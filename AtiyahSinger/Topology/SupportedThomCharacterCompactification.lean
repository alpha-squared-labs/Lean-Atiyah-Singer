/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactificationCohomologyOrdinary
public import AtiyahSinger.Topology.CompactSupportChernOpenExtension
public import AtiyahSinger.Topology.ComplexThomCharacter
public import AtiyahSinger.Topology.InverseToddOperations
public import AtiyahSinger.Topology.SupportedComplexThomOpenNaturality
public import AtiyahSinger.Topology.ThomNaturality
public import AtiyahSinger.Topology.ThomOpenExtension

/-!
# The supported Thom character detected by a specified compactification

Public module ID: M2213.

An actual bundle extension to a compact ambient base carries the original
supported K-Thom symbol and the original compact-support Chern lifts through
their respective open extensions. The supported cohomological inverse uses
the same map of total spaces. If ambient ordinary cohomology detects the base
support class, the compact-base Thom formula therefore returns the original
supported formula. This explicitly retains the support comparison required
when the original base is noncompact.

Sources: SG III.12, (12.9)--(12.11), and p.255, their compact-support extension.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory Topology

universe u

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The original supported formula follows from an actual compact bundle extension and detector. -/
theorem supportedIntegral_chernCharacter_of_compactification
    {X Y : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    {F : Y → Type u} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (hE : ContinuousHermitianMetric E) (hF : ContinuousHermitianMetric F)
    (r : ℕ) (hrE : ∀ x, Module.finrank ℂ (E x) = r)
    (hrF : ∀ y, Module.finrank ℂ (F y) = r)
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (e : Iso E ((f : X → Y) *ᵖ F))
    (χX : ∀ k, CompactSupportKZero X → compactSupportCohomology ℚ X (2 * k))
    (χE : ∀ k, CompactSupportKZero (TotalSpace Unit E) →
      compactSupportCohomology ℚ (TotalSpace Unit E) (2 * k))
    (hχX : ∀ k u, compactSupportCohomologyToOnePoint ℚ X (2 * k) (χX k u) =
      reducedChernCharacterComponent (OnePoint.infty : OnePoint X) k u)
    (hχE : ∀ k u, compactSupportCohomologyToOnePoint ℚ (TotalSpace Unit E) (2 * k)
      (χE k u) = reducedChernCharacterComponent
        (OnePoint.infty : OnePoint (TotalSpace Unit E)) k u)
    (u : CompactSupportKZero X) (j : ℕ)
    (hdetect : Function.Injective (fun a : compactSupportCohomology ℚ X (2 * j) ↦
      compactSupportCohomologyToOrdinary ℚ Y (2 * j)
        (compactSupportCohomologyOpenExtension ℚ f hf (2 * j) a))) :
    hE.supportedComplexCohomologyThomIntegral r hrE (2 * j)
        ((eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace Unit E) (2 * (r + j)) ≅
              compactSupportCohomology ℚ (TotalSpace Unit E) (2 * j + 2 * r)).hom
          (χE (r + j) (hE.supportedThomHom u))) =
      ∑ i : Fin (j + 1), (-1 : ℚ) ^ (r + (j - i.val)) •
        (eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ X (2 * (j - i.val) + 2 * i.val) ≅
              compactSupportCohomology ℚ X (2 * j)).hom
          (compactSupportCohomologyAction ℚ X (2 * (j - i.val)) (2 * i.val)
            (inverseToddClassComponent E hE (j - i.val)) (χX i.val u)) := by
  let P := (f : X → Y) *ᵖ F
  let hP := hF.pullback f
  let ie : C(TotalSpace Unit E, TotalSpace Unit P) :=
    ⟨e.totalHomeomorph, e.totalHomeomorph.continuous⟩
  let q := pullbackTotalMap F f
  let G := q.comp ie
  have hq : IsOpenEmbedding q := (pullbackTotalMap_properties F f).2 hf
  have hG : IsOpenEmbedding G := hq.comp e.totalHomeomorph.isOpenEmbedding
  let U := compactSupportKZeroOpenPushforward f hf u
  let A := (compactSupportKZeroCompactEquiv Y) U
  let D (n : ℕ) := compactSupportCohomologyOpenExtension ℚ f hf n ≫
    compactSupportCohomologyToOrdinary ℚ Y n
  let cE {m n : ℕ} (h : m = n) :=
    (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit E)) h)).hom.hom
  let cF {m n : ℕ} (h : m = n) :=
    (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit F)) h)).hom.hom
  let cX {m n : ℕ} (h : m = n) :=
    (eqToIso (congrArg (compactSupportCohomology ℚ X) h)).hom.hom
  let cY {m n : ℕ} (h : m = n) :=
    (eqToIso (congrArg (singularCohomology ℚ Y) h)).hom.hom
  have hDcast {m n : ℕ} (h : m = n) (a : compactSupportCohomology ℚ X m) :
      D n (cX h a) = cY h (D m a) := by
    subst n
    rfl
  have hGcast {m n : ℕ} (h : m = n)
      (a : compactSupportCohomology ℚ (TotalSpace Unit E) m) :
      compactSupportCohomologyOpenExtension ℚ G hG n (cE h a) =
        cF h (compactSupportCohomologyOpenExtension ℚ G hG m a) := by
    subst n
    rfl
  have hYtrans {m n k : ℕ} (hmn : m = n) (hnk : n = k)
      (a : singularCohomology ℚ Y m) : cY hnk (cY hmn a) = cY (hmn.trans hnk) a := by
    subst n
    subst k
    rfl
  -- The original exterior symbol extends through exactly the same actual total-space map.
  have hKi := DFunLike.congr_fun (supportedThomHom_iso hE hP e) u
  change compactSupportKZeroHomeomorph e.totalHomeomorph (hE.supportedThomHom u) =
    hP.supportedThomHom u at hKi
  have hKq := DFunLike.congr_fun (hF.supportedThomHom_openPushforward f hf) u
  change compactSupportKZeroOpenPushforward q hq (hP.supportedThomHom u) =
    hF.supportedThomHom U at hKq
  have hK : compactSupportKZeroOpenPushforward G hG (hE.supportedThomHom u) =
      hF.supportedThomHom U := by
    have ht := DFunLike.congr_fun (compactSupportKZeroOpenPushforward_comp
      e.totalHomeomorph e.totalHomeomorph.isOpenEmbedding q hq) (hE.supportedThomHom u)
    simp only [AddMonoidHom.comp_apply, compactSupportKZeroOpenPushforward_homeomorph] at ht
    rw [hKi] at ht
    exact ht.trans hKq
  have hchars : compactSupportCohomologyOpenExtension ℚ G hG (2 * (r + j))
      (χE (r + j) (hE.supportedThomHom u)) =
    hF.compactSupportChernCharacterComponent r hrF (r + j) (hF.supportedThomHom U) := by
    apply (hF.compactSupportCohomologyToOnePoint_bijective ℚ r hrF (2 * (r + j))).injective
    rw [hF.compactSupportChernCharacterComponent_toOnePoint]
    exact (compactSupportChernCharacter_openPushforward G hG (r + j)
      (hE.supportedThomHom u) _ (hχE (r + j) _)).trans
        (congrArg (reducedChernCharacterComponent
          (OnePoint.infty : OnePoint (TotalSpace Unit F)) (r + j)) hK)
  have hbasechar (k : ℕ) : D (2 * k) (χX k u) = chernCharacterKZeroComponent Y k A :=
    compactSupportChernCharacter_openPushforward_toOrdinary f hf k u _ (hχX k u)
  have htd (k : ℕ) : inverseToddClassComponent E hE k =
      singularCohomologyPullback ℚ f (2 * k) (inverseToddClassComponent F hF k) :=
    (inverseToddClassComponent_eq_of_iso E hE P hP e k).trans
      (inverseToddClassComponent_pullback F hF f k).symm
  -- Apply the genuine detector only after identifying the original supported inverse square.
  apply hdetect
  change D (2 * j) _ = D (2 * j) _
  have hleft : D (2 * j)
      (hE.supportedComplexCohomologyThomIntegral r hrE (2 * j)
        (cE (by omega) (χE (r + j) (hE.supportedThomHom u)))) =
    hF.complexCohomologyFiberIntegral r hrF (2 * j)
      (cF (by omega) (hF.compactSupportChernCharacterComponent r hrF (r + j)
        (hF.supportedThomHom U))) := by
    have hnat := supportedComplexCohomologyThomIntegral_openExtension hE hF r hrE hrF
      f hf e.linearEquiv G (fun _ ↦ rfl) hG (2 * j)
        (cE (show 2 * (r + j) = 2 * j + 2 * r by omega)
          (χE (r + j) (hE.supportedThomHom u)))
    have h := congrArg (compactSupportCohomologyToOrdinary ℚ Y (2 * j)) hnat
    rw [hF.supportedComplexCohomologyThomIntegral_compact,
      hGcast (show 2 * (r + j) = 2 * j + 2 * r by omega), hchars] at h
    exact h.symm
  rw [hleft]
  have hformula := hF.fiberIntegral_chernCharacter_supportedThom r hrF A j
  have hU : (compactSupportKZeroCompactEquiv Y).symm A = U :=
    (compactSupportKZeroCompactEquiv Y).symm_apply_apply U
  rw [hU] at hformula
  rw [hformula]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  let k := j - i.val
  have hdegree : 2 * k + 2 * i.val = 2 * j := by dsimp only [k]; omega
  have hterm : D (2 * j)
      (cX hdegree (compactSupportCohomologyAction ℚ X (2 * k) (2 * i.val)
        (inverseToddClassComponent E hE k) (χX i.val u))) =
    cY hdegree (singularCohomologyCup ℚ Y (2 * k) (2 * i.val)
      (inverseToddClassComponent F hF k) (chernCharacterKZeroComponent Y i.val A)) := by
    rw [hDcast hdegree, htd]
    change cY hdegree (compactSupportCohomologyToOrdinary ℚ Y (2 * k + 2 * i.val)
      (compactSupportCohomologyOpenExtension ℚ f hf (2 * k + 2 * i.val) _)) = _
    rw [compactSupportCohomologyOpenExtension_toOrdinary_action]
    exact congrArg (fun a ↦ cY hdegree (singularCohomologyCup ℚ Y (2 * k)
      (2 * i.val) (inverseToddClassComponent F hF k) a)) (hbasechar i.val)
  change cY (by omega) (singularCohomologyEvenCup ℚ Y i.val k
    (chernCharacterKZeroComponent Y i.val A) (hF.complexThomDefectComponent r hrF k)) =
      (-1 : ℚ) ^ (r + k) • D (2 * j)
        (cX hdegree (compactSupportCohomologyAction ℚ X (2 * k) (2 * i.val)
          (inverseToddClassComponent E hE k) (χX i.val u)))
  rw [hterm, hF.complexThomDefectComponent_eq_inverseTodd]
  change cY (by omega) (cY (by omega) (singularCohomologyCup ℚ Y (2 * i.val) (2 * k)
    (chernCharacterKZeroComponent Y i.val A) ((-1 : ℚ) ^ (r + k) •
      inverseToddClassComponent F hF k))) = _
  rw [map_smul, map_smul, map_smul]
  apply congrArg (((-1 : ℚ) ^ (r + k)) • ·)
  rw [hYtrans (show 2 * i.val + 2 * k = 2 * (i.val + k) by omega)
    (show 2 * (i.val + k) = 2 * j by dsimp only [k]; omega)]
  have hcomm := singularCohomologyCup_comm ℚ Y (2 * i.val) (2 * k)
    (chernCharacterKZeroComponent Y i.val A) (inverseToddClassComponent F hF k)
  have hsign : (-1 : ℚ) ^ ((2 * i.val) * (2 * k)) = 1 := by
    rw [Nat.mul_assoc, pow_mul]
    norm_num
  rw [hsign, one_smul] at hcomm
  have hc := congrArg (cY hdegree) hcomm
  change cY hdegree (cY (Nat.add_comm (2 * i.val) (2 * k)) _) = _ at hc
  rw [hYtrans (Nat.add_comm (2 * i.val) (2 * k)) hdegree] at hc
  exact hc

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
