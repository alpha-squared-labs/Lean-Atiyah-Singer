/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleCompactSupportCharacter
public import AtiyahSinger.Topology.CompactSupportChernExternal
public import AtiyahSinger.Topology.ComplexificationExternalThomIntegral

/-!
# Supported Chern convolution under real complexification

Public module ID: M1726.

The original supported character is represented on the original zero section.
Pulling its external square along the proper real/imaginary pair and integrating
against the same complex Thom orientation gives the shifted cup convolution of
its original real Thom coefficients. The low components vanish before support
is forgotten. The detector hypothesis must be proved for the actual total space.

Source: multiplicativity of the Chern character and the oriented Thom product;
the comparison of the fixed support and one-point models is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle

attribute [local instance] t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
open scoped TensorProduct

universe u

variable {m : ℕ} {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  (o : ∀ x, Orientation ℝ (E x) (Fin (2 * m)))
  (ho : IsLocallyCompatibleBundleOrientation (2 * m) E o)
  [T2Space X] [CompactSpace X]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]

set_option maxHeartbeats 1000000 in
-- Preserve the same compact-support objects and all dependent degree transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The supported self-product integrates to the signed convolution of the real Thom defects. -/
theorem complexificationCohomologyFiberIntegral_chern_square
    (hV : letI := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (hr : ∀ x, Module.finrank ℂ (ℂ ⊗[ℝ] E x) = 2 * m) :
    let F := fun x ↦ ℂ ⊗[ℝ] E x
    letI := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
    letI := isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
    letI : ∀ x, NormedAddCommGroup (F x) := hV.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (F x) := hV.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (F x) := hV.realFiberInnerProductSpace
    letI := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
    letI := hV.realNativeFiberBundle (2 * m) hr
    letI := hV.realNativeVectorBundle (2 * m) hr
    letI := hV.realNativeRiemannianBundle (2 * m) hr
    let TE := TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E
    let TF := TotalSpace (EuclideanSpace ℝ (Fin (2 * (2 * m)))) F
    ∀ (e : ∀ x, F x ≃L[ℝ] E x × E x)
      (_he : ∀ x, (e x).toLinearEquiv = complexificationReIm (E x))
      (q₁ q₂ : C(TF, TE))
      (_hq₁ : ∀ x v, q₁ ⟨x, v⟩ = ⟨x, (e x v).1⟩)
      (_hq₂ : ∀ x v, q₂ ⟨x, v⟩ = ⟨x, (e x v).2⟩)
      (hp : IsProperMap (q₁.prodMk q₂))
      (a : CompactSupportKZero TE)
      (_hvan : ∀ k, k < m → bundleCompactSupportChernCharacterComponent (2 * m) E k a = 0)
      (_hdetect : ∀ k, Function.Injective (fun z : relativeSingularCohomology ℚ
        ({OnePoint.infty} : Set (OnePoint (TE × TE))) (2 * k) ↦
        singularCohomologyPullback ℚ onePointProductCollapseMap (2 * k)
          (relativeSingularCohomologyToOrdinary ℚ {OnePoint.infty} (2 * k) z)))
      (j : ℕ),
    let O := (geometricCohomologyOrientation (2 * m) E o ho).rationalization
    let δ (n : ℕ) := compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * n)
      ((eqToIso (by congr 1; omega) : compactSupportCohomology ℚ TE (2 * (m + n)) ≅
        compactSupportCohomology ℚ TE (2 * n + 2 * m)).hom
          (bundleCompactSupportChernCharacterComponent (2 * m) E (m + n) a))
    compactSupportCohomologyFiberIntegral ℚ (2 * (2 * m)) F
      (hV.complexCohomologyOrientation (2 * m) hr).rationalization (2 * j)
      ((eqToIso (by congr 1; omega) :
        compactSupportCohomology ℚ TF (2 * (2 * m + j)) ≅
          compactSupportCohomology ℚ TF (2 * j + 2 * (2 * m))).hom
        (bundleCompactSupportChernCharacterComponent (2 * (2 * m)) F (2 * m + j)
          (compactSupportKZeroPullback (q₁.prodMk q₂) hp
            (compactSupportKZeroExternalProduct a a)))) =
      (-1 : ℚ) ^ m • ∑ i : Fin (j + 1),
        (eqToIso (by congr 1; omega) :
          singularCohomology ℚ X (2 * (i.val + (j - i.val))) ≅
            singularCohomology ℚ X (2 * j)).hom
          (singularCohomologyEvenCup ℚ X i.val (j - i.val) (δ i.val) (δ (j - i.val))) := by
  classical
  let F := fun x ↦ ℂ ⊗[ℝ] E x
  let := complexificationTopology (EuclideanSpace ℝ (Fin (2 * m))) E
  let := isFiniteRank_complexification (EuclideanSpace ℝ (Fin (2 * m))) E
  let : ∀ x, NormedAddCommGroup (F x) := hV.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (F x) := hV.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (F x) := hV.realFiberInnerProductSpace
  let := nativeModelTopology F (EuclideanSpace ℝ (Fin (2 * (2 * m))))
  let := hV.realNativeFiberBundle (2 * m) hr
  let := hV.realNativeVectorBundle (2 * m) hr
  let := hV.realNativeRiemannianBundle (2 * m) hr
  dsimp only
  intro e he q₁ q₂ hq₁ hq₂ hp a hvan hdetect j
  let TE := TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E
  let TF := TotalSpace (EuclideanSpace ℝ (Fin (2 * (2 * m)))) F
  let : T2Space TE := t2Space_fiberBundleTotal (EuclideanSpace ℝ (Fin (2 * m))) E
  let : LocallyCompactSpace TE :=
    locallyCompactSpace_fiberBundleTotal (EuclideanSpace ℝ (Fin (2 * m))) E
  let : T2Space (TE × TE) := inferInstance
  let : LocallyCompactSpace (TE × TE) := inferInstance
  let Q := q₁.prodMk q₂
  let O := (geometricCohomologyOrientation (2 * m) E o ho).rationalization
  let K := cohomologyZeroSectionSupport (2 * m) E
  let N := bundleNonzero (2 * m) E
  let d (n : ℕ) := bundleCompactSupportChernCharacterComponent (2 * m) E n a
  let cT {Z : Type u} [TopologicalSpace Z] {p q : ℕ} (h : p = q) :
      compactSupportCohomology ℚ Z p →ₗ[ℚ] compactSupportCohomology ℚ Z q :=
    (eqToIso (congrArg (compactSupportCohomology ℚ Z) h)).hom.hom
  let cH {p q : ℕ} (h : p = q) : singularCohomology ℚ X p →ₗ[ℚ]
      singularCohomology ℚ X q := (eqToIso (congrArg (singularCohomology ℚ X) h)).hom.hom
  let cR {p q : ℕ} (h : p = q) : relativeSingularCohomology ℚ N p →ₗ[ℚ]
      relativeSingularCohomology ℚ N q :=
    (eqToIso (congrArg (relativeSingularCohomology ℚ N) h)).hom.hom
  let δ (n : ℕ) := compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * n)
    (cT (by omega) (d (m + n)))
  let I (n : ℕ) := compactSupportCohomologyFiberIntegral ℚ (2 * (2 * m)) F
    (hV.complexCohomologyOrientation (2 * m) hr).rationalization n
  -- Every original supported character has a unique representative on this same zero section.
  let α (n : ℕ) := (LinearEquiv.ofBijective
    (compactSupportCohomologyClass ℚ TE K (2 * n)).hom
    (compactSupportCohomologyClass_zeroSection_bijective ℚ (2 * m) E (2 * n))).symm (d n)
  have hα (n : ℕ) : compactSupportCohomologyClass ℚ TE K (2 * n) (α n) = d n :=
    (LinearEquiv.ofBijective (compactSupportCohomologyClass ℚ TE K (2 * n)).hom
      (compactSupportCohomologyClass_zeroSection_bijective ℚ (2 * m) E (2 * n))).apply_symm_apply
        (d n)
  have hαzero (n : ℕ) (hn : n < m) : α n = 0 := by
    apply (compactSupportCohomologyClass_zeroSection_bijective ℚ (2 * m) E (2 * n)).injective
    rw [hα, map_zero]
    exact hvan n hn
  have hαpoint (n : ℕ) : compactSupportCohomologyToOnePoint ℚ TE (2 * n)
      (compactSupportCohomologyClass ℚ TE K (2 * n) (α n)) =
        reducedChernCharacterComponent (OnePoint.infty : OnePoint TE) n a := by
    rw [hα]
    exact bundleCompactSupportChernCharacterComponent_toOnePoint (2 * m) E n a
  -- These local identities only reassociate degrees; none changes support or orientation.
  have cT_trans {Z : Type u} [TopologicalSpace Z] {p q r : ℕ}
      (h : p = q) (h' : q = r) (b : compactSupportCohomology ℚ Z p) :
      cT h' (cT h b) = cT (h.trans h') b := by
    subst q
    subst r
    rfl
  have cH_trans {p q r : ℕ} (h : p = q) (h' : q = r)
      (b : singularCohomology ℚ X p) : cH h' (cH h b) = cH (h.trans h') b := by
    subst q
    subst r
    rfl
  have cT_pull {p q : ℕ} (h : p = q) (b : compactSupportCohomology ℚ (TE × TE) p) :
      compactSupportCohomologyProperPullback ℚ Q hp q (cT h b) =
        cT h (compactSupportCohomologyProperPullback ℚ Q hp p b) := by
    subst q
    rfl
  have cT_integral {p q : ℕ} (h : p = q)
      (b : compactSupportCohomology ℚ TF (p + 2 * (2 * m))) :
      I q (cT (congrArg (· + 2 * (2 * m)) h) b) = cH h (I p b) := by
    subst q
    rfl
  have cT_leg {p q : ℕ} (h : p = q) (b : relativeSingularCohomology ℚ N p) :
      cT h (compactSupportCohomologyClass ℚ TE K p b) =
        compactSupportCohomologyClass ℚ TE K q (cR h b) := by
    subst q
    rfl
  have hαthom (n : ℕ) : α (m + n) = cR (by omega)
      (cohomologyThomMap ℚ (2 * m) E O (2 * n) (δ n)) := by
    apply (compactSupportCohomologyClass_zeroSection_bijective ℚ (2 * m) E
      (2 * (m + n))).injective
    rw [hα, ← cT_leg (show 2 * n + 2 * m = 2 * (m + n) by omega)]
    have h := (compactBaseCohomologyThomEquiv ℚ (2 * m) E O (2 * n)).apply_symm_apply
      (cT (show 2 * (m + n) = 2 * n + 2 * m by omega) (d (m + n)))
    change compactSupportCohomologyClass ℚ TE K (2 * n + 2 * m)
      (cohomologyThomMap ℚ (2 * m) E O (2 * n) (δ n)) = _ at h
    rw [h, cT_trans] <;> try omega
    rfl
  let ext (p q : ℕ) (b : relativeSingularCohomology ℚ N p)
      (c : relativeSingularCohomology ℚ N q) :=
    compactSupportCohomologyExternalRepresentative ℚ K K p q b c
  have cT_ext {p p' q q' : ℕ} (h : p = p') (h' : q = q')
      (b : relativeSingularCohomology ℚ N p) (c : relativeSingularCohomology ℚ N q) :
      ext p' q' (cR h b) (cR h' c) = cT (congrArg₂ (· + ·) h h') (ext p q b c) := by
    subst p'
    subst q'
    rfl
  let G (i : Fin (2 * m + j + 1)) : singularCohomology ℚ X (2 * j) :=
    I (2 * j) (cT (by omega) (compactSupportCohomologyProperPullback ℚ Q hp
      (2 * i.val + 2 * (2 * m + j - i.val))
      (ext (2 * i.val) (2 * (2 * m + j - i.val)) (α i.val) (α (2 * m + j - i.val)))))
  -- Detect Chern multiplication in the original point-relative model, then properly pull it back.
  have hsum : I (2 * j) (cT (by omega)
      (bundleCompactSupportChernCharacterComponent (2 * (2 * m)) F (2 * m + j)
        (compactSupportKZeroPullback Q hp (compactSupportKZeroExternalProduct a a)))) =
      ∑ i : Fin (2 * m + j + 1), G i := by
    have hchar : bundleCompactSupportChernCharacterComponent (2 * (2 * m)) F (2 * m + j)
        (compactSupportKZeroPullback Q hp (compactSupportKZeroExternalProduct a a)) =
      compactSupportCohomologyProperPullback ℚ Q hp (2 * (2 * m + j))
        (∑ i : Fin (2 * m + j + 1), cT (by omega)
          (ext (2 * i.val) (2 * (2 * m + j - i.val))
            (α i.val) (α (2 * m + j - i.val)))) := by
      apply (compactSupportCohomologyToOnePoint_bundle_bijective ℚ (2 * (2 * m)) F
        (2 * (2 * m + j))).injective
      rw [bundleCompactSupportChernCharacterComponent_toOnePoint,
        compactSupportCohomologyProperPullback_toOnePoint]
      have hex := compactSupportChernCharacter_externalRepresentative a a K K α α
        hαpoint hαpoint (2 * m + j) (hdetect (2 * m + j))
      rw [hex]
      exact (reducedChernCharacterComponent_pullback
        (OnePoint.infty : OnePoint TF) (OnePoint.infty : OnePoint (TE × TE))
        (properOnePointMap Q hp) rfl (compactSupportKZeroExternalProduct a a) (2 * m + j)).symm
    rw [hchar]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [cT_pull, cT_trans] <;> omega
  -- The middle block is the same signed Thom product; the two outside blocks vanish beforehand.
  have hterm (i : Fin (2 * m + j + 1)) (l k : ℕ)
      (hleft : i.val = m + l) (hright : 2 * m + j - i.val = m + k) (hj : l + k = j) :
      G i = (-1 : ℚ) ^ m • cH (congrArg (2 * ·) hj)
        (singularCohomologyEvenCup ℚ X l k (δ l) (δ k)) := by
    have hαcast (n l : ℕ) (h : n = m + l) : α n =
        cR (by omega) (cohomologyThomMap ℚ (2 * m) E O (2 * l) (δ l)) := by
      subst n
      exact hαthom l
    dsimp only [G]
    rw [hαcast i.val l hleft,
      hαcast (2 * m + j - i.val) k hright,
      cT_ext, cT_pull, cT_trans] <;> try omega
    let p := 2 * l
    let q := 2 * k
    have hdegree : p + q = 2 * j := by dsimp [p, q]; omega
    let b := ext (p + 2 * m) (q + 2 * m)
      (cohomologyThomMap ℚ (2 * m) E O p (δ l))
      (cohomologyThomMap ℚ (2 * m) E O q (δ k))
    have hnormalize : cT (show (p + 2 * m) + (q + 2 * m) =
        2 * j + 2 * (2 * m) by omega)
        (compactSupportCohomologyProperPullback ℚ Q hp _ b) =
      cT (congrArg (· + 2 * (2 * m)) hdegree)
        (cT (show (p + 2 * m) + (q + 2 * m) = (p + q) + 2 * (2 * m) by omega)
          (compactSupportCohomologyProperPullback ℚ Q hp _ b)) := by
      rw [cT_trans] <;> omega
    rw [hnormalize, cT_integral hdegree]
    have ht := complexificationCohomologyFiberIntegral_externalThom E o ho hV hr
      e he q₁ q₂ hq₁ hq₂ hp p q (δ l) (δ k)
    change I (p + q) (cT (by omega) (compactSupportCohomologyProperPullback ℚ Q hp _ b)) =
      (-1 : ℚ) ^ m • singularCohomologyCup ℚ X p q _ _ at ht
    rw [ht, map_smul]
    congr 1
    change cH hdegree (singularCohomologyCup ℚ X p q _ _) =
      cH (by omega) (cH (by omega) (singularCohomologyCup ℚ X p q _ _))
    rw [cH_trans] <;> (try dsimp [p, q]) <;> omega
  have hzero (i : Fin (2 * m + j + 1)) (hi : i.val < m ∨ m + j < i.val) : G i = 0 := by
    dsimp only [G, ext]
    rcases hi with hi | hi
    · rw [hαzero i.val hi]
      simp only [compactSupportCohomologyExternalRepresentative, map_zero,
        LinearMap.zero_apply]
    · rw [hαzero (2 * m + j - i.val) (by omega)]
      simp only [compactSupportCohomologyExternalRepresentative, map_zero]
  change I (2 * j) (cT (by omega) _) = _
  rw [hsum, Finset.smul_sum]
  have hsize : m + ((j + 1) + m) = 2 * m + j + 1 := by omega
  rw [← Fin.sum_congr' G hsize, Fin.sum_univ_add]
  have hfront (i : Fin m) : G ((Fin.castAdd ((j + 1) + m) i).cast hsize) = 0 :=
    hzero _ (Or.inl (by simpa only [Fin.val_cast, Fin.val_castAdd] using i.isLt))
  simp only [hfront, Finset.sum_const_zero, zero_add]
  let H (i : Fin ((j + 1) + m)) := G ((Fin.natAdd m i).cast hsize)
  have htail (i : Fin m) : H (Fin.natAdd (j + 1) i) = 0 :=
    hzero _ (Or.inr (by simp only [Fin.val_cast, Fin.val_natAdd]; omega))
  change (∑ i, H i) = _
  rw [Fin.sum_trunc H htail]
  apply Finset.sum_congr rfl
  intro i _
  exact hterm ((Fin.natAdd m (Fin.castAdd m i)).cast hsize) i.val (j - i.val)
    (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd])
    (by simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]; omega)
    (by omega)

end AtiyahSinger
