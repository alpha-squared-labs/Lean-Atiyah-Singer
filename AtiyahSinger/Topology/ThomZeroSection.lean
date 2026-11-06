/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTensorKZero
public import AtiyahSinger.Topology.ExteriorBundleSum
public import AtiyahSinger.Topology.HermitianSupportedThom
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# The exterior alternating class and the Thom zero-section formula

Public module ID: M2254.

SG III.12, Lemma 12.3 identifies restriction of the Thom map to its zero
section with multiplication by `lambdaMinusOne E`. This is the alternating
class of the even and odd exterior bundles of E itself. Using exterior
powers of the dual would give a different formula; the present definition
retains SG's wedge-minus-contraction convention.

The base is compact Hausdorff, as in the source lemma. Its zero section is
proper, so compact-support pullback is defined. Exterior direct-sum
isomorphisms also give multiplicativity of the alternating class.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology
  exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback t2Space_totalSpace
  locallyCompactSpace_totalSpace

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- The standard alternating exterior class, using E rather than its dual. -/
def lambdaMinusOne : ComplexKZero X :=
  kZeroClass (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) -
    kZeroClass (fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)

/-- The alternating exterior class is multiplicative for the original direct sum. -/
theorem lambdaMinusOne_sum
    (F : X → Type*) [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F] :
    lambdaMinusOne (E ×ᵇ F) = kZeroMul C(X, ℂ) (lambdaMinusOne E) (lambdaMinusOne F) := by
  /- The exterior tensor isomorphism sends xi tensor eta to inclusion_E(xi)
  wedge inclusion_F(eta). Its even part consists of even-even and odd-odd
  terms, and its odd part of even-odd and odd-even terms. These are continuous
  bundle isomorphisms in the original finite exterior topologies. Apply bundle
  class invariance, additivity for sums and the existing tensor-product class
  formula. Distributing the difference of the two parity classes gives exactly
  the stated product. Compactness supplies their absolute K classes; no metric,
  positive rank, fixed rank or connectedness hypothesis is needed. -/
  obtain ⟨u₀, u₁, _, _⟩ := exists_exteriorParity_sum_iso (E := E) (F := F)
  unfold lambdaMinusOne
  rw [← kZeroClass_eq_of_iso u₀, ← kZeroClass_eq_of_iso u₁,
    kZeroClass_sum, kZeroClass_sum]
  rw [kZeroClass_tensor, kZeroClass_tensor, kZeroClass_tensor, kZeroClass_tensor]
  -- Bilinearity distributes this same tensor multiplication over the alternating classes.
  simp only [map_sub, AddMonoidHom.sub_apply]
  abel

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- SG Lemma 12.3: the actual zero-section pullback of the Thom image is the exterior product. -/
theorem zeroSectionPullback_supportedThomHom (h : ContinuousHermitianMetric E)
    (a : CompactSupportKZero X) :
    let i : C(X, TotalSpace Unit E) := ⟨fun x ↦ ⟨x, 0⟩, continuous_zero_section E⟩
    compactSupportKZeroCompactEquiv X
        (compactSupportKZeroPullback i i.continuous.isProperMap (h.supportedThomHom a)) =
      kZeroMul C(X, ℂ) (lambdaMinusOne E) (compactSupportKZeroCompactEquiv X a) := by
  /- Restrict the actual exterior triple to the original zero section, then compute
  its absolute class. The same graph action restricts to tensor multiplication. -/
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (h.toCore x).toCore
  let i : C(X, TotalSpace Unit E) := ⟨fun x ↦ ⟨x, 0⟩, continuous_zero_section E⟩
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let G : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0
  let H : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1
  let : IsFiniteRank (p *ᵖ G) := isFiniteRank_pullback (E := G) p
  let : IsFiniteRank (p *ᵖ H) := isFiniteRank_pullback (E := H) p
  let A := exteriorThomTriple E h.continuous_pairing
  -- Projection after the zero section is the identity on the base.
  have hsection (J : X → Type _) [∀ x, AddCommGroup (J x)] [∀ x, Module ℂ (J x)]
      [TopologicalSpace (TotalSpace Unit J)] [IsFiniteRank J] :
      Nonempty (Iso (i *ᵖ (p *ᵖ J)) J) := by
    let u := pullbackCompIso (E := J) p i
    let v := pullbackIdIso (E := J)
    exact ⟨u.trans v⟩
  -- Forgetting compact support keeps the source-minus-target class of the same triple.
  have habsolute {U V : X → Type _}
      [∀ x, AddCommGroup (U x)] [∀ x, Module ℂ (U x)]
      [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
      [TopologicalSpace (TotalSpace Unit U)] [IsFiniteRank U]
      [TopologicalSpace (TotalSpace Unit V)] [IsFiniteRank V]
      (B : CompactSupportTriple U V) :
      compactSupportKZeroToAbsolute B.compactSupportClass = kZeroClass U - kZeroClass V := by
    have hB := B.toSupportBundleTriple.compactSupportClass_toAbsolute
    change compactSupportKZeroToAbsolute B.compactSupportClass =
      kZeroClass (smallBundle U).Fiber - kZeroClass (smallBundle V).Fiber at hB
    rw [← kZeroClass_eq_of_iso (smallBundleIso U),
      ← kZeroClass_eq_of_iso (smallBundleIso V)] at hB
    exact hB
  -- Both restricted parity bundles are the original ones, with their actual topologies.
  have hclass : compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i i.continuous.isProperMap
        (exteriorThomClass E h.continuous_pairing)) = lambdaMinusOne E := by
    change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i i.continuous.isProperMap A.compactSupportClass) = _
    rw [← A.compactSupportClass_pullback i i.continuous.isProperMap, habsolute]
    obtain ⟨u⟩ := hsection G
    obtain ⟨v⟩ := hsection H
    change kZeroClass (i *ᵖ (p *ᵖ G)) - kZeroClass (i *ᵖ (p *ᵖ H)) = _
    rw [kZeroClass_eq_of_iso u, kZeroClass_eq_of_iso v]
    rfl
  -- The diagonal graph action is tensor multiplication after finite-point restriction.
  let δ : C(X, X × X) := (ContinuousMap.id X).prodMk (ContinuousMap.id X)
  have hδ : IsProperMap δ :=
    isProperMap_of_comp_of_t2 δ.continuous continuous_snd isProperMap_id
  -- Finite-point restriction commutes with this same proper diagonal pullback.
  have hfinite (q : CompactSupportKZero (X × X)) :
      compactSupportKZeroToAbsolute (compactSupportKZeroPullback δ hδ q) =
        complexKZeroPullback δ (compactSupportKZeroToAbsolute q) := by
    change complexKZeroPullback
        ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap δ hδ) q.val) =
      complexKZeroPullback δ
        (complexKZeroPullback
          ⟨((↑) : X × X → OnePoint (X × X)), OnePoint.continuous_coe⟩ q.val)
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  have hdiagonal (u v : CompactSupportKZero X) :
      compactSupportKZeroToAbsolute (compactSupportKZeroAction (ContinuousMap.id X) u v) =
        kZeroMul C(X, ℂ) (compactSupportKZeroToAbsolute u)
          (compactSupportKZeroToAbsolute v) := by
    change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback δ hδ (compactSupportKZeroExternalProduct u v)) = _
    rw [hfinite, compactSupportKZeroToAbsolute_externalProduct]
    -- Absolute diagonal pullback is the original tensor multiplication.
    change kZeroMap _ (kZeroMul _ _ _) = _
    rw [kZeroMap_mul]
    change kZeroMul C(X, ℂ)
      (complexKZeroPullback δ
        (complexKZeroPullback ContinuousMap.fst (compactSupportKZeroToAbsolute u)))
      (complexKZeroPullback δ
        (complexKZeroPullback ContinuousMap.snd (compactSupportKZeroToAbsolute v))) = _
    have hfst : (ContinuousMap.fst : C(X × X, X)).comp δ = ContinuousMap.id X := rfl
    have hsnd : (ContinuousMap.snd : C(X × X, X)).comp δ = ContinuousMap.id X := rfl
    have hid : complexKZeroPullback (ContinuousMap.id X) =
        AddMonoidHom.id (ComplexKZero X) := by
      change kZeroMap (RingHom.id C(X, ℂ)) = _
      exact kZeroMap_id
    have hfstPullback : complexKZeroPullback δ
        (complexKZeroPullback ContinuousMap.fst (compactSupportKZeroToAbsolute u)) =
          compactSupportKZeroToAbsolute u := by
      have h := DFunLike.congr_fun
        (complexKZeroPullback_comp δ (ContinuousMap.fst : C(X × X, X)))
        (compactSupportKZeroToAbsolute u)
      simpa only [hfst, hid, AddMonoidHom.id_apply, AddMonoidHom.comp_apply] using h.symm
    have hsndPullback : complexKZeroPullback δ
        (complexKZeroPullback ContinuousMap.snd (compactSupportKZeroToAbsolute v)) =
          compactSupportKZeroToAbsolute v := by
      have h := DFunLike.congr_fun
        (complexKZeroPullback_comp δ (ContinuousMap.snd : C(X × X, X)))
        (compactSupportKZeroToAbsolute v)
      simpa only [hsnd, hid, AddMonoidHom.id_apply, AddMonoidHom.comp_apply] using h.symm
    rw [hfstPullback, hsndPullback]
  -- Use the proved compact-base comparison and naturality along this same proper section.
  change compactSupportKZeroToAbsolute
    (compactSupportKZeroPullback i i.continuous.isProperMap
      (supportedThomHom E h.continuous_pairing a)) = _
  rw [supportedThomHom_compact E h.continuous_pairing, AddMonoidHom.comp_apply]
  change compactSupportKZeroToAbsolute
    (compactSupportKZeroPullback i i.continuous.isProperMap
      (compactSupportKZeroAction p
        ((compactSupportKZeroCompactEquiv X).symm ((compactSupportKZeroCompactEquiv X) a))
        (exteriorThomClass E h.continuous_pairing))) = _
  rw [AddEquiv.symm_apply_apply, compactSupportKZeroPullback_action]
  have hpi : p.comp i = ContinuousMap.id X := rfl
  rw [hpi, hdiagonal, hclass]
  exact kZeroMul_comm _ _

end AtiyahSinger.ComplexBundle
