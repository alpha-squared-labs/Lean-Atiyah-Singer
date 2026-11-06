/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleComplement
public import AtiyahSinger.Topology.BundleKMinusOne
public import AtiyahSinger.Topology.DifferenceBundle

/-!
# The automorphism boundary of a compact closed pair

Public module ID: M1584.

Karoubi II.3.21--II.3.23 constructs the boundary from a bundle automorphism on A.
Choose a complement so that E ⊕ F is trivial, conjugate α ⊕ Id into that trivial
bundle, and form the actual relative triple on X. The default choice below uses
the already specified idempotent presentation and its complementary image.
The resulting class is the original difference-bundle class in RelativeKZero.

The explicit construction with any given complement is also retained. Its
independence theorem does not assume that a change of trivialization on A extends
to X: stabilization and block homotopy are needed. Isomorphism, direct sum and
elementary homotopy compatibility descend this construction through the actual
BundleKMinusOne quotient. No target relative class is chosen to satisfy exactness.

The restricted-bundle formula records the original triple (E,E,α) whenever the
bundle extends to X, even when its automorphism over A does not extend. Exactness
and the suspended compact-support comparison are proved in separate modules.
The complement construction, its descent relations and the restricted-bundle
formula are proved on the original compact closed pair.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] trivialTopology isFiniteRank_trivial sumTopology isFiniteRank_sum
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber

variable {X : Type*} [TopologicalSpace X]

/-- The actual relative triple made from a specified complement and trivialization on A. -/
def BundleAutomorphism.boundaryTripleOfComplement (A : Set X) (a : BundleAutomorphism A)
    (F : FiniteBundle A) (n : ℕ)
    (e : Iso (a.bundle.sum F).Fiber (FiniteBundle.trivial A n).Fiber) : BundleTriple A :=
  let t := pullbackTrivialIso (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) n
  let α := (e.symm.trans (a.automorphism.sum (Iso.refl F.Fiber))).trans e
  BundleTriple.ofBoundary (FiniteBundle.trivial X n) (FiniteBundle.trivial X n)
    ((t.trans α).trans t.symm)

variable [CompactSpace X] [T2Space X]

/-- The boundary triple using the existing idempotent presentation and its actual complement. -/
def BundleAutomorphism.boundaryTriple (A : Set X) (hA : IsClosed A)
    (a : BundleAutomorphism A) : BundleTriple A :=
  letI := hA.isClosedEmbedding_subtypeVal.compactSpace
  let p := idempotentPresentation (E := a.bundle.Fiber)
  let F := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let e : Iso (a.bundle.sum F).Fiber (FiniteBundle.trivial A p.size).Fiber :=
    (nonempty_presentation_complement_iso (E := a.bundle.Fiber)).some
  a.boundaryTripleOfComplement A F p.size e

/-- The original relative difference class of the specified automorphism boundary triple. -/
def BundleAutomorphism.boundaryClass (A : Set X) (hA : IsClosed A)
    (a : BundleAutomorphism A) : RelativeKZero A hA :=
  (a.boundaryTriple A hA).relativeClass hA

/-- KA II.3.21: the boundary class is independent of the chosen complement and trivialization. -/
theorem BundleAutomorphism.boundaryClass_eq_of_complement (A : Set X) (hA : IsClosed A)
    (a : BundleAutomorphism A) (F : FiniteBundle A) (n : ℕ)
    (e : Iso (a.bundle.sum F).Fiber (FiniteBundle.trivial A n).Fiber) :
    a.boundaryClass A hA = (a.boundaryTripleOfComplement A F n e).relativeClass hA := by
  /- Rotate the two copies of the original bundle inside the direct sum of
  the two specified trivializations. The complementary bundles are fixed.
  The resulting boundary homotopy moves the same original automorphism from
  the first trivial summand to the second, without extending a frame on A. -/
  have rotate (E F G : FiniteBundle A) (a : Iso E.Fiber E.Fiber) :
      Nonempty (IsoHomotopy
        ((a.sum (Iso.refl F.Fiber)).sum (Iso.refl (E.sum G).Fiber))
        ((Iso.refl (E.sum F).Fiber).sum (a.sum (Iso.refl G.Fiber)))) := by
    let P := (E.sum F).sum (E.sum G)
    let Q := (E.sum E).sum (F.sum G)
    -- Rearrange the four original coordinates, keeping both copies of E explicit.
    let s : Iso P.Fiber Q.Fiber :=
      { linearEquiv x := LinearEquiv.prodProdProdComm ℂ (E.Fiber x) (F.Fiber x)
          (E.Fiber x) (G.Fiber x)
        continuous_total := by
          have h₁ := continuous_sum_fst (E := (E.sum F).Fiber) (F := (E.sum G).Fiber)
          have h₂ := continuous_sum_snd (E := (E.sum F).Fiber) (F := (E.sum G).Fiber)
          apply continuous_induced_rng.mpr
          apply Continuous.prodMk
          · apply continuous_induced_rng.mpr
            exact ((continuous_sum_fst (E := E.Fiber) (F := F.Fiber)).comp h₁).prodMk
              ((continuous_sum_fst (E := E.Fiber) (F := G.Fiber)).comp h₂)
          · apply continuous_induced_rng.mpr
            exact ((continuous_sum_snd (E := E.Fiber) (F := F.Fiber)).comp h₁).prodMk
              ((continuous_sum_snd (E := E.Fiber) (F := G.Fiber)).comp h₂)
        continuous_symm := by
          have h₁ := continuous_sum_fst (E := (E.sum E).Fiber) (F := (F.sum G).Fiber)
          have h₂ := continuous_sum_snd (E := (E.sum E).Fiber) (F := (F.sum G).Fiber)
          apply continuous_induced_rng.mpr
          apply Continuous.prodMk
          · apply continuous_induced_rng.mpr
            exact ((continuous_sum_fst (E := E.Fiber) (F := E.Fiber)).comp h₁).prodMk
              ((continuous_sum_fst (E := F.Fiber) (F := G.Fiber)).comp h₂)
          · apply continuous_induced_rng.mpr
            exact ((continuous_sum_snd (E := E.Fiber) (F := E.Fiber)).comp h₁).prodMk
              ((continuous_sum_snd (E := F.Fiber) (F := G.Fiber)).comp h₂) }
    obtain ⟨r, hr, ⟨H⟩⟩ := (Iso.refl E.Fiber).exists_signed_swap_homotopy
    obtain ⟨K⟩ := H.nonempty_sum_refl (Iso.refl (F.sum G).Fiber)
    obtain ⟨L⟩ := (IsoHomotopy.refl s).nonempty_comp K
    obtain ⟨M⟩ := L.nonempty_comp (IsoHomotopy.refl s.symm)
    let R : Iso P.Fiber P.Fiber := (s.trans (r.sum (Iso.refl (F.sum G).Fiber))).trans s.symm
    have hstart : (s.trans ((Iso.refl (E.sum E).Fiber).sum
        (Iso.refl (F.sum G).Fiber))).trans s.symm = Iso.refl P.Fiber := by
      apply Iso.ext
      intro x
      apply LinearEquiv.ext
      intro v
      exact (s.linearEquiv x).symm_apply_apply v
    have J : IsoHomotopy (Iso.refl P.Fiber) R := hstart ▸ M
    have hR (x : A) (v : P.Fiber x) :
        R.linearEquiv x v = ((-v.2.1, v.1.2), (v.1.1, v.2.2)) := by
      change (s.linearEquiv x).symm
        ((r.sum (Iso.refl (F.sum G).Fiber)).linearEquiv x (s.linearEquiv x v)) = _
      apply (s.linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply]
      change (r.linearEquiv x (v.1.1, v.2.1), (v.1.2, v.2.2)) =
        ((-v.2.1, v.1.1), (v.1.2, v.2.2))
      rw [hr]
      rfl
    let C := (a.sum (Iso.refl F.Fiber)).sum (Iso.refl (E.sum G).Fiber)
    let D := (Iso.refl (E.sum F).Fiber).sum (a.sum (Iso.refl G.Fiber))
    obtain ⟨N⟩ := J.nonempty_comp (IsoHomotopy.refl C)
    obtain ⟨O⟩ := N.nonempty_comp J.nonempty_inverse.some
    have hzero : ((Iso.refl P.Fiber).trans C).trans (Iso.refl P.Fiber).symm = C := by
      apply Iso.ext
      intro x
      rfl
    have hone : (R.trans C).trans R.symm = D := by
      apply Iso.ext
      intro x
      apply LinearEquiv.ext
      intro v
      apply (R.linearEquiv x).injective
      change R.linearEquiv x ((R.linearEquiv x).symm
        (C.linearEquiv x (R.linearEquiv x v))) = R.linearEquiv x (D.linearEquiv x v)
      rw [LinearEquiv.apply_symm_apply, hR, hR]
      change ((a.linearEquiv x (-v.2.1), v.1.2), (v.1.1, v.2.2)) =
        ((-(a.linearEquiv x v.2.1), v.1.2), (v.1.1, v.2.2))
      rw [map_neg]
    rw [hzero, hone] at O
    exact ⟨O⟩
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let p := idempotentPresentation (E := a.bundle.Fiber)
  let F₀ := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let e₀ : Iso (a.bundle.sum F₀).Fiber (FiniteBundle.trivial A p.size).Fiber :=
    (nonempty_presentation_complement_iso (E := a.bundle.Fiber)).some
  let T₀ := FiniteBundle.trivial X p.size
  let T₁ := FiniteBundle.trivial X n
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let t₀ := pullbackTrivialIso i p.size
  let t₁ := pullbackTrivialIso i n
  -- Both trivializations keep the original coordinate vectors, including in reverse.
  have ht (k : ℕ) (x : A) (v : Fin k → ℂ) :
      ((pullbackTrivialIso i k).linearEquiv x).symm v = v := by
    apply ((pullbackTrivialIso i k).linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, pullbackTrivialIso_apply]
  have hboundary (J : FiniteBundle A) (k : ℕ)
      (d : Iso (a.bundle.sum J).Fiber (FiniteBundle.trivial A k).Fiber)
      (x : A) (v : Fin k → ℂ) :
      (a.boundaryTripleOfComplement A J k d).boundary.linearEquiv x v =
        d.linearEquiv x ((a.automorphism.sum (Iso.refl J.Fiber)).linearEquiv x
          ((d.linearEquiv x).symm v)) := by
    change ((pullbackTrivialIso i k).linearEquiv x).symm
      (d.linearEquiv x ((a.automorphism.sum (Iso.refl J.Fiber)).linearEquiv x
        ((d.linearEquiv x).symm ((pullbackTrivialIso i k).linearEquiv x v)))) = _
    rw [pullbackTrivialIso_apply, ht]
  let S : Iso ((T₀.sum T₁).restrict A).Fiber
      ((a.bundle.sum F₀).sum (a.bundle.sum F)).Fiber :=
    (restrictSumIso A).trans ((t₀.trans e₀.symm).sum (t₁.trans e.symm))
  have hS (x : A) (v : (T₀.sum T₁).Fiber x) :
      S.linearEquiv x v =
        ((e₀.linearEquiv x).symm v.1, (e.linearEquiv x).symm v.2) := by
    change ((t₀.trans e₀.symm).sum (t₁.trans e.symm)).linearEquiv x
      ((restrictSumIso A).linearEquiv x v) = _
    rw [restrictSumIso_apply]
    change ((e₀.linearEquiv x).symm ((pullbackTrivialIso i p.size).linearEquiv x v.1),
      (e.linearEquiv x).symm ((pullbackTrivialIso i n).linearEquiv x v.2)) = _
    rw [pullbackTrivialIso_apply, pullbackTrivialIso_apply]
  let C := (a.automorphism.sum (Iso.refl F₀.Fiber)).sum
    (Iso.refl (a.bundle.sum F).Fiber)
  let D := (Iso.refl (a.bundle.sum F₀).Fiber).sum
    (a.automorphism.sum (Iso.refl F.Fiber))
  obtain ⟨H⟩ := rotate a.bundle F₀ F a.automorphism
  obtain ⟨K⟩ := (IsoHomotopy.refl S).nonempty_comp H
  obtain ⟨J⟩ := K.nonempty_comp (IsoHomotopy.refl S.symm)
  let L := (a.boundaryTriple A hA).sum (BundleTriple.identity A T₁)
  let R := (BundleTriple.identity A T₀).sum (a.boundaryTripleOfComplement A F n e)
  have hL (x : A) (v : (T₀.sum T₁).Fiber x) :
      L.boundary.linearEquiv x v =
        (e₀.linearEquiv x ((a.automorphism.sum (Iso.refl F₀.Fiber)).linearEquiv x
          ((e₀.linearEquiv x).symm v.1)), v.2) := by
    change (RelativeTriple.sum (a.boundaryTripleOfComplement A F₀ p.size e₀).boundary
      (RelativeTriple.identity T₁.Fiber A)).linearEquiv x v = _
    erw [RelativeTriple.sum_apply]
    change ((a.boundaryTripleOfComplement A F₀ p.size e₀).boundary.linearEquiv x v.1,
      v.2) = _
    rw [hboundary]
    rfl
  have hR (x : A) (v : (T₀.sum T₁).Fiber x) :
      R.boundary.linearEquiv x v =
        (v.1, e.linearEquiv x ((a.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x
          ((e.linearEquiv x).symm v.2))) := by
    change (RelativeTriple.sum (RelativeTriple.identity T₀.Fiber A)
      (a.boundaryTripleOfComplement A F n e).boundary).linearEquiv x v = _
    erw [RelativeTriple.sum_apply]
    change (v.1, (a.boundaryTripleOfComplement A F n e).boundary.linearEquiv x v.2) = _
    rw [hboundary]
    rfl
  have hzero : (S.trans C).trans S.symm = L.boundary := by
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro v
    apply (S.linearEquiv x).injective
    change S.linearEquiv x ((S.linearEquiv x).symm
      (C.linearEquiv x (S.linearEquiv x v))) = S.linearEquiv x (L.boundary.linearEquiv x v)
    rw [LinearEquiv.apply_symm_apply]
    erw [hL, hS, hS]
    change ((a.automorphism.sum (Iso.refl F₀.Fiber)).linearEquiv x
      ((e₀.linearEquiv x).symm v.1), (e.linearEquiv x).symm v.2) = _
    rw [LinearEquiv.symm_apply_apply]
  have hone : (S.trans D).trans S.symm = R.boundary := by
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro v
    apply (S.linearEquiv x).injective
    change S.linearEquiv x ((S.linearEquiv x).symm
      (D.linearEquiv x (S.linearEquiv x v))) = S.linearEquiv x (R.boundary.linearEquiv x v)
    rw [LinearEquiv.apply_symm_apply]
    erw [hR, hS, hS]
    change ((e₀.linearEquiv x).symm v.1,
      (a.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x
        ((e.linearEquiv x).symm v.2)) = _
    rw [LinearEquiv.symm_apply_apply]
  -- The original relative classes are compared through one actual boundary homotopy.
  rw [hzero, hone] at J
  have hclass := bundleTriple_relativeClass_eq_of_homotopy hA
    (T₀.sum T₁) (T₀.sum T₁) L.boundary R.boundary J
  change L.relativeClass hA = R.relativeClass hA at hclass
  simpa only [L, R, BundleTriple.relativeClass_sum, BundleTriple.relativeClass_identity,
    add_zero, zero_add, BundleAutomorphism.boundaryClass] using hclass

/-- Intertwining bundle isomorphisms preserve the same constructed relative boundary class. -/
theorem BundleAutomorphism.boundaryClass_eq_of_isIsomorphic (A : Set X) (hA : IsClosed A)
    (a b : BundleAutomorphism A) (h : a.IsIsomorphic b) :
    a.boundaryClass A hA = b.boundaryClass A hA := by
  -- Transport the same complement along the given intertwining bundle isomorphism.
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  obtain ⟨g, hg⟩ := h
  let p := idempotentPresentation (E := b.bundle.Fiber)
  let F := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let e : Iso (b.bundle.sum F).Fiber (FiniteBundle.trivial A p.size).Fiber :=
    (nonempty_presentation_complement_iso (E := b.bundle.Fiber)).some
  let d : Iso (a.bundle.sum F).Fiber (FiniteBundle.trivial A p.size).Fiber :=
    (g.sum (Iso.refl F.Fiber)).trans e
  rw [a.boundaryClass_eq_of_complement A hA F p.size d,
    b.boundaryClass_eq_of_complement A hA F p.size e]
  -- In these shared coordinates the stabilized boundary automorphisms agree pointwise.
  apply BundleTriple.relativeClass_eq_of_isIsomorphic
  let T := FiniteBundle.trivial X p.size
  refine ⟨Iso.refl T.Fiber, Iso.refl T.Fiber, ?_⟩
  intro x v
  let t := pullbackTrivialIso (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) p.size
  let w := (d.linearEquiv x).symm (t.linearEquiv x v)
  have hw : (g.sum (Iso.refl F.Fiber)).linearEquiv x w =
      (e.linearEquiv x).symm (t.linearEquiv x v) := by
    apply (e.linearEquiv x).injective
    change d.linearEquiv x ((d.linearEquiv x).symm (t.linearEquiv x v)) =
      e.linearEquiv x ((e.linearEquiv x).symm (t.linearEquiv x v))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hcomm : (g.sum (Iso.refl F.Fiber)).linearEquiv x
      ((a.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x w) =
      (b.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x
        ((g.sum (Iso.refl F.Fiber)).linearEquiv x w) := by
    exact Prod.ext (hg x w.1) rfl
  change (t.linearEquiv x).symm (e.linearEquiv x
    ((g.sum (Iso.refl F.Fiber)).linearEquiv x
      ((a.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x w))) =
    (t.linearEquiv x).symm (e.linearEquiv x
      ((b.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x
        ((e.linearEquiv x).symm (t.linearEquiv x v))))
  rw [hcomm, hw]

/-- Direct sum of automorphisms adds their specified relative boundary classes. -/
theorem BundleAutomorphism.boundaryClass_sum (A : Set X) (hA : IsClosed A)
    (a b : BundleAutomorphism A) :
    (a.sum b).boundaryClass A hA = a.boundaryClass A hA + b.boundaryClass A hA := by
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let p := idempotentPresentation (E := a.bundle.Fiber)
  let q := idempotentPresentation (E := b.bundle.Fiber)
  let F := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let G := FiniteBundle.ofFamily (fun x ↦ q.complement.fiber x)
  let e : Iso (a.bundle.sum F).Fiber (FiniteBundle.trivial A p.size).Fiber :=
    (nonempty_presentation_complement_iso (E := a.bundle.Fiber)).some
  let d : Iso (b.bundle.sum G).Fiber (FiniteBundle.trivial A q.size).Fiber :=
    (nonempty_presentation_complement_iso (E := b.bundle.Fiber)).some
  -- The same finite-coordinate concatenation is used over A and over X.
  let c : ((Fin p.size → ℂ) × (Fin q.size → ℂ)) ≃L[ℂ]
      (Fin (p.size + q.size) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin p.size) (Fin q.size) ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (p.size + q.size) ↦ ℂ)
        finSumFinEquiv)).toContinuousLinearEquiv
  let merge (Z : Type _) [TopologicalSpace Z] :
      Iso ((FiniteBundle.trivial Z p.size).sum (FiniteBundle.trivial Z q.size)).Fiber
        (FiniteBundle.trivial Z (p.size + q.size)).Fiber :=
    { linearEquiv _ := c.toLinearEquiv
      continuous_total := by
        have h₁ : Continuous (fun z : TotalSpace Unit
            (FiniteBundle.trivial Z p.size).Fiber ↦ (z.proj, z.snd)) := continuous_induced_dom
        have h₂ : Continuous (fun z : TotalSpace Unit
            (FiniteBundle.trivial Z q.size).Fiber ↦ (z.proj, z.snd)) := continuous_induced_dom
        apply continuous_induced_rng.mpr
        exact (continuous_proj (E := ((FiniteBundle.trivial Z p.size).sum
          (FiniteBundle.trivial Z q.size)).Fiber)).prodMk
            (c.continuous.comp (((h₁.snd.comp continuous_sum_fst).prodMk
              (h₂.snd.comp continuous_sum_snd))))
      continuous_symm := by
        have hz : Continuous (fun z : TotalSpace Unit
            (FiniteBundle.trivial Z (p.size + q.size)).Fiber ↦ (z.proj, z.snd)) :=
          continuous_induced_dom
        have hv := c.symm.continuous.comp hz.snd
        apply continuous_induced_rng.mpr
        exact (continuous_induced_rng.mpr (hz.fst.prodMk hv.fst)).prodMk
          (continuous_induced_rng.mpr (hz.fst.prodMk hv.snd)) }
  -- Reorder the original four bundles before applying their two trivializations.
  let s : Iso ((a.bundle.sum b.bundle).sum (F.sum G)).Fiber
      ((a.bundle.sum F).sum (b.bundle.sum G)).Fiber :=
    { linearEquiv x := LinearEquiv.prodProdProdComm ℂ (a.bundle.Fiber x) (b.bundle.Fiber x)
        (F.Fiber x) (G.Fiber x)
      continuous_total := by
        have h₁ := continuous_sum_fst (E := (a.bundle.sum b.bundle).Fiber)
          (F := (F.sum G).Fiber)
        have h₂ := continuous_sum_snd (E := (a.bundle.sum b.bundle).Fiber)
          (F := (F.sum G).Fiber)
        apply continuous_induced_rng.mpr
        apply Continuous.prodMk
        · apply continuous_induced_rng.mpr
          exact ((continuous_sum_fst (E := a.bundle.Fiber) (F := b.bundle.Fiber)).comp h₁).prodMk
            ((continuous_sum_fst (E := F.Fiber) (F := G.Fiber)).comp h₂)
        · apply continuous_induced_rng.mpr
          exact ((continuous_sum_snd (E := a.bundle.Fiber) (F := b.bundle.Fiber)).comp h₁).prodMk
            ((continuous_sum_snd (E := F.Fiber) (F := G.Fiber)).comp h₂)
      continuous_symm := by
        have h₁ := continuous_sum_fst (E := (a.bundle.sum F).Fiber)
          (F := (b.bundle.sum G).Fiber)
        have h₂ := continuous_sum_snd (E := (a.bundle.sum F).Fiber)
          (F := (b.bundle.sum G).Fiber)
        apply continuous_induced_rng.mpr
        apply Continuous.prodMk
        · apply continuous_induced_rng.mpr
          exact ((continuous_sum_fst (E := a.bundle.Fiber) (F := F.Fiber)).comp h₁).prodMk
            ((continuous_sum_fst (E := b.bundle.Fiber) (F := G.Fiber)).comp h₂)
        · apply continuous_induced_rng.mpr
          exact ((continuous_sum_snd (E := a.bundle.Fiber) (F := F.Fiber)).comp h₁).prodMk
            ((continuous_sum_snd (E := b.bundle.Fiber) (F := G.Fiber)).comp h₂) }
  let eSum : Iso ((a.sum b).bundle.sum (F.sum G)).Fiber
      (FiniteBundle.trivial A (p.size + q.size)).Fiber :=
    s.trans ((e.sum d).trans (merge A))
  rw [(a.sum b).boundaryClass_eq_of_complement A hA (F.sum G) (p.size + q.size) eSum,
    a.boundaryClass_eq_of_complement A hA F p.size e,
    b.boundaryClass_eq_of_complement A hA G q.size d]
  have hboundary (u : BundleAutomorphism A) (J : FiniteBundle A) (k : ℕ)
      (v : Iso (u.bundle.sum J).Fiber (FiniteBundle.trivial A k).Fiber)
      (x : A) (w : Fin k → ℂ) :
      (u.boundaryTripleOfComplement A J k v).boundary.linearEquiv x w =
        v.linearEquiv x ((u.automorphism.sum (Iso.refl J.Fiber)).linearEquiv x
          ((v.linearEquiv x).symm w)) := by
    let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have ht (w : Fin k → ℂ) :
        ((pullbackTrivialIso i k).linearEquiv x).symm w = w := by
      apply ((pullbackTrivialIso i k).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, pullbackTrivialIso_apply]
    change ((pullbackTrivialIso i k).linearEquiv x).symm
      (v.linearEquiv x ((u.automorphism.sum (Iso.refl J.Fiber)).linearEquiv x
        ((v.linearEquiv x).symm ((pullbackTrivialIso i k).linearEquiv x w)))) = _
    rw [pullbackTrivialIso_apply, ht]
  let L := (a.boundaryTripleOfComplement A F p.size e).sum
    (b.boundaryTripleOfComplement A G q.size d)
  let R := (a.sum b).boundaryTripleOfComplement A (F.sum G) (p.size + q.size) eSum
  have hi : L.IsIsomorphic R := by
    refine ⟨merge X, merge X, ?_⟩
    intro x v
    change (Fin p.size → ℂ) × (Fin q.size → ℂ) at v
    let u := (e.linearEquiv x).symm v.1
    let w := (d.linearEquiv x).symm v.2
    let z : ((a.sum b).bundle.sum (F.sum G)).Fiber x := ((u.1, w.1), (u.2, w.2))
    have hz : eSum.linearEquiv x z = c v := by
      change c (e.linearEquiv x ((e.linearEquiv x).symm v.1),
        d.linearEquiv x ((d.linearEquiv x).symm v.2)) = c v
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have hzinv : (eSum.linearEquiv x).symm (c v) = z :=
      ((eSum.linearEquiv x).eq_symm_apply.mpr hz).symm
    change c (L.boundary.linearEquiv x v) = R.boundary.linearEquiv x (c v)
    change c ((RelativeTriple.sum (a.boundaryTripleOfComplement A F p.size e).boundary
      (b.boundaryTripleOfComplement A G q.size d).boundary).linearEquiv x v) = _
    erw [RelativeTriple.sum_apply]
    erw [hboundary, hboundary]
    change c (e.linearEquiv x ((a.automorphism.sum (Iso.refl F.Fiber)).linearEquiv x u),
      d.linearEquiv x ((b.automorphism.sum (Iso.refl G.Fiber)).linearEquiv x w)) =
        R.boundary.linearEquiv x (c v)
    change _ = ((a.sum b).boundaryTripleOfComplement A (F.sum G)
      (p.size + q.size) eSum).boundary.linearEquiv x (c v)
    rw [hboundary, hzinv]
    rfl
  -- The single global concatenation is used on both sides of the boundary square.
  have hclass := BundleTriple.relativeClass_eq_of_isIsomorphic hA L R hi
  rw [BundleTriple.relativeClass_sum] at hclass
  exact hclass.symm

/-- An automorphism homotopic to identity has zero relative boundary class. -/
theorem BundleAutomorphism.boundaryClass_eq_zero_of_isElementary
    (A : Set X) (hA : IsClosed A) (a : BundleAutomorphism A) (h : a.IsElementary) :
    a.boundaryClass A hA = 0 := by
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let p := idempotentPresentation (E := a.bundle.Fiber)
  let F := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let e : Iso (a.bundle.sum F).Fiber (FiniteBundle.trivial A p.size).Fiber :=
    (nonempty_presentation_complement_iso (E := a.bundle.Fiber)).some
  let T := FiniteBundle.trivial X p.size
  let t := pullbackTrivialIso (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) p.size
  let S : Iso (T.restrict A).Fiber (a.bundle.sum F).Fiber := t.trans e.symm
  -- Add the same complementary identity throughout the given elementary homotopy.
  obtain ⟨H⟩ := h
  obtain ⟨K⟩ := H.nonempty_sum_refl (Iso.refl F.Fiber)
  obtain ⟨L⟩ := (IsoHomotopy.refl S).nonempty_comp K
  obtain ⟨M⟩ := L.nonempty_comp (IsoHomotopy.refl S.symm)
  have hzero : (S.trans ((Iso.refl a.bundle.Fiber).sum (Iso.refl F.Fiber))).trans
      S.symm = RelativeTriple.identity T.Fiber A := by
    apply Iso.ext
    intro x
    apply LinearEquiv.ext
    intro v
    exact (S.linearEquiv x).symm_apply_apply v
  have hone : (S.trans (a.automorphism.sum (Iso.refl F.Fiber))).trans S.symm =
      (a.boundaryTriple A hA).boundary := by
    apply Iso.ext
    intro x
    rfl
  -- Conjugation uses precisely the original complement and pullback coordinates.
  rw [hzero, hone] at M
  have hclass := bundleTriple_relativeClass_eq_of_homotopy hA T T
    (RelativeTriple.identity T.Fiber A) (a.boundaryTriple A hA).boundary M
  change (BundleTriple.identity A T).relativeClass hA = a.boundaryClass A hA at hclass
  rw [BundleTriple.relativeClass_identity] at hclass
  exact hclass.symm

/-- KA II.3.21: the actual automorphism boundary descends through the K^{-1} presentation. -/
def bundleKMinusOneBoundary (A : Set X) (hA : IsClosed A) :
    BundleKMinusOne A →+ RelativeKZero A hA :=
  bundleKMinusOneLift A (fun a ↦ a.boundaryClass A hA)
    (fun a b h ↦ a.boundaryClass_eq_of_isIsomorphic A hA b h)
    (fun a b ↦ a.boundaryClass_sum A hA b)
    (fun a h ↦ a.boundaryClass_eq_zero_of_isElementary A hA h)

/-- The quotient boundary sends a generator to its specified relative triple class. -/
theorem bundleKMinusOneBoundary_class (A : Set X) (hA : IsClosed A)
    (a : BundleAutomorphism A) :
    bundleKMinusOneBoundary A hA a.kMinusOneClass = a.boundaryClass A hA := by
  exact bundleKMinusOneLift_apply A _ _ _ _ a

/-- If the bundle extends to X, the boundary is the original triple (E,E,α) over A. -/
theorem bundleKMinusOneBoundary_restricted (A : Set X) (hA : IsClosed A)
    (E : FiniteBundle X) (α : RelativeTriple E.Fiber E.Fiber A) :
    bundleKMinusOneBoundary A hA
        (BundleAutomorphism.kMinusOneClass ⟨E.restrict A, α⟩) =
      (BundleTriple.ofBoundary E E α).relativeClass hA := by
  -- Choose the complement on the whole original compact base, then restrict that same data.
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let p := idempotentPresentation (E := E.Fiber)
  let F := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let e : Iso (E.sum F).Fiber (FiniteBundle.trivial X p.size).Fiber :=
    (nonempty_presentation_complement_iso (E := E.Fiber)).some
  let T := FiniteBundle.trivial X p.size
  let t := pullbackTrivialIso (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)) p.size
  let a : BundleAutomorphism A := ⟨E.restrict A, α⟩
  let d : Iso (a.bundle.sum (F.restrict A)).Fiber
      (FiniteBundle.trivial A p.size).Fiber :=
    ((restrictSumIso A).symm.trans (e.restrict A)).trans t
  rw [bundleKMinusOneBoundary_class]
  change a.boundaryClass A hA = _
  rw [a.boundaryClass_eq_of_complement A hA (F.restrict A) p.size d]
  let L := (BundleTriple.ofBoundary E E α).sum (BundleTriple.identity A F)
  let R := a.boundaryTripleOfComplement A (F.restrict A) p.size d
  have hi : L.IsIsomorphic R := by
    refine ⟨e, e, ?_⟩
    intro x v
    change E.Fiber x × F.Fiber x at v
    have hd : d.linearEquiv x ((restrictSumIso A).linearEquiv x v) =
        t.linearEquiv x (e.linearEquiv x v) := by
      change t.linearEquiv x ((e.restrict A).linearEquiv x
        (((restrictSumIso A).linearEquiv x).symm
          ((restrictSumIso A).linearEquiv x v))) = _
      erw [LinearEquiv.symm_apply_apply]
      rfl
    have hdinv : (d.linearEquiv x).symm (t.linearEquiv x (e.linearEquiv x v)) =
        (restrictSumIso A).linearEquiv x v :=
      ((d.linearEquiv x).eq_symm_apply.mpr hd).symm
    change e.linearEquiv x (L.boundary.linearEquiv x v) =
      (t.linearEquiv x).symm (d.linearEquiv x
        ((Iso.sum α (Iso.refl (F.restrict A).Fiber)).linearEquiv x
          ((d.linearEquiv x).symm (t.linearEquiv x (e.linearEquiv x v)))))
    apply (t.linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, hdinv]
    rfl
  -- Global conjugation compares with (E,E,α) plus a genuinely extending identity triple.
  have hclass := BundleTriple.relativeClass_eq_of_isIsomorphic hA L R hi
  change ((BundleTriple.ofBoundary E E α).sum (BundleTriple.identity A F)).relativeClass hA =
    R.relativeClass hA at hclass
  rw [BundleTriple.relativeClass_sum, BundleTriple.relativeClass_identity, add_zero] at hclass
  exact hclass.symm

end AtiyahSinger.ComplexBundle
