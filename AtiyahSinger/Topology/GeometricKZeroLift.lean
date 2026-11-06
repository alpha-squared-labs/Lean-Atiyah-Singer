/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiniteBundle

/-!
# Extending geometric bundle invariants through the existing K group

Public module ID: M1863.

an isomorphism-invariant, direct-sum-additive function on the actual
finite-rank bundles determines a function on continuous idempotent matrices
by taking their actual image bundles. Rectangular matrix equivalence gives
an isomorphism of these bundles; block diagonal sum gives their direct sum.
Consequently the existing algebraic K-zero universal property supplies an
additive extension, without introducing a second K-group carrier.

The grouped certificate below concerns only those two defining relations.
The value on every original bundle, and the geometric universal property,
are separate statements in GeometricKZeroUniversal. The image topology is
the existing subspace topology; neither a global rank nor a new topology is
chosen. Base and target-group universes are independent. FiniteBundle has
small fibers, and the finite-dimensional image bundles have those same small
fibers; the existing smallBundleIso handles larger original fiber universes.

Sources: SG I.9.3-9.4, p.59, gives the geometric group completion and its
universal property. Its complement route and Karoubi I.6 give the comparison
between bundles and idempotents used for the existing
algebraic presentation. The literal rectangular and block maps below are
implementation comparisons, not additional assumptions on the invariant.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Matrix

variable {X : Type*} [TopologicalSpace X] {G : Type*} [AddCommGroup G]

attribute [local instance] IdempotentMatrix.fiberTotalSpaceTopology
  IdempotentMatrix.isFiniteRank_fiber sumTopology isFiniteRank_sum

variable (φ : FiniteBundle X → G)
  (hiso : ∀ E F : FiniteBundle X, Iso E.Fiber F.Fiber → φ E = φ F)
  (hsum : ∀ E F : FiniteBundle X, φ (E.sum F) = φ E + φ F)

include hiso hsum in
set_option backward.isDefEq.respectTransparency.types false in
/-- Image bundles carry a geometric additive invariant to the two defining K-zero relations.
This grouped certificate supplies the existing algebraic universal property's hypotheses. -/
theorem bundleInvariant_image_properties :
    (∀ p q : IdempotentMatrix C(X, ℂ), p.IsEquivalent q →
      φ (FiniteBundle.ofFamily (fun x ↦ p.fiber x)) =
        φ (FiniteBundle.ofFamily (fun x ↦ q.fiber x))) ∧
    (∀ p q : IdempotentMatrix C(X, ℂ),
      φ (FiniteBundle.ofFamily (fun x ↦ (p.blockSum q).fiber x)) =
        φ (FiniteBundle.ofFamily (fun x ↦ p.fiber x)) +
          φ (FiniteBundle.ofFamily (fun x ↦ q.fiber x))) := by
  /- Stage 1: for rectangular witnesses a,b of p.IsEquivalent q,
  evaluate the continuous matrix entries at each base point. The relations
  ab = p and ba = q make these maps inverse on the two actual images.
  Their total maps are continuous in the prescribed induced topologies.
  Thus they give a bundle isomorphism, and hiso equates the two values.
  Stage 2: concatenate the original image vectors, using exactly the
  finSumFinEquiv reindexing in blockMatrix. Its inverse splits the finite
  coordinates. These continuous maps identify the image bundle of the
  block sum with the actual direct sum of the two image bundles.
  Apply hiso to that isomorphism and then hsum. Neither argument uses
  compactness, a choice of bundle presentation, or a constant fiber rank. -/
  classical
  let ev (x : X) : C(X, ℂ) →+* ℂ := (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom
  -- Rectangular witnesses give continuous maps on the original image coordinates.
  have hmap (p q : IdempotentMatrix C(X, ℂ))
      (a : Matrix (Fin q.size) (Fin p.size) C(X, ℂ)) (ha : q.matrix * a = a) :
      ∃ f : Hom (fun x ↦ p.fiber x) (fun x ↦ q.fiber x),
        ∀ x v, (f.linearMap x v).val = (a.map (ev x)) *ᵥ v.val := by
    let f : Hom (fun x ↦ p.fiber x) (fun x ↦ q.fiber x) := {
      linearMap := fun x ↦
        ((Matrix.mulVecLin (a.map (ev x))).comp (p.fiber x).subtype).codRestrict
          (q.fiber x) fun v ↦ by
            refine ⟨(a.map (ev x)) *ᵥ v.val, ?_⟩
            change q.matrix.map (ev x) *ᵥ
              (a.map (ev x) *ᵥ v.val) =
              a.map (ev x) *ᵥ v.val
            rw [Matrix.mulVec_mulVec]
            have h := congrArg (fun M : Matrix _ _ C(X, ℂ) ↦ M.map (ev x)) ha
            simpa only [Matrix.map_mul] using congrArg (fun M ↦ M *ᵥ v.val) h
      continuous_total := by
        have hz : Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦
            (z.proj, z.snd.val)) := continuous_induced_dom
        apply continuous_induced_rng.mpr
        exact hz.fst.prodMk ((continuous_pi fun i ↦ continuous_pi fun j ↦
          (a i j).continuous.comp hz.fst).matrix_mulVec hz.snd) }
    exact ⟨f, fun _ _ ↦ rfl⟩
  have hisoImage (p q : IdempotentMatrix C(X, ℂ)) (h : p.IsEquivalent q) :
      Nonempty (Iso (fun x ↦ p.fiber x) (fun x ↦ q.fiber x)) := by
    obtain ⟨a, b, hab, hba, hpa, hqb⟩ := h
    obtain ⟨f, hf⟩ := hmap p q b hqb
    obtain ⟨g, hg⟩ := hmap q p a hpa
    have hfix (p : IdempotentMatrix C(X, ℂ)) (x : X) (v : p.fiber x) :
        (p.matrix.map (ev x)) *ᵥ v.val = v.val := by
      obtain ⟨w, hw⟩ := v.property
      change (p.map (ev x)).matrix.mulVecLin v.val = _
      rw [← hw, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul,
        (p.map (ev x)).mul_self]
    have hinv (p q : IdempotentMatrix C(X, ℂ))
        (a : Matrix (Fin p.size) (Fin q.size) C(X, ℂ))
        (b : Matrix (Fin q.size) (Fin p.size) C(X, ℂ))
        (hab : a * b = p.matrix) (x : X) (v : p.fiber x) :
        (a.map (ev x)) *ᵥ ((b.map (ev x)) *ᵥ v.val) = v.val := by
      rw [Matrix.mulVec_mulVec]
      have h := congrArg (fun M : Matrix _ _ C(X, ℂ) ↦ M.map (ev x)) hab
      have heval : (a.map (ev x)) * (b.map (ev x)) =
          (p.matrix.map (ev x)) := by simpa only [Matrix.map_mul] using h
      rw [heval]
      exact hfix p x v
    refine ⟨f.toIso fun x ↦ ⟨?_, ?_⟩⟩
    · have hl : Function.LeftInverse (g.linearMap x) (f.linearMap x) := by
        intro v
        apply Subtype.ext
        rw [hg, hf]
        exact hinv p q a b hab x v
      exact hl.injective
    · have hr : Function.RightInverse (g.linearMap x) (f.linearMap x) := by
        intro v
        apply Subtype.ext
        rw [hf, hg]
        exact hinv q p b a hba x v
      exact hr.surjective
  constructor
  · intro p q hpq
    exact hiso _ _ (Classical.choice (hisoImage p q hpq))
  · intro p q
    -- Split exactly the finite coordinates used in the original block sum.
    let c : (Fin (p.size + q.size) → ℂ) ≃ₗ[ℂ]
        (Fin p.size → ℂ) × (Fin q.size → ℂ) :=
      (LinearEquiv.piCongrLeft' ℂ (fun _ : Fin (p.size + q.size) ↦ ℂ)
        finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ ℂ ℂ)
    have hc_apply (v : Fin (p.size + q.size) → ℂ) :
        c v = (v ∘ Fin.castAdd q.size, v ∘ Fin.natAdd p.size) := rfl
    have hc (x : X) (v : Fin (p.size + q.size) → ℂ) :
        c (((p.blockSum q).matrix.map (ev x)) *ᵥ v) =
          ((p.matrix.map (ev x)) *ᵥ (c v).1,
            (q.matrix.map (ev x)) *ᵥ (c v).2) := by
      have hm : ((p.blockSum q).matrix.map (ev x)) =
          (Matrix.fromBlocks (p.matrix.map (ev x)) 0 0
            (q.matrix.map (ev x))).submatrix
              finSumFinEquiv.symm finSumFinEquiv.symm := by
        ext i j
        change (Matrix.fromBlocks p.matrix 0 0 q.matrix
          (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) x = _
        simp only [Matrix.submatrix_apply]
        cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> rfl
      dsimp only [IdempotentMatrix.blockSum] at hm ⊢
      rw [hm]
      change c ((Matrix.fromBlocks
        (p.matrix.map (ev x)) 0 0
        (q.matrix.map (ev x))).submatrix
          finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ v) = _
      rw [Matrix.submatrix_mulVec_equiv _ _ _ finSumFinEquiv.symm,
        Matrix.fromBlocks_mulVec]
      apply Prod.ext <;> ext i <;> simp [hc_apply, Function.comp_def]
    have hmem (x : X) (v : (p.blockSum q).fiber x) :
        (c v.val).1 ∈ p.fiber x ∧ (c v.val).2 ∈ q.fiber x := by
      obtain ⟨w, hw⟩ := v.property
      change ((p.blockSum q).matrix.map (ev x)) *ᵥ w = v.val at hw
      have hcw := hc x w
      have hv : c v.val =
          (p.matrix.map (ev x) *ᵥ (c w).1,
            q.matrix.map (ev x) *ᵥ (c w).2) :=
        (congrArg c hw).symm.trans hcw
      rw [hv]
      exact ⟨⟨(c w).1, rfl⟩, ⟨(c w).2, rfl⟩⟩
    let f : Hom (fun x ↦ (p.blockSum q).fiber x)
        ((fun x ↦ p.fiber x) ×ᵇ (fun x ↦ q.fiber x)) := {
      linearMap := fun x ↦ {
        toFun := fun v ↦ (⟨(c v.val).1, (hmem x v).1⟩, ⟨(c v.val).2, (hmem x v).2⟩)
        map_add' := fun v w ↦ by
          apply Prod.ext
          · exact Subtype.ext (congrArg Prod.fst (c.map_add v.val w.val))
          · exact Subtype.ext (congrArg Prod.snd (c.map_add v.val w.val))
        map_smul' := fun r v ↦ by
          apply Prod.ext
          · exact Subtype.ext (congrArg Prod.fst (c.map_smul r v.val))
          · exact Subtype.ext (congrArg Prod.snd (c.map_smul r v.val)) }
      continuous_total := by
        have hz : Continuous (fun z : TotalSpace Unit (fun x ↦ (p.blockSum q).fiber x) ↦
            (z.proj, z.snd.val)) := continuous_induced_dom
        have hp : Continuous (fun z : TotalSpace Unit (fun x ↦ (p.blockSum q).fiber x) ↦
            (z.proj, (c z.snd.val).1)) :=
          hz.fst.prodMk (continuous_pi fun i ↦
            (continuous_apply (Fin.castAdd q.size i)).comp hz.snd)
        have hq : Continuous (fun z : TotalSpace Unit (fun x ↦ (p.blockSum q).fiber x) ↦
            (z.proj, (c z.snd.val).2)) :=
          hz.fst.prodMk (continuous_pi fun i ↦ (continuous_apply (Fin.natAdd p.size i)).comp hz.snd)
        apply continuous_induced_rng.mpr
        exact (continuous_induced_rng.mpr hp).prodMk (continuous_induced_rng.mpr hq) }
    have hf : ∀ x, Function.Bijective (f.linearMap x) := by
      intro x
      constructor
      · intro v w hvw
        apply Subtype.ext
        apply c.injective
        exact Prod.ext (congrArg (fun z ↦ z.1.val) hvw) (congrArg (fun z ↦ z.2.val) hvw)
      · rintro ⟨v, w⟩
        obtain ⟨a, ha⟩ := v.property
        obtain ⟨b, hb⟩ := w.property
        refine ⟨((p.blockSum q).map (ev x)).matrix.mulVecLin.rangeRestrict (c.symm (a, b)), ?_⟩
        apply Prod.ext <;> apply Subtype.ext
        · change (c (((p.blockSum q).matrix.map (ev x)) *ᵥ c.symm (a, b))).1 = v.val
          rw [hc, c.apply_symm_apply]
          exact ha
        · change (c (((p.blockSum q).matrix.map (ev x)) *ᵥ c.symm (a, b))).2 = w.val
          rw [hc, c.apply_symm_apply]
          exact hb
    -- The actual block-image bundle isomorphism supplies additivity of the invariant.
    exact (hiso _ _ (f.toIso hf)).trans (hsum _ _)

/-- The additive extension obtained from actual image bundles in the existing K-zero carrier. -/
def bundleKZeroLift : KZero C(X, ℂ) →+ G :=
  (kZero_universal_property
    (fun p : IdempotentMatrix C(X, ℂ) ↦ φ (FiniteBundle.ofFamily (fun x ↦ p.fiber x)))
    (bundleInvariant_image_properties φ hiso hsum).1
    (bundleInvariant_image_properties φ hiso hsum).2).choose

/-- On an image-bundle generator the chosen extension has exactly the prescribed value. -/
theorem bundleKZeroLift_image (p : IdempotentMatrix C(X, ℂ)) :
    bundleKZeroLift φ hiso hsum (AtiyahSinger.kZeroClass C(X, ℂ) p) =
      φ (FiniteBundle.ofFamily (fun x ↦ p.fiber x)) := by
  /- Unfold the lift selected by the existing K-zero universal property.
  Its generator specification evaluates on this exact idempotent p and
  gives the value of φ on its original image bundle. Both sides retain
  the same induced total topology and finite coordinate image. -/
  exact (kZero_universal_property
    (fun p : IdempotentMatrix C(X, ℂ) ↦ φ (FiniteBundle.ofFamily (fun x ↦ p.fiber x)))
    (bundleInvariant_image_properties φ hiso hsum).1
    (bundleInvariant_image_properties φ hiso hsum).2).choose_spec.1 p

end AtiyahSinger.ComplexBundle
