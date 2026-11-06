/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.GradedProductCutoff
public import AtiyahSinger.Topology.BundleIsoAffineHomotopy

/-!
# Affine Hermitian tensor homotopies on the original bundles

The two original boundary maps are expressed in one specified set of tensor
and sum coordinates. The reciprocal tensor matrix built from both factor maps and their
adjoints along the affine path gives a supported homotopy when it is bijective
outside the specified compact control.
Continuity is supplied by the complete endpoint boundaries; the auxiliary
fiber coordinates need no continuity hypothesis.

The associated-sphere application uses uniform conic estimates for the
actual full factors. This construction needs only the resulting common
compact exterior and does not assert that the intervening symbols are PDOs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct unitInterval

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {X : Type*} [TopologicalSpace X]
  {S T : X → Type*}
  [∀ x, AddCommGroup (S x)] [∀ x, Module ℂ (S x)]
  [TopologicalSpace (TotalSpace Unit S)] [IsFiniteRank S]
  [∀ x, AddCommGroup (T x)] [∀ x, Module ℂ (T x)]
  [TopologicalSpace (TotalSpace Unit T)] [IsFiniteRank T]
  {E₀ E₁ F₀ F₁ : X → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, InnerProductSpace ℂ (E₀ x)]
  [∀ x, FiniteDimensional ℂ (E₀ x)]
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, InnerProductSpace ℂ (E₁ x)]
  [∀ x, FiniteDimensional ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (F₀ x)] [∀ x, InnerProductSpace ℂ (F₀ x)]
  [∀ x, FiniteDimensional ℂ (F₀ x)]
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, InnerProductSpace ℂ (F₁ x)]
  [∀ x, FiniteDimensional ℂ (F₁ x)]

set_option maxHeartbeats 1000000 in
-- Keep the original four fibers and their fixed metrics throughout the affine path.
/-- The affine path of two factor maps and their adjoints gives a global supported homotopy. -/
theorem CompactSupportTriple.homotopic_of_affineHermitianTensor
    (a b : CompactSupportTriple S T) (K : Set X) (hK : IsCompact K)
    (ha : a.control ⊆ K) (hb : b.control ⊆ K)
    (e : ∀ x, ((E₀ x ⊗[ℂ] F₀ x) × (E₁ x ⊗[ℂ] F₁ x)) ≃ₗ[ℂ] S x)
    (f : ∀ x, ((E₁ x ⊗[ℂ] F₀ x) × (E₀ x ⊗[ℂ] F₁ x)) ≃ₗ[ℂ] T x)
    (p₀ p₁ : ∀ x, E₀ x →ₗ[ℂ] E₁ x) (q₀ q₁ : ∀ x, F₀ x →ₗ[ℂ] F₁ x)
    (hA : ∀ (x : (Kᶜ : Set X)) v,
      (a.enlarge K hK ha).boundary.linearEquiv x (e x.val v) =
        f x.val (reciprocalTensorSymbol
          (p₀ x.val) (p₀ x.val).adjoint (q₀ x.val) (q₀ x.val).adjoint v))
    (hB : ∀ (x : (Kᶜ : Set X)) v,
      (b.enlarge K hK hb).boundary.linearEquiv x (e x.val v) =
        f x.val (reciprocalTensorSymbol
          (p₁ x.val) (p₁ x.val).adjoint (q₁ x.val) (q₁ x.val).adjoint v))
    (hinvertible : ∀ (t : unitInterval) (x : (Kᶜ : Set X)),
      let P := (1 - (t : ℂ)) • p₀ x.val + (t : ℂ) • p₁ x.val
      let Q := (1 - (t : ℂ)) • q₀ x.val + (t : ℂ) • q₁ x.val
      Function.Bijective (reciprocalTensorSymbol P P.adjoint Q Q.adjoint)) :
    a.Homotopic b := by
  apply a.homotopic_of_affine b K hK ha hb
  intro t x
  let P := (1 - (t : ℂ)) • p₀ x.val + (t : ℂ) • p₁ x.val
  let Q := (1 - (t : ℂ)) • q₀ x.val + (t : ℂ) • q₁ x.val
  let L := reciprocalTensorSymbol P P.adjoint Q Q.adjoint
  -- Real coefficients commute with taking the adjoint for the same fixed metrics.
  have hP : P.adjoint =
      (1 - (t : ℂ)) • (p₀ x.val).adjoint + (t : ℂ) • (p₁ x.val).adjoint := by
    dsimp only [P]
    rw [map_add, map_smulₛₗ, map_smulₛₗ]
    simp only [map_sub, map_one, Complex.conj_ofReal]
  have hQ : Q.adjoint =
      (1 - (t : ℂ)) • (q₀ x.val).adjoint + (t : ℂ) • (q₁ x.val).adjoint := by
    dsimp only [Q]
    rw [map_add, map_smulₛₗ, map_smulₛₗ]
    simp only [map_sub, map_one, Complex.conj_ofReal]
  -- Each of the four tensor blocks is linear in its one factor map.
  have hmatrix :
      (1 - (t : ℂ)) • reciprocalTensorSymbol
        (p₀ x.val) (p₀ x.val).adjoint (q₀ x.val) (q₀ x.val).adjoint +
      (t : ℂ) • reciprocalTensorSymbol
        (p₁ x.val) (p₁ x.val).adjoint (q₁ x.val) (q₁ x.val).adjoint = L := by
    dsimp only [L]
    rw [hP, hQ]
    dsimp only [P, Q]
    apply LinearMap.ext
    intro v
    apply Prod.ext
    all_goals
      simp only [reciprocalTensorSymbol, TensorProduct.map_add_left,
        TensorProduct.map_add_right, TensorProduct.map_smul_left,
        TensorProduct.map_smul_right, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.prod_apply]
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      simp only [Function.prod, LinearMap.coprod_apply, LinearMap.add_apply,
        LinearMap.smul_apply, LinearMap.neg_apply]
      module
  have hpath :
      (1 - (t : ℂ)) • ((a.enlarge K hK ha).boundary.linearEquiv x).toLinearMap +
        (t : ℂ) • ((b.enlarge K hK hb).boundary.linearEquiv x).toLinearMap =
      (f x.val).toLinearMap.comp (L.comp (e x.val).symm.toLinearMap) := by
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := (e x.val).surjective v
    change (1 - (t : ℂ)) • (a.enlarge K hK ha).boundary.linearEquiv x (e x.val v) +
      (t : ℂ) • (b.enlarge K hK hb).boundary.linearEquiv x (e x.val v) =
        f x.val (L ((e x.val).symm (e x.val v)))
    rw [(e x.val).symm_apply_apply, hA, hB]
    have hm := LinearMap.congr_fun hmatrix v
    simpa only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul] using
      congrArg (f x.val) hm
  -- The specified coordinate isomorphisms carry the assumed bijection to this affine boundary.
  rw [hpath]
  exact (f x.val).bijective.comp ((hinvertible t x).comp (e x.val).symm.bijective)

end AtiyahSinger
