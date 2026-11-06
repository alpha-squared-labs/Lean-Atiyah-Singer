/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.OrthogonalDirectSum
public import AtiyahSinger.Topology.EquivariantBottNaturality
public import AtiyahSinger.Topology.EquivariantBottProduct
public import AtiyahSinger.Topology.EquivariantDifferentGroupProduct

/-!
# Orthogonal block restriction and the original Bott external product

Public module ID: M1975.

ASI I uses equation (2.6), p.494, inside Proposition (4.4), pp.504--505.
The class is the original SG wedge-minus-contraction exterior Bott class.
It is first restricted along the actual orthogonal direct-sum inclusion,
then pulled back by the specified inverse of finAddEquivProd. The result is
the existing different-group external product of the two original Bott classes.

All actions on the product-group domains are the existing native compHom
restrictions. No fresh Bott generator, action, K quotient or compact-control
model is introduced. The human proof retains the ordered exterior map and
the established reciprocal-cutoff/negative-square SG comparison. The product
of the two enlarged controls is kept throughout that comparison. Both ranks
may be zero. This is a topological class equality; it assumes no index formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle

set_option maxSynthPendingDepth 35

set_option maxHeartbeats 2000000 in

/-- Actual binary orthogonal restriction identifies the original Bott class with the
different-group external product in the specified complex coordinates. -/
theorem orthogonalExteriorBottClass_directSum (p q : ℕ) :
    letI := compactSpace_orthogonalGroup p
    letI := compactSpace_orthogonalGroup q
    letI : MulAction
        (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
        (EuclideanSpace ℂ (Fin p)) :=
      MulAction.compHom _ (ContinuousMonoidHom.fst
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
    letI : ContinuousSMul
        (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
        (EuclideanSpace ℂ (Fin p)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.fst
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
    letI : MulAction
        (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
        (EuclideanSpace ℂ (Fin q)) :=
      MulAction.compHom _ (ContinuousMonoidHom.snd
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).toMonoidHom
    letI : ContinuousSMul
        (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
        (EuclideanSpace ℂ (Fin q)) :=
      MulAction.continuousSMul_compHom (ContinuousMonoidHom.snd
        (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)).continuous
    letI : MulAction
        (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
        (EuclideanSpace ℂ (Fin (p + q))) :=
      MulAction.compHom _ (orthogonalDirectSumInclusion p q).toMonoidHom
    letI : ContinuousSMul
        (Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ)
        (EuclideanSpace ℂ (Fin (p + q))) :=
      MulAction.continuousSMul_compHom (orthogonalDirectSumInclusion p q).continuous
    let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := p) (m := q)).symm
    equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩
        (orthogonalDirectSumInclusion_complexification p q) e.toHomeomorph.isProperMap
        (equivariantSupportTripleKZeroRestrict (orthogonalDirectSumInclusion p q)
          (equivariantExteriorBottClass (orthogonalComplexification_unitary (p + q)))) =
      equivariantSupportKZeroDifferentGroupExternalProduct
        (equivariantExteriorBottClass (orthogonalComplexification_unitary p))
        (equivariantExteriorBottClass (orthogonalComplexification_unitary q)) := by
  /- Stage 1: equivariantExteriorBottClass_restrict identifies the left
  input with the same original exterior construction on the restricted
  complexification of R^(p+q). All parity bundles, the SG boundary and
  the singleton zero control are retained. Inflate the original p and q
  representations along the two actual product projections.
  Stage 2: use the original Hilbert direct sum WithLp 2 (C^p times C^q).
  Its complex-linear map into C^(p+q) is finAddEquivProd.symm composed
  with WithLp.prodContinuousLinearEquiv. The block-action equality above
  gives its actual equivariance. Apply equivariantExteriorBottClass_natural
  to these two original invariant Hermitian metrics. This step uses the
  full proper linear homeomorphism, not a properness claim for a projection.
  Stage 3: apply equivariantExteriorBottClass_prod to the two inflated
  representations in their given order. Its human proof retains the
  ordered exterior tensor map, the product of enlarged invariant compact
  controls, and the common-control reciprocal homotopy. The odd-odd source
  sign is essential when passing from the reciprocal positive-square
  blocks to the original negative-square SG boundary; no raw boundary
  matrices are silently identified.
  Stage 4: combine the same proper pullbacks. Restriction along fst and
  snd of the two original Bott classes is exactly the definition of
  equivariantSupportKZeroDifferentGroupExternalProduct. This yields the
  displayed equality on the original product carrier with its independent
  action, including either zero rank. No Bott inverse, point index, or
  target Atiyah--Singer formula enters the argument. -/
  let := compactSpace_orthogonalGroup p
  let := compactSpace_orthogonalGroup q
  let G := Matrix.orthogonalGroup (Fin p) ℝ × Matrix.orthogonalGroup (Fin q) ℝ
  let V := EuclideanSpace ℂ (Fin p)
  let W := EuclideanSpace ℂ (Fin q)
  let U := EuclideanSpace ℂ (Fin (p + q))
  let fst := ContinuousMonoidHom.fst
    (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)
  let snd := ContinuousMonoidHom.snd
    (Matrix.orthogonalGroup (Fin p) ℝ) (Matrix.orthogonalGroup (Fin q) ℝ)
  -- These distributive actions extend the exact native restrictions in the statement.
  let : DistribMulAction G V := DistribMulAction.compHom V fst.toMonoidHom
  let : SMulCommClass G ℂ V := ⟨fun g c x ↦ smul_comm (fst g) c x⟩
  let : ContinuousSMul G V := MulAction.continuousSMul_compHom fst.continuous
  let : DistribMulAction G W := DistribMulAction.compHom W snd.toMonoidHom
  let : SMulCommClass G ℂ W := ⟨fun g c x ↦ smul_comm (snd g) c x⟩
  let : ContinuousSMul G W := MulAction.continuousSMul_compHom snd.continuous
  let : DistribMulAction G U :=
    DistribMulAction.compHom U (orthogonalDirectSumInclusion p q).toMonoidHom
  let : SMulCommClass G ℂ U :=
    ⟨fun g c x ↦ smul_comm (orthogonalDirectSumInclusion p q g) c x⟩
  let : ContinuousSMul G U :=
    MulAction.continuousSMul_compHom (orthogonalDirectSumInclusion p q).continuous
  have hV (g : G) (x y : V) : inner ℂ (g • x) (g • y) = inner ℂ x y :=
    orthogonalComplexification_unitary p (fst g) x y
  have hW (g : G) (x y : W) : inner ℂ (g • x) (g • y) = inner ℂ x y :=
    orthogonalComplexification_unitary q (snd g) x y
  have hU (g : G) (x y : U) : inner ℂ (g • x) (g • y) = inner ℂ x y :=
    orthogonalComplexification_unitary (p + q) (orthogonalDirectSumInclusion p q g) x y
  have hsum (g : G) (x y : WithLp 2 (V × W)) :
      inner ℂ (g • x) (g • y) = inner ℂ x y :=
    congrArg₂ (fun a b : ℂ ↦ a + b)
      (hV g (WithLp.ofLp x).1 (WithLp.ofLp y).1)
      (hW g (WithLp.ofLp x).2 (WithLp.ofLp y).2)
  let e := (WithLp.prodContinuousLinearEquiv 2 ℂ V W).symm
  let c := (EuclideanSpace.finAddEquivProd (𝕜 := ℂ) (n := p) (m := q)).symm
  let t : WithLp 2 (V × W) ≃L[ℂ] U := e.symm.trans c
  have ht (g : G) (x : WithLp 2 (V × W)) : t (g • x) = g • t x :=
    orthogonalDirectSumInclusion_complexification p q g (WithLp.ofLp x)
  -- The specified finite coordinates compare the same unitary exterior classes.
  have hnatural := equivariantExteriorBottClass_natural hsum hU t ht
  have hproduct := equivariantExteriorBottClass_prod hV hW
  change equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ (fun _ _ ↦ rfl)
    e.toHomeomorph.isProperMap (equivariantExteriorBottClass hsum) =
      equivariantSupportKZeroExternalProduct
        (equivariantExteriorBottClass hV) (equivariantExteriorBottClass hW) at hproduct
  rw [← hnatural] at hproduct
  have hcomp := equivariantSupportTripleKZeroPullback_comp
    (⟨t, t.continuous⟩ : C(WithLp 2 (V × W), U))
    (⟨e, e.continuous⟩ : C(V × W, WithLp 2 (V × W))) ht (fun _ _ ↦ rfl)
    t.toHomeomorph.isProperMap e.toHomeomorph.isProperMap
  have hvalue := congrArg (fun f ↦ f (equivariantExteriorBottClass hU)) hcomp
  change equivariantSupportTripleKZeroPullback
      ((⟨t, t.continuous⟩ : C(_, U)).comp ⟨e, e.continuous⟩) _ _
        (equivariantExteriorBottClass hU) =
      equivariantSupportTripleKZeroPullback ⟨e, e.continuous⟩ (fun _ _ ↦ rfl)
        e.toHomeomorph.isProperMap
        (equivariantSupportTripleKZeroPullback ⟨t, t.continuous⟩ ht
          t.toHomeomorph.isProperMap (equivariantExteriorBottClass hU)) at hvalue
  change equivariantSupportTripleKZeroPullback ⟨c, c.continuous⟩
    (orthogonalDirectSumInclusion_complexification p q) c.toHomeomorph.isProperMap
      (equivariantExteriorBottClass hU) = _ at hvalue
  -- Restriction along the two actual projections is the given different-group product.
  change equivariantSupportTripleKZeroPullback ⟨c, c.continuous⟩
    (orthogonalDirectSumInclusion_complexification p q) c.toHomeomorph.isProperMap
    (equivariantSupportTripleKZeroRestrict (orthogonalDirectSumInclusion p q)
      (equivariantExteriorBottClass (orthogonalComplexification_unitary (p + q)))) =
    equivariantSupportKZeroExternalProduct
      (equivariantSupportTripleKZeroRestrict fst
        (equivariantExteriorBottClass (orthogonalComplexification_unitary p)))
      (equivariantSupportTripleKZeroRestrict snd
        (equivariantExteriorBottClass (orthogonalComplexification_unitary q)))
  rw [equivariantExteriorBottClass_restrict, equivariantExteriorBottClass_restrict,
    equivariantExteriorBottClass_restrict]
  exact hvalue.trans hproduct

end AtiyahSinger
