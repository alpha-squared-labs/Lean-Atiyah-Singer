/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.KZeroProduct

/-!
# The ring structure on the existing projective K group

Public module ID: M1924.

Package the already specified tensor multiplication, free rank-one unit and
their laws as a commutative ring. The carrier and additive group remain the
original quotient of finite idempotent presentations. In particular, this
instance does not select a new multiplication or a different K-theory model.

Source: Hatcher, Vector Bundles and K-Theory, §2.1, p.40, Ring Structure;
the projective/idempotent realization is the existing `KZeroProduct` interface.
This package lets the associated-bundle map in SG III.13 (13.17) be stated as
an actual ring homomorphism. This instance uses the named tensor-product laws
from `KZeroProduct`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- Tensor multiplication and the free line give the original K group its standard ring. -/
instance commRingKZero (R : Type*) [CommRing R] : CommRing (KZero R) where
  __ := (inferInstance : AddCommGroup (KZero R))
  mul := fun x y ↦ kZeroMul R x y
  one := kZeroClass R (IdempotentMatrix.identity R 1)
  mul_assoc := kZeroMul_assoc
  mul_comm := kZeroMul_comm
  one_mul := kZeroMul_one_left
  mul_one x := (kZeroMul_comm x (kZeroClass R (IdempotentMatrix.identity R 1))).trans
    (kZeroMul_one_left x)
  left_distrib x y z := (kZeroMul R x).map_add y z
  right_distrib x y z := congrArg
    (fun f : KZero R →+ KZero R ↦ f z) ((kZeroMul R).map_add x y)
  zero_mul x := congrArg (fun f : KZero R →+ KZero R ↦ f x) (kZeroMul R).map_zero
  mul_zero x := (kZeroMul R x).map_zero

end AtiyahSinger
