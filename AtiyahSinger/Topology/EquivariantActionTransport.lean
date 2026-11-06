/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality

/-!
# Coherent transport of original equivariant support groups

Public module ID: M1755.

These implementation adapters transport the original support quotient along
an equality of its base actions. The generator calculation checks the same
underlying triple and actual total-space actions. Both homomorphism
postcomposition and proper pullback use this identical transport.
They are used to identify the native cotangent lift after group restriction;
no support presentation or mathematical object is replaced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle
open Bundle

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X]

private theorem structure_eq_of_action_eq [MulAction G X] [ContinuousSMul G X]
    {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)]
    (σ τ : EquivariantStructure G E) (h : σ.toMulAction = τ.toMulAction) : σ = τ := by
  have hlinear : σ.linearMap = τ.linearMap := by
    funext g x
    apply LinearMap.ext
    intro v
    exact TotalSpace.mk_injective (g • x)
      (congrArg (fun A : MulAction G (TotalSpace Unit E) ↦ A.smul g ⟨x, v⟩) h)
  cases σ
  cases τ
  cases hlinear
  rfl

/-- Transport the original quotient along equality of the actual base actions. -/
def kActionTransport (A B : MulAction G X)
    (hA : letI := A; ContinuousSMul G X)
    (hB : letI := B; ContinuousSMul G X) (h : A = B) :
    (letI := A; letI := hA; EquivariantSupportTripleKZero G X) →+
      (letI := B; letI := hB; EquivariantSupportTripleKZero G X) := by
  cases h
  exact AddMonoidHom.id _

/-- The same support triple and the same total actions yield the transported generator. -/
theorem kActionTransport_generator (A B : MulAction G X)
    (hA : letI := A; ContinuousSMul G X)
    (hB : letI := B; ContinuousSMul G X) (h : A = B)
    (t : SupportBundleTriple X)
    (σ : letI := A; letI := hA; SupportBundleTriple.EquivariantStructure G t)
    (τ : letI := B; letI := hB; SupportBundleTriple.EquivariantStructure G t)
    (hs : (letI := A; letI := hA; σ.sourceAction.toMulAction) =
      (letI := B; letI := hB; τ.sourceAction.toMulAction))
    (ht : (letI := A; letI := hA; σ.targetAction.toMulAction) =
      (letI := B; letI := hB; τ.targetAction.toMulAction)) :
    kActionTransport A B hA hB h
      (letI := A; letI := hA; EquivariantSupportBundleTriple.kZeroClass ⟨t, σ⟩) =
        (letI := B; letI := hB; EquivariantSupportBundleTriple.kZeroClass ⟨t, τ⟩) := by
  cases h
  let := A
  let := hA
  have hsource := structure_eq_of_action_eq σ.sourceAction τ.sourceAction hs
  have htarget := structure_eq_of_action_eq σ.targetAction τ.targetAction ht
  have heq : σ = τ := by
    cases σ
    cases τ
    cases hsource
    cases htarget
    rfl
  cases heq
  rfl

/-- Transporting a homomorphism is postcomposition by the same native action transport. -/
theorem transport_hom_eq_comp (A B : MulAction G X)
    (hA : letI := A; ContinuousSMul G X)
    (hB : letI := B; ContinuousSMul G X) (h : A = B)
    {C : Type*} [AddCommGroup C]
    (f : C →+ (letI := A; letI := hA; EquivariantSupportTripleKZero G X)) :
    (by
      have transport (a b : MulAction G X)
          (ha : letI := a; ContinuousSMul G X)
          (hb : letI := b; ContinuousSMul G X) (hab : a = b) :
          (C →+ (letI := a; letI := ha; EquivariantSupportTripleKZero G X)) →
            (C →+ (letI := b; letI := hb; EquivariantSupportTripleKZero G X)) := by
        cases hab
        exact id
      exact transport A B hA hB h f) =
        (kActionTransport A B hA hB h).comp f := by
  cases h
  rfl

variable {Y : Type*} [TopologicalSpace Y]

/-- Proper pullback commutes with transport of both actual base actions. -/
theorem kActionTransport_pullback (A B : MulAction G X) (C D : MulAction G Y)
    (hA : letI := A; ContinuousSMul G X) (hB : letI := B; ContinuousSMul G X)
    (hC : letI := C; ContinuousSMul G Y) (hD : letI := D; ContinuousSMul G Y)
    (hX : A = B) (hY : C = D) (f : C(Y, X))
    (heqA : letI := A; letI := C; ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (heqB : letI := B; letI := D; ∀ (g : G) (y : Y), f (g • y) = g • f y)
    (hf : IsProperMap f) :
    (kActionTransport C D hC hD hY).comp
      (letI := A; letI := hA; letI := C; letI := hC;
        equivariantSupportTripleKZeroPullback f heqA hf) =
      (letI := B; letI := hB; letI := D; letI := hD;
        equivariantSupportTripleKZeroPullback f heqB hf).comp
          (kActionTransport A B hA hB hX) := by
  cases hX
  cases hY
  rfl

end AtiyahSinger.ComplexBundle
