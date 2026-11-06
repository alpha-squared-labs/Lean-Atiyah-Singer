/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Compactly supported scalar symbols and their homotopies

Public module ID: M2113.

A nonvanishing continuous scalar on the exterior of a compact set acts on the
original finite bundle. A scalar homotopy on one common exterior gives an
actual bundle-isomorphism homotopy with that fixed compact control.

These are the scalar form of the standard support-triple construction. They
are used in the direct circle normalization to keep both the Fourier boundary
and the point symbol, including the sign of its complex coordinate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

attribute [local instance] isFiniteRank_restrict isFiniteRank_pullback

/-- A nowhere-zero continuous scalar acts as an automorphism of the same finite bundle. -/
def Iso.scalar (c : C(X, ℂ)) (hc : ∀ x, c x ≠ 0) : Iso E E := by
  let p : C(TotalSpace Unit E, X) := ⟨TotalSpace.proj, continuous_proj⟩
  have hv : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit E → X) *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hs := continuous_smul_section ((p : TotalSpace Unit E → X) *ᵖ E)
    (c.comp p) (fun z ↦ z.snd) hv
  let m : Hom E E :=
    { linearMap x := c x • LinearMap.id
      continuous_total := by
        change Continuous (fun z : TotalSpace Unit E ↦
          (⟨z.proj, c z.proj • z.snd⟩ : TotalSpace Unit E))
        exact (Pullback.continuous_lift Unit E p).comp hs }
  exact m.toIso (fun x ↦ (LinearEquiv.smulOfNeZero ℂ (E x) (c x) (hc x)).bijective)

/-- The scalar symbol retains the supplied compact control and the original bundle. -/
def scalarSupportTriple (K : Set X) (hK : IsCompact K)
    (c : C((Kᶜ : Set X), ℂ)) (hc : ∀ x, c x ≠ 0) : CompactSupportTriple E E where
  control := K
  isCompact_control := hK
  boundary := Iso.scalar (Restrict E Kᶜ) c hc

/-- A pointwise nonzero scalar boundary homotopy compares the actual support triples. -/
theorem CompactSupportTriple.homotopic_of_scalar
    (a b : CompactSupportTriple E E) (K : Set X) (hK : IsCompact K)
    (ha : a.control ⊆ K) (hb : b.control ⊆ K)
    (c : C(unitInterval × (Kᶜ : Set X), ℂ)) (hc : ∀ x, c x ≠ 0)
    (hzero : ∀ (x : (Kᶜ : Set X)) (v : E x.val),
      (a.enlarge K hK ha).boundary.linearEquiv x v = c (0, x) • v)
    (hone : ∀ (x : (Kᶜ : Set X)) (v : E x.val),
      (b.enlarge K hK hb).boundary.linearEquiv x v = c (1, x) • v) :
    a.Homotopic b := by
  let p : C(unitInterval × (Kᶜ : Set X), (Kᶜ : Set X)) := ⟨Prod.snd, continuous_snd⟩
  let P := (p : unitInterval × (Kᶜ : Set X) → (Kᶜ : Set X)) *ᵖ (Restrict E Kᶜ)
  -- Use the same pulled-back bundle and scalar map over the whole cylinder.
  refine ⟨K, hK, ha, hb, ⟨{ iso := Iso.scalar P c hc, map_zero := ?_, map_one := ?_ }⟩⟩
  · intro x v
    exact (hzero x v).symm
  · intro x v
    exact (hone x v).symm

end AtiyahSinger.ComplexBundle
