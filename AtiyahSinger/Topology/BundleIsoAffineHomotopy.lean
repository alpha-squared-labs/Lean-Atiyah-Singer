/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Affine homotopies on the original finite-rank bundles

Public module ID: M1578.

A pointwise invertible affine interpolation of two continuous bundle maps
is an actual bundle isomorphism over the entire cylinder. Local finite rank
supplies joint inverse continuity. Applying this on one compact exterior gives
a uniform supported homotopy, retaining the original bundles and boundaries.

This construction is used for the global product cutoff homotopy. Continuity
belongs to the complete bundle maps; pointwise scalar decompositions are only
needed to establish invertibility.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

attribute [local instance] isFiniteRank_restrict

/-- A fiberwise invertible affine interpolation is a joint homotopy of the same bundle maps. -/
theorem Iso.exists_affineHomotopy (a b : Iso E F)
    (h : ∀ (t : I) (x : X), Function.Bijective
      ((1 - (t : ℂ)) • (a.linearEquiv x).toLinearMap +
        (t : ℂ) • (b.linearEquiv x).toLinearMap)) :
    ∃ H : IsoHomotopy a b, ∀ (t : I) (x : X) (v : E x),
      H.iso.linearEquiv (t, x) v =
        (1 - (t : ℂ)) • a.linearEquiv x v + (t : ℂ) • b.linearEquiv x v := by
  let q : C(I × X, X) := ⟨Prod.snd, continuous_snd⟩
  let E' := (q : I × X → X) *ᵖ E
  let F' := (q : I × X → X) *ᵖ F
  let : IsFiniteRank E' := isFiniteRank_pullback q
  let : IsFiniteRank F' := isFiniteRank_pullback q
  let A : Iso E' F' := Iso.pullback q a
  let B : Iso E' F' := Iso.pullback q b
  let p : C(TotalSpace Unit E', I × X) := ⟨fun z ↦ z.proj, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit E' → I × X) *ᵖ F') :=
    isFiniteRank_pullback p
  -- The two original continuous maps give continuous sections of one common pullback.
  have hA : Continuous (fun z : TotalSpace Unit E' ↦
      (⟨z, A.linearEquiv z.proj z.snd⟩ :
        TotalSpace Unit ((p : TotalSpace Unit E' → I × X) *ᵖ F'))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F' p).continuous_iff]
    exact continuous_id.prodMk A.continuous_total
  have hB : Continuous (fun z : TotalSpace Unit E' ↦
      (⟨z, B.linearEquiv z.proj z.snd⟩ :
        TotalSpace Unit ((p : TotalSpace Unit E' → I × X) *ᵖ F'))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F' p).continuous_iff]
    exact continuous_id.prodMk B.continuous_total
  let c₀ : C(TotalSpace Unit E', ℂ) :=
    ⟨fun z ↦ 1 - (z.proj.1 : ℂ), continuous_const.sub
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp p.continuous.fst))⟩
  let c₁ : C(TotalSpace Unit E', ℂ) :=
    ⟨fun z ↦ (z.proj.1 : ℂ),
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp p.continuous.fst)⟩
  have hsA := continuous_smul_section ((p : TotalSpace Unit E' → I × X) *ᵖ F')
    c₀ (fun z ↦ A.linearEquiv z.proj z.snd) hA
  have hsB := continuous_smul_section ((p : TotalSpace Unit E' → I × X) *ᵖ F')
    c₁ (fun z ↦ B.linearEquiv z.proj z.snd) hB
  have hsum := continuous_add_section ((p : TotalSpace Unit E' → I × X) *ᵖ F')
    (fun z ↦ c₀ z • A.linearEquiv z.proj z.snd)
    (fun z ↦ c₁ z • B.linearEquiv z.proj z.snd) hsA hsB
  let L : Hom E' F' :=
    { linearMap := fun z ↦ (1 - (z.1 : ℂ)) • (a.linearEquiv z.2).toLinearMap +
        (z.1 : ℂ) • (b.linearEquiv z.2).toLinearMap
      continuous_total := (Pullback.continuous_lift Unit F' p).comp hsum }
  -- Inverse continuity is proved for this entire cylinder map in its original topology.
  let path : Iso E' F' := L.toIso (fun z ↦ h z.1 z.2)
  refine ⟨{ iso := path, map_zero := ?_, map_one := ?_ }, fun _ _ _ ↦ rfl⟩
  · intro x v
    change (1 - ((0 : I) : ℂ)) • a.linearEquiv x v +
      ((0 : I) : ℂ) • b.linearEquiv x v = a.linearEquiv x v
    simp
  · intro x v
    change (1 - ((1 : I) : ℂ)) • a.linearEquiv x v +
      ((1 : I) : ℂ) • b.linearEquiv x v = b.linearEquiv x v
    simp

/-- One compact exterior on which the affine path is invertible gives supported homotopy. -/
theorem CompactSupportTriple.homotopic_of_affine (a b : CompactSupportTriple E F)
    (K : Set X) (hK : IsCompact K) (ha : a.control ⊆ K) (hb : b.control ⊆ K)
    (h : ∀ (t : I) (x : (Kᶜ : Set X)), Function.Bijective
      ((1 - (t : ℂ)) • ((a.enlarge K hK ha).boundary.linearEquiv x).toLinearMap +
        (t : ℂ) • ((b.enlarge K hK hb).boundary.linearEquiv x).toLinearMap)) :
    a.Homotopic b := by
  obtain ⟨H, _⟩ := (a.enlarge K hK ha).boundary.exists_affineHomotopy
    (b.enlarge K hK hb).boundary h
  exact ⟨K, hK, ha, hb, ⟨H⟩⟩

end AtiyahSinger.ComplexBundle
