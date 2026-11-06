/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportTripleTransport
public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The explicit complex phase removing the Dirac symbol factor

Public module ID: M2196.

The nonzero scalar multiple of an actual bundle isomorphism retains its two
original bundles. A compact-support triple keeps the identical control set.
The path exp((1-t) pi i / 2) joins i to one, never vanishes, and multiplies
the very same exterior map throughout. Its inverse is the reciprocal phase
times that original inverse. This records an actual uniformly controlled
boundary homotopy; equality of symbol classes is a consequence.

Sources: SG I.9.26 for controlled symbol classes; SG II.5 and III.13.10 for
the Dirac symbol. The explicit path implements the project's D_j=-i partial_j
convention, whose principal symbol is +i times Clifford multiplication.
This is multiplication of the boundary, with no exchange of its two bundles
and no change of chirality. Local ranks may vary and the exterior may be empty.
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

set_option linter.unusedSectionVars false in
/-- Scalar multiplication and its reciprocal preserve continuity of the same bundle map. -/
theorem Iso.continuous_smul (a : Iso E F) (c : ℂ) (hc : c ≠ 0) :
    Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, c • a.linearEquiv z.proj z.snd⟩ : TotalSpace Unit F)) ∧
    Continuous (fun z : TotalSpace Unit F ↦
      (⟨z.proj, (a.linearEquiv z.proj).symm
        ((LinearEquiv.smulOfNeZero ℂ (F z.proj) c hc).symm z.snd)⟩ : TotalSpace Unit E)) := by
  -- Regard the tautological vector as a section over the original total space.
  let p : C(TotalSpace Unit F, X) := ⟨fun z ↦ z.proj, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit F → X) *ᵖ F) := isFiniteRank_pullback p
  have hvector : Continuous (fun z : TotalSpace Unit F ↦
      (⟨z, z.snd⟩ : TotalSpace Unit ((p : TotalSpace Unit F → X) *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
    exact continuous_id.prodMk continuous_id
  have hscale (d : ℂ) : Continuous (fun z : TotalSpace Unit F ↦
      (⟨z.proj, d • z.snd⟩ : TotalSpace Unit F)) := by
    have hsection := continuous_smul_section ((p : TotalSpace Unit F → X) *ᵖ F)
      (ContinuousMap.const _ d) (fun z ↦ z.snd) hvector
    exact (Pullback.continuous_lift Unit F p).comp hsection
  -- The inverse uses the reciprocal on the same target fiber, then the original inverse.
  refine ⟨(hscale c).comp a.continuous_total, ?_⟩
  exact a.continuous_symm.comp (hscale c⁻¹)

/-- Multiply an actual bundle isomorphism by a specified nonzero complex scalar. -/
def Iso.smul (a : Iso E F) (c : ℂ) (hc : c ≠ 0) : Iso E F where
  linearEquiv x := (a.linearEquiv x).trans (LinearEquiv.smulOfNeZero ℂ (F x) c hc)
  continuous_total := (a.continuous_smul c hc).1
  continuous_symm := (a.continuous_smul c hc).2

/-- Nonzero scalar multiplication changes only the original exterior map. -/
def CompactSupportTriple.smul (a : CompactSupportTriple E F) (c : ℂ) (hc : c ≠ 0) :
    CompactSupportTriple E F where
  control := a.control
  isCompact_control := a.isCompact_control
  boundary := a.boundary.smul c hc

/-- The explicit nonvanishing phase joins the i-multiplied boundary to the original boundary. -/
theorem CompactSupportTriple.exists_iPhaseHomotopy (a : CompactSupportTriple E F) :
    ∃ H : IsoHomotopy (a.smul Complex.I Complex.I_ne_zero).boundary a.boundary,
      ∀ (t : I) (x : (a.controlᶜ : Set X)) (v : E x),
        H.iso.linearEquiv (t, x) v =
          Complex.exp (((((1 - (t : ℝ)) * Real.pi / 2 : ℝ) : ℂ) * Complex.I)) •
            a.boundary.linearEquiv x v := by
  let U := (a.controlᶜ : Set X)
  let q : C(I × U, U) := ⟨Prod.snd, continuous_snd⟩
  let E' := (q : I × U → U) *ᵖ (Restrict E a.controlᶜ)
  let F' := (q : I × U → U) *ᵖ (Restrict F a.controlᶜ)
  let : IsFiniteRank E' := isFiniteRank_pullback q
  let : IsFiniteRank F' := isFiniteRank_pullback q
  let b : Iso E' F' := Iso.pullback q a.boundary
  let phase : C(I × U, ℂ) :=
    ⟨fun x ↦ Complex.exp (((((1 - (x.1 : ℝ)) * Real.pi / 2 : ℝ) : ℂ) * Complex.I)),
      by fun_prop⟩
  -- Use the original pullback topology; the phase multiplies the original boundary.
  let p : C(TotalSpace Unit E', I × U) := ⟨fun z ↦ z.proj, continuous_proj⟩
  let : IsFiniteRank ((p : TotalSpace Unit E' → I × U) *ᵖ F') :=
    isFiniteRank_pullback p
  have hboundary : Continuous (fun z : TotalSpace Unit E' ↦
      (⟨z, b.linearEquiv z.proj z.snd⟩ :
        TotalSpace Unit ((p : TotalSpace Unit E' → I × U) *ᵖ F'))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F' p).continuous_iff]
    exact continuous_id.prodMk b.continuous_total
  have hscaled := continuous_smul_section ((p : TotalSpace Unit E' → I × U) *ᵖ F')
    (phase.comp p) (fun z ↦ b.linearEquiv z.proj z.snd) hboundary
  let m : Hom E' F' :=
    { linearMap := fun x ↦ phase x • (b.linearEquiv x).toLinearMap
      continuous_total := (Pullback.continuous_lift Unit F' p).comp hscaled }
  -- Nonvanishing gives a fiberwise inverse. Local finite rank supplies its continuity.
  have hbij (x : I × U) : Function.Bijective (m.linearMap x) := by
    exact ((b.linearEquiv x).trans
      (LinearEquiv.smulOfNeZero ℂ (F' x) (phase x) (Complex.exp_ne_zero _))).bijective
  let path : Iso E' F' := m.toIso hbij
  have hzero (x : U) : phase (0, x) = Complex.I := by
    simp only [phase, ContinuousMap.coe_mk, Set.Icc.coe_zero, sub_zero, one_mul,
      Complex.ofReal_div, Complex.ofReal_ofNat]
    exact Complex.exp_pi_div_two_mul_I
  have hone (x : U) : phase (1, x) = 1 := by
    simp [phase]
  -- Both endpoints retain the same two bundles and the identical compact control set.
  refine ⟨{ iso := path, map_zero := ?_, map_one := ?_ }, fun _ _ _ ↦ rfl⟩
  · intro x v
    change U at x
    change E x at v
    change phase (0, x) • a.boundary.linearEquiv x v =
      Complex.I • a.boundary.linearEquiv x v
    rw [hzero]
  · intro x v
    change U at x
    change E x at v
    change phase (1, x) • a.boundary.linearEquiv x v = a.boundary.linearEquiv x v
    rw [hone, one_smul]

variable [LocallyCompactSpace X] [T2Space X]

/-- The explicit i-to-one boundary homotopy leaves the actual compact-support class unchanged. -/
theorem CompactSupportTriple.compactSupportClass_smul_I (a : CompactSupportTriple E F) :
    (a.smul Complex.I Complex.I_ne_zero).compactSupportClass = a.compactSupportClass := by
  /- Use a.control for both endpoints. The two self-enlargements restrict
  the same original maps through identity fiber comparisons, so the phase
  path from exists_iPhaseHomotopy gives their required uniform Homotopic
  certificate. Apply compactSupportClass_eq_of_homotopic on the original
  bundles, without assuming equality of the target K classes. -/
  -- The explicit phase path changes only the boundary map on the original exterior.
  obtain ⟨H, _⟩ := a.exists_iPhaseHomotopy
  apply (a.smul Complex.I Complex.I_ne_zero).compactSupportClass_eq_of_homotopic a
  refine ⟨a.control, a.isCompact_control, Set.Subset.refl _, Set.Subset.refl _, ?_⟩
  -- Self-enlargement retains the same endpoints through the identity fiber comparisons.
  refine ⟨{ iso := H.iso, map_zero := ?_, map_one := ?_ }⟩
  · intro x v
    exact (H.map_zero x v).trans
      ((a.smul Complex.I Complex.I_ne_zero).enlarge_apply a.control
        a.isCompact_control (Set.Subset.refl _) x v).symm
  · intro x v
    exact (H.map_one x v).trans
      (a.enlarge_apply a.control a.isCompact_control (Set.Subset.refl _) x v).symm

end AtiyahSinger.ComplexBundle
