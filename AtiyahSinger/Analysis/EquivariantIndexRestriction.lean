/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRestriction
public import AtiyahSinger.Analysis.EquivariantFredholmIndex

/-!
# Restriction of the actual equivariant Fredholm index

Public module ID: M0530.

Precompose the fixed source and target actions with a continuous group
homomorphism. The original bounded operator T, kernel, quotient by its range,
and Fredholm certificate remain unchanged. Its virtual representation index
restricts through the actual representation Grothendieck-group homomorphism.

This is the standard restriction naturality supplement to the kernel-minus-
cokernel definition in SG III.9, printed pp.211--213. No separately numbered
SG restriction lemma is claimed. The argument needs neither group compactness
nor unitary actions, a Hilbert adjoint or homotopy stability. The mathematical
proof below uses these same kernel and quotient actions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ContinuousLinearMap

variable {G H : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Restricting the group actions restricts the same operator's virtual kernel-cokernel index. -/
theorem equivariantFredholmIndex_restrict (φ : H →ₜ* G)
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2))
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hT : T.IsFredholm) :
    representationRestriction φ (equivariantFredholmIndex ρ σ hρ hσ T hTg hT) =
      equivariantFredholmIndex (ρ.restrict φ.toMonoidHom) (σ.restrict φ.toMonoidHom)
        (hρ.comp ((φ.continuous.comp continuous_fst).prodMk continuous_snd))
        (hσ.comp ((φ.continuous.comp continuous_fst).prodMk continuous_snd))
        T (fun h ↦ hTg (φ h)) hT := by
  /- Stage 1: use hT.finite_ker, hT.finite_coker and hT.isClosed_range for
  the same original T. Restricting its group actions does not change its
  kernel, range, native quotient, quotient norm or these finite dimensions.
  The covariance equation for h in H is precisely the original equation
  hTg evaluated at φ(h); no new operator or replacement Fredholm witness is used.
  Stage 2: restricting equivariantKernelRepresentation is the same actual
  action on T.ker as first restricting ρ and σ and then constructing the
  kernel representation. On the cokernel, both routes send the original
  quotient class q(y) to q(σ(φ(h))y). Quotient surjectivity identifies them.
  These are equal actions on the same carriers, not merely isomorphic vector
  spaces of equal dimension. Both joint continuity proofs come from the
  original hρ or hσ by the displayed continuous group precomposition.
  Stage 3: expand the existing index difference, use additivity of restriction
  and representationRestriction_class for each actual finite representation.
  The action identifications from Stage 2 give exactly the two terms in the
  restricted operator's index. No unitary metric, compact group averaging,
  semisimplicity, adjoint-kernel substitution or index stability is invoked. -/
  -- Restriction retains the same operator, finite carriers, and native quotient norm.
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : IsClosed (T.range : Set F) := hT.isClosed_range
  unfold equivariantFredholmIndex
  rw [map_sub, representationRestriction_class, representationRestriction_class]
  -- Both constructions evaluate the very same restricted actions at φ(h).
  rfl

end AtiyahSinger
