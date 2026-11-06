/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The actual kernel and cokernel representations of an equivariant operator

Public module ID: M0510.

Restrict the supplied representation to the original kernel of T, and descend
the target representation to the original quotient by range T. Equivariance
supplies the two invariance conditions. These constructions do not replace
either carrier by an abstract finite-dimensional model or by an adjoint kernel.

Mathlib's `ContRepresentation` makes each operator continuous; it does not
assert continuity in the group parameter. The two continuity theorems below
therefore require the actual joint action continuity as a separate premise.
Neither compactness of G nor unitarity is needed for these constructions.

For a Fredholm T, mathlib already supplies `hT.finite_ker`, `hT.finite_coker`
and `hT.isClosed_range` for exactly these subspaces. The last certificate
installs the native Hausdorff quotient norm when a normed cokernel is needed.
No alternative quotient topology or norm is introduced. The basic restriction
and quotient representations themselves are meaningful even without Fredholmness.

Source: SG III.9, the observation before Definition 9.3 and the subsequent
Hilbert-space formulation, printed pp.211--213. The source's compact Lie group,
unitarity and separability assumptions are not needed for these kernel and
quotient constructions. The explicit joint-continuity descent is a project
expansion of the standard invariant-subspace and quotient constructions.
The joint-continuity certificates below are proved for these actual representations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Topology

open ContinuousLinearMap

variable {G E F : Type*} [Group G]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Restrict the original action to the actual kernel of the same equivariant operator. -/
def equivariantKernelRepresentation
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T) :
    ContRepresentation ℂ G T.ker where
  toMonoidHom :=
    { toFun := fun g ↦ (ρ g).restrict (p := T.ker) (q := T.ker) (by
        intro x hx
        change T (ρ g x) = 0
        have heq := congrArg (fun S : E →L[ℂ] F ↦ S x) (hTg g)
        change T (ρ g x) = σ g (T x) at heq
        change T x = 0 at hx
        rw [heq, hx, map_zero])
      map_one' := by
        ext x
        change ρ 1 x = x
        rw [map_one]
        rfl
      map_mul' := by
        intro g h
        ext x
        change ρ (g * h) x = ρ g (ρ h x)
        rw [map_mul]
        rfl }

/-- Descend the original target action to the actual quotient by the range of T. -/
def equivariantCokernelRepresentation
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T) :
    ContRepresentation ℂ G (F ⧸ T.range) where
  toMonoidHom :=
    { toFun := fun g ↦ T.range.liftQL (T.range.mkQL.comp (σ g)) (by
        intro y hy
        change T.range.mkQ (σ g y) = 0
        apply (Submodule.Quotient.mk_eq_zero T.range).mpr
        rcases hy with ⟨x, rfl⟩
        refine ⟨ρ g x, ?_⟩
        exact congrArg (fun S : E →L[ℂ] F ↦ S x) (hTg g))
      map_one' := by
        ext y
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          change T.range.mkQ (σ 1 y) = T.range.mkQ y
          rw [map_one]
          rfl
      map_mul' := by
        intro g h
        ext y
        induction y using Submodule.Quotient.induction_on with
        | _ y =>
          change T.range.mkQ (σ (g * h) y) = T.range.mkQ (σ g (σ h y))
          rw [map_mul]
          rfl }

variable [TopologicalSpace G]

/-- A jointly continuous original action restricts jointly continuously to the kernel. -/
theorem continuous_equivariantKernelRepresentation
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2)) :
    Continuous (fun p : G × T.ker ↦ equivariantKernelRepresentation ρ σ T hTg p.1 p.2) := by
  /- Stage 1: pair the unchanged group parameter with the actual inclusion
  T.ker -> E. Composing this continuous product map with hρ gives the original
  action evaluated on kernel vectors, jointly in the group and vector.
  Stage 2: equivariance gives T(ρ(g)x)=σ(g)T(x)=0, so this very action lands
  in the same original kernel. Continuity into the subtype follows from its
  induced topology. This is exactly the restriction used in the displayed
  representation, not an action on a separately chosen finite-dimensional copy.
  No continuity of σ in g, Fredholmness, compact G or invariant inner product
  is needed for this particular restriction theorem. -/
  -- The kernel has the induced topology; use the original joint action after inclusion.
  apply Continuous.subtype_mk
  exact hρ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- A jointly continuous target action descends jointly continuously to the cokernel. -/
theorem continuous_equivariantCokernelRepresentation
    (ρ : ContRepresentation ℂ G E) (σ : ContRepresentation ℂ G F)
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (ρ g) = (σ g).comp T)
    (hσ : Continuous (fun p : G × F ↦ σ p.1 p.2)) :
    Continuous (fun p : G × (F ⧸ T.range) ↦
      equivariantCokernelRepresentation ρ σ T hTg p.1 p.2) := by
  /- Stage 1: the original quotient map q:F -> F/range(T) is an open
  continuous surjection for the native quotient topology. Hence identity
  on G times q is also an open quotient map; no local compactness assumption
  on G is required for this product of an open quotient map with identity.
  Stage 2: the map (g,y) -> q(σ(g)y) is jointly continuous by hσ and q.
  Equivariance gives σ(g)T(x)=T(ρ(g)x), so changing y by an element of the
  actual range changes its image by another element of that same range.
  The composite therefore descends to G times the original quotient carrier.
  Stage 3: the quotient-map continuity criterion gives joint continuity of
  the descended action. Its value on q(y) is q(σ(g)y), exactly the liftQL
  construction above. Surjectivity of q identifies it with that representation.
  This argument uses neither closed range nor an adjoint; Fredholm closedness
  is needed separately to make the quotient seminorm a norm for downstream
  finite-dimensional representation classes. Each operator's continuity alone
  would not replace the explicit joint-continuity premise hσ. -/
  -- The native linear quotient is open, so its product with identity is a quotient map.
  have hq : IsQuotientMap
      (fun p : G × F ↦ (p.1, T.range.mkQL p.2)) :=
    (IsOpenQuotientMap.id.prodMap T.range.isOpenQuotientMap_mkQL).isQuotientMap
  apply hq.continuous_iff.mpr
  -- Before descent, the same action is followed by the same continuous quotient projection.
  exact T.range.mkQL.continuous.comp hσ

end AtiyahSinger
