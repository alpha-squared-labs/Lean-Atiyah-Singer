/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Locally trivial principal bundles on an existing total space

Public module ID: M2000.

A right G action is the supplied left action of G opposite: p*g is written
`MulOpposite.op g • p`. A principal bundle is an equivariantly locally trivial
projection from the original topological total space. Its local charts are
mathlib's actual `Bundle.Trivialization G projection`, and equivariance uses
right multiplication in their G coordinate. No replacement projection, total
space topology, or abstract fiber carrier is selected.

Source: SG Appendix A, printed p.370 / PDF p.382, includes equivariant local
triviality in its principal-bundle definition. HU IV.2 Definition 2.2, printed
p.42 / PDF p.63, uses a broader free-action/continuous-translation definition;
HU adds local triviality in IV.7 Definition 7.2, p.47 / PDF p.68. We use the
locally trivial SG scope, without conflating those two HU definitions.
Neither paracompactness nor Hausdorffness is needed for the elementary local
consequences below. The proofs retain the given projection, topology, and action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Topology

variable (G : Type*) [Group G] [TopologicalSpace G]
  {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [MulAction Gᵐᵒᵖ P]

/-- A locally trivial right principal G-bundle on the specified projection and topologies. -/
class IsPrincipalBundle [IsTopologicalGroup G] [ContinuousSMul Gᵐᵒᵖ P]
    (projection : P → B) : Prop where
  /-- The original projection is invariant under the supplied right action. -/
  projection_smul : ∀ (g : G) (p : P), projection (MulOpposite.op g • p) = projection p
  /-- Every base point lies in an actual right-equivariant local trivialization. -/
  exists_trivialization : ∀ b : B, ∃ e : Trivialization G projection,
    b ∈ e.baseSet ∧ ∀ (g : G) (p : P), projection p ∈ e.baseSet →
      (e (MulOpposite.op g • p)).2 = (e p).2 * g

variable {G} [IsTopologicalGroup G] [ContinuousSMul Gᵐᵒᵖ P]

/-- The actual projection of a locally trivial principal bundle is continuous, open and onto. -/
theorem IsPrincipalBundle.projection_properties {projection : P → B}
    (hP : IsPrincipalBundle G projection) :
    Continuous projection ∧ IsOpenMap projection ∧ Function.Surjective projection := by
  /- Stage 1: at each base point use the original local trivialization
  supplied by hP. On its actual source projection is first coordinate of
  that chart. The open chart domains cover P, so these local continuous
  formulas prove continuity of the same projection.
  Stage 2: the local model projection U times G -> U is open. Apply this
  to an open subset of each original chart domain and take the union over
  the covering. This proves openness on the unchanged total-space topology.
  Stage 3: for any b choose a chart whose base contains b. The actual
  inverse chart applied to (b,1) lies over b, since G has its identity.
  Thus the original projection is onto. Empty bases and empty total spaces
  are covered without adding a nonemptiness hypothesis. -/
  -- A chart over the image of each point identifies the projection neighborhoods.
  have hlocal (p : P) : Filter.map projection (𝓝 p) = 𝓝 (projection p) := by
    obtain ⟨e, he, _⟩ := hP.exists_trivialization (projection p)
    exact e.map_proj_nhds (e.mem_source.mpr he)
  have hcontinuous : Continuous projection := continuous_iff_continuousAt.mpr
    (fun p ↦ (hlocal p).le)
  have hopen : IsOpenMap projection := IsOpenMap.of_nhds_le (fun p ↦ (hlocal p).ge)
  -- The identity of G supplies a point over every base point in its chosen chart.
  refine ⟨hcontinuous, hopen, ?_⟩
  intro b
  obtain ⟨e, he, _⟩ := hP.exists_trivialization b
  exact ⟨e.toOpenPartialHomeomorph.symm (b, 1), e.proj_symm_apply' he⟩

/-- The given right action is free and transitive on each actual projection fiber. -/
theorem IsPrincipalBundle.existsUnique_smul {projection : P → B}
    (hP : IsPrincipalBundle G projection) (p q : P)
    (hpq : projection p = projection q) :
    ∃! g : G, MulOpposite.op g • p = q := by
  /- Stage 1: take an equivariant chart above the common original base point.
  Write its group coordinates of p and q as a and b. The only candidate
  is g=a inverse times b, since the right action has coordinate a*g.
  Stage 2: projection invariance keeps p*g inside the same original chart.
  Chart equivariance and the chosen g give its coordinates equal to those
  of q. Injectivity of the chart on its source gives p*g=q.
  Stage 3: for another such g, applying the same group coordinate gives
  a*g=b. Left cancellation in G gives uniqueness. This proves freeness and
  fiberwise transitivity from the standard local definition rather than
  adding them as a separate assumption on a replacement action. -/
  obtain ⟨e, he, hequiv⟩ := hP.exists_trivialization (projection p)
  have hp : p ∈ e.source := e.mem_source.mpr he
  have hq : q ∈ e.source := e.mem_source.mpr (hpq ▸ he)
  -- In the same original chart, right translation must multiply a by a⁻¹b.
  let g : G := (e p).2⁻¹ * (e q).2
  have hgbase : projection (MulOpposite.op g • p) ∈ e.baseSet := by
    rw [hP.projection_smul]
    exact he
  have hg : MulOpposite.op g • p = q := by
    apply e.toOpenPartialHomeomorph.injOn (e.mem_source.mpr hgbase) hq
    change e (MulOpposite.op g • p) = e q
    apply Prod.ext
    · rw [e.coe_fst (e.mem_source.mpr hgbase), e.coe_fst hq,
        hP.projection_smul, hpq]
    · rw [hequiv g p he]
      simp [g]
  -- Any other translating element satisfies the same cancellable group equation.
  refine ⟨g, hg, ?_⟩
  intro k hk
  have hkcoord : (e p).2 * k = (e q).2 := by
    rw [← hequiv k p he, hk]
  calc
    k = (e p).2⁻¹ * ((e p).2 * k) := by simp
    _ = g := by rw [hkcoord]

end AtiyahSinger
