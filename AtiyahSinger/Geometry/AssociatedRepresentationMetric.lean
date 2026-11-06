/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedOrthogonalRepresentation
public import AtiyahSinger.Geometry.AtlasHermitianMetric

/-!
# A prescribed invariant metric on the original coefficient bundle

Public module ID: M1065.

A continuous invariant Hermitian form on the given representation descends to
its actual associated vector fibers. Every original principal representative
has precisely the given pairing. In the prescribed smooth associated atlas,
the Gram matrix is constant, so this same metric is smooth. The construction
applies in particular to the full sphere-kernel representation with its
original integral Gram form.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] associatedVectorFiberAddCommGroup associatedVectorFiberModule
  associatedVectorTotalTopology sumTopology

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (ρ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "V" => Fin ρ.dimension → ℂ
local notation "K" => AssociatedVectorFiber S.toIsPrincipalBundle ρ.representation

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1200000 in
-- One original principal chart supplies coordinates; invariance removes that choice everywhere.
/-- The given invariant form defines a smooth metric on the same associated coefficient fibers. -/
theorem exists_associatedRepresentationMetric (c : InnerProductSpace.Core ℂ V)
    (hc : Continuous (fun z : V × V ↦ c.inner z.1 z.2))
    (hinv : ∀ (g : G) (u v : V),
      c.inner (ρ.representation g u) (ρ.representation g v) = c.inner u v) :
    ∃ h : ContinuousHermitianMetric K,
      (associatedOrthogonalRepresentationAtlas S ρ).IsSmoothHermitianMetric h ∧
      ∀ (p : P) (b : B) (hp : projection p = b) (u v : V),
        (h.toCore b).inner
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp u)
          (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp v) =
            c.inner u v := by
  classical
  let A := associatedOrthogonalRepresentationAtlas S ρ
  let : IsFiniteRank K := A.isFiniteRank
  have hb (i : B) : (A.chart i).baseSet = (S.trivialization i).baseSet :=
    (associatedOrthogonalRepresentationChart_properties S ρ i).1
  let e (b : B) := A.frameLinearEquiv b b ((hb b).symm ▸ S.mem_baseSet b)
  let core (b : B) : InnerProductSpace.Core ℂ (K b) := {
    inner u v := c.inner (e b u) (e b v)
    conj_inner_symm u v := c.conj_inner_symm _ _
    re_inner_nonneg u := c.re_inner_nonneg _
    add_left u v w := by rw [(e b).map_add]; exact c.add_left _ _ _
    smul_left u v a := by rw [(e b).map_smul]; exact c.smul_left _ _ _
    definite u hu := (e b).injective ((c.definite _ hu).trans (e b).map_zero.symm) }
  have hrep (i : B) (p : P) (b : B) (hp : projection p = b) (u : V)
      (hi : b ∈ (S.trivialization i).baseSet) :
      (A.chart i ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle
        ρ.representation p hp u⟩).2 = ρ.representation (S.trivialization i p).2 u :=
    (associatedOrthogonalRepresentationChart_properties S ρ i).2 p b hp u hi
  have hpair (p : P) (b : B) (hp : projection p = b) (u v : V) :
      (core b).inner
        (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp u)
        (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp v) =
          c.inner u v := by
    change c.inner
      (A.chart b ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp u⟩).2
      (A.chart b ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp v⟩).2 = _
    rw [hrep b p b hp u (S.mem_baseSet b), hrep b p b hp v (S.mem_baseSet b)]
    exact hinv _ _ _
  -- In any original chart the metric is exactly the fixed representation form.
  have hlocal (i b : B) (hi : b ∈ (A.chart i).baseSet) (u v : K b) :
      (core b).inner u v = c.inner (A.chart i ⟨b, u⟩).2 (A.chart i ⟨b, v⟩).2 := by
    let p := (S.trivialization b).toPartialEquiv.symm (b, 1)
    have hp : projection p = b := (S.trivialization b).proj_symm_apply' (S.mem_baseSet b)
    let q := associatedVectorFiberMkLinearEquiv S.toIsPrincipalBundle ρ.representation p hp
    obtain ⟨u, rfl⟩ := q.surjective u
    obtain ⟨v, rfl⟩ := q.surjective v
    change (core b).inner
      (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp u)
      (associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp v) = _
    rw [hpair]
    change c.inner u v = c.inner
      (A.chart i ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp u⟩).2
      (A.chart i ⟨b, associatedVectorFiberMk S.toIsPrincipalBundle ρ.representation p hp v⟩).2
    rw [hrep i p b hp u (hb i ▸ hi), hrep i p b hp v (hb i ▸ hi)]
    exact (hinv _ _ _).symm
  have hfst : Continuous (fun z : TotalSpace Unit (K ×ᵇ K) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace Unit K)) := continuous_sum_fst
  have hsnd : Continuous (fun z : TotalSpace Unit (K ×ᵇ K) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace Unit K)) := continuous_sum_snd
  have hbase : Continuous (π Unit (K ×ᵇ K)) := (continuous_proj (E := K)).comp hfst
  have hcontinuous : Continuous (fun z : TotalSpace Unit (K ×ᵇ K) ↦
      (core z.proj).inner z.snd.1 z.snd.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    let i := z.proj
    let U := π Unit (K ×ᵇ K) ⁻¹' (A.chart i).baseSet
    have hU : IsOpen U := (A.chart i).open_baseSet.preimage hbase
    have hz : z ∈ U := by
      change z.proj ∈ (A.chart i).baseSet
      exact (hb i).symm ▸ S.mem_baseSet i
    have hu : ContinuousOn (fun w : TotalSpace Unit (K ×ᵇ K) ↦
        (A.chart i ⟨w.proj, w.snd.1⟩).2) U :=
      continuous_snd.comp_continuousOn
        ((A.chart i).toOpenPartialHomeomorph.continuousOn.comp hfst.continuousOn
          (fun w hw ↦ (A.chart i).mem_source.mpr hw))
    have hv : ContinuousOn (fun w : TotalSpace Unit (K ×ᵇ K) ↦
        (A.chart i ⟨w.proj, w.snd.2⟩).2) U :=
      continuous_snd.comp_continuousOn
        ((A.chart i).toOpenPartialHomeomorph.continuousOn.comp hsnd.continuousOn
          (fun w hw ↦ (A.chart i).mem_source.mpr hw))
    have h := (hc.comp_continuousOn (hu.prodMk hv)).congr
      (fun w hw ↦ hlocal i w.proj hw w.snd.1 w.snd.2)
    exact h.continuousAt (hU.mem_nhds hz)
  refine ⟨⟨core, hcontinuous, A.isFiniteRank⟩, ?_, hpair⟩
  -- The Gram entries in the prescribed associated atlas are constant, including rank zero.
  intro i a b
  change Fin ρ.dimension at a b
  have hconstant : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℂ) ∞
      (fun _ : B ↦ c.inner (Pi.single a 1) (Pi.single b 1)) (A.chart i).baseSet :=
    contMDiffOn_const
  apply hconstant.congr
  intro x hx
  refine (dite_eq_left hx).trans ?_
  let f := A.frameLinearEquiv i x hx
  change (core x).inner (f.symm (Pi.single a 1)) (f.symm (Pi.single b 1)) = _
  exact (hlocal i x hx _ _).trans
    (congrArg₂ c.inner (f.apply_symm_apply _) (f.apply_symm_apply _))

end AtiyahSinger
