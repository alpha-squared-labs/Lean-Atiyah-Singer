/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport
public import AtiyahSinger.Geometry.TangentMusical
public import AtiyahSinger.Geometry.TangentNormalBundle
public import AtiyahSinger.Topology.ComplexificationPullbackTopology
public import AtiyahSinger.Topology.ThomNaturality
public import AtiyahSinger.Topology.ThomOpenExtension

/-!
# Musical base change of the original complexified Thom map

Public module ID: M2226.

The metric flat homeomorphism changes only the tangent base point into its
actual covector. The pulled complexified real vector is retained exactly.
The two existing total topologies are compared before applying Thom
naturality to this specified map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Topology
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ B]
  [T2Space B] [SecondCountableTopology B]
  (R : Type*) [NormedAddCommGroup R] [NormedSpace ℝ R] [FiniteDimensional ℝ R]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace R V)] [FiberBundle R V] [VectorBundle ℝ R V]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
  tangentBundleFullChartedSpace tangentBundle_full_isManifold
  ComplexBundle.t2Space_totalSpace ComplexBundle.locallyCompactSpace_totalSpace

set_option maxSynthPendingDepth 45 in
set_option maxHeartbeats 1500000 in
-- Normalize the original pullback topologies and musical total-space Thom square.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Musical transport of the original base commutes with the specified supported Thom map. -/
theorem exists_tangentComplexification_musical_thomMap (g : SmoothTangentMetric (n := n) (M := B)) :
    let TM := TangentBundle (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) B
    let X := CotangentTotalSpace (n := n) (M := B)
    letI : T2Space TM := (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) B).1
    letI : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) TM
    let p : C(TM, B) := ⟨TotalSpace.proj,
      FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin n))))⟩
    let f := cotangentProjection (n := n) (M := B)
    let CB := fun b : B ↦ ℂ ⊗[ℝ] V b
    let WT := (p : TM → B) *ᵖ V
    let CT := fun z : TM ↦ ℂ ⊗[ℝ] WT z
    let CX := (f : X → B) *ᵖ CB
    letI := complexificationTopology R V
    letI := isFiniteRank_complexification R V
    letI := isFiniteRank_pullback (E := CB) f
    letI := complexificationTopology R WT
    letI := isFiniteRank_complexification R WT
    ∃ (q : C(TotalSpace Unit CT, TotalSpace Unit CX)) (hq : IsOpenEmbedding q),
      (∀ z, q z = ⟨g.flatHomeomorph z.proj, z.snd⟩) ∧
      ∀ (hB : ContinuousHermitianMetric CB) (hT : ContinuousHermitianMetric CT),
        (compactSupportKZeroOpenPushforward q hq).comp hT.supportedThomHom =
          (hB.pullback f).supportedThomHom.comp
            (compactSupportKZeroHomeomorph g.flatHomeomorph) := by
  classical
  let TM := TangentBundle (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) B
  let X := CotangentTotalSpace (n := n) (M := B)
  let : T2Space TM := (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) B).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) TM
  let p : C(TM, B) := ⟨TotalSpace.proj,
    FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓘(ℝ, EuclideanSpace ℝ (Fin n))))⟩
  let f := cotangentProjection (n := n) (M := B)
  let CB := fun b : B ↦ ℂ ⊗[ℝ] V b
  let WT := (p : TM → B) *ᵖ V
  let CT := fun z : TM ↦ ℂ ⊗[ℝ] WT z
  let CX := (f : X → B) *ᵖ CB
  let := complexificationTopology R V
  let := isFiniteRank_complexification R V
  let := isFiniteRank_pullback (E := CB) f
  let := complexificationTopology R WT
  let := isFiniteRank_complexification R WT
  let d : C(TM, X) := ⟨g.flatHomeomorph, g.flatHomeomorph.continuous⟩
  let CP := (p : TM → B) *ᵖ CB
  let CD := (d : TM → X) *ᵖ CX
  let := isFiniteRank_pullback (E := CX) d
  let tT := complexificationTopology R WT
  let tP := Pullback.TotalSpace.topologicalSpace Unit CB (p : TM → B)
  have htop : tT = tP := complexificationTopology_pullback R V p
  -- Compare the existing topologies by equality, keeping the same scalar-extension vector.
  let i : @Iso TM CT CP inferInstance inferInstance inferInstance inferInstance tT tP :=
    { linearEquiv := fun _ ↦ LinearEquiv.refl ℂ _
      continuous_total := by
        change @Continuous _ _ tT tP id
        rw [htop]
        exact @continuous_id _ tP
      continuous_symm := by
        change @Continuous _ _ tP tT id
        rw [htop]
        exact @continuous_id _ tP }
  let c : Iso CD CP := pullbackCompIso (E := CB) f d
  let e : Iso CT CD := i.trans c.symm
  have he (z : TM) (v : CT z) : e.linearEquiv z v = v := by
    have hi : (c.linearEquiv z).symm v = v := by
      apply (c.linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (pullbackCompIso_apply (E := CB) f d z v).symm
    exact hi
  let Q := pullbackTotalMap CX d
  have hQ : IsOpenEmbedding Q :=
    (pullbackTotalMap_properties CX d).2 g.flatHomeomorph.isOpenEmbedding
  let q : C(TotalSpace Unit CT, TotalSpace Unit CX) :=
    Q.comp ⟨e.totalHomeomorph, e.totalHomeomorph.continuous⟩
  have hq : IsOpenEmbedding q := hQ.comp e.totalHomeomorph.isOpenEmbedding
  dsimp only
  refine ⟨q, hq, ?_, ?_⟩
  · intro z
    change (⟨g.flatHomeomorph z.proj, e.linearEquiv z.proj z.snd⟩ : TotalSpace Unit CX) = _
    rw [he]
  · intro hB hT
    -- Bundle-isomorphism naturality followed by actual open base change gives the same Thom map.
    have heThom := hT.supportedThomHom_iso ((hB.pullback f).pullback d) e
    have hnatural := (hB.pullback f).supportedThomHom_openPushforward d
      g.flatHomeomorph.isOpenEmbedding
    have hcomp := compactSupportKZeroOpenPushforward_comp e.totalHomeomorph
      e.totalHomeomorph.isOpenEmbedding Q hQ
    rw [compactSupportKZeroOpenPushforward_homeomorph] at hcomp
    change (compactSupportKZeroOpenPushforward (Q ∘ e.totalHomeomorph) _).comp
      hT.supportedThomHom = _
    rw [hcomp, AddMonoidHom.comp_assoc, heThom]
    change (compactSupportKZeroOpenPushforward Q hQ).comp
      ((hB.pullback f).pullback d).supportedThomHom =
        (hB.pullback f).supportedThomHom.comp
          (compactSupportKZeroOpenPushforward g.flatHomeomorph
            g.flatHomeomorph.isOpenEmbedding) at hnatural
    rw [compactSupportKZeroOpenPushforward_homeomorph] at hnatural
    exact hnatural

end AtiyahSinger
