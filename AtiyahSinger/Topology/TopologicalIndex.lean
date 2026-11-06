/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EuclideanEmbedding
public import AtiyahSinger.Topology.EuclideanTangentKTheory
public import AtiyahSinger.Topology.ExteriorBottComparison
public import AtiyahSinger.Topology.LinearEmbeddingPushforward
public import AtiyahSinger.Topology.TangentEmbeddingComposition

/-!
# The topological index associated with a specified Euclidean embedding

Public module ID: M2256.

The index is the actual tangent embedding pushforward followed by the specified
positive integer Bott coordinate on the native Euclidean tangent bundle.
Appending zero coordinates preserves that coordinate. The composite embedding
formula then gives ambient stabilization for this same specified index.

Source: SG III.13, Definition 13.1 and the adjacent stabilization argument,
printed pp.243--244. The construction is defined whenever a proper smooth
Euclidean embedding is supplied, including for a noncompact source and a
compactly supported input class.
For compact sources, `TopologicalIndexIndependence` compares arbitrary
choices of embedding, and `CompactTopologicalIndex` defines the resulting
embedding-independent homomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

set_option maxHeartbeats 800000 in
-- Normalize the tangent product coordinates and the same positive appended Bott coordinate.
/-- Appending real zero coordinates preserves the pushforward's integer Bott coordinate. -/
theorem euclideanTangentKZeroEquivInt_pushforward_zeroAppend (n k : ℕ) :
    (euclideanTangentKZeroEquivInt (n + k)).toAddMonoidHom.comp
        (tangentEmbeddingPushforward (euclideanZeroAppend n k)
          (euclideanZeroAppend_properties n k).1 (euclideanZeroAppend_properties n k).2) =
      (euclideanTangentKZeroEquivInt n).toAddMonoidHom := by
  /- First identify the tangent product homeomorphism in complex coordinates.
  The real finAddEquivProd decomposition and x + I*v identify it with the
  original Fin.appendHomeomorph, with the source block first.
  Next apply tangentEmbeddingPushforward_linear. That theorem computes the
  geometric pushforward using the product normal bundle and normalized tube;
  here it gives external product with exteriorBottClass. The exterior/Bott
  comparison identifies the added factor with the positive bottEuclideanClass.
  Finally every source class is an integer multiple of its positive Bott
  generator. Bott multiplicativity and the integer normalization show that
  appending the second factor preserves that integer, including n=0 and k=0. -/
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin (n + k))
  let W := EuclideanSpace ℂ (Fin k)
  let TM := TangentBundle 𝓘(ℝ, E) E
  let TN := TangentBundle 𝓘(ℝ, F) F
  let : T2Space TM := (tangentBundle_topology E E).1
  let : T2Space TN := (tangentBundle_topology F F).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)
  let H := linearEmbeddingTangentProductHomeomorph k c
  let eN := euclideanTangentComplexHomeomorph n
  let eNK := euclideanTangentComplexHomeomorph (n + k)
  let eW := PiLp.homeomorph 2 (fun _ : Fin k ↦ ℂ)
  let A := Fin.appendHomeomorph (X := ℂ) n k
  -- The whole tangent map appends complex coordinates in precisely the original Fin order.
  have hsquare : H.trans eNK = (eN.prodCongr eW).trans A := by
    apply Homeomorph.ext
    intro z
    funext i
    change Complex.equivRealProdCLM.symm
      ((c.symm (z.1.proj, (EuclideanSpace.equiv (Fin k) ℝ).symm
        (fun j ↦ (z.2 j).re))) i,
        (c.symm (z.1.snd, (EuclideanSpace.equiv (Fin k) ℝ).symm
          (fun j ↦ (z.2 j).im))) i) =
      Fin.append (fun j ↦ Complex.equivRealProdCLM.symm
        (z.1.proj j, (show EuclideanSpace ℝ (Fin n) from z.1.snd) j))
        (fun j ↦ z.2 j) i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [c, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
    · simpa [c, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd] using
        Complex.equivRealProdCLM.symm_apply_apply (z.2 j)
  have htransport (b : CompactSupportKZero (TM × W)) :
      compactSupportKZeroHomeomorph eNK (compactSupportKZeroHomeomorph H b) =
        compactSupportKZeroHomeomorph A
          (compactSupportKZeroHomeomorph (eN.prodCongr eW) b) := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph eNK,
      ← compactSupportKZeroOpenPushforward_homeomorph H,
      ← compactSupportKZeroOpenPushforward_homeomorph A,
      ← compactSupportKZeroOpenPushforward_homeomorph (eN.prodCongr eW)]
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp]
    have hfun := congrArg (fun e : TM × W ≃ₜ (Fin (n + k) → ℂ) ↦ (e : _ → _)) hsquare
    congr 2
  have hproduct (a : CompactSupportKZero TM) :
      compactSupportKZeroHomeomorph eNK
          (tangentEmbeddingPushforward (euclideanZeroAppend n k)
            (euclideanZeroAppend_properties n k).1 (euclideanZeroAppend_properties n k).2 a) =
        compactSupportKZeroHomeomorph A (compactSupportKZeroExternalProduct
          (compactSupportKZeroHomeomorph eN a) (bottEuclideanClass k)) := by
    have h := DFunLike.congr_fun (tangentEmbeddingPushforward_linear k
      (euclideanZeroAppend n k) (euclideanZeroAppend_properties n k).1
        (euclideanZeroAppend_properties n k).2 c (fun _ ↦ rfl)) a
    change tangentEmbeddingPushforward (euclideanZeroAppend n k)
      (euclideanZeroAppend_properties n k).1 (euclideanZeroAppend_properties n k).2 a =
        compactSupportKZeroHomeomorph H
          (compactSupportKZeroExternalProduct a (exteriorBottClass W)) at h
    rw [h, htransport, compactSupportKZeroExternalProduct_homeomorph]
    change compactSupportKZeroHomeomorph A (compactSupportKZeroExternalProduct
      (compactSupportKZeroHomeomorph eN a) (exteriorBottEuclideanClass k)) = _
    rw [exteriorBottEuclideanClass_eq_bottEuclideanClass]
  -- The original positive Bott class generates the entire source group, including rank zero.
  apply AddMonoidHom.ext
  intro a
  let j := bottEuclideanClassEquivInt n (compactSupportKZeroHomeomorph eN a)
  have ha : compactSupportKZeroHomeomorph eN a = j • bottEuclideanClass n := by
    apply (bottEuclideanClassEquivInt n).injective
    simp only [map_zsmul, bottEuclideanClassEquivInt_bottEuclideanClass, zsmul_eq_mul, mul_one]
    rfl
  change bottEuclideanClassEquivInt (n + k)
      (compactSupportKZeroHomeomorph eNK
        (tangentEmbeddingPushforward (euclideanZeroAppend n k)
          (euclideanZeroAppend_properties n k).1 (euclideanZeroAppend_properties n k).2 a)) = j
  rw [hproduct, ha]
  simp only [map_zsmul, AddMonoidHom.smul_apply]
  rw [bottEuclideanClass_add, bottEuclideanClassEquivInt_bottEuclideanClass]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- SG's topological-index formula with the actual proper Euclidean embedding kept explicit. -/
def topologicalIndexOfEmbedding {n : ℕ}
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hp : IsProperMap f) :
    letI : T2Space (TangentBundle 𝓘(ℝ, E) M) := (tangentBundle_topology E M).1
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, E) M) :=
      ChartedSpace.locallyCompactSpace (E × E) (TangentBundle 𝓘(ℝ, E) M)
    CompactSupportKZero (TangentBundle 𝓘(ℝ, E) M) →+ ℤ :=
  (euclideanTangentKZeroEquivInt n).toAddMonoidHom.comp
    (tangentEmbeddingPushforward f hf hp)

end AtiyahSinger
