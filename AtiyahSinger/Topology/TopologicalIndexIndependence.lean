/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CompactEuclideanEmbedding
public import AtiyahSinger.Geometry.EuclideanComplementaryEmbedding
public import AtiyahSinger.Topology.LinearEmbeddingPushforward
public import AtiyahSinger.Topology.TangentEmbeddingIsotopy
public import AtiyahSinger.Topology.TopologicalIndex

/-!
# Independence of the Euclidean embedding in the topological index

Public module ID: M2257.

SG III.13, printed p.244 / PDF p.256, compares two embeddings by placing them
in complementary Euclidean coordinate blocks. Their weighted sum is an actual
smooth isotopy of embeddings. First check that the second block inclusion has
the same positive Bott normalization as the first block inclusion. Then use
the moving-embedding pushforward theorem and actual composition to compare
the two supplied-embedding index homomorphisms.

Compactness of the source supplies parameter control in the isotopy step.
No claim of independence for arbitrary noncompact proper embeddings is made.
The endpoint groups and maps are exactly those already used by
`topologicalIndexOfEmbedding`; no abstract integer isomorphism is substituted.
The complementary-block isotopy compares the actual embedding pushforwards.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

set_option maxHeartbeats 600000 in
-- Normalize the normal-first complex coordinates and the same positive Bott coordinate.
/-- The complementary coordinate inclusion preserves the same positive integer Bott coordinate. -/
theorem euclideanTangentKZeroEquivInt_pushforward_zeroPrepend (n k : ℕ) :
    (euclideanTangentKZeroEquivInt (n + k)).toAddMonoidHom.comp
        (tangentEmbeddingPushforward (euclideanZeroPrepend n k)
          (euclideanZeroPrepend_properties n k).1 (euclideanZeroPrepend_properties n k).2) =
      (euclideanTangentKZeroEquivInt k).toAddMonoidHom := by
  classical
  let E := EuclideanSpace ℝ (Fin k)
  let F := EuclideanSpace ℝ (Fin (n + k))
  let W := EuclideanSpace ℂ (Fin n)
  let TM := TangentBundle 𝓘(ℝ, E) E
  let TN := TangentBundle 𝓘(ℝ, F) F
  let : T2Space TM := (tangentBundle_topology E E).1
  let : T2Space TN := (tangentBundle_topology F F).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let c : F ≃L[ℝ] E × EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).toContinuousLinearEquiv.trans
      (ContinuousLinearEquiv.prodComm ℝ (EuclideanSpace ℝ (Fin n)) E)
  let H := linearEmbeddingTangentProductHomeomorph n c
  let eK := euclideanTangentComplexHomeomorph k
  let eNK := euclideanTangentComplexHomeomorph (n + k)
  let eW := PiLp.homeomorph 2 (fun _ : Fin n ↦ ℂ)
  let J := Homeomorph.prodComm (Fin k → ℂ) (Fin n → ℂ)
  let A₀ := Fin.appendHomeomorph (X := ℂ) n k
  let A := J.trans A₀
  -- The original normal block precedes the base block in the target complex coordinates.
  have hsquare : H.trans eNK = (eK.prodCongr eW).trans A := by
    apply Homeomorph.ext
    intro z
    funext i
    change Complex.equivRealProdCLM.symm
        (((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm
            ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun j ↦ (z.2 j).re), z.1.proj) i),
          ((EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).symm
            ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun j ↦ (z.2 j).im),
              (show E from z.1.snd)) i)) =
      Fin.append (fun j ↦ z.2 j)
        (fun j ↦ Complex.equivRealProdCLM.symm (z.1.proj j, (show E from z.1.snd) j)) i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
        Complex.equivRealProdCLM_symm_apply, Complex.re_add_im]
    · simp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
  have htransport (b : CompactSupportKZero (TM × W)) :
      compactSupportKZeroHomeomorph eNK (compactSupportKZeroHomeomorph H b) =
        compactSupportKZeroHomeomorph A
          (compactSupportKZeroHomeomorph (eK.prodCongr eW) b) := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph eNK,
      ← compactSupportKZeroOpenPushforward_homeomorph H,
      ← compactSupportKZeroOpenPushforward_homeomorph A,
      ← compactSupportKZeroOpenPushforward_homeomorph (eK.prodCongr eW)]
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp]
    have hfun := congrArg (fun e : TM × W ≃ₜ (Fin (n + k) → ℂ) ↦ (e : _ → _)) hsquare
    congr 2
  have hproduct (a : CompactSupportKZero TM) :
      compactSupportKZeroHomeomorph eNK
          (tangentEmbeddingPushforward (euclideanZeroPrepend n k)
            (euclideanZeroPrepend_properties n k).1 (euclideanZeroPrepend_properties n k).2 a) =
        compactSupportKZeroHomeomorph A (compactSupportKZeroExternalProduct
          (compactSupportKZeroHomeomorph eK a) (bottEuclideanClass n)) := by
    have h := DFunLike.congr_fun (tangentEmbeddingPushforward_linear n
      (euclideanZeroPrepend n k) (euclideanZeroPrepend_properties n k).1
        (euclideanZeroPrepend_properties n k).2 c (fun _ ↦ rfl)) a
    change tangentEmbeddingPushforward (euclideanZeroPrepend n k)
      (euclideanZeroPrepend_properties n k).1 (euclideanZeroPrepend_properties n k).2 a =
        compactSupportKZeroHomeomorph H
          (compactSupportKZeroExternalProduct a (exteriorBottClass W)) at h
    rw [h, htransport, compactSupportKZeroExternalProduct_homeomorph]
    change compactSupportKZeroHomeomorph A (compactSupportKZeroExternalProduct
      (compactSupportKZeroHomeomorph eK a) (exteriorBottEuclideanClass n)) = _
    rw [exteriorBottEuclideanClass_eq_bottEuclideanClass]
  -- The already proved K₀ product symmetry exchanges whole complex blocks with positive sign.
  have hA (b : CompactSupportKZero ((Fin k → ℂ) × (Fin n → ℂ))) :
      compactSupportKZeroHomeomorph A b =
        compactSupportKZeroHomeomorph A₀ (compactSupportKZeroHomeomorph J b) := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph A,
      ← compactSupportKZeroOpenPushforward_homeomorph A₀,
      ← compactSupportKZeroOpenPushforward_homeomorph J,
      ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp]
    rfl
  have hBott : compactSupportKZeroHomeomorph A
      (compactSupportKZeroExternalProduct (bottEuclideanClass k) (bottEuclideanClass n)) =
        bottEuclideanClass (n + k) := by
    rw [hA, compactSupportKZeroExternalProduct_swap, bottEuclideanClass_add]
  apply AddMonoidHom.ext
  intro a
  let j := bottEuclideanClassEquivInt k (compactSupportKZeroHomeomorph eK a)
  have ha : compactSupportKZeroHomeomorph eK a = j • bottEuclideanClass k := by
    apply (bottEuclideanClassEquivInt k).injective
    simp only [map_zsmul, bottEuclideanClassEquivInt_bottEuclideanClass, zsmul_eq_mul, mul_one]
    rfl
  change bottEuclideanClassEquivInt (n + k)
      (compactSupportKZeroHomeomorph eNK
        (tangentEmbeddingPushforward (euclideanZeroPrepend n k)
          (euclideanZeroPrepend_properties n k).1 (euclideanZeroPrepend_properties n k).2 a)) = j
  rw [hproduct, ha, map_zsmul, AddMonoidHom.zsmul_apply, map_zsmul, hBott,
    map_zsmul, bottEuclideanClassEquivInt_bottEuclideanClass]
  simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]

/-- For a compact source, any two supplied Euclidean embeddings give the same actual index. -/
theorem topologicalIndexOfEmbedding_eq {n k : ℕ}
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞)
    (g : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      M (EuclideanSpace ℝ (Fin k)) ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f)
    (hg : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ g)
    (hpf : IsProperMap f) (hpg : IsProperMap g) :
    topologicalIndexOfEmbedding f hf hpf = topologicalIndexOfEmbedding g hg hpg := by
  classical
  let W := EuclideanSpace ℝ (Fin (n + k))
  let c := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := k)).toContinuousLinearEquiv
  let H (t : ℝ) : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, W) M W ∞ :=
    ⟨fun x ↦ c.symm ((1 - t) • f x, t • g x),
      c.symm.contDiff.contMDiff.comp
        (((show ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun _ : M ↦ 1 - t)
          from contMDiff_const).smul f.contMDiff).prodMk_space
          ((show ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun _ : M ↦ t)
            from contMDiff_const).smul g.contMDiff))⟩
  have hH : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, W) ∞
      (fun p : ℝ × M ↦ H p.1 p.2) :=
    c.symm.contDiff.contMDiff.comp
      (((contMDiff_const.sub contMDiff_fst).smul
        (f.contMDiff.comp contMDiff_snd)).prodMk_space
        (contMDiff_fst.smul (g.contMDiff.comp contMDiff_snd)))
  -- A nonzero coordinate block recovers an original embedding, including its differential.
  have embedding_of_recovery {l : ℕ}
      (j : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin l))
        M (EuclideanSpace ℝ (Fin l)) ∞)
      (hj : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin l)) ∞ j)
      (t : ℝ) (r : W →L[ℝ] EuclideanSpace ℝ (Fin l))
      (hr : (r : W → EuclideanSpace ℝ (Fin l)) ∘ H t = j) :
      IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, W) ∞ (H t) := by
    have hinj : Function.Injective (H t) := by
      intro x y hxy
      apply hj.isEmbedding.injective
      exact (congrFun hr x).symm.trans ((congrArg r hxy).trans (congrFun hr y))
    have hd (x : M) : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, W) (H t) x) := by
      have hchain := mfderiv_comp x
        ((r.contDiff : ContDiff ℝ ∞ r).contMDiff.mdifferentiable (by simp) (H t x))
        ((H t).contMDiff.mdifferentiable (by simp) x)
      rw [hr, r.hasFDerivAt.hasMFDerivAt.mfderiv] at hchain
      intro u v huv
      apply hj.isImmersion.mfderiv_injective (by simp) x
      rw [hchain]
      exact congrArg r huv
    exact ⟨isImmersion_of_injective_mfderiv (H t) hd,
      ((H t).contMDiff.continuous.isClosedEmbedding hinj).isEmbedding⟩
  have hemb (t : unitInterval) : IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, W) ∞ (H t) := by
    by_cases ht : (t : ℝ) = 1
    · let r : W →L[ℝ] EuclideanSpace ℝ (Fin k) :=
        (ContinuousLinearMap.snd ℝ _ _).comp c.toContinuousLinearMap
      apply embedding_of_recovery g hg t r
      funext x
      change (c (c.symm ((1 - (t : ℝ)) • f x, (t : ℝ) • g x))).2 = g x
      simp [ht]
    · let r : W →L[ℝ] EuclideanSpace ℝ (Fin n) :=
        (1 - (t : ℝ))⁻¹ • (ContinuousLinearMap.fst ℝ _ _).comp c.toContinuousLinearMap
      apply embedding_of_recovery f hf t r
      funext x
      change (1 - (t : ℝ))⁻¹ •
        (c (c.symm ((1 - (t : ℝ)) • f x, (t : ℝ) • g x))).1 = f x
      rw [c.apply_symm_apply, smul_smul,
        inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm ht)), one_smul]
  -- The family endpoints are the two literal complementary-block composites.
  have hzero : H 0 = (euclideanZeroAppend n k).comp f := by
    apply ContMDiffMap.ext
    intro x
    change c.symm ((1 - 0) • f x, (0 : ℝ) • g x) = c.symm (f x, 0)
    simp only [sub_zero, one_smul, zero_smul]
  have hone : H 1 = (euclideanZeroPrepend n k).comp g := by
    apply ContMDiffMap.ext
    intro x
    change c.symm ((1 - 1) • f x, (1 : ℝ) • g x) = c.symm (0, g x)
    simp only [sub_self, one_smul, zero_smul]
  have hiso := tangentEmbeddingPushforward_eq_of_isotopy H hH hemb
  simp only [hzero, hone] at hiso
  have hcomp₀ := tangentEmbeddingPushforward_comp f (euclideanZeroAppend n k)
    hf (euclideanZeroAppend_properties n k).1 hpf (euclideanZeroAppend_properties n k).2
  have hcomp₁ := tangentEmbeddingPushforward_comp g (euclideanZeroPrepend n k)
    hg (euclideanZeroPrepend_properties n k).1 hpg (euclideanZeroPrepend_properties n k).2
  -- Compose that equality with the same positive target Bott coordinate.
  have happ := congrArg (fun p ↦ (euclideanTangentKZeroEquivInt (n + k)).toAddMonoidHom.comp p)
    (hcomp₀.symm.trans (hiso.trans hcomp₁))
  rw [← AddMonoidHom.comp_assoc, ← AddMonoidHom.comp_assoc,
    euclideanTangentKZeroEquivInt_pushforward_zeroAppend,
    euclideanTangentKZeroEquivInt_pushforward_zeroPrepend] at happ
  exact happ

end AtiyahSinger
