/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SmoothFiniteRepresentation
public import AtiyahSinger.Geometry.AtlasBundleMapComposition
public import AtiyahSinger.Geometry.EquivariantAtlasSmoothing
public import AtiyahSinger.Geometry.EquivariantFixedRankModel
public import AtiyahSinger.Geometry.NativeAtlasBundleMap
public import AtiyahSinger.Geometry.SmoothTensorAtlas
public import AtiyahSinger.Topology.EquivariantBundleTensor
public import AtiyahSinger.Topology.EquivariantTrivialBundle
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Native smooth models of representation tensors

Public module ID: M1197.

Tensor the actual original bundle with the trivial bundle carrying a given
finite representation. One native model retains this continuous tensor
bundle and its action, together with smooth standard-basis insertions and
coordinate projections. Its finite coordinates carry the original matrix
mixing action, including at representation dimension zero.
This is the geometric model comparison needed for the representation-ring
module property of the analytic index, using SG III.9 and III.13.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct BigOperators

variable {VG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [FiniteDimensional ℝ VG]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G]
  {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [CompactSpace M] [T2Space M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

attribute [local instance] trivialTopology isFiniteRank_trivial tensorTopology isFiniteRank_tensor

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- One local construction retains both tensor frames and both compatible coordinate maps.
/-- A representation tensor has a compatible native model and smooth original coordinate maps. -/
theorem exists_equivariant_native_smooth_tensor (ρ : FiniteContinuousRepresentation G)
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (hσ : σ.IsSmooth (n := n) (r := r) 𝓘(ℝ, VG)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
    ∃ T : SmoothFiniteComplexBundle (n := n) M, T.rank = ρ.dimension * r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
      ∃ τ : EquivariantStructure G T.Fiber,
        τ.IsSmooth (n := n) (r := T.rank) 𝓘(ℝ, VG) ∧
          ∃ e : Iso (fun x ↦ (Fin ρ.dimension → ℂ) ⊗[ℂ] E x) T.Fiber,
            e.IsEquivariant ((EquivariantStructure.ofFiniteRepresentation ρ).tensor σ) τ ∧
              (∀ i : Fin ρ.dimension, IsSmoothBundleMap (n := n) (r := r) (q := T.rank)
                (fun x ↦ (e.linearEquiv x).toLinearMap.comp
                  (TensorProduct.mk ℂ (Fin ρ.dimension → ℂ) (E x) (Pi.single i 1)))) ∧
              (let c (x : M) := (e.linearEquiv x).symm.trans
                ((TensorProduct.comm ℂ (Fin ρ.dimension → ℂ) (E x)).trans
                  (TensorProduct.piScalarRight ℂ ℂ (E x) (Fin ρ.dimension)))
               (∀ i : Fin ρ.dimension, IsSmoothBundleMap (n := n) (r := T.rank) (q := r)
                 (fun x ↦ (LinearMap.proj i).comp (c x).toLinearMap)) ∧
               ∀ (g : G) (x : M) (v : T.Fiber x) (i : Fin ρ.dimension),
                 c (g • x) (τ.linearMap g x v) i =
                   ∑ j : Fin ρ.dimension,
                     (ρ.representation g (Pi.single j 1)) i • σ.linearMap g x (c x v j)) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let d := ρ.dimension
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  -- Use the global product chart on the same finite trivial bundle.
  let t : Trivialization (Fin d → ℂ) (π Unit (Bundle.Trivial M (Fin d → ℂ))) := {
    toFun z := (z.proj, z.snd)
    invFun p := ⟨p.1, p.2⟩
    source := Set.univ
    target := Set.univ
    baseSet := Set.univ
    map_source' _ _ := Set.mem_univ _
    map_target' _ _ := Set.mem_univ _
    left_inv' _ _ := rfl
    right_inv' _ _ := rfl
    open_source := isOpen_univ
    open_target := isOpen_univ
    open_baseSet := isOpen_univ
    continuousOn_toFun := continuous_induced_dom.continuousOn
    continuousOn_invFun := by
      apply Continuous.continuousOn
      apply continuous_induced_rng.mpr
      exact continuous_id
    source_eq := by simp
    target_eq := by simp
    proj_toFun _ _ := rfl }
  let A : SmoothComplexBundleAtlas.{0} (n := n) (Bundle.Trivial M (Fin d → ℂ)) := {
    Index := Unit
    rank _ := d
    chart _ := t
    covers _ := ⟨(), Set.mem_univ _⟩
    linear _ _ _ := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    contMDiffOn_coordChange _ _ _ := contMDiffOn_const }
  let C := tensorSmoothAtlas A B
  let θ := (EquivariantStructure.ofFiniteRepresentation ρ).tensor σ
  let coords (x : M) : ((Fin d → ℂ) ⊗[ℂ] E x) ≃ₗ[ℂ] (Fin d → E x) :=
    (TensorProduct.comm ℂ (Fin d → ℂ) (E x)).trans
      (TensorProduct.piScalarRight ℂ ℂ (E x) (Fin d))
  have hcoords (x : M) (a : Fin d → ℂ) (v : E x) (i : Fin d) :
      coords x (a ⊗ₜ[ℂ] v) i = a i • v := by
    simp [coords, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  have hspec (p : C.Index) := (exists_tensor_trivialization
    (A.chart p.1) (B.chart p.2) (A.linear p.1) (B.linear p.2)).choose_spec
  have hbase (p : C.Index) : (C.chart p).baseSet = (B.chart p.2).baseSet := by
    exact (hspec p).1.trans (Set.univ_inter _)
  have hpure (p : C.Index) (x : M) (hx : x ∈ (B.chart p.2).baseSet)
      (a : Fin d → ℂ) (v : E x) (k : Fin (C.rank p)) :
      (C.chart p ⟨x, a ⊗ₜ[ℂ] v⟩).2 k =
        a (finProdFinEquiv.symm k).1 * (B.chart p.2 ⟨x, v⟩).2
          (finProdFinEquiv.symm k).2 := by
    have h := (hspec p).2.2 x ⟨Set.mem_univ x, hx⟩ a v
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    change (C.chart p ⟨x, a ⊗ₜ[ℂ] v⟩).2 (finProdFinEquiv
      ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) =
        a (finProdFinEquiv.symm k).1 * (B.chart p.2 ⟨x, v⟩).2
          (finProdFinEquiv.symm k).2 at h
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using h
  -- The same tensor chart sends its pure source-frame vector to the standard tensor basis.
  have hframe (p : C.Index) (x : M) (hx : x ∈ (C.chart p).baseSet)
      (k : Fin (C.rank p)) :
      (C.frameLinearEquiv p x hx).symm (Pi.single k 1) =
        Pi.single (finProdFinEquiv.symm k).1 1 ⊗ₜ[ℂ]
          (B.frameLinearEquiv p.2 x ((hbase p) ▸ hx)).symm
            (Pi.single (finProdFinEquiv.symm k).2 1) := by
    apply (C.frameLinearEquiv p x hx).injective
    rw [LinearEquiv.apply_symm_apply]
    funext l
    change (Pi.single k 1 : Fin (C.rank p) → ℂ) l = (C.chart p ⟨x, _⟩).2 l
    rw [hpure p x ((hbase p) ▸ hx)]
    have hv := (B.frameLinearEquiv p.2 x ((hbase p) ▸ hx)).apply_symm_apply
      (Pi.single (finProdFinEquiv.symm k).2 1)
    change (B.chart p.2 ⟨x, _⟩).2 = _ at hv
    rw [hv]
    obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective l
    obtain ⟨⟨c, e⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp only [Equiv.symm_apply_apply, Pi.single_apply, finProdFinEquiv.injective.eq_iff,
      Prod.mk.injEq]
    simpa only [Set.indicator, Set.mem_prod, Set.mem_singleton_iff, Pi.one_apply] using
      (Set.indicator_prod_one (s := {c}) (t := {e}) (i := a) (j := b) (M₀ := ℂ))
  have hBpoint (i : B.Index) (x : M) (hx : x ∈ (B.chart i).baseSet)
      (k : Fin (B.rank i)) :
      (⟨x, (B.frameLinearEquiv i x hx).symm (Pi.single k 1)⟩ : TotalSpace Unit E) =
        (B.chart i).toPartialEquiv.symm (x, Pi.single k 1) :=
    TotalSpace.mk_cast (F := Unit) (E := E) ((B.chart i).proj_symm_apply' hx) _
  -- Joint smoothness keeps the original representation matrix and the moving bundle action.
  have hB : σ.IsSmoothAtlas 𝓘(ℝ, VG) B := σ.isSmoothAtlas_native 𝓘(ℝ, VG) hσ
  have hθ : θ.IsSmoothAtlas 𝓘(ℝ, VG) C := by
    intro p q k
    apply contMDiffOn_pi_space.mpr
    intro l
    have hρG : ContMDiff 𝓘(ℝ, VG) 𝓘(ℝ, ℂ) ∞
        (fun g : G ↦ ρ.representation g
          (Pi.single (finProdFinEquiv.symm k).1 1) (finProdFinEquiv.symm l).1) :=
      contMDiff_pi_space.mp (ρ.contMDiff_action.comp
        (contMDiff_id.prodMk contMDiff_const)) (finProdFinEquiv.symm l).1
    have hρ : ContMDiffOn (𝓘(ℝ, VG).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, ℂ) ∞ (fun z : G × M ↦ ρ.representation z.1
          (Pi.single (finProdFinEquiv.symm k).1 1) (finProdFinEquiv.symm l).1)
        {z : G × M | z.2 ∈ (C.chart p).baseSet ∧ z.1 • z.2 ∈ (C.chart q).baseSet} :=
      (hρG.comp contMDiff_fst).contMDiffOn
    have hb := (contMDiffOn_pi_space.mp (hB p.2 q.2 (finProdFinEquiv.symm k).2)
      (finProdFinEquiv.symm l).2).mono (by
        intro (z : G × M)
          (hz : z.2 ∈ (C.chart p).baseSet ∧ z.1 • z.2 ∈ (C.chart q).baseSet)
        exact ⟨(hbase p) ▸ hz.1, (hbase q) ▸ hz.2⟩)
    apply ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
      (hρ.prodMk_space hb)).congr
    intro z hz
    simp only [Function.comp_apply, dite_eq_left hz.1, dite_eq_left ((hbase p) ▸ hz.1)]
    rw [hframe p z.2 hz.1]
    change (C.chart q ⟨z.1 • z.2,
      TensorProduct.map (ρ.representation z.1).toLinearMap (σ.linearMap z.1 z.2) _⟩).2 l = _
    rw [TensorProduct.map_tmul, hpure q _ ((hbase q) ▸ hz.2)]
    rfl
  -- Standard insertions are smooth in the same tensor atlas.
  have hinsert (i : Fin d) : IsSmoothAtlasBundleMap B C
      (fun x ↦ TensorProduct.mk ℂ (Fin d → ℂ) (E x) (Pi.single i 1)) := by
    refine ⟨contMDiff_id, ?_⟩
    intro p q k
    apply contMDiffOn_pi_space.mpr
    intro l
    have hb := (contMDiffOn_pi_space.mp (B.contMDiffOn_coordChange p q.2 k)
      (finProdFinEquiv.symm l).2).mono (by
        intro (x : M) (hx : x ∈ (B.chart p).baseSet ∩ (C.chart q).baseSet)
        exact ⟨hx.1, (hbase q) ▸ hx.2⟩)
    apply ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
      ((contMDiffOn_const (c := (Pi.single i 1 : Fin d → ℂ)
        (finProdFinEquiv.symm l).1)).prodMk_space hb)).congr
    intro x hx
    rw [dite_eq_left hx.1]
    change (C.chart q ⟨x, Pi.single i 1 ⊗ₜ[ℂ] _⟩).2 l = _
    rw [hpure q x ((hbase q) ▸ hx.2), hBpoint p x hx.1 k]
    rfl
  -- Each coefficient projection is smooth; its source-frame value is the matching basis scalar.
  have hproject (i : Fin d) : IsSmoothAtlasBundleMap C B
      (fun x ↦ (LinearMap.proj i).comp (coords x).toLinearMap) := by
    refine ⟨contMDiff_id, ?_⟩
    intro p q k
    apply contMDiffOn_pi_space.mpr
    intro l
    have hb := (contMDiffOn_pi_space.mp
      (B.contMDiffOn_coordChange p.2 q (finProdFinEquiv.symm k).2) l).mono (by
        intro (x : M) (hx : x ∈ (C.chart p).baseSet ∩ (B.chart q).baseSet)
        exact ⟨(hbase p) ▸ hx.1, hx.2⟩)
    apply ((contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
      ((contMDiffOn_const (c :=
        (Pi.single (finProdFinEquiv.symm k).1 1 : Fin d → ℂ) i)).prodMk_space hb)).congr
    intro x hx
    rw [dite_eq_left hx.1, hframe p x hx.1]
    change (B.chart q ⟨x, coords x (_ ⊗ₜ[ℂ] _) i⟩).2 l = _
    rw [hcoords]
    have hlin := (B.frameLinearEquiv q x hx.2).map_smul
      ((Pi.single (finProdFinEquiv.symm k).1 1 : Fin d → ℂ) i)
      ((B.frameLinearEquiv p.2 x ((hbase p) ▸ hx.1)).symm
        (Pi.single (finProdFinEquiv.symm k).2 1))
    change (B.chart q ⟨x, _ • _⟩).2 = _ at hlin
    rw [hlin]
    change _ = _
    simp only [Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun z : TotalSpace Unit E ↦
      (Pi.single (finProdFinEquiv.symm k).1 1 : Fin d → ℂ) i * (B.chart q z).2 l)
      (hBpoint p.2 x ((hbase p) ▸ hx.1) (finProdFinEquiv.symm k).2)
  have hrank (x : M) : Module.finrank ℂ ((Fin d → ℂ) ⊗[ℂ] E x) = d * r := by
    let : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    rw [Module.finrank_tensorProduct,
      VectorBundle.finrank_eq ℂ (EuclideanSpace ℂ (Fin r)) E x]
    simp
  -- One compatible native comparison transports the original action and both coordinate maps.
  obtain ⟨T, hrT, τ, hτ, e, he, hforward, hbackward⟩ :=
    C.exists_equivariant_smooth_model_of_rank_with_atlasMaps 𝓘(ℝ, VG) θ (d * r) hrank hθ
  let := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
  refine ⟨T, hrT, τ, hτ, e, he, ?_, ?_, ?_⟩
  · intro i
    exact (isSmoothAtlasBundleMap_native_iff _).mp (hforward.comp (hinsert i))
  · intro i
    exact (isSmoothAtlasBundleMap_native_iff _).mp ((hproject i).comp hbackward)
  · intro g x v i
    have heinv : (e.linearEquiv (g • x)).symm (τ.linearMap g x v) =
        θ.linearMap g x ((e.linearEquiv x).symm v) := by
      apply (e.linearEquiv (g • x)).injective
      rw [LinearEquiv.apply_symm_apply]
      have h := he g x ((e.linearEquiv x).symm v)
      change e.linearEquiv (g • x) (θ.linearMap g x ((e.linearEquiv x).symm v)) =
        τ.linearMap g x (e.linearEquiv x ((e.linearEquiv x).symm v)) at h
      rw [LinearEquiv.apply_symm_apply] at h
      exact h.symm
    change coords (g • x) ((e.linearEquiv (g • x)).symm (τ.linearMap g x v)) i = _
    rw [heinv]
    have hmix (w : (Fin d → ℂ) ⊗[ℂ] E x) :
        coords (g • x) (θ.linearMap g x w) i =
          ∑ j : Fin d, (ρ.representation g (Pi.single j 1)) i •
            σ.linearMap g x (coords x w j) := by
      induction w using TensorProduct.inductionOn with
      | tmul a b =>
        change coords (g • x)
          (TensorProduct.map (ρ.representation g).toLinearMap (σ.linearMap g x) (a ⊗ₜ b)) i = _
        rw [TensorProduct.map_tmul, hcoords]
        have ha : a = ∑ j : Fin d, a j • Pi.single j 1 := by
          ext j
          simp [Pi.single_apply]
        conv_lhs => rw [ha]
        simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Finset.sum_smul, hcoords, smul_smul]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_comm]
        rfl
      | add a b ha hb =>
        simp only [map_add, Pi.add_apply, ha, hb, smul_add, Finset.sum_add_distrib]
    exact hmix ((e.linearEquiv x).symm v)

end AtiyahSinger
