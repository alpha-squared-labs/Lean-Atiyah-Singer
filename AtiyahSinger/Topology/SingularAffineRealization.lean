/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AffineSimplexSubdivision
public import AtiyahSinger.Topology.SingularCohomology
public import Mathlib.Geometry.Convex.ConvexSpace.Topology

/-!
# Affine expressions in the original singular chain complex

Public module ID: M2120.

The affine map determined by points of a standard simplex is continuous and
stays in that same simplex. Composing it with a supplied singular simplex gives
an original singular generator. Extending linearly interprets the finite vertex
expressions for subdivision and its homotopy in the original chain complex.
No extension of a singular simplex outside its domain is chosen.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Convexity Opposite
open scoped Simplicial

universe u

/-- The affine map between finite standard simplices is continuous in the native topology. -/
theorem continuous_stdSimplex_affineMapMk {m n : ℕ}
    (v : Fin (m + 1) → StdSimplex ℝ (Fin (n + 1))) :
    Continuous (StdSimplex.affineMapMk (R := ℝ) v) := by
  classical
  -- Every target coordinate is a finite linear combination of the input weights.
  have hweights (s : StdSimplex ℝ (Fin (m + 1))) (i : Fin (n + 1)) :
      ((StdSimplex.affineMapMk (R := ℝ) v) s).weights i =
        ∑ j : Fin (m + 1), s.weights j * (v j).weights i := by
    simp [StdSimplex.affineMapMk_apply, iConvexComb, Finsupp.sum_mapDomain_index,
      add_smul, Finsupp.sum_fintype]
  apply (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).isInducing.continuous_iff.mpr
  change Continuous (fun s : StdSimplex ℝ (Fin (m + 1)) ↦
    fun i : Fin (n + 1) ↦ ((StdSimplex.affineMapMk (R := ℝ) v) s).weights i)
  simp only [hweights]
  fun_prop

/-- The original affine simplex map with its native continuous-map structure. -/
def stdSimplexAffineMap {m n : ℕ} (v : Fin (m + 1) → StdSimplex ℝ (Fin (n + 1))) :
    C(StdSimplex ℝ (Fin (m + 1)), StdSimplex ℝ (Fin (n + 1))) :=
  ⟨StdSimplex.affineMapMk (R := ℝ) v, continuous_stdSimplex_affineMapMk v⟩

variable {X : Type u} [TopologicalSpace X] {n : ℕ}

/-- Interpret a tuple of points as an actual singular simplex within the supplied simplex. -/
def singularAffineSimplex (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ)
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (n + 1))) :
    (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋k⦌) :=
  ((TopCat.of X).toSSetObjEquiv (op ⦋k⦌)).symm (σ.comp (stdSimplexAffineMap v))

/-- Linear interpretation of finite vertex expressions in the original singular chains. -/
def singularAffineChain (R : Type) [CommRing R]
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ) :
    SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (k + 1) →ₗ[R]
      (singularChains R X).X k :=
  Finsupp.linearCombination R (fun v ↦
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := singularCoefficient R) (singularAffineSimplex σ k v) (ULift.up 1))

variable (R : Type) [CommRing R]

/-- Realization of one finite vertex generator uses its coefficient on the original simplex. -/
theorem singularAffineChain_single (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ)
    (v : Fin (k + 1) → StdSimplex ℝ (Fin (n + 1))) (a : R) :
    singularAffineChain R σ k (Finsupp.single v a) =
      a • (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R) (singularAffineSimplex σ k v) (ULift.up 1) := by
  exact Finsupp.linearCombination_single _ _ _

/-- The original vertices realize the supplied singular generator with exactly its coefficient. -/
theorem singularAffineChain_vertices (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (a : R) :
    singularAffineChain R σ n (Finsupp.single StdSimplex.single a) =
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R)
        (((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)).symm σ) (ULift.up a) := by
  have hvertices : singularAffineSimplex σ n StdSimplex.single =
      ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)).symm σ := by
    apply ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)).injective
    apply ContinuousMap.ext
    intro s
    change σ (s.iConvexComb StdSimplex.single) = σ s
    rw [StdSimplex.iConvexComb_single]
  rw [singularAffineChain_single, hvertices, ← map_smul]
  congr 1
  apply ULift.ext
  simp

/-- The actual singular boundary realizes the alternating vertex boundary of the same expression. -/
theorem singularAffineChain_boundary (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ)
    (c : SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (k + 2)) :
    (singularChains R X).d (k + 1) k (singularAffineChain R σ (k + 1) c) =
      singularAffineChain R σ k
        (vertexChainBoundary R (StdSimplex ℝ (Fin (n + 1))) (k + 1) c) := by
  classical
  let S := TopCat.toSSet.obj (TopCat.of X)
  -- Each original face is the affine simplex obtained by deleting that same vertex.
  have hface (v : Fin (k + 2) → StdSimplex ℝ (Fin (n + 1))) (i : Fin (k + 2)) :
      S.δ i (singularAffineSimplex σ (k + 1) v) =
        singularAffineSimplex σ k (v ∘ i.succAbove) := by
    apply ((TopCat.of X).toSSetObjEquiv (op ⦋k⦌)).injective
    apply ContinuousMap.ext
    intro s
    change σ (StdSimplex.affineMapMk (R := ℝ) v (s.map i.succAbove)) =
      σ (StdSimplex.affineMapMk (R := ℝ) (v ∘ i.succAbove) s)
    have heq : (StdSimplex.affineMapMk (R := ℝ) v).comp (StdSimplex.affineMap i.succAbove) =
        StdSimplex.affineMapMk (R := ℝ) (v ∘ i.succAbove) := by
      apply StdSimplex.affineMap_ext
      intro j
      simp
    exact congrArg σ (congrArg (fun f ↦ f s) heq)
  suffices h : ((singularChains R X).d (k + 1) k).hom.comp (singularAffineChain R σ (k + 1)) =
      (singularAffineChain R σ k).comp
        (vertexChainBoundary R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) from
    congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, singularAffineChain_single, map_smul,
    vertexChainBoundary_single, map_sum]
  erw [((singularChains R X).d (k + 1) k).hom.map_smul]
  apply congrArg (fun z ↦ a • z)
  simp only [one_smul]
  change (S.ιChainComplex (singularAffineSimplex σ (k + 1) v) ≫
    (S.chainComplex (singularCoefficient R)).d (k + 1) k) (ULift.up 1) = _
  rw [SSet.ιChainComplex_d]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hface, ← Int.cast_smul_eq_zsmul R]
  simp
  rfl

/-- Affine substitution before realization equals substitution in the same finite vertex chains. -/
theorem singularAffineChain_comp {m : ℕ}
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X))
    (v : Fin (m + 1) → StdSimplex ℝ (Fin (n + 1))) (k : ℕ)
    (c : SimplexVertexChain R (StdSimplex ℝ (Fin (m + 1))) (k + 1)) :
    singularAffineChain R (σ.comp (stdSimplexAffineMap v)) k c =
      singularAffineChain R σ k
        (vertexChainMap R (StdSimplex ℝ (Fin (m + 1))) (StdSimplex.affineMapMk (R := ℝ) v)
          (k + 1) c) := by
  classical
  suffices h : singularAffineChain R (σ.comp (stdSimplexAffineMap v)) k =
      (singularAffineChain R σ k).comp
        (vertexChainMap R (StdSimplex ℝ (Fin (m + 1))) (StdSimplex.affineMapMk (R := ℝ) v)
          (k + 1)) from congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro w a
  simp only [LinearMap.comp_apply, vertexChainMap, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, singularAffineChain_single]
  apply congrArg (fun τ ↦ a • (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (R := singularCoefficient R) τ (ULift.up 1))
  apply ((TopCat.of X).toSSetObjEquiv (op ⦋k⦌)).injective
  apply ContinuousMap.ext
  intro s
  change σ (StdSimplex.affineMapMk (R := ℝ) v (StdSimplex.affineMapMk (R := ℝ) w s)) =
    σ (StdSimplex.affineMapMk (R := ℝ) ((StdSimplex.affineMapMk (R := ℝ) v) ∘ w) s)
  have heq : (StdSimplex.affineMapMk (R := ℝ) v).comp (StdSimplex.affineMapMk (R := ℝ) w) =
      StdSimplex.affineMapMk (R := ℝ) ((StdSimplex.affineMapMk (R := ℝ) v) ∘ w) := by
    apply StdSimplex.affineMap_ext
    intro j
    simp
  exact congrArg σ (congrArg (fun f ↦ f s) heq)

end AtiyahSinger
