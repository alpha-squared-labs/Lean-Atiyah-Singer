/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantCompactSourceExcision
public import AtiyahSinger.Analysis.EquivariantPositiveExcision
public import AtiyahSinger.Analysis.OpenExtensionIndex
public import AtiyahSinger.Geometry.CotangentDiffeomorph
public import AtiyahSinger.Geometry.OpenCotangent
public import AtiyahSinger.Topology.EquivariantOpenExtension
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Full equivariant analytic excision through a common open manifold

Public module ID: M0527.

Two specified equivariant smooth open embeddings send the same original
cotangent support class into two compact smooth manifolds. The full analytic
indices agree in the original representation ring. The embeddings are given
as diffeomorphisms onto actual open subsets. Their cotangent lifts use their
inverse differentials, followed by the existing open cotangent inclusions.
Neither open embedding is assumed proper, and the two compact environments
need not be diffeomorphic.

Sources: ASI I section 4, the excision axiom B1 and its use in Proposition
(4.4), pp.501--505; SG III.13, Excision Property 13.4, pp.248--249.
The explicit equivariant arbitrary-class assembly is a project supplement.
In particular the existing ordinary finite-CW-source excision theorem does
not by itself prove this full representation-valued statement. The proof uses
compact invariant localization, equivariant relative realization, and the
actual kernel representations; the zero-dimensional case uses clopen extension.
No index equality, trivial action, or global fixed bundle rank is a premise.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 35

variable {n : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold (𝓡 n) ∞ O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

/-- The actual inverse-dual lift of a specified open manifold embedding. -/
def cotangentOpenEmbeddingMap (U : Opens M) (f : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ U) :
    C(CotangentTotalSpace (n := n) (M := O),
      CotangentTotalSpace (n := n) (M := M)) :=
  ⟨fun z ↦ cotangentOpenInclusion U (cotangentDiffeomorph f z),
    (isOpenEmbedding_cotangentOpenInclusion U).continuous.comp
      (cotangentDiffeomorph f).continuous⟩

/-- A smooth open base embedding gives the original open cotangent embedding. -/
theorem isOpenEmbedding_cotangentOpenEmbeddingMap
    (U : Opens M) (f : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ U) :
    IsOpenEmbedding (cotangentOpenEmbeddingMap U f) := by
  /- The first factor is the actual cotangent homeomorphism induced by f.
  The second is the existing open inclusion of the original cotangent of U
  into that of M. Compose their open-embedding certificates. This concerns
  inverse-dual cotangent transport; a bare continuous base embedding would
  not supply this map. In general its open image is not closed or proper. -/
  -- Compose the actual inverse-dual homeomorphism with the open cotangent inclusion.
  exact (isOpenEmbedding_cotangentOpenInclusion U).comp
    (cotangentDiffeomorph f).isOpenEmbedding

variable {VG G : Type*}
  [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace VG G] [LieGroup 𝓘(ℝ, VG) ∞ G]
  [MulAction G O] [ContinuousSMul G O]
  [ContMDiffSMul 𝓘(ℝ, VG) (𝓡 n) ∞ G O]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul 𝓘(ℝ, VG) (𝓡 n) ∞ G M]


set_option linter.unusedSectionVars false in
/-- Base equivariance intertwines the actual native inverse-differential cotangent lifts. -/
theorem cotangentOpenEmbeddingMap_equivariant
    (U : Opens M) (f : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ U)
    (hf : ∀ (a : G) (x : O), (f (a • x) : M) = a • (f x : M)) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    ∀ (a : G) (z : CotangentTotalSpace (n := n) (M := O)),
      cotangentOpenEmbeddingMap U f (a • z) = a • cotangentOpenEmbeddingMap U f z := by
  /- Stage 1: hf says that the same embedding intertwines the two original
  base actions. Its open image is invariant, so the inverse map on that
  image intertwines the restricted actions as well. Retain these exact
  inverse maps, rather than selecting an unrelated action on U.
  Stage 2: differentiate the equations for a inverse and use the chain
  rule. Inherited open-submanifold charts make the inclusion differential
  the identity, while f contributes its genuine inverse differential.
  Precomposition of each original covector with the resulting equal maps
  gives the stated equality on the native total spaces. -/
  let I := 𝓡 n
  let E := EuclideanSpace ℝ (Fin n)
  let := smoothCotangentMulAction (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  -- Inherited open charts give the identity derivative for the actual inclusion.
  have hinclusion (y : U) : mfderiv I I (Subtype.val : U → M) y =
      ContinuousLinearMap.id ℝ E := by
    have hι : MDifferentiableAt (𝓡 n) (𝓡 n) (Subtype.val : U → M) y :=
      (contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)
    have hrep : writtenInExtChartAt (𝓡 n) (𝓡 n) y (Subtype.val : U → M) =ᶠ[
        𝓝 ((extChartAt (𝓡 n) y) y)]
        writtenInExtChartAt (𝓡 n) (𝓡 n) (y : M) (id : M → M) := by
      change (fun v ↦ (chartAt (EuclideanSpace ℝ (Fin n)) (y : M))
          (((chartAt (EuclideanSpace ℝ (Fin n)) y).symm v : U) : M)) =ᶠ[
            𝓝 (chartAt (EuclideanSpace ℝ (Fin n)) (y : M) y)]
        (fun v ↦ (chartAt (EuclideanSpace ℝ (Fin n)) (y : M))
          ((chartAt (EuclideanSpace ℝ (Fin n)) (y : M)).symm v))
      exact
        (U.chartAt_subtype_val_symm_eventuallyEq (x := y)).symm.fun_comp
          (chartAt (EuclideanSpace ℝ (Fin n)) (y : M))
    have hD := hrep.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := Set.range (𝓡 n))
    have hid := mfderiv_id (I := 𝓡 n) (x := (y : M))
    rw [mfderiv, ite_eq_left hι]
    change fderivWithin ℝ (writtenInExtChartAt (𝓡 n) (𝓡 n) y
      (Subtype.val : U → M)) (Set.range (𝓡 n)) ((extChartAt (𝓡 n) y) y) = _
    rw [hD]
    simp only [mfderiv, mdifferentiableAt_id, ↓reduceIte] at hid
    change fderivWithin ℝ (writtenInExtChartAt (𝓡 n) (𝓡 n) (y : M)
      (id : M → M)) (Set.range (𝓡 n)) ((extChartAt (𝓡 n) (y : M)) y) = _ at hid
    exact hid
  let g : O → M := fun x ↦ (f x : M)
  have hg : ContMDiff I I ∞ g := contMDiff_subtype_val.comp f.contMDiff
  have hderiv (x : O) : mfderiv I I g x = mfderiv I I f x := by
    have h := mfderiv_comp x
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp))
      (f.mdifferentiable (by simp) x)
    change mfderiv I I g x = _ at h
    erw [h, hinclusion (f x), ContinuousLinearMap.id_comp]
  -- Differentiate base equivariance for the inverse action, retaining the same f.
  intro a z
  let dO := Diffeomorph.smul (M := O) 𝓘(ℝ, VG) I ∞ a
  let dM := Diffeomorph.smul (M := M) 𝓘(ℝ, VG) I ∞ a
  have heq : g ∘ dO.symm = dM.symm ∘ g := funext (hf a⁻¹)
  have hchain (x : O) :
      (mfderiv I I f (dO.symm x)).comp (mfderiv I I dO.symm x) =
        (mfderiv I I dM.symm (g x)).comp (mfderiv I I f x) := by
    have h : mfderiv I I (g ∘ dO.symm) x =
        mfderiv I I (dM.symm ∘ g) x := by rw [heq]
    rw [mfderiv_comp x (hg.mdifferentiable (by simp) (dO.symm x))
      (dO.symm.mdifferentiable (by simp) x),
      mfderiv_comp x (dM.symm.mdifferentiable (by simp) (g x))
        (hg.mdifferentiable (by simp) x)] at h
    erw [hderiv (dO.symm x), hderiv x] at h
    exact h
  -- The inverse differential of this diffeomorphism cancels its forward differential.
  have hleft (x : O) :
      (mfderiv I I f.symm (f x)).comp (mfderiv I I f x) =
        ContinuousLinearMap.id ℝ E := by
    have h := mfderiv_comp x (f.symm.mdifferentiable (by simp) (f x))
      (f.mdifferentiable (by simp) x)
    have he : (f.symm : U → O) ∘ f = id := funext f.symm_apply_apply
    rw [he, mfderiv_id] at h
    exact h.symm
  have hright (x : O) :
      (mfderiv I I f x).comp (mfderiv I I f.symm (f x)) =
        ContinuousLinearMap.id ℝ E := by
    have h := mfderiv_comp (f x)
      (f.mdifferentiable (by simp) (f.symm (f x)))
      (f.symm.mdifferentiable (by simp) (f x))
    have he : (f : O → U) ∘ f.symm = id := funext f.apply_symm_apply
    rw [he, mfderiv_id] at h
    erw [f.symm_apply_apply] at h
    exact h.symm
  have hdual (x : O) :
      (mfderiv I I dO.symm x).comp (mfderiv I I f.symm (f x)) =
        (mfderiv I I f.symm (f (dO.symm x))).comp
          (mfderiv I I dM.symm (g x)) := by
    apply ContinuousLinearMap.ext
    intro v
    have hl (w : E) : (mfderiv I I f.symm (f (dO.symm x)))
        ((mfderiv I I f (dO.symm x)) w) = w :=
      congrArg (fun A : E →L[ℝ] E ↦ A w) (hleft (dO.symm x))
    have hr (w : E) : (mfderiv I I f x)
        ((mfderiv I I f.symm (f x)) w) = w :=
      congrArg (fun A : E →L[ℝ] E ↦ A w) (hright x)
    have h := congrArg (fun A : E →L[ℝ] E ↦
      (mfderiv I I f.symm (f (dO.symm x)))
        (A ((mfderiv I I f.symm (f x)) v))) (hchain x)
    change (mfderiv I I f.symm (f (dO.symm x)))
        ((mfderiv I I f (dO.symm x))
          ((mfderiv I I dO.symm x) ((mfderiv I I f.symm (f x)) v))) =
      (mfderiv I I f.symm (f (dO.symm x)))
        ((mfderiv I I dM.symm (g x))
          ((mfderiv I I f x) ((mfderiv I I f.symm (f x)) v))) at h
    erw [hl, hr] at h
    exact h
  -- Covector precomposition reverses this chain-rule identity on the native total spaces.
  change (⟨(f (dO z.proj) : M),
    (z.snd.comp (mfderiv I I dO.symm (dO z.proj))).comp
      (mfderiv I I f.symm (f (dO z.proj)))⟩ : CotangentTotalSpace (n := n) (M := M)) =
    ⟨dM (g z.proj), (z.snd.comp (mfderiv I I f.symm (f z.proj))).comp
      (mfderiv I I dM.symm (dM (g z.proj)))⟩
  have hbase : (f (dO z.proj) : M) = dM (g z.proj) := hf a z.proj
  have hfiber :
      (z.snd.comp (mfderiv I I dO.symm (dO z.proj))).comp
          (mfderiv I I f.symm (f (dO z.proj))) =
        (z.snd.comp (mfderiv I I f.symm (f z.proj))).comp
          (mfderiv I I dM.symm (dM (g z.proj))) := by
    apply ContinuousLinearMap.ext
    intro v
    have h := congrArg (fun A : E →L[ℝ] E ↦ z.snd (A v)) (hdual (dO z.proj))
    have hb : g (dO z.proj) = dM (g z.proj) := hbase
    erw [dO.symm_apply_apply, hb] at h
    exact h
  exact TotalSpace.ext hbase (heq_of_eq hfiber)

variable [CompactSpace G] [T2Space G] [T2Space O] [T2Space M]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- Original equivariant open extension through this same inverse-dual cotangent map. -/
def equivariantCotangentKZeroOpenEmbedding
    (U : Opens M) (f : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ U)
    (hf : ∀ (a : G) (x : O), (f (a • x) : M) = a • (f x : M)) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := O)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
    EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := O)) →+
      EquivariantSupportTripleKZero G (CotangentTotalSpace (n := n) (M := M)) := by
  letI := smoothCotangentMulAction (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := O)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  exact equivariantSupportTripleKZeroOpenPushforward
    (cotangentOpenEmbeddingMap U f) (isOpenEmbedding_cotangentOpenEmbeddingMap U f)
    (cotangentOpenEmbeddingMap_equivariant (VG := VG) U f hf)

variable [FiniteDimensional ℝ VG] [MeasurableSpace G] [BorelSpace G]
  [SecondCountableTopology O]
  [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N]
  [MeasurableSpace N] [BorelSpace N]
  [MulAction G N] [ContinuousSMul G N]
  [ContMDiffSMul 𝓘(ℝ, VG) (𝓡 n) ∞ G N]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- Factor both original maps through the same native open cotangent and retain the arbitrary class.
/-- The same arbitrary support class has equal full indices in two compact environments. -/
theorem equivariantAnalyticIndexMap_excision
    (U : Opens M) (V : Opens N)
    (f : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ U) (g : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ V)
    (hf : ∀ (a : G) (x : O), (f (a • x) : M) = a • (f x : M))
    (hg : ∀ (a : G) (x : O), (g (a • x) : N) = a • (g x : N)) :
    letI := smoothCotangentMulAction (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := O)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
    letI := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
    letI : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
      ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
        (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
    (equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := M)).comp
        (equivariantCotangentKZeroOpenEmbedding (VG := VG) U f hf) =
      (equivariantAnalyticIndexMap (n := n) (VG := VG) (G := G) (M := N)).comp
        (equivariantCotangentKZeroOpenEmbedding (VG := VG) V g hg) := by
  classical
  let := smoothCotangentMulAction (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := O) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := O)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := M)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  let := smoothCotangentMulAction (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := N) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := N)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  by_cases hn : n = 0
  · -- The compact zero-dimensional ambient makes the actual source finite and compact.
    subst n
    let : DiscreteTopology M :=
      ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0)) M
    let : Finite M := finite_of_compact_of_discrete
    let : Finite O := Finite.of_injective f f.injective
    let : CompactSpace O := inferInstance
    let : MeasurableSpace O := borel O
    let : BorelSpace O := ⟨rfl⟩
    apply AddMonoidHom.ext
    intro a
    change equivariantAnalyticIndexMap (VG := VG) (G := G) (M := M)
        (equivariantCotangentKZeroOpenEmbedding (VG := VG) U f hf a) =
      equivariantAnalyticIndexMap (VG := VG) (G := G) (M := N)
        (equivariantCotangentKZeroOpenEmbedding (VG := VG) V g hg a)
    exact (equivariantAnalyticIndexMap_compactSource_openPushforward U f hf
      (cotangentOpenEmbeddingMap_equivariant (VG := VG) U f hf) a).trans
      (equivariantAnalyticIndexMap_compactSource_openPushforward V g hg
        (cotangentOpenEmbeddingMap_equivariant (VG := VG) V g hg) a).symm
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  -- Equip the actual images with their inherited actions; the original f and g are retained.
  have hUi (a : G) (x : M) : a • x ∈ U ↔ x ∈ U := by
    constructor
    · intro hx
      have hh := (f (a⁻¹ • f.symm ⟨a • x, hx⟩)).property
      rw [hf, f.apply_symm_apply, inv_smul_smul] at hh
      exact hh
    · intro hx
      have hh := (f (a • f.symm ⟨x, hx⟩)).property
      rw [hf, f.apply_symm_apply] at hh
      exact hh
  have hVi (a : G) (x : N) : a • x ∈ V ↔ x ∈ V := by
    constructor
    · intro hx
      have hh := (g (a⁻¹ • g.symm ⟨a • x, hx⟩)).property
      rw [hg, g.apply_symm_apply, inv_smul_smul] at hh
      exact hh
    · intro hx
      have hh := (g (a • g.symm ⟨x, hx⟩)).property
      rw [hg, g.apply_symm_apply] at hh
      exact hh
  let := invariantOpenMulAction U hUi
  let := continuousSMul_invariantOpen U hUi
  let := contMDiffSMul_invariantOpen (n := n) 𝓘(ℝ, VG) U hUi
  let := invariantOpenMulAction V hVi
  let := continuousSMul_invariantOpen V hVi
  let := contMDiffSMul_invariantOpen (n := n) 𝓘(ℝ, VG) V hVi
  have hU (a : G) (x : U) : ((a • x : U) : M) = a • x.val := rfl
  have hV (a : G) (x : V) : ((a • x : V) : N) = a • x.val := rfl
  let e := f.symm.trans g
  have hfinv (a : G) (x : U) : f.symm (a • x) = a • f.symm x := by
    apply f.injective
    change f (f.symm (a • x)) = f (a • f.symm x)
    apply Subtype.ext
    rw [f.apply_symm_apply, hf, f.apply_symm_apply]
    rfl
  have he (a : G) (x : U) : (e (a • x)).val = a • (e x).val := by
    change (g (f.symm (a • x))).val = a • (g (f.symm x)).val
    rw [hfinv, hg]
  let := smoothCotangentMulAction (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := U) 𝓘(ℝ, VG)
  let : ContinuousSMul G (CotangentTotalSpace (n := n) (M := U)) :=
    ContMDiffSMul.continuousSMul (I := 𝓘(ℝ, VG))
      (I' := (𝓡 n).prod 𝓘(ℝ, CotangentModel n)) ∞
  let XO := CotangentTotalSpace (n := n) (M := O)
  let XU := CotangentTotalSpace (n := n) (M := U)
  let XM := CotangentTotalSpace (n := n) (M := M)
  let XN := CotangentTotalSpace (n := n) (M := N)
  let d : C(XO, XU) := ⟨cotangentDiffeomorph f, (cotangentDiffeomorph f).continuous⟩
  let i : C(XU, XM) :=
    ⟨cotangentOpenInclusion U, (isOpenEmbedding_cotangentOpenInclusion U).continuous⟩
  let j : C(XU, XN) := cotangentOpenEmbeddingMap V e
  have hi : IsOpenEmbedding i := isOpenEmbedding_cotangentOpenInclusion U
  have hj : IsOpenEmbedding j := isOpenEmbedding_cotangentOpenEmbeddingMap V e
  have hd : IsOpenEmbedding d := (cotangentDiffeomorph f).isOpenEmbedding
  have hig : ∀ (a : G) (z : XU), i (a • z) = a • i z :=
    cotangentOpenInclusion_smul 𝓘(ℝ, VG) U hU
  have hjg : ∀ (a : G) (z : XU), j (a • z) = a • j z :=
    cotangentOpenEmbeddingMap_equivariant (VG := VG) V e he
  have hdg (a : G) (z : XO) : d (a • z) = a • d z := by
    apply hi.injective
    exact (cotangentOpenEmbeddingMap_equivariant (VG := VG) U f hf a z).trans
      (hig a (d z)).symm
  -- The inverse-dual composition law identifies these maps on actual covectors.
  have hfe : f.trans e = g := by
    apply Diffeomorph.ext
    intro x
    change g (f.symm (f x)) = g x
    rw [f.symm_apply_apply]
  have hji : j.comp d = cotangentOpenEmbeddingMap V g := by
    apply ContinuousMap.ext
    intro z
    have hh := congrArg (fun H : XO ≃ₜ CotangentTotalSpace (n := n) (M := V) ↦
      cotangentOpenInclusion V (H z)) (cotangentDiffeomorph_trans f e)
    rw [hfe] at hh
    exact hh.symm
  have hMfactor := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    d hd hdg i hi hig
  have hNfactor := equivariantSupportTripleKZeroOpenPushforward_functoriality.2
    d hd hdg j hj hjg
  have hMpush : equivariantCotangentKZeroOpenEmbedding (VG := VG) U f hf =
      (equivariantSupportTripleKZeroOpenPushforward i hi hig).comp
        (equivariantSupportTripleKZeroOpenPushforward d hd hdg) := hMfactor
  have hNpush : equivariantCotangentKZeroOpenEmbedding (VG := VG) V g hg =
      (equivariantSupportTripleKZeroOpenPushforward j hj hjg).comp
        (equivariantSupportTripleKZeroOpenPushforward d hd hdg) := by
    change equivariantSupportTripleKZeroOpenPushforward (cotangentOpenEmbeddingMap V g)
      (isOpenEmbedding_cotangentOpenEmbeddingMap V g)
      (cotangentOpenEmbeddingMap_equivariant (VG := VG) V g hg) = _
    simpa only [hji] using hNfactor
  apply AddMonoidHom.ext
  intro a
  change equivariantAnalyticIndexMap (VG := VG) (G := G) (M := M)
      (equivariantCotangentKZeroOpenEmbedding (VG := VG) U f hf a) =
    equivariantAnalyticIndexMap (VG := VG) (G := G) (M := N)
      (equivariantCotangentKZeroOpenEmbedding (VG := VG) V g hg a)
  rw [hMpush, hNpush]
  exact equivariantAnalyticIndexMap_open_excision_of_pos hnPos U V hU hV hUi e he
    hig hjg (equivariantSupportTripleKZeroOpenPushforward d hd hdg a)

end AtiyahSinger
