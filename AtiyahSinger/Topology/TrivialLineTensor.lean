/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# The original universe-lifted trivial line as tensor unit

Public module ID: M2265.

The trivial line has its standard Hermitian metric. Its pullback and
tensor-unit isomorphisms keep the given fibers and the original total-space
topologies. Tensor insertion is continuous for the finite-sum tensor topology;
finite local rank supplies inverse continuity. These maps are used to compare
actual tautological tensor products along projective line sections.

Source: the tensor-unit and pullback constructions for continuous complex
vector bundles, Hatcher, Vector Bundles and K-Theory, Section 1.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

universe u

attribute [local instance] sumTopology tensorTopology isFiniteRank_tensor isFiniteRank_pullback

/-- The standard Hermitian form on the specified universe-lifted trivial line. -/
def trivialLineMetric (X : Type u) [TopologicalSpace X] :
    letI := modelTopology (ULift.{u} ℂ) (Bundle.Trivial X (ULift.{u} ℂ))
    ContinuousHermitianMetric (Bundle.Trivial X (ULift.{u} ℂ)) := by
  let L := Bundle.Trivial X (ULift.{u} ℂ)
  letI := modelTopology (ULift.{u} ℂ) L
  let e : TotalSpace Unit L ≃ₜ X × ULift.{u} ℂ :=
    (unitTotalHomeomorph (ULift.{u} ℂ) L).trans
      (Bundle.Trivial.homeomorphProd X (ULift.{u} ℂ))
  let C : InnerProductSpace.Core ℂ (ULift.{u} ℂ) :=
    { inner := fun x y ↦ inner ℂ x.down y.down
      conj_inner_symm := fun x y ↦ InnerProductSpace.toCore.conj_inner_symm x.down y.down
      re_inner_nonneg := fun x ↦ InnerProductSpace.toCore.re_inner_nonneg x.down
      add_left := fun x y z ↦ InnerProductSpace.toCore.add_left x.down y.down z.down
      smul_left := fun x y z ↦ InnerProductSpace.toCore.smul_left x.down y.down z
      definite := fun x h ↦ ULift.ext (InnerProductSpace.toCore.definite x.down h) }
  refine
    { toCore := fun _ ↦ C
      continuous_pairing := ?_
      isFiniteRank := isFiniteRank_model (ULift.{u} ℂ) L }
  have hc : Continuous (fun z : TotalSpace Unit (L ×ᵇ L) ↦
      ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit L),
        (⟨z.proj, z.snd.2⟩ : TotalSpace Unit L))) := continuous_induced_dom
  exact (continuous_uliftDown.comp (e.continuous.comp hc.fst).snd).inner
    (continuous_uliftDown.comp (e.continuous.comp hc.snd).snd)

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- Right tensor multiplication by the same standard trivial line is the original bundle. -/
def tensorTrivialLineIso :
    letI := modelTopology (ULift.{u} ℂ) (Bundle.Trivial X (ULift.{u} ℂ))
    Iso (fun x ↦ E x ⊗[ℂ] Bundle.Trivial X (ULift.{u} ℂ) x) E := by
  let L := Bundle.Trivial X (ULift.{u} ℂ)
  letI := modelTopology (ULift.{u} ℂ) L
  letI := isFiniteRank_model (ULift.{u} ℂ) L
  let T := fun x ↦ E x ⊗[ℂ] L x
  let l (x : X) : E x ≃ₗ[ℂ] T x := (TensorProduct.rid ℂ (E x)).symm.trans
    (TensorProduct.congr (LinearEquiv.refl ℂ (E x))
      (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℂ] ℂ).symm)
  have hl (x : X) (v : E x) : l x v = v ⊗ₜ[ℂ] (1 : ULift.{u} ℂ) := rfl
  have hunit : Continuous (fun x : X ↦ (⟨x, (1 : ULift.{u} ℂ)⟩ : TotalSpace Unit L)) := by
    apply (continuous_modelTotal_iff (ULift.{u} ℂ) L _).mpr
    exact (Bundle.Trivial.homeomorphProd X (ULift.{u} ℂ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  -- Insert the constant unit as one pure tensor in the original finite-sum topology.
  have hins : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, l z.proj z.snd⟩ : TotalSpace Unit T)) := by
    let D := TotalSpace Unit (fun x ↦ (Fin 1 → E x) × (Fin 1 → L x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i : Fin 1 ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
        (fun i : Fin 1 ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit L)))) inferInstance
    let lift (z : TotalSpace Unit E) : D := ⟨z.proj, (fun _ ↦ z.snd, fun _ ↦ 1)⟩
    have hlift : Continuous lift := by
      apply continuous_induced_rng.mpr
      exact continuous_proj.prodMk ((continuous_pi fun _ ↦ continuous_id).prodMk
        (continuous_pi fun _ ↦ hunit.comp continuous_proj))
    have hsum : Continuous (fun z : D ↦
        (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ : TotalSpace Unit T)) :=
      continuous_iSup_rng (i := 1) continuous_coinduced_rng
    simpa [hl, lift, Function.comp_def] using hsum.comp hlift
  let f : Hom E T := ⟨fun x ↦ (l x).toLinearMap, hins⟩
  exact (f.toIso (fun x ↦ (l x).bijective)).symm

/-- Left tensor multiplication by the same standard trivial line is the original bundle. -/
def trivialLineTensorIso :
    letI := modelTopology (ULift.{u} ℂ) (Bundle.Trivial X (ULift.{u} ℂ))
    Iso (fun x ↦ Bundle.Trivial X (ULift.{u} ℂ) x ⊗[ℂ] E x) E := by
  let L := Bundle.Trivial X (ULift.{u} ℂ)
  letI := modelTopology (ULift.{u} ℂ) L
  letI := isFiniteRank_model (ULift.{u} ℂ) L
  let T := fun x ↦ L x ⊗[ℂ] E x
  let l (x : X) : E x ≃ₗ[ℂ] T x := (TensorProduct.lid ℂ (E x)).symm.trans
    (TensorProduct.congr (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℂ] ℂ).symm
      (LinearEquiv.refl ℂ (E x)))
  have hl (x : X) (v : E x) : l x v = (1 : ULift.{u} ℂ) ⊗ₜ[ℂ] v := rfl
  have hunit : Continuous (fun x : X ↦ (⟨x, (1 : ULift.{u} ℂ)⟩ : TotalSpace Unit L)) := by
    apply (continuous_modelTotal_iff (ULift.{u} ℂ) L _).mpr
    exact (Bundle.Trivial.homeomorphProd X (ULift.{u} ℂ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  -- This insertion has the same original tensor topology with the factors in left-unit order.
  have hins : Continuous (fun z : TotalSpace Unit E ↦
      (⟨z.proj, l z.proj z.snd⟩ : TotalSpace Unit T)) := by
    let D := TotalSpace Unit (fun x ↦ (Fin 1 → L x) × (Fin 1 → E x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun i : Fin 1 ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit L)),
        (fun i : Fin 1 ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit E)))) inferInstance
    let lift (z : TotalSpace Unit E) : D := ⟨z.proj, (fun _ ↦ 1, fun _ ↦ z.snd)⟩
    have hlift : Continuous lift := by
      apply continuous_induced_rng.mpr
      exact continuous_proj.prodMk ((continuous_pi fun _ ↦ hunit.comp continuous_proj).prodMk
        (continuous_pi fun _ ↦ continuous_id))
    have hsum : Continuous (fun z : D ↦
        (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ : TotalSpace Unit T)) :=
      continuous_iSup_rng (i := 1) continuous_coinduced_rng
    simpa [hl, lift, Function.comp_def] using hsum.comp hlift
  let f : Hom E T := ⟨fun x ↦ (l x).toLinearMap, hins⟩
  exact (f.toIso (fun x ↦ (l x).bijective)).symm

/-- Pullback of the specified trivial line keeps its exact scalar coordinate. -/
def pullbackTrivialLineIso {Y : Type u} [TopologicalSpace Y] (f : C(Y, X)) :
    letI := modelTopology (ULift.{u} ℂ) (Bundle.Trivial X (ULift.{u} ℂ))
    letI := modelTopology (ULift.{u} ℂ) (Bundle.Trivial Y (ULift.{u} ℂ))
    Iso (f *ᵖ (Bundle.Trivial X (ULift.{u} ℂ))) (Bundle.Trivial Y (ULift.{u} ℂ)) := by
  let L := Bundle.Trivial X (ULift.{u} ℂ)
  let K := Bundle.Trivial Y (ULift.{u} ℂ)
  letI := modelTopology (ULift.{u} ℂ) L
  letI := modelTopology (ULift.{u} ℂ) K
  let eX := (unitTotalHomeomorph (ULift.{u} ℂ) L).trans
    (Bundle.Trivial.homeomorphProd X (ULift.{u} ℂ))
  let eY := (unitTotalHomeomorph (ULift.{u} ℂ) K).trans
    (Bundle.Trivial.homeomorphProd Y (ULift.{u} ℂ))
  refine { linearEquiv := fun _ ↦ LinearEquiv.refl ℂ (ULift.{u} ℂ)
           continuous_total := ?_, continuous_symm := ?_ }
  · have hp : Continuous (fun z : TotalSpace Unit (f *ᵖ L) ↦
        (z.proj, (⟨f z.proj, z.snd⟩ : TotalSpace Unit L))) :=
      (inducing_pullbackTotalSpaceEmbedding Unit L f).continuous
    exact eY.symm.continuous.comp (hp.fst.prodMk (eX.continuous.comp hp.snd).snd)
  · apply (inducing_pullbackTotalSpaceEmbedding Unit L f).continuous_iff.mpr
    exact eY.continuous.fst.prodMk (eX.symm.continuous.comp
      ((f.continuous.comp eY.continuous.fst).prodMk eY.continuous.snd))

end AtiyahSinger.ComplexBundle
