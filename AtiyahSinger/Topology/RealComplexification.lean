/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIso
public import AtiyahSinger.Topology.BundleSum
public import AtiyahSinger.Topology.ComplexificationBundle
public import AtiyahSinger.Topology.RealBundleSupport

/-!
# Complexification of original real bundles with locally varying rank

Public module ID: M2040.

The genuine scalar extension and its existing topology are reused from
ComplexificationBundle. Only the finite-rank theorem is generalized from
a native fixed model to original local real-linear charts. Direct sum uses
mathlib's original same-base double topology, with phantom model G times H.
The complexification sum map is the actual tensor-product distributivity map.

Sources: Husemoller Chapter 17, section 11; MS section 15. This is the same
standard scalar-extension construction componentwise, with no global rank
bound, orientation, metric, connectedness or base compactness requirement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RealBundle

open Bundle
open scoped TensorProduct

variable {X : Type*} [TopologicalSpace X]
  (G : Type*) (V : X → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace G V)] [hV : IsFiniteRank G V]

include hV

/-- Complexification preserves local finite rank on exactly the existing original topology. -/
theorem isFiniteRank_complexification :
    letI := ComplexBundle.complexificationTopology G V
    ComplexBundle.IsFiniteRank (fun x ↦ ℂ ⊗[ℝ] V x) := by
  /- Stage 1: take an original real-linear local chart with model R^r.
  Its two copies give a chart for the original same-base real double.
  The existing real/imaginary equivalence identifies its coordinates with
  C^r by (u,v) mapped to u+i*v. These maps and their inverses are continuous
  for exactly complexificationTopology, and complex-linear on each fiber.
  Stage 2: the original chart domains cover the base. Their ranks may vary;
  no uniform rank bound is introduced. These actual complex-linear charts
  establish ComplexBundle.IsFiniteRank, including rank zero and empty bases. -/
  classical
  let := ComplexBundle.complexificationTopology G V
  constructor
  intro x
  obtain ⟨r, e, he, hlinearE⟩ := hV.exists_linear_trivialization x
  let d := e
  let s := r
  have hd : x ∈ d.baseSet := he
  have hlinearF := hlinearE
  -- Use the two original chart inverses on their common open base set.
  let invE (y : X) (v : Fin r → ℝ) : V y :=
    if hy : y ∈ e.baseSet then
      cast (congrArg V (e.proj_symm_apply' hy)) (e.toPartialEquiv.symm (y, v)).snd
    else 0
  let invF (y : X) (v : Fin s → ℝ) : V y :=
    if hy : y ∈ d.baseSet then
      cast (congrArg V (d.proj_symm_apply' hy)) (d.toPartialEquiv.symm (y, v)).snd
    else 0
  have hpointE (y : X) (v : Fin r → ℝ) (hy : y ∈ e.baseSet) :
      (⟨y, invE y v⟩ : TotalSpace G V) = e.toPartialEquiv.symm (y, v) := by
    dsimp only [invE]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := G) (E := V) (e.proj_symm_apply' hy) _
  have hpointF (y : X) (v : Fin s → ℝ) (hy : y ∈ d.baseSet) :
      (⟨y, invF y v⟩ : TotalSpace G V) = d.toPartialEquiv.symm (y, v) := by
    dsimp only [invF]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := G) (E := V) (d.proj_symm_apply' hy) _
  have hinverseE (y : X) (hy : y ∈ e.baseSet) (v : V y) :
      invE y (e ⟨y, v⟩).2 = v := by
    have hp := (hpointE y (e ⟨y, v⟩).2 hy).trans
      (e.symm_apply_mk_proj (x := (⟨y, v⟩ : TotalSpace G V)) (e.mem_source.mpr hy))
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace G V ↦ z.snd) hp)
  have hinverseF (y : X) (hy : y ∈ d.baseSet) (v : V y) :
      invF y (d ⟨y, v⟩).2 = v := by
    have hp := (hpointF y (d ⟨y, v⟩).2 hy).trans
      (d.symm_apply_mk_proj (x := (⟨y, v⟩ : TotalSpace G V)) (d.mem_source.mpr hy))
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace G V ↦ z.snd) hp)
  -- Continuity is proved in the original direct-sum topology, not transported from a chart.
  let pairMap : TotalSpace (G × G) (V ×ᵇ V) → TotalSpace G V × TotalSpace G V :=
    fun z ↦ (⟨z.proj, z.snd.1⟩, ⟨z.proj, z.snd.2⟩)
  have hinducing : Topology.IsInducing pairMap := ⟨rfl⟩
  have hprojE : Continuous (fun z : TotalSpace (G × G) (V ×ᵇ V) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace G V)) := continuous_fst.comp hinducing.continuous
  have hprojF : Continuous (fun z : TotalSpace (G × G) (V ×ᵇ V) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace G V)) := continuous_snd.comp hinducing.continuous
  have hbase : Continuous (π (G × G) (V ×ᵇ V)) := (continuous_projection G V).comp hprojE
  let td : Trivialization ((Fin r → ℝ) × (Fin s → ℝ)) (π (G × G) (V ×ᵇ V)) :=
    { toFun := fun z ↦ (z.proj, (e ⟨z.proj, z.snd.1⟩).2, (d ⟨z.proj, z.snd.2⟩).2)
      invFun := fun y ↦ ⟨y.1, invE y.1 y.2.1, invF y.1 y.2.2⟩
      source := π (G × G) (V ×ᵇ V) ⁻¹' (e.baseSet ∩ d.baseSet)
      baseSet := e.baseSet ∩ d.baseSet
      target := (e.baseSet ∩ d.baseSet) ×ˢ Set.univ
      map_source' := fun _ h ↦ ⟨h, Set.mem_univ _⟩
      map_target' := fun _ h ↦ h.1
      left_inv' := by
        intro z hz
        exact TotalSpace.ext rfl (heq_of_eq (Prod.ext
          (hinverseE z.proj hz.1 z.snd.1) (hinverseF z.proj hz.2 z.snd.2)))
      right_inv' := by
        intro y hy
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · change (e ⟨y.1, invE y.1 y.2.1⟩).2 = y.2.1
            rw [hpointE y.1 y.2.1 hy.1.1]
            exact congrArg Prod.snd (e.apply_symm_apply' hy.1.1)
          · change (d ⟨y.1, invF y.1 y.2.2⟩).2 = y.2.2
            rw [hpointF y.1 y.2.2 hy.1.2]
            exact congrArg Prod.snd (d.apply_symm_apply' hy.1.2)
      open_source := (e.open_baseSet.inter d.open_baseSet).preimage hbase
      open_target := (e.open_baseSet.inter d.open_baseSet).prod isOpen_univ
      open_baseSet := e.open_baseSet.inter d.open_baseSet
      continuousOn_toFun := hbase.continuousOn.prodMk
        ((continuous_snd.comp_continuousOn
          (e.toOpenPartialHomeomorph.continuousOn.comp hprojE.continuousOn
            (fun _ h ↦ e.mem_source.mpr h.1))).prodMk
          (continuous_snd.comp_continuousOn
            (d.toOpenPartialHomeomorph.continuousOn.comp hprojF.continuousOn
              (fun _ h ↦ d.mem_source.mpr h.2))))
      continuousOn_invFun := by
        rw [hinducing.continuousOn_iff]
        have hE : ContinuousOn (fun y : X × (Fin r → ℝ) × (Fin s → ℝ) ↦
            e.toPartialEquiv.symm (y.1, y.2.1)) ((e.baseSet ∩ d.baseSet) ×ˢ Set.univ) :=
          e.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
          (fun y hy ↦ e.mem_target.mpr hy.1.1)
        have hF : ContinuousOn (fun y : X × (Fin r → ℝ) × (Fin s → ℝ) ↦
            d.toPartialEquiv.symm (y.1, y.2.2)) ((e.baseSet ∩ d.baseSet) ×ˢ Set.univ) :=
          d.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
          (fun y hy ↦ d.mem_target.mpr hy.1.2)
        refine (hE.prodMk hF).congr ?_
        intro y hy
        exact Prod.ext (hpointE y.1 y.2.1 hy.1.1) (hpointF y.1 y.2.2 hy.1.2)
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  -- Join the two real coordinate blocks in the fixed complex coordinate space.
  let q : ((Fin r → ℝ) × (Fin r → ℝ)) ≃ₜ (Fin r → ℂ) :=
    { toFun := fun uv j ↦ (uv.1 j : ℂ) + (uv.2 j : ℂ) * Complex.I
      invFun := fun z ↦ (fun j ↦ (z j).re, fun j ↦ (z j).im)
      left_inv := by
        intro uv
        simp
      right_inv := by
        intro z
        funext j
        exact Complex.re_add_im (z j)
      continuous_toFun := by
        apply continuous_pi
        intro j
        exact ((Complex.continuous_ofReal.comp
          ((continuous_apply j).comp continuous_fst)).add
          ((Complex.continuous_ofReal.comp
            ((continuous_apply j).comp continuous_snd)).mul continuous_const))
      continuous_invFun := by
        apply Continuous.prodMk
        · exact continuous_pi (fun j ↦ Complex.continuous_re.comp (continuous_apply j))
        · exact continuous_pi (fun j ↦ Complex.continuous_im.comp (continuous_apply j)) }
  let t : Trivialization (Fin r → ℂ) (π Unit (fun y ↦ ℂ ⊗[ℝ] V y)) :=
    (td.transFiberHomeomorph q).compHomeomorph
      (ComplexBundle.complexificationDoubleTotalHomeomorph G V)
  refine ⟨r, t, ⟨he, hd⟩, ?_⟩
  intro y hy
  let L : V y →ₗ[ℝ] (Fin r → ℝ) := IsLinearMap.mk' _ (hlinearE y hy.1)
  let f : (ℂ ⊗[ℝ] V y) → (Fin r → ℂ) := fun w j ↦
    (L (complexificationReIm (V y) w).1 j : ℂ) +
      (L (complexificationReIm (V y) w).2 j : ℂ) * Complex.I
  have hvalue (w : ℂ ⊗[ℝ] V y) : (t ⟨y, w⟩).2 = f w := rfl
  -- Scalar extension is checked on pure tensors and then on their finite sums.
  have hadd (u v : ℂ ⊗[ℝ] V y) : f (u + v) = f u + f v := by
    funext j
    simp [f, map_add, add_mul]
    ring
  have hpure (z : ℂ) (v : V y) : f (z ⊗ₜ[ℝ] v) = fun j ↦ z * (L v j : ℂ) := by
    funext j
    change (L (complexificationReIm (V y) (z ⊗ₜ[ℝ] v)).1 j : ℂ) +
      (L (complexificationReIm (V y) (z ⊗ₜ[ℝ] v)).2 j : ℂ) * Complex.I = _
    rw [(complexificationReIm_properties (V y)).1]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    calc
      _ = ((z.re : ℂ) + (z.im : ℂ) * Complex.I) * (L v j : ℂ) := by ring
      _ = _ := by rw [Complex.re_add_im]
  constructor
  · intro u v
    rw [hvalue, hvalue, hvalue]
    exact hadd u v
  · intro z w
    rw [hvalue, hvalue]
    induction w using TensorProduct.inductionOn with
    | tmul a v =>
      rw [TensorProduct.smul_tmul', hpure, hpure]
      funext j
      simp [mul_assoc]
    | add u v hu hv =>
      rw [smul_add, hadd, hu, hv, hadd, smul_add]


variable (H : Type*) (W : X → Type*)
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)]
  [TopologicalSpace (TotalSpace H W)] [hW : IsFiniteRank H W]

include hW

/-- The original native same-base direct sum of locally finite real bundles has finite rank. -/
theorem isFiniteRank_prod : IsFiniteRank (G × H) (V ×ᵇ W) := by
  /- Intersect one original real-linear chart from each summand. Their
  fiberwise product is a chart for the existing induced same-base product
  topology. Reindex its finite real coordinates by the sum of the two local
  ranks. These domains cover the base, independently of global rank bounds. -/
  classical
  constructor
  intro x
  obtain ⟨r, e, he, hlinearE⟩ := hV.exists_linear_trivialization x
  obtain ⟨s, d, hd, hlinearF⟩ := hW.exists_linear_trivialization x
  -- Use the two original chart inverses on their common open base set.
  let invE (y : X) (v : Fin r → ℝ) : V y :=
    if hy : y ∈ e.baseSet then
      cast (congrArg V (e.proj_symm_apply' hy)) (e.toPartialEquiv.symm (y, v)).snd
    else 0
  let invF (y : X) (v : Fin s → ℝ) : W y :=
    if hy : y ∈ d.baseSet then
      cast (congrArg W (d.proj_symm_apply' hy)) (d.toPartialEquiv.symm (y, v)).snd
    else 0
  have hpointE (y : X) (v : Fin r → ℝ) (hy : y ∈ e.baseSet) :
      (⟨y, invE y v⟩ : TotalSpace G V) = e.toPartialEquiv.symm (y, v) := by
    dsimp only [invE]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := G) (E := V) (e.proj_symm_apply' hy) _
  have hpointF (y : X) (v : Fin s → ℝ) (hy : y ∈ d.baseSet) :
      (⟨y, invF y v⟩ : TotalSpace H W) = d.toPartialEquiv.symm (y, v) := by
    dsimp only [invF]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := H) (E := W) (d.proj_symm_apply' hy) _
  have hinverseE (y : X) (hy : y ∈ e.baseSet) (v : V y) :
      invE y (e ⟨y, v⟩).2 = v := by
    have hp := (hpointE y (e ⟨y, v⟩).2 hy).trans
      (e.symm_apply_mk_proj (x := (⟨y, v⟩ : TotalSpace G V)) (e.mem_source.mpr hy))
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace G V ↦ z.snd) hp)
  have hinverseF (y : X) (hy : y ∈ d.baseSet) (v : W y) :
      invF y (d ⟨y, v⟩).2 = v := by
    have hp := (hpointF y (d ⟨y, v⟩).2 hy).trans
      (d.symm_apply_mk_proj (x := (⟨y, v⟩ : TotalSpace H W)) (d.mem_source.mpr hy))
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace H W ↦ z.snd) hp)
  -- Continuity is proved in the original direct-sum topology, not transported from a chart.
  let pairMap : TotalSpace (G × H) (V ×ᵇ W) → TotalSpace G V × TotalSpace H W :=
    fun z ↦ (⟨z.proj, z.snd.1⟩, ⟨z.proj, z.snd.2⟩)
  have hinducing : Topology.IsInducing pairMap := ⟨rfl⟩
  have hprojE : Continuous (fun z : TotalSpace (G × H) (V ×ᵇ W) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace G V)) := continuous_fst.comp hinducing.continuous
  have hprojF : Continuous (fun z : TotalSpace (G × H) (V ×ᵇ W) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace H W)) := continuous_snd.comp hinducing.continuous
  have hbase : Continuous (π (G × H) (V ×ᵇ W)) := (continuous_projection G V).comp hprojE
  let t : Trivialization ((Fin r → ℝ) × (Fin s → ℝ)) (π (G × H) (V ×ᵇ W)) :=
    { toFun := fun z ↦ (z.proj, (e ⟨z.proj, z.snd.1⟩).2, (d ⟨z.proj, z.snd.2⟩).2)
      invFun := fun y ↦ ⟨y.1, invE y.1 y.2.1, invF y.1 y.2.2⟩
      source := π (G × H) (V ×ᵇ W) ⁻¹' (e.baseSet ∩ d.baseSet)
      baseSet := e.baseSet ∩ d.baseSet
      target := (e.baseSet ∩ d.baseSet) ×ˢ Set.univ
      map_source' := fun _ h ↦ ⟨h, Set.mem_univ _⟩
      map_target' := fun _ h ↦ h.1
      left_inv' := by
        intro z hz
        exact TotalSpace.ext rfl (heq_of_eq (Prod.ext
          (hinverseE z.proj hz.1 z.snd.1) (hinverseF z.proj hz.2 z.snd.2)))
      right_inv' := by
        intro y hy
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · change (e ⟨y.1, invE y.1 y.2.1⟩).2 = y.2.1
            rw [hpointE y.1 y.2.1 hy.1.1]
            exact congrArg Prod.snd (e.apply_symm_apply' hy.1.1)
          · change (d ⟨y.1, invF y.1 y.2.2⟩).2 = y.2.2
            rw [hpointF y.1 y.2.2 hy.1.2]
            exact congrArg Prod.snd (d.apply_symm_apply' hy.1.2)
      open_source := (e.open_baseSet.inter d.open_baseSet).preimage hbase
      open_target := (e.open_baseSet.inter d.open_baseSet).prod isOpen_univ
      open_baseSet := e.open_baseSet.inter d.open_baseSet
      continuousOn_toFun := hbase.continuousOn.prodMk
        ((continuous_snd.comp_continuousOn
          (e.toOpenPartialHomeomorph.continuousOn.comp hprojE.continuousOn
            (fun _ h ↦ e.mem_source.mpr h.1))).prodMk
          (continuous_snd.comp_continuousOn
            (d.toOpenPartialHomeomorph.continuousOn.comp hprojF.continuousOn
              (fun _ h ↦ d.mem_source.mpr h.2))))
      continuousOn_invFun := by
        rw [hinducing.continuousOn_iff]
        have hE : ContinuousOn (fun y : X × (Fin r → ℝ) × (Fin s → ℝ) ↦
            e.toPartialEquiv.symm (y.1, y.2.1)) ((e.baseSet ∩ d.baseSet) ×ˢ Set.univ) :=
          e.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
          (fun y hy ↦ e.mem_target.mpr hy.1.1)
        have hF : ContinuousOn (fun y : X × (Fin r → ℝ) × (Fin s → ℝ) ↦
            d.toPartialEquiv.symm (y.1, y.2.2)) ((e.baseSet ∩ d.baseSet) ×ˢ Set.univ) :=
          d.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
          (fun y hy ↦ d.mem_target.mpr hy.1.2)
        refine (hE.prodMk hF).congr ?_
        intro y hy
        exact Prod.ext (hpointE y.1 y.2.1 hy.1.1) (hpointF y.1 y.2.2 hy.1.2)
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  -- Concatenate the two finite coordinate families by the standard Fin-sum equivalence.
  let c : ((Fin r → ℝ) × (Fin s → ℝ)) ≃L[ℝ] (Fin (r + s) → ℝ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℝ ℝ).symm.trans
      (LinearEquiv.piCongrLeft ℝ (fun _ : Fin (r + s) ↦ ℝ) finSumFinEquiv)).toContinuousLinearEquiv
  refine ⟨r + s, t.transFiberHomeomorph c.toHomeomorph, ⟨he, hd⟩, ?_⟩
  intro y hy
  constructor
  · intro v w
    change c ((e ⟨y, v.1 + w.1⟩).2, (d ⟨y, v.2 + w.2⟩).2) =
      c ((e ⟨y, v.1⟩).2, (d ⟨y, v.2⟩).2) + c ((e ⟨y, w.1⟩).2, (d ⟨y, w.2⟩).2)
    rw [(hlinearE y hy.1).map_add, (hlinearF y hy.2).map_add]
    exact c.map_add ((e ⟨y, v.1⟩).2, (d ⟨y, v.2⟩).2)
      ((e ⟨y, w.1⟩).2, (d ⟨y, w.2⟩).2)
  · intro a v
    change c ((e ⟨y, a • v.1⟩).2, (d ⟨y, a • v.2⟩).2) =
      a • c ((e ⟨y, v.1⟩).2, (d ⟨y, v.2⟩).2)
    rw [(hlinearE y hy.1).map_smul, (hlinearF y hy.2).map_smul]
    exact c.map_smul a ((e ⟨y, v.1⟩).2, (d ⟨y, v.2⟩).2)


set_option linter.unusedSectionVars false in
/-- Tensor distributivity is continuous in both directions for the original double topologies. -/
theorem complexificationSumIso_properties :
    letI := ComplexBundle.complexificationTopology G V
    letI := ComplexBundle.complexificationTopology H W
    letI := ComplexBundle.complexificationTopology (G × H) (V ×ᵇ W)
    letI := ComplexBundle.sumTopology
      (E := fun x ↦ ℂ ⊗[ℝ] V x) (F := fun x ↦ ℂ ⊗[ℝ] W x)
    Continuous (fun z : TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] (V x × W x)) ↦
      (⟨z.proj, TensorProduct.prodRight ℝ ℂ ℂ (V z.proj) (W z.proj) z.snd⟩ :
        TotalSpace Unit (fun x ↦ (ℂ ⊗[ℝ] V x) × (ℂ ⊗[ℝ] W x)))) ∧
      Continuous (fun z : TotalSpace Unit
          (fun x ↦ (ℂ ⊗[ℝ] V x) × (ℂ ⊗[ℝ] W x)) ↦
        (⟨z.proj, (TensorProduct.prodRight ℝ ℂ ℂ (V z.proj) (W z.proj)).symm z.snd⟩ :
          TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] (V x × W x)))) := by
  /- In the specified real/imaginary total homeomorphisms, these two actual
  tensor maps regroup (v_re,w_re,v_im,w_im) into (v_re,v_im,w_re,w_im)
  and back. Each original component projection is continuous in the induced
  same-base product topology. The regroupings and inverse are continuous,
  and composition with the existing homeomorphisms proves both assertions.
  The algebraic maps are exactly TensorProduct.prodRight, not chosen isomorphisms. -/
  let := ComplexBundle.complexificationTopology G V
  let := ComplexBundle.complexificationTopology H W
  let := ComplexBundle.complexificationTopology (G × H) (V ×ᵇ W)
  let := ComplexBundle.sumTopology
    (E := fun x ↦ ℂ ⊗[ℝ] V x) (F := fun x ↦ ℂ ⊗[ℝ] W x)
  -- Identify the precise tensor distributivity map in the original real/imaginary coordinates.
  have hcoords (x : X) (z : ℂ ⊗[ℝ] (V x × W x)) :
      (complexificationReIm (V x) ((TensorProduct.prodRight ℝ ℂ ℂ (V x) (W x) z).1),
        complexificationReIm (W x) ((TensorProduct.prodRight ℝ ℂ ℂ (V x) (W x) z).2)) =
      (((complexificationReIm (V x × W x) z).1.1,
          (complexificationReIm (V x × W x) z).2.1),
        ((complexificationReIm (V x × W x) z).1.2,
          (complexificationReIm (V x × W x) z).2.2)) := by
    induction z using TensorProduct.inductionOn with
    | tmul a v =>
      simp only [TensorProduct.prodRight_tmul, (complexificationReIm_properties _).1]
      rfl
    | add u v hu hv =>
      simpa only [map_add, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk] using
        congrArg₂ (· + ·) hu hv
  have hinv (x : X) (z : (ℂ ⊗[ℝ] V x) × (ℂ ⊗[ℝ] W x)) :
      complexificationReIm (V x × W x)
          ((TensorProduct.prodRight ℝ ℂ ℂ (V x) (W x)).symm z) =
        (((complexificationReIm (V x) z.1).1, (complexificationReIm (W x) z.2).1),
          ((complexificationReIm (V x) z.1).2, (complexificationReIm (W x) z.2).2)) := by
    have h := hcoords x ((TensorProduct.prodRight ℝ ℂ ℂ (V x) (W x)).symm z)
    rw [LinearEquiv.apply_symm_apply] at h
    exact Prod.ext
      (Prod.ext (congrArg (fun p ↦ p.1.1) h).symm
        (congrArg (fun p ↦ p.2.1) h).symm)
      (Prod.ext (congrArg (fun p ↦ p.1.2) h).symm
        (congrArg (fun p ↦ p.2.2) h).symm)
  constructor
  · -- Each real coordinate projection is continuous in the original nested double topology.
    let Z := TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] (V x × W x))
    have hdouble :=
      (ComplexBundle.complexificationDoubleTotalHomeomorph (G × H) (V ×ᵇ W)).continuous
    have hpair :=
      (FiberBundle.Prod.isInducing_diag (G × H) (V ×ᵇ W)
        (G × H) (V ×ᵇ W)).continuous.comp hdouble
    have hre := (FiberBundle.Prod.isInducing_diag G V H W).continuous.comp
      (continuous_fst.comp hpair)
    have him := (FiberBundle.Prod.isInducing_diag G V H W).continuous.comp
      (continuous_snd.comp hpair)
    have hVre : Continuous (fun z : Z ↦
        (⟨z.proj, (complexificationReIm (V z.proj × W z.proj) z.snd).1.1⟩ :
          TotalSpace G V)) := continuous_fst.comp hre
    have hWre : Continuous (fun z : Z ↦
        (⟨z.proj, (complexificationReIm (V z.proj × W z.proj) z.snd).1.2⟩ :
          TotalSpace H W)) := continuous_snd.comp hre
    have hVim : Continuous (fun z : Z ↦
        (⟨z.proj, (complexificationReIm (V z.proj × W z.proj) z.snd).2.1⟩ :
          TotalSpace G V)) := continuous_fst.comp him
    have hWim : Continuous (fun z : Z ↦
        (⟨z.proj, (complexificationReIm (V z.proj × W z.proj) z.snd).2.2⟩ :
          TotalSpace H W)) := continuous_snd.comp him
    -- Test the actual output map against all three defining induced topologies.
    apply continuous_induced_rng.mpr
    apply Continuous.prodMk
    · apply continuous_induced_rng.mpr
      apply continuous_induced_rng.mpr
      change Continuous (fun z : Z ↦
        ((⟨z.proj, (complexificationReIm (V z.proj)
          ((TensorProduct.prodRight ℝ ℂ ℂ (V z.proj) (W z.proj) z.snd).1)).1⟩ :
            TotalSpace G V),
          (⟨z.proj, (complexificationReIm (V z.proj)
            ((TensorProduct.prodRight ℝ ℂ ℂ (V z.proj) (W z.proj) z.snd).1)).2⟩ :
              TotalSpace G V)))
      have hVcoord (z : Z) := congrArg Prod.fst (hcoords z.proj z.snd)
      refine (hVre.prodMk hVim).congr ?_
      intro z
      have hc := hVcoord z
      dsimp only at hc
      rw [hc]
    · apply continuous_induced_rng.mpr
      apply continuous_induced_rng.mpr
      change Continuous (fun z : Z ↦
        ((⟨z.proj, (complexificationReIm (W z.proj)
          ((TensorProduct.prodRight ℝ ℂ ℂ (V z.proj) (W z.proj) z.snd).2)).1⟩ :
            TotalSpace H W),
          (⟨z.proj, (complexificationReIm (W z.proj)
            ((TensorProduct.prodRight ℝ ℂ ℂ (V z.proj) (W z.proj) z.snd).2)).2⟩ :
              TotalSpace H W)))
      have hWcoord (z : Z) := congrArg Prod.snd (hcoords z.proj z.snd)
      refine (hWre.prodMk hWim).congr ?_
      intro z
      have hc := hWcoord z
      dsimp only at hc
      rw [hc]
  · -- Conversely regroup the same four continuous coordinate projections into two real sums.
    let Z := TotalSpace Unit (fun x ↦ (ℂ ⊗[ℝ] V x) × (ℂ ⊗[ℝ] W x))
    have hp : Continuous (fun z : Z ↦
        ((⟨z.proj, z.snd.1⟩ : TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] V x)),
          (⟨z.proj, z.snd.2⟩ : TotalSpace Unit (fun x ↦ ℂ ⊗[ℝ] W x)))) :=
      continuous_induced_dom
    have hVdouble := (ComplexBundle.complexificationDoubleTotalHomeomorph G V).continuous.comp
      (continuous_fst.comp hp)
    have hWdouble := (ComplexBundle.complexificationDoubleTotalHomeomorph H W).continuous.comp
      (continuous_snd.comp hp)
    have hVpair := (FiberBundle.Prod.isInducing_diag G V G V).continuous.comp hVdouble
    have hWpair := (FiberBundle.Prod.isInducing_diag H W H W).continuous.comp hWdouble
    have hre : Continuous (fun z : Z ↦
        (⟨z.proj, ((complexificationReIm (V z.proj) z.snd.1).1,
          (complexificationReIm (W z.proj) z.snd.2).1)⟩ :
            TotalSpace (G × H) (V ×ᵇ W))) := by
      apply continuous_induced_rng.mpr
      exact (continuous_fst.comp hVpair).prodMk (continuous_fst.comp hWpair)
    have him : Continuous (fun z : Z ↦
        (⟨z.proj, ((complexificationReIm (V z.proj) z.snd.1).2,
          (complexificationReIm (W z.proj) z.snd.2).2)⟩ :
            TotalSpace (G × H) (V ×ᵇ W))) := by
      apply continuous_induced_rng.mpr
      exact (continuous_snd.comp hVpair).prodMk (continuous_snd.comp hWpair)
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    change Continuous (fun z : Z ↦
      ((⟨z.proj, (complexificationReIm (V z.proj × W z.proj)
        ((TensorProduct.prodRight ℝ ℂ ℂ (V z.proj) (W z.proj)).symm z.snd)).1⟩ :
          TotalSpace (G × H) (V ×ᵇ W)),
        (⟨z.proj, (complexificationReIm (V z.proj × W z.proj)
          ((TensorProduct.prodRight ℝ ℂ ℂ (V z.proj) (W z.proj)).symm z.snd)).2⟩ :
            TotalSpace (G × H) (V ×ᵇ W))))
    simpa only [hinv] using hre.prodMk him

/-- The actual complexification of a real direct sum is the sum of its actual complexifications. -/
def complexificationSumIso :
    letI := ComplexBundle.complexificationTopology G V
    letI := ComplexBundle.complexificationTopology H W
    letI := ComplexBundle.complexificationTopology (G × H) (V ×ᵇ W)
    letI := ComplexBundle.sumTopology
      (E := fun x ↦ ℂ ⊗[ℝ] V x) (F := fun x ↦ ℂ ⊗[ℝ] W x)
    ComplexBundle.Iso (fun x ↦ ℂ ⊗[ℝ] (V x × W x))
      (fun x ↦ (ℂ ⊗[ℝ] V x) × (ℂ ⊗[ℝ] W x)) :=
  letI := ComplexBundle.complexificationTopology G V
  letI := ComplexBundle.complexificationTopology H W
  letI := ComplexBundle.complexificationTopology (G × H) (V ×ᵇ W)
  letI := ComplexBundle.sumTopology
    (E := fun x ↦ ℂ ⊗[ℝ] V x) (F := fun x ↦ ℂ ⊗[ℝ] W x)
  { linearEquiv x := TensorProduct.prodRight ℝ ℂ ℂ (V x) (W x)
    continuous_total := (complexificationSumIso_properties G V H W).1
    continuous_symm := (complexificationSumIso_properties G V H W).2 }

end AtiyahSinger.RealBundle
