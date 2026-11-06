/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.EquivariantVectorBundle

/-!
# Tensor actions on the original finite-rank complex bundles

Public module ID: M1768.

The moving-fiber action is exactly `TensorProduct.map` of the two specified
original linear maps. Its topology is the existing finite-sum tensor topology.
Local finite charts prove joint continuity in the group element and tensor
vector. This does not assert that multiplying a final-topology presentation
by an arbitrary group preserves its quotient property.

The existing tensor bundle maps and isomorphisms intertwine these actual actions.
Finite rank is local and may vary; no compact group, compact base, separation,
local compactness, metric or global rank bound is assumed.
Sources: Hatcher, Vector Bundles and K-Theory, pp.13--15, for the tensor charts;
ASI I Section 2 for the equivariant bundle framework. The explicit general
continuous-action and original-map certificates are standard supplements to
these constructions. Their original construction certificates are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

attribute [local instance] tensorTopology

/-- The original tensor maps obey both action laws and are jointly continuous in finite charts. -/
theorem EquivariantStructure.tensor_properties [IsFiniteRank E] [IsFiniteRank F]
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) :
    (∀ (x : X) (v : E x ⊗[ℂ] F x),
      (⟨(1 : G) • x, TensorProduct.map (σ.linearMap 1 x) (τ.linearMap 1 x) v⟩ :
        TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x)) = ⟨x, v⟩) ∧
    (∀ (g h : G) (x : X) (v : E x ⊗[ℂ] F x),
      (⟨(g * h) • x, TensorProduct.map (σ.linearMap (g * h) x)
        (τ.linearMap (g * h) x) v⟩ : TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x)) =
      ⟨g • (h • x), TensorProduct.map (σ.linearMap g (h • x)) (τ.linearMap g (h • x))
        (TensorProduct.map (σ.linearMap h x) (τ.linearMap h x) v)⟩) ∧
    Continuous (fun p : G × TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x) ↦
      (⟨p.1 • p.2.proj,
        TensorProduct.map (σ.linearMap p.1 p.2.proj) (τ.linearMap p.1 p.2.proj) p.2.snd⟩ :
        TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x))) := by
  /- Stage 1: equality of the original moving factor maps includes equality
  of their target base points. After this transport, tensor functoriality gives
  both action laws without introducing another action.
  Stage 2: near each source point choose one finite chart in each factor.
  Their inverse frames lift each tensor coordinate vector continuously into
  one fixed finite-sum generator. The tensor-basis expansion proves that this
  generator returns the original tensor vector, including in rank zero.
  Stage 3: apply the original jointly continuous factor actions to that finite
  generating tuple. The output has the same moved base in every factor, and
  composing with the original target generator gives the displayed action.
  Thus continuity is local in the source charts. No product of a quotient
  map is assumed to remain quotient; no target chart, compactness, separation
  assumption or common global rank is needed. -/
  classical
  -- Equality of moving factor maps includes the base-point transport.
  have hmaps {x y z : X} (a : E x →ₗ[ℂ] E y) (b : F x →ₗ[ℂ] F y)
      (a' : E x →ₗ[ℂ] E z) (b' : F x →ₗ[ℂ] F z)
      (hE : ∀ v, (⟨y, a v⟩ : TotalSpace Unit E) = ⟨z, a' v⟩)
      (hF : ∀ v, (⟨y, b v⟩ : TotalSpace Unit F) = ⟨z, b' v⟩)
      (v : E x ⊗[ℂ] F x) :
      (⟨y, TensorProduct.map a b v⟩ : TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x)) =
        ⟨z, TensorProduct.map a' b' v⟩ := by
    have hyz : y = z := congrArg (fun w : TotalSpace Unit E ↦ w.proj) (hE 0)
    subst z
    have ha : a = a' := LinearMap.ext (fun u ↦ TotalSpace.mk_injective y (hE u))
    have hb : b = b' := LinearMap.ext (fun u ↦ TotalSpace.mk_injective y (hF u))
    rw [ha, hb]
  refine ⟨?_, ?_, ?_⟩
  · intro x v
    simpa only [TensorProduct.map_id, LinearMap.id_apply] using
      hmaps (σ.linearMap 1 x) (τ.linearMap 1 x) LinearMap.id LinearMap.id
        (σ.one_map x) (τ.one_map x) v
  · intro g h x v
    simpa only [TensorProduct.map_comp, LinearMap.comp_apply] using
      hmaps (σ.linearMap (g * h) x) (τ.linearMap (g * h) x)
        ((σ.linearMap g (h • x)).comp (σ.linearMap h x))
        ((τ.linearMap g (h • x)).comp (τ.linearMap h x))
        (σ.mul_map g h x) (τ.mul_map g h x) v
  · -- Map each fixed finite generating family by the jointly continuous factor actions.
    let T := TotalSpace Unit (fun x ↦ E x ⊗[ℂ] F x)
    let D (m : ℕ) := TotalSpace Unit (fun x ↦ (Fin m → E x) × (Fin m → F x))
    let instD (m : ℕ) : TopologicalSpace (D m) := TopologicalSpace.induced
      (fun z : D m ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit F)))) inferInstance
    let generator (m : ℕ) (z : D m) : T :=
      ⟨z.proj, ∑ i, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩
    have hgenerator (m : ℕ) : Continuous (generator m) :=
      continuous_iSup_rng (i := m) continuous_coinduced_rng
    have hcoords (m : ℕ) : Continuous (fun z : D m ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit F)))) := continuous_induced_dom
    have hbase : Continuous (π Unit (fun x ↦ E x ⊗[ℂ] F x)) := by
      apply continuous_iSup_dom.mpr
      intro m
      apply continuous_coinduced_dom.mpr
      exact (hcoords m).fst
    let moved (m : ℕ) (p : G × D m) : D m :=
      ⟨p.1 • p.2.proj, (fun i ↦ σ.linearMap p.1 p.2.proj (p.2.snd.1 i)),
        (fun i ↦ τ.linearMap p.1 p.2.proj (p.2.snd.2 i))⟩
    have hmoved (m : ℕ) : Continuous (moved m) := by
      apply continuous_induced_rng.mpr
      refine (continuous_fst.smul ((hcoords m).fst.comp continuous_snd)).prodMk
        ((continuous_pi ?_).prodMk (continuous_pi ?_))
      · intro i
        exact σ.continuous_action.comp (continuous_fst.prodMk
          (((continuous_apply i).comp (hcoords m).snd.fst).comp continuous_snd))
      · intro i
        exact τ.continuous_action.comp (continuous_fst.prodMk
          (((continuous_apply i).comp (hcoords m).snd.snd).comp continuous_snd))
    apply continuous_iff_continuousAt.mpr
    intro p₀
    obtain ⟨r, e, he₀, he⟩ := IsFiniteRank.exists_linear_trivialization (E := E) p₀.2.proj
    obtain ⟨s, f, hf₀, hf⟩ := IsFiniteRank.exists_linear_trivialization (E := F) p₀.2.proj
    obtain ⟨t, htbase, htlinear, htpure⟩ := exists_tensor_trivialization e f he hf
    -- The original inverse factor coordinates supply a local finite-sum lift.
    let eLin (x : X) (hx : x ∈ e.baseSet) : E x ≃ₗ[ℂ] (Fin r → ℂ) :=
      { toFun := fun v ↦ (e ⟨x, v⟩).2
        invFun := fun v ↦ cast (congrArg E (e.proj_symm_apply' hx))
          (e.toOpenPartialHomeomorph.symm (x, v)).snd
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd)
            (e.symm_apply_mk_proj (x := ⟨x, v⟩) (e.mem_source.mpr hx))
        right_inv := by
          intro v
          have hp := TotalSpace.mk_cast (F := Unit) (E := E)
            (e.proj_symm_apply' (x := v) hx) (e.toOpenPartialHomeomorph.symm (x, v)).snd
          exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hp).trans
            (congrArg Prod.snd (e.apply_symm_apply' hx))
        map_add' := (he x hx).map_add
        map_smul' := (he x hx).map_smul }
    let fLin (x : X) (hx : x ∈ f.baseSet) : F x ≃ₗ[ℂ] (Fin s → ℂ) :=
      { toFun := fun v ↦ (f ⟨x, v⟩).2
        invFun := fun v ↦ cast (congrArg F (f.proj_symm_apply' hx))
          (f.toOpenPartialHomeomorph.symm (x, v)).snd
        left_inv := by
          intro v
          rw [cast_eq_iff_heq]
          exact congr_arg_heq (fun z : TotalSpace Unit F ↦ z.snd)
            (f.symm_apply_mk_proj (x := ⟨x, v⟩) (f.mem_source.mpr hx))
        right_inv := by
          intro v
          have hp := TotalSpace.mk_cast (F := Unit) (E := F)
            (f.proj_symm_apply' (x := v) hx) (f.toOpenPartialHomeomorph.symm (x, v)).snd
          exact (congrArg (fun z : TotalSpace Unit F ↦ (f z).2) hp).trans
            (congrArg Prod.snd (f.apply_symm_apply' hx))
        map_add' := (hf x hx).map_add
        map_smul' := (hf x hx).map_smul }
    have hpointE (x : X) (hx : x ∈ e.baseSet) (v : Fin r → ℂ) :
        (⟨x, (eLin x hx).symm v⟩ : TotalSpace Unit E) =
          e.toOpenPartialHomeomorph.symm (x, v) :=
      TotalSpace.mk_cast (F := Unit) (E := E) (e.proj_symm_apply' hx) _
    have hpointF (x : X) (hx : x ∈ f.baseSet) (v : Fin s → ℂ) :
        (⟨x, (fLin x hx).symm v⟩ : TotalSpace Unit F) =
          f.toOpenPartialHomeomorph.symm (x, v) :=
      TotalSpace.mk_cast (F := Unit) (E := F) (f.proj_symm_apply' hx) _
    let U : Set X := e.baseSet ∩ f.baseSet
    have hU : IsOpen U := e.open_baseSet.inter f.open_baseSet
    let bp : Module.Basis (Fin r) ℂ (Fin r → ℂ) := Pi.basisFun ℂ (Fin r)
    let bq : Module.Basis (Fin s) ℂ (Fin s → ℂ) := Pi.basisFun ℂ (Fin s)
    let b : Module.Basis (Fin (r * s)) ℂ ((Fin r → ℂ) ⊗[ℂ] (Fin s → ℂ)) :=
      (bp.tensorProduct bq).reindex finProdFinEquiv
    let c (x : X) (hx : x ∈ U) : (E x ⊗[ℂ] F x) ≃ₗ[ℂ] (Fin (r * s) → ℂ) :=
      (TensorProduct.congr (eLin x hx.1) (fLin x hx.2)).trans b.equivFun
    have hpure (x : X) (hx : x ∈ U) (v : E x) (w : F x) (k : Fin (r * s)) :
        c x hx (v ⊗ₜ[ℂ] w) k =
          (e ⟨x, v⟩).2 (finProdFinEquiv.symm k).1 *
            (f ⟨x, w⟩).2 (finProdFinEquiv.symm k).2 := by
      change (b.repr ((eLin x hx.1) v ⊗ₜ[ℂ] (fLin x hx.2) w)) k = _
      rw [Module.Basis.repr_reindex_apply]
      calc
        _ = (fLin x hx.2 w) (finProdFinEquiv.symm k).2 *
            (eLin x hx.1 v) (finProdFinEquiv.symm k).1 :=
          bp.tensorProduct_repr_tmul_apply bq _ _ _ _
        _ = _ := mul_comm _ _
    have hchart (x : X) (hx : x ∈ U) (v : E x ⊗[ℂ] F x) :
        (t ⟨x, v⟩).2 = c x hx v := by
      let L : (E x ⊗[ℂ] F x) →ₗ[ℂ] (Fin (r * s) → ℂ) :=
        { toFun := fun w ↦ (t ⟨x, w⟩).2
          map_add' := (htlinear x (htbase.symm ▸ hx)).map_add
          map_smul' := (htlinear x (htbase.symm ▸ hx)).map_smul }
      have hL : L = (c x hx).toLinearMap := by
        apply TensorProduct.ext'
        intro u w
        funext k
        obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective k
        exact (htpure x hx u w i j).trans (by simpa using (hpure x hx u w
          (finProdFinEquiv (i, j))).symm)
      exact congrArg (fun l : (E x ⊗[ℂ] F x) →ₗ[ℂ] (Fin (r * s) → ℂ) ↦ l v) hL
    let lift (y : X × (Fin (r * s) → ℂ)) : D (r * s) :=
      ⟨y.1,
        (fun k ↦ if hx : y.1 ∈ U then
          (eLin y.1 hx.1).symm (y.2 k • bp (finProdFinEquiv.symm k).1) else 0),
        (fun k ↦ if hx : y.1 ∈ U then
          (fLin y.1 hx.2).symm (bq (finProdFinEquiv.symm k).2) else 0)⟩
    have hlift : ContinuousOn lift (U ×ˢ Set.univ) := by
      let hind : Topology.IsInducing (fun z : D (r * s) ↦ (z.proj,
        (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit E)),
        (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit F)))) := ⟨rfl⟩
      rw [hind.continuousOn_iff]
      refine continuous_fst.continuousOn.prodMk ((continuousOn_pi.mpr ?_).prodMk
        (continuousOn_pi.mpr ?_))
      · intro k
        have harg : Continuous (fun y : X × (Fin (r * s) → ℂ) ↦
            (y.1, y.2 k • bp (finProdFinEquiv.symm k).1)) :=
          continuous_fst.prodMk (((continuous_apply k).comp continuous_snd).smul
            continuous_const)
        refine (e.toOpenPartialHomeomorph.continuousOn_symm.comp harg.continuousOn
          (fun y hy ↦ e.mem_target.mpr hy.1.1)).congr ?_
        intro y hy
        change (⟨y.1, if hx : y.1 ∈ U then _ else 0⟩ : TotalSpace Unit E) = _
        rw [dite_eq_left hy.1]
        exact hpointE y.1 hy.1.1 _
      · intro k
        have harg : Continuous (fun y : X × (Fin (r * s) → ℂ) ↦
            (y.1, bq (finProdFinEquiv.symm k).2)) := continuous_fst.prodMk continuous_const
        refine (f.toOpenPartialHomeomorph.continuousOn_symm.comp harg.continuousOn
          (fun y hy ↦ f.mem_target.mpr hy.1.2)).congr ?_
        intro y hy
        change (⟨y.1, if hx : y.1 ∈ U then _ else 0⟩ : TotalSpace Unit F) = _
        rw [dite_eq_left hy.1]
        exact hpointF y.1 hy.1.2 _
    have hrepresentation (z : T) (hz : z.proj ∈ U) :
        z.snd = ∑ k : Fin (r * s),
          (eLin z.proj hz.1).symm ((t z).2 k • bp (finProdFinEquiv.symm k).1) ⊗ₜ[ℂ]
            (fLin z.proj hz.2).symm (bq (finProdFinEquiv.symm k).2) := by
      calc
        z.snd = (c z.proj hz).symm ((t z).2) := by
          rw [hchart z.proj hz z.snd]
          exact ((c z.proj hz).symm_apply_apply z.snd).symm
        _ = _ := by
          simp only [c, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
            Module.Basis.equivFun_symm_apply, map_sum, map_smul]
          apply Finset.sum_congr rfl
          intro k _
          simp only [b, Module.Basis.reindex_apply, Module.Basis.tensorProduct_apply',
            TensorProduct.congr_symm, TensorProduct.congr_tmul, TensorProduct.smul_tmul']
    -- Near p₀, lift only the source tensor. The target generator supplies continuity.
    have hp₀ : p₀.2.proj ∈ U := ⟨he₀, hf₀⟩
    have ht₀ : p₀.2 ∈ t.source := t.mem_source.mpr (htbase.symm ▸ hp₀)
    have harg : ContinuousAt (fun p : G × T ↦ (p.2.proj, (t p.2).2)) p₀ :=
      (hbase.comp continuous_snd).continuousAt.prodMk
        ((t.toOpenPartialHomeomorph.continuousAt ht₀).comp continuousAt_snd).snd
    have hliftAt := hlift.continuousAt
      ((hU.prod isOpen_univ).mem_nhds (show (p₀.2.proj, (t p₀.2).2) ∈ U ×ˢ Set.univ from
        ⟨hp₀, Set.mem_univ _⟩))
    have hinput : ContinuousAt (fun p : G × T ↦
        (p.1, lift (p.2.proj, (t p.2).2))) p₀ :=
      continuousAt_fst.prodMk (hliftAt.comp
        (f := fun p : G × T ↦ (p.2.proj, (t p.2).2)) harg)
    have hlocal := ((hgenerator (r * s)).comp (hmoved (r * s))).continuousAt.comp hinput
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [(hU.preimage (hbase.comp continuous_snd)).mem_nhds hp₀] with p hp
    change p.2.proj ∈ U at hp
    change (⟨p.1 • p.2.proj,
      TensorProduct.map (σ.linearMap p.1 p.2.proj) (τ.linearMap p.1 p.2.proj) p.2.snd⟩ : T) = _
    apply congrArg (TotalSpace.mk (p.1 • p.2.proj))
    change TensorProduct.map _ _ p.2.snd = ∑ k : Fin (r * s),
      σ.linearMap p.1 p.2.proj
        (if hx : p.2.proj ∈ U then (eLin p.2.proj hx.1).symm
          ((t p.2).2 k • bp (finProdFinEquiv.symm k).1) else 0) ⊗ₜ[ℂ]
      τ.linearMap p.1 p.2.proj
        (if hx : p.2.proj ∈ U then (fLin p.2.proj hx.2).symm
          (bq (finProdFinEquiv.symm k).2) else 0)
    rw [hrepresentation p.2 hp, map_sum]
    simp only [dite_eq_left hp, TensorProduct.map_tmul]

/-- The original moving tensor action with its original tensor-bundle total topology. -/
def EquivariantStructure.tensor [IsFiniteRank E] [IsFiniteRank F]
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) :
    EquivariantStructure G (fun x ↦ E x ⊗[ℂ] F x) where
  linearMap g x := TensorProduct.map (σ.linearMap g x) (τ.linearMap g x)
  one_map := (σ.tensor_properties τ).1
  mul_map := (σ.tensor_properties τ).2.1
  continuous_action := (σ.tensor_properties τ).2.2

variable {E' : X → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module ℂ (E' x)]
  [TopologicalSpace (TotalSpace Unit E')]
  {F' : X → Type*} [∀ x, AddCommGroup (F' x)] [∀ x, Module ℂ (F' x)]
  [TopologicalSpace (TotalSpace Unit F')]

/-- The existing tensor bundle maps and isomorphisms intertwine the same original tensor actions. -/
theorem EquivariantStructure.tensor_maps
    [IsFiniteRank E] [IsFiniteRank F] [IsFiniteRank E'] [IsFiniteRank F']
    (σE : EquivariantStructure G E) (σF : EquivariantStructure G F)
    (τE : EquivariantStructure G E') (τF : EquivariantStructure G F') :
    (∀ (a : Hom E E') (b : Hom F F'),
      a.IsEquivariant σE τE → b.IsEquivariant σF τF →
        (a.tensor b).IsEquivariant (σE.tensor σF) (τE.tensor τF)) ∧
    (∀ (a : Iso E E') (b : Iso F F'),
      a.IsEquivariant σE τE → b.IsEquivariant σF τF →
        (a.tensor b).IsEquivariant (σE.tensor σF) (τE.tensor τF)) := by
  /- Stage 1: on an original pure tensor, the Hom.tensor intertwining equation
  is the tensor of the two supplied original intertwining equations. Both
  routes use the same group element, source point and moved target point.
  TensorProduct.map is linear and pure tensors span, so the equation holds
  on all vectors. Hom.tensor already carries continuity for the original
  tensor topologies; no alternative continuous map is chosen.
  Stage 2: apply the same argument to the original forward maps of the two
  bundle isomorphisms. Iso.tensor uses exactly their TensorProduct.congr on
  each fiber, whose forward map is the preceding TensorProduct.map. Its
  existing inverse and continuity data are retained. Finite rank supplies
  the tensor actions above; no further compactness or rank equality is used. -/
  -- First prove the fiber equation for the actual Hom.tensor maps.
  have hhom (a : Hom E E') (b : Hom F F')
      (ha : a.IsEquivariant σE τE) (hb : b.IsEquivariant σF τF) :
      (a.tensor b).IsEquivariant (σE.tensor σF) (τE.tensor τF) := by
    intro g x v
    change TensorProduct.map (a.linearMap (g • x)) (b.linearMap (g • x))
      (TensorProduct.map (σE.linearMap g x) (σF.linearMap g x) v) =
        TensorProduct.map (τE.linearMap g x) (τF.linearMap g x)
          (TensorProduct.map (a.linearMap x) (b.linearMap x) v)
    rw [TensorProduct.map_map, TensorProduct.map_map]
    have hE : (a.linearMap (g • x)).comp (σE.linearMap g x) =
        (τE.linearMap g x).comp (a.linearMap x) := LinearMap.ext (ha g x)
    have hF : (b.linearMap (g • x)).comp (σF.linearMap g x) =
        (τF.linearMap g x).comp (b.linearMap x) := LinearMap.ext (hb g x)
    rw [hE, hF]
  refine ⟨hhom, ?_⟩
  -- The given tensor isomorphism has precisely the tensor of these forward maps.
  intro a b ha hb
  exact hhom a.toHom b.toHom ha hb

end AtiyahSinger.ComplexBundle
