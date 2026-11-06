/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleSum

/-!
# Finite trivial complex bundles and their section modules

Public module ID: M1602.

D07/K01. The total-space topology is the product topology transported to
Bundle.TotalSpace Unit. The section equivalence uses actual coordinate functions,
not an unspecified free-module isomorphism. No compactness is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]

/-- Product topology on the finite trivial complex bundle. -/
@[instance_reducible]
def trivialTopology (n : ℕ) :
    TopologicalSpace (TotalSpace Unit (Bundle.Trivial X (Fin n → ℂ))) :=
  TopologicalSpace.induced
    (fun z : TotalSpace Unit (Bundle.Trivial X (Fin n → ℂ)) ↦ (z.proj, z.snd))
    inferInstance

attribute [local instance] trivialTopology

/-- The standard finite trivial bundle is locally linearly trivial. -/
theorem isFiniteRank_trivial (n : ℕ) : IsFiniteRank (Bundle.Trivial X (Fin n → ℂ)) := by
  /- Use the global product chart and its evident inverse, transporting only the
  phantom total-space parameter. Its fiber coordinate is identity and its open base
  set is all of X, including the zero-dimensional case. -/
  -- Use the global product chart in the original induced total-space topology.
  let t : Trivialization (Fin n → ℂ) (π Unit (Bundle.Trivial X (Fin n → ℂ))) :=
    { toFun := fun z ↦ (z.proj, z.snd)
      invFun := fun p ↦ ⟨p.1, p.2⟩
      source := Set.univ
      target := Set.univ
      baseSet := Set.univ
      map_source' := fun _ _ ↦ Set.mem_univ _
      map_target' := fun _ _ ↦ Set.mem_univ _
      left_inv' := fun _ _ ↦ rfl
      right_inv' := fun _ _ ↦ rfl
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
      proj_toFun := fun _ _ ↦ rfl }
  constructor
  intro x
  refine ⟨n, t, Set.mem_univ x, ?_⟩
  intro y hy
  exact ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

attribute [local instance] isFiniteRank_trivial sectionModule

/-- A continuous trivial-bundle section has continuous scalar coordinates. -/
theorem continuous_trivial_coordinate (n : ℕ)
    (s : continuousSections (Bundle.Trivial X (Fin n → ℂ))) (i : Fin n) :
    Continuous (fun x ↦ s.val x i) := by
  /- Compose the continuous section with the inducing product map, then the fiber
  projection and coordinate evaluation at i. Each map is continuous for the product topology. -/
  have hp : Continuous (fun z : TotalSpace Unit (Bundle.Trivial X (Fin n → ℂ)) ↦
      (z.proj, z.snd)) := continuous_induced_dom
  exact (continuous_apply i).comp (continuous_snd.comp (hp.comp s.property))

/-- A finite tuple of continuous scalar functions determines a continuous section. -/
theorem continuous_trivial_section (n : ℕ) (v : Fin n → C(X, ℂ)) :
    Continuous (fun x ↦ (⟨x, fun i ↦ v i x⟩ :
      TotalSpace Unit (Bundle.Trivial X (Fin n → ℂ)))) := by
  /- The base component is identity, and each fiber coordinate is one of the
  continuous functions v(i). Product continuity gives the section in the induced topology. -/
  apply continuous_induced_rng.mpr
  exact continuous_id.prodMk (continuous_pi (fun i ↦ (v i).continuous))

/-- The coordinate map from actual sections to the finite free function module. -/
def trivialSectionCoordinates (n : ℕ) :
    continuousSections (Bundle.Trivial X (Fin n → ℂ)) →ₗ[C(X, ℂ)] (Fin n → C(X, ℂ)) where
  toFun s i := ⟨fun x ↦ s.val x i, continuous_trivial_coordinate n s i⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inverse coordinate construction on actual continuous sections. -/
def trivialSectionMap (n : ℕ) : (Fin n → C(X, ℂ)) →ₗ[C(X, ℂ)]
    continuousSections (Bundle.Trivial X (Fin n → ℂ)) where
  toFun v := ⟨fun x i ↦ v i x, continuous_trivial_section n v⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Coordinates of the reconstructed section are the original functions. -/
theorem trivialSectionCoordinates_comp_map (n : ℕ) :
    (trivialSectionCoordinates (X := X) n).comp (trivialSectionMap n) = LinearMap.id := by
  /- Evaluate the two module maps on a vector of functions, then at a coordinate
  and base point. Both sides yield the original scalar value v(i)(x). Extensionality concludes. -/
  apply LinearMap.ext
  intro v
  funext i
  apply ContinuousMap.ext
  intro x
  rfl

/-- Reconstructing the coordinates of a section recovers that section. -/
theorem trivialSectionMap_comp_coordinates (n : ℕ) :
    (trivialSectionMap (X := X) n).comp (trivialSectionCoordinates n) = LinearMap.id := by
  /- Evaluate on a section, then a base point and a coordinate. The reconstructed
  fiber vector has exactly the original coordinate values, so the section is unchanged. -/
  apply LinearMap.ext
  intro s
  apply Subtype.ext
  funext x i
  rfl

/-- The coordinate section map is bijective. -/
theorem trivialSectionMap_bijective (n : ℕ) :
    Function.Bijective (trivialSectionMap (X := X) n) := by
  /- The coordinate map is a two-sided inverse by the two componentwise identities.
  This proves bijectivity over any topological base and does not invoke Serre-Swan. -/
  -- The coordinate construction and coordinate extraction are inverses as actual maps.
  have hleft : Function.LeftInverse (trivialSectionCoordinates (X := X) n)
      (trivialSectionMap n) := fun v ↦
    DFunLike.congr_fun (trivialSectionCoordinates_comp_map n) v
  have hright : Function.RightInverse (trivialSectionCoordinates (X := X) n)
      (trivialSectionMap n) := fun s ↦
    DFunLike.congr_fun (trivialSectionMap_comp_coordinates n) s
  exact ⟨hleft.injective, hright.surjective⟩

/-- The specified free-module equivalence for sections of a trivial bundle. -/
def trivialSectionEquiv (n : ℕ) : (Fin n → C(X, ℂ)) ≃ₗ[C(X, ℂ)]
    continuousSections (Bundle.Trivial X (Fin n → ℂ)) :=
  LinearEquiv.ofBijective (trivialSectionMap n) (trivialSectionMap_bijective n)

/-- The free-module equivalence evaluates by the original scalar functions. -/
theorem trivialSectionEquiv_apply (n : ℕ) (v : Fin n → C(X, ℂ)) (x : X) (i : Fin n) :
    (trivialSectionEquiv n v).val x i = v i x := by
  /- Its forward map is the explicit coordinate construction. Evaluating its
  underlying section at x and then i returns exactly the value used in that construction. -/
  rfl

set_option linter.unusedSectionVars false in
/-- The trivial fiber dimension is the specified natural number. -/
theorem finrank_trivial (n : ℕ) (x : X) :
    Module.finrank ℂ (Bundle.Trivial X (Fin n → ℂ) x) = n := by
  /- The fiber is the finite function space from Fin n to ℂ. Its coordinate basis
  has n elements, giving the dimension also for n=0 and independently of the base topology. -/
  exact Module.finrank_fin_fun ℂ

variable {Y : Type*} [TopologicalSpace Y]

/-- Pullback of a trivial bundle admits the canonical vector-preserving isomorphism. -/
theorem exists_pullback_trivial_iso (f : C(X, Y)) (n : ℕ) :
    ∃ e : Iso ((f : X → Y) *ᵖ (Bundle.Trivial Y (Fin n → ℂ)))
      (Bundle.Trivial X (Fin n → ℂ)), ∀ x v, e.linearEquiv x v = v := by
  /- The two fiber families have the same coordinate vectors. The pullback topology
  is the product topology: its additional Y component is f of the X component.
  Thus the identity on vectors is continuous in both directions. -/
  -- Identity on the coordinate vectors compares the two prescribed total topologies.
  let e : Iso ((f : X → Y) *ᵖ (Bundle.Trivial Y (Fin n → ℂ)))
      (Bundle.Trivial X (Fin n → ℂ)) :=
    { linearEquiv := fun _ ↦ LinearEquiv.refl ℂ (Fin n → ℂ)
      continuous_total := by
        apply continuous_induced_rng.mpr
        have hcoords : Continuous (fun z : TotalSpace Unit (Bundle.Trivial Y (Fin n → ℂ)) ↦
            z.snd) := by
          have hp : Continuous (fun z : TotalSpace Unit (Bundle.Trivial Y (Fin n → ℂ)) ↦
              (z.proj, z.snd)) := continuous_induced_dom
          exact continuous_snd.comp hp
        exact (Pullback.continuous_proj Unit (Bundle.Trivial Y (Fin n → ℂ)) f).prodMk
          (hcoords.comp (Pullback.continuous_lift Unit (Bundle.Trivial Y (Fin n → ℂ)) f))
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit
          (Bundle.Trivial Y (Fin n → ℂ)) f).continuous_iff]
        have hp : Continuous (fun z : TotalSpace Unit (Bundle.Trivial X (Fin n → ℂ)) ↦
            (z.proj, z.snd)) := continuous_induced_dom
        apply (continuous_fst.comp hp).prodMk
        apply continuous_induced_rng.mpr
        exact (f.continuous.comp (continuous_fst.comp hp)).prodMk (continuous_snd.comp hp) }
  exact ⟨e, fun _ _ ↦ rfl⟩

/-- Canonical trivialization of the pullback of a finite trivial bundle. -/
def pullbackTrivialIso (f : C(X, Y)) (n : ℕ) :
    Iso ((f : X → Y) *ᵖ (Bundle.Trivial Y (Fin n → ℂ))) (Bundle.Trivial X (Fin n → ℂ)) :=
  (exists_pullback_trivial_iso f n).choose

/-- The canonical pullback trivialization keeps the original coordinate vector. -/
theorem pullbackTrivialIso_apply (f : C(X, Y)) (n : ℕ) (x : X) (v : Fin n → ℂ) :
    (pullbackTrivialIso f n).linearEquiv x v = v := by
  /- Use the vector-preserving characterization in the existence theorem underlying
  the choice. This fixes the map and excludes an arbitrary change of frame. -/
  exact (exists_pullback_trivial_iso f n).choose_spec x v

end AtiyahSinger.ComplexBundle
