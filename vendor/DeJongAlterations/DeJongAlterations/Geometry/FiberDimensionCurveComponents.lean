import DeJongAlterations.Geometry.FiberDimensionOne
import DeJongAlterations.Geometry.GenericFiberIntegral

/-!
# The actual componentwise generic lower bound in relative dimension one

Positive generic fiber dimension rules out every native quasi-finite point.
A zero-dimensional actual fiber component would be an isolated singleton,
producing such a point. This proves the componentwise generic lower bound
when the actual generic fiber dimension is one, retaining every component
of every fiber. It does not assert the arbitrary-dimensional lower bound.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FiberDimensionCurveComponents

open FiberDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An irreducible zero-dimensional `T₀` space has at most one point. -/
theorem subsingleton_of_irreducible_dimension_le_zero (T : Type u)
    [TopologicalSpace T] [T0Space T] [IrreducibleSpace T]
    (hdim : topologicalKrullDim T ≤ 0) : Subsingleton T := by
  let C (x : T) : IrreducibleCloseds T :=
    ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
  let whole : IrreducibleCloseds T :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ T, isClosed_univ⟩
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hdim
  have hclosure (x : T) : closure ({x} : Set T) = Set.univ := by
    have hle : whole ≤ C x := hmax (C x) (show C x ≤ whole from Set.subset_univ _)
    exact Set.Subset.antisymm (Set.subset_univ _) hle
  refine ⟨fun x y => ?_⟩
  have hxy : x ⤳ y := specializes_iff_mem_closure.mpr (hclosure x ▸ Set.mem_univ y)
  have hyx : y ⤳ x := specializes_iff_mem_closure.mpr (hclosure y ▸ Set.mem_univ x)
  exact (hxy.antisymm hyx).eq

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The original source generic point is generic in its actual scheme-theoretic fiber. -/
theorem isGenericPoint_asFiber_genericPoint [IsIntegral X] :
    IsGenericPoint (f.asFiber (genericPoint X))
      (Set.univ : Set (f.fiber (f (genericPoint X)))) := by
  rw [isGenericPoint_iff_specializes]
  intro x
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  apply (f.fiberι (f (genericPoint X))).isEmbedding.isInducing.specializes_iff.mp
  rw [f.fiberι_asFiber]
  exact (genericPoint_spec X).specializes (Set.mem_univ _)

/-- Native quasi-finiteness at the source generic point forces its actual fiber to have dimension zero. -/
theorem fiberDimension_le_zero_of_quasiFiniteAt_genericPoint
    [IsIntegral X] [LocallyOfFiniteType f]
    (hq : f.QuasiFiniteAt (genericPoint X)) :
    fiberDimension f (f (genericPoint X)) ≤ 0 := by
  have hc := hq.isClopen_singleton_asFiber.isClosed
  have hall : (Set.univ : Set (f.fiber (f (genericPoint X)))) ⊆
      {f.asFiber (genericPoint X)} :=
    ((isGenericPoint_asFiber_genericPoint f).mem_closed_set_iff hc).mp (by simp)
  let : Subsingleton (f.fiber (f (genericPoint X))) := ⟨fun x y => by
    have hx := Set.mem_singleton_iff.mp (hall (Set.mem_univ x))
    have hy := Set.mem_singleton_iff.mp (hall (Set.mem_univ y))
    exact hx.trans hy.symm⟩
  exact topologicalKrullDim_zero_of_discreteTopology _

/-- Positive actual generic fiber dimension rules out all original quasi-finite points. -/
theorem not_quasiFiniteAt_of_one_le_genericFiberDimension
    [IsIntegral X] [IsIntegral S] [LocallyOfFiniteType f] [IsDominant f]
    (hgen : (1 : WithBot ℕ∞) ≤ fiberDimension f (genericPoint S)) (x : X) :
    ¬ f.QuasiFiniteAt x := by
  intro hx
  have hη : f.QuasiFiniteAt (genericPoint X) :=
    ((genericPoint_spec X).mem_open_set_iff f.quasiFiniteLocus.isOpen).mpr
      ⟨x, Set.mem_univ _, hx⟩
  have hzero := fiberDimension_le_zero_of_quasiFiniteAt_genericPoint f hη
  rw [genericPoint_map_of_isDominant f] at hzero
  have hbad : (1 : WithBot ℕ∞) ≤ 0 := hgen.trans hzero
  norm_num at hbad

/-- The actual native quasi-finite locus is empty in positive generic relative dimension. -/
theorem quasiFiniteLocus_eq_bot_of_one_le_genericFiberDimension
    [IsIntegral X] [IsIntegral S] [LocallyOfFiniteType f] [IsDominant f]
    (hgen : (1 : WithBot ℕ∞) ≤ fiberDimension f (genericPoint S)) :
    f.quasiFiniteLocus = ⊥ := by
  ext x
  change f.QuasiFiniteAt x ↔ False
  exact iff_false_intro (not_quasiFiniteAt_of_one_le_genericFiberDimension f hgen x)

/-- An actual isolated fiber point gives quasi-finiteness of the original morphism. -/
theorem quasiFiniteAt_of_isOpen_singleton_fiber [LocallyOfFiniteType f]
    (s : S) (z : f.fiber s) (hz : IsOpen ({z} : Set (f.fiber s))) :
    f.QuasiFiniteAt (f.fiberι s z) := by
  have htop : ∀ (x : X) (hx : f x = s),
      IsOpen ({⟨x, hx⟩} : Set (f ⁻¹' {s})) → f.QuasiFiniteAt x := by
    intro x hx ho
    subst s
    apply Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
    simpa only [Set.image_singleton, Scheme.Hom.asFiber] using
      (f.fiberHomeo (f x)).symm.isOpenMap _ ho
  apply htop (f.fiberHomeo s z).val (f.fiberHomeo s z).property
  simpa only [Set.image_singleton] using (f.fiberHomeo s).isOpenMap _ hz

/-- A zero-dimensional actual fiber component internally yields an original quasi-finite point. -/
theorem exists_quasiFiniteAt_of_fiberComponent_dimension_le_zero
    [LocallyOfFiniteType f] [QuasiCompact f] (s : S) (Z : Set (f.fiber s))
    (hZ : Z ∈ irreducibleComponents (f.fiber s))
    (hdim : topologicalKrullDim Z ≤ 0) :
    ∃ z : f.fiber s, z ∈ Z ∧ f.QuasiFiniteAt (f.fiberι s z) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  have : IsNoetherian (f.fiber s) := ⟨⟩
  have : IrreducibleSpace Z := Subtype.irreducibleSpace hZ.1
  have : Subsingleton Z := subsingleton_of_irreducible_dimension_le_zero Z hdim
  obtain ⟨o, ho, ⟨z, hzo⟩, hoZ⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  have heq : o = {z} := by
    apply Set.Subset.antisymm
    · intro w hw
      exact Set.mem_singleton_iff.mpr
        (congrArg Subtype.val (Subsingleton.elim (⟨w, hoZ hw⟩ : Z) ⟨z, hoZ hzo⟩))
    · rintro w rfl
      exact hzo
  exact ⟨z, hoZ hzo, quasiFiniteAt_of_isOpen_singleton_fiber f s z (heq ▸ ho)⟩

/-- Every actual fiber component is positive dimensional when the actual generic fiber is. -/
theorem one_le_fiberComponentDimension_of_one_le_genericFiberDimension
    [IsIntegral X] [IsIntegral S] [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f]
    (hgen : (1 : WithBot ℕ∞) ≤ fiberDimension f (genericPoint S))
    (s : S) (Z : Set (f.fiber s)) (hZ : Z ∈ irreducibleComponents (f.fiber s)) :
    (1 : WithBot ℕ∞) ≤ topologicalKrullDim Z := by
  by_contra hnot
  have hdim : topologicalKrullDim Z ≤ 0 := by
    have hthreshold : (1 : WithBot ℕ∞) ≤ topologicalKrullDim Z ↔
        ¬ topologicalKrullDim Z ≤ 0 := by
      simpa only [Nat.cast_zero, zero_add, lt_iff_not_ge] using
        (ENat.WithBot.add_one_le_iff (n := 0) (m := topologicalKrullDim Z))
    exact Classical.not_not.mp (fun h => hnot (hthreshold.mpr h))
  obtain ⟨z, hz, hq⟩ := exists_quasiFiniteAt_of_fiberComponent_dimension_le_zero f s Z hZ hdim
  exact not_quasiFiniteAt_of_one_le_genericFiberDimension f hgen _ hq

/-- Source 2.7(c), retaining every component of every actual fiber, in relative dimension one. -/
theorem everyFiberComponentDimensionGEGeneric_of_genericFiberDimension_eq_one
    [IsIntegral X] [IsIntegral S] [LocallyOfFiniteType f] [QuasiCompact f] [IsDominant f]
    (hgen : fiberDimension f (genericPoint S) = 1) :
    EveryFiberComponentDimensionGEGeneric f := by
  intro s Z hZ
  rw [hgen]
  exact one_le_fiberComponentDimension_of_one_le_genericFiberDimension f hgen.ge s Z hZ

end DeJongAlterations.Geometry.FiberDimensionCurveComponents
