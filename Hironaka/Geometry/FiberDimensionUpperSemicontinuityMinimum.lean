import Hironaka.Geometry.FiberDimensionUpperSemicontinuityComponents
import Hironaka.Geometry.FiberDimensionGenericGlobal

/-!
# Actual generic minima and constant opens for a Noetherian proper source

The original reduced component family computes every actual fiber. Native
proper surjectivity and the full componentwise lower bound produce the
generic minimum; generic constancy on the actual dominant components
produces a common original target open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.FiberDimensionUpperSemicontinuityMinimum

open FiberDimension FiberDimensionUpperSemicontinuityComponents

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}}

/-- An actual empty fiber has the native bottom dimension. -/
theorem fiberDimension_eq_bot_of_not_mem_range (f : X ⟶ S) (s : S)
    (hs : s ∉ Set.range f) : fiberDimension f s = ⊥ := by
  have hnot : ¬ (0 : WithBot ℕ∞) ≤ fiberDimension f s :=
    fun h ↦ hs ((fiberDimension_nonneg_iff_mem_range f s).mp h)
  exact WithBot.lt_coe_bot.mp (lt_of_not_ge hnot)

/-- Nondominant original morphisms into an integral base have empty actual generic fibers. -/
theorem genericFiberDimension_eq_bot_of_not_dominant [IsIntegral S]
    (f : X ⟶ S) (hf : ¬ IsDominant f) : fiberDimension f (genericPoint S) = ⊥ := by
  apply fiberDimension_eq_bot_of_not_mem_range
  intro hη
  apply hf
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec S).def]
  exact closure_mono (Set.singleton_subset_iff.mpr hη)

/-- Proper integral source components have their actual generic dimension as a global minimum. -/
theorem genericFiberDimension_le_of_integral_source [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [UniversallyClosed f] (s : S) :
    fiberDimension f (genericPoint S) ≤ fiberDimension f s := by
  by_cases hf : IsDominant f
  · let : IsDominant f := hf
    obtain ⟨x, hx⟩ := f.surjective s
    let z : f.fiber s := (f.fiberHomeo s).symm ⟨x, hx⟩
    exact (FiberDimensionComponentLowerBound.everyFiberComponentDimensionGEGeneric f s
      (irreducibleComponent z) (irreducibleComponent_mem_irreducibleComponents z)).trans
        (topologicalKrullDim_subspace_le _ _)
  · rw [genericFiberDimension_eq_bot_of_not_dominant f hf]
    exact bot_le

/-- The actual original generic fiber is a minimum for any Noetherian source,
without reducedness or an integral-source certificate. -/
theorem genericFiberDimension_le_fiberDimension [NoetherianSpace X] [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFiniteType f] [UniversallyClosed f] (s : S) :
    fiberDimension f (genericPoint S) ≤ fiberDimension f s := by
  rw [fiberDimension_eq_iSup_componentFiberDimension f (genericPoint S),
    fiberDimension_eq_iSup_componentFiberDimension f s]
  apply iSup_le
  intro Z
  exact (genericFiberDimension_le_of_integral_source (componentInclusion X Z ≫ f) s).trans
    (le_iSup (fun Z : irreducibleComponents X ↦ fiberDimension (componentInclusion X Z ≫ f) s) Z)

/-- An original proper component has a nonempty target open of its actual generic dimension,
including the internally detected nondominant case. -/
theorem exists_nonempty_constant_genericFiberDimension_of_integral_source
    [IsIntegral X] [IsIntegral S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [UniversallyClosed f] :
    ∃ U : S.Opens, Nonempty U ∧ ∀ s : U,
      fiberDimension f s.val = fiberDimension f (genericPoint S) := by
  by_cases hf : IsDominant f
  · let : IsDominant f := hf
    obtain ⟨U, hU, -, hdim⟩ :=
      FiberDimensionGenericGlobal.exists_nonempty_dense_fiberDimension_eq_generic f
    exact ⟨U, hU, hdim⟩
  · let U : S.Opens := ⟨(Set.range f)ᶜ, f.isClosedMap.isClosed_range.isOpen_compl⟩
    have hη : genericPoint S ∈ U := by
      intro hη
      apply hf
      refine ⟨?_⟩
      rw [denseRange_iff_closure_range]
      apply Set.Subset.antisymm (Set.subset_univ _)
      rw [← (genericPoint_spec S).def]
      exact closure_mono (Set.singleton_subset_iff.mpr hη)
    refine ⟨U, ⟨⟨_, hη⟩⟩, fun s ↦ ?_⟩
    rw [fiberDimension_eq_bot_of_not_mem_range f s.val s.property,
      genericFiberDimension_eq_bot_of_not_dominant f hf]

/-- Actual Noetherian source components internally give a common open of constant
original generic dimension, with no source-integrality or presentation premise. -/
theorem exists_nonempty_constant_genericFiberDimension
    [NoetherianSpace X] [IsIntegral S] (f : X ⟶ S)
    [LocallyOfFiniteType f] [UniversallyClosed f] :
    ∃ U : S.Opens, Nonempty U ∧ ∀ s : U,
      fiberDimension f s.val = fiberDimension f (genericPoint S) := by
  classical
  let : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  have hlocal (Z : irreducibleComponents X) :=
    exists_nonempty_constant_genericFiberDimension_of_integral_source (componentInclusion X Z ≫ f)
  choose U hU hdim using hlocal
  let V : S.Opens := ⨅ Z, U Z
  have hη : genericPoint S ∈ V := by
    change genericPoint S ∈ ((⨅ Z, U Z : S.Opens) : Set S)
    rw [Opens.coe_iInf, Set.mem_iInter]
    intro Z
    exact ((genericPoint_spec S).mem_open_set_iff (U Z).isOpen).mpr (by simpa using hU Z)
  refine ⟨V, ⟨⟨_, hη⟩⟩, fun s ↦ ?_⟩
  rw [fiberDimension_eq_iSup_componentFiberDimension f s.val,
    fiberDimension_eq_iSup_componentFiberDimension f (genericPoint S)]
  apply iSup_congr
  intro Z
  exact hdim Z ⟨s.val, (iInf_le U Z) s.property⟩

end Hironaka.Geometry.FiberDimensionUpperSemicontinuityMinimum
