import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Separation.Basic

/-!
# Topology and properness on the same original glued source

The local source opens are the LITERAL saturated subspaces `p ⁻¹' U i`.
Actual local-model homeomorphisms transport native properties; no new
gluing/category record, global source topology certificate or transition
data are introduced. Blueprint: `embedded-blowup-topology.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Topology

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupTopology

variable {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Equal images lie in the SAME Hausdorff saturated model; unequal images
are separated in the original Hausdorff target. -/
theorem t2Space_of_saturated_cover [T2Space X]
    (p : Y → X) (hp : Continuous p) (U : ι → Opens X) (hU : IsOpenCover U)
    (hlocal : ∀ i, T2Space (p ⁻¹' (U i : Set X))) : T2Space Y := by
  constructor
  intro y z hyz
  by_cases h : p y = p z
  · obtain ⟨i, hi⟩ := hU.exists_mem (p y)
    have hz : p z ∈ U i := h ▸ hi
    let := hlocal i
    let y' : p ⁻¹' (U i : Set X) := ⟨y, hi⟩
    let z' : p ⁻¹' (U i : Set X) := ⟨z, hz⟩
    have hne : y' ≠ z' := fun he => hyz (congrArg Subtype.val he)
    exact separated_by_isOpenEmbedding
      ((U i).isOpen.preimage hp).isOpenEmbedding_subtypeVal hne
  · exact separated_by_continuous hp h

/-- Actual compact neighborhoods pass through the same saturated open
inclusion to compact neighborhoods in the original source. -/
theorem locallyCompactSpace_of_saturated_cover
    (p : Y → X) (hp : Continuous p) (U : ι → Opens X) (hU : IsOpenCover U)
    (hlocal : ∀ i, LocallyCompactSpace (p ⁻¹' (U i : Set X))) : LocallyCompactSpace Y := by
  constructor
  intro y N hN
  obtain ⟨i, hi⟩ := hU.exists_mem (p y)
  let := hlocal i
  let y' : p ⁻¹' (U i : Set X) := ⟨y, hi⟩
  have hN' : (Subtype.val : p ⁻¹' (U i : Set X) → Y) ⁻¹' N ∈ 𝓝 y' :=
    continuous_subtype_val.continuousAt hN
  obtain ⟨K, hKnhds, hKN, hKcompact⟩ := local_compact_nhds hN'
  refine ⟨Subtype.val '' K,
    ((U i).isOpen.preimage hp).isOpenEmbedding_subtypeVal.isOpenMap.image_mem_nhds hKnhds,
    ?_, hKcompact.image continuous_subtype_val⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hKN hz

/-- Native target-cover locality of closed maps plus actual compact fibres
gives properness of the SAME original projection. No source separation or
compactness assumption is used. -/
theorem isProperMap_of_saturated_cover
    (p : Y → X) (hp : Continuous p) (U : ι → Opens X) (hU : IsOpenCover U)
    (hlocal : ∀ i, IsProperMap ((U i : Set X).restrictPreimage p)) : IsProperMap p := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨hp, (hU.isClosedMap_iff_restrictPreimage).mpr (fun i => (hlocal i).isClosedMap), ?_⟩
  intro x
  obtain ⟨i, hi⟩ := hU.exists_mem x
  have hcompact := (hlocal i).isCompact_preimage
    (K := {(⟨x, hi⟩ : U i)}) isCompact_singleton
  have himage : (Subtype.val : p ⁻¹' (U i : Set X) → Y) ''
      ((U i : Set X).restrictPreimage p ⁻¹' {(⟨x, hi⟩ : U i)}) = p ⁻¹' {x} := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (Set.mem_singleton_iff.mp hz)
    · intro hy
      have hpy : p y = x := hy
      have hyU : p y ∈ U i := by rw [hpy]; exact hi
      refine ⟨⟨y, hyU⟩, ?_, rfl⟩
      apply Subtype.ext
      exact hpy
  rw [← himage]
  exact hcompact.image continuous_subtype_val

/-- Actual local homeomorphisms and actual local proper projections provide
all global topology/properness conclusions, not incoming certificates. -/
theorem topology_of_local_models [T2Space X]
    (p : Y → X) (hp : Continuous p) (U : ι → Opens X) (hU : IsOpenCover U)
    (Z : ι → Type*) [∀ i, TopologicalSpace (Z i)]
    (e : ∀ i, (p ⁻¹' (U i : Set X)) ≃ₜ Z i)
    (q : ∀ i, Z i → U i)
    (hcomm : ∀ i, q i ∘ e i = (U i : Set X).restrictPreimage p)
    (hproper : ∀ i, IsProperMap (q i))
    (hHaus : ∀ i, T2Space (Z i)) (hLC : ∀ i, LocallyCompactSpace (Z i)) :
    T2Space Y ∧ LocallyCompactSpace Y ∧ IsProperMap p := by
  have hHaus' : ∀ i, T2Space (p ⁻¹' (U i : Set X)) := by
    intro i
    let := hHaus i
    exact (e i).symm.t2Space
  have hLC' : ∀ i, LocallyCompactSpace (p ⁻¹' (U i : Set X)) :=
    fun i => (e i).locallyCompactSpace_iff.mpr (hLC i)
  have hproper' : ∀ i, IsProperMap ((U i : Set X).restrictPreimage p) := by
    intro i
    rw [← hcomm i]
    exact (hproper i).comp (e i).isProperMap
  exact ⟨t2Space_of_saturated_cover p hp U hU hHaus',
    locallyCompactSpace_of_saturated_cover p hp U hU hLC',
    isProperMap_of_saturated_cover p hp U hU hproper'⟩

/-- Compactness is DERIVED from the ordinary compact original base and
actual local proper maps, without any global source certificate. -/
theorem compactSpace_of_local_models [T2Space X] [CompactSpace X]
    (p : Y → X) (hp : Continuous p) (U : ι → Opens X) (hU : IsOpenCover U)
    (Z : ι → Type*) [∀ i, TopologicalSpace (Z i)]
    (e : ∀ i, (p ⁻¹' (U i : Set X)) ≃ₜ Z i)
    (q : ∀ i, Z i → U i)
    (hcomm : ∀ i, q i ∘ e i = (U i : Set X).restrictPreimage p)
    (hproper : ∀ i, IsProperMap (q i))
    (hHaus : ∀ i, T2Space (Z i)) (hLC : ∀ i, LocallyCompactSpace (Z i)) :
    CompactSpace Y := by
  have hglobal := (topology_of_local_models p hp U hU Z e q hcomm hproper hHaus hLC).2.2
  constructor
  simpa only [preimage_univ] using hglobal.isCompact_preimage (K := univ) isCompact_univ

end Hironaka.Analytic.Unibranch.EmbeddedBlowupTopology
