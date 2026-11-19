import Hironaka.Resolution.HironakaG34ChartTorusLemma
import Hironaka.Resolution.HironakaDimensionThreeStepOneCurveEnvelope
import Hironaka.Resolution.HironakaActualReferenceHSSingularCentre
import Hironaka.Resolution.HironakaNormalCrossingsLocalBranches

/-! Original two-axis analytic geometry and the actual HS drop on a boundary branch. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold

namespace Hironaka.HironakaG1NativeCrossingGeometry
noncomputable section

open NormalCrossings HironakaG34ChartTorusLemma HironakaG8BFamilyEmptyMember
  HironakaNormalCrossingsLocalBranches HironakaEmbeddedAnalytic AnalyticDimensionBasics
  HironakaDimensionThreeStepOneCurveEnvelope RegularLocusComponent AnalyticIrreducibleComponents
  RegularPointDimension HironakaHilbertSamuelTangentValue HironakaHolomorphicJetChartInvariance

abbrev M := LiftedModel.{0} 2
def origin : M := ULift.up (0 : ComplexModel 2)
def axis (i : Fin 2) : Set M := {z | z.down i = 0}
def crossing : Set M := axis 0 ∪ axis 1

theorem origin_mem_axis (i : Fin 2) : origin ∈ axis i := by
  change (0 : ComplexModel 2) i = 0
  simp

theorem axis_regular (i : Fin 2) {x : M} (hx : x ∈ axis i) :
    RegularAtDim (n := 2) (axis i) x 1 := by
  have hs : {q : M | q.down ∈ coordSubspace {i}} = axis i := by
    ext z
    simp [coordSubspace,axis]
  have hx' : x.down ∈ coordSubspace {i} := by
    change x ∈ {q : M | q.down ∈ coordSubspace {i}}
    rwa [hs]
  simpa only [hs,Finset.card_singleton,show 2 - 1 = 1 by decide]
    using regularAtDim_liftedModel_coordSubspace {i} hx'

theorem axis_closed (i : Fin 2) : IsClosed (axis i) :=
  isClosed_eq ((EuclideanSpace.proj i).continuous.comp continuous_uliftDown) continuous_const

theorem axis_analytic (i : Fin 2) : IsComplexAnalyticSubset (n := 2) (axis i) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    ⟨axis_closed i, fun _ hx => ⟨1,axis_regular i hx⟩⟩

theorem crossing_analytic : IsComplexAnalyticSubset (n := 2) crossing :=
  HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union (axis_analytic 0) (axis_analytic 1)

theorem crossing_pure : IsPureDim (n := 2) crossing 1 := by
  have hAxis (i : Fin 2) : DimLE (n := 2) (axis i) 1 := by
    intro x d hx
    exact BlowupStrictSubmanifold.le_of_regularAtDim_subset hx (axis_regular i hx.2.1) subset_rfl
  have hUpper := (analytic_dimLE_union (axis_analytic 0) (hAxis 0)
    (axis_analytic 1) (hAxis 1)).2
  intro x d h
  apply le_antisymm (hUpper x d h)
  rcases h.2.1 with hx | hx
  · exact BlowupStrictSubmanifold.le_of_regularAtDim_subset (axis_regular 0 hx) h subset_union_left
  · exact BlowupStrictSubmanifold.le_of_regularAtDim_subset (axis_regular 1 hx) h subset_union_right

theorem frequently_axis_away {i j : Fin 2} (hij : i ≠ j) :
    ∃ᶠ z in 𝓝 origin, z ∈ axis i ∧ z ∉ axis j := by
  let f : ℂ → M := fun t => ULift.up (t • (EuclideanSpace.single j 1 : ComplexModel 2))
  have hc : Continuous f := continuous_uliftUp.comp (continuous_id.smul continuous_const)
  have h0 : f 0 = origin := congrArg ULift.up (zero_smul ℂ _)
  have ht : Tendsto f (𝓝 0) (𝓝 origin) := h0 ▸ hc.tendsto 0
  apply ht.frequently
  have hfreq : ∃ᶠ t in 𝓝 (0 : ℂ), t ≠ 0 :=
    mem_closure_iff_frequently.mp (dense_compl_singleton (0 : ℂ) 0)
  refine hfreq.mono (fun t ht => ?_)
  change (t • (EuclideanSpace.single j 1 : ComplexModel 2)) i = 0 ∧
    (t • (EuclideanSpace.single j 1 : ComplexModel 2)) j ≠ 0
  simpa [PiLp.single_apply,hij] using ht

theorem crossing_origin_singular : origin ∈ singularSet (n := 2) crossing := by
  apply mem_singularSet_iff.mpr
  refine ⟨Or.inl (origin_mem_axis 0), fun d hr => ?_⟩
  let C := closure (component (n := 2) crossing origin)
  have hC := isComplexAnalyticallyIrreducible_closure_component crossing_analytic hr
  have hCsub : C ⊆ crossing := closure_minimal (component_subset (n := 2) crossing origin)
    crossing_analytic.isClosed
  have hEq : C = (C ∩ axis 0) ∪ (C ∩ axis 1) := by
    ext z
    constructor
    · intro hz
      exact (hCsub hz).elim (fun h => Or.inl ⟨hz,h⟩) (fun h => Or.inr ⟨hz,h⟩)
    · rintro (hz | hz) <;> exact hz.1
  obtain ⟨O,hO,h0,hPart,_,_⟩ := exists_isOpen_inter_subset (mem_component_self hr) hr
  rcases hC.eq_left_or_eq_right (hC.analytic.inter (axis_analytic 0))
    (hC.analytic.inter (axis_analytic 1)) inter_subset_left inter_subset_left hEq with hA | hB
  · obtain ⟨z,hz,hzO⟩ := ((frequently_axis_away (i := 1) (j := 0) (by decide)).and_eventually
      (hO.mem_nhds h0)).exists
    have hzC : z ∈ C := subset_closure (hPart ⟨Or.inr hz.1,hzO⟩)
    change z ∈ closure (component (n := 2) crossing origin) at hzC
    have hZ : z ∈ closure (component (n := 2) crossing origin) ∩ axis 0 := hA ▸ hzC
    exact hz.2 hZ.2
  · obtain ⟨z,hz,hzO⟩ := ((frequently_axis_away (i := 0) (j := 1) (by decide)).and_eventually
      (hO.mem_nhds h0)).exists
    have hzC : z ∈ C := subset_closure (hPart ⟨Or.inl hz.1,hzO⟩)
    change z ∈ closure (component (n := 2) crossing origin) at hzC
    have hZ : z ∈ closure (component (n := 2) crossing origin) ∩ axis 1 := hB ▸ hzC
    exact hz.2 hZ.2

theorem crossing_hs_drop_on_axis :
    ∃ᶠ z in 𝓝 origin, z ∈ axis 0 ∧
      ∃ q, hilbertSamuelAt (HolomorphicIdealSheaves.vanishingIdeal (n := 2) crossing) z q ≠
        hilbertSamuelAt (HolomorphicIdealSheaves.vanishingIdeal (n := 2) crossing) origin q := by
  have hSing := singularLocus_eq_first_hilbertSamuel_superlevel crossing_analytic
    (by decide : 1 ≤ 2) crossing_pure
  have h0 : origin ∈ crossing \ regularLocus (n := 2) crossing 1 :=
    ⟨Or.inl (origin_mem_axis 0), (mem_singularSet_iff.mp crossing_origin_singular).2 1⟩
  have h0Rank := (Set.ext_iff.mp hSing origin).mp h0
  refine (frequently_axis_away (i := 0) (j := 1) (by decide)).mono ?_
  rintro z ⟨hz,hz'⟩
  refine ⟨hz,1,?_⟩
  have hr : RegularAtDim (n := 2) crossing z 1 := by
    apply regularAtDim_of_inter_eq (axis_closed 1).isOpen_compl hz' _ (axis_regular 0 hz)
    ext y
    simp only [mem_inter_iff, mem_compl_iff, crossing, mem_union]
    tauto
  intro hf
  exact ((Set.ext_iff.mp hSing z).mpr ⟨Or.inl hz,hf.symm ▸ h0Rank.2⟩).2 hr

theorem axis_zero_ordered_snc : IsSNCDivisor 2 [axis 0] := by
  simpa [coordinateHyperplanes, axis] using
    (isSNCDivisor_coordinateHyperplanes (n := 2) ({0} : Finset (Fin 2)))

#print axioms crossing_hs_drop_on_axis

end
end Hironaka.HironakaG1NativeCrossingGeometry
