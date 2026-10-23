import DeJongAlterations.StableModificationBridge.StableOpenNoSelfNodeGenus

/-! Zero arithmetic genus on the SAME original component removes intrinsic normalization defects. -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
universe u

namespace DeJongAlterations.StableModificationBridge.StableOpenRationalNormalization

open StableModification CurvesField CurvesField.Genus BlowDown.ClosureComponent Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Y : Scheme.{u}} [CompactSpace Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    [Finite (genericPoints Y)] [IsReduced Y] {k : Type u} [Field k] [IsAlgClosed k]
    (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q]
    (hdim : topologicalKrullDim Y ≤ 1) (v : Y)
    (hp : IsProjectiveOver (closureι v ≫ q))
    (hpt : ∃ y ∈ closure {v}, y ≠ v)
    (hpa : arithmeticGenus (closureScheme v) (structureCoeff (closureι v ≫ q)) = 0)

include hdim hp hpt hpa

omit [Finite (genericPoints Y)] [IsReduced Y] in
/-- Native normalized genus and EVERY intrinsic defect vanish; no normality or branch certificate. -/
theorem genus_and_delta_eq_zero :
    componentGenus (structureCoeff q) v = 0 ∧
    ∀ y : closureScheme v,
      deltaInvariant (normalizationPointsMap ({closurePt v} : Set (closureScheme v)))
        (structureCoeff (closureι v ≫ q)) y = 0 := by
  classical
  have hdimT : topologicalKrullDim (closureScheme v) ≤ 1 :=
    (closureι v).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hgen : genericPoint (closureScheme v) = closurePt v := by
    apply (genericPoint_spec (closureScheme v)).eq
    rw [isGenericPoint_iff_specializes]
    exact fun x => ⟨fun _ => trivial, fun _ => closurePt_specializes v x⟩
  have hG : ({closurePt v} : Set (closureScheme v)) =
      genericPoints (closureScheme v) := by
    rw [genericPoints_eq_singleton, hgen]
  have hptT : ∃ y ∈ closure ({closurePt v} : Set (closureScheme v)), y ≠ closurePt v := by
    obtain ⟨z, hz, hne⟩ := hpt
    rw [← range_closureι] at hz
    obtain ⟨y, rfl⟩ := hz
    refine ⟨y, specializes_iff_mem_closure.mp (closurePt_specializes v y), fun hy => hne ?_⟩
    rw [hy, closureι_closurePt]
  have hgT := BlowDown.ExcSpecialize.componentGenus_nonneg (closureι v ≫ q) hp hdimT hptT
  have hge := BlowDown.ExcSpecialize.componentGenus_eq q (closureι v) (closurePt v)
  rw [closureι_closurePt] at hge
  rw [hge] at hgT
  obtain ⟨_, hsupp, hformula⟩ := arithmeticGenus_eq_normalizationPoints (closureι v ≫ q)
    ({closurePt v} : Set (closureScheme v)) hG hdimT hp
  change arithmeticGenus (closureScheme v) (structureCoeff (closureι v ≫ q)) =
    componentGenus (structureCoeff (closureι v ≫ q)) (closurePt v) +
      ((∑ᶠ y, deltaInvariant (normalizationPointsMap ({closurePt v} : Set (closureScheme v)))
        (structureCoeff (closureι v ≫ q)) y : ℕ) : ℤ) at hformula
  rw [hge, hpa] at hformula
  have hg : componentGenus (structureCoeff q) v = 0 := by omega
  have hsum : ∑ᶠ y : closureScheme v,
      deltaInvariant (normalizationPointsMap ({closurePt v} : Set (closureScheme v)))
        (structureCoeff (closureι v ≫ q)) y = 0 := by omega
  refine ⟨hg, fun y => ?_⟩
  let δ := deltaInvariant (normalizationPointsMap ({closurePt v} : Set (closureScheme v)))
    (structureCoeff (closureι v ≫ q))
  have hle : δ y ≤ ∑ᶠ z, δ z := by
    rw [finsum_eq_sum_of_support_subset δ (s := hsupp.toFinset) (fun _ hx => hsupp.mem_toFinset.mpr hx)]
    by_cases hy : y ∈ hsupp.toFinset
    · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy
    · have hz : δ y = 0 := by simpa [Function.support] using hy
      rw [hz]
      exact Nat.zero_le _
  change δ y = 0
  change ∑ᶠ y, δ y = 0 at hsum
  omega

/-- Every ORIGINAL closed node on an arithmetic-genus-zero component meets another ORIGINAL component. -/
theorem node_meets_other_component (hN : Curves.IsNodalFiber q)
    (hv : v ∈ genericPoints Y) (z : Y) (hzv : z ∈ closure {v})
    (hzc : IsClosed ({z} : Set Y)) (hnode : Geometry.IsGeometricOrdinaryDoublePoint q z) :
    ∃ w ∈ genericPoints Y, w ≠ v ∧ z ∈ closure {w} := by
  classical
  by_contra hother
  have hother' : ∀ w ∈ genericPoints Y, w ≠ v → z ∉ closure {w} := by
    simpa only [not_exists, not_and] using hother
  have h2 := StableOpenBoundaryBranches.branchCount_eq_two_of_no_other q hdim z hzc
    (BlowDown.not_mem_genericPoints_of_isClosed hN.pure hzc) hnode hv hother'
  obtain ⟨y, hy⟩ : z ∈ Set.range (closureι v) := by rwa [range_closureι]
  have hyc : IsClosed ({y} : Set (closureScheme v)) := by
    have he : ({y} : Set (closureScheme v)) = (closureι v) ⁻¹' {z} := by
      rw [← hy]
      simpa only [Set.image_singleton] using
        ((closureι v).isClosedEmbedding.injective.preimage_image (s := {y})).symm
    rw [he]
    exact hzc.preimage (closureι v).continuous
  have hG : ({closurePt v} : Set (closureScheme v)) =
      genericPoints (closureScheme v) := by
    have he : genericPoint (closureScheme v) = closurePt v := by
      apply (genericPoint_spec (closureScheme v)).eq
      rw [isGenericPoint_iff_specializes]
      exact fun x => ⟨fun _ => trivial, fun _ => closurePt_specializes v x⟩
    rw [genericPoints_eq_singleton, he]
  have hdimT : topologicalKrullDim (closureScheme v) ≤ 1 :=
    (closureι v).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  let π := normalizationPointsMap ({closurePt v} : Set (closureScheme v))
  have : IsFinite π := isFinite_normalizationPointsMap (S := ({closurePt v} : Set _))
    (closureι v ≫ q)
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  let _ := (sectionsRingHom (structureCoeff (closureι v ≫ q)) (le_top : V ≤ ⊤)).toAlgebra
  let _ := (π.app V).hom.toAlgebra
  let _ := ((π.app V).hom.comp
    (sectionsRingHom (structureCoeff (closureι v ≫ q)) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(closureScheme v, V) Γ(normalizationPoints ({closurePt v} : Set _),
      π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ := finite_local_inputs π (closureι v ≫ q) y hyc V hV hyV
    (normalizationPoints_app_injective hG V hV)
    (normalizationPoints_isFiniteCoker (closureι v ≫ q) hG hdimT V hV)
  have hle := CurvesField.card_le_delta_add_one_of_isLocalRing _ hres
  rw [hcard, ← hdelta] at hle
  have hcard2 : Nat.card ↥(π ⁻¹' {y}) = 2 := by
    rw [BlowDown.ExcSpecialize.natCard_fiber_normalizationPoints_eq q (closureι v) (closurePt v) y,
      closureι_closurePt, hy]
    exact h2
  have hzero := (genus_and_delta_eq_zero q hdim v hp hpt hpa).2 y
  change deltaInvariant π (structureCoeff (closureι v ≫ q)) y = 0 at hzero
  omega

/-- The actual normalized component is the SAME original rational component with its whole map. -/
theorem exists_normalization_iso (hN : Curves.IsNodalFiber q) (hv : v ∈ genericPoints Y) :
    ∃ e : normalizationPoints ({v} : Set Y) ≅ closureScheme v,
      e.hom ≫ closureι v = normalizationPointsMap ({v} : Set Y) := by
  apply StableOpenNoSelfNodeGenus.exists_normalization_iso_reduced_component q hN v hv
  exact fun z hzv hzc hnode => node_meets_other_component q hdim v hp hpt hpa hN hv z hzv hzc hnode

end DeJongAlterations.StableModificationBridge.StableOpenRationalNormalization
