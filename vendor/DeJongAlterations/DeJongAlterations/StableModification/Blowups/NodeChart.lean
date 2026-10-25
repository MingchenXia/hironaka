import DeJongAlterations.StableModification.Blowups.Basic
import DeJongAlterations.StableModification.Blowups.StrictlySemistable
import DeJongAlterations.Geometry.NodeBlowupCover
import DeJongAlterations.Geometry.NodeFamilySmooth

/-!
# The blow-up of a node chart over a domain

Let `A` be a domain (in Temkin's application a valuation ring `R` with separably closed
fraction field), `π, b ∈ A` nonzero, and `N = A[u,v]/(uv - πb)` the nodal standard model
(`Curves.nodeModel (π * b)`). We study the blow-up of `N` along `(u, π)` (Codex's
`Algebra.NodeBlowupChart.centerIdeal π b`). This is the first stage of M. Temkin, *Stable
modification of relative curves*, proof of Prop 4.3.1 (T:2970–2990): there `a ∈ R` with
`|a| ≤ |π|`, so `a = πb` with `b ∈ R`, and

* `Bl_{(u,π)}(N)` is covered by the charts `A[u, π/u]/(u·(π/u) - π)` (Codex's
  `uChartInclusion π b`, the node `Node A π`) and `A[v, u/π]/(v·(u/π) - b)`
  (`tChartInclusion π b`, the node `Node A b`), hence is strictly semi-stable
  (`nodeBlowup_isStrictlySemistable`);
* it is a modification (`nodeBlowup_isModification`), an isomorphism over the complement of
  `V(u, v, π)` (`nodeBlowup_isIso`) and over `D(b)` (`nodeBlowup_isIso_basicOpen`): the modification locus lies in `V(u, v, π)`, which maps
  isomorphically onto the closed subscheme `Spec A/(π)`-part `V(π) ⊆ Spec A`
  (`nodeLocus`, `isClosedImmersion_nodeLocus_comp`); over a local `A` it has a single closed
  point, the origin of the closed fibre ("`x` is the only closed point of the modification
  locus", T:2989);
* the open `{π/u invertible} ≅ Spec A[u/π, π/u]/((u/π)(π/u) - 1)` of the `u`-chart is smooth
  over `A` (`nodeBlowupSmoothOpen`, `smooth_nodeBlowupSmoothOpen`; T:2989–2990).

This is `lem:sm-blowup-node-chart` of the blueprint chapter `sm-blowups-valuation.tex`.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace Polynomial

noncomputable section

namespace DeJongAlterations.StableModification.Blowups

universe u

open Curves Algebra.NodeBlowupChart NodeBlowupCover

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsDomain A] (π b : A) [Fact (π ≠ 0)] [Fact (b ≠ 0)]

/-- The structure morphism `Bl_{(u,π)} Spec A[u,v]/(uv - πb) ⟶ Spec A`. -/
def nodeBlowupMorphism : affineBlowup (centerIdeal π b) ⟶ Spec (.of A) :=
  affineBlowupStructure (centerIdeal π b) ≫ nodeModel (π * b)

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The centre `(u, π)` is finitely generated. -/
theorem centerIdeal_fg : (centerIdeal π b).FG :=
  Submodule.fg_span ((Set.finite_singleton _).insert _)

/-- The parameter `π` is nonzero in the node ring. -/
theorem algebraMap_ne_zero_node : algebraMap A (Node A (π * b)) π ≠ 0 :=
  (map_ne_zero_iff _ (Algebra.NodeDomain.algebraMap_nodeQuotient_injective (π * b)
    (mul_ne_zero (Fact.out : π ≠ 0) (Fact.out : b ≠ 0)))).mpr Fact.out

/-- The centre `(u, π)` is a nonzero ideal. -/
theorem centerIdeal_ne_bot : centerIdeal π b ≠ ⊥ := by
  intro h
  have hmem : algebraMap A (Node A (π * b)) π ∈ centerIdeal π b :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  rw [h, Ideal.mem_bot] at hmem
  exact algebraMap_ne_zero_node π b hmem

/-- **The blow-up of the node chart is a modification.** -/
theorem nodeBlowup_isModification : IsModification (affineBlowupStructure (centerIdeal π b)) :=
  isModification_affineBlowupStructure _ (centerIdeal_ne_bot π b) (centerIdeal_fg π b)

/-- The `u`-chart `A[u, π/u]/(u·(π/u) - π)` lies over `Spec A` as the node model `nodeModel π`. -/
theorem uChartInclusion_nodeBlowupMorphism :
    uChartInclusion π b ≫ nodeBlowupMorphism π b = nodeModel π := by
  rw [nodeBlowupMorphism, ← Category.assoc, uChartInclusion_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a : 2
  exact (uChartOriginalMap π b).commutes a

/-- The `π`-chart `A[v, u/π]/(v·(u/π) - b)` lies over `Spec A` as the node model `nodeModel b`. -/
theorem tChartInclusion_nodeBlowupMorphism :
    tChartInclusion π b ≫ nodeBlowupMorphism π b = nodeModel b := by
  rw [nodeBlowupMorphism, ← Category.assoc, tChartInclusion_structure]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  ext a : 2
  exact (tChartOriginalMap π b).commutes a

/-- An open immersion over `S` from a strictly semi-stable unmarked curve gives a strictly
semi-stable unmarked open. -/
theorem isStrictlySemistable_opensRange_of_comp {X Y S : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (g : Y ⟶ S) (hX : IsStrictlySemistable (j ≫ g) ⊤) :
    IsStrictlySemistable (j.opensRange.ι ≫ g) ((⊤ : Y.IdealSheafData).comap j.opensRange.ι) := by
  have heq : j.opensRange.ι ≫ g = j.isoOpensRange.inv ≫ j ≫ g := by
    rw [← Category.assoc, Scheme.Hom.isoOpensRange_inv_comp]
  rw [heq, Scheme.IdealSheafData.comap_top]
  simpa using hX.etale_comp j.isoOpensRange.inv

/-- **The blow-up of the node chart is strictly semi-stable** (without marks): it is covered
by the two charts, which are node models over `A`. -/
theorem nodeBlowup_isStrictlySemistable : IsStrictlySemistable (nodeBlowupMorphism π b) ⊤ := by
  refine IsStrictlySemistable.of_openCover fun x => ?_
  have hx : x ∈ (uChartInclusion π b).opensRange ⊔ (tChartInclusion π b).opensRange := by
    rw [chartInclusions_sup_opensRange]
    trivial
  rcases hx with hu | ht
  · refine ⟨_, hu, isStrictlySemistable_opensRange_of_comp _ _ ?_⟩
    rw [uChartInclusion_nodeBlowupMorphism]
    exact isStrictlySemistable_nodeModel π
  · refine ⟨_, ht, isStrictlySemistable_opensRange_of_comp _ _ ?_⟩
    rw [tChartInclusion_nodeBlowupMorphism]
    exact isStrictlySemistable_nodeModel b

section Locus

/-- The ideal `(u, v, π)` of the node ring: its vanishing locus contains the modification
locus of the blow-up. -/
def nodeLocusIdeal : Ideal (Node A (π * b)) :=
  Ideal.span {coordinate (π * b) 0, coordinate (π * b) 1, algebraMap A (Node A (π * b)) π}

/-- The open `D(u) ∪ D(v) ∪ D(π)`, the complement of `V(u, v, π)`. -/
def nodeLocusComplement : (Spec (.of (Node A (π * b)))).Opens :=
  PrimeSpectrum.basicOpen (coordinate (π * b) 0) ⊔ PrimeSpectrum.basicOpen (coordinate (π * b) 1) ⊔
    PrimeSpectrum.basicOpen (algebraMap A (Node A (π * b)) π)

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The coordinates of the node satisfy `u v = π b`. -/
theorem coordinate_mul_coordinate :
    coordinate (π * b) 0 * coordinate (π * b) 1 =
      algebraMap A (Node A (π * b)) π * algebraMap A (Node A (π * b)) b := by
  rw [← map_mul]
  exact Algebra.NodeDomain.nodeCoordinateProduct (π * b)

/-- **The blow-up of the node chart is an isomorphism off `V(u, v, π)`.** Over `D(u)` and
`D(π)` the centre is the unit ideal; over `D(v)` it is principal, generated by `π`, since
`v·u = π b`. -/
theorem nodeBlowup_isIso :
    IsIso (affineBlowupStructure (centerIdeal π b) ∣_ nodeLocusComplement π b) := by
  have hc : π * b ≠ 0 := mul_ne_zero Fact.out Fact.out
  have huI : coordinate (π * b) 0 ∈ centerIdeal π b := Ideal.subset_span (Set.mem_insert _ _)
  have hπI : algebraMap A (Node A (π * b)) π ∈ centerIdeal π b :=
    Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  have hu := affineBlowupStructure_restrict_isIso (centerIdeal π b) _ huI
    (Algebra.NodeDomain.nodeCoordinate_ne_zero (π * b) hc 0)
  have hπ := affineBlowupStructure_restrict_isIso (centerIdeal π b) _ hπI
    (algebraMap_ne_zero_node π b)
  have hv := affineBlowupStructure_restrict_isIso_of_mul_mem (centerIdeal π b)
    (coordinate (π * b) 1) hπI (algebraMap_ne_zero_node π b) (by
      intro a ha
      obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.mp ha
      refine ⟨1, x * algebraMap A _ b + y * coordinate (π * b) 1, ?_⟩
      linear_combination x * coordinate_mul_coordinate π b)
  have := isIso_morphismRestrict_sup (affineBlowupStructure (centerIdeal π b))
    (PrimeSpectrum.basicOpen (coordinate (π * b) 0)) (PrimeSpectrum.basicOpen (coordinate (π * b) 1))
  exact isIso_morphismRestrict_sup (affineBlowupStructure (centerIdeal π b))
    (PrimeSpectrum.basicOpen (coordinate (π * b) 0) ⊔ PrimeSpectrum.basicOpen (coordinate (π * b) 1))
    (PrimeSpectrum.basicOpen (algebraMap A (Node A (π * b)) π))

/-- **Over `D(b)` the blow-up of the node chart is an isomorphism**: there the centre `(u, π)` is
principal, generated by `u`, since `b·π = u·v`. In particular the blow-up is an isomorphism if
`b` is a unit (the case `|a| = |π|`). -/
theorem nodeBlowup_isIso_basicOpen :
    IsIso (affineBlowupStructure (centerIdeal π b) ∣_
      PrimeSpectrum.basicOpen (algebraMap A (Node A (π * b)) b)) := by
  have hc : π * b ≠ 0 := mul_ne_zero Fact.out Fact.out
  have huI : coordinate (π * b) 0 ∈ centerIdeal π b := Ideal.subset_span (Set.mem_insert _ _)
  refine affineBlowupStructure_restrict_isIso_of_mul_mem (centerIdeal π b) _ huI
    (Algebra.NodeDomain.nodeCoordinate_ne_zero (π * b) hc 0) ?_
  intro c hcI
  obtain ⟨x, y, rfl⟩ := Ideal.mem_span_pair.mp hcI
  refine ⟨1, x * algebraMap A _ b + y * coordinate (π * b) 1, ?_⟩
  linear_combination (-y) * coordinate_mul_coordinate π b

/-- The closed immersion of `V(u, v, π) = Spec N/(u, v, π)` into the node chart. -/
def nodeLocus : Spec (.of (Node A (π * b) ⧸ nodeLocusIdeal π b)) ⟶ Spec (.of (Node A (π * b))) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _))

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
instance isClosedImmersion_nodeLocus : IsClosedImmersion (nodeLocus π b) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The locus `V(u, v, π)` is exactly the complement of `nodeLocusComplement`. -/
theorem range_nodeLocus :
    Set.range (nodeLocus π b) = ((nodeLocusComplement π b : Set (Spec (.of (Node A (π * b))))))ᶜ := by
  have h : Set.range (nodeLocus π b) =
      Set.range (PrimeSpectrum.comap (S := Node A (π * b) ⧸ nodeLocusIdeal π b)
        (Ideal.Quotient.mk (nodeLocusIdeal π b))) := rfl
  rw [h, range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_compl_iff]
  rw [nodeLocusIdeal, Ideal.span_le]
  simp only [nodeLocusComplement, Opens.coe_sup, Set.mem_union, SetLike.mem_coe, not_or,
    Set.insert_subset_iff, Set.singleton_subset_iff]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨fun h => h h0, fun h => h h1⟩, fun h => h h2⟩
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact ⟨Classical.not_not.mp h0, Classical.not_not.mp h1, Classical.not_not.mp h2⟩

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The coefficient map `A ⟶ N/(u, v, π)` is surjective: `V(u, v, π)` is the image of a closed
subscheme of `Spec A`. -/
theorem algebraMap_nodeLocus_surjective :
    Function.Surjective (algebraMap A (Node A (π * b) ⧸ nodeLocusIdeal π b) :
      A →+* Node A (π * b) ⧸ nodeLocusIdeal π b) := by
  intro z
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨a, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨c, hc⟩ := hq
    exact ⟨a + c, by rw [map_add, ha, hc, map_add, map_add]⟩
  | mul_X p i hp =>
    obtain ⟨a, ha⟩ := hp
    refine ⟨0, ?_⟩
    have hi : Ideal.Quotient.mk (nodeLocusIdeal π b)
        (Ideal.Quotient.mk (Algebra.NodeChart.uChartIdeal A (π * b)) (MvPolynomial.X i)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      fin_cases i
      · exact Ideal.subset_span (Set.mem_insert _ _)
      · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    rw [map_zero, map_mul, map_mul, hi]
    exact (mul_zero (M₀ := Node A (π * b) ⧸ nodeLocusIdeal π b) _).symm

/-- **The modification locus is a closed subscheme of the base**: the composite
`V(u, v, π) ⟶ Spec N ⟶ Spec A` is a closed immersion. -/
instance isClosedImmersion_nodeLocus_comp : IsClosedImmersion (nodeLocus π b ≫ nodeModel (π * b)) := by
  have h : nodeLocus π b ≫ nodeModel (π * b) =
      Spec.map (CommRingCat.ofHom (algebraMap A (Node A (π * b) ⧸ nodeLocusIdeal π b))) := by
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  rw [h]
  exact IsClosedImmersion.spec_of_surjective _ (algebraMap_nodeLocus_surjective π b)

omit [IsDomain A] [Fact (π ≠ 0)] [Fact (b ≠ 0)] in
/-- The image of `V(u, v, π)` in `Spec A` lies in `V(π)`. -/
theorem range_nodeLocus_comp_subset :
    Set.range (nodeLocus π b ≫ nodeModel (π * b)) ⊆ PrimeSpectrum.zeroLocus {π} := by
  rintro _ ⟨y, rfl⟩
  rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  change π ∈ Ideal.comap ((Ideal.Quotient.mk (nodeLocusIdeal π b)).comp
    (algebraMap A (Node A (π * b)))) y.asIdeal
  rw [Ideal.mem_comap]
  have : (Ideal.Quotient.mk (nodeLocusIdeal π b)) (algebraMap A (Node A (π * b)) π) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  change (Ideal.Quotient.mk (nodeLocusIdeal π b)) (algebraMap A (Node A (π * b)) π) ∈ y.asIdeal
  rw [this]
  exact y.asIdeal.zero_mem

end Locus

section SmoothOpen

/-- The open `{π/u invertible}` of the `u`-chart `A[u, w]/(uw - π)`, `w = π/u`, i.e.
`Spec A[u/π, π/u]/((u/π)(π/u) - 1)` (T:2989–2990). -/
def nodeBlowupSmoothOpen : (affineBlowup (centerIdeal π b)).Opens :=
  uChartInclusion π b ''ᵁ Geometry.NodeFamilySmooth.coordinateOpen π 1

/-- **The open `{π/u invertible}` of the blow-up is smooth over `A`.** -/
theorem smooth_nodeBlowupSmoothOpen :
    Smooth ((nodeBlowupSmoothOpen π b).ι ≫ nodeBlowupMorphism π b) := by
  rw [nodeBlowupSmoothOpen, ← Scheme.Hom.isoImage_inv_ι, Category.assoc, Category.assoc,
    uChartInclusion_nodeBlowupMorphism]
  have := Geometry.NodeFamilySmooth.nodeMorphism_smooth_on_coordinate π 1
  infer_instance

end SmoothOpen

end DeJongAlterations.StableModification.Blowups
