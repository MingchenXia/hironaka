/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ProjectiveCurveFibrationCharts
import DeJongAlterations.StableModification.BlowDown.Genus
import DeJongAlterations.StableModification.Cohomology.FiniteProjective
import DeJongAlterations.StableModification.CurvesField.CohomologyP1Proj
import DeJongAlterations.StableModification.CurvesField.OmegaDegree
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricCor
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricNormalization
import DeJongAlterations.StableModification.ValCurves.ModificationsDomination
import DeJongAlterations.StableModification.CurvesField.DualitySchemeExistence
import DeJongAlterations.StableModification.Cohomology.Connected
import DeJongAlterations.StableModification.BlowDown.ClosureComponent

/-!
# Subcurves of a reduced curve over an algebraically closed field: genus bounds

Let `X` be a reduced projective curve over an algebraically closed field `k` and `j : T → X` a
closed immersion of a reduced scheme whose image `Z` is a union of components of `X`. This file
compares the arithmetic genus `p_a(T) = 1 − χ(𝒪_T)` (`CurvesField.Genus.arithmeticGenus`) with the
combinatorial genus `γ` of the incidence graph of `X` along `Z` (`CurvesField.Genus.nodalGraph`),
the input of the exceptional-tree step in the proof of M. Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), Lemma 4.4.4 (`emptylem`, T:3158–3176; ERRATA T57) through
Temkin's genus formula, Lemma B.1 (`lastlem`, T:4413–4433). Blueprint: `lem:sm-bd-subcurve-genus`,
chapter `sm-blow-down-exceptional.tex`.

## Main results

* `normalizationPointsIso`: for `η ∈ T` the normalization of `T` in `Spec κ(η)` is that of `X`
  in `Spec κ(j η)`, over `X`; hence `componentGenus_eq` (component genera can be computed in `X`)
  and `natCard_fiber_normalizationPoints_eq` (so can branch counts).
* `one_le_deltaInvariant_of_mem_inner`: at an ordinary double point of `X` with both branches on
  `Z`, `δ_T ≥ 1` (two branches of `T`, Temkin's inequality `g(x) ≥ |x̃| − 1`).
* `combGenus_le_arithmeticGenus`: **`γ(Z) ≤ p_a(T)`** if the genera of the components of `Z` are
  nonnegative.
* `eulerChar_projectiveSpace_one`: `χ(ℙ¹_K, 𝒪) = 1` (lane COH4's cohomology of `ℙ¹`, with the
  structure coefficients of `DeJongAlterations.projectiveSpace`,
  `structureCoeff_projectiveSpaceStructure_one`).
* `bijective_structureCoeff_of_isIntegral`, `finrank_cohomology_zero_of_isIntegral`: an integral
  scheme universally closed over `k = k̄` has `Γ(𝒪) = k` and `h⁰(𝒪) = 1`.
* `componentGenus_nonneg`: **the normalized components of a projective curve over `k = k̄` have
  nonnegative genus** (the hypothesis `hg` of lane T44A2's `stability_criterion_fibre` and of
  lane CRV4, ERRATA T60), blueprint `lem:sm-bde-component-genus-nonneg`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace DeJongAlterations.StableModification.BlowDown.ExcSpecialize

universe u

open Cohomology CurvesField CurvesField.Genus

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section ResidueField

variable {T X : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j]

/-- A closed immersion induces isomorphisms of residue fields. -/
instance isIso_residueFieldMap_of_isClosedImmersion (η : T) : IsIso (j.residueFieldMap η) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨RingHom.injective _, ValCurves.residueFieldMap_surjective_of_stalkMap_surjective
    (j.stalkMap_surjective η)⟩

end ResidueField

section Points

variable {T X : Scheme.{u}} (j : T ⟶ X) [IsClosedImmersion j] (η : T)

/-- The residue field isomorphism `Spec κ_T(w) ≅ Spec κ_X(j η)` for `w ∈ {η}`. -/
def pointsIsoAux : ∀ x : ({η} : Set T),
    Spec (X.residueField ((Equiv.ofUnique ({η} : Set T) ({j η} : Set X)) x).1) ≅
      Spec (T.residueField x.1)
  | ⟨_, rfl⟩ => (asIso (Spec.map (j.residueFieldMap η))).symm

/-- The points scheme of `{η}` in `T` is that of `{j η}` in `X`. -/
def pointsIso : pointsScheme T ({η} : Set T) ≅ pointsScheme X ({j η} : Set X) :=
  Sigma.whiskerEquiv (Equiv.ofUnique _ _) (pointsIsoAux j η)

/-- `pointsIso` is compatible with the maps to `T` and `X`. -/
theorem pointsIso_hom_pointsMap :
    (pointsIso j η).hom ≫ pointsMap X ({j η} : Set X) = pointsMap T ({η} : Set T) ≫ j := by
  refine Sigma.hom_ext _ _ fun w => ?_
  obtain ⟨w, rfl⟩ := w
  simp only [pointsIso, Sigma.whiskerEquiv_hom, Sigma.ι_comp_map'_assoc, ι_pointsMap,
    ι_pointsMap_assoc]
  change Spec.map (j.residueFieldMap w) ≫ X.fromSpecResidueField (j w) = _
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField j w

end Points


section Normalization

variable {T X : Scheme.{u}} {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType q] (j : T ⟶ X) [IsClosedImmersion j]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from T))] (η : T)

include q

/-- The normalization of `T` in `κ(η)`, composed with `j`, is integral over `X`. -/
theorem isIntegralHom_normalizationPointsMap_comp :
    IsIntegralHom ((pointsMap T ({η} : Set T)).fromNormalization ≫ j) := by
  have : IsFinite (normalizationPointsMap ({η} : Set T)) :=
    isFinite_normalizationPointsMap (S := ({η} : Set T)) (j ≫ q)
  have : IsIntegralHom (normalizationPointsMap ({η} : Set T)) := inferInstance
  exact inferInstanceAs (IsIntegralHom (normalizationPointsMap ({η} : Set T) ≫ j))

/-- **The normalization of a component of a closed subscheme is that of the component of the
ambient scheme**: for a closed immersion `j : T → X` and `η ∈ T`, the normalization of `T` in
`Spec κ(η)` is the normalization of `X` in `Spec κ(j η)`, over `X`. -/
def normalizationPointsIso :
    normalizationPoints ({η} : Set T) ≅ normalizationPoints ({j η} : Set X) :=
  have := isIntegralHom_normalizationPointsMap_comp q j η
  (normalizationCompIso (pointsMap T ({η} : Set T)) j).symm ≪≫
    normalizationIsoOfIso (pointsMap T ({η} : Set T) ≫ j) (pointsMap X ({j η} : Set X))
      (pointsIso j η) (pointsIso_hom_pointsMap j η)

/-- `normalizationPointsIso` is compatible with the maps to `T` and `X`. -/
theorem normalizationPointsIso_hom_comp :
    (normalizationPointsIso q j η).hom ≫ normalizationPointsMap ({j η} : Set X) =
      normalizationPointsMap ({η} : Set T) ≫ j := by
  have := isIntegralHom_normalizationPointsMap_comp q j η
  simp only [normalizationPointsIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [normalizationIsoOfIso_hom_fromNormalization, Iso.inv_comp_eq,
    normalizationCompIso_hom_fromNormalization]

end Normalization


section ComponentGenus

variable {T X : Scheme.{u}} {k : Type u} [Field k] (q : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType q] (j : T ⟶ X) [IsClosedImmersion j] [CompactSpace X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from T))] [CompactSpace T] (η : T)

/-- `structureCoeff (f ≫ q) = f^♯ ∘ structureCoeff q`. -/
theorem structureCoeff_comp {Y : Scheme.{u}} (f : Y ⟶ X) :
    structureCoeff (f ≫ q) = f.appTop.hom.comp (structureCoeff q) := by
  ext a
  simp [structureCoeff]

include q in
/-- **Component genera are computed in the ambient scheme**: for a closed immersion `j : T → X`
of `k`-schemes and `η ∈ T`, `g_T(η) = g_X(j η)`. -/
theorem componentGenus_eq :
    componentGenus (structureCoeff (j ≫ q)) η = componentGenus (structureCoeff q) (j η) := by
  have := isIntegralHom_normalizationPointsMap_comp q j η
  unfold componentGenus arithmeticGenus
  congr 1
  rw [← structureCoeff_comp, ← structureCoeff_comp]
  refine BlowDown.eulerChar_eq_of_iso _ _ (normalizationPointsIso q j η) ?_
  rw [← Category.assoc, normalizationPointsIso_hom_comp, Category.assoc]

include q in
/-- Branch counts are computed in the ambient scheme. -/
theorem natCard_fiber_normalizationPoints_eq (y : T) :
    Nat.card ↥(normalizationPointsMap ({η} : Set T) ⁻¹' {y}) =
      Nat.card ↥(normalizationPointsMap ({j η} : Set X) ⁻¹' {j y}) := by
  let e := normalizationPointsIso q j η
  refine Nat.card_congr (Equiv.ofBijective (fun w => ⟨e.hom w.1, ?_⟩) ⟨fun w₁ w₂ h => ?_, fun w => ?_⟩)
  · change (e.hom ≫ normalizationPointsMap ({j η} : Set X)) w.1 = j y
    rw [normalizationPointsIso_hom_comp q j η, Scheme.Hom.comp_apply]
    exact congrArg j w.2
  · exact Subtype.ext (e.hom.homeomorph.injective (congrArg Subtype.val h))
  · refine ⟨⟨e.inv w.1, ?_⟩, Subtype.ext ?_⟩
    · apply j.isClosedEmbedding.injective
      change (normalizationPointsMap ({η} : Set T) ≫ j) (e.inv w.1) = j y
      rw [← normalizationPointsIso_hom_comp q j η, ← Scheme.Hom.comp_apply, e.inv_hom_id_assoc]
      exact w.2
    · change (e.inv ≫ e.hom) w.1 = w.1
      rw [e.inv_hom_id]
      rfl

end ComponentGenus


section InnerDelta

variable {T X : Scheme.{u}} {k : Type u} [Field k] [IsAlgClosed k]
  (q : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType q] (j : T ⟶ X) [IsClosedImmersion j]
  [CompactSpace X] [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from T))] [CompactSpace T]
  [IsReduced X] [IsReduced T] [Finite (genericPoints X)] [Finite (genericPoints T)]
  (hdim : topologicalKrullDim X ≤ 1) (hdimT : topologicalKrullDim T ≤ 1)
  {Z : Set X} (G : Finset X) (G' : Finset T) (hG' : (G' : Set T) = genericPoints T)
  (hGG' : ∀ η, η ∈ G' ↔ j η ∈ G) (hGj : ∀ v ∈ G, v ∈ Set.range j)
  (hGgen : ∀ v ∈ G, v ∈ genericPoints X)

include hGG' hGj in
/-- Sums over the generic points of `T` are sums over their images in `X`. -/
theorem sum_comp_eq (φ : X → ℤ) : ∑ η ∈ G', φ (j η) = ∑ v ∈ G, φ v := by
  refine Finset.sum_nbij (fun η => j η) (fun η hη => (hGG' η).mp hη)
    (fun a _ b _ h => j.isClosedEmbedding.injective h) (fun v hv => ?_) (fun _ _ => rfl)
  obtain ⟨η, rfl⟩ := hGj v hv
  exact ⟨η, (hGG' η).mpr hv, rfl⟩

open scoped Classical in
include hdim hdimT hG' hGG' hGj hGgen in
/-- **At an inner double point the δ-invariant of the subcurve is at least one.** Let `T ⊆ X` be a
reduced closed subcurve with generic points `G' ↔ G`, and `e` an ordinary double point of `X` both
of whose branches lie on components in `G`. Then the normalization of `T` has two points over `e`,
so `δ_T(e) ≥ 1` (Temkin, App. B l. 4388–4391: `g(x) ≥ |x̃| - 1`). -/
theorem one_le_deltaInvariant_of_mem_inner [Fintype (nodesIn q Z)] (e : nodesIn q Z)
    (he : e ∈ (nodalGraph q hdim Z).inner G) (y : T) (hy : j y = e.1) :
    1 ≤ deltaInvariant (normalizationPointsMap (G' : Set T)) (structureCoeff (j ≫ q)) y := by
  have hyc : IsClosed ({y} : Set T) := by
    have : ({y} : Set T) = j ⁻¹' {j y} := by
      ext w
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ rfl, fun h => j.isClosedEmbedding.injective h⟩
    rw [this, hy]
    exact e.2.2.1.preimage j.continuous
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤) trivial
  have : IsFinite (normalizationPointsMap (G' : Set T)) :=
    isFinite_normalizationPointsMap (S := (G' : Set T)) (j ≫ q)
  let _ := (sectionsRingHom (structureCoeff (j ≫ q)) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (G' : Set T)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (G' : Set T)).app V).hom.comp
    (sectionsRingHom (structureCoeff (j ≫ q)) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(T, V) Γ(normalizationPoints (G' : Set T),
      normalizationPointsMap (G' : Set T) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ := finite_local_inputs
    (normalizationPointsMap (G' : Set T)) (j ≫ q) y hyc V hV hyV
    (normalizationPoints_app_injective hG' V hV)
    (normalizationPoints_isFiniteCoker (j ≫ q) hG' hdimT V hV)
  have hle := CurvesField.card_le_delta_add_one_of_isLocalRing _ hres
  rw [hcard, ← hdelta] at hle
  -- the normalization of `T` has two points over `y`
  have h2 : Nat.card ↥(normalizationPointsMap (G' : Set T) ⁻¹' {y}) = 2 := by
    rw [natCard_fiber_eq_sum_of_eq (j ≫ q) (G' : Set T) G' rfl y]
    have hb : ∀ η ∈ G', branchCount η y = branchCount (j η) e.1 := fun η _ => by
      rw [branchCount, branchCount, natCard_fiber_normalizationPoints_eq q j η y, hy]
    rw [Finset.sum_congr rfl hb]
    have hsum : ∑ η ∈ G', ((branchCount (j η) e.1 : ℕ) : ℤ) = ∑ v ∈ G, ((branchCount v e.1 : ℕ) : ℤ) :=
      sum_comp_eq j G G' hGG' hGj (fun v => (branchCount v e.1 : ℤ))
    have hsum' : ∑ η ∈ G', branchCount (j η) e.1 = ∑ v ∈ G, branchCount v e.1 := by
      exact_mod_cast hsum
    rw [hsum']
    have hzero : ∀ v ∈ genericFinset X, v ∉ G → branchCount v e.1 = 0 := by
      intro v hv hvG
      by_contra hne
      have hcl := (branchCount_ne_zero_iff q v e.1).mp hne
      exact hvG ((IncidenceGraph.mem_inner.mp he) v
        ((mem_nodalGraph_ends q hdim e v).mpr ⟨mem_genericFinset.mp hv, hcl⟩))
    have hGsub : G ⊆ genericFinset X := fun v hv => mem_genericFinset.mpr (hGgen v hv)
    rw [Finset.sum_subset hGsub hzero, ← natCard_fiber_eq_sum_of_eq q (genericPoints X)
      (genericFinset X) coe_genericFinset.symm e.1, ← card_branches q e.1,
      card_branches_of_mem_nodesIn q hdim e.2]
  omega


open scoped Classical in
include hdim hdimT hG' hGG' hGj hGgen in
/-- **The arithmetic genus of a reduced subcurve bounds its combinatorial genus.** Let `X` be a
reduced projective curve over `k = k̄` (`dim X ≤ 1`), `j : T → X` a closed immersion of a reduced
scheme with image `Z` whose generic points `G'` correspond to the components `G` of `X` in `Z`,
and the double points of `X` on `Z` (`nodesIn q Z`) finite. If the genera of the components in
`G` are nonnegative, then `γ(G) ≤ p_a(T)` for the combinatorial genus `γ` of the incidence graph
of `X` along `Z` (Temkin's genus formula, Lemma B.1, for `T`, with `δ_T ≥ 1` at the inner double
points and `≥ 0` elsewhere; `CurvesField.Genus.arithmeticGenus_eq_one_sub_card_add`). -/
theorem combGenus_le_arithmeticGenus [Fintype (nodesIn q Z)]
    (hg : ∀ v ∈ G, 0 ≤ componentGenus (structureCoeff q) v) (hpT : IsProjectiveOver (j ≫ q))
    (hZ : ∀ e : nodesIn q Z, e.1 ∈ Set.range j) :
    (nodalGraph q hdim Z).combGenus G ≤ arithmeticGenus T (structureCoeff (j ≫ q)) := by
  obtain ⟨hsupp, hpa⟩ := arithmeticGenus_eq_one_sub_card_add (j ≫ q) G' hG' hdimT hpT
  rw [hpa]
  unfold IncidenceGraph.combGenus
  -- the counts of components agree
  have hcard : G'.card = G.card := by
    refine Finset.card_nbij (fun η => j η) (fun η hη => (hGG' η).mp hη)
      (fun a _ b _ h => j.isClosedEmbedding.injective h) (fun v hv => ?_)
    obtain ⟨η, rfl⟩ := hGj v hv
    exact ⟨η, (hGG' η).mpr hv, rfl⟩
  -- the component genera agree
  have hgen : ∑ η ∈ G', componentGenus (structureCoeff (j ≫ q)) η =
      ∑ v ∈ G, ((nodalGraph q hdim Z).genus v : ℤ) := by
    rw [Finset.sum_congr rfl fun η _ => componentGenus_eq q j η,
      sum_comp_eq j G G' hGG' hGj (fun v => componentGenus (structureCoeff q) v)]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [nodalGraph_genus, Int.toNat_of_nonneg (hg v hv)]
  -- the inner double points contribute at least one each
  have hδ : ((nodalGraph q hdim Z).inner G).card ≤
      ∑ᶠ x, deltaInvariant (normalizationPointsMap (G' : Set T)) (structureCoeff (j ≫ q)) x := by
    set δ := deltaInvariant (normalizationPointsMap (G' : Set T)) (structureCoeff (j ≫ q))
    let ι : nodesIn q Z → T := fun e => (hZ e).choose
    have hι : ∀ e, j (ι e) = e.1 := fun e => (hZ e).choose_spec
    have hιinj : Function.Injective ι := fun a b h => Subtype.ext (by rw [← hι a, ← hι b, h])
    rw [finsum_eq_sum_of_support_subset δ (s := hsupp.toFinset) (by simp)]
    calc ((nodalGraph q hdim Z).inner G).card
        = ∑ e ∈ (nodalGraph q hdim Z).inner G, 1 := by simp
      _ ≤ ∑ e ∈ (nodalGraph q hdim Z).inner G, δ (ι e) := Finset.sum_le_sum fun e he =>
          one_le_deltaInvariant_of_mem_inner q j hdim hdimT G G' hG' hGG' hGj hGgen e he (ι e) (hι e)
      _ = ∑ x ∈ ((nodalGraph q hdim Z).inner G).image ι, δ x :=
          (Finset.sum_image fun a _ b _ h => hιinj h).symm
      _ ≤ ∑ x ∈ hsupp.toFinset, δ x := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun _ _ _ => Nat.zero_le _
          obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
          rw [Set.Finite.mem_toFinset, Function.mem_support]
          exact Nat.one_le_iff_ne_zero.mp (one_le_deltaInvariant_of_mem_inner q j hdim hdimT G G'
            hG' hGG' hGj hGgen e he (ι e) (hι e))
  rw [hcard, hgen]
  have : (((nodalGraph q hdim Z).inner G).card : ℤ) ≤
      ((∑ᶠ x, deltaInvariant (normalizationPointsMap (G' : Set T))
        (structureCoeff (j ≫ q)) x : ℕ) : ℤ) := by exact_mod_cast hδ
  linarith

end InnerDelta



section ProjectiveLine

variable (K : Type u) [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

instance compactSpace_projectiveSpace (n : ℕ) : CompactSpace (projectiveSpace K n) :=
  BlowDown.compactSpace_of_quasiCompact (projectiveSpaceStructure K n)

instance isAffineHom_diagonal_projectiveSpace (n : ℕ) :
    IsAffineHom (pullback.diagonal (terminal.from (projectiveSpace K n))) :=
  BlowDown.isAffineHom_diagonal_of_isSeparated (projectiveSpaceStructure K n)

/-- The structure coefficients of `ℙ¹_K = Proj K[X₀, X₁]` (`DeJongAlterations.projectiveSpace`) are
the constants `ProjectiveLine.constants` of lane COH4's cohomology computation. -/
theorem structureCoeff_projectiveSpaceStructure_one :
    structureCoeff (projectiveSpaceStructure K 1) = CurvesField.ProjectiveLine.constants K := by
  have h := closedConstants_eq_structureCoeff (𝟙 (projectiveSpace K 1)) (Category.id_comp _)
  rw [← h]
  ext a
  refine CurvesField.ProjectiveLine.eq_of_restrict (CurvesField.ProjectiveLine.chart_sup K) ?_ ?_
  · refine Eq.trans ?_ (CurvesField.ProjectiveLine.constGlob_U K a).symm
    change (Proj (projectiveSpaceGrading K 1)).presheaf.map
      (homOfLE (le_top : Proj.basicOpen (projectiveSpaceGrading K 1) (MvPolynomial.X 0) ≤ ⊤)).op
      (Geometry.ProperSteinProjectiveCech.gradedProjectiveConstants (projectiveSpaceGrading K 1) ⊤ a) = _
    refine (Geometry.ProperSteinProjectiveCech.gradedProjectiveConstants_basicOpen _ _ a).trans ?_
    change _ = (Proj.awayToSection (projectiveSpaceGrading K 1) (MvPolynomial.X 0))
      (CurvesField.ProjectiveLine.ψ K 0 1 (Polynomial.C a))
    rw [CurvesField.ProjectiveLine.ψ_C]
    rfl
  · refine Eq.trans ?_ (CurvesField.ProjectiveLine.constGlob_V K a).symm
    change (Proj (projectiveSpaceGrading K 1)).presheaf.map
      (homOfLE (le_top : Proj.basicOpen (projectiveSpaceGrading K 1) (MvPolynomial.X 1) ≤ ⊤)).op
      (Geometry.ProperSteinProjectiveCech.gradedProjectiveConstants (projectiveSpaceGrading K 1) ⊤ a) = _
    refine (Geometry.ProperSteinProjectiveCech.gradedProjectiveConstants_basicOpen _ _ a).trans ?_
    change _ = (Proj.awayToSection (projectiveSpaceGrading K 1) (MvPolynomial.X 1))
      (CurvesField.ProjectiveLine.ψ K 1 0 (Polynomial.C a))
    rw [CurvesField.ProjectiveLine.ψ_C]
    rfl

/-- `χ(ℙ¹_K, 𝒪) = 1`, i.e. `p_a(ℙ¹_K) = 0`. -/
theorem eulerChar_projectiveSpace_one :
    eulerChar (projectiveSpace K 1) (structureCoeff (projectiveSpaceStructure K 1)) = 1 := by
  rw [structureCoeff_projectiveSpaceStructure_one]
  change DualityScheme.eulerCharOf (SheafOfModules.unit (CurvesField.ProjectiveLine.projectiveLine K).ringCatSheaf)
    (CurvesField.ProjectiveLine.constants K) = 1
  rw [DualityScheme.eulerCharOf_eq_of_pair _ _ (CurvesField.ProjectiveLine.chart_sup K)
    (CurvesField.ProjectiveLine.projectiveLineCharts K).isAffineOpen_U
    (CurvesField.ProjectiveLine.projectiveLineCharts K).isAffineOpen_V
    (CurvesField.ProjectiveLine.projectiveLineCharts K).isAffineOpen_inf]
  have h0 := CurvesField.ProjectiveLine.finrank_cohomology_zero_projectiveLine K
  have h1 : Module.finrank K (cohomology (SheafOfModules.unit
      (CurvesField.ProjectiveLine.projectiveLine K).ringCatSheaf)
      (CurvesField.ProjectiveLine.constants K) 1) = 0 := by
    have := ModuleCat.subsingleton_of_isZero
      (CurvesField.ProjectiveLine.isZero_cohomology_one_projectiveLine K)
    exact Module.finrank_zero_of_subsingleton
  rw [h1, Nat.cast_zero, sub_zero]
  exact_mod_cast h0

end ProjectiveLine

section ComponentGenusNonneg

/-- The reduced closure of a point of a scheme with affine diagonal has affine diagonal. -/
instance isAffineHom_diagonal_closureScheme {X : Scheme.{u}}
    [IsAffineHom (pullback.diagonal (terminal.from X))] (z : X) :
    IsAffineHom (pullback.diagonal (terminal.from (ClosureComponent.closureScheme z))) :=
  CurvesField.Genus.isAffineHom_diagonal_of_isAffineHom (ClosureComponent.closureι z)

/-- The scheme of a single point (`CurvesField.Genus.pointsScheme C {η}`, the spectrum of its
residue field) is integral. -/
instance isIntegral_pointsScheme_singleton {C : Scheme.{u}} (η : C) :
    IsIntegral (pointsScheme C ({η} : Set C)) := by
  let e := Limits.coproductUniqueIso
    (fun x : ({η} : Set C) => Spec (C.residueField x.1))
  have : Nonempty (pointsScheme C ({η} : Set C)) :=
    ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

variable {Y : Scheme.{u}} [CompactSpace Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
  [IsReduced Y] {k : Type u} [Field k] [IsAlgClosed k] (q : Y ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType q]

/-- **Global functions on an integral scheme proper over `k = k̄` are constants**: the structure
coefficient `k → Γ(N, 𝒪)` is bijective (`Γ(N, 𝒪)` is a domain integral over `k`). -/
theorem bijective_structureCoeff_of_isIntegral {N : Scheme.{u}} [IsIntegral N]
    (f : N ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f] :
    Function.Bijective (structureCoeff f) := by
  have h := isIntegral_appTop_of_universallyClosed f
  have h' : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.IsIntegral :=
    RingHom.isIntegral_of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact IsAlgClosed.ringHom_bijective_of_isIntegral _ (RingHom.IsIntegral.trans _ _ h' h)

/-- **`h⁰ = 1` on an integral scheme proper over `k = k̄`.** -/
theorem finrank_cohomology_zero_of_isIntegral {N : Scheme.{u}} [IsIntegral N] [CompactSpace N]
    [IsAffineHom (pullback.diagonal (terminal.from N))]
    (f : N ⟶ Spec (CommRingCat.of k)) [UniversallyClosed f] :
    Module.finrank k (cohomology (SheafOfModules.unit N.ringCatSheaf) (structureCoeff f) 0) = 1 := by
  let L : k →ₗ[k] sectionsModuleCat (Cohomology.Connected.unitModule N) (structureCoeff f) ⊤
      le_top :=
    { toFun := fun l => (show Γ(N, ⊤) from structureCoeff f l)
      map_add' := fun l l' => map_add _ l l'
      map_smul' := fun r l => by
        change structureCoeff f (r * l) =
          sectionsRingHom (structureCoeff f) (le_top : ⊤ ≤ ⊤) r * structureCoeff f l
        rw [map_mul]
        congr 1
        exact (Cohomology.Connected.presheaf_map_self_apply _ _).symm }
  have hL : Function.Bijective L := bijective_structureCoeff_of_isIntegral f
  rw [← (cohomologyZeroIso (SheafOfModules.unit N.ringCatSheaf)
      (structureCoeff f)).toLinearEquiv.finrank_eq,
    ← (LinearEquiv.ofBijective L hL).finrank_eq, Module.finrank_self]

/-- **The genera of the normalized components of a projective curve are nonnegative** (the
hypothesis of lane CRV4's and T44A2's stability counts, ERRATA T60): for `Y` reduced, projective
over `k = k̄`, of dimension at most one, and a generic point `v` whose component is not a point,
`g(v) = p_a(Ỹ_v) ≥ 0`. The normalization `Ỹ_v` of the component is integral and proper over `k`,
so `h⁰(𝒪) = 1`, and it is covered by the preimages of a chart pair of the integral curve
`closure {v}` (`CurvesField.DualityScheme.exists_isSeparable_chartPair`), so
`χ = h⁰ − h¹ ≤ 1`. -/
theorem componentGenus_nonneg (hp : IsProjectiveOver q) (hdim : topologicalKrullDim Y ≤ 1)
    {v : Y} (hpt : ∃ y ∈ closure {v}, y ≠ v) :
    0 ≤ componentGenus (structureCoeff q) v := by
  have h := componentGenus_eq q (ClosureComponent.closureι v) (ClosureComponent.closurePt v)
  rw [ClosureComponent.closureι_closurePt] at h
  rw [← h]
  -- the integral projective curve `V = closure {v}` and a chart pair on it
  have hpV : IsProjectiveOver (ClosureComponent.closureι v ≫ q) :=
    DeJong.IsProjectiveOver.comp_isClosedImmersion hp _
  have hdimV : topologicalKrullDim (ClosureComponent.closureScheme v) ≤ 1 :=
    (ClosureComponent.closureι v).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hgen : genericPoint (ClosureComponent.closureScheme v) = ClosureComponent.closurePt v := by
    have hg : IsGenericPoint (ClosureComponent.closurePt v) (⊤ : Set _) := by
      rw [isGenericPoint_iff_specializes]
      exact fun x => ⟨fun _ => trivial, fun _ => ClosureComponent.closurePt_specializes v x⟩
    exact ((genericPoint_spec (ClosureComponent.closureScheme v)).eq hg)
  have hptV : ∃ x : ClosureComponent.closureScheme v,
      x ≠ genericPoint (ClosureComponent.closureScheme v) := by
    obtain ⟨y, hyv, hne⟩ := hpt
    rw [← ClosureComponent.range_closureι] at hyv
    obtain ⟨x, rfl⟩ := hyv
    refine ⟨x, fun hx => hne ?_⟩
    rw [hx, hgen, ClosureComponent.closureι_closurePt]
  obtain ⟨P, -⟩ := CurvesField.DualityScheme.exists_isSeparable_chartPair
    (ClosureComponent.closureι v ≫ q) hpV hdimV hptV
  -- the normalization of the component, covered by the preimages of the chart pair
  have : IsFinite (normalizationPointsMap
      ({ClosureComponent.closurePt v} : Set (ClosureComponent.closureScheme v))) :=
    isFinite_normalizationPointsMap (ClosureComponent.closureι v ≫ q)
  have := hpV.isProper
  set π := normalizationPointsMap
    ({ClosureComponent.closurePt v} : Set (ClosureComponent.closureScheme v)) with hπ
  have hc := structureCoeff_comp (ClosureComponent.closureι v ≫ q) π
  unfold componentGenus
  rw [← hc]
  have h₀ : IsAffineOpen (π ⁻¹ᵁ P.U₀) := P.isAffineOpen₀.preimage π
  have h₁ : IsAffineOpen (π ⁻¹ᵁ P.U₁) := P.isAffineOpen₁.preimage π
  have h₀₁ : IsAffineOpen (π ⁻¹ᵁ P.U₀ ⊓ π ⁻¹ᵁ P.U₁) := P.isAffineOpen_inf.preimage π
  have hsup : π ⁻¹ᵁ P.U₀ ⊔ π ⁻¹ᵁ P.U₁ = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, P.sup_eq_top, Scheme.Hom.preimage_top]
  have hχ := CurvesField.DualityScheme.eulerCharOf_eq_of_pair
    (SheafOfModules.unit (normalizationPoints
      ({ClosureComponent.closurePt v} : Set (ClosureComponent.closureScheme v))).ringCatSheaf)
    (structureCoeff (π ≫ ClosureComponent.closureι v ≫ q)) hsup h₀ h₁ h₀₁
  rw [CurvesField.DualityScheme.eulerCharOf_unit] at hχ
  have h0 := finrank_cohomology_zero_of_isIntegral (π ≫ ClosureComponent.closureι v ≫ q)
  rw [arithmeticGenus, hχ, h0]
  omega

end ComponentGenusNonneg

end DeJongAlterations.StableModification.BlowDown.ExcSpecialize
