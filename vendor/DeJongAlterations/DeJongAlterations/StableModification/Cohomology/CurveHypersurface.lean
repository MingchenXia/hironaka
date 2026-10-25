/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.Valuation
import DeJongAlterations.StableModification.Cohomology.CurveCover
import DeJongAlterations.Geometry.AffineBlowupIsomorphism
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.GroupTheory.CosetCover
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Two hyperplanes without common zero on the closed fibre of a projective curve

Let `A` be a local ring with infinite residue field `k` and `X ⊆ ℙⁿ_A` a closed subscheme whose
closed fibre `X_k` has dimension at most one. Then there are two linear forms `f, g` without
common zero on `X_k` (`exists_linearForms_closedFibre`). Consequently (lane COH3A,
`isZero_cechCohomology_of_hypersurfaces_closedFibre`) `X` is the union of the two affine opens
`X ∩ D₊(f)` and `X ∩ D₊(g)`, the Čech cohomology of every quasi-coherent module vanishes in degrees
`≥ 2`, and over a valuation ring with infinite residue field the Mumford complex of a projective
curve is a two-term complex `K⁰ → K¹` of finite free modules
(`ProjectiveCoordinates.exists_twoTerm_mumfordComplex_of_closedFibre`).

This is the input of Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Lemma 4.4.2 and Proposition 4.4.6 (`semi-stable.tex` lines 3120–3131 and 3212–3219),
where the cohomology of projective curves over a valuation ring `V` (with algebraically closed,
hence infinite, residue field) is computed by a two-term complex; Temkin uses Noetherian
approximation and EGA III, we use the complex of `sm-cohomology-valuation.tex`.

## The argument

* *Prime avoidance for linear forms* (`exists_linearCombination_X_notMem`): finitely many prime
  ideals `P_j` of `A[T₀, …, Tₙ]` not containing all `Tᵢ` avoid a common linear form (so finitely
  many points of `ℙⁿ_A` lie in a common `D₊(f)`, `exists_linearForm_mem_basicOpen`). Otherwise
  `Aⁿ⁺¹` is the union of the finitely many submodules `W_j = {c | ∑ cᵢ Tᵢ ∈ P_j}`, so one of
  them has finite index (B. H. Neumann's lemma, `Submodule.exists_finiteIndex_of_cover`); but
  `t ↦ t·e_i` embeds `k` into `Aⁿ⁺¹ / W_j` for an index `i` with `Tᵢ ∉ P_j`, and `k` is
  infinite.
* *Topology of the closed fibre* (`exists_finite_specializes`,
  `finite_inter_of_disjoint`): the closed fibre `Z` is a Noetherian space (it is of finite type
  over `k`), so it has finitely many generic points of irreducible components, and every point of
  `Z` is a specialization of one of them. If `Z` has no chains `x ⤳ y ⤳ z` of three distinct
  points, a closed set `W` containing none of these generic points meets `Z` in a finite set: a
  point of `W ∩ Z` which specializes further inside `W ∩ Z` would give a chain of length two.
* *Choice of `f` and `g`*: `f` avoids the generic points of `Z`, so `Z ∩ V₊(f)` is finite, and `g`
  avoids the finitely many points of `Z ∩ V₊(f)`.

Blueprint: `sm-cohomology-stein.tex`, `lem:sm-linear-avoidance`, `lem:sm-proj-points`,
`lem:sm-closed-fibre-generic`, `lem:sm-closed-fibre-dimension`, `prop:sm-curve-hyperplanes`,
`cor:sm-val-curve-two-term`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

section LinearForms

variable {A : Type u} [CommRing A] [IsLocalRing A] {n : ℕ}

omit [IsLocalRing A] in
/-- A linear form `∑ cᵢ Tᵢ` is homogeneous of degree one. -/
theorem linearCombination_X_mem_grading (c : Fin (n + 1) → A) :
    Fintype.linearCombination A (fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) A)) c ∈
      projectiveSpaceGrading A n 1 := by
  rw [Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (isHomogeneous_X A i)

/-- A constant `C a` lies in a proper ideal `P` containing `C 𝔪` only if `a ∈ 𝔪`. -/
theorem mem_maximalIdeal_of_C_mem {P : Ideal (MvPolynomial (Fin (n + 1)) A)} (hP : P ≠ ⊤)
    {a : A} (ha : C a ∈ P) : a ∈ maximalIdeal A := by
  by_contra h
  have hu : IsUnit (C a : MvPolynomial (Fin (n + 1)) A) := by
    refine IsUnit.map C ?_
    by_contra h'
    exact h ((mem_maximalIdeal a).mpr h')
  exact hP (Ideal.eq_top_of_isUnit_mem _ ha hu)

/-- **Prime avoidance for linear forms** over a local ring with infinite residue field: finitely
many prime ideals of `A[T₀, …, Tₙ]` which do not contain all the variables avoid a common linear
form `∑ cᵢ Tᵢ`. (Typically the primes are the homogeneous primes of points of the closed fibre of
`ℙⁿ_A`.) -/
theorem exists_linearCombination_X_notMem [Infinite (ResidueField A)] {ι : Type*}
    (s : Finset ι) (P : ι → Ideal (MvPolynomial (Fin (n + 1)) A)) (hP : ∀ j ∈ s, (P j).IsPrime)
    (hrel : ∀ j ∈ s, ∃ i, X i ∉ P j) :
    ∃ c : Fin (n + 1) → A, ∀ j ∈ s,
      Fintype.linearCombination A (fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) A))
        c ∉ P j := by
  set lin := Fintype.linearCombination A
    (fun i : Fin (n + 1) => (X i : MvPolynomial (Fin (n + 1)) A))
  by_contra hcon
  push Not at hcon
  let W : ι → Submodule A (Fin (n + 1) → A) := fun j => ((P j).restrictScalars A).comap lin
  have hcov : ⋃ j ∈ s, (W j : Set (Fin (n + 1) → A)) = Set.univ := by
    refine Set.eq_univ_of_forall fun c => ?_
    obtain ⟨j, hj, hc⟩ := hcon c
    exact Set.mem_biUnion hj hc
  obtain ⟨j, hj, hfi⟩ := Submodule.exists_finiteIndex_of_cover hcov
  obtain ⟨i, hi⟩ := hrel j hj
  have hfin : Finite ((Fin (n + 1) → A) ⧸ (W j).toAddSubgroup) :=
    AddSubgroup.finite_quotient_of_finiteIndex
  let σ : ResidueField A → A := Function.surjInv residue_surjective
  let g : ResidueField A → (Fin (n + 1) → A) ⧸ (W j).toAddSubgroup :=
    fun t => QuotientAddGroup.mk (Pi.single i (σ t))
  have hg : Function.Injective g := by
    intro t t' htt'
    rw [QuotientAddGroup.eq] at htt'
    have hmem : lin (-Pi.single i (σ t) + Pi.single i (σ t')) ∈ P j := htt'
    have hlin : lin (-Pi.single i (σ t) + Pi.single i (σ t')) = C (σ t' - σ t) * X i := by
      rw [map_add, map_neg]
      simp only [lin, Fintype.linearCombination_apply_single, smul_eq_C_mul, map_sub]
      ring
    rw [hlin] at hmem
    have hC : C (σ t' - σ t) ∈ P j := ((hP j hj).mem_or_mem hmem).resolve_right hi
    have hmax := mem_maximalIdeal_of_C_mem (hP j hj).ne_top hC
    have : residue A (σ t') = residue A (σ t) := by
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      exact hmax
    simpa only [σ, Function.surjInv_eq residue_surjective] using this.symm
  have := Finite.of_injective g hg
  exact not_finite (ResidueField A)

end LinearForms

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} [CommRing A] {n : ℕ}

/-- The image of a point `y` of `ℙⁿ_A` in `Spec A` is the prime `{a | C a ∈ P_y}`, `P_y` the
homogeneous prime of `y`. -/
theorem mem_projectiveSpaceStructure_asIdeal_iff (y : Proj (projectiveSpaceGrading A n)) (a : A) :
    a ∈ (projectiveSpaceStructure A n y).asIdeal ↔ C a ∈ y.asHomogeneousIdeal := by
  have h := proj_toSpecZero_preimage_basicOpen (projectiveSpaceGrading A n)
    (projectiveSpaceDegreeZeroEquiv A n a)
  have hy := congrArg (fun U : (Proj (projectiveSpaceGrading A n)).Opens => y ∈ U) h
  simp only [eq_iff_iff] at hy
  exact not_iff_not.mp hy

/-- A point of `ℙⁿ_A` does not contain all the variables in its homogeneous prime. -/
theorem exists_X_notMem_asHomogeneousIdeal (y : Proj (projectiveSpaceGrading A n)) :
    ∃ i, (X i : MvPolynomial (Fin (n + 1)) A) ∉ y.asHomogeneousIdeal := by
  by_contra h
  push Not at h
  apply y.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro d hd a ha
  have ha' : (a : MvPolynomial (Fin (n + 1)) A).IsHomogeneous d := ha
  have hspan : a ∈ Ideal.span ((X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A) '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro m hm
    by_contra hall
    push Not at hall
    have hm0 : m = 0 := Finsupp.ext fun i => hall i (Set.mem_univ i)
    have := ha' (mem_support_iff.mp hm)
    rw [hm0, map_zero] at this
    omega
  exact (Ideal.span_le.mpr (by rintro _ ⟨i, -, rfl⟩; exact h i)) hspan

variable [IsLocalRing A] [Infinite (ResidueField A)]

/-- **Finitely many points of `ℙⁿ_A` lie in a common `D₊(f)`, `f` linear**, over a local ring with
infinite residue field. -/
theorem exists_linearForm_mem_basicOpen {ι : Type*} (s : Finset ι)
    (y : ι → Proj (projectiveSpaceGrading A n)) :
    ∃ f ∈ projectiveSpaceGrading A n 1, ∀ j ∈ s,
      y j ∈ Proj.basicOpen (projectiveSpaceGrading A n) f := by
  obtain ⟨c, hc⟩ := exists_linearCombination_X_notMem s (fun j => (y j).asHomogeneousIdeal.toIdeal)
    (fun j _ => (y j).isPrime) (fun j _ => exists_X_notMem_asHomogeneousIdeal (y j))
  exact ⟨_, linearCombination_X_mem_grading c, fun j hj => hc j hj⟩

end ProjectiveSpace

section Topology

open TopologicalSpace

variable {T : Type*} [TopologicalSpace T] [QuasiSober T]

/-- **Generic points of a Noetherian closed subset**: a closed subset `Z` of a quasi-sober space
which is Noetherian (as a subspace) contains a finite set `G` of points such that every point of
`Z` is a specialization of a point of `G` (the generic points of the irreducible components). -/
theorem exists_finite_specializes {Z : Set T} (hZ : IsClosed Z) [NoetherianSpace Z] :
    ∃ G : Set T, G.Finite ∧ G ⊆ Z ∧ ∀ z ∈ Z, ∃ η ∈ G, η ⤳ z := by
  rcases Z.eq_empty_or_nonempty with hZe | ⟨z₀, hz₀⟩
  · exact ⟨∅, Set.finite_empty, Set.empty_subset _, fun z hz => by simp [hZe] at hz⟩
  have : Nonempty T := ⟨z₀⟩
  have key : ∀ C ∈ irreducibleComponents Z, ∃ η ∈ Z, ∀ z ∈ C, η ⤳ (z : T) := by
    intro C hC
    have hS : IsIrreducible (closure ((↑) '' C : Set T)) :=
      (hC.1.image _
        continuous_subtype_val.continuousOn).closure
    obtain ⟨η, hη⟩ := QuasiSober.sober hS isClosed_closure
    have hsub : closure ((↑) '' C : Set T) ⊆ Z :=
      closure_minimal (by rintro _ ⟨z, -, rfl⟩; exact z.2) hZ
    refine ⟨η, hsub hη.mem, fun z hz => ?_⟩
    rw [specializes_iff_mem_closure, hη.def]
    exact subset_closure ⟨z, hz, rfl⟩
  choose! η hηZ hη using key
  refine ⟨η '' irreducibleComponents Z,
    NoetherianSpace.finite_irreducibleComponents.image _, ?_, fun z hz => ?_⟩
  · rintro _ ⟨C, hC, rfl⟩
    exact hηZ C hC
  · obtain ⟨C, hC, hzC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
      {(⟨z, hz⟩ : Z)} isIrreducible_singleton
    exact ⟨η C, ⟨C, hC, rfl⟩, hη C hC ⟨z, hz⟩ (hzC rfl)⟩

/-- **Closed sets avoiding the generic points of a curve are finite**: let `Z` be a Noetherian
closed subset of a quasi-sober space without chains `x ⤳ y ⤳ z` of three distinct points
starting in `Z` (dimension at most one), and `G ⊆ Z` a set of which every point of `Z` is a
specialization. Then a closed set `W` disjoint from `G` meets `Z` in a finite set. -/
theorem finite_inter_of_disjoint {Z : Set T} (hZ : IsClosed Z) [NoetherianSpace Z]
    (hdim : ∀ x ∈ Z, ∀ y z : T, x ⤳ y → y ⤳ z → x = y ∨ y = z) {G : Set T} (hGZ : G ⊆ Z)
    (hG : ∀ z ∈ Z, ∃ η ∈ G, η ⤳ z) {W : Set T} (hW : IsClosed W) (hGW : Disjoint G W) :
    (Z ∩ W).Finite := by
  have : NoetherianSpace (Z ∩ W : Set T) := by
    rw [noetherianSpace_set_iff] at *
    exact fun t ht => ‹∀ t ⊆ Z, IsCompact t› t (ht.trans Set.inter_subset_left)
  obtain ⟨G', hG'fin, hG'sub, hG'⟩ := exists_finite_specializes (hZ.inter hW)
  refine hG'fin.subset fun w hw => ?_
  obtain ⟨ξ, hξ, hξw⟩ := hG' w hw
  obtain ⟨η, hη, hηξ⟩ := hG ξ (hG'sub hξ).1
  have hne : η ≠ ξ := fun h => hGW.ne_of_mem hη (hG'sub hξ).2 h
  rcases hdim η (hGZ hη) ξ w hηξ hξw with h | h
  · exact absurd h hne
  · exact h ▸ hξ

end Topology

section ClosedFibre

attribute [local instance] MvPolynomial.gradedAlgebra

open TopologicalSpace

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} {n : ℕ}

set_option backward.isDefEq.respectTransparency.types false in
/-- The closed fibre of a quasi-compact scheme of finite type over a local ring is a Noetherian
space (it is homeomorphic to the scheme-theoretic fibre, of finite type over the residue
field). -/
theorem noetherianSpace_closedFibre (p : X ⟶ Spec (CommRingCat.of A)) [LocallyOfFiniteType p]
    [QuasiCompact p] : NoetherianSpace (p ⁻¹' {closedPoint A}) := by
  have : LocallyOfFiniteType (p.fiberToSpecResidueField (closedPoint A)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : AlgebraicGeometry.IsNoetherian (p.fiber (closedPoint A)) :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian (p.fiberToSpecResidueField (closedPoint A)) }
  exact (noetherianSpace_iff_of_homeomorph (p.fiberHomeo _)).mp inferInstance

omit [IsLocalRing A] in
/-- A `T₀` space with a chain `c ⤳ b ⤳ a` of three distinct points has Krull dimension at least
two (for the specialization order). -/
theorem two_le_krullDim_of_specializes {T : Type*} [TopologicalSpace T] [T0Space T] {a b c : T}
    (hba : b ⤳ a) (hcb : c ⤳ b) (hab : a ≠ b) (hbc : b ≠ c) :
    letI := specializationOrder T
    (2 : WithBot ℕ∞) ≤ Order.krullDim T := by
  let := specializationOrder T
  have h₁ : a < b := lt_of_le_of_ne hba hab
  have h₂ : b < c := lt_of_le_of_ne hcb hbc
  let q : LTSeries T := ⟨2, ![a, b, c], fun i => by fin_cases i <;> simp [h₁, h₂]⟩
  exact Order.LTSeries.length_le_krullDim q

/-- **Dimension of the closed fibre**: if the scheme-theoretic closed fibre of
`p : X → Spec A` has topological Krull dimension at most one, there are no chains `x ⤳ y ⤳ z` of
three distinct points of `X` starting in the closed fibre. -/
theorem eq_or_eq_of_topologicalKrullDim_fiber_le_one (p : X ⟶ Spec (CommRingCat.of A))
    (hdim : topologicalKrullDim (p.fiber (closedPoint A)) ≤ 1) (x y z : X)
    (hx : p x = closedPoint A) (hxy : x ⤳ y) (hyz : y ⤳ z) : x = y ∨ y = z := by
  have hcl := isClosed_singleton_closedPoint A
  have hy : p y = closedPoint A := (hxy.map p.continuous).mem_closed hcl hx
  have hz : p z = closedPoint A := (hyz.map p.continuous).mem_closed hcl hy
  by_contra h
  push Not at h
  let e := (p.fiberHomeo (closedPoint A)).symm
  have hi : Topology.IsInducing (Subtype.val : (p ⁻¹' {closedPoint A} : Set X) → X) :=
    Topology.IsInducing.subtypeVal
  have hxy' : e ⟨x, hx⟩ ⤳ e ⟨y, hy⟩ := (hi.specializes_iff.mp hxy).map e.continuous
  have hyz' : e ⟨y, hy⟩ ⤳ e ⟨z, hz⟩ := (hi.specializes_iff.mp hyz).map e.continuous
  have hne₁ : e ⟨z, hz⟩ ≠ e ⟨y, hy⟩ := fun h' => h.2 (congrArg Subtype.val (e.injective h')).symm
  have hne₂ : e ⟨y, hy⟩ ≠ e ⟨x, hx⟩ := fun h' => h.1 (congrArg Subtype.val (e.injective h')).symm
  have h2 := two_le_krullDim_of_specializes hyz' hxy' hne₁ hne₂
  rw [← Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints] at h2
  exact absurd (h2.trans hdim) (by decide)

variable [Infinite (ResidueField A)]

/-- **Two hyperplanes without common zero on the closed fibre of a projective curve**: let `A` be
a local ring with infinite residue field and `i : X → ℙⁿ_A` a closed immersion whose closed fibre
has no chains `x ⤳ y ⤳ z` of three distinct points (dimension at most one). Then there are two
linear forms `f`, `g` such that `X ∩ D₊(f)` and `X ∩ D₊(g)` cover the closed fibre of `X`. -/
theorem exists_linearForms_closedFibre (i : X ⟶ projectiveSpace A n) [IsClosedImmersion i]
    (hdim : ∀ x y z : X, (i ≫ projectiveSpaceStructure A n) x = closedPoint A →
      x ⤳ y → y ⤳ z → x = y ∨ y = z) :
    ∃ f ∈ projectiveSpaceGrading A n 1, ∃ g ∈ projectiveSpaceGrading A n 1,
      ∀ x : X, (i ≫ projectiveSpaceStructure A n) x = closedPoint A →
        x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f ⊔
          i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) g := by
  set p := i ≫ projectiveSpaceStructure A n
  have hZ : IsClosed (p ⁻¹' {closedPoint A}) :=
    (isClosed_singleton_closedPoint A).preimage p.continuous
  have := noetherianSpace_closedFibre p
  obtain ⟨G, hGfin, hGZ, hG⟩ := exists_finite_specializes hZ
  obtain ⟨f, hf, hfG⟩ := exists_linearForm_mem_basicOpen hGfin.toFinset
    (fun x => (i x : Proj (projectiveSpaceGrading A n)))
  set W : Set X := ((i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f : X.Opens) : Set X)ᶜ
  have hW : IsClosed W :=
    (i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f).isOpen.isClosed_compl
  have hGW : Disjoint G W :=
    Set.disjoint_left.mpr fun x hx hxW => hxW (hfG x (hGfin.mem_toFinset.mpr hx))
  have hfin := finite_inter_of_disjoint hZ (fun x hx y z => hdim x y z hx) hGZ hG hW hGW
  obtain ⟨g, hg, hgW⟩ := exists_linearForm_mem_basicOpen hfin.toFinset
    (fun x => (i x : Proj (projectiveSpaceGrading A n)))
  refine ⟨f, hf, g, hg, fun x hx => ?_⟩
  rw [TopologicalSpace.Opens.mem_sup]
  by_cases hxf : x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f
  · exact Or.inl hxf
  · exact Or.inr (hgW x (hfin.mem_toFinset.mpr ⟨hx, hxf⟩))

/-- **Two hyperplanes from the dimension of the closed fibre**: as
`exists_linearForms_closedFibre`, with the hypothesis that the scheme-theoretic closed fibre has
topological Krull dimension at most one. -/
theorem exists_linearForms_of_topologicalKrullDim_le_one (i : X ⟶ projectiveSpace A n)
    [IsClosedImmersion i]
    (hdim : topologicalKrullDim ((i ≫ projectiveSpaceStructure A n).fiber (closedPoint A)) ≤ 1) :
    ∃ f ∈ projectiveSpaceGrading A n 1, ∃ g ∈ projectiveSpaceGrading A n 1,
      ∀ x : X, (i ≫ projectiveSpaceStructure A n) x = closedPoint A →
        x ∈ i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) f ⊔
          i ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading A n) g :=
  exists_linearForms_closedFibre i (eq_or_eq_of_topologicalKrullDim_fiber_le_one _ hdim)

/-- **Projective curves over a local base have Čech cohomology in degrees `≤ 1`**: let `A` be a
local ring with infinite residue field and `i : X → ℙⁿ_A` a closed immersion (with `X` of affine
diagonal) whose closed fibre has dimension at most one. Then `Ȟᵖ(U, F) = 0` for `p ≥ 2`, every
finite cover `U` of `X` by affine opens and every quasi-coherent `F`. -/
theorem isZero_cechCohomology_of_topologicalKrullDim_le_one
    [IsAffineHom (pullback.diagonal (terminal.from X))] (i : X ⟶ projectiveSpace A n)
    [IsClosedImmersion i]
    (hdim : topologicalKrullDim ((i ≫ projectiveSpaceStructure A n).fiber (closedPoint A)) ≤ 1)
    {R : Type u} [CommRing R] (F : X.Modules) [F.IsQuasicoherent] (c : R →+* Γ(X, ⊤))
    {ι : Type u} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (hUa : ∀ i, IsAffineOpen (U i)) (p : ℕ) (hp : 2 ≤ p) : IsZero (cechCohomology F U c p) := by
  obtain ⟨f, hf, g, hg, hcov⟩ := exists_linearForms_of_topologicalKrullDim_le_one i hdim
  exact isZero_cechCohomology_of_hypersurfaces_closedFibre F c i
    (i ≫ projectiveSpaceStructure A n) U hU hUa f g hf one_pos hg one_pos hcov p hp

end ClosedFibre

section MumfordCurve

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}} {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  [Infinite (ResidueField V)] {p : X ⟶ Spec (CommRingCat.of V)}

namespace ProjectiveCoordinates

variable (D : ProjectiveCoordinates X V (structureCoeff p)) (F : X.Modules) [F.IsQuasicoherent]
  (hF : ∀ i, Module.Finite Γ(X, D.U i) Γ(F, D.U i))
  (hflat : ∀ i, Module.Flat V (sectionsModuleCat F (structureCoeff p) (D.U i) le_top))

include hF hflat in
/-- **The two-term Mumford complex of a projective curve over a valuation ring** (blueprint
`cor:sm-val-curve-two-term`): let `V` be a valuation ring with infinite residue field (e.g.
algebraically closed), `p : X → Spec V` with a closed immersion `i : X → ℙⁿ_V` over `V` (`X` with
affine diagonal) whose closed fibre has dimension at most one, `D` projective coordinates over `V`
and `F` quasi-coherent with finite `V`-flat sections on the charts. Then there are a two-term
complex `K⁰ → K¹` of finite free `V`-modules and a universal quasi-isomorphism `K → Č(U, F)`;
in particular `Hʲ(K ⊗_V B) ≅ Ȟʲ(X_B, F_B)` for every `V → B`. -/
theorem exists_twoTerm_mumfordComplex_of_closedFibre
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    {n : ℕ} (i : X ⟶ projectiveSpace V n) [IsClosedImmersion i]
    (hp : i ≫ projectiveSpaceStructure V n = p)
    (hdim : topologicalKrullDim (p.fiber (closedPoint V)) ≤ 1) :
    ∃ (K : CochainComplex (ModuleCat.{u} V) ℕ) (γ : K ⟶ cechComplex F D.U (structureCoeff p)),
      IsUnivQuasiIso γ ∧ (∀ k, Module.Finite V (K.X k)) ∧ (∀ k, Module.Free V (K.X k)) ∧
      (∀ k, 1 < k → IsZero (K.X k)) ∧
      ∀ (B : Type u) [CommRing B] (φ : V →+* B) (j : ℕ),
        Nonempty (((baseChange φ).obj K).homology j ≅
          cechCohomology ((Scheme.Modules.pullback (bcFst φ p)).obj F)
            (fun l => bcFst φ p ⁻¹ᵁ D.U l) (structureCoeff (bcSnd φ p)) j) := by
  subst hp
  obtain ⟨f, hf, g, hg, hcov⟩ := exists_linearForms_of_topologicalKrullDim_le_one i hdim
  exact D.exists_twoTerm_mumfordComplex_of_hypersurfaces F hF hflat i f g hf one_pos hg one_pos hcov

end ProjectiveCoordinates

end MumfordCurve

end

end DeJongAlterations.StableModification.Cohomology
