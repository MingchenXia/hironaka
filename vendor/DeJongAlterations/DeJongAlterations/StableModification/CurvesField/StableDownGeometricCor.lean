/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDownGeometricGraph

/-!
# Contracting a semi-stable subcurve to an ordinary point (Temkin, Cor. B.2, scheme level)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, l. 4435–4467), Corollary B.2
(`stabdowncor`): let `f : C' → C` be a proper morphism of reduced projective curves over an
algebraically closed field `k` with `p_a(C') = p_a(C)`, an isomorphism off `Z = f⁻¹(x)` for a closed
point `x`, and let `Z` be a connected curve in the semi-stable locus of `C'`. Then `x` is an
ordinary `n`-fold point if and only if `Z` is a `ℙ¹_k`-tree with `|∂Z| = n`.

## Main results

* `stabdown_scheme`: in the situation above (with `C'` semi-stable along `Z`: every closed point of
  `Z` is a smooth point or an ordinary double point of `C'`; `Z` a connected curve; the component
  genera `g(v) = p_a(C̃'_v)` nonnegative), for an affine open `V ∋ x`, `A = 𝒪_{C,x} = Γ(V, 𝒪_C)_𝔭`
  and `B = Γ(b⁻¹V, 𝒪_N)_𝔭` the semilocal ring over `x` of the normalization `b : N → C` of `C'` in
  its components not in `Z`:
  - `B` has exactly `|∂Z|` maximal ideals (`|x̃| = |∂Z|`, `∂Z` the boundary double points of the
    incidence graph `nodalGraph` of `C'` along `Z`), and
  - `A` is the gluing ring `{b ∈ B | b(x̃₁) = ⋯ = b(x̃ₙ) ∈ k}` (`x` is an ordinary `|∂Z|`-fold point
    in gluing form) if and only if the components of `Z` form a `ℙ¹`-tree in `nodalGraph`.
* `stabdown_scheme_of_isP1Tree`: the usable variant for a possibly disconnected `Z` (ERRATA DJA-O7):
  if the components of `Z` are partitioned into families with pairwise disjoint unions, each a
  `ℙ¹`-tree, then there is at most one family (`Z` is connected) and `x` is ordinary.
* `finite_local_inputs`, `outer_local_inputs`: the local hypotheses of the gluing criterion
  (`stabdown_gluing_iff_of_isAlgClosed`) at a closed point `x` for a finite `π : Y → X` with
  `𝒪_X → π_*𝒪_Y` injective and finite-dimensional cokernel (e.g. `b`, or the normalization of
  `C`): `A` is local with residue field `k` (Nullstellensatz), `B` is integral over `A` with
  finitely many maximal ideals, one for each point of `π⁻¹(x)`, `B / A` is finite-dimensional,
  and its dimension is `δ_π(x)`.
* `eq_gluing_of_isGeometricOrdinaryDoublePoint`, `eq_gluing_of_isSmoothAt`: an ordinary double
  point (smooth point) of a reduced curve over `k = k̄` is an ordinary `2`-fold (`1`-fold) point in
  gluing form (blueprint `lem:sm-ordinary-completion`, "⇒" for `n = 2, 1`).
* `finite_nodesIn`: a reduced projective curve has finitely many ordinary double points.

The semi-stable inputs are `CurvesField.StableDownGeometricLocal` (`δ = 1` at double points, `0`
at smooth points) and `CurvesField.StableDownGeometricGraph` (the incidence graph, its boundary,
the branch count and connectedness); the δ-count is CRV3's
`deltaInvariant_contraction_of_arithmeticGenus_eq`.

The ring `B` is the semilocal ring of `N`, the normalization of `C'` in its components other than
those of `Z`; `N` is the normalization `C̃` of `C` over `C`
(`CurvesField.StableDownGeometricNormalization`, `outerNormalizationIso`), where the corollaries
are restated with `C̃` (`stabdown_scheme_normalization`).

Blueprint: `sm-curves-fields-stabdown.tex`, `lem:sm-stabdown-outer-local`,
`lem:sm-ordinary-completion-gluing`, `lem:sm-stabdown-partition`, `lem:sm-stabdown-delta-graph`,
`lem:sm-stabdown-graph-connected`, `cor:sm-stabdown-scheme-proof`, `cor:sm-stabdown-scheme-tree`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Module IsLocalRing
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion

set_option autoImplicit false

universe u

noncomputable section

section LocalInputs

/-! ### The local hypotheses of the gluing criterion

`R = Γ(V, 𝒪_C)`, `B = Γ(b⁻¹V, 𝒪_N)` for a finite `b : N → C`, `P` a maximal ideal of `R`; the
local ring is the image `A` of `R_P` in `B_P` (`rangeIn`). -/

variable {k : Type*} [Field k] {R B : Type*} [CommRing R] [CommRing B] [Algebra k R]
  [Algebra R B] [Algebra k B] [IsScalarTower k R B] (P : Ideal R) [P.IsMaximal]

local notation "Rₚ" => Localization.AtPrime P
local notation "Bₚ" => Localization (Algebra.algebraMapSubmonoid B P.primeCompl)

/-- **The image of `R_P` in `B_P` is local** when `R → B` is injective. -/
theorem isLocalRing_rangeIn (hRB : Function.Injective (algebraMap R B)) :
    IsLocalRing (rangeIn k Rₚ Bₚ) := by
  have hinj := algebraMap_localization_injective P hRB
  have : Nontrivial Bₚ := hinj.nontrivial
  exact IsLocalRing.of_surjective'
    (IsScalarTower.toAlgHom k Rₚ Bₚ).rangeRestrict.toRingHom (AlgHom.rangeRestrict_surjective _)

/-- **`B_P` is integral over the image of `R_P`** when `B` is integral over `R`. -/
theorem isIntegral_rangeIn [Algebra.IsIntegral R B] :
    Algebra.IsIntegral (rangeIn k Rₚ Bₚ) Bₚ := by
  have : Algebra.IsIntegral Rₚ Bₚ :=
    ⟨isIntegral_localization (M := P.primeCompl) (Rₘ := Rₚ) (Sₘ := Bₚ)⟩
  let _ : Algebra Rₚ (rangeIn k Rₚ Bₚ) :=
    (IsScalarTower.toAlgHom k Rₚ Bₚ).rangeRestrict.toRingHom.toAlgebra
  have : IsScalarTower Rₚ (rangeIn k Rₚ Bₚ) Bₚ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨fun b => (Algebra.IsIntegral.isIntegral (R := Rₚ) b).tower_top⟩

omit [Algebra R B] [Algebra k B] [IsScalarTower k R B] in
/-- **The residue field at a closed point is `k`** (Nullstellensatz): for `R` of finite type over
an algebraically closed field `k` and `P` maximal, every `a ∈ R_P` is congruent to a constant
modulo the maximal ideal. -/
theorem exists_sub_mem_maximalIdeal_localization [IsAlgClosed k] [Algebra.FiniteType k R]
    (a : Rₚ) : ∃ c : k, a - algebraMap k Rₚ c ∈ maximalIdeal Rₚ := by
  obtain ⟨r, hr⟩ := Ideal.algebraMap_residueField_surjective P (IsLocalRing.residue Rₚ a)
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  have : Algebra.FiniteType k (R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) (Ideal.Quotient.mkₐ_surjective k P)
  have : Module.Finite k (R ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ P)
  have : Algebra.IsIntegral k (R ⧸ P) := Algebra.IsIntegral.of_finite k _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ P)).2
    (Ideal.Quotient.mk P r)
  have hrc : r - algebraMap k R c ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, Ideal.Quotient.mk_algebraMap, hc, sub_self]
  refine ⟨c, ?_⟩
  have h1 := (IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ P _).2 hrc
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub] at h1
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
  have h2 : IsLocalRing.residue Rₚ (algebraMap R Rₚ r) = IsLocalRing.residue Rₚ a := hr
  rw [h2, ← IsScalarTower.algebraMap_apply k R Rₚ] at h1
  exact h1

/-- **The residue condition** for the image `A` of `R_P` in `B_P`: every element of `A` is
congruent to a constant modulo the maximal ideal (`R` of finite type over `k = k̄`). -/
theorem residue_rangeIn [IsAlgClosed k] [Algebra.FiniteType k R]
    (hRB : Function.Injective (algebraMap R B)) [IsLocalRing (rangeIn k Rₚ Bₚ)] :
    ∀ a : rangeIn k Rₚ Bₚ, ∃ c : k,
      a - algebraMap k (rangeIn k Rₚ Bₚ) c ∈ maximalIdeal (rangeIn k Rₚ Bₚ) := by
  rintro ⟨_, a, rfl⟩
  obtain ⟨c, hc⟩ := exists_sub_mem_maximalIdeal_localization (k := k) P a
  refine ⟨c, ?_⟩
  have hinj := algebraMap_localization_injective P hRB
  let e : Rₚ ≃+* rangeIn k Rₚ Bₚ := RingEquiv.ofBijective
    (IsScalarTower.toAlgHom k Rₚ Bₚ).rangeRestrict
    ⟨fun y z h => hinj (congrArg Subtype.val h), AlgHom.rangeRestrict_surjective _⟩
  have he : e (a - algebraMap k Rₚ c) =
      ⟨_, a, rfl⟩ - algebraMap k (rangeIn k Rₚ Bₚ) c := by
    apply Subtype.ext
    change algebraMap Rₚ Bₚ (a - algebraMap k Rₚ c) = algebraMap Rₚ Bₚ a - algebraMap k Bₚ c
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
  rw [← he, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff e]
  rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hc

/-- **`B_P / A` is finite-dimensional** when `B / R` is (`b_*𝒪_N / 𝒪_C` is a finite skyscraper). -/
theorem finiteDimensional_rangeIn [FiniteDimensional k (Coker R B)] :
    FiniteDimensional k (Bₚ ⧸ Subalgebra.toSubmodule (rangeIn k Rₚ Bₚ)) := by
  have h1 := (isLocalDecomposition (k := k) (A := R) (Coker R B)).finiteDimensional
    ⟨P, inferInstance⟩
  have : IsLocalizedModule P.primeCompl (cokerMap Rₚ Bₚ : Coker R B →ₗ[R] Coker Rₚ Bₚ) :=
    isLocalizedModule_cokerMap_of_submonoid P.primeCompl
  let e := IsLocalizedModule.iso P.primeCompl (cokerMap Rₚ Bₚ : Coker R B →ₗ[R] Coker Rₚ Bₚ)
  let e' : LocalizedModule P.primeCompl (Coker R B) ≃ₗ[k] Coker Rₚ Bₚ :=
    { e.toAddEquiv with
      map_smul' := fun c z => by
        change e (c • z) = c • e z
        rw [← algebraMap_smul R c z, map_smul, ← algebraMap_smul Rₚ c (e z),
          ← algebraMap_smul Rₚ (algebraMap k R c) (e z), ← IsScalarTower.algebraMap_apply] }
  have h2 : FiniteDimensional k (Coker Rₚ Bₚ) := Module.Finite.equiv e'
  have h : Subalgebra.toSubmodule (rangeIn k Rₚ Bₚ) =
      (LinearMap.range (Algebra.linearMap Rₚ Bₚ)).restrictScalars k := by
    ext b
    simp
  rw [h]
  exact Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv k _).symm

end LocalInputs

section Partition

/-! ### Partitions of a subcurve into separated families -/

variable {V : Type*} {E : Type*} {M : Type*} (Γ : IncidenceGraph V E M) [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M] {G : Finset V} {𝒴 : Finset (Finset V)}
  (hsub : ∀ Y ∈ 𝒴, Y ⊆ G) (hcov : ∀ v ∈ G, ∃ Y ∈ 𝒴, v ∈ Y)
  (hdisj : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → Disjoint Y Y')
  (hsep : ∀ e, ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, (∃ v ∈ Γ.ends e, v ∈ Y) → (∃ v ∈ Γ.ends e, v ∈ Y') → Y = Y')
  (hmeet : ∀ e, ∃ v ∈ Γ.ends e, v ∈ G)

/-- The double points meeting `Y` are its boundary and inner double points. -/
lemma mem_boundary_union_inner {Y : Finset V} {e : E} :
    e ∈ Γ.boundary Y ∪ Γ.inner Y ↔ ∃ v ∈ Γ.ends e, v ∈ Y := by
  rw [Finset.mem_union, mem_boundary, mem_inner]
  constructor
  · rintro (⟨h, -⟩ | h)
    · exact h
    · obtain ⟨a, b, hab⟩ := Γ.exists_ends e
      exact ⟨a, by simp [hab], h a (by simp [hab])⟩
  · intro h
    by_cases h' : ∀ v ∈ Γ.ends e, v ∈ Y
    · exact Or.inr h'
    · push Not at h'
      exact Or.inl ⟨h, h'⟩

lemma disjoint_boundary_inner (Y : Finset V) : Disjoint (Γ.boundary Y) (Γ.inner Y) := by
  rw [Finset.disjoint_left]
  intro e hb hi
  obtain ⟨-, v, hv, hvY⟩ := mem_boundary.1 hb
  exact hvY (mem_inner.1 hi v hv)

omit [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M] in
include hsub hcov hdisj in
/-- `G` is the disjoint union of the families. -/
lemma eq_biUnion_of_partition : G = 𝒴.biUnion id ∧ (𝒴 : Set (Finset V)).PairwiseDisjoint id := by
  refine ⟨?_, fun Y hY Y' hY' hne => hdisj Y hY Y' hY' hne⟩
  ext v
  simp only [Finset.mem_biUnion, id]
  exact ⟨hcov v, fun ⟨Y, hY, hv⟩ => hsub Y hY hv⟩

include hcov hsep hmeet in
/-- **Every double point meeting `G` meets exactly one family**:
`∑_Y (#∂Y + #inner(Y)) = #(double points)`. -/
lemma sum_card_boundary_add_card_inner :
    ∑ Y ∈ 𝒴, ((Γ.boundary Y).card + (Γ.inner Y).card) = Fintype.card E := by
  have hpd : (𝒴 : Set (Finset V)).PairwiseDisjoint fun Y => Γ.boundary Y ∪ Γ.inner Y := by
    intro Y hY Y' hY' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e h h'
    exact hne (hsep e Y hY Y' hY' ((mem_boundary_union_inner Γ).1 h)
      ((mem_boundary_union_inner Γ).1 h'))
  have hcov' : 𝒴.biUnion (fun Y => Γ.boundary Y ∪ Γ.inner Y) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun e => ?_
    obtain ⟨v, hv, hvG⟩ := hmeet e
    obtain ⟨Y, hY, hvY⟩ := hcov v hvG
    exact Finset.mem_biUnion.2 ⟨Y, hY, (mem_boundary_union_inner Γ).2 ⟨v, hv, hvY⟩⟩
  rw [← Finset.card_univ, ← hcov', Finset.card_biUnion hpd]
  exact Finset.sum_congr rfl fun Y _ =>
    (Finset.card_union_of_disjoint (disjoint_boundary_inner Γ Y)).symm

include hsub hcov hsep in
/-- **The boundary of `G` is the disjoint union of the boundaries of the families**. -/
lemma sum_card_boundary : ∑ Y ∈ 𝒴, (Γ.boundary Y).card = (Γ.boundary G).card := by
  have hpd : (𝒴 : Set (Finset V)).PairwiseDisjoint fun Y => Γ.boundary Y := by
    intro Y hY Y' hY' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e h h'
    exact hne (hsep e Y hY Y' hY' (mem_boundary.1 h).1 (mem_boundary.1 h').1)
  have heq : Γ.boundary G = 𝒴.biUnion fun Y => Γ.boundary Y := by
    ext e
    rw [Finset.mem_biUnion, mem_boundary]
    constructor
    · rintro ⟨⟨v, hv, hvG⟩, w, hw, hwG⟩
      obtain ⟨Y, hY, hvY⟩ := hcov v hvG
      exact ⟨Y, hY, mem_boundary.2 ⟨⟨v, hv, hvY⟩, w, hw, fun hwY => hwG (hsub Y hY hwY)⟩⟩
    · rintro ⟨Y, hY, hb⟩
      obtain ⟨⟨v, hv, hvY⟩, w, hw, hwY⟩ := mem_boundary.1 hb
      refine ⟨⟨v, hv, hsub Y hY hvY⟩, w, hw, fun hwG => ?_⟩
      obtain ⟨Y', hY', hwY'⟩ := hcov w hwG
      exact hwY ((hsep e Y hY Y' hY' ⟨v, hv, hvY⟩ ⟨w, hw, hwY'⟩) ▸ hwY')
  rw [heq, Finset.card_biUnion hpd]

include hsub hcov hdisj hsep hmeet in
/-- **The δ-count of `G` is the sum of the δ-counts of the families**. -/
lemma contractedDelta_eq_sum (hnodes : (Γ.boundary G).card + (Γ.inner G).card = Fintype.card E) :
    contractedDelta Γ G = ∑ Y ∈ 𝒴, contractedDelta Γ Y := by
  obtain ⟨hG, hpd⟩ := eq_biUnion_of_partition hsub hcov hdisj
  have h1 := sum_card_boundary_add_card_inner Γ hcov hsep hmeet
  have h2 : ∑ Y ∈ 𝒴, ∑ v ∈ Y, (Γ.genus v : ℤ) = ∑ v ∈ G, (Γ.genus v : ℤ) := by
    conv_rhs => rw [hG]
    rw [Finset.sum_biUnion hpd]
    rfl
  have h3 : ∑ Y ∈ 𝒴, Y.card = G.card := by
    conv_rhs => rw [hG]
    rw [Finset.card_biUnion hpd]
    rfl
  simp only [contractedDelta, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [h2]
  have h1' : (∑ Y ∈ 𝒴, ((Γ.boundary Y).card : ℤ)) + ∑ Y ∈ 𝒴, ((Γ.inner Y).card : ℤ) =
      (Γ.boundary G).card + (Γ.inner G).card := by
    rw [← Finset.sum_add_distrib]
    exact_mod_cast h1.trans hnodes.symm
  have h3' : (∑ Y ∈ 𝒴, (Y.card : ℤ)) = G.card := by exact_mod_cast h3
  rw [h3']
  linarith

end Partition

section Finiteness

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [CompactSpace X] [IsReduced X] {k : Type u} [Field k]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]

/-- **A reduced projective curve has finitely many ordinary double points** (they lie in the
finite support of the δ-invariant, where `δ = 1`); so the instance `Fintype (nodesIn q Z)` of the
results below is always available (`(finite_nodesIn q hdim hp Z).fintype`). -/
theorem finite_nodesIn (hdim : topologicalKrullDim X ≤ 1) (hp : IsProjectiveOver q) (Z : Set X) :
    (nodesIn q Z).Finite := by
  obtain ⟨-, hsupp, -⟩ := arithmeticGenus_eq_normalizationPoints q (genericPoints X) rfl hdim hp
  refine hsupp.subset fun z hz => ?_
  rw [Function.mem_support,
    (deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint q hdim z hz.2.1 hz.2.2.1 hz.2.2.2).1]
  exact one_ne_zero

end Finiteness

section FiniteLocal

variable {X Y : Scheme.{u}} {k : Type u} [Field k] (π : Y ⟶ X) [IsFinite π]
  (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]

/-- **The local hypotheses of the gluing criterion for a finite morphism** (Temkin, App. B,
l. 4384–4391). Let `π : Y → X` be finite, `X` locally of finite type over `k = k̄`, `x ∈ X` a
closed point in an affine open `V`, `R = Γ(V, 𝒪_X)`, `B = Γ(π⁻¹V, 𝒪_Y)`, `𝔭` the prime of `x`, and
assume `R → B` injective with `B / R` finite-dimensional. Then the image `A` of `R_𝔭 = 𝒪_{X,x}` in
`B_𝔭` is local with residue field `k`, `B_𝔭` is integral over `A` with finitely many maximal ideals,
as many as points of `π⁻¹(x)`, `B_𝔭 / A` is finite-dimensional and `δ_π(x) = dim_k B_𝔭 / A`. -/
theorem finite_local_inputs [IsAlgClosed k] (x : X) (hx : IsClosed {x}) (V : X.Opens)
    (hV : IsAffineOpen V) (hxV : x ∈ V) (hinj : Function.Injective (π.app V).hom)
    (hcoker : IsFiniteCoker (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)) (π.app V).hom) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := (π.app V).hom.toAlgebra
    letI := ((π.app V).hom.comp (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∃ (_ : IsLocalRing (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
        (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))))
      (_ : Algebra.IsIntegral (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
        (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))
        (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))
      (_ : FiniteDimensional k (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl) ⧸ Subalgebra.toSubmodule
        (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))))
      (_ : Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))),
      (∀ a : rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)), ∃ c : k,
        a - algebraMap k _ c ∈ maximalIdeal _) ∧
      Fintype.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) = Nat.card ↥(π ⁻¹' {x}) ∧
      deltaInvariant π (structureCoeff p) x =
        delta k (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid Γ(Y, π ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) := by
  let _ := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
  let _ := (π.app V).hom.toAlgebra
  let _ := ((π.app V).hom.comp (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hPmax : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.IsMaximal :=
    hV.primeIdealOf_isMaximal_of_isClosed ⟨x, hxV⟩ hx
  have : Module.Finite Γ(X, V) Γ(Y, π ⁻¹ᵁ V) := IsFinite.finite_app π V hV
  have : Algebra.FiniteType k Γ(X, V) :=
    Geometry.NormalizationFinite.affineSections_finiteType p ⟨V, hV⟩
  have : FiniteDimensional k (Coker Γ(X, V) Γ(Y, π ⁻¹ᵁ V)) := hcoker
  have hloc := isLocalRing_rangeIn (k := k) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal hinj
  have hfib : Finite ↥(π ⁻¹' {x}) := (π.finite_preimage_singleton x).to_subtype
  have hfinM : Finite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
      Γ(Y, π ⁻¹ᵁ V) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) :=
    Finite.of_equiv _ ((fiberEquivPrimes π V hV x hxV).trans
      (maximalSpectrumEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal).symm)
  let _ := Fintype.ofFinite (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
      Γ(Y, π ⁻¹ᵁ V) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))
  refine ⟨hloc, isIntegral_rangeIn (k := k) _, finiteDimensional_rangeIn (k := k) _,
    inferInstance, residue_rangeIn (k := k) _ hinj, ?_, ?_⟩
  · rw [← Nat.card_eq_fintype_card]
    exact (natCard_fiber_eq_natCard_maximalSpectrum π V hV x hxV hx).symm
  · exact deltaInvariant_eq_delta (π := π) (c := structureCoeff p) V hV x hxV

end FiniteLocal

section Nodes

variable {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
  [Finite (genericPoints X)] [IsReduced X] {k : Type u} [Field k]
  (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q]

/-- **An ordinary double point is an ordinary `2`-fold point in gluing form** (Temkin, App. B,
l. 4381–4397; blueprint `lem:sm-ordinary-completion`, "⇒" for `n = 2`): for a reduced curve `X`
over `k = k̄`, a closed point `z` which is not generic with `Ô_{X,z} ≅ k[[u, v]]/(uv)`, an affine
open `V ∋ z`, `A` the image of `𝒪_{X,z}` in the semilocal ring `B = Γ(π⁻¹V, 𝒪_{X̃})_𝔭` of the
normalization: `B` has two maximal ideals and `A` is the gluing ring of `B`. -/
theorem eq_gluing_of_isGeometricOrdinaryDoublePoint [IsAlgClosed k]
    (hdim : topologicalKrullDim X ≤ 1) (z : X) (hzc : IsClosed {z}) (hzg : z ∉ genericPoints X)
    (hnode : Geometry.IsGeometricOrdinaryDoublePoint q z) (V : X.Opens) (hV : IsAffineOpen V)
    (hzV : z ∈ V) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
      (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
        normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl))) = 2 ∧
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨z, hzV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints X),
              normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints X),
              normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl)) := by
  have : IsFinite (normalizationPointsMap (genericPoints X)) :=
    isFinite_normalizationPointsMap (S := genericPoints X) q
  let _ := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
    (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
      normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ :=
    finite_local_inputs (normalizationPointsMap (genericPoints X)) q z hzc V hV hzV
      (normalizationPoints_app_injective rfl V hV) (normalizationPoints_isFiniteCoker q rfl hdim V hV)
  have h1 := (deltaInvariant_eq_one_of_isGeometricOrdinaryDoublePoint q hdim z hzc hzg hnode).1
  have h2 := natCard_fiber_eq_two_of_isGeometricOrdinaryDoublePoint q hdim z hzc hzg hnode
  refine ⟨Nat.card_eq_fintype_card.trans (hcard.trans h2),
    ((delta_add_one_eq_card_iff_of_isLocalRing _ hres).1 ?_).2⟩
  rw [← hdelta, h1, hcard, h2]

/-- **A smooth point is an ordinary `1`-fold point in gluing form** (blueprint
`lem:sm-ordinary-completion`, "⇒" for `n = 1`): at a closed point `z`, not generic, at which the
reduced curve `X` is smooth over `k = k̄`, the semilocal ring `B` of the normalization over `z` is
local and `A = 𝒪_{X,z}` is its gluing ring (in fact `A = B`). -/
theorem eq_gluing_of_isSmoothAt [IsAlgClosed k] (hdim : topologicalKrullDim X ≤ 1) (z : X)
    (hzc : IsClosed {z}) (hzg : z ∉ genericPoints X) (hsm : DeJong.IsSmoothAt q z)
    (V : X.Opens) (hV : IsAffineOpen V) (hzV : z ∈ V) :
    letI := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
    letI := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
      (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
        normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (genericPoints X), normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl))) = 1 ∧
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨z, hzV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints X),
              normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (genericPoints X),
              normalizationPointsMap (genericPoints X) ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨z, hzV⟩).asIdeal.primeCompl)) := by
  have : LocallyOfFinitePresentation q := inferInstance
  have : IsFinite (normalizationPointsMap (genericPoints X)) :=
    isFinite_normalizationPointsMap (S := genericPoints X) q
  let _ := (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((normalizationPointsMap (genericPoints X)).app V).hom.toAlgebra
  let _ := (((normalizationPointsMap (genericPoints X)).app V).hom.comp
    (sectionsRingHom (structureCoeff q) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(X, V) Γ(normalizationPoints (genericPoints X),
      normalizationPointsMap (genericPoints X) ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ :=
    finite_local_inputs (normalizationPointsMap (genericPoints X)) q z hzc V hV hzV
      (normalizationPoints_app_injective rfl V hV) (normalizationPoints_isFiniteCoker q rfl hdim V hV)
  have h1 := (deltaInvariant_eq_zero_of_isSmoothAt q hdim z hzc hzg hsm).1
  have h2 := natCard_fiber_eq_one_of_isSmoothAt q hdim z hzc hzg hsm
  refine ⟨Nat.card_eq_fintype_card.trans (hcard.trans h2),
    ((delta_add_one_eq_card_iff_of_isLocalRing _ hres).1 ?_).2⟩
  rw [← hdelta, h1, hcard, h2]

end Nodes

section Corollary

variable {C C' : Scheme.{u}} (f : C' ⟶ C) (x : C) (U : C.Opens) (hU : ∀ y, y ∈ U ↔ y ≠ x)
  [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] {k : Type u} [Field k]
  [Finite (genericPoints C')]

include hU in
/-- **The local hypotheses of the gluing criterion at `x`** (Temkin, App. B, l. 4384–4391, for
the outer normalization `b : N → C`). For an affine open `V ∋ x`, `R = Γ(V, 𝒪_C)`,
`B = Γ(b⁻¹V, 𝒪_N)`, `𝔭` the prime of `x` and `A` the image of `R_𝔭 = 𝒪_{C,x}` in `B_𝔭`: `A` is
local with residue field `k`, `B_𝔭` is integral over `A` with finitely many maximal ideals, as
many as points of `b⁻¹(x)`, `B_𝔭 / A` is finite-dimensional and `δ_b(x) = dim_k B_𝔭 / A`. -/
theorem outer_local_inputs [IsAlgClosed k] [CompactSpace C'] [IsReduced C] [IsProper f]
    (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p] (p' : C' ⟶ Spec (.of k))
    [LocallyOfFiniteType p'] (hxg : x ∉ genericPoints C) (hx : IsClosed {x})
    (hdim : topologicalKrullDim C ≤ 1) (hdim' : topologicalKrullDim C' ≤ 1)
    (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((outerMap f x).app V).hom.toAlgebra
    letI := (((outerMap f x).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    ∃ (_ : IsLocalRing (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
        (Localization (Algebra.algebraMapSubmonoid
          Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))))
      (_ : Algebra.IsIntegral (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
        (Localization (Algebra.algebraMapSubmonoid
          Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))
        (Localization (Algebra.algebraMapSubmonoid
          Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))
      (_ : FiniteDimensional k (Localization (Algebra.algebraMapSubmonoid
          Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl) ⧸ Subalgebra.toSubmodule
        (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))))
      (_ : Fintype (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
          Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)))),
      (∀ a : rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)), ∃ c : k,
        a - algebraMap k _ c ∈ maximalIdeal _) ∧
      Fintype.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
          Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
          (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        Nat.card ↥(outerMap f x ⁻¹' {x}) ∧
      deltaInvariant (outerMap f x) (structureCoeff p) x =
        delta k (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) := by
  have : IsFinite (outerMap f x) := isFinite_outerNormalization f x U hU p' hdim' hx
  exact finite_local_inputs (outerMap f x) p x hx V hV hxV (outerMap_app_injective f x U hU hxg V hV)
    (outerMap_isFiniteCoker f x U hU p' p hxg hdim hdim' hx V hV)

omit [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] [Finite (genericPoints C')] in
/-- The components of `Z = f⁻¹(x)` are the generic points of `C'` in `Z`. -/
lemma coe_eq_genericPoints_inter {G : Finset C'} (hG : (G : Set C') = innerPoints f x) :
    (G : Set C') = genericPoints C' ∩ f ⁻¹' {x} := by
  rw [hG]
  rfl

omit [IsIso (f ∣_ U)] [IsAffineHom (pullback.diagonal (terminal.from C'))] [Finite (genericPoints C')] in
/-- The other components are the generic points of `C'` outside `Z`. -/
lemma outerPoints_eq_diff : outerPoints f x = genericPoints C' \ f ⁻¹' {x} :=
  rfl

omit [IsIso (f ∣_ U)] in
/-- The points of `N` over `x` are the points of the outer normalization over `Z`. -/
lemma outerMap_preimage_eq : outerMap f x ⁻¹' {x} =
    normalizationPointsMap (outerPoints f x) ⁻¹' (f ⁻¹' {x}) := by
  ext w
  exact Iff.rfl

open scoped Classical in
include hU in
/-- **The δ-count in incidence-graph form, from the semi-stable hypotheses** (Temkin, Cor. B.2,
l. 4442–4447): under the hypotheses of `deltaInvariant_contraction_of_arithmeticGenus_eq`, if
`Z = f⁻¹(x)` is a curve (every point of `Z` lies on a component of `C'` in `Z`), `C'` is
semi-stable along `Z` and the genera `g(v)` of the components of `Z` are nonnegative, then
`δ_b(x) = #∂Z + #inner(Z) + ∑_{v ∈ Z⁰} g(v) - |Z⁰|` in the incidence graph `nodalGraph` of `C'`
along `Z`, and `#b⁻¹(x) = #∂Z`. -/
theorem deltaInvariant_eq_contractedDelta_nodalGraph [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x)
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ v ∈ G, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] :
    (deltaInvariant (outerMap f x) (structureCoeff p) x : ℤ) =
        contractedDelta (nodalGraph p' hdim' (f ⁻¹' {x})) G ∧
      Nat.card ↥(outerMap f x ⁻¹' {x}) = ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card := by
  have : LocallyOfFinitePresentation p' := inferInstance
  have hG' := coe_eq_genericPoints_inter f x hG
  have hO := outerPoints_eq_diff f x
  have hδ := deltaInvariant_contraction_eq_ncard_nodes f x U hU p p' hfp hxg hx hdim hdim' hp hp'
    hpa G hG hnodal
  have hnodes := card_boundary_add_card_inner_nodalGraph p' hdim' hG' hO hcurve
  have hgen : ∑ v ∈ G, componentGenus (structureCoeff p') v =
      ∑ v ∈ G, ((nodalGraph p' hdim' (f ⁻¹' {x})).genus v : ℤ) :=
    Finset.sum_congr rfl fun v hv => (Int.toNat_of_nonneg (hg v hv)).symm
  refine ⟨?_, ?_⟩
  · rw [hδ, contractedDelta, hgen, ← hnodes]
    push_cast
    ring
  · rw [outerMap_preimage_eq]
    exact natCard_preimage_eq_card_boundary p' hdim' hG' hO hcurve hnodal

omit [IsIso (f ∣_ U)] in
open scoped Classical in
/-- **A connected curve `Z = f⁻¹(x)` is connected in the incidence graph.** -/
lemma isConnected_nodalGraph_fiber [CompactSpace C'] [IsReduced C'] (p' : C' ⟶ Spec (.of k))
    [LocallyOfFiniteType p'] (hx : IsClosed {x}) (hdim' : topologicalKrullDim C' ≤ 1)
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) (hZ : _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] :
    (nodalGraph p' hdim' (f ⁻¹' {x})).IsConnected G := by
  have hG' := coe_eq_genericPoints_inter f x hG
  have hZc : IsClosed (f ⁻¹' {x}) := hx.preimage f.continuous
  have hunion : (⋃ v ∈ G, closure ({v} : Set C')) = f ⁻¹' {x} := by
    refine Set.Subset.antisymm (Set.iUnion₂_subset fun v hv => closure_subset_of_mem hZc hG' hv)
      fun z hz => ?_
    obtain ⟨v, hv, hzv⟩ := hcurve z hz
    exact Set.mem_biUnion hv hzv
  have hGne : G.Nonempty := by
    obtain ⟨z, hz⟩ := hZ.nonempty
    obtain ⟨v, hv, -⟩ := hcurve z hz
    exact ⟨v, hv⟩
  exact isConnected_nodalGraph p' hdim' hZc hG' hnodal (Finset.Subset.refl G) hGne
    (hunion ▸ hZ.isPreconnected)

omit [IsIso (f ∣_ U)] in
open scoped Classical in
/-- **The counts for a separated family of subcurves of `Z`**: if the components `G` of `Z` are
partitioned into families `Y ∈ 𝒴` whose components pairwise do not meet, then the δ-count and the
boundary of `G` are the sums of those of the families. -/
lemma partition_nodalGraph [CompactSpace C'] [IsReduced C'] (p' : C' ⟶ Spec (.of k))
    [LocallyOfFiniteType p'] (hdim' : topologicalKrullDim C' ≤ 1) (G : Finset C')
    (hG : (G : Set C') = innerPoints f x) (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (𝒴 : Finset (Finset C')) (hsub : ∀ Y ∈ 𝒴, Y ⊆ G)
    (hcov : ∀ v ∈ G, ∃ Y ∈ 𝒴, v ∈ Y)
    (hsep : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → ∀ v ∈ Y, ∀ v' ∈ Y',
      Disjoint (closure ({v} : Set C')) (closure {v'})) :
    contractedDelta (nodalGraph p' hdim' (f ⁻¹' {x})) G =
        ∑ Y ∈ 𝒴, contractedDelta (nodalGraph p' hdim' (f ⁻¹' {x})) Y ∧
      ∑ Y ∈ 𝒴, ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary Y).card =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card := by
  have hG' := coe_eq_genericPoints_inter f x hG
  have hO := outerPoints_eq_diff f x
  set Γ := nodalGraph p' hdim' (f ⁻¹' {x})
  have hgen : ∀ v ∈ G, v ∈ genericPoints C' := fun v hv => by
    have : v ∈ (G : Set C') := hv
    rw [hG'] at this
    exact this.1
  have hdisj : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → Disjoint Y Y' := by
    intro Y hY Y' hY' hne
    rw [Finset.disjoint_left]
    intro v hvY hvY'
    exact Set.disjoint_left.1 (hsep Y hY Y' hY' hne v hvY v hvY') (subset_closure rfl)
      (subset_closure rfl)
  have hsep' : ∀ e, ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, (∃ v ∈ Γ.ends e, v ∈ Y) → (∃ v ∈ Γ.ends e, v ∈ Y') →
      Y = Y' := by
    rintro e Y hY Y' hY' ⟨v, hv, hvY⟩ ⟨v', hv', hv'Y'⟩
    by_contra hne
    exact Set.disjoint_left.1 (hsep Y hY Y' hY' hne v hvY v' hv'Y')
      ((mem_nodalGraph_ends p' hdim' e v).1 hv).2 ((mem_nodalGraph_ends p' hdim' e v').1 hv').2
  have hmeet : ∀ e, ∃ v ∈ Γ.ends e, v ∈ G := by
    intro e
    obtain ⟨v, hv, hev⟩ := hcurve e.1 e.2.1
    exact ⟨v, (mem_nodalGraph_ends p' hdim' e v).2 ⟨hgen v hv, hev⟩, hv⟩
  have hnodes : (Γ.boundary G).card + (Γ.inner G).card = Fintype.card (nodesIn p' (f ⁻¹' {x})) := by
    rw [card_boundary_add_card_inner_nodalGraph p' hdim' hG' hO hcurve, Fintype.card_eq_nat_card,
      Nat.card_coe_set_eq]
  exact ⟨contractedDelta_eq_sum Γ hsub hcov hdisj hsep' hmeet hnodes,
    sum_card_boundary Γ hsub hcov hsep'⟩

open scoped Classical in
include hU in
/-- **Temkin, Corollary B.2, scheme level** (`stabdowncor`, `semi-stable.tex` l. 4435–4467).
Let `k` be algebraically closed and `f : C' → C` a proper morphism of reduced projective curves
over `k` (`f ≫ p = p'`), an isomorphism over `C ∖ {x}` for a closed point `x` which is not a
generic point, with `p_a(C') = p_a(C)`. Assume `Z = f⁻¹(x)` is a connected curve (`hZ`,
`hcurve`), `C'` is semi-stable along `Z` (`hnodal`) and the genera of the components of `Z` are
nonnegative (`hg`). Let `G` be the components of `Z`, `b : N → C` the normalization of `C'` in its
other components, `V ∋ x` an affine open, `A` the image of `𝒪_{C,x} = Γ(V, 𝒪_C)_𝔭` in the
semilocal ring `B = Γ(b⁻¹V, 𝒪_N)_𝔭` over `x`, and `Γ = nodalGraph` the incidence graph of `C'`
along `Z`. Then `B` has `|∂Z|` maximal ideals (`|x̃| = |∂Z|`), and `x` is an ordinary point in
gluing form (`A` is the ring of `b ∈ B` taking one value `c ∈ k` at all points of `x̃`) if and only
if `Z` is a `ℙ¹`-tree. -/
theorem stabdown_scheme [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x) (hZ : _root_.IsConnected (f ⁻¹' {x}))
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ v ∈ G, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((outerMap f x).app V).hom.toAlgebra
    letI := (((outerMap f x).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card ∧
      (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) ↔
        (nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree G) := by
  obtain ⟨hδ, hbr⟩ := deltaInvariant_eq_contractedDelta_nodalGraph f x U hU p p' hfp hxg hx hdim
    hdim' hp hp' hpa G hG hcurve hnodal hg
  have hconn := isConnected_nodalGraph_fiber f x p' hx hdim' G hG hZ hcurve hnodal
  let _ := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((outerMap f x).app V).hom.toAlgebra
  let _ := (((outerMap f x).app V).hom.comp
    (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(C, V) Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ :=
    outer_local_inputs f x U hU p p' hxg hx hdim hdim' V hV hxV
  have hδ' : (delta k (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
      (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) : ℤ) =
      contractedDelta (nodalGraph p' hdim' (f ⁻¹' {x})) G := by
    rw [← hdelta]
    exact hδ
  refine ⟨?_, stabdown_gluing_iff_of_isAlgClosed _ hres hconn hδ' (hcard.trans hbr)⟩
  rw [Nat.card_eq_fintype_card]
  exact hcard.trans hbr

open scoped Classical in
include hU in
/-- **The usable variant of Corollary B.2 for a disconnected fibre** (ERRATA DJA-O7; Temkin,
Cor. B.2): in the situation of `stabdown_scheme`, without assuming `Z` connected, let the
components `G` of `Z` be partitioned into families `Y ∈ 𝒴` such that components in different
families do not meet. If every family is a `ℙ¹`-tree in the incidence graph, then there is at most
one family (so `Z` is connected) and `x` is an ordinary point in gluing form, with `|x̃| = |∂Z|`. -/
theorem stabdown_scheme_of_isP1Tree [IsAlgClosed k] [CompactSpace C]
    [IsAffineHom (pullback.diagonal (terminal.from C))] [IsReduced C] [CompactSpace C']
    [IsReduced C'] [IsProper f] (p : C ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (p' : C' ⟶ Spec (.of k)) [LocallyOfFiniteType p'] (hfp : f ≫ p = p')
    (hxg : x ∉ genericPoints C) (hx : IsClosed {x}) (hdim : topologicalKrullDim C ≤ 1)
    (hdim' : topologicalKrullDim C' ≤ 1) (hp : IsProjectiveOver p) (hp' : IsProjectiveOver p')
    (hpa : arithmeticGenus C' (structureCoeff p') = arithmeticGenus C (structureCoeff p))
    (G : Finset C') (hG : (G : Set C') = innerPoints f x)
    (hcurve : ∀ z ∈ f ⁻¹' {x}, ∃ v ∈ G, z ∈ closure {v})
    (hnodal : ∀ y ∈ f ⁻¹' {x}, IsClosed {y} →
      DeJong.IsSmoothAt p' y ∨ Geometry.IsGeometricOrdinaryDoublePoint p' y)
    (hg : ∀ v ∈ G, 0 ≤ componentGenus (structureCoeff p') v)
    [Fintype (nodesIn p' (f ⁻¹' {x}))] (𝒴 : Finset (Finset C')) (hsub : ∀ Y ∈ 𝒴, Y ⊆ G)
    (hcov : ∀ v ∈ G, ∃ Y ∈ 𝒴, v ∈ Y)
    (hsep : ∀ Y ∈ 𝒴, ∀ Y' ∈ 𝒴, Y ≠ Y' → ∀ v ∈ Y, ∀ v' ∈ Y',
      Disjoint (closure ({v} : Set C')) (closure {v'}))
    (htree : ∀ Y ∈ 𝒴, (nodalGraph p' hdim' (f ⁻¹' {x})).IsP1Tree Y)
    (V : C.Opens) (hV : IsAffineOpen V) (hxV : x ∈ V) :
    letI := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
    letI := ((outerMap f x).app V).hom.toAlgebra
    letI := (((outerMap f x).app V).hom.comp
      (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
    haveI : IsScalarTower k Γ(C, V) Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    𝒴.card ≤ 1 ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) =
        ((nodalGraph p' hdim' (f ⁻¹' {x})).boundary G).card ∧
      rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
          (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) =
        gluing k (Localization (Algebra.algebraMapSubmonoid
            Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
            (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)) := by
  obtain ⟨hδ, hbr⟩ := deltaInvariant_eq_contractedDelta_nodalGraph f x U hU p p' hfp hxg hx hdim
    hdim' hp hp' hpa G hG hcurve hnodal hg
  obtain ⟨hsum, hbsum⟩ := partition_nodalGraph f x p' hdim' G hG hcurve 𝒴 hsub hcov hsep
  set Γ := nodalGraph p' hdim' (f ⁻¹' {x})
  -- the local algebra
  let _ := (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤)).toAlgebra
  let _ := ((outerMap f x).app V).hom.toAlgebra
  let _ := (((outerMap f x).app V).hom.comp
    (sectionsRingHom (structureCoeff p) (le_top : V ≤ ⊤))).toAlgebra
  have : IsScalarTower k Γ(C, V) Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _, _, _, hres, hcard, hdelta⟩ :=
    outer_local_inputs f x U hU p p' hxg hx hdim hdim' V hV hxV
  have hδ' : (delta k (rangeIn k (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
      (Localization (Algebra.algebraMapSubmonoid
        Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
        (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) : ℤ) =
      ∑ Y ∈ 𝒴, contractedDelta Γ Y + ((0 : ℕ) : ℤ) := by
    rw [← hdelta, hδ, hsum]
    simp
  have hbr' : (Fintype.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid
      Γ(normalizationPoints (outerPoints f x), outerMap f x ⁻¹ᵁ V)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl))) : ℤ) =
      ∑ Y ∈ 𝒴, ((Γ.boundary Y).card : ℤ) + 2 * ((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ) := by
    rw [hcard, hbr, ← hbsum]
    push_cast
    ring
  obtain ⟨hle, hord⟩ := stabdown_connected_of_isP1Tree _ hres 𝒴 0 0 hδ' hbr' htree
  refine ⟨by simpa using hle, ?_, ((delta_add_one_eq_card_iff_of_isLocalRing _ hres).1 hord).2⟩
  rw [Nat.card_eq_fintype_card]
  exact hcard.trans hbr

end Corollary

end

end DeJongAlterations.StableModification.CurvesField.Genus
