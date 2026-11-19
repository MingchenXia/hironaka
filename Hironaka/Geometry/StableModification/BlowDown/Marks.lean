/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.StableModification.Blowups.Extension
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.Data.Set.Card

/-!
# Marks through a contracted point (Temkin, proof of Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Lemma 4.4.2
(`stabcritlem`, T:3106–3110) compares `|D'_s ∩ Z|` (the marks of `C'_s` on `Z = f⁻¹(x)`) with
the marks of `C` through `x`. In the de Jong route (plan S2) the marks are the closures of
finitely many `K`-points `P_i` of the generic fibre, `K = Frac V`, and over the valuation ring `V`
these closures are sections (blueprint `lem:sm-bd-marks`, chapter `sm-blow-down-criterion.tex`):

* `existsUnique_section` (valuative criterion of properness): a `K`-point `P` of a proper
  `X → Spec V` extends uniquely to a section `σ : Spec V → X`;
* `range_section_eq_closure`: the image of `σ` is the closure of the point `P`;
* `section_comp_eq`: for `f : C' → C` over `V`, the section through `P'` of `C'` maps to the
  section through `f(P')` of `C` (`f(P̄'_i) = P̄_i`);
* `ncard_marks_le`, `ncard_marks_eq`: for sections `σ'_i` of `C'` and `σ_i = f ∘ σ'_i`, the number
  of points of `⋃ σ'_i(Spec V)` over `s` in `f⁻¹(x)` is at most `m = #{i | σ_i(s) = x}`, with
  equality if the `σ'_i(s)` are pairwise distinct (e.g. `D'` étale, `(C', D')` semi-stable).
-/

namespace Hironaka.StableModification.BlowDown

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

section Sections

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V] {X : Scheme.{u}}
  (q : X ⟶ Spec (CommRingCat.of V))

/-- The generic point `Spec K → Spec V`, `K = Frac V`. -/
abbrev genericSpecMap : Spec (CommRingCat.of (FractionRing V)) ⟶ Spec (CommRingCat.of V) :=
  Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))

/-- **The valuative criterion of properness for sections**: a point `P : Spec K → X` of the generic
fibre of a proper `q : X → Spec V` (`V` a valuation ring, `K = Frac V`) extends uniquely to a
section `σ : Spec V → X` of `q`. -/
theorem existsUnique_section [IsProper q] (P : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hP : P ≫ q = genericSpecMap) :
    ∃! σ : Spec (CommRingCat.of V) ⟶ X, σ ≫ q = 𝟙 _ ∧ genericSpecMap ≫ σ = P := by
  have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType) q := by
    rw [← IsProper.eq_valuativeCriterion]
    exact (inferInstance : IsProper q)
  have hv : ValuativeCriterion q := h.1.1.1
  let S : ValuativeCommSq q :=
    { R := V
      K := FractionRing V
      i₁ := P
      i₂ := 𝟙 _
      commSq := ⟨by rw [hP, Category.comp_id]⟩ }
  obtain ⟨hu⟩ := hv S
  refine ⟨hu.default.l, ⟨hu.default.fac_right, hu.default.fac_left⟩, fun σ hσ => ?_⟩
  have := hu.uniq { l := σ, fac_left := hσ.2, fac_right := hσ.1 }
  exact congrArg CommSq.LiftStruct.l this

omit [ValuationRing V] in
/-- The generic point map sends the point of `Spec K` to the generic point of `Spec V`. -/
theorem genericSpecMap_apply (t : Spec (CommRingCat.of (FractionRing V))) :
    genericSpecMap t = genericPoint (Spec (CommRingCat.of V)) := by
  rw [genericPoint_eq_bot_of_affine, Spec.map_apply]
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  change a ∈ Ideal.comap (algebraMap V (FractionRing V)) t.asIdeal ↔ a ∈ (⊥ : Ideal V)
  have := t.isPrime
  rw [Ideal.eq_bot_of_prime t.asIdeal, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))]

omit [ValuationRing V] in
/-- **The image of the section through `P` is the closure of `P`**: `σ` maps the dense generic
point of `Spec V` to the point of `P`, and its image is closed (a section of a separated morphism
is proper). -/
theorem range_section_eq_closure [IsSeparated q] (σ : Spec (CommRingCat.of V) ⟶ X)
    (hσ : σ ≫ q = 𝟙 _) (t : Spec (CommRingCat.of (FractionRing V))) :
    Set.range σ = closure {(genericSpecMap ≫ σ) t} := by
  have : IsProper (σ ≫ q) := by rw [hσ]; infer_instance
  have hcl : IsClosed (Set.range σ) := Blowups.isClosed_range_of_isProper_comp σ q
  have hgen : closure {genericSpecMap t} = (Set.univ : Set (Spec (CommRingCat.of V))) := by
    rw [genericSpecMap_apply]
    exact (genericPoint_spec (Spec (CommRingCat.of V))).def
  refine Set.Subset.antisymm ?_ (closure_minimal (by
    rintro _ rfl
    exact ⟨_, rfl⟩) hcl)
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ closure {genericSpecMap t} := hgen ▸ Set.mem_univ z
  have := image_closure_subset_closure_image σ.continuous (Set.mem_image_of_mem σ hz)
  rw [Set.image_singleton] at this
  exact this

omit [IsDomain V] [ValuationRing V] in
/-- A point in the image of a section over `s` is the value of the section at `s`. -/
theorem eq_of_mem_range_section (σ : Spec (CommRingCat.of V) ⟶ X) (hσ : σ ≫ q = 𝟙 _)
    {y : X} (hy : y ∈ Set.range σ) {s : Spec (CommRingCat.of V)} (hys : q y = s) : y = σ s := by
  obtain ⟨z, rfl⟩ := hy
  have : q (σ z) = z := by rw [← Scheme.Hom.comp_apply, hσ]; rfl
  rw [← hys, this]

variable {C C' : Scheme.{u}} (p : C ⟶ Spec (CommRingCat.of V)) (f : C' ⟶ C)

/-- **The section through `P'` maps to the section through `f(P')`** (`f(P̄'_i) = P̄_i`): for the
unique sections `σ'` of `C'` through `P'` and `σ` of `C` through `P' ≫ f`, `σ' ≫ f = σ`. -/
theorem section_comp_eq [IsProper p] (P' : Spec (CommRingCat.of (FractionRing V)) ⟶ C')
    (σ' : Spec (CommRingCat.of V) ⟶ C') (hσ' : σ' ≫ f ≫ p = 𝟙 _)
    (hσ'P : genericSpecMap ≫ σ' = P') (σ : Spec (CommRingCat.of V) ⟶ C) (hσ : σ ≫ p = 𝟙 _)
    (hσP : genericSpecMap ≫ σ = P' ≫ f) : σ' ≫ f = σ := by
  have hP : (P' ≫ f) ≫ p = genericSpecMap := by
    rw [← hσP, Category.assoc, hσ, Category.comp_id]
  obtain ⟨σ₀, -, huniq⟩ := existsUnique_section p (P' ≫ f) hP
  rw [huniq (σ' ≫ f) ⟨by rw [Category.assoc, hσ'], by rw [← Category.assoc, hσ'P]⟩,
    huniq σ ⟨hσ, hσP⟩]

end Sections

section Count

variable {V : Type u} [CommRing V] {C C' : Scheme.{u}} (p : C ⟶ Spec (CommRingCat.of V))
  (f : C' ⟶ C) {ι : Type*} [Fintype ι] (σ' : ι → (Spec (CommRingCat.of V) ⟶ C'))
  (hσ' : ∀ i, σ' i ≫ f ≫ p = 𝟙 _) (s : Spec (CommRingCat.of V)) (x : C)

/-- The marks of `C'_s` on `Z = f⁻¹(x)`: the points over `s` in `f⁻¹(x)` on one of the sections
`σ'_i` (for `D'` the union of the sections, `D'_s ∩ Z`). -/
def marksOn : Set C' := {y | f y = x ∧ (f ≫ p) y = s ∧ ∃ i, y ∈ Set.range (σ' i)}

omit [Fintype ι] in
include hσ' in
/-- The marks on `f⁻¹(x)` are the values at `s` of the sections through `x`. -/
theorem marksOn_eq : marksOn p f σ' s x =
    (fun i => σ' i s) '' {i | (σ' i ≫ f) s = x} := by
  ext y
  constructor
  · rintro ⟨hyx, hys, i, hi⟩
    have hy := eq_of_mem_range_section (f ≫ p) (σ' i) (hσ' i) hi hys
    refine ⟨i, ?_, hy.symm⟩
    change f (σ' i s) = x
    rw [← hy, hyx]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨hi, ?_, i, ⟨s, rfl⟩⟩
    rw [← Scheme.Hom.comp_apply, hσ' i]
    rfl

open scoped Classical in
include hσ' in
/-- **Marks through a contracted point** (blueprint `lem:sm-bd-marks`): the number of marks of
`C'_s` on `f⁻¹(x)` is at most the number `m = #{i | σ_i(s) = x}` of sections `σ_i = f ∘ σ'_i` of
`C` through `x`. -/
theorem ncard_marksOn_le :
    (marksOn p f σ' s x).ncard ≤ (Finset.univ.filter fun i => (σ' i ≫ f) s = x).card := by
  rw [marksOn_eq p f σ' hσ' s x]
  calc _ ≤ ({i | (σ' i ≫ f) s = x} : Set ι).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = _ := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext i
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

open scoped Classical in
include hσ' in
/-- **Marks through a contracted point, equality** (blueprint `lem:sm-bd-marks`): if the sections
`σ'_i` of `C'` pass through pairwise distinct points over `s` (e.g. `D'` étale over `V`), the
number of marks of `C'_s` on `f⁻¹(x)` is the number of sections of `C` through `x`. -/
theorem ncard_marksOn_eq (hinj : ∀ i j, σ' i s = σ' j s → i = j) :
    (marksOn p f σ' s x).ncard = (Finset.univ.filter fun i => (σ' i ≫ f) s = x).card := by
  rw [marksOn_eq p f σ' hσ' s x, Set.ncard_image_of_injective _ fun i j h => hinj i j h,
    ← Set.ncard_coe_finset]
  congr 1
  ext i
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

end Count


end

end Hironaka.StableModification.BlowDown
