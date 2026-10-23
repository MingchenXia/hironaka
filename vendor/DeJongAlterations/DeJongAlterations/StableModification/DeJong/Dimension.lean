import DeJongAlterations.Modification
import DeJongAlterations.Geometry.VarietyFunctionFieldDimension
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberOpenDimension

/-!
# Dimension under alterations

The induction of de Jong 4.3 (`dejong96-alterations:page-0017`) is on `d = dim X`. Every
reduction step 4.4–4.10 replaces `X` by an alteration or by a dense open subscheme of a
compactification; these steps preserve the dimension:

* `topologicalKrullDim_eq_of_isAlteration`: an alteration `f : X ⟶ S` of schemes locally of
  finite type over a field satisfies `dim X = dim S`. Over a nonempty open `U ⊆ S` on which
  `f` is finite, `f⁻¹(U) → U` is finite and dominant, so the function field degrees agree
  (Codex's `VarietyFunctionFieldDimension.dimension_eq_of_isFinite`); nonempty opens of
  integral schemes of finite type have the dimension of the whole scheme
  (`FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion`).
* `exists_nat_topologicalKrullDim_eq`: a variety has finite dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.StableModification.DeJong

universe u

variable {k : Type u} [Field k] {X S : Scheme.{u}}

/-- An alteration has surjective underlying map, as a morphism property. -/
theorem IsAlteration.toSurjective (f : X ⟶ S) [IsAlteration f] : Surjective f :=
  ⟨IsAlteration.surjective f⟩

/-- **Alterations preserve dimension.** If `S` is locally of finite type over a field and
`f : X ⟶ S` is an alteration, then `dim X = dim S`. -/
theorem topologicalKrullDim_eq_of_isAlteration (p : S ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (f : X ⟶ S) [hf : IsAlteration f] :
    topologicalKrullDim X = topologicalKrullDim S := by
  have : IsIntegral X := hf.sourceIntegral
  have : IsIntegral S := hf.targetIntegral
  have hsurj : Surjective f := IsAlteration.toSurjective f
  obtain ⟨U, hU, hfin⟩ := hf.genericallyFinite
  have hV : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨⟨s, hs⟩⟩ := hU
    obtain ⟨x, rfl⟩ := f.surjective s
    exact ⟨⟨x, hs⟩⟩
  have : IsIntegral U := isIntegral_of_isOpenImmersion U.ι
  have : IsIntegral (f ⁻¹ᵁ U) := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  have : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) hsurj U
  have hdimU := Geometry.VarietyFunctionFieldDimension.dimension_eq_of_isFinite
    (U.ι ≫ p) (f ∣_ U)
  have h1 := Geometry.FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion
    (f ≫ p) (f ⁻¹ᵁ U).ι
  have h2 := Geometry.FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion p U.ι
  rw [← h1, ← h2, hdimU]

/-- A modification preserves dimension. -/
theorem topologicalKrullDim_eq_of_isModification (p : S ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (f : X ⟶ S) [IsModification f] :
    topologicalKrullDim X = topologicalKrullDim S :=
  topologicalKrullDim_eq_of_isAlteration p f

/-- A variety over a field has finite dimension. -/
theorem exists_nat_topologicalKrullDim_eq (p : X ⟶ Spec (.of k)) [IsVariety p] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  obtain ⟨n, hn, -⟩ := Geometry.FunctionFieldDimension.exists_dimension_and_trdeg p
  exact ⟨n, hn⟩

end DeJongAlterations.StableModification.DeJong
