import DeJongAlterations.Composition

/-!
# Alterations on actual nonempty target opens

The open restriction used in the compactification reduction of de Jong 4.7.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual base change of an alteration to a nonempty target open is an alteration. -/
theorem IsAlteration.morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hf : IsAlteration f] (U : Y.Opens) [Nonempty U] : IsAlteration (f ∣_ U) := by
  let := hf.sourceIntegral
  let := hf.targetIntegral
  let : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨y, hy⟩ := Set.nonempty_coe_sort.mp (inferInstance : Nonempty U)
    obtain ⟨x, hx⟩ := IsAlteration.surjective f y
    exact ⟨⟨x, by change f x ∈ U; rw [hx]; exact hy⟩⟩
  let : IsDominant (f ∣_ U) := IsZariskiLocalAtTarget.restrict
    (P := @IsDominant) (inferInstance : IsDominant f) U
  have hq : f.QuasiFiniteAt (genericPoint X) :=
    hf.genericallyFinite.quasiFiniteAt_genericPoint f
  have hη : (f ⁻¹ᵁ U).ι (genericPoint (f ⁻¹ᵁ U).toScheme) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  have hq' : ((f ⁻¹ᵁ U).ι ≫ f).QuasiFiniteAt
      (genericPoint (f ⁻¹ᵁ U).toScheme) := by
    apply (Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion
      (f := (f ⁻¹ᵁ U).ι) (g := f)).mpr
    rw [hη]
    exact hq
  rw [← morphismRestrict_ι] at hq'
  have hqU := (Scheme.Hom.quasiFiniteAt_comp_iff
    (f := f ∣_ U) (g := U.ι)).mp hq'
  exact {
    sourceIntegral := inferInstance
    targetIntegral := inferInstance
    genericallyFinite := isGenericallyFinite_of_quasiFiniteAt_genericPoint (f ∣_ U) hqU }

end DeJongAlterations
