import Hironaka.Geometry.ProjectiveSecantProjectionFiniteLocalIso
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The actual original finite affine chart internally produces native Nakayama localization data
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.ProjectiveSecant

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The exact actual chart triangle and source-chart injectivity carry actual original singleton fibres to actual native Spec singleton fibres. -/
theorem chart_fibre_eq_of_original {X Y : Scheme.{u}} (f : X ⟶ Y)
    {R S : CommRingCat.{u}} (a : Spec S ⟶ X) [IsOpenImmersion a]
    (b : Spec R ⟶ Y) (β : R ⟶ S) (ht : a ≫ f = Spec.map β ≫ b)
    (Q : PrimeSpectrum S) (hfibre : ∀ z : X, f z = f (a Q) → z = a Q)
    (Q' : PrimeSpectrum S) (hQ' : Spec.map β Q' = Spec.map β Q) : Q' = Q := by
  apply a.isOpenEmbedding.injective
  apply hfibre
  have h1 := congrArg (fun g : Spec S ⟶ Y => g Q') ht
  have h2 := congrArg (fun g : Spec S ⟶ Y => g Q) ht
  change f (a Q') = b (Spec.map β Q') at h1
  change f (a Q) = b (Spec.map β Q) at h2
  exact h1.trans ((congrArg (fun z => b z) hQ').trans h2.symm)

/-- The whole actual original finite affine chart map, source prime and native Nakayama coefficient are all produced from original finite integral geometry and SAME-point original local properties. -/
theorem exists_original_finite_chart_awayMap_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsDominant f] [IsReduced Y]
    (x : X) (U : Y.Opens) (hU : IsAffineOpen U) (hx : f x ∈ U)
    (hfibre : ∀ z : X, f z = f x → z = x)
    (hfu : (f.stalkMap x).hom.FormallyUnramified) [IsIso (f.residueFieldMap x)] :
    ∃ Q : PrimeSpectrum Γ(X, f ⁻¹ᵁ U), (hU.preimage f).fromSpec Q = x ∧
      ∃ r ∉ (PrimeSpectrum.comap (f.app U).hom Q).asIdeal,
        ∀ r', r ∣ r' → Function.Bijective (Localization.awayMap (f.app U).hom r') := by
  let hV := hU.preimage f
  have hr : x ∈ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    exact hx
  obtain ⟨Q, rfl⟩ := hr
  have ht : hV.fromSpec ≫ f = Spec.map (f.app U) ≫ hU.fromSpec := by
    simpa only [Scheme.Hom.app_eq_appLE] using
      (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl).symm
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have hβinj : Function.Injective (f.app U).hom := f.app_injective U
  have hβfibre := chart_fibre_eq_of_original f hV.fromSpec hU.fromSpec (f.app U) ht Q hfibre
  have hβfu := chart_stalkMap_formallyUnramified_of_original f hV.fromSpec hU.fromSpec (f.app U) ht Q hfu
  let : IsIso ((Spec.map (f.app U)).residueFieldMap Q) :=
    chart_residueFieldMap_isIso_of_original f hV.fromSpec hU.fromSpec (f.app U) ht Q
  exact ⟨Q, rfl, exists_awayMap_bijective_of_spec_local_data (f.app U) (f.finite_app U hU)
    hβinj Q hβfibre hβfu⟩

end Hironaka.Geometry.ProjectiveSecant
