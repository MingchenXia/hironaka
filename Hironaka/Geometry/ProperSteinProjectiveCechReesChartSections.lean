/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.ProperSteinProjectiveCechReesRestriction

/-!
Closed native proof adapted from
`EnvelopeProperty/EnvelopeProperty/AlgGeom/ReesFormalChartSheaf.lean`,
SHA256 8480562384d192823b3ce52bff5ab7ee07c0971bbc75dcc970be3777817d0c18.
Only Mathlib and the actual owned original Rees image/chart cone are imported.
No chart-section, coefficient, restriction or naturality output is assumed.


# Actual affine Rees chart sections and restriction

The projection of the actual schematic Rees family to its original scheme
is affine. Its genuine chart sections are identified with the actual chart
Rees algebra, retaining the original coefficient homomorphisms.
-/

open CategoryTheory AlgebraicGeometry Limits
open scoped Polynomial
noncomputable section
universe u

namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesChartSections

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The genuine original-scheme projection of the actual schematic Rees
family, including its original closed immersion. -/
def projection : ReesFamily.family I f ⟶ X :=
  ReesFamily.familyImmersion I f ≫
    pullback.fst f (ReesFamily.reesBase I)

/-- Actual affine chart pullbacks prove the original-scheme projection
of the constructed schematic Rees family affine. -/
instance projection_isAffineHom : IsAffineHom (projection I f) := by
  constructor
  intro U hU
  unfold projection
  rw [← ReesRestriction.chartMap_opensRange I f hU]
  exact isAffineOpen_opensRange _

/-- Genuine sections on the whole inverse image of an original affine open
are canonically its actual extended-ideal Rees algebra. -/
def chartSectionsIso {U : X.Opens} (hU : IsAffineOpen U) :
    Γ(ReesFamily.family I f, projection I f ⁻¹ᵁ U) ≅
      .of (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU))) := by
  let j := ReesRestriction.chartMap I f hU
  have hrange : j ''ᵁ ⊤ = projection I f ⁻¹ᵁ U :=
    j.image_top_eq_opensRange.trans (ReesRestriction.chartMap_opensRange I f hU)
  exact (ReesFamily.family I f).presheaf.mapIso (eqToIso hrange).op ≪≫
    j.appIso ⊤ ≪≫ Scheme.ΓSpecIso _

/-- The original chart coefficient homomorphisms are compatible with the
actual original sheaf restriction, on all coefficients. -/
theorem chartCoefficient_naturality {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (X.presheaf.map (homOfLE hUV).op).hom.comp
        (ReesRestriction.chartCoefficient f hV) =
      ReesRestriction.chartCoefficient f hU := by
  have h : Spec.map (X.presheaf.map (homOfLE hUV).op) ≫ (hV.fromSpec ≫ f) =
      hU.fromSpec ≫ f := by
    rw [← Category.assoc, hV.map_fromSpec hU (homOfLE hUV).op]
  have hpre := congrArg Spec.preimage h
  rw [Spec.preimage_comp, Spec.preimage_map] at hpre
  exact congrArg CommRingCat.Hom.hom hpre

/-- The actual original chart restriction maps the full extended-ideal Rees
algebras by coefficientwise polynomial restriction. -/
def reesRestriction {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    reesAlgebra (I.map (ReesRestriction.chartCoefficient f hV)) →+*
      reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU)) :=
  ((Polynomial.mapRingHom (X.presheaf.map (homOfLE hUV).op).hom).comp
    (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hV))).val.toRingHom).codRestrict
    (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU))) fun p n => by
      change (Polynomial.map (X.presheaf.map (homOfLE hUV).op).hom
        (p : Γ(X, V)[X])).coeff n ∈
          I.map (ReesRestriction.chartCoefficient f hU) ^ n
      rw [Polynomial.coeff_map]
      have hp := Ideal.mem_map_of_mem (X.presheaf.map (homOfLE hUV).op).hom (p.2 n)
      rw [Ideal.map_pow, Ideal.map_map, chartCoefficient_naturality f hUV hU hV] at hp
      exact hp

/-- The full original chart polynomial is retained by actual Rees restriction. -/
theorem reesRestriction_val {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (p : reesAlgebra (I.map (ReesRestriction.chartCoefficient f hV))) :
    (reesRestriction I f hUV hU hV p : Γ(X, U)[X]) =
      Polynomial.map (X.presheaf.map (homOfLE hUV).op).hom (p : Γ(X, V)[X]) := rfl

/-- Actual restriction preserves every homogeneous coefficient in its
original degree. -/
theorem reesRestriction_coeff {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (p : reesAlgebra (I.map (ReesRestriction.chartCoefficient f hV))) (n : ℕ) :
    (reesRestriction I f hUV hU hV p : Γ(X, U)[X]).coeff n =
      (X.presheaf.map (homOfLE hUV).op).hom ((p : Γ(X, V)[X]).coeff n) :=
  Polynomial.coeff_map _ _

/-- The genuine original Rees coefficient homomorphism on an actual chart. -/
def reesCoefficient {U : X.Opens} (hU : IsAffineOpen U) :
    reesAlgebra I →+*
      reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU)) :=
  letI := ReesRestriction.chartAlgebra f hU
  (ReesBaseChange.reesMap (A := Γ(X, U)) I).toRingHom

/-- Actual Rees restriction retains the entire original affine coefficient
homomorphism, including degree zero. -/
theorem reesRestriction_comp_algebraMap {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (reesRestriction I f hUV hU hV).comp
        (algebraMap Γ(X, V)
          (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hV)))) =
      (algebraMap Γ(X, U)
        (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU)))).comp
          (X.presheaf.map (homOfLE hUV).op).hom := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change Polynomial.map _ (Polynomial.C a) = Polynomial.C _
  exact Polynomial.map_C _

/-- The entire original Rees coefficient homomorphism commutes with actual
chart restriction. -/
theorem reesRestriction_comp_reesCoefficient {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (reesRestriction I f hUV hU hV).comp (reesCoefficient I f hV) =
      reesCoefficient I f hU := by
  apply RingHom.ext
  intro p
  apply Subtype.ext
  change Polynomial.map (X.presheaf.map (homOfLE hUV).op).hom
      (Polynomial.map (ReesRestriction.chartCoefficient f hV) (p : R[X])) =
    Polynomial.map (ReesRestriction.chartCoefficient f hU) (p : R[X])
  rw [Polynomial.map_map, chartCoefficient_naturality f hUV hU hV]

/-- The actual chart inclusion retains the whole original-scheme projection. -/
theorem chartMap_original {U : X.Opens} (hU : IsAffineOpen U) :
    ReesRestriction.chartMap I f hU ≫ projection I f =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U)
          (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU))))) ≫
        hU.fromSpec :=
  (ReesRestriction.chartMap_isPullback_over_original I f hU).w.symm

/-- The actual chart inclusion retains the entire original Rees coefficient
homomorphism with its canonical chart algebra structure. -/
theorem chartMap_rees {U : X.Opens} (hU : IsAffineOpen U) :
    ReesRestriction.chartMap I f hU ≫ ReesFamily.familyProjection I f =
      Spec.map (CommRingCat.ofHom (reesCoefficient I f hU)) :=
  ReesRestriction.chartMap_projection I f hU

/-- The actual spectrum of Rees restriction retains the whole original
affine coefficient triangle. -/
theorem spec_reesRestriction_comp_algebraMap {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Spec.map (CommRingCat.ofHom (reesRestriction I f hUV hU hV)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, V)
            (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hV))))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap Γ(X, U)
          (reesAlgebra (I.map (ReesRestriction.chartCoefficient f hU))))) ≫
        Spec.map (X.presheaf.map (homOfLE hUV).op) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (reesRestriction_comp_algebraMap I f hUV hU hV)

/-- The entire actual chart restriction on the original global schematic
family is the spectrum of the coefficientwise Rees restriction. -/
theorem chartMap_naturality {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Spec.map (CommRingCat.ofHom (reesRestriction I f hUV hU hV)) ≫
        ReesRestriction.chartMap I f hV =
      ReesRestriction.chartMap I f hU := by
  apply (cancel_mono (ReesFamily.familyImmersion I f)).mp
  apply pullback.hom_ext
  · simp only [Category.assoc]
    change Spec.map (CommRingCat.ofHom (reesRestriction I f hUV hU hV)) ≫
      (ReesRestriction.chartMap I f hV ≫ projection I f) =
        ReesRestriction.chartMap I f hU ≫ projection I f
    rw [chartMap_original, ← Category.assoc,
      spec_reesRestriction_comp_algebraMap I f hUV hU hV, Category.assoc,
      hV.map_fromSpec hU (homOfLE hUV).op, chartMap_original]
  · simp only [Category.assoc]
    change Spec.map (CommRingCat.ofHom (reesRestriction I f hUV hU hV)) ≫
      (ReesRestriction.chartMap I f hV ≫ ReesFamily.familyProjection I f) =
        ReesRestriction.chartMap I f hU ≫ ReesFamily.familyProjection I f
    rw [chartMap_rees, chartMap_rees, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (reesRestriction_comp_reesCoefficient I f hUV hU hV)

/-- The whole inverse image of an original affine chart is the entire
canonical affine Rees source. -/
theorem chartMap_preimage {U : X.Opens} (hU : IsAffineOpen U) :
    ReesRestriction.chartMap I f hU ⁻¹ᵁ (projection I f ⁻¹ᵁ U) = ⊤ := by
  change ReesRestriction.chartMap I f hU ⁻¹ᵁ
    ((ReesFamily.familyImmersion I f ≫
      pullback.fst f (ReesFamily.reesBase I)) ⁻¹ᵁ U) = ⊤
  rw [← ReesRestriction.chartMap_opensRange I f hU,
    Scheme.Hom.preimage_opensRange]

/-- The whole chart section isomorphism is induced by the actual chart
inclusion on all sections, followed by the genuine affine section isomorphism. -/
theorem chartSectionsIso_hom {U : X.Opens} (hU : IsAffineOpen U) :
    (chartSectionsIso I f hU).hom =
      (ReesRestriction.chartMap I f hU).appLE (projection I f ⁻¹ᵁ U) ⊤
        (by rw [chartMap_preimage I f hU]) ≫ (Scheme.ΓSpecIso _).hom := by
  simp only [chartSectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    eqToIso.hom, eqToHom_op, Scheme.Hom.appIso_hom', ← Category.assoc, Scheme.Hom.map_appLE]

private theorem appLE_comp_appTop {S T Z : Scheme.{u}} (s : S ⟶ T) (j : T ⟶ Z)
    (U : Z.Opens) (hj : ⊤ ≤ j ⁻¹ᵁ U) :
    j.appLE U ⊤ hj ≫ s.appTop =
      (s ≫ j).appLE U ⊤ (by
        intro x _
        exact hj trivial) := by
  have hs : ⊤ ≤ s ⁻¹ᵁ (⊤ : T.Opens) := by simp
  have ht : s.appTop = s.appLE ⊤ ⊤ hs := by
    simpa only [Scheme.Hom.appTop, TopologicalSpace.Opens.map_top] using
      s.app_eq_appLE (U := ⊤)
  rw [ht]
  exact Scheme.Hom.appLE_comp_appLE s j U ⊤ ⊤ hj hs

private theorem appLE_eq_of_hom_eq {S T : Scheme.{u}} (g h : S ⟶ T) (e : g = h)
    (U : T.Opens) (V : S.Opens) (hg : V ≤ g ⁻¹ᵁ U) (hh : V ≤ h ⁻¹ᵁ U) :
    g.appLE U V hg = h.appLE U V hh := by
  subst h
  rfl

private theorem affineChartSections_naturality {A B : CommRingCat.{u}} {Z : Scheme.{u}}
    (jA : Spec A ⟶ Z) (jB : Spec B ⟶ Z) (φ : B ⟶ A)
    (hφ : Spec.map φ ≫ jB = jA)
    (U V : Z.Opens) (hUV : U ≤ V)
    (hA : ⊤ ≤ jA ⁻¹ᵁ U) (hB : ⊤ ≤ jB ⁻¹ᵁ V) :
    Z.presheaf.map (homOfLE hUV).op ≫
        (jA.appLE U ⊤ hA ≫ (Scheme.ΓSpecIso A).hom) =
      (jB.appLE V ⊤ hB ≫ (Scheme.ΓSpecIso B).hom) ≫ φ := by
  have hAV : ⊤ ≤ jA ⁻¹ᵁ V := hA.trans (fun _ hx => hUV hx)
  have hc : jB.appLE V ⊤ hB ≫ (Spec.map φ).appTop = jA.appLE V ⊤ hAV :=
    (appLE_comp_appTop (Spec.map φ) jB V hB).trans
      (appLE_eq_of_hom_eq _ _ hφ _ _ _ _)
  rw [← Category.assoc, Scheme.Hom.map_appLE, ← hc, Category.assoc,
    Scheme.ΓSpecIso_naturality, Category.assoc]

/-- Genuine restriction on sections of the original global schematic family
is coefficientwise Rees restriction under the canonical chart isomorphisms. -/
theorem chartSectionsIso_naturality {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (ReesFamily.family I f).presheaf.map
        (homOfLE (show projection I f ⁻¹ᵁ U ≤ projection I f ⁻¹ᵁ V from
          fun _ hx => hUV hx)).op ≫ (chartSectionsIso I f hU).hom =
      (chartSectionsIso I f hV).hom ≫ CommRingCat.ofHom (reesRestriction I f hUV hU hV) := by
  rw [chartSectionsIso_hom, chartSectionsIso_hom]
  exact affineChartSections_naturality
    (ReesRestriction.chartMap I f hU) (ReesRestriction.chartMap I f hV)
    (CommRingCat.ofHom (reesRestriction I f hUV hU hV)) (chartMap_naturality I f hUV hU hV)
    _ _ (fun _ hx => hUV hx) _ _

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesChartSections
