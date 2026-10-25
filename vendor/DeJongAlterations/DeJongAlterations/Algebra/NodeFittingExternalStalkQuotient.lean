import DeJongAlterations.Algebra.NodeFittingIdealSheafQuotient
import DeJongAlterations.Algebra.NodeFittingOmegaGluing
import DeJongAlterations.Geometry.CompletedLocalRing

/-! # ACTUAL closed-subscheme stalk quotients over the SAME native external coefficients -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Algebra.NodeFittingExternalStalkQuotient

open NodeFittingIdealSheaf NodeFittingOmegaCharts

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

section External

variable (K : Type u) [CommRing K] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) (I : X.IdealSheafData)

/-- The ACTUAL native closed-subscheme stalk quotient with the SAME actual external coefficient actions. -/
def externalStalkQuotientEquiv (z : I.subscheme) :
    letI := Scheme.stalkAlgebra p (I.subschemeι z)
    letI := Scheme.stalkAlgebra (I.subschemeι ≫ p) z
    (X.presheaf.stalk (I.subschemeι z) ⧸ stalkIdeal I (I.subschemeι z)) ≃ₐ[K]
      I.subscheme.presheaf.stalk z := by
  letI := Scheme.stalkAlgebra p (I.subschemeι z)
  letI := Scheme.stalkAlgebra (I.subschemeι ≫ p) z
  refine { toRingEquiv := stalkQuotientEquiv I z, commutes' := ?_ }
  intro k
  change I.subschemeι.stalkMap z (Scheme.baseToStalk p (I.subschemeι z) k) =
    Scheme.baseToStalk (I.subschemeι ≫ p) z k
  exact (I.subschemeι.stalkMapAlgHom p z).commutes k

/-- EVERY original ambient representative follows the SAME actual closed-inclusion stalk map. -/
@[simp]
theorem externalStalkQuotientEquiv_mk (z : I.subscheme)
    (a : X.presheaf.stalk (I.subschemeι z)) :
    externalStalkQuotientEquiv K p I z (Ideal.Quotient.mk _ a) = I.subschemeι.stalkMap z a := rfl

end External

section Pulled

variable {X S Y : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (g : Y ⟶ X)

/-- The ENTIRE pulled original Fitting stalk ideal is the actual image of the ORIGINAL chart ideal. -/
theorem pulledFittingStalkIdeal_eq_chart_image (i : ℕ) (C : Chart f) (y : Y)
    (hy : g y ∈ C.source.1) :
    stalkIdeal ((NodeFittingOmegaGluing.idealSheaf f i).comap g) y =
      (C.ideal f i).map ((g.stalkMap y).hom.comp
        (X.presheaf.germ C.source.1 (g y) hy).hom) := by
  rw [stalkIdeal_comap, NodeFittingOmegaGluing.idealSheaf_stalk,
    ← NodeFittingOmegaStalk.chart_ideal_stalk f C i hy, Ideal.map_map]

variable (K : Type u) [CommRing K] (p : Y ⟶ Spec (CommRingCat.of K))

/-- The ACTUAL pulled Fitting closed-subscheme stalk, modulo the ENTIRE original chart ideal image, over SAME K. -/
def pulledChartStalkQuotientEquiv (i : ℕ) (C : Chart f)
    (z : ((NodeFittingOmegaGluing.idealSheaf f i).comap g).subscheme)
    (hy : g (((NodeFittingOmegaGluing.idealSheaf f i).comap g).subschemeι z) ∈ C.source.1) :
    let y := ((NodeFittingOmegaGluing.idealSheaf f i).comap g).subschemeι z
    letI := Scheme.stalkAlgebra p y
    letI := Scheme.stalkAlgebra (((NodeFittingOmegaGluing.idealSheaf f i).comap g).subschemeι ≫ p) z
    (Y.presheaf.stalk y ⧸ (C.ideal f i).map ((g.stalkMap y).hom.comp
      (X.presheaf.germ C.source.1 (g y) hy).hom)) ≃ₐ[K]
      ((NodeFittingOmegaGluing.idealSheaf f i).comap g).subscheme.presheaf.stalk z := by
  let J := (NodeFittingOmegaGluing.idealSheaf f i).comap g
  let y := J.subschemeι z
  letI := Scheme.stalkAlgebra p y
  letI := Scheme.stalkAlgebra (J.subschemeι ≫ p) z
  let h := pulledFittingStalkIdeal_eq_chart_image f g i C y hy
  let e := externalStalkQuotientEquiv K p J z
  refine { toRingEquiv := (Ideal.quotEquivOfEq h.symm).trans e.toRingEquiv, commutes' := ?_ }
  intro k
  change e (Ideal.Quotient.mk _ (algebraMap K (Y.presheaf.stalk y) k)) =
    algebraMap K (J.subscheme.presheaf.stalk z) k
  exact e.commutes k

/-- EVERY actual ambient quotient representative retains its actual native inclusion map. -/
@[simp]
theorem pulledChartStalkQuotientEquiv_mk (i : ℕ) (C : Chart f)
    (z : ((NodeFittingOmegaGluing.idealSheaf f i).comap g).subscheme)
    (hy : g (((NodeFittingOmegaGluing.idealSheaf f i).comap g).subschemeι z) ∈ C.source.1)
    (a : Y.presheaf.stalk (((NodeFittingOmegaGluing.idealSheaf f i).comap g).subschemeι z)) :
    pulledChartStalkQuotientEquiv f g K p i C z hy (Ideal.Quotient.mk _ a) =
      ((NodeFittingOmegaGluing.idealSheaf f i).comap g).subschemeι.stalkMap z a := rfl

end Pulled

end DeJongAlterations.Algebra.NodeFittingExternalStalkQuotient
