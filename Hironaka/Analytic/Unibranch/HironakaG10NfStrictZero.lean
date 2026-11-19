import Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonicalPre

/-!
# H3.4 (`strict₀`, fused generic form): flatness transfer from a morphism square

Lane G10H3, run 0081 (field `strict₀` of `HironakaG10NfGeoFibreModel.GeoFibreModel`).

Elaborating the canonical instance of `HironakaG10NfStrictCanonical.strict0_builder` with the STALK-level square
`HironakaG10GlCanonicalBaseSquare.canonical_square_joint` as input is slow (> 10 min): the stalk-level statements of
different modules carry different (defeq) instance constants (`IsFiniteType` of the pulled ideal module, one `local
instance` per module; `IsComplexManifold` of the chart domain).  Here the stalk-level square is derived INSIDE a
generic lemma from the MORPHISM-level square `ci ≫ (sc ≫ ind) = actualSubspaceMap f ≫ tc` (G10GL's `square_apply`
and TN's `targetStalkToJoint_strict_square`), so that the canonical instance only feeds morphisms and a morphism
equation.

* `strict0_generic` — on a real-open blowup chart with the joint ideal, flatness of the fibre stalk map of `ind` at
  the strict chart point transfers to `mk_T ∘ ψ`, `ψ = targetStalkToJoint ∘ tc^♯`.

No named input.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG10NfStrictZero

noncomputable section

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaRealOpenGeometricStrictSaturation HironakaG10RealOpenStrictTorsionKernel
  HironakaG10JointStrictTorsion HironakaG10JointNativeScalar HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps HironakaG10HirFlatQuotient

variable (d t : ℕ) (j : Fin t) (b : Fin (d+t) → ℂ) (U : Opens (ComplexModel (d+t))) (W : Set U)
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  (f : realOpenChartDomain d t j b U → Y) (V : Set Y)
  (hf : ContMDiff 𝓘(ℂ,ComplexModel (d+t)) 𝓘(ℂ,ComplexModel n) ∞ f)
  (hV : IsComplexAnalyticSubset (n := n) V)
  (h0 : (0 : ComplexModel (d+t)) ∈ U) (hW : IsComplexAnalyticSubset (n := d+t) W)
  (hland : realOpenStrictTransform d t j b U W ⊆ f ⁻¹' V)

/-- **Flatness transfer at a strict chart point from a morphism square (generic).** -/
theorem strict0_generic {C Ys Bl : LocallyRingedSpace.{0}} (ind : Ys ⟶ Bl)
    (ci : actualSubspaceLocallyRingedSpace (n := d+t) (realOpenStrictTransform d t j b U W) ⟶ C)
    [LocallyRingedSpace.IsOpenImmersion ci] (sc : C ⟶ Ys) [LocallyRingedSpace.IsOpenImmersion sc]
    (tc : actualSubspaceLocallyRingedSpace (n := n) V ⟶ Bl)
    (H : ci ≫ (sc ≫ ind) = actualSubspaceMap hf (fun _ hx => hland hx) ≫ tc)
    (y : realOpenChartDomain d t j b U) (hy : y ∈ localDomain d t j b U W h0 hW)
    (hyS : y ∈ realOpenStrictTransform d t j b U W) (hyV : f y ∈ V)
    (hp : ind.base (sc.base (ci.base ⟨y, hyS⟩)) = tc.base ⟨f y, hyV⟩)
    (J₁ : Ideal (Bl.presheaf.stalk (tc.base ⟨f y, hyV⟩)))
    (h : (quotMap ((ind.stalkMap (sc.base (ci.base ⟨y, hyS⟩))).hom.comp
      (eqToHom (congrArg Bl.presheaf.stalk hp.symm)).hom) J₁).Flat) :
    (quotMap ((Ideal.Quotient.mk (pivotTorsion (n := n) d t j b U W f V y)).comp
      ((targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV).comp
        (tc.stalkMap ⟨f y, hyV⟩).hom)) J₁).Flat := by
  have hs : tc.base ((actualSubspaceMap hf (fun _ hx => hland hx)).base ⟨y, hyS⟩) =
      ind.base (sc.base (ci.base ⟨y, hyS⟩)) :=
    (congrArg (fun k => k.base ⟨y, hyS⟩) H).symm
  have hsq := fun a => (Hironaka.Analytic.Unibranch.HironakaG10GlCanonicalBaseSquare.square_apply ci sc ind
    (actualSubspaceMap hf (fun _ hx => hland hx)) tc H ⟨y, hyS⟩ hs a).trans
    (targetStalkToJoint_strict_square (n := n) d t j b U W f V hf hV h0 hW hland y hy hyS _).symm
  exact Hironaka.Analytic.Unibranch.HironakaG10NfStrictCanonical.strict0_builder ci sc ind ⟨y, hyS⟩
    (pivotTorsion (n := n) d t j b U W f V y)
    (jointStrictStalkMap (n := n) d t j b U W f V h0 hW hf.continuous hland y hy hyS)
    (jointTorsionQuotientEquiv (n := n) d t j b U W f V h0 hW hf.continuous hland y hy hyS)
    (jointTorsionQuotientEquiv_mk (n := n) d t j b U W f V h0 hW hf.continuous hland y hy hyS)
    _ hsq hp ((targetStalkToJoint (n := n) d t j b U W f V hf hV y hyV).comp (tc.stalkMap ⟨f y, hyV⟩).hom)
    (fun _ => rfl) J₁ h

end

end Hironaka.Analytic.Unibranch.HironakaG10NfStrictZero
