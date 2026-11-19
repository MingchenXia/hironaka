import Hironaka.Algebra.FiniteDimensionDominance
import Hironaka.Geometry.AlterationBasic
import Hironaka.Geometry.RationalCoordinateMapGenericFiberOpenDimension

/-!
# A genuine finite map of full-dimensional varieties is dominant

The original affine coefficient map has no nonzero kernel, by actual
integral image dimension. Its native spectrum dominance then proves
dominance of the original finite scheme morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.FiniteVarietyDominance

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {S T : Scheme.{u}} [IsIntegral T]

/-- Finiteness plus the original global dimension inequality internally forces actual dominance. -/
theorem isDominant_of_dimension_le
    (p : S ⟶ Spec (.of k)) [IsVariety p] (f : T ⟶ S) [IsFinite f]
    (hdim : topologicalKrullDim S ≤ topologicalKrullDim T) : IsDominant f := by
  let : IsVariety (f ≫ p) := .mk
  obtain ⟨d, hd, htr⟩ := FunctionFieldDimension.exists_dimension_and_trdeg p
  obtain ⟨e, he, htrT⟩ := FunctionFieldDimension.exists_dimension_and_trdeg (f ≫ p)
  obtain ⟨U, hUa, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := f (genericPoint T)) (U := (⊤ : S.Opens)) trivial
  let Ua : S.affineOpens := ⟨U, hUa⟩
  let Va : T.affineOpens := ⟨f ⁻¹ᵁ U, hUa.preimage f⟩
  let : Nonempty U := ⟨⟨f (genericPoint T), hxU⟩⟩
  let : Nonempty Va.1 := ⟨⟨genericPoint T, hxU⟩⟩
  let R := Γ(S, U)
  let B := Γ(T, Va.1)
  let : IsDomain R := IsIntegral.component_integral U
  let : IsDomain B := IsIntegral.component_integral Va.1
  let : Algebra R B := (f.app U).hom.toAlgebra
  let : Module.Finite R B := f.finite_app U hUa
  let : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  have hRdim : ringKrullDim R = d := FunctionFieldDimension.affineSections_dimension_eq p Ua d htr
  have hBdim : ringKrullDim B = e :=
    FunctionFieldDimension.affineSections_dimension_eq (f ≫ p) Va e htrT
  have hinj : Function.Injective (f.app U).hom := by
    apply Algebra.FiniteDimensionDominance.algebraMap_injective_of_dimension_le R B d hRdim
    rw [hBdim]
    rwa [hd, he] at hdim
  let g : Spec (.of B) ⟶ Spec (.of R) := Spec.map (f.app U)
  let : IsDominant g := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (f.app U).hom)
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense ⟨_, hxU⟩)
  let : IsDominant hUa.fromSpec := by
    change IsDominant (hUa.isoSpec.inv ≫ U.ι)
    infer_instance
  have htriangle : g ≫ hUa.fromSpec = Va.2.fromSpec ≫ f := by
    simpa only [Va, g, Scheme.Hom.appLE_eq_app] using
      IsAffineOpen.SpecMap_appLE_fromSpec f hUa Va.2 le_rfl
  let : IsDominant (Va.2.fromSpec ≫ f) := by
    rw [← htriangle]
    infer_instance
  exact IsDominant.of_comp Va.2.fromSpec f

end Hironaka.Geometry.FiniteVarietyDominance
