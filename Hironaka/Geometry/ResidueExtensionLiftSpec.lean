import Hironaka.Geometry.ResidueExtensionLift
import Hironaka.Geometry.ResidueExtensionLiftResidueFields
import Hironaka.Algebra.ResidueExtensionLiftScalar

/-! # Lifting the specified native residue extension of an actual closed affine point -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ResidueExtensionLift

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Hironaka.Algebra.ResidueExtensionLift

section IdealPoint

variable {R : Type u} [CommRing R] (P : Ideal R) [P.IsMaximal]
  (L : Type u) [Field L] [Algebra P.ResidueField L]
  [FiniteDimensional P.ResidueField L] [Algebra.IsSeparable P.ResidueField L]

/-- The actual scheme residue field at the constructed lifted point is the specified field. -/
def pointResidueIso : (liftScheme P L).residueField (liftPoint P L) ≅ .of L :=
  Scheme.Spec.residueFieldIso (.of (LiftRing P L)) (liftPoint P L) ≪≫
    (residueFieldEquiv P L).toCommRingCatIso

/-- The native residue map of the actual finite-free spectrum morphism preserves the specified embedding. -/
theorem pointResidueIso_comp :
    (Scheme.Spec.residueFieldIso (.of R) (⟨P, inferInstance⟩ : PrimeSpectrum R)).inv ≫
      ((Spec (.of R)).residueFieldCongr (liftPoint_map P L)).inv ≫
        (structureMap P L).residueFieldMap (liftPoint P L) ≫ (pointResidueIso P L).hom =
          CommRingCat.ofHom (algebraMap P.ResidueField L) := by
  have h := spec_residueFieldMap_congr (CommRingCat.ofHom (algebraMap R (LiftRing P L)))
    (liftPoint P L) ⟨P, inferInstance⟩ (liftPoint_map P L)
  have hc := congrArg (fun m => m ≫ (residueFieldEquiv P L).toCommRingCatIso.hom) h
  calc
    _ = CommRingCat.ofHom (residueBaseMap P L) ≫
        (residueFieldEquiv P L).toCommRingCatIso.hom := by
      simpa only [structureMap, pointResidueIso, Iso.trans_hom, Category.assoc, residueBaseMap, liftPoint, CommRingCat.hom_ofHom] using hc
    _ = _ := by
      change CommRingCat.ofHom ((residueFieldEquiv P L).toRingHom.comp (residueBaseMap P L)) = _
      exact congrArg CommRingCat.ofHom (residueFieldEquiv_comp P L)

end IdealPoint

/-- Source 5.7 over an actual spectrum, with its actual native residue field as input.
The finite-free algebra, whole scheme fibre, unique point, specified residue map and
whole-base etale neighbourhood are all constructed internally. -/
theorem exists_spec_residue_extension_lift (R : CommRingCat.{u}) (u : Spec R)
    (hu : IsClosed ({u} : Set (Spec R))) (L : Type u) [Field L]
    [Algebra ((Spec R).residueField u) L] [FiniteDimensional ((Spec R).residueField u) L]
    [Algebra.IsSeparable ((Spec R).residueField u) L] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      let ψ := Spec.map (CommRingCat.ofHom (algebraMap R S))
      Module.Free R S ∧ Module.Finite R S ∧ IsFinite ψ ∧ Flat ψ ∧
      Nonempty (ψ.fiber u ≅ Spec (.of L)) ∧
      ∃ (v : Spec (.of S)) (hv : ψ v = u),
        (∀ q, ψ q = u → q = v) ∧
        (∃ e : (Spec (.of S)).residueField v ≅ .of L,
          ((Spec R).residueFieldCongr hv).inv ≫ ψ.residueFieldMap v ≫ e.hom =
            CommRingCat.ofHom (algebraMap ((Spec R).residueField u) L)) ∧
        ∃ V : (Spec R).Opens, u ∈ V ∧ Etale (ψ ∣_ V) := by
  let P := u.asIdeal
  let : P.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal u).mp hu
  let e₀ := (Scheme.Spec.residueFieldIso R u).symm.commRingCatIsoToRingEquiv
  let := algebraOfEquiv (L := L) e₀
  let := finite_of_equiv (L := L) e₀
  let := separable_of_equiv (L := L) e₀
  refine ⟨LiftRing P L, inferInstance, inferInstance, inferInstance, inferInstance,
    structureMap_isFinite P L, structureMap_flat P L, ⟨fibreIso P L⟩,
    liftPoint P L, liftPoint_map P L, ?_, ?_, etaleBaseOpen P L,
    mem_etaleBaseOpen P L, structureMap_restrict_etale P L⟩
  · intro q hq
    exact unique_point_over P L q hq
  · refine ⟨pointResidueIso P L, ?_⟩
    apply (cancel_epi (Scheme.Spec.residueFieldIso R u).inv).mp
    exact pointResidueIso_comp P L

end Hironaka.Geometry.ResidueExtensionLift
