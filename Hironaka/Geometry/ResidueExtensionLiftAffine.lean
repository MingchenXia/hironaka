import Hironaka.Geometry.ResidueExtensionLiftSpec
import Hironaka.Geometry.ProjectiveCurveFibrationFiberMaps

/-!
# Source 5.7 for arbitrary affine schemes

All coordinate rings, closed-point ideals, scalar transports, lifted algebras,
actual fibre comparisons and etale base neighbourhoods are chosen internally.
The finite-free module structure is linked to the actual displayed spectrum map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ResidueExtensionLift

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Hironaka.Algebra.ResidueExtensionLift

/-- De Jong 5.7: an actual finite free lift of a specified finite separable native
residue extension, with the actual whole fibre and a genuine etale base neighbourhood. -/
theorem exists_affine_residue_extension_lift (U : Scheme.{u}) [IsAffine U] (u : U)
    (hu : IsClosed ({u} : Set U)) (L : Type u) [Field L] [Algebra (U.residueField u) L]
    [FiniteDimensional (U.residueField u) L] [Algebra.IsSeparable (U.residueField u) L] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra Γ(U, ⊤) S),
      Module.Free Γ(U, ⊤) S ∧ Module.Finite Γ(U, ⊤) S ∧
      ∃ ψ : Spec (.of S) ⟶ U,
        ψ = Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) S)) ≫ U.isoSpec.inv ∧
        IsFinite ψ ∧ Flat ψ ∧ Nonempty (ψ.fiber u ≅ Spec (.of L)) ∧
        ∃ (v : Spec (.of S)) (hv : ψ v = u),
          (∀ q, ψ q = u → q = v) ∧
          (∃ e : (Spec (.of S)).residueField v ≅ .of L,
            (U.residueFieldCongr hv).inv ≫ ψ.residueFieldMap v ≫ e.hom =
              CommRingCat.ofHom (algebraMap (U.residueField u) L)) ∧
          ∃ V : U.Opens, u ∈ V ∧ Etale (ψ ∣_ V) := by
  let R := Γ(U, ⊤)
  let u₀ := U.isoSpec.hom u
  have hu₀ : IsClosed ({u₀} : Set (Spec R)) := by
    simpa only [Set.image_singleton] using U.isoSpec.hom.isClosedMap _ hu
  let e₀ := (asIso (U.isoSpec.hom.residueFieldMap u)).commRingCatIsoToRingEquiv
  let := algebraOfEquiv (L := L) e₀
  let := finite_of_equiv (L := L) e₀
  let := separable_of_equiv (L := L) e₀
  obtain ⟨S, hS, hA, hfree, hfin, hψfin, hψflat, ⟨ef⟩, v, hv, huniq, ⟨e, he⟩, V, hV, hEt⟩ :=
    exists_spec_residue_extension_lift R u₀ hu₀ L
  let := hS
  let := hA
  let ψ₀ := Spec.map (CommRingCat.ofHom (algebraMap R S))
  let : IsFinite ψ₀ := hψfin
  let : Flat ψ₀ := hψflat
  let ψ := ψ₀ ≫ U.isoSpec.inv
  have hcomp : ψ ≫ U.isoSpec.hom = ψ₀ := by simp [ψ]
  have hvU : ψ v = u := by
    change U.isoSpec.inv (ψ₀ v) = u
    rw [hv]
    simp [u₀]
  let eFib : ψ.fiber u ≅ ψ₀.fiber u₀ := by
    simpa only [hcomp] using
      ProjectiveCurveFibration.fiberCompOpenImmersionIso ψ U.isoSpec.hom u
  refine ⟨S, hS, hA, hfree, hfin, ψ, rfl, inferInstance, inferInstance,
    ⟨eFib ≪≫ ef⟩, v, hvU, ?_, ?_, U.isoSpec.hom ⁻¹ᵁ V, hV, ?_⟩
  · intro q hq
    apply huniq
    change ψ₀ q = u₀
    rw [← hcomp]
    change U.isoSpec.hom (ψ q) = U.isoSpec.hom u
    exact congrArg U.isoSpec.hom hq
  · refine ⟨e, ?_⟩
    apply (cancel_epi (U.isoSpec.hom.residueFieldMap u)).mp
    have hnat := residueFieldMap_targetIso U.isoSpec ψ ψ₀ hcomp v u hvU hv
    calc
      _ = ((Spec R).residueFieldCongr hv).inv ≫ ψ₀.residueFieldMap v ≫ e.hom := by
        simpa only [Category.assoc] using congrArg (fun m => m ≫ e.hom) hnat
      _ = _ := he
  · let W := U.isoSpec.hom ⁻¹ᵁ V
    have hpre : U.isoSpec.inv ⁻¹ᵁ W = V := by
      change U.isoSpec.inv ⁻¹ᵁ (U.isoSpec.hom ⁻¹ᵁ V) = V
      rw [← Scheme.Hom.comp_preimage, U.isoSpec.inv_hom_id, Scheme.Hom.id_preimage]
    let : Etale (ψ₀ ∣_ U.isoSpec.inv ⁻¹ᵁ W) := by
      rw [hpre]
      exact hEt
    change Etale ((ψ₀ ≫ U.isoSpec.inv) ∣_ W)
    rw [morphismRestrict_comp]
    infer_instance

end Hironaka.Geometry.ResidueExtensionLift
