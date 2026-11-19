import Hironaka.Geometry.GenericallyEtaleComposition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.Topology.NoetherianSpace

/-!
# Genuine dense target etale opens for finite generically etale maps

The whole original finite map is restricted over an internally produced
base open. Generic-fibre points are identified intrinsically by discrete
fibres and actual source component generic points.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.FiniteGenericallyEtaleOpen

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z S : Scheme.{u}}

/-- An actual point over the base generic is the generic point of its actual source component. -/
theorem eq_component_genericPoint [IsIntegral S] (f : Z ⟶ S) [LocallyQuasiFinite f]
    (z : Z) (hz : f z = genericPoint S) (C : Set Z)
    (hC : C ∈ irreducibleComponents Z) (hzC : z ∈ C) : z = hC.1.genericPoint := by
  have hη := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  have hsp := hη.specializes hzC
  have hspb : f hC.1.genericPoint ⤳ genericPoint S := by
    simpa only [hz] using hsp.map f.continuous
  have he : f hC.1.genericPoint = genericPoint S :=
    (hspb.antisymm (genericPoint_specializes (f hC.1.genericPoint))).eq
  exact ((f.isDiscrete_preimage_singleton (genericPoint S)).eq_of_specializes hsp
    (by exact he) (by exact hz)).symm

/-- A genuine dense source open contains each actual native component generic point. -/
theorem component_genericPoint_mem_dense_open [NoetherianSpace Z]
    (A : Z.Opens) (hA : Dense (A : Set Z)) (C : Set Z)
    (hC : C ∈ irreducibleComponents Z) : hC.1.genericPoint ∈ A := by
  obtain ⟨O, hO, hOne, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨z, hzA, hzO⟩ := hA.exists_mem_open hO hOne
  exact (hC.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents C hC)).mem_open_set_iff A.isOpen |>.mpr
      ⟨z, hOC hzO, hzA⟩

/-- The WHOLE original finite map is etale on a genuinely constructed dense target open. -/
theorem exists_dense_target_etale_open [IsIntegral S] [NoetherianSpace Z]
    (f : Z ⟶ S) [IsFinite f] (hf : IsGenericallyEtale f) :
    ∃ V : S.Opens, genericPoint S ∈ V ∧ Dense (V : Set S) ∧ Etale (f ∣_ V) := by
  obtain ⟨A, hA, hEt⟩ := hf
  let := hEt
  have hgen : ∀ z : Z, f z = genericPoint S → z ∈ A := by
    intro z hz
    let C := irreducibleComponent z
    have hC : C ∈ irreducibleComponents Z := irreducibleComponent_mem_irreducibleComponents z
    rw [eq_component_genericPoint f z hz C hC mem_irreducibleComponent]
    exact component_genericPoint_mem_dense_open A hA C hC
  let V : S.Opens := ⟨(f '' (A : Set Z)ᶜ)ᶜ,
    (f.isClosedMap _ A.isOpen.isClosed_compl).isOpen_compl⟩
  have hη : genericPoint S ∈ V := by
    rintro ⟨z, hzA, hz⟩
    exact hzA (hgen z hz)
  have hpre : f ⁻¹ᵁ V ≤ A := by
    intro z hz
    by_contra hzA
    exact hz ⟨z, hzA, rfl⟩
  let i := Z.homOfLE hpre
  have hi : (f ⁻¹ᵁ V).ι ≫ f = i ≫ (A.ι ≫ f) := by
    rw [← Category.assoc, Scheme.homOfLE_ι]
  let : Etale ((f ⁻¹ᵁ V).ι ≫ f) := by rw [hi]; infer_instance
  let : Etale ((f ∣_ V) ≫ V.ι) := by rw [morphismRestrict_ι]; infer_instance
  exact ⟨V, hη, V.isOpen.dense ⟨genericPoint S, hη⟩, Etale.of_comp (f ∣_ V) V.ι⟩

end Hironaka.Geometry.FiniteGenericallyEtaleOpen
