import Hironaka.Geometry.FiniteMorphismFlattening
import Hironaka.Geometry.AffineGenericFlatness
import Hironaka.Geometry.GenericFlatness
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# The entire original prescribed flat open lies in the original module free locus

Every original point is covered by an original target principal open.
The actual restriction--tensor comparison transports the original native
flatness; the original localized module is then finite flat and finitely
presented, hence projective. The native free-locus localization theorem
retains the entire original open.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace Hironaka.Geometry.FiniteMorphismFlatteningCenter

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

omit [IsDomain R] in
/-- Native flatness over the whole original prescribed open implies that every
point of that open belongs to the original finite module's actual free locus. -/
theorem prescribed_flat_open_subset_freeLocus [Module.FinitePresentation R A]
    (U : (Spec (.of R)).Opens)
    (hflat : Flat (FiniteMorphismFlattening.originalMap R A ∣_ U)) :
    (U : Set (Spec (.of R))) ⊆ Module.freeLocus R A := by
  intro p hp
  obtain ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hps, hsU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp U.isOpen
  have hflatD : Flat (FiniteMorphismFlattening.originalMap R A ∣_ PrimeSpectrum.basicOpen s) :=
    GenericFlatness.flat_morphismRestrict_of_le _ hsU hflat
  have hflatT := (AffineGenericFlatness.flat_morphismRestrict_iff_tensor R A s).mp hflatD
  let : Module.Flat (Localization.Away s) (Localization.Away s ⊗[R] A) :=
    RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hflatT)
  let e := LocalizedModule.equivTensorProduct (Submonoid.powers s) A
  let : Module.Flat (Localization.Away s) (LocalizedModule.Away s A) :=
    Module.Flat.of_linearEquiv e
  let : Module.FinitePresentation (Localization.Away s) (LocalizedModule.Away s A) :=
    Module.FinitePresentation.of_equiv e.symm
  let : Module.Projective (Localization.Away s) (LocalizedModule.Away s A) :=
    Module.Flat.projective_of_finitePresentation
  exact (Module.basicOpen_subset_freeLocus_iff (R := R) (M := A) (f := s)).mpr
    inferInstance hps

end Hironaka.Geometry.FiniteMorphismFlatteningCenter
