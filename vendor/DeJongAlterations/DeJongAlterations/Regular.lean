import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Regular schemes

Regularity is stated intrinsically on the local rings of the native scheme.
-/

open CategoryTheory AlgebraicGeometry

namespace DeJongAlterations

/-- Stalkwise regularity. For varieties (and locally Noetherian schemes), this
is the usual regular-scheme condition. Local Noetherianity is not imposed by
this predicate on arbitrary schemes. -/
def IsRegularScheme (X : Scheme) : Prop :=
  ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- An open subscheme of a regular scheme is regular: its local rings are unchanged. -/
theorem IsRegularScheme.of_isOpenImmersion {X Y : Scheme} (hY : IsRegularScheme Y)
    (f : X ⟶ Y) [IsOpenImmersion f] : IsRegularScheme X := by
  intro x
  let := hY (f x)
  exact IsRegularLocalRing.of_ringEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv

/-- A zero-dimensional integral scheme has exactly one point. -/
theorem subsingleton_of_topologicalKrullDim_le_zero (X : Scheme) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 0) : Subsingleton X := by
  have horder : Order.krullDim X ≤ 0 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp horder
  refine ⟨fun x y ↦ ?_⟩
  have hxy : x ≤ y := le_top.trans (hmax y le_top)
  have hyx : y ≤ x := le_top.trans (hmax x le_top)
  exact ((show x ⤳ y from hyx).antisymm (show y ⤳ x from hxy)).eq

/-- Every proper closed subset in the dimension-zero integral base case is empty.
In fact closedness is unnecessary for this conclusion. -/
theorem eq_empty_of_topologicalKrullDim_le_zero (X : Scheme) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 0) (Z : Set X) (hZ : Z ≠ Set.univ) : Z = ∅ := by
  let := subsingleton_of_topologicalKrullDim_le_zero X hdim
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  apply hZ
  exact Set.eq_univ_iff_forall.mpr fun y ↦ (Subsingleton.elim x y) ▸ hx

/-- The global functions on a zero-dimensional integral scheme form a field. -/
theorem isField_globalSections_of_topologicalKrullDim_le_zero (X : Scheme) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 0) : IsField Γ(X, ⊤) := by
  let := subsingleton_of_topologicalKrullDim_le_zero X hdim
  exact isField_of_isIntegral_of_subsingleton X

/-- Every local ring of a zero-dimensional integral scheme is a field. -/
theorem isField_stalk_of_topologicalKrullDim_le_zero (X : Scheme) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 0) (x : X) : IsField (X.presheaf.stalk x) := by
  have horder : Order.krullDim X ≤ 0 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hdim
  have hcoheight : Order.coheight x ≤ (0 : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim x).trans horder
  let := krullDimLE_of_coheight_le hcoheight
  exact Ring.KrullDimLE.isField_of_isDomain

/-- A zero-dimensional integral scheme is regular. -/
theorem isRegularScheme_of_topologicalKrullDim_le_zero (X : Scheme) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 0) : IsRegularScheme X := by
  intro x
  let := (isField_stalk_of_topologicalKrullDim_le_zero X hdim x).toField
  infer_instance

/-- The spectrum of any field is regular, in arbitrary characteristic. -/
theorem isRegularScheme_spec_field (K : Type*) [Field K] :
    IsRegularScheme (Spec (CommRingCat.of K)) := by
  apply isRegularScheme_of_topologicalKrullDim_le_zero
  change topologicalKrullDim (PrimeSpectrum K) ≤ 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]

end DeJongAlterations
