import Hironaka.Resolution.HironakaG1NativeBoundaryTrace
import Hironaka.Analytic.DimensionMonotone

/-! Raw native boundary exponents under an intrinsic local dimension bound. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold

namespace Hironaka.HironakaG1NativeBoundaryCodimension
noncomputable section

open Hironaka.BlowupSequences BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HironakaG11PresLineState HironakaG11PresLineStable HironakaG8LocalHistory
  AnalyticDimensionBasics DimensionMonotone AnalyticSubsetOpens
  HironakaG1NativeBoundaryTrace HironakaNormalCrossingsFiniteMarkedCompletion DivisorExponentAlong
  HironakaG1OriginalUnequalMarkCanonical HironakaG11InvBMClass CanonicalCentres

variable {n k l : ℕ} {X : CMfd.{0} n}
  {W : Set X} {P Q : MarkedIdeal n X} {A : ℕ → ℕ}

/-- A locally contained regular analytic trace forces the corresponding
intrinsic local lower dimension, even with containment only as a germ. -/
theorem locDimGE_of_regularAtDim_eventually_subset {H : Set X} {x : X}
    (hW : IsComplexAnalyticSubset (n := n) W) {r : ℕ} (hReg : RegularAtDim (n := n) H x r)
    (hSub : ∀ᶠ y in 𝓝 x, y ∈ H → y ∈ W) : LocDimGE (n := n) W x r := by
  obtain ⟨O,hO,hOpen,hxO⟩ := mem_nhds_iff.mp hSub
  let U : Opens X := ⟨O,hOpen⟩
  let x' : U := ⟨x,hxO⟩
  have hW' := isComplexAnalyticSubset_preimage_val hW U
  have hReg' : RegularAtDim (n := n) ((Subtype.val : U → X) ⁻¹' H) x' r :=
    regularAtDim_preimage_val_iff.mpr hReg
  have hSub' : (Subtype.val : U → X) ⁻¹' H ⊆ (Subtype.val : U → X) ⁻¹' W :=
    fun y hy => hO y.property hy
  exact locDimGE_preimage_val_iff.mp (locDimGE_of_regularAtDim_subset hW' hSub' hReg')

/-- Intrinsic local codimension at least two rules out every literal SNC
boundary slot as a contained trace at a genuine native cut point. -/
theorem native_boundary_exponent_zero_of_local_codimension_two
    (hP : NativeHSState P W A) (hD : IsInvDomain k P)
    (i : Fin P.E.length) (x : X) (hx : x ∈ P.cosupp) (hxE : x ∈ P.E.get i)
    (p : ℕ) (hCodim : p + 2 ≤ n) (hDim : LocDimLE (n := n) W x p) :
    divExpAlong n P.N P.ideal (P.E.get i) x = 0 := by
  apply native_boundary_exponent_zero_of_not_contained hP hD i x hx hxE
  intro hSub
  obtain ⟨r,hReg,hr⟩ := (snc_member_codimOne_geometry hD.isWellFormed.isSNCDivisor i).2.2 x hxE
  have hGE := locDimGE_of_regularAtDim_eventually_subset hP.2.1 hReg hSub
  obtain ⟨O,hO,hUpper⟩ := hDim
  obtain ⟨y,hy,b,hb,hWb⟩ := hGE O hO
  have := hUpper y hy b hWb
  omega

/-- A common intrinsic codimension bound derives simultaneous zero raw
exponents for independent source marks on the same ordered boundaries. -/
theorem independent_native_boundary_exponents_zero_of_local_codimension_two
    (hP : NativeHSState P W A) (hQ : NativeHSState Q W A)
    (hPD : IsInvDomain k P) (hQD : IsInvDomain l Q) (hE : Q.E = P.E)
    (hCodim : ∀ x ∈ P.cosupp, ∃ p, p + 2 ≤ n ∧ LocDimLE (n := n) W x p)
    (i : Fin P.E.length) (x : X) (hx : x ∈ P.cosupp) (hxE : x ∈ P.E.get i) :
    divExpAlong n P.N P.ideal (P.E.get i) x = 0 ∧
      divExpAlong n Q.N Q.ideal (P.E.get i) x = 0 := by
  obtain ⟨p,hp,hDim⟩ := hCodim x hx
  let j : Fin Q.E.length := ⟨i.val,hE.symm ▸ i.isLt⟩
  have hj : Q.E.get j = P.E.get i := by
    simp only [List.get_eq_getElem]
    exact getElem_congr hE rfl j.isLt
  have hxQ : x ∈ Q.cosupp := (locWPEquiv_native hP hQ hE).cosupp_eq_base ▸ hx
  refine ⟨native_boundary_exponent_zero_of_local_codimension_two hP hPD i x hx hxE p hp hDim,?_⟩
  exact hj ▸ native_boundary_exponent_zero_of_local_codimension_two
    hQ hQD j x hxQ (hj.symm ▸ hxE) p hp hDim

/-- The codimension hypothesis on the common intrinsic set supplies initial
exponent compatibility at unequal marks and canonicality on every common
ordinary history. -/
theorem independent_native_canonical_iff_of_local_codimension_two
    {Y : CMfd.{0} n} (hn : 0 < n) (hP : NativeHSState P W A) (hQ : NativeHSState Q W A)
    (hPD : IsInvDomain k P) (hQD : IsInvDomain k Q) (hE : Q.E = P.E)
    (hCodim : ∀ x ∈ P.cosupp, ∃ p, p + 2 ≤ n ∧ LocDimLE (n := n) W x p)
    (T : BlowupTower X Y) :
    IsCanonical P ((invFamily hn k).inv P) T ↔ IsCanonical Q ((invFamily hn k).inv Q) T := by
  refine invFamily_isCanonical_iff_of_local hn P Q hPD hQD (locWPEquiv_native hP hQ hE)
    (SameCarrierDim.of_N_eq (hP.2.2.1.trans hQ.2.2.1.symm)) ?_ T
  intro H hH x hx hxH
  obtain ⟨i,rfl⟩ := List.get_of_mem hH
  obtain ⟨ha,hb⟩ := independent_native_boundary_exponents_zero_of_local_codimension_two
    hP hQ hPD hQD hE hCodim i x hx hxH
  rw [ha,hb,Nat.mul_zero,Nat.mul_zero]

#print axioms independent_native_boundary_exponents_zero_of_local_codimension_two
#print axioms independent_native_canonical_iff_of_local_codimension_two

end
end Hironaka.HironakaG1NativeBoundaryCodimension
