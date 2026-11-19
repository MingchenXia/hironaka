import Hironaka.Resolution.HironakaG10SmoothBaseFibreExactness
import Hironaka.Resolution.HironakaG10SmoothBaseMatrixFlatness
import Hironaka.Resolution.HironakaG10OneParameterQuotientFlatness

/-! Actual one-row quotient flatness over every smooth base germ is
equivalent to exactness of the actual normal fibre of an ordinary exact start. -/

set_option autoImplicit false
open Set Filter
open scoped Topology Matrix

namespace Hironaka.HironakaG10SmoothBaseQuotientFlatCriterion
noncomputable section
open HolGerm OkaRelationSheaf OkaGermBridge HironakaRelativeNormalIdeal
  HironakaG10FlatGermChain HironakaG10FlatResolutionStart
  HironakaG10HirChartFlattener HironakaG10SmoothBaseFibreExactness
  HironakaG10SmoothBaseMatrixFlatness HironakaG10OneParameterQuotientFlatness

attribute [local instance] tangentAlgebra

def rowIdeal {b : ℕ} (d t : ℕ)
    (F : Matrix (Fin 1) (Fin b) (HolGerm (ComplexModel (d + t)))) :
    Ideal (HolGerm (ComplexModel (d + t))) :=
  Ideal.span (Set.range fun j => F 0 j)

/-- The generic one-row image theorem supplies the whole quotient dictionary. -/
def rowCokernelQuotientEquiv {b : ℕ} (d t : ℕ)
    (F : Matrix (Fin 1) (Fin b) (HolGerm (ComplexModel (d + t)))) :
    ((Fin 1 → HolGerm (ComplexModel (d + t))) ⧸ LinearMap.range F.mulVecLin)
      ≃ₗ[HolGerm (ComplexModel (d + t))] HolGerm (ComplexModel (d + t)) ⧸ rowIdeal d t F :=
  Submodule.Quotient.equiv (LinearMap.range F.mulVecLin) (rowIdeal d t F)
    (LinearEquiv.funUnique (Fin 1) (HolGerm (ComplexModel (d + t)))
      (HolGerm (ComplexModel (d + t)))) (one_row_image_eq_ideal F)

/-- The dictionary respects the actual tangent action and literal quotient structure map. -/
def nativeCokernelQuotientEquiv {b : ℕ} (d t : ℕ)
    (F : Matrix (Fin 1) (Fin b) (HolGerm (ComplexModel (d + t)))) :
    letI : Module (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d + t)) ⧸ rowIdeal d t F) :=
        Module.compHom _ (chartMap d t (rowIdeal d t F))
    nativeCokernel d t F ≃ₗ[HolGerm (ComplexModel d)]
      HolGerm (ComplexModel (d + t)) ⧸ rowIdeal d t F := by
  letI : Module (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d + t)) ⧸ rowIdeal d t F) :=
    Module.compHom _ (chartMap d t (rowIdeal d t F))
  refine { (rowCokernelQuotientEquiv d t F).toAddEquiv with map_smul' := ?_ }
  intro a x
  refine Submodule.Quotient.induction_on
    (LinearMap.range (F.mulVecLin.restrictScalars (HolGerm (ComplexModel d)))) x ?_
  intro v
  change Ideal.Quotient.mk (rowIdeal d t F) (tangentPullback d t a * v 0) =
    Ideal.Quotient.mk (rowIdeal d t F) (tangentPullback d t a) *
      Ideal.Quotient.mk (rowIdeal d t F) (v 0)
  exact (Ideal.Quotient.mk (rowIdeal d t F)).map_mul _ _

/-- Ring-map flatness and actual native-cokernel flatness use the same internally derived action. -/
theorem chartMap_flat_iff_nativeCokernel {b : ℕ} (d t : ℕ)
    (F : Matrix (Fin 1) (Fin b) (HolGerm (ComplexModel (d + t)))) :
    (chartMap d t (rowIdeal d t F)).Flat ↔
      Module.Flat (HolGerm (ComplexModel d)) (nativeCokernel d t F) := by
  let _ : Module (HolGerm (ComplexModel d))
      (HolGerm (ComplexModel (d + t)) ⧸ rowIdeal d t F) :=
    Module.compHom _ (chartMap d t (rowIdeal d t F))
  change Module.Flat (HolGerm (ComplexModel d))
    (HolGerm (ComplexModel (d + t)) ⧸ rowIdeal d t F) ↔ _
  constructor
  · intro h
    let _ := h
    exact Module.Flat.of_linearEquiv (nativeCokernelQuotientEquiv d t F)
  · intro h
    let _ := h
    exact Module.Flat.of_linearEquiv (nativeCokernelQuotientEquiv d t F).symm

/-- Any ordinary local exact start detects actual quotient flatness on its same normal fibre. -/
theorem chartMap_flat_iff_normal_fibre_exact {b c : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel (d + t) → ℂ)
    (G : Fin b → Fin c → ComplexModel (d + t) → ℂ)
    {U : Set (ComplexModel (d + t))} (hU : IsOpen U) (h0 : 0 ∈ U)
    (hstart : ExactStartOn U G F) :
    (chartMap d t (HironakaG10LinearCurveMatrixPullback.entryIdeal d t F)).Flat ↔
      ∀ v : Fin b → ComplexModel t → ℂ,
        IsRelationAt (normalFamily d t F) 0 v →
          IsCombinationAt (columns (normalFamily d t G)) 0 v := by
  constructor
  · intro hflat
    exact normal_fibre_exact_of_flat_exactStart d t F G hU h0 hstart
      ((chartMap_flat_iff_nativeCokernel d t (germMat 0 F)).mp hflat)
  · intro hfib
    apply chartMap_entryIdeal_flat_of_specialFibreExact d t F G
      (fun i j => holAt_of_differentiableOn hU (hstart.holF i j) h0)
      (fun j k => holAt_of_differentiableOn hU (hstart.holG j k) h0)
    · intro i k
      filter_upwards [hU.mem_nhds h0] with x hx
      exact hstart.comp i k x hx
    · exact hfib

/-- Oka supplies an ordinary exact start internally; only its fibre exactness detects flatness. -/
theorem chartMap_flat_iff_exists_exact_start {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel (d + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    (chartMap d t (HironakaG10LinearCurveMatrixPullback.entryIdeal d t F)).Flat ↔
      ∃ U : Set (ComplexModel (d + t)), IsOpen U ∧ 0 ∈ U ∧
        ∃ (c : ℕ) (G : Fin b → Fin c → ComplexModel (d + t) → ℂ),
          ExactStartOn U G F ∧
            ∀ v : Fin b → ComplexModel t → ℂ,
              IsRelationAt (normalFamily d t F) 0 v →
                IsCombinationAt (columns (normalFamily d t G)) 0 v := by
  constructor
  · intro hflat
    obtain ⟨U, hU, h0, c, G, hstart⟩ := exists_exactStartOn_euclidean (d + t) F 0 hF
    exact ⟨U, hU, h0, c, G, hstart,
      (chartMap_flat_iff_normal_fibre_exact d t F G hU h0 hstart).mp hflat⟩
  · rintro ⟨U, hU, h0, c, G, hstart, hfib⟩
    exact (chartMap_flat_iff_normal_fibre_exact d t F G hU h0 hstart).mpr hfib

end
end Hironaka.HironakaG10SmoothBaseQuotientFlatCriterion
