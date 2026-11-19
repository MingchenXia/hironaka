import Hironaka.Resolution.HironakaG10SmoothBaseResidueFibre
import Hironaka.Resolution.HironakaG10FlatGermChain
import Hironaka.Resolution.HironakaG10FlatHorseshoe
import Mathlib.RingTheory.Flat.Equalizer

/-! Actual flatness of the native presentation cokernel preserves its exact
special-fibre complex in every smooth base dimension and every finite rank. -/

set_option autoImplicit false
open Set Filter
open scoped Topology TensorProduct Matrix

namespace Hironaka.HironakaG10SmoothBaseFibreExactness
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaActualJointBaseFibre
  HironakaRelativeNormalNearbyUniformRanks HironakaG10SmoothBaseResidueFibre
  HironakaG10FlatGermChain HironakaG10FlatHorseshoe HironakaG10FlatResolutionStart
  HironakaActualCentreJointJets HironakaHolomorphicJetChartInvariance
  OkaRelationSheaf OkaGermBridge

attribute [local instance] tangentAlgebra baseGermResidueAlgebra

/-- The quotient by the entire original germ-matrix image, with the actual
tangent-pullback base action. Restriction of scalars does not restrict the domain. -/
abbrev nativeCokernel {a b : ℕ} (d t : ℕ)
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d + t)))) : Type :=
  (Fin a → HolGerm (ComplexModel (d + t))) ⧸
    LinearMap.range (F.mulVecLin.restrictScalars (HolGerm (ComplexModel d)))

/-- A flat actual cokernel gives tensor exactness; the ambient modules need not be flat. -/
theorem tensor_exact_of_flat_nativeCokernel {a b c : ℕ} (d t : ℕ)
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d + t))))
    (G : Matrix (Fin b) (Fin c) (HolGerm (ComplexModel (d + t))))
    (hex : Function.Exact G.mulVecLin F.mulVecLin)
    (hflat : Module.Flat (HolGerm (ComplexModel d)) (nativeCokernel d t F)) :
    Function.Exact
      ((G.mulVecLin.restrictScalars (HolGerm (ComplexModel d))).lTensor ℂ)
      ((F.mulVecLin.restrictScalars (HolGerm (ComplexModel d))).lTensor ℂ) := by
  let f := F.mulVecLin.restrictScalars (HolGerm (ComplexModel d))
  let g := G.mulVecLin.restrictScalars (HolGerm (ComplexModel d))
  let _ : Module.Flat (HolGerm (ComplexModel d))
      ((Fin a → HolGerm (ComplexModel (d + t))) ⧸ LinearMap.range f) := hflat
  have hrange : Function.Exact g f.rangeRestrict := by
    intro x
    constructor
    · intro h
      exact (hex x).mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (hex x).mpr h
  have hinj : Function.Injective ((LinearMap.range f).subtype.lTensor ℂ) :=
    LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range f).mkQ
      (Submodule.mkQ_surjective _) (LinearMap.range f).subtype
      (Submodule.subtype_injective _) (LinearMap.exact_subtype_mkQ _) ℂ
  have hT := _root_.lTensor_exact ℂ hrange f.surjective_rangeRestrict
  have hcomp := hT.comp_injective ((LinearMap.range f).subtype.lTensor ℂ)
    hinj ((LinearMap.range f).subtype.lTensor ℂ).map_zero
  change Function.Exact (g.lTensor ℂ)
    (((LinearMap.range f).subtype.lTensor ℂ).comp (f.rangeRestrict.lTensor ℂ)) at hcomp
  rw [← LinearMap.lTensor_comp] at hcomp
  exact hcomp

/-- True exactness of the actual normal-fibre germ matrices, with no supplied fibre dictionary. -/
theorem trace_exact_of_flat_nativeCokernel {a b c : ℕ} (d t : ℕ)
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d + t))))
    (G : Matrix (Fin b) (Fin c) (HolGerm (ComplexModel (d + t))))
    (hex : Function.Exact G.mulVecLin F.mulVecLin)
    (hflat : Module.Flat (HolGerm (ComplexModel d)) (nativeCokernel d t F)) :
    Function.Exact (G.map (jointBaseZeroTrace d t)).mulVecLin
      (F.map (jointBaseZeroTrace d t)).mulVecLin := by
  have hT := tensor_exact_of_flat_nativeCokernel d t F G hex hflat
  intro v
  let w := (fibreTensorVectorEquiv d t b).symm v
  constructor
  · intro hv
    have hw : ((F.mulVecLin.restrictScalars (HolGerm (ComplexModel d))).lTensor ℂ) w = 0 := by
      apply (fibreTensorVectorEquiv d t a).injective
      rw [fibreTensorVectorEquiv_lTensor_mulVec, map_zero]
      simpa only [w, LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply] using hv
    obtain ⟨u, hu⟩ := (hT w).mp hw
    refine ⟨fibreTensorVectorEquiv d t c u, ?_⟩
    have h := congrArg (fibreTensorVectorEquiv d t b) hu
    rw [fibreTensorVectorEquiv_lTensor_mulVec] at h
    simpa only [w, LinearEquiv.apply_symm_apply, Matrix.mulVecLin_apply] using h
  · rintro ⟨u, rfl⟩
    have hzero := hT.apply_apply_eq_zero ((fibreTensorVectorEquiv d t c).symm u)
    have h := congrArg (fibreTensorVectorEquiv d t a) hzero
    rw [fibreTensorVectorEquiv_lTensor_mulVec, fibreTensorVectorEquiv_lTensor_mulVec,
      map_zero, LinearEquiv.apply_symm_apply] at h
    simpa only [Matrix.mulVecLin_apply] using h

/-- The project matrix-exactness predicate on the same actual special fibre. -/
theorem trace_matExact_of_flat_nativeCokernel {a b c : ℕ} (d t : ℕ)
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d + t))))
    (G : Matrix (Fin b) (Fin c) (HolGerm (ComplexModel (d + t))))
    (hex : Function.Exact G.mulVecLin F.mulVecLin)
    (hflat : Module.Flat (HolGerm (ComplexModel d)) (nativeCokernel d t F)) :
    MatExact (G.map (jointBaseZeroTrace d t)) (F.map (jointBaseZeroTrace d t)) :=
  fun v hv => (trace_exact_of_flat_nativeCokernel d t F G hex hflat v).mp hv

def normalFamily {a b : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ) :
    Fin a → Fin b → ComplexModel t → ℂ :=
  fun i j z => F i j (actualJointNormalInclusion d t z)

theorem holAt_normalFamily {a b : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    ∀ i j, HolAt (normalFamily d t F i j) 0 :=
  fun i j => eventually_differentiableAt_comp_clm (actualJointNormalInclusion d t) (hF i j)

theorem trace_germMat_eq_normalFamily {a b : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ)
    (hF : ∀ i j, HolAt (F i j) 0) :
    (germMat 0 F).map (jointBaseZeroTrace d t) = germMat 0 (normalFamily d t F) := by
  apply Matrix.ext
  intro i j
  change jointBaseZeroTrace d t (germAt 0 (F i j)) = germAt 0 (normalFamily d t F i j)
  rw [germAt_of_holAt (hF i j), germAt_of_holAt (holAt_normalFamily d t F hF i j)]
  unfold jointBaseZeroTrace
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp [normalFamily]

/-- Ordinary local exact starts with a flat actual cokernel give exactness
of holomorphic relation germs on the actual normal special fibre. -/
theorem normal_fibre_exact_of_flat_exactStart {a b c : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel (d + t) → ℂ)
    (G : Fin b → Fin c → ComplexModel (d + t) → ℂ)
    {U : Set (ComplexModel (d + t))} (hU : IsOpen U) (h0 : 0 ∈ U)
    (hstart : ExactStartOn U G F)
    (hflat : Module.Flat (HolGerm (ComplexModel d)) (nativeCokernel d t (germMat 0 F))) :
    ∀ v : Fin b → ComplexModel t → ℂ,
      IsRelationAt (normalFamily d t F) 0 v →
        IsCombinationAt (columns (normalFamily d t G)) 0 v := by
  have hF : ∀ i j, HolAt (F i j) 0 := fun i j => holAt_of_differentiableOn hU (hstart.holF i j) h0
  have hG : ∀ j k, HolAt (G j k) 0 := fun j k => holAt_of_differentiableOn hU (hstart.holG j k) h0
  have hmat := matExact_of_exactStartOn hU hstart h0
  have hcomp : germMat 0 F * germMat 0 G = 0 := by
    rw [germMat_mul hF hG]
    apply germMat_eq_zero (fun i k => HolAt.fintype_sum fun j => (hF i j).mul (hG j k))
    filter_upwards [hU.mem_nhds h0] with x hx i k
    exact hstart.comp i k x hx
  have hex : Function.Exact (germMat 0 G).mulVecLin (germMat 0 F).mulVecLin := by
    intro v
    constructor
    · exact hmat v
    · rintro ⟨u, rfl⟩
      change germMat 0 F *ᵥ (germMat 0 G *ᵥ u) = 0
      rw [Matrix.mulVec_mulVec, hcomp, Matrix.zero_mulVec]
  apply (exact_iff_matExact (holAt_normalFamily d t F hF) (holAt_normalFamily d t G hG)).mpr
  have h := trace_matExact_of_flat_nativeCokernel d t (germMat 0 F) (germMat 0 G) hex hflat
  simpa only [trace_germMat_eq_normalFamily d t F hF, trace_germMat_eq_normalFamily d t G hG] using h

end
end Hironaka.HironakaG10SmoothBaseFibreExactness
