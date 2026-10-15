/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionTangentContact
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionContactCoefficientRestriction
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSmoothSubmersionTangentContact HironakaSmoothSubmersionRelativeDifferentialIdeals
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaSmoothSubmersionRelativeOrder
  HironakaSmoothSubmersionRelativeGeometry GermIdealPullbackCalculus RestrictedIdealExtension
  HomogenizedIdealAlong TangentDirectionAlong MarkedIdeals MarkedIdeal GermIdealOrder
noncomputable section
variable {n m : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {f : Y → X}

theorem opens_inverse_holomorphic (U : TopologicalSpace.Opens X) (hU : Nonempty U) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (U.openPartialHomeomorphSubtypeCoe hU).symm
      (U.openPartialHomeomorphSubtypeCoe hU).target := by
  let e := U.openPartialHomeomorphSubtypeCoe hU
  have hval : ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      ((Subtype.val : U → X) ∘ e.symm) e.target := by
    apply contMDiffOn_id.congr
    intro x hx
    exact e.right_inv hx
  intro x hx
  exact (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm e.target x).mp (hval x hx)

theorem restrictedChart_mem_maximal (U : TopologicalSpace.Opens X) (hU : Nonempty U)
    (e : OpenPartialHomeomorph X (ComplexModel n))
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ X) :
    (U.openPartialHomeomorphSubtypeCoe hU).trans e ∈
      IsManifold.maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ U := by
  let v := U.openPartialHomeomorphSubtypeCoe hU
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (e ∘ (Subtype.val : U → X)) (v.source ∩ v ⁻¹' e.source)
    exact (contMDiffOn_of_mem_maximalAtlas he).comp
      contMDiff_subtype_val.contMDiffOn (fun _ hz => hz.2)
  · change ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (v.symm ∘ e.symm) (e.target ∩ e.symm ⁻¹' v.target)
    exact (opens_inverse_holomorphic U hU).comp
      ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left) (fun _ hz => hz.2)

def preimageOpen
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (U : TopologicalSpace.Opens X) : TopologicalSpace.Opens Y :=
  ⟨f ⁻¹' (U : Set X),U.isOpen.preimage hf.contMDiff.continuous⟩

def openMap
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (U : TopologicalSpace.Opens X) : preimageOpen hf U → U :=
  fun y => ⟨f y.val,y.property⟩

theorem openMap_isSubmersionOfComplement
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (U : TopologicalSpace.Opens X) :
    Manifold.IsSubmersionOfComplement hf.complement
      𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (openMap hf U) := by
  intro y
  let V := preimageOpen hf U
  let h := hf.isSubmersionOfComplement_complement y.val
  have hV : Nonempty V := ⟨y⟩
  have hU : Nonempty U := ⟨openMap hf U y⟩
  let a := V.openPartialHomeomorphSubtypeCoe hV
  let b := U.openPartialHomeomorphSubtypeCoe hU
  let d := a.trans h.domChart
  let c := b.trans h.codChart
  apply Manifold.IsSubmersionAtOfComplement.mk_of_charts h.equiv d c
  · exact ⟨mem_univ _,h.mem_domChart_source⟩
  · exact ⟨mem_univ _,h.mem_codChart_source⟩
  · exact restrictedChart_mem_maximal V hV h.domChart h.domChart_mem_maximalAtlas
  · exact restrictedChart_mem_maximal U hU h.codChart h.codChart_mem_maximalAtlas
  · intro z hz
    exact ⟨mem_univ _,h.source_subset_preimage_source hz.2⟩
  · intro z hz
    have hz' : z ∈ d.target := by simpa [mfld_simps] using hz
    have ha : (a.symm (h.domChart.symm z)).val = h.domChart.symm z := a.right_inv hz'.2
    have hzo : z ∈ (h.domChart.extend 𝓘(ℂ, ComplexModel m)).target := by
      simpa [mfld_simps] using hz'.1
    have he := h.writtenInCharts hzo
    simpa [c,d,b,OpenPartialHomeomorph.extend,Function.comp_def,mfld_simps,openMap,ha] using he

theorem openMap_isSubmersion
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (U : TopologicalSpace.Opens X) :
    Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (openMap hf U) :=
  (openMap_isSubmersionOfComplement hf U).isSubmersion

theorem whole_marked_open_square
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (U : TopologicalSpace.Opens X) (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) :
    markedPullback (m := m) (openMap hf U)
      (markedPullback (m := n) (Subtype.val : U → X) M) =
      markedPullback (m := m) (Subtype.val : preimageOpen hf U → Y)
        (markedPullback (m := m) f M) := by
  calc
    _ = markedPullback (m := m) ((Subtype.val : U → X) ∘ openMap hf U) M :=
      (whole_markedPullback_comp contMDiff_subtype_val
        (openMap_isSubmersion hf U).contMDiff M hI).symm
    _ = markedPullback (m := m) (f ∘ (Subtype.val : preimageOpen hf U → Y)) M := rfl
    _ = _ := whole_markedPullback_comp hf.contMDiff contMDiff_subtype_val M hI

def contactCoefficient (M : MarkedIdeal n X) (C : Set X) : MarkedIdeal n X where
  N := C
  E := (coeffMarkedAlong M).E
  ideal := restrictOn n C (coeffMarkedAlong M).ideal
  d := (coeffMarkedAlong M).d

theorem contactCoefficient_pullback
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (C : Set X) (hC : IsClosedSubmanifold n C) :
    markedPullback (m := m) f (contactCoefficient M C) =
      contactCoefficient (markedPullback (m := m) f M) (f ⁻¹' C) := by
  have hc := HironakaSmoothSubmersionRelativeDifferentialIdeals.pullback_coeffMarkedAlong hf M hI hN
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  change GermIdeal.pullback (m := m) f (restrictOn n C (coeffMarkedAlong M).ideal) =
    restrictOn m (f ⁻¹' C) (coeffMarkedAlong (markedPullback (m := m) f M)).ideal
  rw [pullback_restrictOn_eq hf (isCoherent_coeffMarkedAlong hI hN) hC]
  exact congrArg (restrictOn m (f ⁻¹' C)) (congrArg MarkedIdeal.ideal hc)

theorem contactCoefficient_isCoherent
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (C : Set X) (hC : IsClosedSubmanifold n C) :
    (contactCoefficient M C).ideal.IsCoherent :=
  isCoherent_restrictOn_of_isClosedSubmanifold (isCoherent_coeffMarkedAlong hI hN) hC

theorem contactCoefficient_cosupp_preimage
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (C : Set X) (hC : IsClosedSubmanifold n C) :
    (contactCoefficient (markedPullback (m := m) f M) (f ⁻¹' C)).cosupp =
      f ⁻¹' (contactCoefficient M C).cosupp := by
  rw [← contactCoefficient_pullback hf M hI hN C hC]
  exact cosupport_preimage_eq hf (contactCoefficient_isCoherent M hI hN C hC)
    (contactCoefficient M C).N (contactCoefficient M C).d

def openContact (U : TopologicalSpace.Opens X) (M : MarkedIdeal n X) (u : X → ℂ) : Set U :=
  (Subtype.val : U → X) ⁻¹' contactCarrier M.N (U : Set X) u

theorem openMap_preimage_contact
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (U : TopologicalSpace.Opens X) (M : MarkedIdeal n X) (u : X → ℂ) :
    (openMap hf U) ⁻¹' openContact U M u =
      openContact (preimageOpen hf U) (markedPullback (m := m) f M) (u ∘ f) := by
  ext y
  rfl

theorem whole_reduced_open_record
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (U : TopologicalSpace.Opens X) (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n M.N) (u : X → ℂ)
    (hC : IsClosedSubmanifold n (openContact U M u)) :
    markedPullback (m := m) (openMap hf U)
      (contactCoefficient (X := CMfd.of (n := n) U) (markedPullback (m := n) (Subtype.val : U → X) M) (openContact U M u)) =
      contactCoefficient (X := CMfd.of (n := m) (preimageOpen hf U))
        (markedPullback (m := m) (Subtype.val : preimageOpen hf U → Y) (markedPullback (m := m) f M))
        (openContact (preimageOpen hf U) (markedPullback (m := m) f M) (u ∘ f)) := by
  rw [contactCoefficient_pullback (X := CMfd.of (n := n) U)
    (Y := CMfd.of (n := m) (preimageOpen hf U)) (openMap_isSubmersion hf U) _
    (isCoherent_pullback contMDiff_subtype_val hI)
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U) _ hC,
    whole_marked_open_square hf U M hI,openMap_preimage_contact]

theorem whole_reduced_open_cosupp
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (U : TopologicalSpace.Opens X) (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n M.N) (u : X → ℂ)
    (hC : IsClosedSubmanifold n (openContact U M u)) :
    (contactCoefficient (X := CMfd.of (n := m) (preimageOpen hf U))
        (markedPullback (m := m) (Subtype.val : preimageOpen hf U → Y) (markedPullback (m := m) f M))
        (openContact (preimageOpen hf U) (markedPullback (m := m) f M) (u ∘ f))).cosupp =
      (openMap hf U) ⁻¹'
        (contactCoefficient (X := CMfd.of (n := n) U) (markedPullback (m := n) (Subtype.val : U → X) M) (openContact U M u)).cosupp := by
  rw [← whole_reduced_open_record hf U M hI hN u hC]
  exact cosupport_preimage_eq (openMap_isSubmersion hf U)
    (contactCoefficient_isCoherent (X := CMfd.of (n := n) U) _ (isCoherent_pullback contMDiff_subtype_val hI)
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U) _ hC) _ _

theorem exists_joint_original_contact_reductions
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (hd : 1 ≤ M.d) (y : Y) (hy : y ∈ (markedPullback (m := m) f M).cosupp)
    (hmax : ¬ OrderGE n M.N M.ideal (f y) (M.d+1)) :
    ∃ (U : TopologicalSpace.Opens X) (u : X → ℂ), f y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d (U : Set X) u ∧
      IsTangentDirectionAlong (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal)
        M.d (preimageOpen hf U : Set Y) (u ∘ f) ∧
      IsClosedSubmanifold n (openContact U M u) ∧
      IsClosedSubmanifold m
        (openContact (preimageOpen hf U) (markedPullback (m := m) f M) (u ∘ f)) ∧
      Manifold.IsSubmersionOfComplement hf.complement
        𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ (openMap hf U) ∧
      markedPullback (m := m) (openMap hf U)
        (contactCoefficient (X := CMfd.of (n := n) U)
          (markedPullback (m := n) (Subtype.val : U → X) M) (openContact U M u)) =
        contactCoefficient (X := CMfd.of (n := m) (preimageOpen hf U))
          (markedPullback (m := m) (Subtype.val : preimageOpen hf U → Y) (markedPullback (m := m) f M))
          (openContact (preimageOpen hf U) (markedPullback (m := m) f M) (u ∘ f)) ∧
      (contactCoefficient (X := CMfd.of (n := m) (preimageOpen hf U))
          (markedPullback (m := m) (Subtype.val : preimageOpen hf U → Y) (markedPullback (m := m) f M))
          (openContact (preimageOpen hf U) (markedPullback (m := m) f M) (u ∘ f))).cosupp =
        (openMap hf U) ⁻¹'
          (contactCoefficient (X := CMfd.of (n := n) U)
            (markedPullback (m := n) (Subtype.val : U → X) M) (openContact U M u)).cosupp := by
  obtain ⟨U,u,hyU,hu,hup,hC,hCp,_,_⟩ := exists_joint_original_closed_contacts hf hI hN hd y hy hmax
  exact ⟨U,u,hyU,hu,hup,hC,hCp,openMap_isSubmersionOfComplement hf U,
    whole_reduced_open_record hf U M hI hN u hC,whole_reduced_open_cosupp hf U M hI hN u hC⟩

end
end Hironaka.HironakaSmoothSubmersionContactCoefficientRestriction
