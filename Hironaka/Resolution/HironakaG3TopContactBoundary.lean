import Hironaka.Resolution.HironakaG3BoundaryContainedAnalyticTrace
import Hironaka.Resolution.HironakaG3RPureFinal
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Invariant.CodimOneAdmissibleAlong

/-!
# The full original boundary at the top contact dimension

A pure analytic subset of a closed smooth contact, of the same dimension as
that contact, is open in it. This derives equality of their ambient germs at
target points. Residual transversality and the existing containing-member
comparison then give normal crossings with every original boundary member.
The actual identity tower supplies the endpoint, including zero dimensions.

Blueprint: `hironaka-g3-top-contact-boundary.tex`.
-/

set_option autoImplicit false

open Set Filter Function TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG3TopContactBoundary

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison CodimOneAdmissibleAlong
  SubmanifoldChartedSpace HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionRegularity HironakaG3BoundaryContainedAnalyticTrace
  HironakaDisjointFiniteControlledHistory HironakaSharpActualFiniteChronologicalHistory

/-- A pure analytic target of the full contact dimension is an ambient open
part of that contact and is regular of the same dimension everywhere. -/
theorem exists_open_eq_inter_contact {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    (hpure : W ⊆ closure (regularLocus (n := d+t) W d)) :
    ∃ O : Opens X, W = N ∩ (O : Set X) ∧
      ∀ x ∈ W, RegularAtDim (n := d+t) W x d := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  let V : Set (nativeManifold (Nat.le_add_right d t) N hN) := (Subtype.val : N → X) ⁻¹' W
  have hImage : (Subtype.val : N → X) '' V = W := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp
    · intro hx
      exact ⟨⟨x,hWN hx⟩,hx,rfl⟩
  have hImageA : IsComplexAnalyticSubset (n := d+t) ((Subtype.val : N → X) '' V) := by
    rw [hImage]
    exact hWa
  have hVa := native_analytic_of_ambient_image N hN V hImageA
  have hImagePure : ((Subtype.val : N → X) '' V) ⊆
      closure (regularLocus (n := d+t) ((Subtype.val : N → X) '' V) d) := by
    rw [hImage]
    exact hpure
  have hVPure := native_pure_of_ambient_image N hNc hN V d hImagePure
  obtain ⟨hVo,hVreg⟩ := HironakaG3RPureFinal.isOpen_of_pure_of_le hVa le_rfl hVPure
  obtain ⟨O,hO,hOV⟩ := (isOpen_induced_iff (f := (Subtype.val : N → X))).mp hVo
  refine ⟨⟨O,hO⟩,?_,?_⟩
  · ext x
    constructor
    · intro hx
      refine ⟨hWN hx,?_⟩
      have hxV : (⟨x,hWN hx⟩ : N) ∈ V := hx
      rw [←hOV] at hxV
      exact hxV
    · rintro ⟨hxN,hxO⟩
      have hxV : (⟨x,hxN⟩ : N) ∈ (Subtype.val : N → X) ⁻¹' O := hxO
      rw [hOV] at hxV
      exact hxV
  · intro x hx
    let p : N := ⟨x,hWN hx⟩
    have hr := (regularAtDim_native_image_iff (Nat.le_add_right d t) hN V p d).mpr
      (hVreg p hx)
    rwa [hImage] at hr

/-- The full original SNC list is already normal crossings with a target of
equal contact dimension; no future history or caller NC premise is needed. -/
theorem hasNormalCrossings_full_boundary {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    (hpure : W ⊆ closure (regularLocus (n := d+t) W d))
    (E B : List (Set X)) (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hTrans : IsTransverse (d+t) N B)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H) :
    HasNormalCrossings (d+t) W E := by
  obtain ⟨O,hWO,_hReg⟩ := exists_open_eq_inter_contact N hNc hN W hWa hWN hpure
  have hNCB : HasNormalCrossings (d+t) W B := by
    apply hasNormalCrossings_of_forall_eventually
    intro x hx
    have hxNO : x ∈ N ∩ (O : Set X) := by rwa [←hWO]
    refine ⟨N,hWN hx,?_,hTrans.hasNormalCrossings⟩
    filter_upwards [O.isOpen.mem_nhds hxNO.2] with y hyO
    rw [hWO]
    exact ⟨fun hy => hy.1,fun hy => ⟨hy,hyO⟩⟩
  exact (hasNormalCrossings_iff_of_forall_mem hE
    (fun _ hH => hBsub.subset hH)
    (fun H hH hNot => hWN.trans (hOmitted H hH hNot))).mp hNCB

/-- The actual empty tower supplies the full-boundary equal-contact endpoint,
with unchanged original ideals and boundary, and identity projection. -/
theorem identity_tower_geometry {d t : ℕ} {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    (hpure : W ⊆ closure (regularLocus (n := d+t) W d))
    (E B : List (Set X)) (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hTrans : IsTransverse (d+t) N B)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H) :
    let T : BlowupTower X X := .refl
    let M := fullMarked E (vanishingIdeal (n := d+t) W)
    IsGeoTestTower M T ∧
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      strictTransform (d+t) T.proj W = W ∧
      IsClosedSubmanifold (d+t) (geoTransformAlong (geometricTemplate W []) T).N ∧
      (∀ x ∈ W, RegularAtDim (n := d+t) W x d) ∧
      IsSNCDivisor (d+t) (geoTransformAlong M T).E ∧
      HasNormalCrossings (d+t) (geoTransformAlong (geometricTemplate W []) T).N
        (geoTransformAlong M T).E ∧
      IsProperMap T.proj ∧ IsIsomorphismOver (d+t) T.proj univ := by
  obtain ⟨_O,_hWO,hReg⟩ := exists_open_eq_inter_contact N hNc hN W hWa hWN hpure
  have hNC := hasNormalCrossings_full_boundary N hNc hN W hWa hWN hpure
    E B hE hBsub hTrans hOmitted
  refine ⟨trivial,trivial,trivial,?_,⟨hWa.isClosed,fun x hx => ⟨d,hReg x hx⟩⟩,
    hReg,hE,hNC,isProperMap_id,?_⟩
  · simp [strictTransform,exceptionalLocus_id,hWa.isClosed.closure_eq]
  · change IsIsomorphismOver (d+t) (id : X → X) univ
    exact ⟨bijOn_id _,by rw [exceptionalLocus_id]; exact disjoint_empty _⟩

end

end Hironaka.HironakaG3TopContactBoundary
