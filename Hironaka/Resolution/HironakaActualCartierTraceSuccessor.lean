import Hironaka.Resolution.HironakaActualPolymorphicBornExponent
import Hironaka.Blowup.BlowupExistence
import Hironaka.Resolution.HironakaLocalPrincipalization

/-!
# A test-free native Cartier trace successor

The carrier may have varying local dimensions. Genuine coordinate density
and actual properness produce a selected strict-carrier lift independently
of any queried ideal, mark or native test. Every old boundary position is
retained, including the distinguished position whose trace becomes empty.
Blueprint FIRST: `hironaka-actual-cartier-trace-successor.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCartierTraceSuccessor
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers NormalCrossings BlowupFlatCoordinates MonomialPart GiraudAlong
  DivisorExponentAlong MemberInterAlong BoundaryCount SimultaneousNormalCrossings
  BlowupStrictSubmanifold BlowupStrictIdeal BlowupSNCTransform ExceptionalPushforwardAlong

variable {m : ℕ} {X Y : CMfd.{u} m}

/-- The centre and divisor predicates are logically equivalent on the same
carrier, including all exponents and points. No finiteness is assumed. -/
theorem isDivNearAlong_inter_carrier_iff
    (N D : Set X) (I : GermIdeal m X) (e : ℕ) (x : X) :
    IsDivNearAlong m N I (N ∩ D) e x ↔ IsDivNearAlong m N I D e x := by
  constructor
  · intro h
    exact Filter.Eventually.mono h fun y hy hyN hyD => hy hyN ⟨hyN,hyD⟩
  · intro h
    exact Filter.Eventually.mono h fun y hy hyN hyC => hy hyN hyC.2

/-- Transport the entire predicate before unfolding the native least-failure
exponent. The fallback value also agrees, without a domain premise. -/
theorem divExpAlong_inter_carrier
    (N D : Set X) (I : GermIdeal m X) (x : X) :
    divExpAlong m N I (N ∩ D) x = divExpAlong m N I D x := by
  have hPred : IsDivNearAlong m N I (N ∩ D) = IsDivNearAlong m N I D :=
    funext fun e => funext fun y =>
      propext (isDivNearAlong_inter_carrier_iff N D I e y)
  unfold divExpAlong
  rw [hPred]

private theorem carrier_density {N : Set X} {E : List (Set X)}
    (hT : IsTransverse m N E) (i : Fin E.length) :
    N ⊆ closure (N \ E.get i) := by
  intro x hxN
  by_cases hxi : x ∈ E.get i
  · obtain ⟨S₀,S,⟨Φ,hsrc,h0,hflat⟩,hS⟩ := hT x hxN
    obtain ⟨t,ht⟩ := Finset.card_eq_one.mp (hS i hxi).1
    have htS₀ : t ∉ S₀ := by
      have hdis := (hS i hxi).2
      rw [ht] at hdis
      exact Finset.disjoint_singleton_left.mp hdis
    have hxFlat : x ∈ flatDomain Φ := ⟨mem_chart_source _ x,Φ.center_mem_source⟩
    apply mem_closure_iff_frequently.mpr
    refine (frequently_flatMap_ne_zero hsrc hxFlat {t}).mono ?_
    rintro y ⟨hyFlat,hyne,hyfixed⟩
    have hyN : y ∈ N := by
      apply (hflat none hxN hyFlat.1 hyFlat.2).mpr
      intro l hl
      have hlt : l ∉ ({t} : Finset (Fin m)) := by
        simpa only [Finset.mem_singleton] using (fun h : l=t => htS₀ (h ▸ hl))
      change flatMap Φ y l = 0
      rw [hyfixed l hlt]
      change Φ.toFun (chartAt (ComplexModel m) x x) l = 0
      exact congrArg (fun w : ComplexModel m => w l) h0
    refine ⟨hyN,?_⟩
    intro hyD
    have hyzero := (hflat (some i) hxi hyFlat.1 hyFlat.2).mp hyD
    exact hyne t (Finset.mem_singleton_self t)
      (hyzero t (by change t ∈ S i; rw [ht];exact Finset.mem_singleton_self t))
  · exact subset_closure ⟨hxN,hxi⟩

private theorem member_interior_empty {E : List (Set X)} (hE : IsSNCDivisor m E)
    (i : Fin E.length) : interior (E.get i) = ∅ := by
  have hDense : closure (E.get i)ᶜ = univ := by
    apply eq_univ_of_univ_subset
    intro x _hx
    have hDiff : (univ : Set X) \ E.get i = (E.get i)ᶜ := by
      ext y
      exact ⟨fun h=>h.2,fun h=>⟨mem_univ y,h⟩⟩
    rw [←hDiff]
    exact carrier_density (isTransverse_univ_of_isSNCDivisor hE) i (mem_univ x)
  rw [closure_compl] at hDense
  simpa using congrArg (fun A : Set X => Aᶜ) hDense

private theorem strict_carrier_image {N : Set X} {E : List (Set X)}
    (hN : IsClosed N) (hT : IsTransverse m N E) (i : Fin E.length)
    {π : Y → X} (hπ : IsBlowupAlong m (N ∩ E.get i) π) :
    π '' geoStrictTransform π (N ∩ E.get i) N = N := by
  let C := N ∩ E.get i
  let N' := geoStrictTransform π C N
  have hClosed : IsClosed (π '' N') :=
    (HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hπ).isClosedMap _ isClosed_closure
  have hSub : N \ C ⊆ π '' N' := by
    rintro x ⟨hxN,hxC⟩
    obtain ⟨y,hy⟩ := HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ x
    refine ⟨y,subset_closure ⟨?_,?_⟩,hy⟩
    · simpa only [hy] using hxN
    · simpa only [hy] using hxC
  have hDense : N ⊆ closure (N \ C) := by
    apply (carrier_density hT i).trans
    apply closure_mono
    rintro x ⟨hxN,hxD⟩
    exact ⟨hxN,fun hxC=>hxD hxC.2⟩
  apply Subset.antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN hy
  · exact hDense.trans (hClosed.closure_subset_iff.mpr hSub)

/-- Construct a genuine blowup of the ENTIRE actual Cartier trace from pure
geometry alone, retaining the old distinguished position after its trace is
empty, and select a strict-carrier lift above the same given point. -/
theorem exists_pure_cartier_trace_successor
    (hm : 0 < m) (N : Set X) (E : List (Set X))
    (hN : IsClosedSubmanifold m N) (hE : IsSNCDivisor m E)
    (hT : IsTransverse m N E) (i : Fin E.length)
    (z : X) (hz : z ∈ N ∩ E.get i) :
    ∃ (Y : CMfd.{u} m) (π : Y → X)
      (_hπ : IsBlowupAlong m (N ∩ E.get i) π) (z' : Y),
      let C := N ∩ E.get i
      let N' := geoStrictTransform π C N
      let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
      IsClosedSubmanifold m N' ∧ IsSNCDivisor m E' ∧
      IsTransverse m N' E' ∧ π '' N' = N ∧
      z' ∈ N' ∧ π z' = z ∧ z' ∈ π ⁻¹' C ∧
      N' ∩ geoStrictTransform π C (E.get i) = ∅ ∧
      E'.length = E.length+1 ∧
      (∀ h : Fin E.length, E'.get ⟨h.val, by
        dsimp [E']; simp only [List.length_append,List.length_map,List.length_singleton]; omega⟩ =
        geoStrictTransform π C (E.get h)) ∧
      E'.getLast (by dsimp [E']; simp) = π ⁻¹' C := by
  let C := N ∩ E.get i
  have hC : IsClosedSubmanifold m C := by
    simpa only [memberInter_singleton] using
      isClosedSubmanifold_inter_memberInter hm hN.1 hE hT {i}
  have hNC : HasNormalCrossings m C E := by
    simpa only [memberInter_singleton] using hasNormalCrossings_inter_memberInter hT {i}
  have hInt : interior C = ∅ :=
    eq_empty_of_subset_empty ((interior_mono (inter_subset_right : C ⊆ E.get i)).trans
      (member_interior_empty hE i).subset)
  obtain ⟨Y0,tY,cY,hY,π,hπ⟩ := BlowupExistence.exists_isBlowupAlong C hC hInt
  let := tY
  let := cY
  let := hY
  let Y : CMfd.{u} m := CMfd.of Y0
  have hπ' : IsBlowupAlong m C (π : Y → X) := hπ
  let N' := geoStrictTransform π C N
  let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  have hN' : IsClosedSubmanifold m N' :=
    isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ' hN inter_subset_left
  have hAdapt : ∀ x∈C,IsAdaptedAt m C N E x :=
    fun _ hx=>isAdaptedAt_of_hasNormalCrossings hm inter_subset_left hE hT hNC hx
  have hE' : IsSNCDivisor m E' := isSNCDivisor_geoTransformE hπ' hE hAdapt
  have hT' : IsTransverse m N' E' := isTransverse_geoTransformE hπ' hN.1 hE hT hAdapt
  have hImage : π '' N' = N := strict_carrier_image (Y:=Y) hN.1 hT i (π:=π) hπ'
  obtain ⟨z',hzN',hzMap⟩ := hImage.symm ▸ hz.1
  have hSeparated : N' ∩ geoStrictTransform π C (E.get i) = ∅ := by
    have hInter := geoStrictTransform_inter_eq hπ' hN.1 inter_subset_left hE hT hNC i
    have hSource : E.get i ∩ N = C := inter_comm _ _
    rw [hSource] at hInter
    have hEmpty : geoStrictTransform π C C = ∅ := by
      simp [geoStrictTransform]
    rw [hEmpty] at hInter
    exact (inter_comm _ _).trans hInter.symm
  refine ⟨Y,π,hπ',z',hN',hE',hT',hImage,hzN',hzMap,?_,hSeparated,by simp,?_,?_⟩
  · change π z'∈C
    rw [hzMap]
    exact hz
  · intro h
    rw [get_map_append_singleton]
    exact dif_pos h.isLt
  · simp

end
end Hironaka.HironakaActualCartierTraceSuccessor
