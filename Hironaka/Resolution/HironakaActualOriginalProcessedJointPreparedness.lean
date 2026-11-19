import Hironaka.Resolution.HironakaActualProtectedOtherRowLocalStep

/-! Joint residual coordinates from ordinary original per-row processed laws.
BP FIRST: hironaka-actual-original-processed-joint-preparedness.tex.
The full remaining OLD+born list is essential; no history is reset or chosen.
General processed entry and the full K1 sharp driver remain separate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualOriginalProcessedJointPreparedness
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower NormalCrossings
  NormalCrossingsComparison NormalCrossingsInvariance SimultaneousNormalCrossings
  BlowupFlatCoordinates BlowupStrictSubmanifold HironakaG4PreparedCentreCoordinates
  HironakaG4RecordedTowerResidualCompatibility HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaActualProtectedOtherRowLocalStep
  HironakaSharpActualChronologicalStrictStep
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong
  NonmonomialTransformAlong GermIdealOrder MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem trace_family_coordinates {α : Type*} (hn : 0 < n)
    (N : Set X) (F : List (Set X)) (hF : IsSNCDivisor n F)
    (hTr : IsTransverse n N F) (A : α → Set X) (c : α → Fin F.length)
    (hA : ∀ a,A a=N ∩ F.get (c a)) {x : X} (hx : x ∈ N)
    (hc : Set.InjOn c {a | x ∈ A a}) :
    ∃ (S₀ : Finset (Fin n)) (p : α → Fin n),
      IsCoordinateFamilyAt n (fun o : Option α => o.elim N A)
        (fun o => o.elim S₀ (fun a => S₀ ∪ {p a})) x ∧
      (∀ a,x ∈ A a → p a ∉ S₀) ∧ Set.InjOn p {a | x ∈ A a} := by
  obtain ⟨_kC,kN,Φ,s,_hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl N) hF hTr hTr.hasNormalCrossings hx
  let Q : Finset (Fin n) := Finset.univ.filter fun q => kN ≤ q.val
  have hIncident (a : α) (ha : x ∈ A a) : x ∈ F.get (c a) := by
    rw [hA a] at ha
    exact ha.2
  refine ⟨Q,(fun a => s (c a)),?_,?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | a) ha y hy hyΦ
    · simpa only [Option.elim_none,Q,coordSubspace_eq_complexCoordinatePlane,complexChartAt]
        using (hflat hy hyΦ).2.1
    · change y ∈ A a ↔ _
      rw [hA a]
      have hH := (hflat hy hyΦ).2.2 (c a) (hIncident a ha)
      constructor
      · rintro ⟨hyN,hyH⟩ q hq
        rcases Finset.mem_union.mp hq with hQ | hOne
        · exact ((hflat hy hyΦ).2.1.mp hyN) q (Finset.mem_filter.mp hQ).2
        · have he : q=s (c a) := Finset.mem_singleton.mp hOne
          subst q
          exact hH.mp hyH
      · intro hz
        refine ⟨(hflat hy hyΦ).2.1.mpr ?_,hH.mpr ?_⟩
        · intro q hq
          exact hz q (Finset.mem_union.mpr (Or.inl (by simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and];exact hq)))
        · exact hz _ (Finset.mem_union.mpr (Or.inr (by simp)))
  · intro a ha hQ
    change s (c a) ∈ Q at hQ
    exact Nat.not_le_of_gt (hs (c a) (hIncident a ha)) (Finset.mem_filter.mp hQ).2
  · intro a ha b hb hab
    exact hc ha hb (hinj (hIncident a ha) (hIncident b hb) hab)

private def fullIndex (old born : List (Set X)) :
    Fin old.length ⊕ Fin born.length → Fin (old ++ born).length :=
  Sum.elim (fun a => ⟨a.val,by simp only [List.length_append];omega⟩)
    (fun b => ⟨old.length+b.val,by simp only [List.length_append];omega⟩)

private theorem fullIndex_injective (old born : List (Set X)) :
    Function.Injective (fullIndex old born) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext hv)
    | inr b => simp only [fullIndex,Sum.elim_inl,Sum.elim_inr] at hv;omega
  | inr a =>
    cases b with
    | inl b => simp only [fullIndex,Sum.elim_inl,Sum.elim_inr] at hv;omega
    | inr b =>
      simp only [fullIndex,Sum.elim_inr] at hv
      exact congrArg Sum.inr (Fin.ext (by omega))

private theorem fullIndex_get (old born : List (Set X))
    (a : Fin old.length ⊕ Fin born.length) :
    (old ++ born).get (fullIndex old born a)=Sum.elim old.get born.get a := by
  cases a with
  | inl a => simp [fullIndex,List.get_eq_getElem,List.getElem_append_left a.isLt]
  | inr b => simp [fullIndex,List.get_eq_getElem,
      List.getElem_append_right (by omega : old.length ≤ old.length+b.val)]

private theorem retained_mem (old born : List (Set X)) (i : Fin old.length)
    (a : Fin old.length ⊕ Fin born.length) (ha : a ≠ Sum.inl i) :
    Sum.elim old.get born.get a ∈ old.eraseIdx i.val ++ born := by
  cases a with
  | inl a =>
    apply List.mem_append_left
    apply List.mem_eraseIdx_iff_getElem.mpr
    refine ⟨a.val,a.isLt,?_,rfl⟩
    intro he
    exact ha (congrArg Sum.inl (Fin.ext he))
  | inr b => exact List.mem_append_right _ (List.get_mem born b)

private theorem replacement_coordinates (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (hFull : IsSNCDivisor n (old ++ born))
    (i : Fin old.length) (A : Fin old.length ⊕ Fin born.length → Set X)
    (U : Opens X) (H : Set U)
    (hAux : IsSNCDivisor n (H :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)))
    (hTr : IsTransverse n ((Subtype.val : U → X) ⁻¹' N)
      (H :: (old.eraseIdx i.val ++ born).map ((Subtype.val : U → X) ⁻¹' ·)))
    (hSelected : (Subtype.val : U → X) ⁻¹' A (Sum.inl i)=
      ((Subtype.val : U → X) ⁻¹' N) ∩ H)
    (hOther : ∀ a,a ≠ Sum.inl i → (Subtype.val : U → X) ⁻¹' A a=
      ((Subtype.val : U → X) ⁻¹' N) ∩
        ((Subtype.val : U → X) ⁻¹' Sum.elim old.get born.get a))
    {x : X} (hxN : x ∈ N) (hxU : x ∈ U) :
    ∃ (S₀ : Finset (Fin n)) (p : Fin old.length ⊕ Fin born.length → Fin n),
      IsCoordinateFamilyAt n (fun o : Option (Fin old.length ⊕ Fin born.length) => o.elim N A)
        (fun o => o.elim S₀ (fun a => S₀ ∪ {p a})) x ∧
      (∀ a,x ∈ A a → p a ∉ S₀) ∧ Set.InjOn p {a | x ∈ A a} := by
  let F := old.eraseIdx i.val ++ born
  let Aux := H :: F.map ((Subtype.val : U → X) ⁻¹' ·)
  let u : U := ⟨x,hxU⟩
  have hMem (a : Fin old.length ⊕ Fin born.length) (ha : a ≠ Sum.inl i) :
      ∃ q : Fin F.length,F.get q=Sum.elim old.get born.get a :=
    List.mem_iff_get.mp (retained_mem old born i a ha)
  let g : ∀ a : Fin old.length ⊕ Fin born.length,a ≠ Sum.inl i → Fin F.length :=
    fun a ha => Classical.choose (hMem a ha)
  have hg (a : Fin old.length ⊕ Fin born.length) (ha : a ≠ Sum.inl i) :
      F.get (g a ha)=Sum.elim old.get born.get a := Classical.choose_spec (hMem a ha)
  let z : Fin Aux.length := ⟨0,by simp only [Aux,List.length_cons];omega⟩
  let lift : Fin F.length → Fin Aux.length := fun q =>
    ⟨q.val+1,by simp only [Aux,List.length_cons,List.length_map];omega⟩
  have hLiftGet (q : Fin F.length) :
      Aux.get (lift q)=(Subtype.val : U → X) ⁻¹' F.get q := by
    simp [Aux,lift,List.get_eq_getElem]
  let c (a : Fin old.length ⊕ Fin born.length) : Fin Aux.length :=
    if ha : a=Sum.inl i then z else lift (g a ha)
  have hZero (a : Fin old.length ⊕ Fin born.length) : c a=z ↔ a=Sum.inl i := by
    by_cases ha : a=Sum.inl i
    · simp [c,ha]
    · simp only [c,dif_neg ha,ha,iff_false]
      intro he
      have hv := congrArg Fin.val he
      simp only [lift,z] at hv
      omega
  have hTrace (a : Fin old.length ⊕ Fin born.length) :
      (Subtype.val : U → X) ⁻¹' A a=
        ((Subtype.val : U → X) ⁻¹' N) ∩ Aux.get (c a) := by
    by_cases ha : a=Sum.inl i
    · subst a
      simpa only [c,dif_pos rfl,z,Aux,List.get_eq_getElem,List.getElem_cons_zero] using hSelected
    · rw [hOther a ha]
      congr 1
      rw [show c a=lift (g a ha) from dif_neg ha,hLiftGet,hg a ha]
  have hInjective : Set.InjOn c {a | u ∈ (Subtype.val : U → X) ⁻¹' A a} := by
    intro a ha b hb hab
    by_cases hai : a=Sum.inl i
    · have hbi : b=Sum.inl i := (hZero b).mp (hab.symm.trans ((hZero a).mpr hai))
      exact hai.trans hbi.symm
    · have hbi : b ≠ Sum.inl i := by
        intro he
        exact hai ((hZero a).mp (hab.trans ((hZero b).mpr he)))
      have he : lift (g a hai)=lift (g b hbi) := by
        simpa only [c,dif_neg hai,dif_neg hbi] using hab
      have hEqG : g a hai=g b hbi := by
        apply Fin.ext
        have hv := congrArg Fin.val he
        simp only [lift] at hv
        omega
      have hB : Sum.elim old.get born.get a=Sum.elim old.get born.get b :=
        (hg a hai).symm.trans ((congrArg F.get hEqG).trans (hg b hbi))
      have hIncA : x ∈ Sum.elim old.get born.get a := by
        have hh : u ∈ ((Subtype.val : U → X) ⁻¹' N) ∩
            ((Subtype.val : U → X) ⁻¹' Sum.elim old.get born.get a) := by
          rw [←hOther a hai]
          exact ha
        exact hh.2
      have hIncB : x ∈ Sum.elim old.get born.get b := by
        have hh : u ∈ ((Subtype.val : U → X) ⁻¹' N) ∩
            ((Subtype.val : U → X) ⁻¹' Sum.elim old.get born.get b) := by
          rw [←hOther b hbi]
          exact hb
        exact hh.2
      apply fullIndex_injective old born
      apply eq_of_eventually_mem_iff hFull
        (show x ∈ (old ++ born).get (fullIndex old born a) from by rw [fullIndex_get];exact hIncA)
        (show x ∈ (old ++ born).get (fullIndex old born b) from by rw [fullIndex_get];exact hIncB)
      exact Eventually.of_forall (fun _ => by rw [fullIndex_get,fullIndex_get,hB])
  obtain ⟨S₀,p,hFam,hFree,hInj⟩ := trace_family_coordinates (X := CMfd.of (n := n) U)
    hn ((Subtype.val : U → X) ⁻¹' N) Aux hAux hTr
    (fun a => (Subtype.val : U → X) ⁻¹' A a) c hTrace hxN hInjective
  refine ⟨S₀,p,?_,hFree,hInj⟩
  apply (isCoordinateFamilyAt_preimage_val_iff (x := u)).mp
  convert hFam using 1
  funext o
  cases o <;> rfl

private theorem no_old_support_coordinates (hn : 0 < n)
    (N : Set X) (old born : List (Set X)) (hBorn : IsSNCDivisor n born)
    (hTr : IsTransverse n N born) {x : X} (hx : x ∈ N)
    (hNone : ∀ i : Fin old.length,x ∉ preparedSupport N old born (Sum.inl i)) :
    IsPreparedResidualSNCAt N old born x := by
  obtain ⟨_kC,kN,Φ,s,_hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn (Subset.refl N) hBorn hTr hTr.hasNormalCrossings hx
  let Q : Finset (Fin n) := Finset.univ.filter fun q => kN ≤ q.val
  let p : Fin old.length ⊕ Fin born.length → Fin n := Sum.elim (fun _ => ⟨0,hn⟩) s
  refine ⟨Q,p,?_,?_,?_⟩
  · apply coordinateFamilyAt_of_flattening Φ ?_
      (mem_complexChartAt_source x) Φ.center_mem_source (fun _ hi => hi)
    rintro (_ | (i | b)) ha y hy hyΦ
    · simpa only [Option.elim_none,Q,coordSubspace_eq_complexCoordinatePlane,complexChartAt]
        using (hflat hy hyΦ).2.1
    · exact (hNone i ha).elim
    · change y ∈ N ∩ born.get b ↔
        Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (Q ∪ {s b})
      have hH := (hflat hy hyΦ).2.2 b ha.2
      constructor
      · rintro ⟨hyN,hyH⟩ q hq
        rcases Finset.mem_union.mp hq with hQ | hOne
        · exact ((hflat hy hyΦ).2.1.mp hyN) q (Finset.mem_filter.mp hQ).2
        · have he : q=s b := Finset.mem_singleton.mp hOne
          subst q
          exact hH.mp hyH
      · intro hz
        refine ⟨(hflat hy hyΦ).2.1.mpr ?_,hH.mpr ?_⟩
        · intro q hq
          exact hz q (Finset.mem_union.mpr (Or.inl (by simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and];exact hq)))
        · exact hz _ (Finset.mem_union.mpr (Or.inr (by simp)))
  · rintro (i | b) ha hQ
    · exact hNone i ha
    · change s b ∈ Q at hQ
      exact Nat.not_le_of_gt (hs b ha.2) (Finset.mem_filter.mp hQ).2
  · rintro (i | a) ha (j | b) hb hab
    · exact (hNone i ha).elim
    · exact (hNone i ha).elim
    · exact (hNone j hb).elim
    · exact congrArg Sum.inr (hinj ha.2 hb.2 hab)

private theorem actual_prepared_at_processed_row (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (i : Fin E.length) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNC : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H))
    {x : Y} (hx : x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) :
    let A := geoTransformAlong (geometricTemplate W []) T
    IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun h : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get h)) T).ideal
  let back : Fin old.length → Fin E.length := fun a =>
    ⟨a.val,by simpa only [old,List.length_map] using a.isLt⟩
  let iOld : Fin old.length := ⟨i.val,by simpa only [old,List.length_map] using i.isLt⟩
  have hBack : back iOld=i := Fin.ext rfl
  have hGet (a : Fin old.length) : old.get a=strictAlong T (E.get (back a)) := by
    simp [old,back,List.get_eq_getElem]
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hCurrent (a : Fin old.length) : oldResidualPart A.N old A.E a=J (back a) := by
    change nonmonomialPartAlong n A.N (restrictOn n A.N (vanishingIdeal (n := n) (old.get a))) A.E=_
    rw [hGet a]
    exact (hRecorded.2.2.2.2 (back a)).2.2.1
  obtain ⟨U,hxU,_hU,H,hAux,hTr,hSi,_hJi,hOthers⟩ :=
    protected_slice_window hn hW hE hdense i T hT hFull hOrd hNC hDenseS hx
      (⊤ : Opens Y) (by trivial)
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
  have hxN : x ∈ A.N := by rw [hNi] at hx;exact hx.1
  have hSelected : (Subtype.val : U → Y) ⁻¹' preparedSupport A.N old A.E (Sum.inl iOld)=
      ((Subtype.val : U → Y) ⁻¹' A.N) ∩ H := by
    change (Subtype.val : U → Y) ⁻¹' (A.N ∩ (oldResidualPart A.N old A.E iOld).zeroLocus)=_
    rw [hCurrent iOld,hBack]
    exact hSi
  have hOther (a : Fin old.length ⊕ Fin A.E.length) (ha : a ≠ Sum.inl iOld) :
      (Subtype.val : U → Y) ⁻¹' preparedSupport A.N old A.E a=
        ((Subtype.val : U → Y) ⁻¹' A.N) ∩
          ((Subtype.val : U → Y) ⁻¹' Sum.elim old.get A.E.get a) := by
    cases a with
    | inl a =>
      have hne : back a ≠ i := by
        intro he
        apply ha
        apply congrArg Sum.inl
        apply Fin.ext
        change a.val=i.val
        exact congrArg (fun q : Fin E.length => q.val) he
      change (Subtype.val : U → Y) ⁻¹' (A.N ∩ (oldResidualPart A.N old A.E a).zeroLocus)=_
      rw [hCurrent a]
      simp only [Sum.elim_inl]
      rw [hGet a]
      exact (hOthers (back a) hne).2
    | inr b => rfl
  exact replacement_coordinates hn hRecorded.2.1 iOld (preparedSupport A.N old A.E)
    U H hAux hTr hSelected hOther hxN hxU

/-- Joint actual residual SNC is DERIVED from ordinary per-original-row
processed geometry against the ENTIRE remaining OLD+born family. The SAME
history and every literal original/born/empty position remain unchanged. -/
theorem actual_original_processed_joint_preparedness (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1)
    (hNC : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDenseS : ∀ i : Fin E.length,
      let A := geoTransformAlong (geometricTemplate W []) T
      let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H)) :
    let A := geoTransformAlong (geometricTemplate W []) T
    ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N (E.map (strictAlong T)) A.E x := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let old := E.map (strictAlong T)
  let J := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  change ∀ x ∈ A.N,IsPreparedResidualSNCAt A.N old A.E x
  intro x hx
  by_cases hSome : ∃ i : Fin E.length,x ∈ (J i).zeroLocus
  · obtain ⟨i,hxi⟩ := hSome
    have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
    change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hNi
    have hOrdI : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
        ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1 := by
      rw [hNi]
      exact fun y hy => hOrd y hy i
    exact actual_prepared_at_processed_row hn hW hE hdense i T hT hFull hOrdI (hNC i) (hDenseS i)
      ⟨by rw [hNi];exact hx,hxi⟩
  · have hBorn : IsSNCDivisor n A.E := isSNCDivisor_of_sublist hRecorded.2.1
      (List.sublist_append_right old A.E)
    apply no_old_support_coordinates hn A.N old A.E hBorn hRecorded.2.2.1 hx
    intro a ha
    let i : Fin E.length := ⟨a.val,by simpa only [old,List.length_map] using a.isLt⟩
    have hGet : old.get a=strictAlong T (E.get i) := by
      simp [old,i,List.get_eq_getElem]
    have hCurrent : oldResidualPart A.N old A.E a=J i := by
      change nonmonomialPartAlong n A.N (restrictOn n A.N (vanishingIdeal (n := n) (old.get a))) A.E=_
      rw [hGet]
      exact (hRecorded.2.2.2.2 i).2.2.1
    change x ∈ A.N ∩ (oldResidualPart A.N old A.E a).zeroLocus at ha
    rw [hCurrent] at ha
    exact hSome ⟨i,ha.2⟩

end
end Hironaka.HironakaActualOriginalProcessedJointPreparedness
