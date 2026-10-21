import TranscendentalNakamaye.Pending.HironakaBoundaryCoefficientBranchHistories

/-!
# Genuine intrinsic carriers and counts from whole SNC boundary blocks

Actual SNC coordinates and a genuine finite avoidance restriction construct
an NC union adapted to the entire retained block. Its intrinsic count is the
actual number of through-old indices. No boundary-adapted union is assumed.
Blueprint: `hironaka-normal-crossings-snc-block-carrier-extension.tex`.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace TranscendentalNakamaye.Pending.HironakaNormalCrossingsSNCBlockCarrier
noncomputable section
open FirstPass FirstPass.BlowupSequences NormalCrossings BlowupFlatCoordinates
  HironakaNormalCrossingsLocalBranches HironakaNormalCrossingsMultiplicityStrata
  HironakaNormalCrossingsBoundaryTransform
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
private theorem union_block_coordinates (B E : List (Set M)) (h : IsSNCDivisor n (B++E)) (x : M) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (S : Finset (Fin n)) (D : Fin E.length→Finset (Fin n)),
      Φ.source⊆(chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      (∀ y∈flatDomain Φ,y∈(⋃ A∈B,A)↔∃ i∈S,flatCoord Φ i y=0) ∧
      (∀ i,x∈E.get i→(D i).card=1 ∧ Disjoint S (D i)) ∧
      Set.InjOn D {i|x∈E.get i} ∧
      (∀ i,x∈E.get i→∀ y∈flatDomain Φ,
        y∈E.get i↔Φ.toFun (chartAt (ComplexModel n) x y)∈coordSubspace (D i)) ∧
      S.card=(Finset.univ.filter (fun i : Fin B.length=>x∈B.get i)).card := by
  obtain ⟨C,⟨Φ,hsrc,h0,hEq⟩,hcard,hinj⟩ := h.2 x
  let old (i : Fin B.length) : Fin (B++E).length := ⟨i.val,by rw [List.length_append];omega⟩
  let born (i : Fin E.length) : Fin (B++E).length := ⟨B.length+i.val,by rw [List.length_append];omega⟩
  have hOld (i : Fin B.length) : (B++E).get (old i)=B.get i := by simp [old,List.get_eq_getElem]
  have hBorn (i : Fin E.length) : (B++E).get (born i)=E.get i := by simp [born,List.get_eq_getElem]
  let P := Finset.univ.filter (fun i : Fin B.length=>x∈B.get i)
  let S := P.biUnion (fun i=>C (old i))
  let D := fun i : Fin E.length=>C (born i)
  have hThroughOld (i : Fin B.length) (hi : i∈P) : x∈(B++E).get (old i) := by
    rw [hOld]
    exact (Finset.mem_filter.mp hi).2
  have hThroughBorn (i : Fin E.length) (hi : x∈E.get i) : x∈(B++E).get (born i) := by
    rwa [hBorn]
  have hDis (i j : Fin (B++E).length) (hi : x∈(B++E).get i)
      (hj : x∈(B++E).get j) (hne : i≠j) : Disjoint (C i) (C j) := by
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard i hi)
    obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (hcard j hj)
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hka : k=a := by simpa only [ha,Finset.mem_singleton] using hki
    have hkb : k=b := by simpa only [hb,Finset.mem_singleton] using hkj
    apply hne
    apply hinj hi hj
    rw [ha,hb,hka.symm.trans hkb]
  have hDisOld : (↑P : Set (Fin B.length)).PairwiseDisjoint (fun i=>C (old i)) := by
    intro i hi j hj hne
    exact hDis _ _ (hThroughOld i hi) (hThroughOld j hj)
      (fun he=>hne (Fin.ext (congrArg (fun z : Fin (B++E).length=>z.val) he)))
  have hScard : S.card=P.card := by
    rw [Finset.card_biUnion hDisOld]
    calc
      ∑ i∈P,(C (old i)).card=∑ _i∈P,1 := Finset.sum_congr rfl (fun i hi=>hcard _ (hThroughOld i hi))
      _=P.card := by simp
  let W : Set M := ⋂ i : Fin B.length,if x∈B.get i then univ else (B.get i)ᶜ
  have hWo : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact isOpen_univ
    · exact (h.1 _ (List.mem_append_left _ (List.get_mem _ _))).isOpen_compl
  have hxW : x∈W := by
    apply mem_iInter.mpr
    intro i
    split_ifs with hi
    · exact mem_univ _
    · exact hi
  let e := chartAt (ComplexModel n) x
  let V := e.target∩e.symm ⁻¹' W
  have hVo : IsOpen V := e.isOpen_inter_preimage_symm hWo
  have hxV : e x∈V := ⟨e.map_source (mem_chart_source _ x),by
    change e.symm (e x)∈W
    rwa [e.left_inv (mem_chart_source _ x)]⟩
  let Θ := Φ.restrict V hVo (e x) ⟨Φ.center_mem_source,hxV⟩
  have hflat (y : M) (hy : y∈flatDomain Θ) : y∈flatDomain Φ ∧ y∈W := by
    refine ⟨⟨hy.1,hy.2.1⟩,?_⟩
    have hh : e.symm (e y)∈W := hy.2.2.2
    rwa [e.left_inv hy.1] at hh
  refine ⟨Θ,S,D,(fun _ hz=>hsrc hz.1),h0,?_,?_,?_,?_,hScard⟩
  · intro y hy
    constructor
    · intro hyU
      obtain ⟨A,hyU₂⟩ := mem_iUnion.mp hyU
      obtain ⟨hAB,hyA⟩ := mem_iUnion.mp hyU₂
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hAB
      have hxi : x∈B.get i := by
        by_contra hxi
        have hh := mem_iInter.mp (hflat y hy).2 i
        rw [if_neg hxi] at hh
        exact hh hyA
      have hmem : Φ.toFun (e y)∈coordSubspace (C (old i)) :=
        (hEq (old i) (hThroughOld i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxi⟩))
          (hflat y hy).1.1 (hflat y hy).1.2).mp (by
            change y∈(B++E).get (old i)
            rw [hOld]
            exact hyA)
      obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard _ (by rwa [hOld]))
      refine ⟨a,Finset.mem_biUnion.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxi⟩,by simp [ha]⟩,?_⟩
      exact hmem a (by simp [ha])
    · rintro ⟨a,ha,hya⟩
      obtain ⟨i,hi,hai⟩ := Finset.mem_biUnion.mp ha
      change Φ.toFun (e y) a=0 at hya
      have hmem : Φ.toFun (e y)∈coordSubspace (C (old i)) := by
        obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (hcard _ (hThroughOld i hi))
        have hab : a=b := by simpa only [hb,Finset.mem_singleton] using hai
        intro k hk
        have hkb : k=b := by simpa only [hb,Finset.mem_singleton] using hk
        simpa only [hab,hkb] using hya
      have hyA : y∈B.get i := by
        rw [←hOld]
        exact (hEq (old i) (hThroughOld i hi) (hflat y hy).1.1 (hflat y hy).1.2).mpr hmem
      exact mem_iUnion.mpr ⟨B.get i,mem_iUnion.mpr ⟨List.get_mem _ _,hyA⟩⟩
  · intro i hi
    refine ⟨hcard _ (hThroughBorn i hi),Finset.disjoint_left.mpr ?_⟩
    intro k hkS hkD
    obtain ⟨j,hj,hkj⟩ := Finset.mem_biUnion.mp hkS
    have hneq : old j≠born i := by
      intro he
      have hv := congrArg Fin.val he
      change j.val=B.length+i.val at hv
      omega
    exact Finset.disjoint_left.mp (hDis _ _ (hThroughOld j hj) (hThroughBorn i hi) hneq) hkj hkD
  · intro i hi j hj he
    apply Fin.ext
    have hh := congrArg Fin.val (hinj (hThroughBorn i hi) (hThroughBorn j hj) he)
    change B.length+i.val=B.length+j.val at hh
    omega
  · intro i hi y hy
    change y∈E.get i↔Φ.toFun (e y)∈coordSubspace (C (born i))
    rw [←hBorn]
    exact hEq (born i) (hThroughBorn i hi) (hflat y hy).1.1 (hflat y hy).1.2

omit [IsComplexManifold n M] in
/-- The actual old union is an NC carrier adapted to the ENTIRE other block. -/
theorem boundaryAdapted_union_of_snc_append (B E : List (Set M)) (h : IsSNCDivisor n (B++E)) :
    IsBoundaryAdaptedCarrier (n := n) (⋃ A∈B,A) E := by
  refine ⟨?_,(fun A hA=>h.1 A (List.mem_append_right _ hA)),fun x=>?_⟩
  · exact (List.finite_toSet B).isClosed_biUnion (fun A hA=>h.1 A (List.mem_append_left _ hA))
  · obtain ⟨Φ,S,D,hsrc,h0,hU,hD,hinj,hEq,_hCard⟩ := union_block_coordinates B E h x
    exact ⟨Φ,S,D,hsrc,h0,hU,hD,hinj,hEq⟩

/-- The intrinsic count is the actual number of old members passing through x. -/
theorem branchMultiplicity_union_eq_count (B E : List (Set M)) (h : IsSNCDivisor n (B++E)) (x : M) :
    branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_snc_append B E h)) x=
      (Finset.univ.filter (fun i : Fin B.length=>x∈B.get i)).card ∧
    branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_snc_append B E h)) x≤B.length := by
  obtain ⟨Φ,S,_D,_hsrc,h0,hU,_hD,_hinj,_hEq,hCard⟩ := union_block_coordinates B E h x
  have he := (branchMultiplicity_eq_card
    (isNormalCrossingsCarrier_of_boundaryAdapted (boundaryAdapted_union_of_snc_append B E h)) Φ h0 S hU).trans hCard
  refine ⟨he,?_⟩
  rw [he]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_fin B.length)

private theorem strictAlong_list_union {X Y : BlowupTowers.CMfd.{u} n}
    (T : BlowupTowers.BlowupTower X Y) (B : List (Set X)) :
    HomogenizedGlueingTower.strictAlong T (⋃ A∈B,A)=
      ⋃ A∈B.map (HomogenizedGlueingTower.strictAlong T),A := by
  have hcons (A : Set X) (B : List (Set X)) : (⋃ C∈A::B,C)=A∪(⋃ C∈B,C) := by
    ext x
    simp
  have hconsY (A : Set Y) (B : List (Set Y)) : (⋃ C∈A::B,C)=A∪(⋃ C∈B,C) := by
    ext x
    simp
  induction B with
  | nil => simpa using StepOneEmptyPrefix.strictAlong_empty T
  | cons A B ih =>
      rw [hcons,MemberInterTowerAlong.strictAlong_union,ih,List.map_cons,hconsY]

open FirstPass.HolomorphicIdealSheaves MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit HomogenizedGlueingTower
  CoefficientIdeal CoefficientIdealRestriction GermIdealOrder
  HironakaBoundaryCoefficientBranchHistories MarkedIdealBiholomorphism

/-- A SAME original-only phase now produces genuine current local old carriers
and intrinsic counts relative to the ENTIRE current retained/born boundary. -/
theorem exists_original_phase_current_local_carriers {X : CMfd.{u} n}
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) (hd : 1≤d)
    (hK : IsCompact (cosupport n univ I d))
    {H : Set X} {E : List (Set X)} (h : IsBoundaryAdaptedCarrier (n := n) H E)
    {r : ℕ} (hr : 0<r)
    (hbound : ∀ x : X,branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x≤r) :
    let M : MarkedIdeal n X := ⟨univ,E,I,d⟩
    let Z := {x : X | r≤branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted h) x}
    let L := withN (coeffMarked M) Z
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),IsGeoResolution L T ∧
      IsGeoTestTower M T ∧ CentresIn Z T ∧
      (geoTransformAlong M T).cosupp∩strictAlong T Z=∅ ∧
      ∀ x∈Z,∃ (U : Opens X) (B : List (Set U)),x∈U ∧
        (Subtype.val : U→X) ⁻¹' H=(⋃ A∈B,A) ∧
        ∀ j : ℕ,
          let P := head (restrict U T) j
          let MU := MarkedIdeal.pullback (Subtype.val : U→X) M
          ∃ hc : IsBoundaryAdaptedCarrier (n := n)
            (strictAlong P ((Subtype.val : U→X) ⁻¹' H)) (geoTransformAlong MU P).E,
            ∀ y,
              branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y=
                (Finset.univ.filter (fun i : Fin (B.map (strictAlong P)).length=>
                  y∈(B.map (strictAlong P)).get i)).card ∧
              branchMultiplicity (isNormalCrossingsCarrier_of_boundaryAdapted hc) y≤B.length := by
  dsimp only
  obtain ⟨Y,T,hres,hTM,hTZ,hclear,hBranch⟩ :=
    exists_original_boundary_stratum_joint_histories I hI d hd hK h hr hbound
  refine ⟨Y,T,hres,hTM,hTZ,hclear,?_⟩
  intro x hx
  obtain ⟨U,B,hxU,_hBE,hunion,_hTB,hPrefix⟩ := hBranch x hx
  refine ⟨U,B,hxU,hunion,?_⟩
  intro j
  let P := head (restrict U T) j
  let MU := MarkedIdeal.pullback (Subtype.val : U→X) (⟨univ,E,I,d⟩ : MarkedIdeal n X)
  obtain ⟨hWF,hEntire⟩ := hPrefix j
  have hSNC : IsSNCDivisor n (B.map (strictAlong P)++(geoTransformAlong MU P).E) := by
    rw [←hEntire]
    exact hWF.isSNCDivisor
  have hUnion : strictAlong P ((Subtype.val : U→X) ⁻¹' H)=⋃ A∈B.map (strictAlong P),A := by
    rw [hunion]
    exact strictAlong_list_union P B
  rw [hUnion]
  refine ⟨boundaryAdapted_union_of_snc_append _ _ hSNC,?_⟩
  intro y
  obtain ⟨he,hle⟩ := branchMultiplicity_union_eq_count _ _ hSNC y
  exact ⟨he,by simpa only [List.length_map] using hle⟩

end
end TranscendentalNakamaye.Pending.HironakaNormalCrossingsSNCBlockCarrier
