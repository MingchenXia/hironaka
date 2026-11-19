import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.InvDomainTowerAlong

/-! Actual geometry of a BM08 exceptional boundary-intersection test.
The centre need not lie in the original carrier or cosupport. No controlled
transform, future test, HS cut or canonical-value comparison is assumed.
Blueprint FIRST: hironaka-actual-exceptional-carrier-geometry.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualExceptionalCarrierGeometry
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  NormalCrossings BoundaryCount SimultaneousNormalCrossings BlowupSNCTransform
  BlowupStrictSubmanifold BlowupMonomialCharts BlowupLocalSurjectivity BlowupFibreDirection
  MarkedIdeals ResolutionInvariantSpec RegularPointDimension BlowupTowers RegularAtDimTransport

variable {n : ℕ} {X Y : CMfd.{u} n}

private def linearCoordinates (L : ComplexModel n ≃L[ℂ] ComplexModel n) :
    LocalHolomorphicEquivAt (n := n) 0 where
  source := univ
  target := univ
  isOpen_source := isOpen_univ
  isOpen_target := isOpen_univ
  center_mem_source := mem_univ _
  toFun := L
  invFun := L.symm
  toFun_holomorphic := L.differentiable.differentiableOn
  invFun_holomorphic := L.symm.differentiable.differentiableOn
  mapsTo_toFun := fun _ _ => mem_univ _
  mapsTo_invFun := fun _ _ => mem_univ _
  left_inv := fun _ _ => L.symm_apply_apply _
  right_inv := fun _ _ => L.apply_symm_apply _

private def permutationMap (σ : Fin n ≃ Fin n) : ComplexModel n ≃L[ℂ] ComplexModel n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ σ).toContinuousLinearEquiv

private theorem permutation_apply (σ : Fin n ≃ Fin n) (w : ComplexModel n) (t : Fin n) :
    permutationMap σ w (σ t)=w t := by
  simp [permutationMap,LinearIsometryEquiv.piLpCongrLeft_apply,Equiv.piCongrLeft']

private theorem permutation_subspace (σ : Fin n ≃ Fin n) (A : Finset (Fin n))
    (w : ComplexModel n) :
    permutationMap σ w ∈ coordSubspace (A.map σ.toEmbedding) ↔ w ∈ coordSubspace A := by
  constructor
  · intro h t ht
    simpa only [permutation_apply] using h (σ t) (Finset.mem_map.mpr ⟨t,ht,rfl⟩)
  · intro h t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp ht
    change permutationMap σ w (σ s)=0
    rw [permutation_apply]
    exact h s hs

private theorem coordinate_regular {A : Set X} {x : X} (hx : x ∈ A)
    (S : Finset (Fin n))
    (hc : IsCoordinateFamilyAt n (fun _ : Unit => A) (fun _ => S) x) :
    RegularAtDim (n := n) A x (n-S.card) := by
  obtain ⟨Φ,hsrc,h0,hflat⟩ := hc
  obtain ⟨σ,hσ⟩ := exists_perm_nested (X := S) (Y := S) subset_rfl
  let Ψ := LocalHolomorphicEquivAt.comp Φ (linearCoordinates (permutationMap σ)) h0
  refine ⟨Nat.sub_le _ _,hx,Ψ,fun _ h => hsrc h.1,?_,?_⟩
  · change permutationMap σ (Φ.toFun _) = 0
    rw [h0,map_zero]
  · intro z hz hzΨ
    change z ∈ A ↔ permutationMap σ (Φ.toFun ((complexChartAt (n := n) x).val z)) ∈
      complexCoordinatePlane n (n-S.card)
    rw [hflat () hx hz hzΨ.1]
    constructor
    · intro h t ht
      obtain ⟨s,rfl⟩ := σ.surjective t
      rw [permutation_apply]
      exact h s ((hσ s).1.mp ht)
    · intro h t ht
      rw [←permutation_apply σ _ t]
      exact h (σ t) ((hσ t).1.mpr ht)

private theorem union_subspace (A B : Finset (Fin n)) (w : ComplexModel n) :
    w ∈ coordSubspace (A ∪ B) ↔ w ∈ coordSubspace A ∧ w ∈ coordSubspace B := by
  constructor
  · intro h
    exact ⟨fun t ht => h t (Finset.mem_union_left B ht),
      fun t ht => h t (Finset.mem_union_right A ht)⟩
  · rintro ⟨ha,hb⟩ t ht
    exact (Finset.mem_union.mp ht).elim (ha t) (hb t)

private theorem centre_regular {E : List (Set X)} (hE : IsSNCDivisor n E)
    (i j : Fin E.length) (hij : i ≠ j) {x : X} (hx : x ∈ E.get i ∩ E.get j) :
    2 ≤ n ∧ RegularAtDim (n := n) (E.get i ∩ E.get j) x (n-2) := by
  obtain ⟨S,⟨Φ,hsrc,h0,hflat⟩,hcard,hinj⟩ := hE.2 x
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard i hx.1)
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (hcard j hx.2)
  have hab : a ≠ b := by
    intro he
    exact hij (hinj hx.1 hx.2 (by rw [ha,hb,he]))
  have hR : (S i ∪ S j).card=2 := by rw [ha,hb]; simp [hab]
  have hn : 2 ≤ n := by
    have h := Finset.card_le_univ (s := S i ∪ S j)
    simpa only [hR,Fintype.card_fin] using h
  have hc : IsCoordinateFamilyAt n (fun _ : Unit => E.get i ∩ E.get j)
      (fun _ => S i ∪ S j) x := by
    refine ⟨Φ,hsrc,h0,fun _ _ z hz hzΦ => ?_⟩
    rw [union_subspace]
    exact and_congr (hflat i hx.1 hz hzΦ) (hflat j hx.2 hz hzΦ)
  exact ⟨hn,by simpa only [hR] using coordinate_regular hx _ hc⟩

/-- The actual ambient two-member centre is smooth/full NC; a nonempty
centre has genuine codimension two, including the low-dimensional cases. -/
theorem exceptional_centre_geometry (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (i j : Fin M.E.length) (hij : i ≠ j) :
    let C := M.E.get i ∩ M.E.get j
    IsClosedSubmanifold n C ∧ HasNormalCrossings n C M.E ∧
      (∀ x ∈ C,2 ≤ n ∧ RegularAtDim (n := n) C x (n-2)) ∧ (n<2 → C=∅) := by
  dsimp only
  have hE := hM.isWellFormed.isSNCDivisor
  have hr := fun x hx => centre_regular hE i j hij (x := x) hx
  have heq : M.E.get i ∩ M.E.get j=memberInter M.E {i,j} := by
    ext x
    simp [memberInter]
  refine ⟨⟨(hE.1 _ (List.get_mem _ _)).inter (hE.1 _ (List.get_mem _ _)),
    fun x hx => ⟨n-2,(hr x hx).2⟩⟩,?_,hr,?_⟩
  · rw [heq]
    exact hasNormalCrossings_memberInter hE {i,j}
  · intro hn
    exact eq_empty_iff_forall_notMem.mpr fun x hx => (Nat.not_le_of_gt hn) (hr x hx).1

private theorem joint_coordinates {N : Set X} {E : List (Set X)}
    (hT : IsTransverse n N E) (i j : Fin E.length) {x : X}
    (hxN : x ∈ N) (hxC : x ∈ E.get i ∩ E.get j) :
    ∃ (c : ℕ) (A : Finset (Fin n)) (S : Fin E.length → Finset (Fin n))
      (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      (∀ t ∈ A,t.val<c) ∧
      (∀ h,x ∈ E.get h → (S h).card=1 ∧ Disjoint (S h) A) ∧
      (∀ {z : X},z ∈ (chartAt (ComplexModel n) x).source →
        chartAt (ComplexModel n) x z ∈ Φ.source →
        (z ∈ E.get i ∩ E.get j ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n c) ∧
        (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ coordSubspace A) ∧
        ∀ h,x ∈ E.get h → (z ∈ E.get h ↔
          Φ.toFun (chartAt (ComplexModel n) x z) ∈ coordSubspace (S h))) := by
  obtain ⟨A,S,⟨Φ,hsrc,h0,hflat⟩,hcard⟩ := hT x hxN
  change Φ.toFun (chartAt (ComplexModel n) x x)=0 at h0
  let R := S i ∪ S j
  obtain ⟨σ,hσ⟩ := exists_perm_nested (X := R) (Y := R) subset_rfl
  let Ψ := LocalHolomorphicEquivAt.comp Φ (linearCoordinates (permutationMap σ)) h0
  have hRA : Disjoint R A := Finset.disjoint_union_left.mpr
    ⟨(hcard i hxC.1).2,(hcard j hxC.2).2⟩
  refine ⟨n-R.card,A.map σ.toEmbedding,fun h => (S h).map σ.toEmbedding,Ψ,
    fun _ h => hsrc h.1,?_,?_,?_,?_⟩
  · change permutationMap σ (Φ.toFun _) = 0
    rw [h0,map_zero]
  · intro t ht
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp ht
    apply Nat.lt_of_not_ge
    intro h
    exact Finset.disjoint_left.mp hRA ((hσ s).1.mp h) hs
  · intro h hh
    refine ⟨by simpa only [Finset.card_map] using (hcard h hh).1,Finset.disjoint_left.mpr ?_⟩
    intro t htS htA
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp htS
    obtain ⟨a,ha,he⟩ := Finset.mem_map.mp htA
    change σ a=σ s at he
    have has : a=s := σ.injective he
    exact Finset.disjoint_left.mp (hcard h hh).2 hs (has ▸ ha)
  · intro z hz hzΨ
    refine ⟨?_,?_,?_⟩
    · change z ∈ E.get i ∩ E.get j ↔ permutationMap σ (Φ.toFun
        (chartAt (ComplexModel n) x z)) ∈ complexCoordinatePlane n (n-R.card)
      have hc : z ∈ E.get i ∩ E.get j ↔
          Φ.toFun (chartAt (ComplexModel n) x z) ∈ coordSubspace R := by
        rw [union_subspace]
        exact and_congr (hflat (some i) hxC.1 hz hzΨ.1) (hflat (some j) hxC.2 hz hzΨ.1)
      rw [hc]
      constructor
      · intro hw t ht
        obtain ⟨s,rfl⟩ := σ.surjective t
        rw [permutation_apply]
        exact hw s ((hσ s).1.mp ht)
      · intro hw t ht
        rw [←permutation_apply σ _ t]
        exact hw (σ t) ((hσ t).1.mpr ht)
    · change z ∈ N ↔ permutationMap σ (Φ.toFun (chartAt (ComplexModel n) x z)) ∈
        coordSubspace (A.map σ.toEmbedding)
      rw [permutation_subspace]
      exact hflat none hxN hz hzΨ.1
    · intro h hh
      change z ∈ E.get h ↔ permutationMap σ (Φ.toFun (chartAt (ComplexModel n) x z)) ∈
        coordSubspace ((S h).map σ.toEmbedding)
      rw [permutation_subspace]
      exact hflat (some h) hh hz hzΨ.1

private theorem over_centre {N : Set X} {E : List (Set X)}
    (hEc : ∀ H ∈ E,IsClosed H) (hT : IsTransverse n N E) (i j : Fin E.length)
    {π : Y → X} (hπ : IsBlowupAlong n (E.get i ∩ E.get j) π) {y : Y}
    (hyN : π y ∈ N) (hyC : π y ∈ E.get i ∩ E.get j) :
    let C := E.get i ∩ E.get j
    let E' := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    ∃ (A : Finset (Fin n)) (S : Fin E'.length → Finset (Fin n)),
      y ∈ geoStrictTransform π C N ∧ RegularAtDim (n := n) N (π y) (n-A.card) ∧
      IsCoordinateFamilyAt n (fun o : Option (Fin E'.length) =>
        o.elim (geoStrictTransform π C N) (fun h => E'.get h)) (fun o => o.elim A S) y ∧
      ∀ h,y ∈ E'.get h → (S h).card=1 ∧ Disjoint (S h) A := by
  dsimp only
  let C := E.get i ∩ E.get j
  obtain ⟨c,A,S,Φ,hsrc,h0,hAlt,hcard,hflat⟩ := joint_coordinates hT i j hyN hyC
  have hc := fun {z} hz hzΦ => (hflat (z := z) hz hzΦ).1
  have hn := fun {z} hz hzΦ => (hflat (z := z) hz hzΦ).2.1
  have hh := fun h hh {z} hz hzΦ => (hflat (z := z) hz hzΦ).2.2 h hh
  obtain ⟨p,hp,O,hO,hyO,W,hWs,hWeq,hℓ,_⟩ :=
    exists_monomialLocalInverse hπ hsrc hc ⟨mem_chart_source _ (π y),Φ.center_mem_source⟩
  have hpA : p ∉ A := fun h => (Nat.not_lt_of_ge hp) (hAlt p h)
  have hWmem : ∀ u ∈ O,W u ∈ monomialDomain Φ c p := fun u hu => by
    show monomial c p (W u) ∈ Φ.target
    rw [(hWeq u hu).2]
    exact Φ.mapsTo_toFun (hWeq u hu).1.2
  have hpre : ∀ u ∈ O,π u ∈ N ↔ W u ∈ coordSubspace A := by
    intro u hu
    rw [hn (hWeq u hu).1.1 (hWeq u hu).1.2,←(hWeq u hu).2]
    have he : ∀ t ∈ A,monomial c p (W u) t=W u t := by
      intro t ht
      rw [monomial_apply,if_neg (fun h => (Nat.not_lt_of_ge h.1) (hAlt t ht))]
    exact ⟨fun h t ht => he t ht ▸ h t ht,fun h t ht => (he t ht).symm ▸ h t ht⟩
  have hNu : ∀ u ∈ O,u ∈ geoStrictTransform π C N ↔ W u ∈ coordSubspace A := by
    intro u hu
    exact (mem_geoStrictTransform_iff_of_chart hπ hsrc hc hn hp hO hWs hWeq hℓ hu).trans
      (and_iff_right hpA)
  have hWy := (hpre y hyO).mp hyN
  have hyStrict := (hNu y hyO).mpr hWy
  have hHu : ∀ h,π y ∈ E.get h → ∀ u ∈ O,
      u ∈ geoStrictTransform π C (E.get h) ↔ p ∉ S h ∧ W u ∈ coordSubspace (S h) :=
    fun h hhx u hu => mem_geoStrictTransform_iff_of_chart hπ hsrc hc (hh h hhx)
      hp hO hWs hWeq hℓ hu
  have hCu : ∀ u ∈ O,π u ∈ C ↔ W u p=0 := fun u hu => by
    rw [hc (hWeq u hu).1.1 (hWeq u hu).1.2,←(hWeq u hu).2,monomial_mem_plane_iff hp]
  obtain ⟨ℓ,⟨hℓs,hℓπ⟩,_⟩ := existsUnique_monomialLift hπ hsrc hc hp
  have hFinj := injective_fderiv_of_monomialInverse hO hWs hWmem hℓs (hℓ ℓ hℓs hℓπ) hyO
  obtain ⟨Θ,hΘsrc,hΘ0,hΘ⟩ := exists_recentred_coords hO hWs hyO hFinj
  let B := E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  let S' : Fin B.length → Finset (Fin n) :=
    fun h => if ht : h.val<E.length then S ⟨h.val,ht⟩ else {p}
  have hthrough : ∀ h,y ∈ geoStrictTransform π C (E.get h) → π y ∈ E.get h :=
    fun h hyh => geoStrictTransform_subset_preimage hπ.contMDiff.continuous (hEc _ (List.get_mem _ _)) hyh
  refine ⟨A,S',hyStrict,?_,⟨Θ,hΘsrc,hΘ0,?_⟩,?_⟩
  · exact coordinate_regular hyN A ⟨Φ,hsrc,h0,fun _ _ {z} hz hzΦ => hn hz hzΦ⟩
  · rintro (_|h) hyh u hu huΘ
    · obtain ⟨huO,hΘu⟩ := hΘ hu huΘ
      change u ∈ geoStrictTransform π C N ↔ Θ.toFun _ ∈ coordSubspace A
      rw [hΘu,hNu u huO,sub_mem_coordSubspace_iff hWy]
    · obtain ⟨huO,hΘu⟩ := hΘ hu huΘ
      change u ∈ B.get h ↔ Θ.toFun _ ∈ coordSubspace (S' h)
      rw [hΘu]
      change y ∈ B.get h at hyh
      rw [get_map_append_singleton] at hyh ⊢
      by_cases ht : h.val<E.length
      · simp only [ht,dif_pos,S'] at hyh ⊢
        obtain ⟨hpS,hWyS⟩ := (hHu _ (hthrough _ hyh) y hyO).mp hyh
        rw [hHu _ (hthrough _ hyh) u huO,sub_mem_coordSubspace_iff hWyS]
        exact and_iff_right hpS
      · simp only [S',dif_neg ht] at hyh ⊢
        change π u ∈ C ↔ W u-W y ∈ coordSubspace {p}
        rw [hCu u huO,mem_coordSubspace_singleton,PiLp.sub_apply,(hCu y hyO).mp hyC,sub_zero]
  · intro h hyh
    change y ∈ B.get h at hyh
    rw [get_map_append_singleton] at hyh
    by_cases ht : h.val<E.length
    · simp only [ht,dif_pos] at hyh
      simpa only [S',ht,dif_pos] using hcard _ (hthrough _ hyh)
    · simp only [S',ht]
      exact ⟨Finset.card_singleton _,Finset.disjoint_singleton_left.mpr hpA⟩

private theorem transverse_off {N : Set X} {E : List (Set X)} (hNc : IsClosed N)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n N E) {C : Set X}
    {π : Y → X} (hπ : IsBlowupAlong n C π) {y : Y}
    (hyN : y ∈ geoStrictTransform π C N) (hyC : π y ∉ C) :
    ∃ (A : Finset (Fin n)) (S : Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length → Finset (Fin n)),
      IsCoordinateFamilyAt n (fun o : Option (Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length) => o.elim (geoStrictTransform π C N)
        (fun h => (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get h)) (fun o => o.elim A S) y ∧
      ∀ h,y ∈ (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get h →
        (S h).card=1 ∧ Disjoint (S h) A := by
  have hyπN := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hNc hyN
  obtain ⟨S₀,S,⟨Φ,hsrc,h0,hflat⟩,hcard⟩ := hT (π y) hyπN
  let A : Option (Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length) → Set X :=
    fun o => o.elim N fun h => if ht : h.val<E.length then E.get ⟨h.val,ht⟩ else C
  let S' : Option (Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length) → Finset (Fin n) :=
    fun o => o.elim S₀ fun h => if ht : h.val<E.length then S ⟨h.val,ht⟩ else ∅
  have ha : IsCoordinateFamilyAt n A S' (π y) := by
    refine ⟨Φ,hsrc,h0,?_⟩
    rintro (_|h) hh z hz hzΦ
    · exact hflat none hh hz hzΦ
    · by_cases ht : h.val<E.length
      · simp only [A,S',Option.elim,ht,dif_pos] at hh ⊢
        exact hflat (some ⟨h.val,ht⟩) hh hz hzΦ
      · simp only [A,Option.elim,ht] at hh
        exact (hyC hh).elim
  have hO : IsOpen (π ⁻¹' Cᶜ) := hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous
  have hAO : ∀ o : Option (Fin (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).length),
      ∀ u ∈ π ⁻¹' Cᶜ,u ∈ (o.elim (geoStrictTransform π C N)
      (fun h => (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).get h)) ↔ π u ∈ A o := by
    rintro (_|h) u hu
    · exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hNc hu
    · simp only [Option.elim]
      rw [get_map_append_singleton]
      by_cases ht : h.val<E.length
      · simp only [A,Option.elim,ht,dif_pos]
        exact mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous
          (hE.1 _ (List.get_mem _ _)) hu
      · simp only [A,Option.elim,ht]
        exact Iff.rfl
  have hyExc : y ∉ exceptionalLocus n π := fun h =>
    hyC (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ h)
  refine ⟨S₀,fun h => S' (some h),
    isCoordinateFamilyAt_of_preimage hπ.contMDiff hyExc hO hyC hAO ha,?_⟩
  intro h hyh
  have hh := (hAO (some h) y hyC).mp hyh
  by_cases ht : h.val<E.length
  · simp only [A,Option.elim,ht,dif_pos] at hh
    simpa only [S',Option.elim,ht,dif_pos] using hcard _ hh
  · simp only [A,Option.elim,ht] at hh
    exact (hyC hh).elim

/-- The genuine exceptional boundary blowup retains the original carrier
dimension and full transverse boundary, without requiring centre inclusion. -/
theorem exceptional_carrier_geometry (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (i j : Fin M.E.length) (hij : i ≠ j) {π : Y → X}
    (hπ : IsBlowupAlong n (M.E.get i ∩ M.E.get j) π) :
    let C := M.E.get i ∩ M.E.get j
    let N' := geoStrictTransform π C M.N
    let E' := M.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
    N'=π ⁻¹' M.N ∧ IsClosedSubmanifold n N' ∧ DimLE n N' k ∧
      IsSNCDivisor n E' ∧ IsTransverse n N' E' ∧
      (∀ y ∈ N',∀ d,RegularAtDim (n := n) M.N (π y) d → RegularAtDim (n := n) N' y d) ∧
      E'.length=M.E.length+1 ∧
      (∀ h : Fin M.E.length,E'.get ⟨h.val,by
        dsimp [E'];simp only [List.length_append,List.length_map,List.length_singleton];omega⟩=
          geoStrictTransform π C (M.E.get h)) ∧
      E'.getLast (by dsimp [E'];simp)=π ⁻¹' C := by
  dsimp only
  let C := M.E.get i ∩ M.E.get j
  let N' := geoStrictTransform π C M.N
  let E' := M.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]
  have hN := hM.isWellFormed.isClosedSubmanifold_N
  have hE := hM.isWellFormed.isSNCDivisor
  have hT := hM.isWellFormed.isTransverse
  have hC := exceptional_centre_geometry M hM i j hij
  have heq : N'=π ⁻¹' M.N := by
    apply Subset.antisymm (geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1)
    intro y hy
    by_cases hyC : π y ∈ C
    · obtain ⟨A,S,hyN',_hr,_hc,_hcard⟩ := over_centre hE.1 hT i j hπ hy hyC
      exact hyN'
    · exact subset_closure ⟨hy,hyC⟩
  have hreg : ∀ y ∈ N',∀ d,RegularAtDim (n := n) M.N (π y) d →
      RegularAtDim (n := n) N' y d := by
    intro y hy d hd
    by_cases hyC : π y ∈ C
    · have hyN : π y ∈ M.N := heq.subset hy
      obtain ⟨A,S,_hyN',hr,⟨Φ,hsrc,h0,hflat⟩,_hcard⟩ := over_centre hE.1 hT i j hπ hyN hyC
      have hr' := coordinate_regular hy A ⟨Φ,hsrc,h0,fun _ _ {z} hz hzΦ => hflat none hy hz hzΦ⟩
      exact (eq_of_regularAtDim hr hd) ▸ hr'
    · exact regularAtDim_geoStrictTransform_of_notMem hπ hN.1 hyC hd
  have hTr : IsTransverse n N' E' := by
    intro y hy
    by_cases hyC : π y ∈ C
    · have hyN : π y ∈ M.N := heq.subset hy
      obtain ⟨A,S,_hyN',_hr,hcoord,hcard⟩ := over_centre hE.1 hT i j hπ hyN hyC
      exact ⟨A,S,hcoord,hcard⟩
    · exact transverse_off hN.1 hE hT hπ hy hyC
  refine ⟨heq,⟨isClosed_closure,?_⟩,?_,
    isSNCDivisor_geoTransformE_of_hasNormalCrossings hπ hE hC.2.1,hTr,hreg,by simp,?_,by simp⟩
  · intro y hy
    have hyN : π y ∈ M.N := heq.subset hy
    obtain ⟨d,_hdk,hd⟩ := hM.dimLE (π y) hyN
    exact ⟨d,hreg y hy d hd⟩
  · intro y hy
    have hyN : π y ∈ M.N := heq.subset hy
    obtain ⟨d,hdk,hd⟩ := hM.dimLE (π y) hyN
    exact ⟨d,hdk,hreg y hy d hd⟩
  · intro h
    rw [get_map_append_singleton]
    exact dif_pos h.isLt

end
end Hironaka.HironakaActualExceptionalCarrierGeometry
