import Hironaka.Resolution.HironakaG8CaseTCoordinateReplacement
import Hironaka.Resolution.HironakaG8P1ArcOrderTwo
import Hironaka.Resolution.HironakaIntrinsicCarrierBoundaryCharts
import Hironaka.Resolution.HironakaSharpNormalCrossingsOpenLocus

set_option autoImplicit false

/-!
# The actual Case T hypersurface frame

For a hypersurface carrier P inside an ambient regular carrier N, a tangent
original boundary member selects an actual nonzero pivot of a local defining
equation of P. Replacing that coordinate preserves every other active original
boundary equation. The resulting finite coordinate family gives a genuine
open neighborhood on which the remaining boundary is transverse to P.

The ambient-carrier configuration is explicit. It is not inferred for the
old universal hO signature with arbitrary carriers.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8CaseTHypersurfaceFrame

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates BlowupSpaceTangent NormalCrossings
  NormalCrossingsInvariance NestedFlattening RegularAtDimTransport
  HironakaIntrinsicCarrierBoundaryCharts HironakaSharpNormalCrossingsOpenLocus
  HironakaG8P1ArcOrderTwo HironakaG8CaseTCoordinateReplacement

noncomputable section

variable {n : ℕ} {X : CMfd.{u} n}

private theorem tangent_of_nested_coordinate_eq_zero
    {P N : Set X} {x : X} {m : ℕ}
    (Ω : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Ω.source ⊆ (chartAt (ComplexModel n) x).target)
    (hPflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Ω.source →
        (y ∈ P ↔ Ω.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n m))
    (hNflat : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Ω.source →
        (y ∈ N ↔ Ω.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n (m+1)))
    (hxP : x ∈ P) (hxN : x ∈ N) (hm : m < n)
    {ξ : ComplexModel n} (hξN : ξ ∈ tangentSpace n N x)
    (hξf : germDiff n (flatCoord Ω ⟨m, hm⟩) x ξ = 0) :
    ξ ∈ tangentSpace n P x := by
  apply (mem_tangentSpace_iff hsrc hPflat (mem_flatDomain_self Ω) hxP).mpr
  intro i hi
  by_cases him : i.val = m
  · have hieq : i = ⟨m, hm⟩ := Fin.ext him
    rw [hieq]
    exact hξf
  · exact (mem_tangentSpace_iff hsrc hNflat (mem_flatDomain_self Ω) hxN).mp hξN i (by omega)

private theorem exists_local_hypersurface_equation_at_pivot
    {P N H : Set X} {x : X} {m : ℕ}
    (hP : RegularAtDim (n := n) P x m) (hN : RegularAtDim (n := n) N x (m+1))
    (hPN : P ⊆ N)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hzero : Φ.toFun (chartAt (ComplexModel n) x x) = 0)
    (hNflat : ∀ y ∈ flatDomain Φ,
      y ∈ N ↔ GiraudAlong.flatMap Φ y ∈ complexCoordinatePlane n (m+1))
    (j : Fin n) (hj : j.val < m+1)
    (hHflat : ∀ y ∈ flatDomain Φ, y ∈ H ↔ flatCoord Φ j y = 0)
    (hTang : x ∈ GermIdealOrder.cosupport n P (vanishingIdeal (n := n) H) 2) :
    ∃ F : ComplexModel n → ℂ, F 0 = 0 ∧
      fderiv ℂ F 0 (EuclideanSpace.single j 1) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0 : ComplexModel n), DifferentiableAt ℂ F z ∧
        (GiraudAlong.flatInv Φ z ∈ P ↔
          z ∈ complexCoordinatePlane n (m+1) ∧ F z = 0) := by
  have hm : m < n := by have hmn := hN.1; omega
  obtain ⟨Ω, hΩsrc, hΩzero, hΩflat⟩ :=
    exists_nested_flattening (Nat.le_succ m) hP hN hPN
  dsimp only [complexChartAt] at Ω hΩsrc hΩzero hΩflat
  let l : Fin n := ⟨m, hm⟩
  let fP : X → ℂ := flatCoord Ω l
  let F : ComplexModel n → ℂ := fP ∘ GiraudAlong.flatInv Φ
  have hfP : HolomorphicAt n fP x := holomorphicAt_flatCoord Ω l (mem_flatDomain_self Ω)
  have hcoordH : (vanishingIdeal (n := n) H).mem x (flatCoord Φ j) := by
    refine ⟨holomorphicAt_flatCoord Φ j (mem_flatDomain_self Φ), ?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy hyH
    exact (hHflat y hy).mp hyH
  let v : ComplexModel n := flatVec Φ x (EuclideanSpace.single j 1)
  have hvN : v ∈ tangentSpace n N x := by
    apply (mem_tangentSpace_iff hsrc (fun hy hyΦ => hNflat _ ⟨hy, hyΦ⟩)
      (mem_flatDomain_self Φ) hN.2.1).mpr
    intro i hi
    rw [germDiff_flatCoord_flatVec hsrc (mem_flatDomain_self Φ)]
    have hij : i ≠ j := by intro he; subst i; omega
    simp [hij]
  have hdfP : germDiff n fP x v ≠ 0 := by
    intro hvf
    have hvP := tangent_of_nested_coordinate_eq_zero Ω hΩsrc
      (fun hy hyΩ => (hΩflat hy hyΩ).1) (fun hy hyΩ => (hΩflat hy hyΩ).2)
      hP.2.1 hN.2.1 hm hvN hvf
    have hHkill := germDiff_eq_zero_of_order_two hcoordH.1 (hTang.2 _ hcoordH) hvP
    have hHone : germDiff n (flatCoord Φ j) x v = 1 := by
      rw [germDiff_flatCoord_flatVec hsrc (mem_flatDomain_self Φ)]
      simp
    exact one_ne_zero (hHone.symm.trans hHkill)
  have hFpartial : fderiv ℂ F 0 (EuclideanSpace.single j 1) ≠ 0 := by
    have hchain := germDiff_flatVec hsrc (mem_flatDomain_self Φ) hfP (EuclideanSpace.single j 1)
    rw [hzero] at hchain
    intro hFzero
    exact hdfP (hchain.trans hFzero)
  have hFzero : F 0 = 0 := by
    change flatCoord Ω l (GiraudAlong.flatInv Φ 0) = 0
    rw [GiraudAlong.flatInv_zero hzero]
    change Ω.toFun (chartAt (ComplexModel n) x x) l = 0
    rw [hΩzero]
    rfl
  have hInv : Tendsto (GiraudAlong.flatInv Φ) (𝓝 0) (𝓝 x) := by
    simpa only [GiraudAlong.flatInv_zero hzero] using
      (GiraudAlong.continuousAt_flatInv (GiraudAlong.zero_mem_target hzero) hsrc).tendsto
  refine ⟨F, hFzero, hFpartial, ?_⟩
  filter_upwards [Φ.isOpen_target.mem_nhds (GiraudAlong.zero_mem_target hzero),
    hInv ((isOpen_flatDomain Ω).mem_nhds (mem_flatDomain_self Ω))] with z hzT hzΩ
  have hzΦ := GiraudAlong.flatInv_mem_flatDomain hzT hsrc
  have hmap := GiraudAlong.flatMap_flatInv hzT hsrc
  refine ⟨GiraudAlong.differentiableAt_comp_flatInv hzT hsrc
    (holomorphicAt_flatCoord Ω l hzΩ), ?_⟩
  constructor
  · intro hzP
    refine ⟨?_, ?_⟩
    · rw [← hmap]
      exact (hNflat _ hzΦ).mp (hPN hzP)
    · exact (hΩflat hzΩ.1 hzΩ.2).1.mp hzP l le_rfl
  · rintro ⟨hzN, hzF⟩
    apply (hΩflat hzΩ.1 hzΩ.2).1.mpr
    intro i hi
    by_cases him : i.val = m
    · have hil : i = l := Fin.ext him
      rw [hil]
      exact hzF
    · have hzN' : GiraudAlong.flatInv Φ z ∈ N :=
        (hNflat _ hzΦ).mpr (hmap.symm ▸ hzN)
      exact (hΩflat hzΩ.1 hzΩ.2).2.mp hzN' i (by omega)

/-- An actual regular hypersurface of a regular ambient carrier, tangent
to one original SNC member, has a constructed chart preserving every
other active original boundary coordinate. The pivot is derived from the
given tangency and the actual nested carrier geometry. -/
theorem exists_hypersurface_frame
    {P N : Set X} {x : X} {m : ℕ}
    (hP : RegularAtDim (n := n) P x m) (hN : RegularAtDim (n := n) N x (m+1))
    (hPN : P ⊆ N) (E : List (Set X))
    (hE : IsSNCDivisor n E) (hTrans : IsTransverse n N E)
    (i₀ : Fin E.length) (hxi₀ : x ∈ E.get i₀)
    (hTang : x ∈ GermIdealOrder.cosupport n P (vanishingIdeal (n := n) (E.get i₀)) 2) :
    ∃ (j₀ : Fin n)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (s : Fin E.length → Fin n),
      j₀ = s i₀ ∧ j₀.val < m+1 ∧
      Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i, x ∈ E.get i → (s i).val < m+1) ∧
      Set.InjOn s {i | x ∈ E.get i} ∧
      (∀ i, x ∈ E.get i → i ≠ i₀ → s i ≠ j₀) ∧
      ∀ y ∈ flatDomain Θ,
        (y ∈ N ↔ GiraudAlong.flatMap Θ y ∈ complexCoordinatePlane n (m+1)) ∧
        (y ∈ P ↔ GiraudAlong.flatMap Θ y ∈ complexCoordinatePlane n (m+1) ∧
          flatCoord Θ j₀ y = 0) ∧
        ∀ i, i ≠ i₀ →
          (y ∈ E.get i ↔ x ∈ E.get i ∧ flatCoord Θ (s i) y = 0) := by
  have hn : 0 < n := (Nat.succ_pos m).trans_le hN.1
  obtain ⟨a, ha, Φ, s, hsrc, hzero, hs, hinj, hflat⟩ :=
    exists_centered_full_boundary_chart hn hE hTrans x (hPN hP.2.1)
  have hNa : RegularAtDim (n := n) N x a :=
    ⟨ha, hN.2.1, Φ, hsrc, hzero, fun hy hyΦ => (hflat _ ⟨hy, hyΦ⟩).1⟩
  have haEq : a = m+1 := RegularPointDimension.eq_of_regularAtDim hNa hN
  subst a
  let j₀ := s i₀
  have hj₀ : j₀.val < m+1 := hs i₀ hxi₀
  have hHflat : ∀ y ∈ flatDomain Φ, y ∈ E.get i₀ ↔ flatCoord Φ j₀ y = 0 := by
    intro y hy
    simpa only [hxi₀, true_and] using (hflat y hy).2 i₀
  obtain ⟨F, hFzero, hFpartial, hFnear⟩ :=
    exists_local_hypersurface_equation_at_pivot hP hN hPN Φ hsrc hzero
      (fun y hy => (hflat y hy).1) j₀ hj₀ hHflat hTang
  have hnear : ∀ᶠ z in 𝓝 (0 : ComplexModel n), z ∈ Φ.target ∧
      DifferentiableAt ℂ F z ∧
      (GiraudAlong.flatInv Φ z ∈ P ↔ z ∈ complexCoordinatePlane n (m+1) ∧ F z = 0) := by
    filter_upwards [Φ.isOpen_target.mem_nhds (GiraudAlong.zero_mem_target hzero), hFnear]
      with z hzT hz
    exact ⟨hzT, hz⟩
  obtain ⟨V, hVsub, hVopen, h0V⟩ := mem_nhds_iff.mp hnear
  obtain ⟨Ψ, hΨV, hΨzero, hΨpivot, hΨoff⟩ :=
    exists_coordinate_replacement_at hVopen h0V
      (fun z hz => (hVsub hz).2.1.differentiableWithinAt) hFzero j₀ hFpartial
  let Θ := LocalHolomorphicEquivAt.comp Φ Ψ hzero
  have hPlane : ∀ z : ComplexModel n,
      z ∈ complexCoordinatePlane n (m+1) ↔ Ψ.toFun z ∈ complexCoordinatePlane n (m+1) := by
    intro z
    constructor
    · intro hz i hi
      have hij : i ≠ j₀ := by intro he; subst i; omega
      rw [hΨoff z i hij]
      exact hz i hi
    · intro hz i hi
      have hij : i ≠ j₀ := by intro he; subst i; omega
      have hzi := hz i hi
      rw [hΨoff z i hij] at hzi
      exact hzi
  have hOther : ∀ i, x ∈ E.get i → i ≠ i₀ → s i ≠ j₀ := by
    intro i hi hi₀ he
    exact hi₀ (hinj hi hxi₀ he)
  refine ⟨j₀, Θ, s, rfl, hj₀, fun z hz => hsrc hz.1, ?_, hs, hinj, hOther, ?_⟩
  · change Ψ.toFun (Φ.toFun (chartAt (ComplexModel n) x x)) = 0
    rw [hzero, hΨzero]
  · intro y hy
    change y ∈ (chartAt (ComplexModel n) x).source ∧
      chartAt (ComplexModel n) x y ∈ Φ.source ∩ Φ.toFun ⁻¹' Ψ.source at hy
    have hyΦ : y ∈ flatDomain Φ := ⟨hy.1, hy.2.1⟩
    have hyV := hVsub (hΨV hy.2.2)
    have hInvy : GiraudAlong.flatInv Φ (Φ.toFun (chartAt (ComplexModel n) x y)) = y :=
      GiraudAlong.flatInv_flatMap hyΦ
    refine ⟨?_, ?_, ?_⟩
    · change y ∈ N ↔ Ψ.toFun (Φ.toFun (chartAt (ComplexModel n) x y)) ∈
        complexCoordinatePlane n (m+1)
      exact (hflat y hyΦ).1.trans (hPlane _)
    · change y ∈ P ↔ Ψ.toFun (Φ.toFun (chartAt (ComplexModel n) x y)) ∈
        complexCoordinatePlane n (m+1) ∧ Ψ.toFun (Φ.toFun (chartAt (ComplexModel n) x y)) j₀ = 0
      rw [← hPlane, hΨpivot]
      simpa only [hInvy] using hyV.2.2
    · intro i hi₀
      change y ∈ E.get i ↔ x ∈ E.get i ∧
        Ψ.toFun (Φ.toFun (chartAt (ComplexModel n) x y)) (s i) = 0
      by_cases hxi : x ∈ E.get i
      · rw [hΨoff _ _ (hOther i hxi hi₀)]
        exact (hflat y hyΦ).2 i
      · simpa only [hxi, false_and] using (hflat y hyΦ).2 i

/-- The same constructed hypersurface frame gives a genuine original open
on which the literal boundary list obtained by erasing the selected member
is SNC and transverse to P. All original coordinate and activity data are
retained with the very same frame and open. -/
theorem exists_hypersurface_transverse_open
    {P N : Set X} {x : X} {m : ℕ}
    (hP : RegularAtDim (n := n) P x m) (hN : RegularAtDim (n := n) N x (m+1))
    (hPN : P ⊆ N) (E : List (Set X))
    (hE : IsSNCDivisor n E) (hTrans : IsTransverse n N E)
    (i₀ : Fin E.length) (hxi₀ : x ∈ E.get i₀)
    (hTang : x ∈ GermIdealOrder.cosupport n P (vanishingIdeal (n := n) (E.get i₀)) 2) :
    ∃ (j₀ : Fin n)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (s : Fin E.length → Fin n) (U : Opens X),
      j₀ = s i₀ ∧ j₀.val < m+1 ∧
      Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      (∀ i, x ∈ E.get i → (s i).val < m+1) ∧
      Set.InjOn s {i | x ∈ E.get i} ∧
      (∀ i, x ∈ E.get i → i ≠ i₀ → s i ≠ j₀) ∧
      x ∈ U ∧ (U : Set X) = flatDomain Θ ∧
      (∀ y ∈ flatDomain Θ,
        (y ∈ N ↔ GiraudAlong.flatMap Θ y ∈ complexCoordinatePlane n (m+1)) ∧
        (y ∈ P ↔ GiraudAlong.flatMap Θ y ∈ complexCoordinatePlane n (m+1) ∧
          flatCoord Θ j₀ y = 0) ∧
        ∀ i, i ≠ i₀ →
          (y ∈ E.get i ↔ x ∈ E.get i ∧ flatCoord Θ (s i) y = 0)) ∧
      IsSNCDivisor n ((E.eraseIdx i₀.val).map ((Subtype.val : U → X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → X) ⁻¹' P)
        ((E.eraseIdx i₀.val).map ((Subtype.val : U → X) ⁻¹' ·)) := by
  classical
  obtain ⟨j₀, Θ, s, hjEq, hj₀, hsrc, hzero, hs, hinj, hOther, hAll⟩ :=
    exists_hypersurface_frame hP hN hPN E hE hTrans i₀ hxi₀ hTang
  let G := E.eraseIdx i₀.val
  let U : Opens X := ⟨flatDomain Θ, isOpen_flatDomain Θ⟩
  have hidx : ∀ a : Fin G.length, ∃ i : Fin E.length, i ≠ i₀ ∧ E.get i = G.get a := by
    intro a
    have ha : G.get a ∈ E.eraseIdx i₀.val := List.get_mem G a
    obtain ⟨i, hi, hne, hget⟩ := List.mem_eraseIdx_iff_getElem.mp ha
    refine ⟨⟨i, hi⟩, ?_, hget⟩
    intro he
    exact hne (congrArg Fin.val he)
  choose idx hidxne hidxget using hidx
  let Q : Finset (Fin n) :=
    (Finset.univ.filter fun j : Fin n => m+1 ≤ j.val) ∪ {j₀}
  let A : Option (Fin G.length) → Set X := fun o => o.elim P G.get
  let S : Option (Fin G.length) → Finset (Fin n) := fun o =>
    o.elim Q (fun a => {s (idx a)})
  have hflat : ∀ o, x ∈ A o → ∀ {y : X},
      y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Θ.source →
      (y ∈ A o ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace (S o)) := by
    rintro (_ | a) hxa y hy hyΘ
    · change y ∈ P ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈
        coordSubspace ((Finset.univ.filter fun j : Fin n => m+1 ≤ j.val) ∪ {j₀})
      rw [HironakaG8P1ForeignCount.coordSubspace_union, coordSubspace_eq_complexCoordinatePlane,
        Set.mem_inter_iff, BlowupSNCTransform.mem_coordSubspace_singleton]
      exact (hAll y ⟨hy, hyΘ⟩).2.1
    · change x ∈ G.get a at hxa
      change y ∈ G.get a ↔ Θ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace {s (idx a)}
      rw [BlowupSNCTransform.mem_coordSubspace_singleton]
      have he := (hAll y ⟨hy, hyΘ⟩).2.2 (idx a) (hidxne a)
      rw [hidxget a] at he
      simpa only [hxa, true_and, flatCoord] using he
  have hOpenTrans : IsTransverse n ((Subtype.val : U → X) ⁻¹' P)
      (G.map ((Subtype.val : U → X) ⁻¹' ·)) := by
    intro y _hyP
    let GU := G.map ((Subtype.val : U → X) ⁻¹' ·)
    let c : Fin GU.length → Fin G.length := Fin.cast (List.length_map _)
    have hseen : ∀ o, y.val ∈ A o → x ∈ A o := by
      rintro (_ | a) hya
      · exact hP.2.1
      · change y.val ∈ G.get a at hya
        change x ∈ G.get a
        rw [← hidxget a] at hya ⊢
        exact ((hAll y.val y.property).2.2 (idx a) (hidxne a)).mp hya |>.1
    have hfy := coordinateFamilyAt_of_flattening Θ hflat y.property.1 y.property.2 hseen
    have hfu := isCoordinateFamilyAt_preimage_val_iff.mpr hfy
    refine ⟨Q, fun a => {s (idx (c a))}, ?_, ?_⟩
    · exact IsCoordinateFamilyAt.reindex hfu (Option.map c)
        (by rintro (_ | a); rfl; exact get_map_preimage G a)
        (by rintro (_ | a) <;> rfl)
    · intro a ha
      have hya : y.val ∈ G.get (c a) := by
        change y ∈ GU.get a at ha
        rwa [get_map_preimage] at ha
      have hxa : x ∈ G.get (c a) := hseen (some (c a)) hya
      have hxaOld : x ∈ E.get (idx (c a)) := by rw [hidxget]; exact hxa
      have hbound := hs (idx (c a)) hxaOld
      have hne := hOther (idx (c a)) hxaOld (hidxne (c a))
      refine ⟨Finset.card_singleton _, Finset.disjoint_singleton_left.mpr ?_⟩
      intro hmem
      rcases Finset.mem_union.mp hmem with hnormal | hpivot
      · exact Nat.not_lt_of_ge (Finset.mem_filter.mp hnormal).2 hbound
      · exact hne (Finset.mem_singleton.mp hpivot)
  have hGsnc := NormalCrossingsComparison.isSNCDivisor_of_sublist hE
    (List.eraseIdx_sublist E i₀.val)
  exact ⟨j₀, Θ, s, U, hjEq, hj₀, hsrc, hzero, hs, hinj, hOther,
    mem_flatDomain_self Θ, rfl, hAll,
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hGsnc,
    hOpenTrans⟩

end

end Hironaka.HironakaG8CaseTHypersurfaceFrame
