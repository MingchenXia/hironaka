/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualSuppliedFlatteningNormalPowers
import Hironaka.Blowup.SimultaneousNormalCrossings
import Hironaka.Invariant.CodimOneAdmissibleAlong

/-!
# Literal contact and the entire old boundary in the transverse-contact branch

Genuine transversality of the actual contact carrier to the old SNC boundary
and normal crossings of the same centre produce one actual joint chart.
Replacing only its last normal slot retains the literal original contact
function and every original boundary slot. Canonical reduced normal powers
then hold for that exact chart, by the supplied-flattening producer.
Contact transversality is a genuine retained geometric hypothesis.
Blueprint: `hironaka-actual-boundary-contact-normal-powers-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualBoundaryContactNormalPowers
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  NormalCrossings BlowupSNCTransform SimultaneousNormalCrossings RegularPointDimension
  BlowupStrictSubmanifold RegularPatchPullback GiraudAlong BlowupFlatCoordinates
  TangentDirectionAlong HironakaActualCentreContactCoordinates
  HironakaSmoothSubmersionContactCoordinates HironakaActualSuppliedFlatteningNormalPowers
  HironakaSmoothCentreNearbyIdeal HironakaActualOriginalFormalTaylor
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualCoefficientPresentationCentrePower
  HironakaRelativeNormalCoherentTranslatedJets HironakaActualHSConstantCentreJetFrames GermIdealOrder
  DerivativeIdeal HironakaHolomorphicJetChartInvariance HironakaRelativeNormalDeformationInitialRelations
  HironakaSmoothCentreCoherentDomain

variable {n : ℕ} {X : CMfd.{u} n}

private theorem plane_min (a : ℕ) :
    complexCoordinatePlane n (min n a)=complexCoordinatePlane n a := by
  ext z
  constructor
  · intro h i hi
    exact h i (by omega)
  · intro h i hi
    exact h i (by have hin:=i.isLt; omega)

private theorem sub_mem_plane_iff {a : ℕ} {z c : ComplexModel n}
    (hc : c∈complexCoordinatePlane n a) :
    z-c∈complexCoordinatePlane n a ↔ z∈complexCoordinatePlane n a := by
  constructor
  · intro h i hi
    have he:=h i hi
    simpa only [PiLp.sub_apply,hc i hi,sub_zero] using he
  · intro h i hi
    change z i-c i=0
    rw [h i hi,hc i hi,sub_self]

/-- True transverse geometry gives centred simultaneous coordinates with the ACTUAL regular dimensions. -/
theorem exists_centred_transverse_centre_hypersurface_coordinates
    (hn : 0<n) {C H : Set X} {E : List (Set X)} {x : X} {d : ℕ}
    (hC : RegularAtDim (n := n) C x d)
    (hH : RegularAtDim (n := n) H x (n-1)) (hCH : C⊆H)
    (hE : IsSNCDivisor n E) (hT : IsTransverse n H E)
    (hNC : HasNormalCrossings n C E) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (s : Fin E.length → Fin n), d≤n-1 ∧
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
      (∀ i,x∈E.get i → (s i).val<n-1) ∧ Set.InjOn s {i | x∈E.get i} ∧
      ∀ z∈flatDomain Φ,
        (z∈C ↔ flatMap Φ z∈complexCoordinatePlane n d) ∧
        (z∈H ↔ flatMap Φ z∈complexCoordinatePlane n (n-1)) ∧
        ∀ i,x∈E.get i → (z∈E.get i ↔ flatCoord Φ (s i) z=0) := by
  have hd : d≤n-1 := le_of_regularAtDim_subset hC hH hCH
  obtain ⟨a,b,Ψ,s,hsrc,hs,hinj,hflat⟩ :=
    isAdaptedAt_of_hasNormalCrossings hn hCH hE hT hNC hC.2.1
  let c := flatMap Ψ x
  have hxD := mem_flatDomain_self Ψ
  have hcC : c∈complexCoordinatePlane n a := (hflat hxD.1 hxD.2).1.mp hC.2.1
  have hcH : c∈complexCoordinatePlane n b := (hflat hxD.1 hxD.2).2.1.mp hH.2.1
  have hcE : ∀ i,x∈E.get i → c (s i)=0 :=
    fun i hi => (hflat hxD.1 hxD.2).2.2 i hi |>.mp hi
  let Φ := subConst Ψ c
  have hΦsrc : Φ.source⊆(chartAt (ComplexModel n) x).target := hsrc
  have hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0 := sub_self _
  have hflatC : ∀ {z : X},z∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z∈Φ.source →
      (z∈C ↔ Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n a) := by
    intro z hz hzΦ
    exact (hflat hz hzΦ).1.trans (sub_mem_plane_iff hcC).symm
  have hflatH : ∀ {z : X},z∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z∈Φ.source →
      (z∈H ↔ Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n b) := by
    intro z hz hzΦ
    exact (hflat hz hzΦ).2.1.trans (sub_mem_plane_iff hcH).symm
  have hCa : RegularAtDim (n := n) C x (min n a) := by
    refine ⟨Nat.min_le_left _ _,hC.2.1,Φ,hΦsrc,hΦ0,?_⟩
    intro z hz hzΦ
    rw [plane_min]
    exact hflatC hz hzΦ
  have hHb : RegularAtDim (n := n) H x (min n b) := by
    refine ⟨Nat.min_le_left _ _,hH.2.1,Φ,hΦsrc,hΦ0,?_⟩
    intro z hz hzΦ
    rw [plane_min]
    exact hflatH hz hzΦ
  have ha : a=d := by
    have he := eq_of_regularAtDim hCa hC
    omega
  have hb : b=n-1 := by
    have he := eq_of_regularAtDim hHb hH
    omega
  subst a
  subst b
  refine ⟨Φ,s,hd,hΦsrc,hΦ0,hs,hinj,?_⟩
  intro z hz
  refine ⟨hflatC hz.1 hz.2,hflatH hz.1 hz.2,?_⟩
  intro i hi
  have he := (hflat hz.1 hz.2).2.2 i hi
  change (z∈E.get i ↔ (Ψ.toFun (chartAt (ComplexModel n) x z)-c) (s i)=0)
  simpa only [PiLp.sub_apply,hcE i hi,sub_zero] using he


/-- The SAME literal contact function and EVERY original boundary slot survive one actual joint chart. -/
theorem exists_actual_boundary_contact_coordinates
    {C U : Set X} {x : X} {d : ℕ} {E : List (Set X)}
    (hC : RegularAtDim (n := n) C x d) (hU : IsOpen U) (hxU : x∈U)
    (u : X → ℂ) (hu : ∀ z∈U,HolomorphicAt n u z)
    (hu1 : ∀ z∈U,u z=0 → ∃ (e : ComplexChart n X) (v : ComplexModel n),
      z∈e.val.source ∧ chartDeriv e v u z≠0)
    (hzero : ∀ z∈C∩U,u z=0)
    (hE : IsSNCDivisor n E) (hNC : HasNormalCrossings n C E)
    (hT : IsTransverse n ({z | u z=0}∩U) E) :
    ∃ (hn : 0<n) (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (s : Fin E.length → Fin n), d≤n-1 ∧
      Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x)=0 ∧ flatDomain Θ⊆U ∧
      (∀ i,x∈E.get i → (s i).val<n-1) ∧ Set.InjOn s {i | x∈E.get i} ∧
      ∀ z∈flatDomain Θ,
        (z∈C ↔ flatMap Θ z∈complexCoordinatePlane n d) ∧
        flatCoord Θ ⟨n-1,Nat.sub_lt hn one_pos⟩ z=u z ∧
        ∀ i,x∈E.get i → (z∈E.get i ↔ flatCoord Θ (s i) z=0) := by
  have hux : u x=0 := hzero x ⟨hC.2.1,hxU⟩
  obtain ⟨e,v,hxe,hdu⟩ := hu1 x hxU hux
  have hn : 0<n := positive_dimension_of_chartDeriv_ne_zero hdu
  have hCU : RegularAtDim (n := n) (C∩U) x d :=
    regularAtDim_of_inter_eq hU hxU (by rw [inter_assoc,inter_self]) hC
  let H : Set X := {z | u z=0}∩U
  have hH : RegularAtDim (n := n) H x (n-1) :=
    LocalGiraudTransform.regularAtDim_zeroSet hU hu hu1 hxU hux
  have hCH : C∩U⊆H := fun z hz => ⟨hzero z hz,hz.2⟩
  have hNCU : HasNormalCrossings n (C∩U) E := by
    apply CodimOneAdmissibleAlong.hasNormalCrossings_of_forall_eventually
    intro z hz
    refine ⟨C,hz.1,?_,hNC⟩
    filter_upwards [hU.mem_nhds hz.2] with y hy
    exact and_iff_left hy
  obtain ⟨Φ,s,hd,hΦsrc,hΦ0,hslt,hinj,hflat⟩ :=
    exists_centred_transverse_centre_hypersurface_coordinates hn hCU hH hCH hE hT hNCU
  have hflatC : ∀ {z : X},z∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z∈Φ.source →
      (z∈C∩U ↔ Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n d) :=
    fun {z} hz hzΦ => (hflat z ⟨hz,hzΦ⟩).1
  have hflatH : ∀ {z : X},z∈(chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z∈Φ.source →
      (z∈H ↔ Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n (n-1)) :=
    fun {z} hz hzΦ => (hflat z ⟨hz,hzΦ⟩).2.1
  have huH : (vanishingIdeal (n := n) H).mem x u :=
    ⟨hu x hxU,Eventually.of_forall (fun _ hz => hz.1)⟩
  have hlast := flatPartial_last_ne_zero hn Φ hΦsrc hflatH hH.2.1 huH hxe hdu
  let l : Fin n := ⟨n-1,Nat.sub_lt hn one_pos⟩
  let O : Set X := U∩flatDomain Φ
  have hO : IsOpen O := hU.inter (isOpen_flatDomain Φ)
  have hxO : x∈O := ⟨hxU,mem_flatDomain_self Φ⟩
  have hWs : ∀ z∈O,
      ContMDiffAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (contactCoords Φ l l u) z :=
    fun z hz => contMDiffAt_of_eventually_mdifferentiableAt
      (eventually_of_mem (hO.mem_nhds hz) fun y hy =>
        mdifferentiableAt_contactCoords l l hy.2 (hu y hy.1))
  have hWx : contactCoords Φ l l u x=0 := by
    ext i
    change contactCoords Φ l l u x i=(0 : ℂ)
    rw [contactCoords_apply]
    split_ifs
    · exact hux
    · change Φ.toFun (chartAt (ComplexModel n) x x) (Equiv.swap l l i)=0
      rw [hΦ0]
      rfl
  obtain ⟨Θ,hΘsrc,hΘ0,hΘ⟩ := exists_recentred_coords hO hWs hxO
    (injective_fderiv_contactCoords hΦsrc (hu x hxU) hlast)
  refine ⟨hn,Θ,s,hd,hΘsrc,hΘ0,fun z hz => (hΘ hz.1 hz.2).1.1,hslt,hinj,?_⟩
  intro z hz
  obtain ⟨hzO,he⟩ := hΘ hz.1 hz.2
  change flatMap Θ z=contactCoords Φ l l u z-contactCoords Φ l l u x at he
  have he' : flatMap Θ z=contactCoords Φ l l u z := by simpa only [hWx,sub_zero] using he
  have huPlane : u z=0 ↔ flatMap Φ z∈complexCoordinatePlane n (n-1) := by
    have hh := hflatH hzO.2.1 hzO.2.2
    change (u z=0 ∧ z∈U) ↔ _ at hh
    exact (and_iff_left hzO.1).symm.trans hh
  refine ⟨?_,?_,?_⟩
  · rw [he']
    have hc := contactCoords_same_normal_mem_centre_plane hn hd Φ hflatC u z hzO.2 huPlane
    exact ((and_iff_left hzO.1).symm.trans hc.symm)
  · change flatMap Θ z l=u z
    rw [he',contactCoords_contact_slot]
  · intro i hi
    have hsne : s i≠l := fun h => by
      have hh:=hslt i hi
      rw [h] at hh
      exact Nat.lt_irrefl _ hh
    have heq : contactCoords Φ l l u z (s i)=flatCoord Φ (s i) z := by
      simp [contactCoords_apply,hsne,flatCoord,flatMap]
    have hh := (hflat z hzO.2).2.2 i hi
    change (z∈E.get i ↔ flatMap Θ z (s i)=0)
    rw [he',heq]
    exact hh

section Original
variable {d t : ℕ} {M : CMfd.{u} (d+t)}

/-- Original tangent membership supplies vanishing; true transverse contact geometry gives SAME-chart hV. -/
theorem exists_original_boundary_contact_reduced_normal_powers
    {A : GermIdeal (d+t) M} (hA : A.IsCoherent) {m : ℕ} (hm : 1≤m)
    {C U : Set M} {x : M} {E : List (Set M)}
    (hC : RegularAtDim (n := d+t) C x d)
    (hCC : C⊆cosupport (d+t) univ A m)
    {u : M → ℂ} (hu : MaximalContact.IsTangentDirection A m U u) (hxU : x∈U)
    (hE : IsSNCDivisor (d+t) E) (hNC : HasNormalCrossings (d+t) C E)
    (hT : IsTransverse (d+t) ({z | u z=0}∩U) E)
    (hhs : ∀ y∈C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ (hn : 0<d+t) (Θ : LocalHolomorphicEquivAt (n := d+t) (chartAt (ComplexModel (d+t)) x x))
      (s : Fin E.length → Fin (d+t)), d≤d+t-1 ∧
      Θ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      Θ.toFun (chartAt (ComplexModel (d+t)) x x)=0 ∧ flatDomain Θ⊆U ∧
      (∀ i,x∈E.get i → (s i).val<d+t-1) ∧ Set.InjOn s {i | x∈E.get i} ∧
      (∀ z∈flatDomain Θ,
        (z∈C ↔ flatMap Θ z∈complexCoordinatePlane (d+t) d) ∧
        flatCoord Θ ⟨d+t-1,Nat.sub_lt hn one_pos⟩ z=u z ∧
        ∀ i,x∈E.get i → (z∈E.get i ↔ flatCoord Θ (s i) z=0)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Θ) 0)
      ∀ a : actualInitialVertices MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0),
        actualReducedVertexSeries MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) a∈
            actualFormalCoordinateIdeal (d+t) (actualTangentCentreVariables d t)^
              Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val := by
  have hhol : ∀ z g,A.mem z g → HolomorphicAt (d+t) g z :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hA hg
  have huhol : ∀ z∈U,HolomorphicAt (d+t) u z :=
    fun z hz => DerivativeIdeal.holomorphicAt_of_mem_iterDerivIdeal hhol (m-1) z u (hu.mem z hz)
  have hzero : ∀ z∈C∩U,u z=0 :=
    fun z hz => MaximalContact.apply_eq_zero_of_mem_cosupport hhol hm (hCC hz.1) (hu.mem z hz.2)
  obtain ⟨hn,Θ,s,hd,hsrc,h0,hDom,hslt,hinj,hΘ⟩ :=
    exists_actual_boundary_contact_coordinates hC hu.isOpen hxU u huhol hu.multiplicity_one hzero hE hNC hT
  refine ⟨hn,Θ,s,hd,hsrc,h0,hDom,hslt,hinj,hΘ,?_⟩
  apply supplied_flattening_reduced_normal_powers C x Θ hsrc h0 _ A hA hhs
  intro y hy hyΘ
  exact (hΘ y ⟨hy,hyΘ⟩).1

end Original

end
end Hironaka.HironakaActualBoundaryContactNormalPowers
