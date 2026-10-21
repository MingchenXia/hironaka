/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionContactCoordinates
import Hironaka.Blowup.NestedFlattening
import Hironaka.MarkedIdeal.MaximalContact
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Analytic.RegularPointDimension

/-!
# Actual joint coordinates for the same centre and contact function

Nested flattening of the original centre inside the original smooth contact
hypersurface gives a genuine normal partial. Replacing only the last normal
coordinate by the literal chosen contact function preserves the entire centre.
Actual original maximal-order data internally choose the contact function;
no joint chart or vanishing-on-centre certificate is required at that endpoint.
Canonical normal freeness after this coordinate change is not asserted.
Blueprint: `hironaka-actual-centre-contact-coordinates-extension.tex`.
-/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualCentreContactCoordinates
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupFlatCoordinates GiraudAlong DerivativeIdealAlong DerivativeIdealAlongCoherent
  DerivativeIdeal TangentDirectionAlong LocalGiraudTransform NestedFlattening
  HironakaSmoothSubmersionContactCoordinates BlowupStrictSubmanifold BlowupSNCTransform GermIdealOrder

variable {n : ℕ} {X : CMfd.{u} n}

theorem positive_dimension_of_chartDeriv_ne_zero {x : X} {u : X → ℂ}
    {e : ComplexChart n X} {v : ComplexModel n} (hne : chartDeriv e v u x≠0) : 0<n := by
  by_contra h
  have hn : n=0 := by omega
  subst n
  have hv : v=0 := Subsingleton.elim _ _
  exact hne (by simp [chartDeriv,hv])

/-- The SAME literal contact function has a nonzero last NORMAL partial in any actual hypersurface flattening. -/
theorem flatPartial_last_ne_zero (hn : 0<n) {x : X} {H : Set X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (hflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
        (z∈H ↔ Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n (n-1)))
    (hxH : x∈H) {u : X → ℂ} (hu : (vanishingIdeal (n := n) H).mem x u)
    {e : ComplexChart n X} {v : ComplexModel n} (hxe : x∈e.val.source)
    (hne : chartDeriv e v u x≠0) :
    flatPartial Φ ⟨n-1,Nat.sub_lt hn one_pos⟩ u x≠0 := by
  intro hlast
  apply hne
  rw [chartDeriv_eq_sum_flat hsrc e v hxe (mem_flatDomain_self Φ) hu.1]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← flatPartial_eq (mem_flatDomain_self Φ) hu.1 i]
  by_cases hil : i=⟨n-1,Nat.sub_lt hn one_pos⟩
  · rw [hil,hlast,mul_zero]
  · have hik : i.val<n-1 := by
      have hil' : i.val≠n-1 := fun h => hil (Fin.ext h)
      have hin := i.isLt
      omega
    have ht := isTangentField_flatField hsrc hflat (single_mem_complexCoordinatePlane hik)
      (mem_flatDomain_self Φ)
    have hz := (ht.preserves u hu).2.self_of_nhds hxH
    change flatPartial Φ i u x=0 at hz
    rw [hz,mul_zero]

/-- Replacing only the SAME last normal slot preserves the ENTIRE centre plane. -/
theorem contactCoords_same_normal_mem_centre_plane (hn : 0<n) {x : X} {k : ℕ}
    (hk : k≤n-1) {C : Set X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
        (z∈C ↔ Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n k))
    (u : X → ℂ) (z : X) (hz : z∈flatDomain Φ)
    (huPlane : u z=0 ↔ flatMap Φ z∈complexCoordinatePlane n (n-1)) :
    contactCoords Φ ⟨n-1,Nat.sub_lt hn one_pos⟩ ⟨n-1,Nat.sub_lt hn one_pos⟩ u z∈
      complexCoordinatePlane n k ↔ z∈C := by
  let l : Fin n := ⟨n-1,Nat.sub_lt hn one_pos⟩
  have huLast : u z=0 ↔ flatMap Φ z l=0 := by
    simpa only [l,mem_plane_pred_iff hn] using huPlane
  rw [hflat hz.1 hz.2]
  constructor
  · intro h i hi
    by_cases hil : i=l
    · subst i
      exact huLast.mp (by simpa [l,contactCoords_apply] using h l hk)
    · have he := h i hi
      simp only [l] at hil
      simpa [contactCoords_apply,l,hil,flatMap] using he
  · intro h i hi
    by_cases hil : i=l
    · subst i
      have hu0 := huLast.mpr (h l hk)
      simpa [l,contactCoords_apply] using hu0
    · simp only [l] at hil
      simpa [contactCoords_apply,l,hil,flatMap] using h i hi

/-- The SAME actual regular centre and literal smooth contact function admit genuine joint coordinates. -/
theorem exists_actual_centre_contact_coordinates {C U : Set X} {x : X} {k : ℕ}
    (hC : RegularAtDim (n := n) C x k) (hU : IsOpen U) (hxU : x∈U)
    (u : X → ℂ) (hu : ∀ z∈U, HolomorphicAt n u z)
    (hu1 : ∀ z∈U, u z=0 → ∃ (e : ComplexChart n X) (v : ComplexModel n),
      z∈e.val.source ∧ chartDeriv e v u z≠0)
    (hzero : ∀ z∈C∩U, u z=0) :
    ∃ (hn : 0<n) (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      k≤n-1 ∧ Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x)=0 ∧ flatDomain Θ ⊆ U ∧
      ∀ z∈flatDomain Θ,
        (z∈C ↔ flatMap Θ z∈complexCoordinatePlane n k) ∧
        flatCoord Θ ⟨n-1,Nat.sub_lt hn one_pos⟩ z=u z := by
  have hux : u x=0 := hzero x ⟨hC.2.1,hxU⟩
  obtain ⟨e,v,hxe,hdu⟩ := hu1 x hxU hux
  have hn : 0<n := positive_dimension_of_chartDeriv_ne_zero hdu
  have hCU : RegularAtDim (n := n) (C∩U) x k :=
    RegularPointDimension.regularAtDim_of_inter_eq hU hxU (by rw [inter_assoc,inter_self]) hC
  let H : Set X := {z | u z=0}∩U
  have hH : RegularAtDim (n := n) H x (n-1) := regularAtDim_zeroSet hU hu hu1 hxU hux
  have hCH : C∩U⊆H := fun z hz => ⟨hzero z hz,hz.2⟩
  have hk : k≤n-1 := le_of_regularAtDim_subset hCU hH hCH
  obtain ⟨Φ,hΦsrc,hΦ0,hΦ⟩ := exists_nested_flattening hk hCU hH hCH
  change LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) at Φ
  change Φ.toFun (chartAt (ComplexModel n) x x)=0 at hΦ0
  have hflatC : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
        (z∈C∩U ↔ Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n k) :=
    fun {z} hz hzΦ => (hΦ hz hzΦ).1
  have hflatH : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
        (z∈H ↔ Φ.toFun (chartAt (ComplexModel n) x z)∈complexCoordinatePlane n (n-1)) :=
    fun {z} hz hzΦ => (hΦ hz hzΦ).2
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
  refine ⟨hn,Θ,hk,hΘsrc,hΘ0,fun z hz => (hΘ hz.1 hz.2).1.1,?_⟩
  intro z hz
  obtain ⟨hzO,he⟩ := hΘ hz.1 hz.2
  change flatMap Θ z=contactCoords Φ l l u z-contactCoords Φ l l u x at he
  have he' : flatMap Θ z=contactCoords Φ l l u z := by simpa only [hWx,sub_zero] using he
  have huPlane : u z=0 ↔ flatMap Φ z∈complexCoordinatePlane n (n-1) := by
    have hh := hflatH hzO.2.1 hzO.2.2
    change (u z=0 ∧ z∈U) ↔ _ at hh
    exact (and_iff_left hzO.1).symm.trans hh
  refine ⟨?_,?_⟩
  · rw [he']
    have hc := contactCoords_same_normal_mem_centre_plane hn hk Φ hflatC u z hzO.2 huPlane
    exact ((and_iff_left hzO.1).symm.trans hc.symm)
  · change flatMap Θ z l=u z
    rw [he',contactCoords_contact_slot]

/-- Genuine centre cosupport and the prescribed original tangent direction derive all joint-chart hypotheses. -/
theorem exists_actual_marked_centre_contact_coordinates
    {I : GermIdeal n X} (hI : I.IsCoherent) {m : ℕ} (hm : 1≤m)
    {C U : Set X} {x : X} {k : ℕ} (hC : RegularAtDim (n := n) C x k)
    (hCC : C⊆cosupport n univ I m) {u : X → ℂ}
    (hu : MaximalContact.IsTangentDirection I m U u) (hxU : x∈U) :
    ∃ (hn : 0<n) (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      k≤n-1 ∧ Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x)=0 ∧ flatDomain Θ ⊆ U ∧
      ∀ z∈flatDomain Θ,
        (z∈C ↔ flatMap Θ z∈complexCoordinatePlane n k) ∧
        flatCoord Θ ⟨n-1,Nat.sub_lt hn one_pos⟩ z=u z := by
  have hhol : ∀ z g, I.mem z g → HolomorphicAt n g z :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  apply exists_actual_centre_contact_coordinates hC hu.isOpen hxU u
    (fun z hz => holomorphicAt_of_mem_iterDerivIdeal hhol (m-1) z u (hu.mem z hz)) hu.multiplicity_one
  intro z hz
  exact MaximalContact.apply_eq_zero_of_mem_cosupport hhol hm (hCC hz.1) (hu.mem z hz.2)

/-- Only original coherent maximal-order data and the SAME actual smooth admissible centre are supplied. -/
theorem exists_original_maximal_order_centre_contact_coordinates
    {I : GermIdeal n X} (hI : I.IsCoherent) {m : ℕ} (hm : 1≤m)
    (hmax : MaximalContact.IsMaximalOrder I m)
    {C : Set X} {x : X} {k : ℕ} (hC : RegularAtDim (n := n) C x k)
    (hCC : C⊆cosupport n univ I m) :
    ∃ (U : Set X) (u : X → ℂ), x∈U ∧ MaximalContact.IsTangentDirection I m U u ∧
      ∃ (hn : 0<n) (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
        k≤n-1 ∧ Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
        Θ.toFun (chartAt (ComplexModel n) x x)=0 ∧ flatDomain Θ ⊆ U ∧
        ∀ z∈flatDomain Θ,
          (z∈C ↔ flatMap Θ z∈complexCoordinatePlane n k) ∧
          flatCoord Θ ⟨n-1,Nat.sub_lt hn one_pos⟩ z=u z := by
  have hhol : ∀ z g, I.mem z g → HolomorphicAt n g z :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  obtain ⟨U,u,hxU,hu⟩ := MaximalContact.exists_isTangentDirection hI hhol hm hmax (hCC hC.2.1)
  exact ⟨U,u,hxU,hu,exists_actual_marked_centre_contact_coordinates hI hm hC hCC hu hxU⟩

end
end Hironaka.HironakaActualCentreContactCoordinates
