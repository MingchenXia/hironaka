/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionContactCoefficientRestriction
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionContactCoordinates
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSmoothSubmersionTangentContact HironakaSmoothSubmersionRelativeDifferentialIdeals
  HironakaSmoothSubmersionAdaptedProductCoordinates HironakaSmoothSubmersionRelativeOrder
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionMonomialOrdering
  TangentDirectionAlong BlowupFlatCoordinates BlowupSNCTransform GiraudAlong HomogenizedIdealAlong DerivativeIdealAlong
  DerivativeIdealAlongCoherent RelativePrincipalizationSpan GermIdealOrder MarkedIdeals MarkedIdeal
  HironakaSmoothSubmersionCoefficientIdeals
noncomputable section
variable {n : ℕ} {X : CMfd.{u} n}

theorem contactCoords_mem_original_plane {N : Set X} {x : X} {k : ℕ}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hflat : ∀ {z : X}, z ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x z ∈ Φ.source →
        (z ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x z) ∈ complexCoordinatePlane n k))
    {j l : Fin n} (hj : j.val < k) (hl : l.val+1 = k) (u : X → ℂ)
    (z : X) (hz : z ∈ flatDomain Φ) :
    contactCoords Φ j l u z ∈ complexCoordinatePlane n k ↔ z ∈ N := by
  have hswap : ∀ i : Fin n, k ≤ i.val → Equiv.swap j l i = i := fun i hi =>
    Equiv.swap_apply_of_ne_of_ne (fun h => by subst h; omega) (fun h => by subst h; omega)
  rw [hflat hz.1 hz.2]
  constructor
  · intro h i hi
    have hil : i ≠ l := fun he => by subst he; omega
    have he := h i hi
    simpa only [contactCoords_apply,hil,if_false,hswap i hi,flatMap] using he
  · intro h i hi
    have hil : i ≠ l := fun he => by subst he; omega
    simpa only [contactCoords_apply,hil,if_false,hswap i hi,flatMap] using h i hi

theorem contactCoords_contact_slot {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (j l : Fin n) (u : X → ℂ) (z : X) : contactCoords Φ j l u z l = u z := by
  simp [contactCoords_apply]

theorem exists_original_contact_coordinates
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong N I μ U u)
    (x : X) (hx : x ∈ contactCarrier N U u) :
    ∃ (k : ℕ) (l : Fin n)
      (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
      0 < k ∧ l.val+1 = k ∧
      Θ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Θ.toFun (chartAt (ComplexModel n) x x) = 0 ∧ flatDomain Θ ⊆ U ∧
      ∀ z ∈ flatDomain Θ,
        (z ∈ N ↔ flatMap Θ z ∈ complexCoordinatePlane n k) ∧
        (z ∈ contactCarrier N U u ↔ flatMap Θ z ∈ complexCoordinatePlane n (k-1)) ∧
        flatCoord Θ l z = u z := by
  obtain ⟨k,hkn,_,Φ,hΦsrc,hΦ0,hflat⟩ := hN.2 x hx.1.1
  change LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) at Φ
  change Φ.toFun (chartAt (ComplexModel n) x x) = 0 at hΦ0
  have hhol : ∀ z ∈ U, HolomorphicAt n u z := fun z hz =>
    holomorphicAt_of_mem_iterDerivIdealAlong
      (fun y g hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) (μ-1) z u (hu.mem z hz)
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one x hx.2 hx.1.2
  obtain ⟨j,hjk,hjne⟩ := exists_flatPartial_ne_zero hΦsrc hflat (mem_flatDomain_self Φ)
    hx.1.1 (hhol x hx.2) hξ hne
  let l : Fin n := ⟨k-1,by omega⟩
  have hl : l.val+1 = k := by dsimp [l]; omega
  have hO : IsOpen (U ∩ flatDomain Φ) := hu.isOpen.inter (isOpen_flatDomain Φ)
  have hxO : x ∈ U ∩ flatDomain Φ := ⟨hx.2,mem_flatDomain_self Φ⟩
  have hWs : ∀ z ∈ U ∩ flatDomain Φ,
      ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (contactCoords Φ j l u) z :=
    fun z hz => contMDiffAt_of_eventually_mdifferentiableAt
      (eventually_of_mem (hO.mem_nhds hz) fun w hw =>
        mdifferentiableAt_contactCoords j l hw.2 (hhol w hw.1))
  have hWx : contactCoords Φ j l u x = 0 := by
    ext i
    change contactCoords Φ j l u x i = (0 : ℂ)
    rw [contactCoords_apply]
    split_ifs with hil
    · exact hx.1.2
    · change Φ.toFun (chartAt (ComplexModel n) x x) (Equiv.swap j l i) = 0
      rw [hΦ0]
      rfl
  obtain ⟨Θ,hΘsrc,hΘ0,hΘ⟩ := exists_recentred_coords hO hWs hxO
    (injective_fderiv_contactCoords hΦsrc (hhol x hx.2) hjne)
  change LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x) at Θ
  refine ⟨k,l,Θ,by omega,hl,hΘsrc,hΘ0,fun z hz => (hΘ hz.1 hz.2).1.1,?_⟩
  intro z hz
  obtain ⟨hzO,he⟩ := hΘ hz.1 hz.2
  change flatMap Θ z = contactCoords Φ j l u z - contactCoords Φ j l u x at he
  have he' : flatMap Θ z = contactCoords Φ j l u z := by
    simpa only [hWx,sub_zero] using he
  refine ⟨?_,?_,?_⟩
  · rw [he']
    exact (contactCoords_mem_original_plane Φ hflat hjk hl u z hzO.2).symm
  · rw [he',contactCoords_mem_plane_iff hflat hjk hl u hzO.2]
    exact ⟨fun h => h.1,fun h => ⟨h,hzO.1⟩⟩
  · change flatMap Θ z l = u z
    rw [he',contactCoords_contact_slot]

private def JointContactCoordinates {m : ℕ} {Y : CMfd.{u} m}
    (f : Y → X) (N U : Set X) (u : X → ℂ) (y : Y) : Prop :=
  ∃ (k : ℕ) (l : Fin n)
    (Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (Γ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) y y))
    (ρ : Fin n ↪ Fin m),
    0 < k ∧ l.val+1 = k ∧
    Θ.source ⊆ (chartAt (ComplexModel n) (f y)).target ∧
    Θ.toFun (chartAt (ComplexModel n) (f y) (f y)) = 0 ∧
    Γ.source ⊆ (chartAt (ComplexModel m) y).target ∧
    Γ.toFun (chartAt (ComplexModel m) y y) = 0 ∧ flatDomain Θ ⊆ U ∧
    (∀ z ∈ flatDomain Θ,
      (z ∈ N ↔ flatMap Θ z ∈ complexCoordinatePlane n k) ∧
      (z ∈ contactCarrier N U u ↔ flatMap Θ z ∈ complexCoordinatePlane n (k-1)) ∧
      flatCoord Θ l z = u z) ∧
    ∀ z ∈ flatDomain Γ, f z ∈ flatDomain Θ ∧
      (f z ∈ N ↔ flatMap Γ z ∈ complexCoordinatePlane m (k+(m-n))) ∧
      (f z ∈ contactCarrier N U u ↔
        flatMap Γ z ∈ complexCoordinatePlane m ((k-1)+(m-n))) ∧
      flatCoord Γ (ρ l) z = u (f z) ∧
      ∀ j : Fin n, flatCoord Γ (ρ j) z = flatCoord Θ j (f z)

theorem exists_joint_contact_coordinates {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {I : GermIdeal n X} (hI : I.IsCoherent) {N : Set X} (hN : IsClosedSubmanifold n N)
    {μ : ℕ} {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong N I μ U u)
    (y : Y) (hy : y ∈ f ⁻¹' contactCarrier N U u) :
    JointContactCoordinates f N U u y := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (dimension_le_of_submersionAt (hf.isSubmersionAt y))
  obtain ⟨k,l,Θ,hk,hl,hΘsrc,hΘ0,hΘU,hΘ⟩ := exists_original_contact_coordinates hI hN hu (f y) hy
  let Γ := adaptedCoordinates (hf.isSubmersionAt y) Θ hΘ0
  let ρ : Fin n ↪ Fin (n+t) := ⟨actualTargetIndex n t,fun i j h => by
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp [actualTargetIndex] at hv
    omega⟩
  obtain ⟨hΓsrc,hΓ0,hΓ⟩ := adaptedCoordinates_dictionary (hf.isSubmersionAt y) Θ hΘ0
  refine ⟨k,l,Θ,Γ,ρ,hk,hl,hΘsrc,hΘ0,hΓsrc,hΓ0,hΘU,hΘ,?_⟩
  intro z hz
  have hzΘ := (hΓ z hz).1
  have hNplane := adaptedCoordinates_whole_centre (hf.isSubmersionAt y) Θ hΘ0 N k
    (fun w hw => (hΘ w hw).1) z hz
  have hCplane := adaptedCoordinates_whole_centre (hf.isSubmersionAt y) Θ hΘ0
    (contactCarrier N U u) (k-1) (fun w hw => (hΘ w hw).2.1) z hz
  change f z ∈ N ↔ flatMap Γ z ∈ complexCoordinatePlane (n+t) (t+k) at hNplane
  change f z ∈ contactCarrier N U u ↔
    flatMap Γ z ∈ complexCoordinatePlane (n+t) (t+(k-1)) at hCplane
  refine ⟨hzΘ,?_,?_,?_,?_⟩
  · simpa only [Nat.add_sub_cancel_left,Nat.add_comm] using hNplane
  · simpa only [Nat.add_sub_cancel_left,Nat.add_comm] using hCplane
  · exact (adaptedCoordinates_flatCoord_target (hf.isSubmersionAt y) Θ hΘ0 z hz l).trans
      (hΘ (f z) hzΘ).2.2
  · intro j
    exact adaptedCoordinates_flatCoord_target (hf.isSubmersionAt y) Θ hΘ0 z hz j

theorem exists_original_only_joint_contact_coordinates {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (hd : 1 ≤ M.d) (y : Y) (hy : y ∈ (markedPullback (m := m) f M).cosupp)
    (hmax : ¬ OrderGE n M.N M.ideal (f y) (M.d+1)) :
    ∃ (U : TopologicalSpace.Opens X) (u : X → ℂ), f y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d (U : Set X) u ∧
      IsTangentDirectionAlong (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal)
        M.d (f ⁻¹' (U : Set X)) (u ∘ f) ∧
      JointContactCoordinates f M.N (U : Set X) u y := by
  obtain ⟨U,u,hyU,hu,hup,_,_,hC,_⟩ := exists_joint_original_closed_contacts hf hI hN hd y hy hmax
  have hyt : f y ∈ cosupport n M.N M.ideal M.d := by
    have hyp : y ∈ f ⁻¹' cosupport n M.N M.ideal M.d := by
      rw [← cosupport_preimage_eq hf hI M.N M.d]
      exact hy
    exact hyp
  exact ⟨U,u,hyU,hu,hup,exists_joint_contact_coordinates hf hI hN hu y (hC ⟨hyt,hyU⟩)⟩

end
end Hironaka.HironakaSmoothSubmersionContactCoordinates
