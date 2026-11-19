import Hironaka.Analytic.PshCodimTwoExtension
import Hironaka.Analytic.PshAmbientExtensionLineControl
import Hironaka.Analytic.HolomorphicPullback
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Analytic.UscRegularizationContinuous
import Hironaka.Analytic.UscRegularizationLocality

set_option autoImplicit false

/-!
# Equivariance of the coordinate PSH extension

The coordinate extension used in the codimension-two and hypersurface
arguments is upper-semicontinuous regularization after replacing an exceptional
set by `-∞`.  It is therefore covariant under an open partial homeomorphism.
This file records that equality in the form needed by a local holomorphic
flattening: a coordinate extension on the target pulls back to the extension
across the inverse image of its exceptional set on the source.
-/

open Set Filter
open scoped Topology

namespace Hironaka.PshExtensionEquivariance


open PshCodimTwoExtension
open PshHypersurfaceRemovable
open PshAmbientExtensionLineControl

noncomputable section

variable {n : ℕ}

/-- Coordinate extensions agree at a point when their exceptional sets and
branches agree on one open neighbourhood of that point.  This isolates the
germ-locality required when a flattened analytic hypersurface is only equal to
a coordinate hyperplane on the local source of its flattening. -/
theorem extension_eq_of_eqOn_nhds
    {A A' O : Set (ComplexModel n)} {f g : ComplexModel n → EReal}
    {x : ComplexModel n} (hO : IsOpen O) (hxO : x ∈ O)
    (hA : ∀ y ∈ O, y ∈ A ↔ y ∈ A') (hfg : EqOn f g O) :
    extension A f x = extension A' g x := by
  classical
  apply uscRegularization_congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  simp only [hA y hy, hfg hy]

/-- Adding a finite continuous local potential commutes pointwise with a
coordinate extension.  This supplies the exact equality needed to pass from
ordinary PSH extension in flattened coordinates to theta-PSH extension after
adding a local potential. -/
theorem extension_add_coe_continuousAt_apply
    (A : Set (ComplexModel n)) (f : ComplexModel n → EReal)
    {c : ComplexModel n → ℝ} {x : ComplexModel n} (hc : ContinuousAt c x) :
    extension A (fun y => f y + (c y : EReal)) x =
      extension A f x + (c x : EReal) := by
  classical
  rw [extension_eq_uscRegularization, extension_eq_uscRegularization]
  have hraw : (fun y => if y ∈ A then (⊥ : EReal) else f y + (c y : EReal)) =
      fun y => (if y ∈ A then (⊥ : EReal) else f y) + (c y : EReal) := by
    funext y
    by_cases hy : y ∈ A
    · simp [hy]
    · simp [hy]
  rw [hraw]
  exact uscRegularization_add_coe_continuousAt_apply _ hc

/-- Coordinate extension commutes pointwise with every open partial
homeomorphism, at points in its source. -/
theorem extension_comp_openPartialHomeomorph_apply
    (A : Set (ComplexModel n)) (psi : ComplexModel n → EReal)
    (e : OpenPartialHomeomorph (ComplexModel n) (ComplexModel n))
    {x : ComplexModel n} (hx : x ∈ e.source) :
    extension (e ⁻¹' A) (psi ∘ e) x = extension A psi (e x) := by
  classical
  rw [extension_eq_uscRegularization, extension_eq_uscRegularization]
  have hraw : (fun y => if y ∈ e ⁻¹' A then (⊥ : EReal) else (psi ∘ e) y) =
      (fun y => if y ∈ A then (⊥ : EReal) else psi y) ∘ e := by
    funext y
    simp only [Function.comp_apply, mem_preimage]
  rw [hraw]
  exact uscRegularization_comp_openPartialHomeomorph_apply _ e hx

/-- The preceding covariance specialized to a local holomorphic equivalence.
The equality is valid on the actual local source of the flattening; no values
outside that source are used. -/
theorem extension_comp_localHolomorphicEquivAt_apply
    {p : ComplexModel n} (Phi : LocalHolomorphicEquivAt (n := n) p)
    (A : Set (ComplexModel n)) (psi : ComplexModel n → EReal)
    {x : ComplexModel n} (hx : x ∈ Phi.source) :
    extension (Phi.toFun ⁻¹' A) (psi ∘ Phi.toFun) x =
      extension A psi (Phi.toFun x) := by
  simpa only [LocalHolomorphicEquivAt.coe_toOpenPartialHomeomorph] using
    extension_comp_openPartialHomeomorph_apply A psi Phi.toOpenPartialHomeomorph hx

/-- Local upper bounds off a flattened hypersurface transport through the
inverse coordinate map.  The target neighbourhood is kept inside the actual
target of the local equivalence, so no arbitrary values of `Phi.invFun` are
used. -/
theorem locallyBoundedAboveOff_comp_localHolomorphicEquivAt_inv
    {p : ComplexModel n} (Phi : LocalHolomorphicEquivAt (n := n) p)
    (i : Fin n) (S W : Set (ComplexModel n)) (f : ComplexModel n → EReal)
    (hW : IsOpen W) (hbound : LocallyBoundedAboveOff S W f)
    (hS : ∀ y ∈ W, y ∈ S ↔ Phi.toFun y ∈ coordHyperplane i) :
    LocallyBoundedAboveOff (coordHyperplane i)
      (Phi.target ∩ Phi.invFun ⁻¹' W) (fun b => f (Phi.invFun b)) := by
  have hB : IsOpen (Phi.target ∩ Phi.invFun ⁻¹' W) :=
    Phi.invFun_holomorphic.continuousOn.isOpen_inter_preimage Phi.isOpen_target hW
  intro b hb
  obtain ⟨U, hU, C, hC⟩ := hbound (Phi.invFun b) hb.2
  have hpre : Phi.invFun ⁻¹' U ∈ 𝓝 b :=
    (Phi.invFun_holomorphic.differentiableAt
      (Phi.isOpen_target.mem_nhds hb.1)).continuousAt.preimage_mem_nhds hU
  refine ⟨(Phi.target ∩ Phi.invFun ⁻¹' W) ∩ Phi.invFun ⁻¹' U,
    inter_mem (hB.mem_nhds hb) hpre, C, ?_⟩
  intro y hy hyH
  have hyW : Phi.invFun y ∈ W := hy.1.2
  have hyt : y ∈ Phi.target := hy.1.1
  have hyS : Phi.invFun y ∉ S := by
    intro hyS
    have : Phi.toFun (Phi.invFun y) ∈ coordHyperplane i := (hS _ hyW).mp hyS
    exact hyH (by rwa [Phi.right_inv y hyt] at this)
  exact hC (Phi.invFun y) hy.2 hyS

/-- A PSH branch on the complement of a locally flattened hypersurface
transports through the inverse coordinate map.  The target domain is kept
inside the genuine target of the local equivalence, so the inverse and the
right-inverse identity are only invoked where they are certified. -/
theorem plurisubharmonicOn_comp_localHolomorphicEquivAt_inv
    {p : ComplexModel n} (Phi : LocalHolomorphicEquivAt (n := n) p)
    (i : Fin n) (S W : Set (ComplexModel n)) (f : ComplexModel n → EReal)
    (hW : IsOpen W) (hpsh : PlurisubharmonicOn f (W \ S))
    (hS : ∀ y ∈ W, y ∈ S ↔ Phi.toFun y ∈ coordHyperplane i) :
    PlurisubharmonicOn (fun b => f (Phi.invFun b))
      ((Phi.target ∩ Phi.invFun ⁻¹' W) \ coordHyperplane i) := by
  have hB : IsOpen (Phi.target ∩ Phi.invFun ⁻¹' W) :=
    Phi.invFun_holomorphic.continuousOn.isOpen_inter_preimage Phi.isOpen_target hW
  have hH : IsClosed (coordHyperplane i) := by
    change IsClosed {z : ComplexModel n | z i = 0}
    exact isClosed_singleton.preimage (PiLp.continuous_apply 2 _ i)
  have hBA : IsOpen ((Phi.target ∩ Phi.invFun ⁻¹' W) \ coordHyperplane i) := hB.sdiff hH
  refine HolomorphicPullback.plurisubharmonicOn_comp_holomorphic
    (F := Phi.invFun) (V := W \ S) hBA
    (Phi.invFun_holomorphic.mono (sdiff_subset.trans inter_subset_left)) ?_ hpsh
  intro b hb
  have hbW : Phi.invFun b ∈ W := hb.1.2
  refine ⟨hbW, ?_⟩
  intro hbS
  have hbT : b ∈ Phi.target := hb.1.1
  have : Phi.toFun (Phi.invFun b) ∈ coordHyperplane i := (hS _ hb.1.2).mp hbS
  exact hb.2 (by rwa [Phi.right_inv b hbT] at this)

/-- The coordinate-hyperplane removable theorem transports through a local
holomorphic equivalence.  It gives a PSH extension on the local source across
the inverse image of the coordinate hyperplane.  This is the analytic core of
the regular-hypersurface chart argument; set-theoretic identification of that
inverse image with the analytic stratum is kept as a separate local step. -/
theorem plurisubharmonicOn_extension_preimage_coordHyperplane
    {p : ComplexModel n} (Phi : LocalHolomorphicEquivAt (n := n) p)
    (i : Fin n) (B : Set (ComplexModel n)) (psi : ComplexModel n → EReal)
    (hB : IsOpen B)
    (hbound : LocallyBoundedAboveOff (coordHyperplane i) B psi)
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i)) :
    PlurisubharmonicOn
      (extension (Phi.toFun ⁻¹' coordHyperplane i) (psi ∘ Phi.toFun))
      (Phi.source ∩ Phi.toFun ⁻¹' B) := by
  have hD : IsOpen (Phi.source ∩ Phi.toFun ⁻¹' B) :=
    Phi.toFun_holomorphic.continuousOn.isOpen_inter_preimage Phi.isOpen_source hB
  have hmap : MapsTo Phi.toFun (Phi.source ∩ Phi.toFun ⁻¹' B) B :=
    fun _ hx => hx.2
  have htarget : PlurisubharmonicOn (extension (coordHyperplane i) psi) B :=
    plurisubharmonicOn_extension_of_punctured_plurisubharmonic hB hbound hpsi hBA
  have hpull : PlurisubharmonicOn
      (fun y => extension (coordHyperplane i) psi (Phi.toFun y))
      (Phi.source ∩ Phi.toFun ⁻¹' B) :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic hD
      (Phi.toFun_holomorphic.mono inter_subset_left) hmap htarget
  intro x hx
  apply (hpull x hx).congr
  filter_upwards [hD.mem_nhds hx] with y hy
  exact (extension_comp_localHolomorphicEquivAt_apply Phi (coordHyperplane i) psi hy.1).symm

/-- A local analytic hypersurface that is flattened to a coordinate
hyperplane has a PSH coordinate extension on the source.  The hypotheses keep
the two genuinely local facts separate: the exceptional set is the inverse
image of the hyperplane on `Phi.source`, and the source branch is the pullback
of the target branch there.  Germ locality then identifies the two upper
regularizations without asserting any equality outside the chart. -/
theorem plurisubharmonicOn_extension_of_locally_flattened_coordHyperplane
    {p : ComplexModel n} (Phi : LocalHolomorphicEquivAt (n := n) p)
    (i : Fin n) (B S : Set (ComplexModel n))
    (f psi : ComplexModel n → EReal)
    (hS : ∀ y ∈ Phi.source, y ∈ S ↔ Phi.toFun y ∈ coordHyperplane i)
    (hfg : EqOn f (psi ∘ Phi.toFun) Phi.source)
    (hB : IsOpen B)
    (hbound : LocallyBoundedAboveOff (coordHyperplane i) B psi)
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i)) :
    PlurisubharmonicOn (extension S f) (Phi.source ∩ Phi.toFun ⁻¹' B) := by
  have hflat : PlurisubharmonicOn
      (extension (Phi.toFun ⁻¹' coordHyperplane i) (psi ∘ Phi.toFun))
      (Phi.source ∩ Phi.toFun ⁻¹' B) :=
    plurisubharmonicOn_extension_preimage_coordHyperplane Phi i B psi hB hbound hpsi hBA
  have hD : IsOpen (Phi.source ∩ Phi.toFun ⁻¹' B) :=
    Phi.toFun_holomorphic.continuousOn.isOpen_inter_preimage Phi.isOpen_source hB
  intro x hx
  apply (hflat x hx).congr
  filter_upwards [hD.mem_nhds hx] with y hy
  exact (extension_eq_of_eqOn_nhds Phi.isOpen_source hy.1 hS hfg).symm

/-- Local-domain form of the flattened-hypersurface extension theorem.  The
flattening, the set equation, and the branch equation are only required on an
open neighbourhood `O`; the conclusion is correspondingly restricted to the
part of `O` whose image lies in the target coordinate domain. -/
theorem plurisubharmonicOn_extension_of_locally_flattened_coordHyperplane_on
    {p : ComplexModel n} (Phi : LocalHolomorphicEquivAt (n := n) p)
    (i : Fin n) (B S O : Set (ComplexModel n))
    (f psi : ComplexModel n → EReal)
    (hO : IsOpen O)
    (hS : ∀ y ∈ O, y ∈ S ↔ Phi.toFun y ∈ coordHyperplane i)
    (hfg : EqOn f (psi ∘ Phi.toFun) O)
    (hB : IsOpen B)
    (hbound : LocallyBoundedAboveOff (coordHyperplane i) B psi)
    (hpsi : PlurisubharmonicOn psi (B \ coordHyperplane i))
    (hBA : IsOpen (B \ coordHyperplane i)) :
    PlurisubharmonicOn (extension S f) (O ∩ (Phi.source ∩ Phi.toFun ⁻¹' B)) := by
  have hflat : PlurisubharmonicOn
      (extension (Phi.toFun ⁻¹' coordHyperplane i) (psi ∘ Phi.toFun))
      (Phi.source ∩ Phi.toFun ⁻¹' B) :=
    plurisubharmonicOn_extension_preimage_coordHyperplane Phi i B psi hB hbound hpsi hBA
  have hD : IsOpen (O ∩ (Phi.source ∩ Phi.toFun ⁻¹' B)) :=
    hO.inter (Phi.toFun_holomorphic.continuousOn.isOpen_inter_preimage Phi.isOpen_source hB)
  intro x hx
  apply (hflat x hx.2).congr
  filter_upwards [hD.mem_nhds hx] with y hy
  exact (extension_eq_of_eqOn_nhds hO hy.1 hS hfg).symm

end

end Hironaka.PshExtensionEquivariance
