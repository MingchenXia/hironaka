/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaStageCenters
import Hironaka.MarkedIdeal.GermIdealOrderValue
import Hironaka.Invariant.CoherentZeroLocus
import Hironaka.Blowup.StrictVanishingIdealSupport

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Current reduced ideals and the actual residual order

Blueprint `hironaka-current-strict-transform-ideal-extension.tex`.
The actual current controlled ideal, and then its actual nonmonomial part,
vanish on the current strict transform by preserved dense-open geometry.
The fresh reduced order is bounded by the old residual order. This does not
assert descent of the full reinitialized invariant or completion of G8.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaCurrentStrictTransformIdeal

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
open BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
open GermIdealOrder HironakaAdmissibleSequence HironakaAdmissibleCalculus
open NonmonomialOrderLocal ResolutionInvariantSpec InvDomainTowerAlong

noncomputable section

variable {n : ℕ}

/-- Ideal inclusion reverses order, including infinite order. -/
theorem order_le_of_ideal_le {X : CMfd.{u} n} {N : Set X} {a b : GermIdeal n X}
    (h : a.Le b) (x : X) : order n N b x ≤ order n N a x := by
  refine iSup₂_le fun q hq => ?_
  exact le_iSup₂ (f := fun (k : ℕ) (_ : OrderGE n N a x k) => (k : ℕ∞)) q
    (fun g hg => hq g (h x g hg))

/-- A preserved dense initial open part puts the actual current strict transform
inside the actual controlled cosupport, even for a singular initial set. -/
theorem strictTransform_subset_cosupp_of_centresAvoid {X Y : CMfd.{u} n} {W : Set X}
    {E₀ : List (Set X)} {k : ℕ} (hW : IsClosed W)
    (hdom : IsInvDomain k (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    (O : Opens X) (hdense : W ⊆ closure (W ∩ (O : Set X))) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    (hO : CentresAvoid O T) :
    strictTransform n T.proj W ⊆
      (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).cosupp := by
  let m : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
  obtain ⟨hN, hcoh, _⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := m) rfl hdom.isWellFormed.isCoherent T hT
  have hcos : (geoTransformAlong m T).cosupp = (geoTransformAlong m T).ideal.zeroLocus := by
    rw [MarkedIdeal.cosupp, hN, d_geoTransformAlong, cosupport_one
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg), univ_inter]
  have hclosed : IsClosed (geoTransformAlong m T).cosupp := by
    rw [hcos]
    exact OrderTaylor.isClosed_zeroLocus_of_isCoherent hcoh
  have hD := strictTransform_subset_closure_diff T.contMDiff_proj hW (F := (O : Set X)ᶜ)
    (by simpa only [Set.sdiff_compl] using hdense)
  refine hD.trans (closure_minimal ?_ hclosed)
  rintro y ⟨hyS, hyO⟩
  have hyO' : T.proj y ∈ O := by simpa using hyO
  exact (HironakaEmbeddedBoundary.mem_cosupp_iff_of_centresAvoid hW hdom O T hT hO hyO').mpr
    (strictTransform_subset_preimage T.contMDiff_proj.continuous hW hyS)

/-- Actual controlled germs vanish near every point on the current strict transform. -/
theorem controlledIdeal_le_currentStrictIdeal {X Y : CMfd.{u} n} {W : Set X}
    {E₀ : List (Set X)} {k : ℕ} (hW : IsClosed W)
    (hdom : IsInvDomain k (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    (O : Opens X) (hdense : W ⊆ closure (W ∩ (O : Set X))) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    (hO : CentresAvoid O T) :
    (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T).ideal.Le
      (vanishingIdeal (n := n) (strictTransform n T.proj W)) := by
  let m : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
  obtain ⟨hN, hcoh, _⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := m) rfl hdom.isWellFormed.isCoherent T hT
  apply BlowupTowerTransforms.le_vanishingIdeal_of_subset_zeroLocus hcoh
  have hS := strictTransform_subset_cosupp_of_centresAvoid hW hdom O hdense T hT hO
  rw [MarkedIdeal.cosupp, hN, d_geoTransformAlong, cosupport_one
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg), univ_inter] at hS
  exact hS

/-- The actual residual ideal has the original germs away from the whole divisor. -/
theorem nmPart_mem_iff_of_notMem_boundary {X : CMfd.{u} n} {m : MarkedIdeal n X}
    (hN : m.N = univ) (hcoh : m.ideal.IsCoherent) {x : X}
    (hx : x ∉ ⋃ H ∈ m.E, H) {g : X → ℂ} : (nmPart m).mem x g ↔ m.ideal.mem x g := by
  constructor
  · intro hg
    have h1 : (MonomialPartAlong.monomialPartAlong n m.N m.ideal m.E).mem x (fun _ => (1 : ℂ)) :=
      ⟨holomorphicAt_const 1, fun i _ hi => False.elim (hx (mem_iUnion₂.mpr ⟨m.E.get i, List.get_mem _ _, hi⟩))⟩
    have hp := hg.2 (fun _ => (1 : ℂ)) h1
    change (RestrictedIdealExtension.restrictOn n m.N m.ideal).mem x (fun y => 1 * g y) at hp
    rw [hN, BlowupTowerTransforms.restrictOn_univ hcoh] at hp
    simpa only [one_mul] using hp
  · exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hcoh x g

/-- Dividing off the actual monomial part preserves vanishing on a set dense
outside the divisor, by coherence of the residual ideal and its closed zero locus. -/
theorem nmPart_le_vanishingIdeal_of_dense_zeroLocus {X : CMfd.{u} n} {m : MarkedIdeal n X}
    (hn : 0 < n) (hN : m.N = univ) (hdom : IsInvDomain n m) {S : Set X}
    (hS : S ⊆ m.ideal.zeroLocus) (hdense : S ⊆ closure (S \ ⋃ H ∈ m.E, H)) :
    (nmPart m).Le (vanishingIdeal (n := n) S) := by
  have hcoh := MonomialPartAlong.isCoherent_nonmonomialPartAlong hn
    hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isSNCDivisor
    hdom.isWellFormed.isTransverse hdom.isWellFormed.isCoherent hdom.isNonzeroAlongAt
  apply BlowupTowerTransforms.le_vanishingIdeal_of_subset_zeroLocus hcoh
  refine hdense.trans (closure_minimal ?_ (OrderTaylor.isClosed_zeroLocus_of_isCoherent hcoh))
  rintro x ⟨hxS, hxE⟩ g hg
  exact hS hxS g ((nmPart_mem_iff_of_notMem_boundary hN hdom.isWellFormed.isCoherent hxE).mp hg)

/-- The actual old nonmonomial ideal lies in the current reduced ideal when
the preserved dense open part also misses the initial divisor. -/
theorem nonmonomialIdeal_le_currentStrictIdeal {X Y : CMfd.{u} n} {W : Set X}
    {E₀ : List (Set X)} (hn : 0 < n) (hW : IsClosed W)
    (hdom : IsInvDomain n (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    (O : Opens X) (hdense : W ⊆ closure (W ∩ (O : Set X)))
    (hEO : ∀ H ∈ E₀, Disjoint H (O : Set X)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    (hO : CentresAvoid O T) :
    (nmPart (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)).Le
      (vanishingIdeal (n := n) (strictTransform n T.proj W)) := by
  let m : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
  obtain ⟨hN, hcoh, _⟩ := pullback_eq_mul_geoTransformAlong (𝔪 := m) rfl hdom.isWellFormed.isCoherent T hT
  have hS := strictTransform_subset_cosupp_of_centresAvoid hW hdom O hdense T hT hO
  rw [MarkedIdeal.cosupp, hN, d_geoTransformAlong, cosupport_one
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg), univ_inter] at hS
  apply nmPart_le_vanishingIdeal_of_dense_zeroLocus hn hN (isInvDomain_geoTransformAlong hdom T hT) hS
  have hadm := isAdmissibleBlowupSequence_proj m _ T hT (centresOver_compl_of_centresAvoid O T hO)
  have hB := IsAdmissibleBlowupSequence.biUnion_subset hadm hdom.isWellFormed.isSNCDivisor.1
  have hD := strictTransform_subset_closure_diff T.contMDiff_proj hW (F := (O : Set X)ᶜ)
    (by simpa only [Set.sdiff_compl] using hdense)
  refine hD.trans (closure_mono ?_)
  rintro y ⟨hyS, hyO⟩
  refine ⟨hyS, fun hyE => ?_⟩
  rcases hB hyE with hyE₀ | hyF
  · obtain ⟨H, hH, hyH⟩ := mem_iUnion₂.mp hyE₀
    exact Set.disjoint_left.mp (hEO H hH) hyH (by simpa using hyO)
  · exact hyO hyF

/-- The fresh current reduced order is at most the actual finite old residual
order, the first coordinate of the general-step invariant. -/
theorem fresh_order_le_nmOrd_geoTransformAlong {X Y : CMfd.{u} n} {W : Set X}
    {E₀ : List (Set X)} (hn : 0 < n) (hW : IsClosed W)
    (hdom : IsInvDomain n (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X))
    (O : Opens X) (hdense : W ⊆ closure (W ∩ (O : Set X)))
    (hEO : ∀ H ∈ E₀, Disjoint H (O : Set X)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T)
    (hO : CentresAvoid O T) (y : Y) :
    order n univ (vanishingIdeal (n := n) (strictTransform n T.proj W)) y ≤
      (nmOrd (geoTransformAlong (⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n X) T) y : ℕ∞) := by
  let m : MarkedIdeal n X := ⟨univ, E₀, vanishingIdeal (n := n) W, 1⟩
  have hle := nonmonomialIdeal_le_currentStrictIdeal hn hW hdom O hdense hEO T hT hO
  have hdomT := isInvDomain_geoTransformAlong hdom T hT
  have hN := (pullback_eq_mul_geoTransformAlong (𝔪 := m) rfl hdom.isWellFormed.isCoherent T hT).1
  refine iSup₂_le fun q hq => ?_
  have hyN : y ∈ (geoTransformAlong m T).N := by rw [hN]; exact mem_univ _
  have hq' : y ∈ ordGe (geoTransformAlong m T) q := by
    refine ⟨hyN, ?_⟩
    rw [hN]
    exact fun g hg => hq g (hle y g hg)
  exact_mod_cast (mem_ordGe_iff hdomT.isWellFormed hdomT.isNonzeroAlongAt hyN q).mp hq'

end

end Hironaka.HironakaCurrentStrictTransformIdeal
