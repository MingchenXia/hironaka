import Hironaka.Resolution.HironakaG8PlaneLineGerms
import Hironaka.Resolution.HironakaG8SquarefreePlaneProfile

set_option autoImplicit false
open Filter
open scoped Topology
namespace Hironaka.HironakaG8PlaneLineProducts
noncomputable section
open HolomorphicGermReducednessBridge HironakaG8PlaneLineGerms

abbrev R := HolGerm (ComplexModel 2)
local notation "𝔪" => IsLocalRing.maximalIdeal R

def lineProduct (L : List ℂ) : R := (L.map lineGerm).prod

private theorem lineGerm_dvd_lineProduct {s : ℂ} {L : List ℂ}
    (h : lineGerm s ∣ lineProduct L) : s ∈ L := by
  induction L with
  | nil => exact ((prime_lineGerm s).not_isUnit (isUnit_of_dvd_one h)).elim
  | cons t L ih =>
    change lineGerm s ∣ lineGerm t * lineProduct L at h
    rcases (prime_lineGerm s).dvd_mul.mp h with ht | hL
    · exact List.mem_cons.mpr (Or.inl (by
        by_contra hne
        exact lineGerm_not_dvd (Ne.symm hne) ht))
    · exact List.mem_cons.mpr (Or.inr (ih hL))

theorem squarefree_lineProduct (L : List ℂ) (hL : L.Nodup) :
    Squarefree (lineProduct L) := by
  let := ActualHolomorphicGermFactoriality.uniqueFactorizationMonoid_holGerm_euclidean 2
  induction L with
  | nil => exact squarefree_one
  | cons s L ih =>
    obtain ⟨hs,hL⟩ := List.nodup_cons.mp hL
    change Squarefree (lineGerm s * lineProduct L)
    refine squarefree_mul_iff.mpr ⟨?_,(prime_lineGerm s).squarefree,ih hL⟩
    intro a ha hb
    obtain ⟨u,hu⟩ := ha
    rcases (prime_lineGerm s).irreducible.isUnit_or_isUnit hu with h | h
    · exact h
    · obtain ⟨v,rfl⟩ := h
      have hd : a * (v : R) ∣ a := ⟨↑v⁻¹,by simp [mul_assoc]⟩
      rw [← hu] at hd
      exact (hs (lineGerm_dvd_lineProduct (dvd_trans hd hb))).elim


open HironakaHolomorphicPointJets HironakaActualPrincipalJetMultiplication

theorem lineGerm_orderOne (s : ℂ) :
    lineGerm s ∈ 𝔪 ^ 1 ∧ lineGerm s ∉ 𝔪 ^ 2 := by
  constructor
  · rw [pow_one]
    apply (HolGerm.mem_maximalIdeal_iff _).mpr
    rw [lineGerm, HolGerm.eval_mk, map_zero]
  · intro h
    have hzero := (mem_maximalIdeal_pow_iff_iteratedFDeriv
      (Eventually.of_forall fun _ => (lineLinear s).differentiableAt) 2).mp h 1 (by decide)
    have hv := congrArg (fun g => g (fun _ => EuclideanSpace.single (1 : Fin 2) (1 : ℂ))) hzero
    simp at hv
    change s * (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) 0 +
      (EuclideanSpace.single (1 : Fin 2) (1 : ℂ)) 1 = 0 at hv
    simp at hv

theorem lineProduct_order (L : List ℂ) :
    lineProduct L ∈ 𝔪 ^ L.length ∧ lineProduct L ∉ 𝔪 ^ (L.length + 1) := by
  induction L with
  | nil =>
    change (1 : R) ∈ 𝔪 ^ 0 ∧ (1 : R) ∉ 𝔪 ^ (0+1)
    refine ⟨by simp, ?_⟩
    rw [pow_one]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
  | cons s L ih =>
    obtain ⟨hs,hs'⟩ := lineGerm_orderOne s
    exact ⟨(actual_mul_mem_maximal_pow_iff _ _ 1 L.length hs hs').mpr ih.1,
      fun h => ih.2 ((actual_mul_mem_maximal_pow_iff _ _ 1 (L.length+1) hs hs').mp h)⟩

open Hironaka.HolomorphicIdealSheaves OkaRelationSheaf
  HironakaHolomorphicJetChartInvariance HironakaG8SquarefreePlaneProfile

def lineProductFunction : List ℂ → ComplexModel 2 → ℂ
  | [] => 1
  | s :: L => fun z => lineLinear s z * lineProductFunction L z

private theorem lineProductFunction_hol (L : List ℂ) :
    HolAt (lineProductFunction L) 0 := by
  induction L with
  | nil => exact (Eventually.of_forall fun _ => differentiableAt_const (1 : ℂ))
  | cons s L ih =>
    have hs : HolAt (lineLinear s : ComplexModel 2 → ℂ) 0 :=
      Eventually.of_forall fun _ => (lineLinear s).differentiableAt
    exact hs.mul ih

private theorem lineProductFunction_mk (L : List ℂ) :
    HolGerm.mk (lineProductFunction L) (lineProductFunction_hol L) = lineProduct L := by
  induction L with
  | nil => exact HolGerm.mk_one
  | cons s L ih =>
    change HolGerm.mk (fun z => lineLinear s z * lineProductFunction L z) _ =
      lineGerm s * lineProduct L
    rw [HolGerm.mk_mul _ _ (Eventually.of_forall fun _ => (lineLinear s).differentiableAt) (lineProductFunction_hol L), ih]
    rfl

def planeLineArrangement (r : ℕ) : Set (ComplexModel 2) :=
  {z | lineProductFunction ((List.range r).map (fun i : ℕ => (i : ℂ))) z = 0}

theorem planeLineArrangement_profile (r l : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := 2) (planeLineArrangement r)) 0 l =
      Nat.choose (2+l) 2 - (if r ≤ l then Nat.choose (2+(l-r)) 2 else 0) := by
  let L := (List.range r).map (fun i : ℕ => (i : ℂ))
  have hL : L.Nodup := List.nodup_range.map (fun a b h => by exact_mod_cast h)
  have hlen : L.length = r := by simp [L]
  have hmk := lineProductFunction_mk L
  obtain ⟨hOrder,hOrder'⟩ := lineProduct_order L
  rw [hlen,← hmk] at hOrder hOrder'
  have hne : HolGerm.mk (lineProductFunction L) (lineProductFunction_hol L) ≠ 0 :=
    fun h => hOrder' (h.symm ▸ Ideal.zero_mem _)
  have hsf : Squarefree (HolGerm.mk (lineProductFunction L) (lineProductFunction_hol L)) :=
    hmk ▸ squarefree_lineProduct L hL
  have h := origin_profile_of_squarefree_plane_equation
    (lineProductFunction L) (lineProductFunction_hol L) hsf hne l
  rw [actualGermOrder_unique _ hne r hOrder hOrder'] at h
  exact h

theorem planeLineArrangement_profile_strictMono :
    StrictMono (fun r => toLex
      (hilbertSamuelAt (vanishingIdeal (n := 2) (planeLineArrangement r)) 0)) := by
  intro r s hrs
  refine ⟨r,?_,?_⟩
  · intro l hl
    change hilbertSamuelAt (vanishingIdeal (n := 2) (planeLineArrangement r)) 0 l =
      hilbertSamuelAt (vanishingIdeal (n := 2) (planeLineArrangement s)) 0 l
    rw [planeLineArrangement_profile,planeLineArrangement_profile,
      if_neg (Nat.not_le_of_lt hl), if_neg (Nat.not_le_of_lt (hl.trans hrs))]
  · change hilbertSamuelAt (vanishingIdeal (n := 2) (planeLineArrangement r)) 0 r <
      hilbertSamuelAt (vanishingIdeal (n := 2) (planeLineArrangement s)) 0 r
    rw [planeLineArrangement_profile,planeLineArrangement_profile,
      if_pos (le_refl r), if_neg (Nat.not_le_of_lt hrs), Nat.sub_self, Nat.add_zero, Nat.sub_zero]
    have hp : 0 < Nat.choose (2+r) 2 := Nat.choose_pos (by omega)
    norm_num
    omega

end
end Hironaka.HironakaG8PlaneLineProducts
