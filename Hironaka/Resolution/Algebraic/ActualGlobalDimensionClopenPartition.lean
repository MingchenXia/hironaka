import Hironaka.Resolution.Algebraic.ActualGlobalDimensionIdealAffineComparison
import Hironaka.Scheme.BlowUp.Transform.WeakTransform
import Hironaka.Scheme.BlowUpSequence.PullbackInduced

/-!
# Canonical clopen pieces of the actual global dimension-separation blowup

Source-first proof: `actual-global-dimension-clopen-partition-20261102.tex`.
The actual complementary ideals, exceptional divisor and invertible colon
division produce the global partition.  Affine identification and purity
of its actual pieces remain separate consumers.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalDimensionClopenPartition

noncomputable section
open ActualIntrinsicComponentDimensions

variable (X : Scheme.{u}) [NoetherianSpace X]

def complementaryIdeal (d : WithBot ℕ∞) : X.IdealSheafData :=
  vanishingIdeal (ActualGlobalDimensionSeparationIdeal.complementaryClosed X d)

theorem complementaryIdeal_mul_eq_bot [IsReduced X] {d e : WithBot ℕ∞} (hde : d ≠ e) :
    complementaryIdeal X d * complementaryIdeal X e = ⊥ := by
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  rw [support_mul]
  change ActualGlobalDimensionSeparationIdeal.complementaryClosed X d ⊔
    ActualGlobalDimensionSeparationIdeal.complementaryClosed X e = ⊤
  apply top_le_iff.mp
  intro x _
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  change x ∈ ActualGlobalDimensionSeparationIdeal.complementaryClosed X d ∨
    x ∈ ActualGlobalDimensionSeparationIdeal.complementaryClosed X e
  by_cases hd : componentDimension C = d
  · right
    apply (ActualGlobalDimensionSeparationIdeal.mem_complementaryClosed X e x).mpr
    exact ⟨C, fun he => hde (hd.symm.trans he), mem_irreducibleComponent⟩
  · left
    exact (ActualGlobalDimensionSeparationIdeal.mem_complementaryClosed X d x).mpr
      ⟨C, hd, mem_irreducibleComponent⟩

abbrev separationSpace : Scheme.{u} := (ActualGlobalDimensionSeparationIdeal.separationIdeal X).blowUp

abbrev separationProjection : separationSpace X ⟶ X :=
  (ActualGlobalDimensionSeparationIdeal.separationIdeal X).blowUpπ

def exceptionalIdeal : (separationSpace X).IdealSheafData :=
  (ActualGlobalDimensionSeparationIdeal.separationIdeal X).comap (separationProjection X)

theorem exceptionalIdeal_isInvertible : (exceptionalIdeal X).IsInvertible :=
  blowUp.isInvertible_comap_π _

def normalizedIdeal (d : dimensionIndex X) : (separationSpace X).IdealSheafData :=
  ((complementaryIdeal X d.val).comap (separationProjection X)).colon (exceptionalIdeal X)

theorem exceptional_mul_normalized (d : dimensionIndex X) :
    exceptionalIdeal X * normalizedIdeal X d =
      (complementaryIdeal X d.val).comap (separationProjection X) := by
  have hle : complementaryIdeal X d.val ≤ ActualGlobalDimensionSeparationIdeal.separationIdeal X :=
    le_iSup_of_le d.val le_rfl
  have hpull := comap_mono (separationProjection X) hle
  have hdiv : exceptionalIdeal X ^ 1 ∣
      (complementaryIdeal X d.val).comap (separationProjection X) :=
    pow_dvd_of_le_pow_of_isInvertible (exceptionalIdeal_isInvertible X)
      (by simpa only [pow_one, exceptionalIdeal] using hpull)
  simpa only [pow_one, normalizedIdeal] using pow_mul_colon_of_dvd
    ((complementaryIdeal X d.val).comap (separationProjection X)) (exceptionalIdeal X) 1 hdiv

private theorem numerator_iSup [IsReduced X] :
    (⨆ d : dimensionIndex X, (complementaryIdeal X d.val).comap (separationProjection X)) =
      exceptionalIdeal X := by
  rw [← comap_iSup]
  congr 1
  exact (ActualGlobalDimensionSeparationIdeal.separationIdeal_eq_finite_sum X).symm

theorem normalizedIdeal_iSup [IsReduced X] :
    (⨆ d : dimensionIndex X, normalizedIdeal X d) = ⊤ := by
  have hmul : exceptionalIdeal X * (⨆ d : dimensionIndex X, normalizedIdeal X d) =
      exceptionalIdeal X := by
    apply le_antisymm
    · exact mul_le_self_left _ _
    · calc
        exceptionalIdeal X =
            ⨆ d : dimensionIndex X, (complementaryIdeal X d.val).comap
              (separationProjection X) := (numerator_iSup X).symm
        _ ≤ exceptionalIdeal X * (⨆ d : dimensionIndex X, normalizedIdeal X d) := by
          refine iSup_le fun d => ?_
          rw [← exceptional_mul_normalized X d]
          intro U
          change (exceptionalIdeal X).ideal U * (normalizedIdeal X d).ideal U ≤
            (exceptionalIdeal X).ideal U * (⨆ e : dimensionIndex X, normalizedIdeal X e).ideal U
          exact Ideal.mul_mono_right ((le_iSup (normalizedIdeal X) d) U)
  have hsum := colon_pow_eq_of_mul_eq (exceptionalIdeal X)
    (exceptionalIdeal_isInvertible X) 1 (⨆ d : dimensionIndex X, normalizedIdeal X d)
      (by simpa only [pow_one] using hmul)
  have htop := colon_pow_eq_of_mul_eq (exceptionalIdeal X)
    (exceptionalIdeal_isInvertible X) 1 ⊤ (by rw [pow_one, mul_top])
  exact hsum.symm.trans htop

theorem normalizedIdeal_mul_eq_bot [IsReduced X] {d e : dimensionIndex X} (hde : d ≠ e) :
    normalizedIdeal X d * normalizedIdeal X e = ⊥ := by
  have hval : d.val ≠ e.val := fun h => hde (Subtype.ext h)
  have hmul : exceptionalIdeal X ^ 2 * (normalizedIdeal X d * normalizedIdeal X e) = ⊥ := by
    calc
      _ = (exceptionalIdeal X * normalizedIdeal X d) *
          (exceptionalIdeal X * normalizedIdeal X e) := by rw [pow_two]; ac_rfl
      _ = ((complementaryIdeal X d.val).comap (separationProjection X)) *
          ((complementaryIdeal X e.val).comap (separationProjection X)) := by
        rw [exceptional_mul_normalized, exceptional_mul_normalized]
      _ = (complementaryIdeal X d.val * complementaryIdeal X e.val).comap
          (separationProjection X) := (comap_mul _ _ _).symm
      _ = ⊥ := by rw [complementaryIdeal_mul_eq_bot X hval, comap_bot]
  have hcolon := colon_pow_eq_of_mul_eq (⊥ : (separationSpace X).IdealSheafData)
    (exceptionalIdeal_isInvertible X) 2 (normalizedIdeal X d * normalizedIdeal X e) hmul
  rw [colon_pow_bot_of_isInvertible (exceptionalIdeal_isInvertible X)] at hcolon
  exact hcolon.symm

theorem normalizedIdeal_flat_pullback {Y : Scheme.{u}} (q : Y ⟶ separationSpace X) [Flat q]
    (d : dimensionIndex X) :
    (normalizedIdeal X d).comap q =
      (((complementaryIdeal X d.val).comap (separationProjection X)).comap q).colon
        ((exceptionalIdeal X).comap q) :=
  colon_comap_of_flat q _ (exceptionalIdeal_isInvertible X)

def dimensionPartOpen (d : dimensionIndex X) : (separationSpace X).Opens :=
  ⟨((normalizedIdeal X d).support : Set (separationSpace X))ᶜ,
    (normalizedIdeal X d).support.isClosed.isOpen_compl⟩

theorem dimensionPartOpen_cover [IsReduced X] :
    (⨆ d : dimensionIndex X, dimensionPartOpen X d) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  by_contra hx
  have hs : x ∈ (⨅ d : dimensionIndex X, (normalizedIdeal X d).support) := by
    apply Closeds.mem_iInf.mpr
    intro d
    by_contra hd
    exact hx (Opens.mem_iSup.mpr ⟨d, hd⟩)
  rw [← support_iSup, normalizedIdeal_iSup, support_top] at hs
  exact hs

theorem dimensionPartOpen_disjoint [IsReduced X] :
    Pairwise (fun d e : dimensionIndex X =>
      Disjoint (dimensionPartOpen X d : Set (separationSpace X))
        (dimensionPartOpen X e : Set (separationSpace X))) := by
  intro d e hde
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hs : (normalizedIdeal X d).support ⊔ (normalizedIdeal X e).support = ⊤ := by
    rw [← support_mul, normalizedIdeal_mul_eq_bot X hde, support_bot]
  have hxs : x ∈ (normalizedIdeal X d).support ⊔ (normalizedIdeal X e).support := by
    rw [hs]
    trivial
  change x ∈ (normalizedIdeal X d).support ∨ x ∈ (normalizedIdeal X e).support at hxs
  obtain hd | he := hxs
  · exact hx hd
  · exact hy he

theorem dimensionPartOpen_isClosed [IsReduced X] (d : dimensionIndex X) :
    IsClosed (dimensionPartOpen X d : Set (separationSpace X)) := by
  have hComp : (dimensionPartOpen X d : Set (separationSpace X))ᶜ =
      ⋃ e : dimensionIndex X, ⋃ (_ : e ≠ d),
        (dimensionPartOpen X e : Set (separationSpace X)) := by
    ext x
    constructor
    · intro hx
      have hcov : x ∈ (⨆ e : dimensionIndex X, dimensionPartOpen X e) := by
        rw [dimensionPartOpen_cover]
        trivial
      obtain ⟨e, he⟩ := Opens.mem_iSup.mp hcov
      refine Set.mem_iUnion₂.mpr ⟨e, ?_, he⟩
      intro hed
      subst e
      exact hx he
    · intro hx hd
      obtain ⟨e, hed, he⟩ := Set.mem_iUnion₂.mp hx
      exact Set.disjoint_left.mp (dimensionPartOpen_disjoint X hed.symm) hd he
  apply isOpen_compl_iff.mp
  rw [hComp]
  exact isOpen_iUnion fun e => isOpen_iUnion fun _ => (dimensionPartOpen X e).isOpen

end
end Hironaka.Resolution.Algebraic.ActualGlobalDimensionClopenPartition
