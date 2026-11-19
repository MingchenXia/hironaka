import Hironaka.Resolution.HironakaG8PhysicalChartOccupiedLifts
import Hironaka.Resolution.HironakaG3UniverseEmptyAwareOpenRestriction

/-! Consecutive genuine nested comparisons suffice on a monotone chain. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8ConsecutiveNestedReorderings

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaG3EmptyAwareHistory G3UniverseEmptyAwareOpenRestriction HironakaSharpActualCurveComparisonRestriction
  HironakaBaseChange BlowupTowerIsomorphism

variable {n : ℕ} {X : CMfd.{0} n} {U V W : Opens X} {A B C : CMfd.{0} n}

/-- Literal comparison over the underlying identity on the smaller base. -/
def NestedGeometry
    (S : BlowupTower (CMfd.of (n := n) U) A) (T : BlowupTower (CMfd.of (n := n) V) B) : Prop :=
  ∃ e : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens V U),
    (∀ x : U, (e x).val.val = x.val) ∧
    ∃ f : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T (nestedOpens V U)),
      EmptyAwareTowerIso e S (restrict (nestedOpens V U) T) f

private theorem full_restriction
    {A B : CMfd.{0} n} (T : BlowupTower A B) (H : Opens A) (hH : ∀ x : A, x ∈ H) :
    ∃ e : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) H,
      (∀ x : A, (e x).val = x) ∧
      ∃ f : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T H),
        (∀ y : B, (f y).val = y) ∧ IsTowerIso e T (restrict H T) f := by
  let mk (D : CMfd.{0} n) (O : Opens D) (ho : ∀ x : D, x ∈ O) :
      D ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) O :=
    { toFun := fun x => ⟨x,ho x⟩, invFun := Subtype.val
      left_inv := fun _ => rfl, right_inv := fun _ => rfl
      contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk contMDiff_id ho
      contMDiff_invFun := contMDiff_subtype_val }
  induction T with
  | refl => exact ⟨mk A H hH,fun _ => rfl,mk A H hH,fun _ => rfl,.refl⟩
  | @step D E T L π hπ ih =>
    obtain ⟨e,he,f,hf,hIso⟩ := ih
    let O := openPreimage (.step T L π hπ) H
    refine ⟨e,he,mk E O (fun y => hH (T.proj (π y))),fun _ => rfl,
      IsTowerIso.step hIso _ _ _ ?_ ?_⟩
    · intro y
      apply Subtype.ext
      exact (hf (π y)).symm
    · ext y
      change (f y).val ∈ L ↔ y ∈ L
      rw [hf]

theorem NestedGeometry.refl (S : BlowupTower (CMfd.of (n := n) U) A) :
    NestedGeometry S S := by
  obtain ⟨e,he,f,_,h⟩ := full_restriction S (nestedOpens U U) (fun x => x.property)
  exact ⟨e,fun x => congrArg Subtype.val (he x),f,emptyAware_of_isTowerIso h⟩

theorem NestedGeometry.trans
    {S : BlowupTower (CMfd.of (n := n) U) A}
    {T : BlowupTower (CMfd.of (n := n) V) B}
    {R : BlowupTower (CMfd.of (n := n) W) C}
    (hUV : U ≤ V) (hST : NestedGeometry S T) (hTR : NestedGeometry T R) :
    NestedGeometry S R := by
  obtain ⟨e,he,f,hf⟩ := hST
  obtain ⟨g,hg,k,hk⟩ := hTR
  let V' := nestedOpens W V
  let U' := nestedOpens W U
  let H := nestedOpens V' U'
  have hU'V' : U' ≤ V' := fun _ hx => hUV hx
  have hH : preimageOpen g H = nestedOpens V U := by
    ext x
    change (g x).val.val ∈ U ↔ x.val ∈ U
    rw [hg]
  let Geometry (O : Opens V) : Prop :=
    ∃ a : CMfd.of (n := n) O ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) H,
      (∀ x : O, (a x).val.val.val = x.val.val) ∧
      ∃ b, EmptyAwareTowerIso a (restrict O T) (restrict H (restrict V' R)) b
  have hk' : Geometry (preimageOpen g H) :=
    ⟨_,fun x => hg x.val,_,emptyAware_open_restriction hk H⟩
  obtain ⟨a,ha,b,hb⟩ := hH ▸ hk'
  have hFlatten := emptyAware_of_isTowerIso (isTowerIso_restrict_nestedOpens hU'V' R)
  have h := G3UniverseEmptyAwareCore.trans hf (G3UniverseEmptyAwareCore.trans hb hFlatten)
  refine ⟨_,?_,_,h⟩
  intro x
  change (a (e x)).val.val.val = x.val
  exact (ha (e x)).trans (he x)

/-- A natural chain needs consecutive genuine comparisons only. -/
theorem nestedGeometry_of_succ (U : ℕ → Opens X) (hMono : Monotone U)
    {Y : ℕ → CMfd.{0} n} (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (hSucc : ∀ i, NestedGeometry (T i) (T (i+1))) :
    ∀ i j, i ≤ j → NestedGeometry (T i) (T j) := by
  intro i j hij
  induction hij with
  | refl => exact NestedGeometry.refl (T i)
  | @step j hij ih => exact ih.trans (hMono hij) (hSucc j)

/-- Consecutive comparisons supply the exact intersection-open premise of
the nested rank-reordering endpoint, before any rank readback. -/
theorem intersection_geometry_of_succ (U : ℕ → Opens X) (hMono : Monotone U)
    {Y : ℕ → CMfd.{0} n} (T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i))
    (hSucc : ∀ i, NestedGeometry (T i) (T (i+1))) :
    ∀ i j, i ≤ j →
      ∃ e : CMfd.of (n := n) (U i) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (nestedOpens (U j) (U i ⊓ U j)),
        (∀ x : U i, (e x).val.val = x.val) ∧
        ∃ f : Y i ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
            CMfd.of (n := n) (openPreimage (T j) (nestedOpens (U j) (U i ⊓ U j))),
          EmptyAwareTowerIso e (T i) (restrict (nestedOpens (U j) (U i ⊓ U j)) (T j)) f := by
  intro i j hij
  rw [inf_eq_left.mpr (hMono hij)]
  exact nestedGeometry_of_succ U hMono T hSucc i j hij

end Hironaka.HironakaG8ConsecutiveNestedReorderings
