import Hironaka.Resolution.HironakaG3UniverseEmptyAwareOpenRestriction
import Hironaka.Resolution.HironakaSharpActualCurveComparisonRestriction

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8FixedNestedOpenReadback

open BlowupTowers BlowupTowerTransforms MaxLocusLocal
  G3UniverseEmptyAwareCore G3UniverseEmptyAwareOpenRestriction
  HironakaSharpActualCurveComparisonRestriction

variable {n : ℕ} {X A B A' B' : CMfd.{0} n} {U V O : Opens X}

/-- Restrict the fixed comparison and flatten on the large side. The resulting
terminal comparison is the same original point map on the smaller subopen. -/
theorem restrict_fixed_nested
    (S : BlowupTower (CMfd.of (n := n) U) A)
    (T : BlowupTower (CMfd.of (n := n) V) B) (hOU : O ≤ U)
    (e : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens V U))
    (he : ∀ x : U, (e x).val.val = x.val)
    (f : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T (nestedOpens V U)))
    (h : EmptyAwareTowerIso e S (restrict (nestedOpens V U) T) f) :
    ∃ g : CMfd.of (n := n) (nestedOpens U O) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (nestedOpens V O),
      (∀ x : nestedOpens U O, (g x).val.val = x.val.val) ∧
      ∃ k : CMfd.of (n := n) (openPreimage S (nestedOpens U O))
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T (nestedOpens V O)),
        (∀ y, (k y).val = (f y.val).val) ∧
        EmptyAwareTowerIso g (restrict (nestedOpens U O) S) (restrict (nestedOpens V O) T) k := by
  let V' := nestedOpens V U
  let O' := nestedOpens V O
  let H := nestedOpens V' O'
  have hOV' : O' ≤ V' := fun _ hx => hOU hx
  have hH : preimageOpen e H = nestedOpens U O := by
    ext x
    change (e x).val.val ∈ O ↔ x.val ∈ O
    rw [he]
  let Restricted (Q : Opens (CMfd.of (n := n) U)) : Prop :=
    ∃ a : CMfd.of (n := n) Q ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) H,
      (∀ x : Q, (a x).val.val.val = x.val.val) ∧
      ∃ b : CMfd.of (n := n) (openPreimage S Q)
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage (restrict V' T) H),
        (∀ y, (b y).val.val = (f y.val).val) ∧
        EmptyAwareTowerIso a (restrict Q S) (restrict H (restrict V' T)) b
  have hR : Restricted (preimageOpen e H) :=
    ⟨_,fun x => he x.val,_,fun _ => rfl,emptyAware_open_restriction h H⟩
  obtain ⟨a,ha,b,hb,hbIso⟩ := hH ▸ hR
  exact ⟨_,ha,_,hb,G3UniverseEmptyAwareCore.trans hbIso
    (emptyAware_of_isTowerIso (isTowerIso_restrict_nestedOpens hOV' T))⟩


/-- Transport the fixed nested comparison between the two actual output
restrictions by their chosen sorted maps. -/
theorem sorted_nested_common_subopen
    (S : BlowupTower (CMfd.of (n := n) U) A)
    (T : BlowupTower (CMfd.of (n := n) V) B)
    (S' : BlowupTower (CMfd.of (n := n) U) A')
    (T' : BlowupTower (CMfd.of (n := n) V) B') (hOU : O ≤ U)
    (e : CMfd.of (n := n) U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens V U))
    (he : ∀ x : U, (e x).val.val = x.val)
    (f : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T (nestedOpens V U)))
    (h : EmptyAwareTowerIso e S (restrict (nestedOpens V U) T) f)
    (a : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A')
    (b : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B')
    (aO : CMfd.of (n := n) (openPreimage S (nestedOpens U O))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage S' (nestedOpens U O)))
    (bO : CMfd.of (n := n) (openPreimage T (nestedOpens V O))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T' (nestedOpens V O)))
    (ha : ∀ y, (aO y).val = a y.val) (hb : ∀ y, (bO y).val = b y.val)
    (hA : EmptyAwareTowerIso (Diffeomorph.refl _ _ _)
      (restrict (nestedOpens U O) S) (restrict (nestedOpens U O) S') aO)
    (hB : EmptyAwareTowerIso (Diffeomorph.refl _ _ _)
      (restrict (nestedOpens V O) T) (restrict (nestedOpens V O) T') bO) :
    ∃ g : CMfd.of (n := n) (nestedOpens U O) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (nestedOpens V O),
      (∀ x : nestedOpens U O, (g x).val.val = x.val.val) ∧
      ∃ k : CMfd.of (n := n) (openPreimage S' (nestedOpens U O))
          ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T' (nestedOpens V O)),
        (∀ y, (k y).val = b (f (a.symm y.val)).val) ∧
        EmptyAwareTowerIso g (restrict (nestedOpens U O) S') (restrict (nestedOpens V O) T') k := by
  obtain ⟨g,hg,k,hk,hK⟩ := restrict_fixed_nested S T hOU e he f h
  let G := ((Diffeomorph.refl _ _ _).symm.trans g).trans (Diffeomorph.refl _ _ _)
  refine ⟨G,hg,(aO.symm.trans k).trans bO,?_,?_⟩
  · intro y
    have hVal : (aO.symm y).val = a.symm y.val := by
      apply a.injective
      change a (aO.symm y).val = a (a.symm y.val)
      rw [a.apply_symm_apply, ← ha (aO.symm y), aO.apply_symm_apply]
    change (bO (k (aO.symm y))).val = _
    rw [hb,hk,hVal]
  · exact G3UniverseEmptyAwareCore.trans (G3UniverseEmptyAwareCore.trans
      (G3UniverseEmptyAwareCore.symm hA) hK) hB

end Hironaka.HironakaG8FixedNestedOpenReadback
