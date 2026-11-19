import Hironaka.Resolution.HironakaG8NestedWordLocalCover

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8SortedNestedEndpoint

noncomputable section

open BlowupTowers BlowupTowerTransforms MaxLocusLocal BlowupTowerIsomorphism
  G3UniverseEmptyAwareCore HironakaSharpActualCurveComparisonRestriction

variable {n : ℕ} {X A A' B B' : CMfd.{0} n} {U V O : Opens X}

/-- The global terminal conjugation, using the literal restriction of the
larger sorting diffeomorphism to the preimage of the smaller chart. -/
def sortedEndpoint
    (T : BlowupTower (CMfd.of (n := n) V) B)
    (T' : BlowupTower (CMfd.of (n := n) V) B')
    (a : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ A')
    (b : B ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ B')
    (hb : T'.proj ∘ b = T.proj)
    (f : A ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T (nestedOpens V U))) :
    A' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T' (nestedOpens V U)) :=
  (a.symm.trans f).trans
    (openRestriction b (openPreimage T (nestedOpens V U))
      (openPreimage T' (nestedOpens V U)) (by
        ext y
        change T.proj y ∈ nestedOpens V U ↔ T'.proj (b y) ∈ nestedOpens V U
        have hp : T'.proj (b y) = T.proj y := congrFun hb y
        rw [hp]))


open MarkedIdeals HironakaG8NestedVisibleWordLift HironakaG8GeometricIndexedWord
  HironakaG8NestedWordLocalCover

local notation "BU" => CMfd.of (n := n) U
local notation "BV" => CMfd.of (n := n) V

/-- Every local word comparison is an actual restriction of one global
terminal conjugation, after undoing the large-side double flattening. -/
theorem nested_words_have_fixed_endpoint_cover
    {L L' : TowerAt BU} {R R' : TowerAt BV}
    (WL : Set BU) (WR : Set BV) (ML : MarkedIdeal n BU) (MR : MarkedIdeal n BV)
    {w v : List ℕ}
    (hL : RealizedWord (GeometricIndexedMove WL ML) w L L')
    (hR : RealizedWord (GeometricIndexedMove WR MR) v R R')
    (e : BU ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (nestedOpens V U))
    (he : ∀ x : U, (e x).val.val = x.val)
    (f : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage R.2 (nestedOpens V U)))
    (h : EmptyAwareTowerIso e L.2 (restrict (nestedOpens V U) R.2) f) :
    ∃ (a : L.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ L'.1)
      (b : R.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ R'.1)
      (_ha : L'.2.proj ∘ a = L.2.proj) (hb : R'.2.proj ∘ b = R.2.proj),
      let T := restrict (nestedOpens V U) R'.2
      let g := sortedEndpoint R.2 R'.2 a b hb f
      (∀ y, T.proj (g y) = e (L'.2.proj y)) ∧
      ∀ x : U, ∃ O : Opens X, x.val ∈ O ∧ O ≤ U ∧ O ≤ V ∧
        let H := nestedOpens (nestedOpens V U) (nestedOpens V O)
        ∃ p : CMfd.of (n := n) (nestedOpens U O)
            ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) H,
          (∀ z : nestedOpens U O, (p z).val = e z.val) ∧
          ∃ q : CMfd.of (n := n) (openPreimage L'.2 (nestedOpens U O))
              ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
              CMfd.of (n := n) (openPreimage T H),
            (∀ z, (q z).val = g z.val) ∧
            EmptyAwareTowerIso p (restrict (nestedOpens U O) L'.2) (restrict H T) q := by
  obtain ⟨a,b,ha,hb,hLocal⟩ := nested_words_local_cover WL WR ML MR hL hR e he f h
  refine ⟨a,b,ha,hb,?_,?_⟩
  · intro y
    apply Subtype.ext
    have hB (z : R.1) : R'.2.proj (b z) = R.2.proj z := congrFun hb z
    have hA (z : L.1) : L'.2.proj (a z) = L.2.proj z := congrFun ha z
    rw [proj_restrict]
    change R'.2.proj (b (f (a.symm y)).val) = (e (L'.2.proj y)).val
    rw [hB]
    have hE := congrArg Subtype.val (emptyAware_proj_comm h (a.symm y))
    rw [proj_restrict] at hE
    change R.2.proj (f (a.symm y)).val = (e (L.2.proj (a.symm y))).val at hE
    rw [hE,← hA,a.apply_symm_apply]
  · intro x
    obtain ⟨O,hx,hOU,hOV,_,_,p,hp,q,hq,hIso⟩ := hLocal x
    have hNested : nestedOpens V O ≤ nestedOpens V U := fun _ hz => hOU hz
    have hFlat := isTowerIso_restrict_nestedOpens hNested R'.2
    refine ⟨O,hx,hOU,hOV,_,?_,_,?_,G3UniverseEmptyAwareCore.trans hIso
      (G3UniverseEmptyAwareCore.symm (emptyAware_of_isTowerIso hFlat))⟩
    · intro z
      apply Subtype.ext
      apply Subtype.ext
      exact (hp z).trans (he z.val).symm
    · intro z
      apply Subtype.ext
      exact hq z

end
end Hironaka.HironakaG8SortedNestedEndpoint
