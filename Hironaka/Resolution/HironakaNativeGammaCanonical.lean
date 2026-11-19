import Hironaka.Invariant.CanonicalCentres

/-! The native monomial history is canonical for the original family whenever
the actual marked transform is monomial at each of its prefixes. -/

set_option autoImplicit false

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaNativeGammaCanonical

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MonomialPartAlong NonmonomialOrderLocal NonmonomialOrderMonomialCanonical
  MonomialStepAlong MonomialInvariant GermIdealOrder
  ResolutionInvariantOrder ResolutionInvariantSeq ResolutionInvariantDriver
  StepOneLowerDomain CanonicalCentres

variable {n : ℕ} {X : CMfd.{u} n}

/-- At every point the nonmonomial order of a monomial ideal is zero. -/
theorem nmOrd_eq_zero_of_isMonomialAlong (M : MarkedIdeal n X)
    (hM : IsMonomialAlong n M.N M.ideal M.E) (x : X) : nmOrd M x = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply nmOrd_le_of_notMem
  intro hx
  have hUnit : (nmPart M).mem x (fun _ => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const 1, fun g hg => ⟨?_, ?_⟩⟩
    · simpa only [mul_one] using hg.1
    · simpa only [mul_one] using hM x hx.1 g hg
  have hVanish := hx.2 _ hUnit
  have hOne := (vanishesToOrderOn_one_iff hx.1 (holomorphicAt_const 1)).mp hVanish
  exact one_ne_zero hOne

set_option maxHeartbeats 400000 in
/-- Every native Gamma maximum is the original-family maximum on a tower all
of whose marked transforms are monomial. The physical tower is unchanged. -/
theorem original_canonical_of_monomial_segment (hn : 0 < n) (d : ℕ)
    (M : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower M T →
      ResolutionDriver.IsCanonicalSegment M
        (fun {Y} Q => towerInvAlong M (Y := Y) Q) T →
      (∀ k : ℕ,
        let A := geoTransformAlong M (BlowupTowerSplit.head T k)
        IsMonomialAlong n A.N A.ideal A.E) →
      ResolutionInvariantSpec.IsCanonical M ((invFamily hn (d+1)).inv M) T := by
  let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {D : CMfd.{u} n}
    (S : BlowupTower A D) (z : D) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn d) J S z
  let f := fun w : WithBot Val =>
    toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot Val ⊕ₗ WithTop (Lex (ℕ × WithTop (ValTy d)))))
  have hv : OrdZeroValue M ((invFamily hn (d+1)).inv M) f := by
    intro Z Q hQ z hz hz0
    exact GeneralCanonicalTail.ordZeroValue_genInv (Y := Z) lower M Q hQ z hz hz0
  have hMono : StrictMono f := strictMono_toLex_zero_inl
  intro Y T
  induction T with
  | refl => exact fun _ _ _ => trivial
  | @step A D P C π hπ ih =>
    intro hTest hCan hM
    have hTestP := ((isGeoTestTower_step_iff M P C π hπ).mp hTest).1
    have hMP (k : ℕ) :
        let A := geoTransformAlong M (BlowupTowerSplit.head P k)
        IsMonomialAlong n A.N A.ideal A.E := hM (k+1)
    have hMonoP := hMP 0
    change (let A := geoTransformAlong M (BlowupTowerSplit.split P 0).2.1
      IsMonomialAlong n A.N A.ideal A.E) at hMonoP
    rw [StepOneEmptyPrefix.split_zero P] at hMonoP
    refine ⟨ih hTestP hCan.1 hMP, Or.inr ?_⟩
    rw [hCan.2.2]
    have hMax :=
      ResolutionInvariantExt.maxLocus_congr
        (f := ((invFamily hn (d+1)).inv M) P) (g := f ∘ towerInvAlong M P)
        (s := (geoTransformAlong M P).cosupp)
        (fun z hz => hv.apply hTestP z hz (nmOrd_eq_zero_of_isMonomialAlong _ hMonoP z))
    exact (hMax.trans (MaxLocusLocal.maxLocus_comp_strictMono hMono _ _)).symm

end
end Hironaka.HironakaNativeGammaCanonical
