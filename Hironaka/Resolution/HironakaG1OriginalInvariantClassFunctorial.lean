import Hironaka.Resolution.HironakaG1OriginalMaxOrderClassFunctorial

/-! Class functoriality of the LITERAL ORIGINAL invariant family.
Blueprint FIRST: hironaka-g1-original-invariant-class-functorial.tex.
Native SAME marks/full boundary/class data are retained. Unequal-mark
order embeddings and weighted normal re-embedding remain separate. -/
set_option autoImplicit false
namespace Hironaka.HironakaG1OriginalInvariantClassFunctorial
noncomputable section
open BlowupTowers MarkedIdeals HironakaG8LocalHistory HironakaG11InvBMClass
  HironakaG8P1GenInv CanonicalCentres HironakaG1OriginalMaxOrderClassFunctorial

/-- The actual original general step uses its actual original maximal-order
class producer, with only the honest lower-family class induction hypothesis. -/
theorem classFunctorialFor_generalStep {n k : ℕ} (hn : 0 < n)
    {Λ : Type} [LinearOrder Λ] [WellFoundedLT Λ]
    (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n k Λ)
    (hR : ClassFunctorialFor (fun {X} A B => LocWPEquiv (X := X) A B) k R.inv) :
    ClassFunctorialFor (fun {X} A B => LocWPEquiv (X := X) A B) (k+1) (generalStep R hn).inv := by
  exact classFunctorial_genInv (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k+1) R hn) hn
    (classFunctorialMaxOrder_stepOneInvM (k := k+1) hn R hR)

/-- Every member of the actual ORIGINAL family is class functorial for
ordinary SAME native mark, full ordered boundary and actual class data. -/
theorem classFunctorialFor_invFamily {n : ℕ} (hn : 0 < n) (k : ℕ) :
    ClassFunctorialFor (fun {X} A B => LocWPEquiv (X := X) A B) k (invFamily.{0} hn k).inv := by
  induction k with
  | zero =>
      exact classFunctorialFor_ofDimZero (fun {X} A B => LocWPEquiv (X := X) A B) (0 : ℕ)
  | succ k ih =>
      exact classFunctorialFor_generalStep hn (invFamily hn k) ih

/-- The literal ORIGINAL canonical invariant has the same complete class
theorem, including ambient dimension zero and different proper carriers. -/
theorem classFunctorialFor_canonicalInvariant (n : ℕ) :
    ClassFunctorialFor (fun {X} A B => LocWPEquiv (X := X) A B) n (canonicalInvariant.{0} n).inv := by
  cases n with
  | zero =>
      exact classFunctorialFor_ofDimZero (fun {X} A B => LocWPEquiv (X := X) A B) (0 : ℕ)
  | succ n =>
      exact classFunctorialFor_invFamily (Nat.succ_pos n) (n+1)

end
end Hironaka.HironakaG1OriginalInvariantClassFunctorial
