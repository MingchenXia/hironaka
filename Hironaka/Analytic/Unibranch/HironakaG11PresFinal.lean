import Hironaka.Analytic.Unibranch.HironakaG11PresLineReduction
import Hironaka.Resolution.HironakaG11PresPadClose
import Hironaka.Resolution.HironakaG8ClassStepBridge

/-!
# G11 from plan modules 6 and 10 for the padded lower family (repair (B'), the padded module-12 closing)

Lane G11C, run 0080 round 5.  `g11:general` (`CompactSingularCentreResolution`) was reduced along the native Hilbert–Samuel window
records to the single named input `HironakaG11PresReduction.ClassFunctorialInvariants` (`HironakaG11PresLineReduction`; native
line stability is proved).  TN `HironakaG11PresPadClose` builds these invariants by induction on the dimension for the PADDED
Step 1 operator `𝔍 ↦ stepOneInvBM (padInvSeq R |𝔍.E|) 𝔍` (lane G11B's decision r7; plan module 8 for it is proved, lane G11C r4),
from the inputs `PadFamilyInputs`: at every level `1 ≤ k ≤ N`,

* plan module 6 (lane G8B's `HironakaG8BFamily.TangentIndepStepBM`): every class-functorial lower invariant has the independence
  of the hypersurface of maximal contact (Bierstone–Milman 2008, §5 Step I.A, Cor 4.2);
* the input of plan module 10 (`HironakaG11PresPadClose.LowerExpStepBM`, lane G8C's `hExpB`, `R`-free): the boundary exponents
  below the mark of the lower ideals of class-equivalent marked ideals agree (BM08 §5 Step I.B, Theorems 6.1, 6.2).

Neither input is `HironakaG8BFamily.FamilyInputsBM` / `MaxOrderStepBM` (false for the unpadded lower family) or
`EmptyMemberIndep` (false for the general value).

* **`classFunctorialInvariants_of_padFamilyInputs`**: `PadFamilyInputs → ClassFunctorialInvariants`;
* **`compactSingularCentreResolution_of_padFamilyInputs`**: `PadFamilyInputs → CompactSingularCentreResolution`;
* `exists_endpoint_of_padFamilyInputs`: the full endpoint (modification, resolution, proper, surjective, isomorphism over the
  original regular locus, dense preimage of it, thin preimage of the singular locus, compact source) for every compact `X`;
* with plan module 6 proved by lane G8B from its exponent input: **`compactSingularCentreResolution_of_padExpInputs`**,
  `classFunctorialInvariants_of_padExpInputs`, `exists_endpoint_of_padExpInputs`, from `PadFamilyExpInputs`: the two `R`-free
  inputs `HironakaG8BFamilyTangent.TangentExpAgreeSuccBM` (two hypersurfaces of maximal contact, level `s + 1`) and
  `HironakaG11PresPadClose.LowerExpStepBM` (two class-equivalent marked ideals), both the agreement of the boundary exponents
  of lower ideals BELOW THE MARK (at or above the mark it is proved, BM08 Theorem 6.1);
* with the first input proved by lane G8 (`HironakaG8TangentExpSucc.tangentExpAgreeSuccBM`, so plan module 6 holds):
  **`compactSingularCentreResolution_of_lowerExpInputs`**, `classFunctorialInvariants_of_lowerExpInputs`,
  `exists_endpoint_of_lowerExpInputs`, from `PadFamilyLowerExpInputs` = `LowerExpStepBM` at every level (lane G8C's `hExpB`):
  **`g11:general` from ONE `R`-free statement** (the lower ideals of two class-equivalent marked ideals have the same boundary
  exponents below the mark);
* with lane G8C's reduction of `LowerExpStepBM` to its residual (`HironakaG8ClassStepBridge.lowerExpStepBM_of_residualStep`):
  `PadFamilyResidualInputs` (lane G8C's `LowerExpResidualStepBM` at every level: the same agreement only at level-`0` points
  over original members and at level-`(s+1)` points where the `ℰ`-term is divisible by the member),
  **`compactSingularCentreResolution_of_residualInputs`**, `classFunctorialInvariants_of_residualInputs`,
  `exists_endpoint_of_residualInputs`.

Blueprint: `hironaka-g11-pres-final.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG11PresFinal

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace SmoothCentreModification OriginalIntrinsicSingularLocus
open HironakaG11PresReduction HironakaG11SingularCentreModification
open Hironaka.HironakaG11PresPadClose (PadFamilyInputs exists_bmInvariant_pad PadFamilyExpInputs
  exists_bmInvariant_padExp PadFamilyLowerExpInputs exists_bmInvariant_padLowerExp)

/-- **Class-functorial resolution invariants exist, given plan modules 6 and 10 for the padded lower family.** -/
theorem classFunctorialInvariants_of_padFamilyInputs (h : PadFamilyInputs) : ClassFunctorialInvariants :=
  exists_bmInvariant_pad h

/-- **G11 from plan modules 6 and 10** (padded lower family): every compact reduced complex space has a resolution by finitely
many blowups with smooth centres in the singular loci. -/
theorem compactSingularCentreResolution_of_padFamilyInputs (h : PadFamilyInputs) : CompactSingularCentreResolution :=
  HironakaG11PresLineReduction.compactSingularCentreResolution_of_classFunctorialInvariants
    (classFunctorialInvariants_of_padFamilyInputs h)

/-- **The full G11 endpoint from plan modules 6 and 10** (padded lower family), for every compact reduced complex space. -/
theorem exists_endpoint_of_padFamilyInputs (h : PadFamilyInputs) (X : SourceReducedComplexSpace)
    (hX : CompactSpace X.obj.left) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSingularCentreModification p ∧ IsModification p ∧ Y.IsSmooth ∧ IsResolution p ∧
      Function.Surjective p.hom.left.base ∧ IsProperMap p.hom.left.base ∧
      IsIsoOver p (intrinsicRegularLocus X.obj) ∧
      Dense (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) ∧
      interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ ∧
      (CompactSpace X.obj.left → CompactSpace Y.obj.left) :=
  (compactSingularCentreResolution_of_padFamilyInputs h X hX).exists_endpoint

/-- **Class-functorial resolution invariants exist, given the two `R`-free exponent inputs below the mark.** -/
theorem classFunctorialInvariants_of_padExpInputs (h : PadFamilyExpInputs) : ClassFunctorialInvariants :=
  exists_bmInvariant_padExp h

/-- **G11 from the two `R`-free exponent inputs below the mark** (padded lower family; plan modules 6, 8 and the rest of 10
proved): every compact reduced complex space has a resolution by finitely many blowups with smooth centres in the singular
loci. -/
theorem compactSingularCentreResolution_of_padExpInputs (h : PadFamilyExpInputs) : CompactSingularCentreResolution :=
  HironakaG11PresLineReduction.compactSingularCentreResolution_of_classFunctorialInvariants
    (classFunctorialInvariants_of_padExpInputs h)

/-- **The full G11 endpoint from the two `R`-free exponent inputs below the mark**, for every compact reduced complex
space. -/
theorem exists_endpoint_of_padExpInputs (h : PadFamilyExpInputs) (X : SourceReducedComplexSpace)
    (hX : CompactSpace X.obj.left) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSingularCentreModification p ∧ IsModification p ∧ Y.IsSmooth ∧ IsResolution p ∧
      Function.Surjective p.hom.left.base ∧ IsProperMap p.hom.left.base ∧
      IsIsoOver p (intrinsicRegularLocus X.obj) ∧
      Dense (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) ∧
      interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ ∧
      (CompactSpace X.obj.left → CompactSpace Y.obj.left) :=
  (compactSingularCentreResolution_of_padExpInputs h X hX).exists_endpoint

/-- **Class-functorial resolution invariants exist, given the input of plan module 10 alone.** -/
theorem classFunctorialInvariants_of_lowerExpInputs (h : PadFamilyLowerExpInputs) : ClassFunctorialInvariants :=
  exists_bmInvariant_padLowerExp h

/-- **G11 from ONE `R`-free statement** (plan modules 6, 8, the rest of 10 and the induction proved): if, at every level, the
lower ideals of two class-equivalent marked ideals of maximal order have the same boundary exponents below the mark
(`LowerExpStepBM`, lane G8C's `hExpB`), then every compact reduced complex space has a resolution by finitely many blowups with
smooth centres in the singular loci. -/
theorem compactSingularCentreResolution_of_lowerExpInputs (h : PadFamilyLowerExpInputs) :
    CompactSingularCentreResolution :=
  HironakaG11PresLineReduction.compactSingularCentreResolution_of_classFunctorialInvariants
    (classFunctorialInvariants_of_lowerExpInputs h)

/-- **The full G11 endpoint from the input of plan module 10 alone**, for every compact reduced complex space. -/
theorem exists_endpoint_of_lowerExpInputs (h : PadFamilyLowerExpInputs) (X : SourceReducedComplexSpace)
    (hX : CompactSpace X.obj.left) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSingularCentreModification p ∧ IsModification p ∧ Y.IsSmooth ∧ IsResolution p ∧
      Function.Surjective p.hom.left.base ∧ IsProperMap p.hom.left.base ∧
      IsIsoOver p (intrinsicRegularLocus X.obj) ∧
      Dense (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) ∧
      interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ ∧
      (CompactSpace X.obj.left → CompactSpace Y.obj.left) :=
  (compactSingularCentreResolution_of_lowerExpInputs h X hX).exists_endpoint

/-- **The residual input** (lane G8C's `HironakaG8ClassStepBridge.LowerExpResidualStepBM` at every level `1 ≤ k ≤ N`, for every
ambient dimension `N`): the boundary exponents below the mark of the lower ideals of two class-equivalent marked ideals agree at
the level-`0` points whose base point lies on an original member and at the level-`(s + 1)` points where the `ℰ`-term is divisible
by the member (at all other points this is proved, `HironakaG8ClassStepResidual.lowerPairs_expAgree_of_residual`).  It is the
restriction of `PadFamilyLowerExpInputs` to these points and does not mention a resolution invariant. -/
def PadFamilyResidualInputs : Prop :=
  ∀ N k : ℕ, k < N → Hironaka.HironakaG8ClassStepBridge.LowerExpResidualStepBM N (k + 1)

/-- The input of plan module 10 from its residual (lane G8C's `lowerExpStepBM_of_residualStep`). -/
theorem padFamilyLowerExpInputs_of_residual (h : PadFamilyResidualInputs) : PadFamilyLowerExpInputs := fun N k hk =>
  Hironaka.HironakaG8ClassStepBridge.lowerExpStepBM_of_residualStep (Nat.zero_lt_of_lt hk) (h N k hk)

/-- **Class-functorial resolution invariants exist, given the residual input.** -/
theorem classFunctorialInvariants_of_residualInputs (h : PadFamilyResidualInputs) : ClassFunctorialInvariants :=
  classFunctorialInvariants_of_lowerExpInputs (padFamilyLowerExpInputs_of_residual h)

/-- **G11 from the residual input** (lane G8C's `LowerExpResidualStepBM` at every level): every compact reduced complex space
has a resolution by finitely many blowups with smooth centres in the singular loci. -/
theorem compactSingularCentreResolution_of_residualInputs (h : PadFamilyResidualInputs) :
    CompactSingularCentreResolution :=
  compactSingularCentreResolution_of_lowerExpInputs (padFamilyLowerExpInputs_of_residual h)

/-- **The full G11 endpoint from the residual input**, for every compact reduced complex space. -/
theorem exists_endpoint_of_residualInputs (h : PadFamilyResidualInputs) (X : SourceReducedComplexSpace)
    (hX : CompactSpace X.obj.left) :
    ∃ (Y : SourceReducedComplexSpace) (p : Y ⟶ X),
      IsSingularCentreModification p ∧ IsModification p ∧ Y.IsSmooth ∧ IsResolution p ∧
      Function.Surjective p.hom.left.base ∧ IsProperMap p.hom.left.base ∧
      IsIsoOver p (intrinsicRegularLocus X.obj) ∧
      Dense (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) ∧
      interior (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ ∧
      (CompactSpace X.obj.left → CompactSpace Y.obj.left) :=
  (compactSingularCentreResolution_of_residualInputs h X hX).exists_endpoint

end Hironaka.Analytic.Unibranch.HironakaG11PresFinal
