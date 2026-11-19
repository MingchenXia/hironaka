import Hironaka.Resolution.HironakaG11InvBMCanonicalTail

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Independence of the hypersurface of maximal contact for Bierstone--Milman's lower ideals (repair (B'), plan modules 6/8)

Blueprint: `hironaka-g11-inv-bm-max-order.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §1 modules 6, 8.
Source: Bierstone--Milman 2008, §5 Step I.A ("the marked ideals `𝒞_U(ℐ)` and `𝒞_V(ℐ)` defined in two overlapping charts `U` and
`V` are equivalent in `U ∩ V` ...; therefore, by functoriality in dimension `n − 1`, their resolution sequences are the same over
`U ∩ V`"), Corollary 4.2 and Step I.B.

The anchor change `HironakaG11InvBMCanonicalTail.AnchorChangeBM 𝔍 R` compares the lower ideals of two anchors, each formed with
the tangent direction chosen at its base point.  The properties (4'), (5), (6), (7) of the Step 1 value compare lower ideals
formed with the tangent direction chosen for one marked ideal with the transport of the one chosen for another (a restriction, a
biholomorphic copy, a representative, a transform along empty centres).  Both are instances of one property of the
lower-dimensional invariant `R`: **the values of `R` on Bierstone--Milman's lower ideals do not depend on the hypersurface of
maximal contact** (`TangentIndepBM 𝔍 R`), stated for arbitrary tangent directions `w₁`, `w₂` on arbitrary opens.  It is TRUE for
class-functorial `R` (BM08 Step I.A: on the overlap both lower ideals are equivalent to `(I_∅)_{T₀}` there, with the same
`ℰ`-term, the same mark, the same born divisor, carriers of the same dimension and the same boundary exponents); it is the
statement plan module 6 is to prove from lane G8's port P4.

* `lowerIdealWBM 𝔍 s w T₀ S`: the lower ideal with an explicit tangent function `w` and member list `S`;
  `lowerIdealBM_eq_lowerIdealWBM` (`rfl` per level);
* **`TangentIndepBM 𝔍 R`** (definition, a property of `R`), **`anchorChangeBM_of_tangentIndepBM`**;
* the transport of the lower ideals: `contactCoeffBM_isTowerIso` (isomorphisms of towers over a biholomorphism),
  `contactCoeffBM_restrict` (restriction to an open set of the base).

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMTangentIndep

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.StepOneValue Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong Hironaka.BlowupTowerIsomorphism
  Hironaka.HironakaG11InvBMMask Hironaka.HironakaG11InvBMLower
  Hironaka.HironakaG11InvBMCanonicalTail Hironaka.MarkedIdealBiholomorphism
open Hironaka.HomogenizedGlueingTower (strictAlong strictAlong_restrict)
open Hironaka.RestrictedIdealExtension (sumIdeal)
open Hironaka.CoefficientIdealRestriction (withN)
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

/-! ### Lower ideals with an explicit tangent function -/

section Defs

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **Bierstone--Milman's lower ideal for an explicit tangent function `w` and member list `S`**: the coefficient ideal on
`V(w)` transformed along `T₀` at level `0`; at the levels `s + 1` its same-mark sum with the `ℰ`-term of `S`. -/
def lowerIdealWBM (s : ℕ) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (S : List (Set Y₀)) :
    MarkedIdeal n Y₀ :=
  match s with
  | 0 => contactCoeffBM 𝔍 w T₀
  | _ + 1 =>
    { N := (contactCoeffBM 𝔍 w T₀).N
      E := (contactCoeffBM 𝔍 w T₀).E
      ideal := sumIdeal (contactCoeffBM 𝔍 w T₀).ideal (exceptionalTermBM S (contactCoeffBM 𝔍 w T₀).d)
      d := (contactCoeffBM 𝔍 w T₀).d }

/-- The lower ideals of the family are the instances at the chosen tangent direction and the members through the anchor. -/
theorem lowerIdealBM_eq_lowerIdealWBM (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    lowerIdealBM 𝔍 s T₀ y₀ =
      lowerIdealWBM 𝔍 s (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀ (throughMembers 𝔍 T₀ y₀) := by
  cases s <;> rfl

/-- **The ideal and the mark of the lower ideal do not depend on the tangent function** (only the carrier does). -/
theorem lowerIdealWBM_ideal_eq (s : ℕ) (w w' : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (S : List (Set Y₀)) :
    (lowerIdealWBM 𝔍 s w T₀ S).ideal = (lowerIdealWBM 𝔍 s w' T₀ S).ideal ∧
      (lowerIdealWBM 𝔍 s w T₀ S).d = (lowerIdealWBM 𝔍 s w' T₀ S).d ∧
      (lowerIdealWBM 𝔍 s w T₀ S).E = (lowerIdealWBM 𝔍 s w' T₀ S).E := by
  cases s <;> exact ⟨rfl, rfl, rfl⟩

/-- **The lower ideal for any tangent function has a coherent ideal** (the members through an anchor; `T₀` a multiple test
blow-up of `J̄`, `0 < n`). -/
theorem isCoherent_lowerIdealWBM (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n) (s : ℕ) (w : X → ℂ)
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) (a : Y₀) :
    (lowerIdealWBM 𝔍 s w T₀ (throughMembers 𝔍 T₀ a)).ideal.IsCoherent := by
  rw [(lowerIdealWBM_ideal_eq 𝔍 s w (tangentChoice 𝔍 (T₀.proj a)).2 T₀ _).1, ← lowerIdealBM_eq_lowerIdealWBM]
  exact HironakaG11InvBMRebase.isCoherent_lowerIdealBM 𝔍 h𝔍 hd hn T₀ hT₀ a s

end Defs

/-! ### Independence of the hypersurface of maximal contact -/

section Indep

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  (R : ResolutionInvariant.{u, v} n (k - 1) Λ)

/-- **Independence of the hypersurface of maximal contact** (a property of the lower-dimensional invariant `R`; BM08 §5
Step I.A): along every multiple test blow-up `T₀ T₁` of `J̄`, for an anchor `a` of the cosupport at `T₀` of level `s`, two
tangent directions `w₁`, `w₂` of `(𝔍.ideal|_N, d)` on `U₁`, `U₂` and opens `O₁`, `O₂` of the stage over them, if the restrictions
to `O₁`, `O₂` of the lower ideals formed with `w₁`, `w₂` and the original members through `a` lie in the domain of `R` with
`T₁|_{O₁}`, `T₁|_{O₂}` canonical segments of them, then at every common point of the cosupport of the second their values
agree. -/
def TangentIndepBM : Prop :=
  ∀ {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y), IsGeoTestTower (barMarked 𝔍) (T₀.append T₁) →
    ∀ (s : ℕ) (a : Y₀), a ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp → level 𝔍 T₀ a = s →
    ∀ (U₁ U₂ : Set X) (w₁ w₂ : X → ℂ), IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U₁ w₁ →
      IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U₂ w₂ →
    ∀ (O₁ O₂ : Opens Y₀), (O₁ : Set Y₀) ⊆ T₀.proj ⁻¹' U₁ → (O₂ : Set Y₀) ⊆ T₀.proj ⁻¹' U₂ →
      IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O₁ → Y₀)
        (lowerIdealWBM 𝔍 s w₁ T₀ (throughMembers 𝔍 T₀ a))) →
      IsInvDomain (k - 1) (MarkedIdeal.pullback (Subtype.val : O₂ → Y₀)
        (lowerIdealWBM 𝔍 s w₂ T₀ (throughMembers 𝔍 T₀ a))) →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : O₁ → Y₀) (lowerIdealWBM 𝔍 s w₁ T₀ (throughMembers 𝔍 T₀ a)))
        (R.inv (MarkedIdeal.pullback (Subtype.val : O₁ → Y₀) (lowerIdealWBM 𝔍 s w₁ T₀ (throughMembers 𝔍 T₀ a))))
        (restrict O₁ T₁) →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : O₂ → Y₀) (lowerIdealWBM 𝔍 s w₂ T₀ (throughMembers 𝔍 T₀ a)))
        (R.inv (MarkedIdeal.pullback (Subtype.val : O₂ → Y₀) (lowerIdealWBM 𝔍 s w₂ T₀ (throughMembers 𝔍 T₀ a))))
        (restrict O₂ T₁) →
      ∀ (p : Y) (hp₁ : T₁.proj p ∈ O₁) (hp₂ : T₁.proj p ∈ O₂),
        (⟨p, hp₂⟩ : openPreimage T₁ O₂) ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O₂ → Y₀)
          (lowerIdealWBM 𝔍 s w₂ T₀ (throughMembers 𝔍 T₀ a))) (restrict O₂ T₁)).cosupp →
        R.inv (MarkedIdeal.pullback (Subtype.val : O₁ → Y₀) (lowerIdealWBM 𝔍 s w₁ T₀ (throughMembers 𝔍 T₀ a)))
            (restrict O₁ T₁) ⟨p, hp₁⟩ =
          R.inv (MarkedIdeal.pullback (Subtype.val : O₂ → Y₀) (lowerIdealWBM 𝔍 s w₂ T₀ (throughMembers 𝔍 T₀ a)))
            (restrict O₂ T₁) ⟨p, hp₂⟩

/-- **The chosen tangent direction is one as soon as its open set is nonempty** (otherwise the choice is `(∅, 0)`). -/
theorem isTangentDirectionAlong_tangentChoice_of_nonempty {x : X} (h : ((tangentChoice 𝔍 x).1).Nonempty) :
    IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d (tangentChoice 𝔍 x).1 (tangentChoice 𝔍 x).2 := by
  classical
  by_cases hex : ∃ (U : Set X) (w : X → ℂ), x ∈ U ∧ IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w
  · exact (StepOneLowerDomain.tangentChoice_spec 𝔍 hex).2
  · exfalso
    rw [tangentChoice, dif_neg hex] at h
    exact Set.not_nonempty_empty h

/-- **The anchor change is an instance of the independence of the hypersurface of maximal contact**: the two anchors use the
tangent directions chosen at their base points, which are tangent directions on their open sets (nonempty: they contain the
base points of the common point). -/
theorem anchorChangeBM_of_tangentIndepBM (hTI : TangentIndepBM 𝔍 R) : AnchorChangeBM 𝔍 R := by
  intro Y₀ Y T₀ T₁ hT s a b Oa Ob ha _ hla hlb hab hOa hOb hdoma hdomb hcana hcanb p hpa hpb hpc
  have hwa := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍 ⟨_, hOa hpa⟩
  have hwb := isTangentDirectionAlong_tangentChoice_of_nonempty 𝔍 ⟨_, hOb hpb⟩
  have hLa := lowerIdealBM_eq_lowerIdealWBM 𝔍 s T₀ a
  have hLb : lowerIdealBM 𝔍 s T₀ b =
      lowerIdealWBM 𝔍 s (tangentChoice 𝔍 (T₀.proj b)).2 T₀ (throughMembers 𝔍 T₀ a) := by
    rw [lowerIdealBM_eq_lowerIdealWBM, hab]
  rw [hLa] at hdoma hcana ⊢
  rw [hLb] at hdomb hcanb hpc ⊢
  exact hTI T₀ T₁ hT s a ha hla _ _ _ _ hwa hwb Oa Ob hOa hOb hdoma hdomb hcana hcanb p hpa hpb hpc

end Indep

/-! ### Transport of the coefficient ideal on maximal contact -/

section Transport

/-- **The coefficient ideal on maximal contact along isomorphic towers**: for a biholomorphism `Φ : X' ≃ X`, towers `T₀' ≅ T₀`
over `Φ` (last-stage map `χ₀`) and `T₀` a multiple test blow-up of `𝓒_N(𝔍_∅)`, the coefficient ideal of `Φ^*𝔍` on `V(w ∘ Φ)`
along `T₀'` is the `χ₀`-pullback of that of `𝔍` on `V(w)` along `T₀`. -/
theorem contactCoeffBM_isTowerIso {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (w : X → ℂ) {Y₀' Y₀ : CMfd.{u} n}
    {T₀' : BlowupTower X' Y₀'} {T₀ : BlowupTower X Y₀}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₀} (hiso : IsTowerIso Φ T₀' T₀ χ₀)
    (hT₀ : IsGeoTestTower (coeffEmptyBM 𝔍) T₀) :
    contactCoeffBM (MarkedIdeal.pullback Φ 𝔍) (w ∘ Φ) T₀' = MarkedIdeal.pullback χ₀ (contactCoeffBM 𝔍 w T₀) := by
  have hwf := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM h𝔍
  have hc : coeffEmptyBM (MarkedIdeal.pullback Φ 𝔍) = MarkedIdeal.pullback Φ (coeffEmptyBM 𝔍) := by
    show coeffMarkedAlong (MarkedIdeal.pullback Φ (emptyBoundary 𝔍)) = _
    exact (pullback_coeffMarkedAlong_of_inverse Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply Φ.symm_apply_apply
      (emptyBoundary 𝔍) h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd).symm
  show withN (geoTransformAlong (coeffEmptyBM (MarkedIdeal.pullback Φ 𝔍)) T₀')
      (strictAlong T₀' (Φ ⁻¹' (𝔍.N ∩ {x | w x = 0}))) = _
  rw [hc, IsTowerIso.geoTransformAlong_eq Φ hwf.isClosedSubmanifold_N hwf.isCoherent hiso hT₀,
    IsTowerIso.strictAlong_eq hiso]
  rfl

/-- **The coefficient ideal on maximal contact along restricted towers**: for `U ⊆ X` open and `T₀` a multiple test blow-up of
`𝓒_N(𝔍_∅)`, the coefficient ideal of `𝔍|_U` on `V(w ∘ ι)` along `T₀|_U` is the restriction to `T₀⁻¹U` of that of `𝔍` on `V(w)`
along `T₀`. -/
theorem contactCoeffBM_restrict {X : CMfd.{u} n} (U : Opens X) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) (w : X → ℂ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (coeffEmptyBM 𝔍) T₀) :
    contactCoeffBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (w ∘ (Subtype.val : U → X)) (restrict U T₀) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (contactCoeffBM 𝔍 w T₀) := by
  have hwf := HironakaG11InvBMStage.isWellFormed_coeffEmptyBM h𝔍
  have hc : coeffEmptyBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (coeffEmptyBM 𝔍) := by
    show coeffMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → X) (emptyBoundary 𝔍)) = _
    exact (pullback_val_coeffMarkedAlong U (emptyBoundary 𝔍) h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd).symm
  show withN (geoTransformAlong (coeffEmptyBM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀)) (strictAlong (restrict U T₀) ((Subtype.val : U → X) ⁻¹' (𝔍.N ∩ {x | w x = 0}))) = _
  rw [hc, geoTransformAlong_restrict U hwf.isClosedSubmanifold_N hwf.isCoherent T₀ hT₀, strictAlong_restrict U T₀]
  rfl

end Transport

end

end Hironaka.HironakaG11InvBMTangentIndep
