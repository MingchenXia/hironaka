import Hironaka.Invariant.MemberRestrictTowerIso
import Hironaka.Resolution.HironakaG3RRawRegimeLocality

/-! # O7a′-1: the restriction laws of Step 1's lower values with WINDOW lower data

Lane G3 (run 0080, round 2).  Blueprint: `hironaka-g3-r-window-lower-value.tex`.
Plan: `work/hironaka-resume-20261111/G3/O7A-PRIME-PLAN.md` (§3 LocalLaw, §4 node N2, §5 item 2: the first genuinely
missing lemma O7a′-1).  Human decision (I-1334 C-0002): G3L07's endpoint quantifies only over canonical next centres, so
O7a′ is needed only in its LocalLaw / StageLaw form: values along towers that are canonical OVER A WINDOW.

The held restriction laws of the lower values of the masked Step 1 value function
(`ContactLowerValue.lowerValueL_zero_restrict`, `MemberRestrictTowerIso.lowerValueL_succ_restrict`) need GLOBAL lower data:
the restricted lower tail is a canonical segment of the lower marked ideal on its WHOLE mask.  Along a tower that is
canonical only over a window, that fails off the window.  Here:

* `LocalLaw R` (named hypothesis on the lower invariant `R`, the inductive hypothesis of O7a′; TRUE for `ofDimZero`,
  `localLaw_ofDimZero`, and claimed for the canonical family by the O7a′ induction): the value of a marked ideal of the
  domain along ANY tower, at a point over an open set `U`, equals the value of its restriction to `U` along the restricted
  tower whenever the latter is a canonical segment -- property (5) with global canonicity replaced by canonicity over `U`;
* `isInvDomain_restrict_nestedOpens`, **`inv_eq_restrict_nestedOpens_of_localLaw`**: the window form of
  `MaxLocusLocal.restrict_nestedOpens` (values on `V ⊆ W` agree when only the `V`-tail is canonical);
* `windowB`, `windowLowerB`, `windowA`, `windowLowerA`: the trace windows `mask ∩ T₀⁻¹U` and the lower marked ideals there;
* **`lowerValueL_zero_restrict_window`**, **`lowerValueL_succ_restrict_window`** (O7a′-1): the two held restriction laws
  with window lower data in place of global lower data, given `LocalLaw R`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG3RWindowLowerValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  BlowupTowerIsomorphism ResolutionInvariantExt StepOneTangentChange ContactStageKept
  StepOneValue StepOneLowerDomain StepOneValueMasked MarkedIdealOperationsAlong.MarkedIdeal
  InvDomainMemberRestriction InvDomainRebase StepOneNearby BoundaryCount
  ContactLowerValue MemberRestrictTowerIso
open HomogenizedGlueingTower (strictAlong)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The window-local law (named hypothesis) and its base case -/

section LocalLaw

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The window-local law of a resolution invariant** (`LocalLaw(k)` of the O7a′ plan, with the marked ideal in the
domain): for `𝔪` in the domain, an open `U`, ANY tower `T` whose restriction to `U` is a canonical segment of `𝔪|_U`, and a
point `p` over `U` in the cosupport of `𝔪_T`, the value of `𝔪` along `T` at `p` is the value of `𝔪|_U` along `T|_U` at `p`.
This is property (5) (`ResolutionInvariant.restrictOpen`) with the global canonicity of `T` replaced by canonicity over `U`
(no hypothesis on `T` over `X ∖ U`).  It is the inductive hypothesis of O7a′: the value along a tower depends only on the
germs of the data along the history of the point, the classical choices of tangent directions being absorbed by property
(7) on the canonical window.  Proved for `ofDimZero` (`localLaw_ofDimZero`); for the canonical family it is the open O7a′
induction. -/
def LocalLaw (R : ResolutionInvariant.{u, v} n k Λ) : Prop :=
  ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ (U : Opens X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y),
    IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (R.inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪))
      (restrict U T) →
    ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp →
      R.inv (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = R.inv 𝔪 T p

/-- **The base case `k = 0`**: the constant invariant `ofDimZero` satisfies the window-local law. -/
theorem localLaw_ofDimZero (Λ : Type v) [LinearOrder Λ] (l₀ : Λ) :
    LocalLaw (ResolutionInvariant.ofDimZero.{u, v} (n := n) Λ l₀) :=
  fun _ _ _ _ _ _ _ _ => rfl

end LocalLaw

/-! ### Nested open sets: the window form of `MaxLocusLocal.restrict_nestedOpens` -/

section Nested

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The domain restricts to a smaller open set** (the domain part of `MaxLocusLocal.restrict_nestedOpens`, without any
tower). -/
theorem isInvDomain_restrict_nestedOpens {𝔫 : MarkedIdeal n X} (h𝔫 : 𝔫.ideal.IsCoherent) {W V : Opens X} (hVW : V ≤ W)
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)) :
    IsInvDomain k (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) := by
  have hdom' := InvDomainTowerAlong.isInvDomain_pullback_val (MaxLocusLocal.nestedOpens W V) hdom
  have hdomV := InvDomainTowerAlong.isInvDomain_pullback (MaxLocusLocal.nestedOpensDiffeo (n := n) hVW).symm hdom'
  rwa [MaxLocusLocal.pullback_symm_nestedOpensDiffeo (M := X) h𝔫 hVW] at hdomV

/-- **Values on nested open sets with only the smaller tail canonical** (the window form of
`MaxLocusLocal.restrict_nestedOpens`): let `𝔫|_W` lie in the domain, `V ⊆ W` open, `T` ANY tower with `T|_V` a canonical
segment of `𝔫|_V`.  At a point of the cosupport over `V` the values of `𝔫|_V` along `T|_V` and of `𝔫|_W` along `T|_W`
agree, given the window-local law of `R`.  (`T|_V` is `T|_W` restricted to `W ∩ V`, `MaxLocusLocal.isTowerIso_restrict_nestedOpens`;
property (6) on the canonical `V`-side, then `LocalLaw R` for `𝔫|_W` at the open `W ∩ V` of `W`.) -/
theorem inv_eq_restrict_nestedOpens_of_localLaw (R : ResolutionInvariant.{u, v} n k Λ) (hLL : LocalLaw R)
    {𝔫 : MarkedIdeal n X} (h𝔫 : 𝔫.ideal.IsCoherent) {W V : Opens X} (hVW : V ≤ W)
    (hdom : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcanV : IsCanonical (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫)
      (R.inv (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫)) (restrict V T))
    (p : openPreimage T V)
    (hpV : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T)).cosupp)
    (hpW : (⟨(p : Y), MaxLocusLocal.openPreimage_mono T hVW p.2⟩ : openPreimage T W) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T)).cosupp) :
    R.inv (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T) p =
      R.inv (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T)
        ⟨(p : Y), MaxLocusLocal.openPreimage_mono T hVW p.2⟩ := by
  have hdomV := isInvDomain_restrict_nestedOpens h𝔫 hVW hdom
  have hiso := MaxLocusLocal.isTowerIso_restrict_nestedOpens (X := X) hVW T
  set ξ := MaxLocusLocal.nestedDiffeo (n := n) (openPreimage T W) (openPreimage (restrict W T) (MaxLocusLocal.nestedOpens W V))
    (openPreimage T V) (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens W V T)
    (MaxLocusLocal.openPreimage_mono T hVW) with hξ
  have hξq : ξ (ξ.symm p) = p := ξ.apply_symm_apply p
  have hcan' := ResolutionInvariantExt.isCanonical_of_isTowerIso R hdomV
    (MaxLocusLocal.nestedOpensDiffeo (n := n) hVW) hiso hcanV
  have hpb := MaxLocusLocal.pullback_val_pullback_val (M := X) h𝔫 hVW
  have key := R.towerIso (MaxLocusLocal.nestedOpensDiffeo (n := n) hVW) _ hdomV _ _ _ hiso hcanV (ξ.symm p)
    (by rw [hξq]; exact hpV)
  rw [hξq, ← hpb] at key
  rw [← hpb] at hcan'
  have hLLq := hLL _ hdom (MaxLocusLocal.nestedOpens W V) (restrict W T) hcan' (ξ.symm p) hpW
  exact key.symm.trans hLLq

end Nested

/-! ### The trace windows of the masks -/

section Windows

variable {X : CMfd.{u} n}

/-- **The trace window of Step 1bb's mask** on the preimage of an open `U` of the base. -/
abbrev windowB (𝔍 : MarkedIdeal n X) (U : Opens X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) : Opens Y₀ :=
  maskB 𝔍 T₀ y₀ ⊓ openPreimage T₀ U

/-- **Step 1bb's lower marked ideal on the trace window** (tangent direction chosen for `𝔍` at the base point of `y₀`). -/
abbrev windowLowerB (𝔍 : MarkedIdeal n X) (U : Opens X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    MarkedIdeal n (windowB 𝔍 U T₀ y₀) :=
  contactMarkedKept 𝔍 (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀ (windowB 𝔍 U T₀ y₀)

/-- **The trace window of Step 1ab's mask** on the preimage of an open `U` of the base. -/
abbrev windowA (𝔍 : MarkedIdeal n X) (U : Opens X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) : Opens Y₀ :=
  maskA 𝔍 T₀ y₀ ⊓ openPreimage T₀ U

/-- **Step 1ab's lower marked ideal on the trace window.** -/
abbrev windowLowerA (𝔍 : MarkedIdeal n X) (U : Opens X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    MarkedIdeal n (windowA 𝔍 U T₀ y₀) :=
  MarkedIdeal.pullback (Subtype.val : windowA 𝔍 U T₀ y₀ → Y₀)
    (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
      (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) y₀))

end Windows

/-! ### O7a′-1: the restriction laws with window lower data -/

section Restrict

variable {X : CMfd.{u} n} (U : Opens X) {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **O7a′-1 at level `0`: property (5) of Step 1bb's lower value with WINDOW lower data.**  The held
`ContactLowerValue.lowerValueL_zero_restrict` with its global lower data `hD` (the restricted lower tail is a canonical
segment of the GLOBAL lower marked ideal on the whole mask) replaced by window data: the image of `χ p'` lies in its mask,
the global lower marked ideal lies in the domain, and the lower tail restricted to the trace window
`windowB = mask ∩ T₀⁻¹U` is a canonical segment of the lower marked ideal restricted there (`hcanW`); plus the
window-local law `LocalLaw R` of the lower invariant (the inductive hypothesis).  The global test tower `T₀ T₁` of `J̄`
is kept (the consumers' towers are test towers; canonicity holds only over the window).  Proof: the held proof, its first
step (`MaxLocusLocal.restrict_nestedOpens`, which needs the global canonical tail) replaced by
`inv_eq_restrict_nestedOpens_of_localLaw`. -/
theorem lowerValueL_zero_restrict_window (R : ResolutionInvariant.{u, v} n k Λ) (hLL : LocalLaw R) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) {Y₀ Z Y₀' Z' : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Z}
    {T₀' : BlowupTower (CMfd.of (n := n) U) Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₀ U)}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) T₀' (restrict U T₀) χ₀)
    {T₁' : BlowupTower Y₀' Z'}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ U))}
    (hχ : IsTowerIso χ₀ T₁' (restrict (openPreimage T₀ U) T₁) χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    {p' : Z'} (hp : ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈
      (geoTransformAlong (barMarked 𝔍) (T₀.append T₁)).cosupp)
    (hD' : LowerDataL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) 0 T₀' T₁' p')
    (hmask : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈
      lowerMask 𝔍 0 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))
    (hdom : IsInvDomain k (lowerMarkedM 𝔍 0 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z))))
    (hcanW : IsCanonical (windowLowerB 𝔍 U T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))
      (R.inv (windowLowerB 𝔍 U T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z))))
      (restrict (windowB 𝔍 U T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z))) T₁)) :
    lowerValueL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) 0 T₀' T₁' p' =
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) 0 T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍U : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed := MarkedIdealRestrictOpen.IsWellFormed.pullback_val h𝔍 U
  have hJU := isWellFormed_barMarked (X := CMfd.of (n := n) U) _ h𝔍U
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  -- the restricted towers
  have hT₀U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T₀) := by
    rw [hbarU]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hgU : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T₀) =
      MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y₀) (geoTransformAlong (barMarked 𝔍) T₀) := by
    rw [hbarU]
    exact geoTransformAlong_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hRU : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁)) := by
    refine (isGeoTestTower_append_iff _ _ _).mpr ⟨hT₀U, ?_⟩
    rw [hgU]
    exact isGeoTestTower_restrict (openPreimage T₀ U) hNT hcT T₁ hT₁
  have hcosR : χ p' ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁))).cosupp := by
    rw [geoTransformAlong_append, hgU,
      ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hNT hcT (openPreimage T₀ U) T₁ hT₁, mem_preimage,
      ← geoTransformAlong_append]
    exact hp
  -- along the isomorphism over `id_U`
  have hiso' := hiso.append hχ
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) =
      barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) :=
    ContactCanonicalAlong.pullback_id _ hJU.isCoherent
  have hT' : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (T₀'.append T₁') := by
    have h1 := (IsTowerIso.isGeoTestTower_iff _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso').mpr hRU
    rwa [hpb] at h1
  have hp' : p' ∈ (geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (T₀'.append T₁')).cosupp := by
    have h1 := IsTowerIso.cosupp_geoTransformAlong _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso' hRU
    rw [hpb] at h1
    rw [h1]
    exact hcosR
  -- the images of `p'` and `χ p'`
  have hy : χ₀ (T₁'.proj p') = (restrict (openPreimage T₀ U) T₁).proj (χ p') := hχ.proj_comm p'
  have hy' : (((restrict (openPreimage T₀ U) T₁).proj (χ p') : openPreimage T₀ U) : Y₀) =
      T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := proj_restrict _ T₁ (χ p')
  -- the data on the side of `𝔍`: the mask `W` of `χ p'` and the tangent direction `w` chosen at its base point
  have h := hmask
  have hxw : T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) ∈
      (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).1 :=
    (interior_subset h).1
  have hw := StepOneCompare.tangentChoice_spec_of_mem 𝔍 hxw
  set W : Opens Y₀ := maskB 𝔍 T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)) with hWdef
  set w : X → ℂ := (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).2
    with hwdef
  set Uw : Set X := (tangentChoice 𝔍 (T₀.proj (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))).1
    with hUwdef
  -- (1) shrink the mask to its part over `U`
  set W₁ : Opens Y₀ := W ⊓ openPreimage T₀ U with hW₁def
  have hW₁W : W₁ ≤ W := inf_le_left
  have hW₁U : W₁ ≤ openPreimage T₀ U := inf_le_right
  have hcoh := isCoherent_restrictedCoeff 𝔍 h𝔍.isCoherent h𝔍.isClosedSubmanifold_N w T₀ hT₀
  have hdom₁ : IsInvDomain k (contactMarkedKept 𝔍 w T₀ W₁) := isInvDomain_restrict_nestedOpens hcoh hW₁W hdom
  have hcan₁ : IsCanonical (contactMarkedKept 𝔍 w T₀ W₁) (R.inv (contactMarkedKept 𝔍 w T₀ W₁)) (restrict W₁ T₁) := hcanW
  have hpW₁ : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈ W₁ := ⟨h, (χ p').2⟩
  have hcos₁ : (⟨((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z), hpW₁⟩ : openPreimage T₁ W₁) ∈
      (geoTransformAlong (contactMarkedKept 𝔍 w T₀ W₁) (restrict W₁ T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
      ⟨Uw, hw.isOpen⟩ hw T₀ T₁ hT W₁ fun y hy => (interior_subset (hW₁W hy)).1).2]
    exact hp
  have hcosW : (⟨((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z), MaxLocusLocal.openPreimage_mono T₁ hW₁W hpW₁⟩ :
      openPreimage T₁ W) ∈ (geoTransformAlong (contactMarkedKept 𝔍 w T₀ W) (restrict W T₁)).cosupp := by
    rw [(ContactStageTail.isGeoTestTower_tail_coeffHomAlong_of_le 𝔍 h𝔍.isClosedSubmanifold_N h𝔍.isCoherent hd
      ⟨Uw, hw.isOpen⟩ hw T₀ T₁ hT W fun y hy => (interior_subset hy).1).2]
    exact hp
  have hv1 := inv_eq_restrict_nestedOpens_of_localLaw R hLL hcoh hW₁W hdom T₁ hcan₁ ⟨_, hpW₁⟩ hcos₁ hcosW
  -- (2) restrict to `U`
  obtain ⟨-, hcan₂, hval₂⟩ := inv_contactMarkedKept_restrict U R h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd T₀ hT₀ w
    hW₁U hdom₁ T₁ hcan₁
  have hdom₂ := (inv_contactMarkedKept_restrict U R h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd T₀ hT₀ w
    hW₁U hdom₁ T₁ hcan₁).1
  set W₂ : Opens (CMfd.of (n := n) (openPreimage T₀ U)) := MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁ with hW₂def
  have hq₂ : χ p' ∈ openPreimage (restrict (openPreimage T₀ U) T₁) W₂ := by
    show (((restrict (openPreimage T₀ U) T₁).proj (χ p') : openPreimage T₀ U) : Y₀) ∈ W₁
    rw [hy']
    exact hpW₁
  obtain ⟨hcosiff, hv2⟩ := hval₂ ⟨χ p', hq₂⟩ ⟨_, hpW₁⟩ rfl
  have hcos₂ := hcosiff.mpr hcos₁
  have hv2' := hv2 hcos₁
  -- (3) along the isomorphism over `id_U`
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (W₂ : Set (CMfd.of (n := n) (openPreimage T₀ U))),
    W₂.isOpen.preimage χ₀.continuous⟩ with hW'def
  have hW' : ∀ q, q ∈ W' ↔ χ₀ q ∈ W₂ := fun _ => Iff.rfl
  obtain ⟨hdom₃, hcan₃, hval₃⟩ := inv_contactMarkedKept_isTowerIso
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) R h𝔍U.isCoherent h𝔍U.isClosedSubmanifold_N hd hiso
    hT₀U (w ∘ Subtype.val) hW' hχ hdom₂ hcan₂
  have hpbU : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔍 :=
    ContactCanonicalAlong.pullback_id _ h𝔍U.isCoherent
  rw [hpbU] at hdom₃ hcan₃ hval₃
  have hpW' : T₁'.proj p' ∈ W' := by
    show χ₀ (T₁'.proj p') ∈ W₂
    rw [hy]
    exact hq₂
  have hv3 := hval₃ ⟨p', hpW'⟩ ⟨χ p', hq₂⟩ rfl hcos₂
  -- (4) the anchor for `𝔍|_U` with `w ∘ ι` on `W'`
  have hu : IsTangentDirectionAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).N
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).ideal (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).d
      ((Subtype.val : U → X) ⁻¹' Uw) (w ∘ Subtype.val) :=
    ContactMarkedCanonical.isTangentDirectionAlong_comp_val U h𝔍.isCoherent hw
  have hproj : ∀ q, (((T₀'.proj q : CMfd.of (n := n) U) : U) : X) = T₀.proj ((χ₀ q : openPreimage T₀ U) : Y₀) := by
    intro q
    have e : T₀'.proj q = (restrict U T₀).proj (χ₀ q) := hiso.proj_comm q
    rw [e, proj_restrict]
  have hW'U : (W' : Set Y₀') ⊆ T₀'.proj ⁻¹' ((Subtype.val : U → X) ⁻¹' Uw) := by
    intro q hq
    have h1 : ((χ₀ q : openPreimage T₀ U) : Y₀) ∈ W₁ := hq
    show (((T₀'.proj q : CMfd.of (n := n) U) : U) : X) ∈ Uw
    rw [hproj]
    exact (interior_subset (hW₁W h1)).1
  have hW'E : ∀ H ∈ origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀', Disjoint (W' : Set Y₀') H := by
    intro H hH
    have e := origMembers_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) _ h𝔍U hd hiso hT₀U
    rw [hpbU, origMembers_restrict U 𝔍 h𝔍 hd hT₀, List.map_map] at e
    rw [e] at hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    refine Set.disjoint_left.mpr fun q hq hqH => ?_
    have h1 : ((χ₀ q : openPreimage T₀ U) : Y₀) ∈ W₁ := hq
    exact (interior_subset (hW₁W h1)).2.1 H₀ hH₀ hqH
  have key := lowerValueL_zero_eq (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U hd T₀' T₁' hT' hu W' hW'U hW'E
    hdom₃ hcan₃ hpW' hp' hD'
  rw [key, lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  exact hv3.trans (hv2'.trans hv1)

/-- **O7a′-1 at the levels `s + 1`: property (5) of Step 1ab's lower value with WINDOW lower data.**  The held
`MemberRestrictTowerIso.lowerValueL_succ_restrict` with its global lower data `hD` replaced by window data: the image of
`χ p'` lies in its mask, the global lower marked ideal lies in the domain, `χ p'` lies in its cosupport along the
restricted tail, and the lower tail restricted to the trace window `windowA = mask ∩ T₀⁻¹U` is a canonical segment of the
lower marked ideal restricted there (`hcanW`); plus `LocalLaw R`.  No test hypothesis on the restricted tail over the whole
mask is used (it can fail off the window: centres of lower level); the window cosupport is the trace of the mask one along
EVERY tower (`HironakaG3RRawRegimeLocality.cosupp_restrict_raw`, node N1). -/
theorem lowerValueL_succ_restrict_window (R : ResolutionInvariant.{u, v} n k Λ) (hLL : LocalLaw R) (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed)
    (hd : 1 ≤ 𝔍.d) (hn : 0 < n) {s : ℕ} {Y₀ Z Y₀' Z' : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Z}
    {T₀' : BlowupTower (CMfd.of (n := n) U) Y₀'}
    {χ₀ : Y₀' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₀ U)}
    (hiso : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) T₀' (restrict U T₀) χ₀)
    {T₁' : BlowupTower Y₀' Z'}
    {χ : Z' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage T₁ (openPreimage T₀ U))}
    (hχ : IsTowerIso χ₀ T₁' (restrict (openPreimage T₀ U) T₁) χ) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁))
    {p' : Z'}
    (hD' : LowerDataL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
      (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (s + 1) T₀' T₁' p')
    (hmask : T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) ∈
      lowerMask 𝔍 (s + 1) T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))
    (hdom : IsInvDomain k (lowerMarkedM 𝔍 (s + 1) T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z))))
    (hcos : (⟨((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z), hmask⟩ :
        openPreimage T₁ (lowerMask 𝔍 (s + 1) T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))) ∈
      (geoTransformAlong (lowerMarkedM 𝔍 (s + 1) T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))
        (restrict (lowerMask 𝔍 (s + 1) T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z))) T₁)).cosupp)
    (hcanW : IsCanonical (windowLowerA 𝔍 U T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z)))
      (R.inv (windowLowerA 𝔍 U T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z))))
      (restrict (windowA 𝔍 U T₀ (T₁.proj ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z))) T₁)) :
    lowerValueL (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (lowerMarkedM (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (s + 1) T₀' T₁' p' =
      lowerValueL R 𝔍 (lowerMarkedM 𝔍) (s + 1) T₀ T₁ ((χ p' : openPreimage T₁ (openPreimage T₀ U)) : Z) := by
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔍U : (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍).IsWellFormed :=
    MarkedIdealRestrictOpen.IsWellFormed.pullback_val h𝔍 U
  have hJU := isWellFormed_barMarked (X := CMfd.of (n := n) U) _ h𝔍U
  have hbarU : barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) =
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked 𝔍) :=
    ContactStageKept.barMarked_pullback_val U h𝔍.isCoherent h𝔍.isClosedSubmanifold_N hd
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff _ T₀ T₁).mp hT
  have hwf : (geoTransformAlong (barMarked 𝔍) T₀).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔫 : 1 ≤ (geoTransformAlong (barMarked 𝔍) T₀).d := by
    rw [d_geoTransformAlong]; exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hE₀𝔫 : ∀ H ∈ origMembers 𝔍 T₀, H ∈ (geoTransformAlong (barMarked 𝔍) T₀).E :=
    fun H hH => List.mem_of_mem_take hH
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    T₀ hT₀
  -- the restricted towers and the test tower on the side of `𝔍|_U`
  have hT₀U : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀) := by
    rw [hbarU]
    exact isGeoTestTower_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hgU : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (restrict U T₀) = MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) (geoTransformAlong (barMarked 𝔍) T₀) := by
    rw [hbarU]
    exact geoTransformAlong_restrict U hJ.isClosedSubmanifold_N hJ.isCoherent T₀ hT₀
  have hRU : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      ((restrict U T₀).append (restrict (openPreimage T₀ U) T₁)) := by
    refine (isGeoTestTower_append_iff _ _ _).mpr ⟨hT₀U, ?_⟩
    rw [hgU]
    exact isGeoTestTower_restrict (openPreimage T₀ U) hNT hcT T₁ hT₁
  have hiso' := hiso.append hχ
  have hpb : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) =
      barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) :=
    ContactCanonicalAlong.pullback_id _ hJU.isCoherent
  have hT' : IsGeoTestTower (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍))
      (T₀'.append T₁') := by
    have h1 := (IsTowerIso.isGeoTestTower_iff _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso').mpr hRU
    rwa [hpb] at h1
  -- the stage `T₀'` and its original members
  have h𝔫' : geoTransformAlong (barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) T₀' =
      MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) (geoTransformAlong (barMarked 𝔍) T₀)) := by
    have h1 := IsTowerIso.geoTransformAlong_eq _ hJU.isClosedSubmanifold_N hJU.isCoherent hiso hT₀U
    rw [hpb, hgU] at h1
    exact h1
  have hOrig : origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀' =
      ((origMembers 𝔍 T₀).map ((Subtype.val : (openPreimage T₀ U) → Y₀) ⁻¹' ·)).map (χ₀ ⁻¹' ·) := by
    have e := ContactLowerValue.origMembers_isTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
      _ h𝔍U hd hiso hT₀U
    have hpbU : MarkedIdeal.pullback (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞)
        (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) = MarkedIdeal.pullback (Subtype.val : U → X) 𝔍 :=
      ContactCanonicalAlong.pullback_id _ h𝔍U.isCoherent
    rw [hpbU, ContactLowerValue.origMembers_restrict U 𝔍 h𝔍 hd hT₀] at e
    exact e
  -- the points
  have hy : χ₀ (T₁'.proj p') = (restrict (openPreimage T₀ U) T₁).proj (χ p') := hχ.proj_comm p'
  have hy' : (((restrict (openPreimage T₀ U) T₁).proj (χ p') : (openPreimage T₀ U)) : Y₀) = T₁.proj ((χ p') : Z) := proj_restrict _ T₁ (χ p')
  -- Step 1ab's restricted marked ideal of `𝔍|_U` at the image of `p'`
  set 𝔐 : MarkedIdeal n Y₀ := memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
    (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) (T₁.proj ((χ p') : Z))) with h𝔐def
  have hwfS : 𝔐.IsWellFormed := isWellFormed_memberRestrict hn hwf _
  have hM : memberRestrict (geoTransformAlong (barMarked (X := CMfd.of (n := n) U)
        (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) T₀')
      (membersThrough (geoTransformAlong (barMarked (X := CMfd.of (n := n) U)
          (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) T₀').E
        (origMembers (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) T₀') (T₁'.proj p')) =
      MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) 𝔐) := by
    rw [h𝔫', hOrig]
    rw [← pullback_diffeo_memberRestrict_membersThrough χ₀ (IsWellFormed.pullback_val hwf (openPreimage T₀ U)) hd𝔫 _ (T₁'.proj p'), hy]
    congr 1
    have e := InvDomainRebase.pullback_val_memberRestrict_membersThrough hwf hd𝔫 hE₀𝔫 (openPreimage T₀ U) ((restrict (openPreimage T₀ U) T₁).proj (χ p'))
    rw [hy'] at e
    exact e.symm
  -- the data on the side of `𝔍`: the mask `A` of `(χ p')`, shrunk to `W₁ = A ∩ (openPreimage T₀ U)`
  have h := hmask
  set A : Opens Y₀ := lowerMask 𝔍 (s + 1) T₀ (T₁.proj ((χ p') : Z)) with hAdef
  have hdomA : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐) := hdom
  have hcosA : (⟨((χ p') : Z), h⟩ : openPreimage T₁ A) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐) (restrict A T₁)).cosupp := hcos
  set W₁ : Opens Y₀ := A ⊓ (openPreimage T₀ U) with hW₁def
  have hW₁A : W₁ ≤ A := inf_le_left
  have hW₁V : W₁ ≤ (openPreimage T₀ U) := inf_le_right
  have hdom₁ : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : W₁ → Y₀) 𝔐) :=
    isInvDomain_restrict_nestedOpens hwfS.isCoherent hW₁A hdomA
  have hcan₁ : IsCanonical (MarkedIdeal.pullback (Subtype.val : W₁ → Y₀) 𝔐)
      (R.inv (MarkedIdeal.pullback (Subtype.val : W₁ → Y₀) 𝔐)) (restrict W₁ T₁) := hcanW
  have hz₁ : T₁.proj ((χ p') : Z) ∈ W₁ := ⟨h, (χ p').2⟩
  have hhol𝔐 : ∀ x g, 𝔐.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwfS.isCoherent hg
  have hcos₁ : (⟨((χ p') : Z), hz₁⟩ : openPreimage T₁ W₁) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W₁ → Y₀) 𝔐) (restrict W₁ T₁)).cosupp := by
    have e1 := HironakaG3RRawRegimeLocality.cosupp_restrict_raw 𝔐 hhol𝔐 W₁ T₁
    have e2 := HironakaG3RRawRegimeLocality.cosupp_restrict_raw 𝔐 hhol𝔐 A T₁
    rw [e1]
    have h2 := hcosA
    rw [e2] at h2
    exact h2
  have hv₁ : R.inv (MarkedIdeal.pullback (Subtype.val : A → Y₀) 𝔐) (restrict A T₁) ⟨((χ p') : Z), h⟩ =
      R.inv (MarkedIdeal.pullback (Subtype.val : W₁ → Y₀) 𝔐) (restrict W₁ T₁) ⟨((χ p') : Z), hz₁⟩ :=
    (inv_eq_restrict_nestedOpens_of_localLaw R hLL hwfS.isCoherent hW₁A hdomA T₁ hcan₁ ⟨_, hz₁⟩ hcos₁ hcosA).symm
  -- `(𝔐|_V)|_{W₂}` is `𝔐|_{W₁}` transported along `nestedOpensDiffeo`
  set W₂ : Opens (CMfd.of (n := n) (openPreimage T₀ U)) := MaxLocusLocal.nestedOpens (openPreimage T₀ U) W₁ with hW₂def
  have hiso₂ := MaxLocusLocal.isTowerIso_restrict_nestedOpens (X := Y₀) hW₁V T₁
  obtain ⟨hdom₂, hcan₂, hval₂⟩ := inv_pullback_isTowerIso R hdom₁ (MaxLocusLocal.nestedOpensDiffeo (n := n) hW₁V)
    hiso₂ hcan₁
  have hpb₂ := MaxLocusLocal.pullback_val_pullback_val (M := Y₀) hwfS.isCoherent hW₁V
  rw [← hpb₂] at hdom₂ hcan₂ hval₂
  have hq₂ : (χ p') ∈ openPreimage (restrict (openPreimage T₀ U) T₁) W₂ :=
    (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens (openPreimage T₀ U) W₁ T₁ (χ p')).mpr hz₁
  have hξ₂ : MaxLocusLocal.nestedDiffeo (n := n) (openPreimage T₁ (openPreimage T₀ U)) (openPreimage (restrict (openPreimage T₀ U) T₁) W₂) (openPreimage T₁ W₁)
      (MaxLocusLocal.mem_openPreimage_restrict_nestedOpens (openPreimage T₀ U) W₁ T₁) (MaxLocusLocal.openPreimage_mono T₁ hW₁V)
      ⟨(χ p'), hq₂⟩ = ⟨((χ p') : Z), hz₁⟩ := rfl
  obtain ⟨hcosq₂, hvq₂⟩ := hval₂ ⟨(χ p'), hq₂⟩ (by rw [hξ₂]; exact hcos₁)
  rw [hξ₂] at hvq₂
  -- transport along `χ₀` to `W' = χ₀⁻¹ W₂`
  set W' : Opens Y₀' := ⟨χ₀ ⁻¹' (W₂ : Set (CMfd.of (n := n) (openPreimage T₀ U))), W₂.isOpen.preimage χ₀.continuous⟩ with hW'def
  have hW' : ∀ r, r ∈ W' ↔ χ₀ r ∈ W₂ := fun _ => Iff.rfl
  have hξ := isTowerIso_restrictOpens hW' hχ (isTowerIso_mem_openPreimage_iff hχ hW')
  have hwfV : (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) 𝔐).ideal.IsCoherent :=
    (IsWellFormed.pullback_val hwfS (openPreimage T₀ U)).isCoherent
  obtain ⟨hdom₃, hcan₃, hval₃⟩ := inv_pullback_isTowerIso R hdom₂ (diffeoOpens χ₀ W' W₂ hW') hξ hcan₂
  have hpb₃ : MarkedIdeal.pullback (Subtype.val : W' → Y₀')
      (MarkedIdeal.pullback χ₀ (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) 𝔐)) =
      MarkedIdeal.pullback (diffeoOpens χ₀ W' W₂ hW')
        (MarkedIdeal.pullback (Subtype.val : W₂ → CMfd.of (n := n) (openPreimage T₀ U)) (MarkedIdeal.pullback (Subtype.val : (openPreimage T₀ U) → Y₀) 𝔐)) :=
    ContactMarkedCanonical.pullback_pullback_of_comp_eq hwfV χ₀.contMDiff contMDiff_subtype_val
      (diffeoOpens χ₀ W' W₂ hW').contMDiff contMDiff_subtype_val fun _ => rfl
  rw [← hpb₃, ← hM] at hdom₃ hcan₃ hval₃
  have hpW' : T₁'.proj p' ∈ W' := by
    show χ₀ (T₁'.proj p') ∈ W₂
    rw [hy]
    exact hq₂
  have hξp : diffeoOpens χ (openPreimage T₁' W') (openPreimage (restrict (openPreimage T₀ U) T₁) W₂) (isTowerIso_mem_openPreimage_iff hχ hW')
      ⟨p', hpW'⟩ = ⟨(χ p'), hq₂⟩ := Subtype.ext rfl
  obtain ⟨-, hvp⟩ := hval₃ ⟨p', hpW'⟩ (by rw [hξp]; exact hcosq₂)
  rw [hξp] at hvp
  -- the anchors on both sides
  have key' := lowerValueL_succ_eq (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) h𝔍U hn
    T₀' T₁' hT' hD' W' hpW' hdom₃ hcan₃
  rw [key', lowerValueL_eq_of_mem R 𝔍 _ h]
  congr 1
  exact hvp.trans (hvq₂.trans hv₁.symm)


end Restrict

end

end Hironaka.HironakaG3RWindowLowerValue
