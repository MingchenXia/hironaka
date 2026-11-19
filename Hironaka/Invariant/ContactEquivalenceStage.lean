import Hironaka.Invariant.ContactEquivalenceAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.Invariant.MemberInterTowerAlong

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The reduction to a hypersurface of maximal contact at a later stage of a tower

Hironaka phase H3 (TN23-ENVELOPES), claimed on I-0981 C-0082 (offered C-0080, form fixed by TN-CLASSICAL in C-0081):
Step 1b of `hir:maximal-order-step` (`blueprint/src/hironaka.tex`) forms the restricted marked ideal
`𝓢_{u,T₀} = 𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}}` at the stage `T₀` where it starts, for a tangent direction `u` chosen
at the start of Step 1 on an open `U`, and evaluates the inductive invariant of `𝓢_{u,T₀}` along the rest `T₁` of the
segment.  This module proves that over `V = T₀⁻¹U` the transform `J̄_{T₀}` and `𝓢_{u,T₀}` are equivalent marked ideals
(`MarkedIdealEquivalence.WEquiv`), so that the tails `T₁|_V` are multiple test blow-ups of `𝓢_{u,T₀}|_V` with cosupports
`cosupp J̄_{T₀ T₁}`.  Blueprint `mc:strict-along-local`, `mc:giraud-local`, `mc:contact-equivalence-stage`,
`mc:contact-equivalence-stage-coeff-hom` (`blueprint/src/maximal-contact.tex`).  Source: Włodarczyk 2005 (arXiv `hiron.tex`),
Step 1bb ("By Lemma `le:codim2`, `(V(u)_i)_{0 ≤ i ≤ p}` is a multiple test blow-up of `(V(u), J̄|_{V(u)}, ∅, μ̄)`. In
particular the induced marked ideal for `i = p` is `J̄_{p|V(u)_p}`").

## Main results

* `strictAlong_inter_preimage_eq` (**strict transforms are local over open sets of the base**): if `A ∩ O = B ∩ O` for an
  open `O`, then `strictAlong T A ∩ T⁻¹O = strictAlong T B ∩ T⁻¹O`.
* `cosupp_subset_strictAlong_of_forall_exists` (**Giraud from local hypersurfaces of maximal contact**): if near every
  point of `N` some tangent direction `w` of `(𝔞|_N, d)` has `N ∩ V(w)` inside `S`, then along every multiple test blow-up
  the cosupports lie in the strict transforms of `S`; `centresIn_of_cosupp_subset`: then so do the centres;
  `cosupp_subset_of_wEquiv`: the condition passes to equivalent marked ideals.
* `wEquiv_withN_coeffMarkedAlong_of_cosupp_subset`: if the cosupports along every multiple test blow-up lie in the
  strict transforms of a closed submanifold `S ⊆ N`, then `𝔪 ≃ 𝓒_N(𝔪)|_S` (`le:codim2` with `S` in place of `V(u)`).
* `exists_isTangentDirectionAlong_stage` (**the tangent directions at the stage `T₀`**): every point of `N_{T₀}` over `U`
  has an open neighbourhood `W` and a tangent direction `w` of `𝔪_{T₀}` on `W` with `N_{T₀} ∩ V(w) ∩ W = S_{T₀} ∩ W`,
  `S_{T₀} = strictAlong T₀ (N ∩ V(u))`; `forall_exists_isTangentDirectionAlong_stage_val`: the same on `V = T₀⁻¹U`.
* `isClosedSubmanifold_strictAlong_stage`: `S_{T₀}` meets `V` in a closed submanifold of `V`.
* `wEquiv_stage_of_wEquiv` / `wEquiv_stage` (**the contact equivalence at the stage `T₀`**, for every `𝔫` with the same `N`
  and `𝔫_{T₀}|_V ≃ 𝔪_{T₀}|_V`): `𝔫_{T₀}|_V ≃ (𝓒_{N_{T₀}}(𝔫_{T₀})|_{S_{T₀}})|_V`;
  `wEquiv_pullback_val_geoTransformAlong`: an equivalence over `U` passes to the stages over `T⁻¹U`.
* `isGeoTestTower_tail_of_wEquiv` (**the tails**): a marked ideal equivalent to `𝔫_{T₀}|_V` has the tails `T₁|_V` of the
  multiple test blow-ups `T₀ T₁` of `𝔫` as multiple test blow-ups, with cosupports the traces of `cosupp 𝔫_{T₀ T₁}`.
* For `J̄ = 𝓒_N(𝓗_N(𝔞), μ)` (`homMarkedAlong_mk`, `wEquiv_pullback_val_coeffHom`: `J̄|_U ≃ (𝔞, μ)|_U`):
  `wEquiv_stage_coeffHom` (READING `(𝔞, μ)`, the one TN-CLASSICAL consumes, I-0981 C-0081): for a tangent direction `u` of
  `(𝔞|_N, μ)` on `U` and `T₀` a multiple test blow-up of `J̄`, `J̄_{T₀}|_V ≃ 𝓢_{u,T₀}|_V`; `exists_wEquiv_stage_coeffHom`: the
  form `∃ W ∋ z, W ⊆ T₀⁻¹U, ...` asked for in C-0081; `wEquiv_stage_coeffHom_of_isTangentDirectionAlong_coeffHom`
  (READING `J̄`, Włodarczyk's "`u ∈ 𝒟^{μ̄-1}(J̄)`"); `isGeoTestTower_tail_coeffHom`: if `T₀ T₁` is a multiple test blow-up of
  `J̄`, then `T₁|_V` is one of `𝓢_{u,T₀}|_V` and its cosupport is the trace of `cosupp J̄_{T₀ T₁}`.
* For `J̄ = 𝓒_N(𝓗_N(𝔍))` with `𝔍` carrying any divisor `E` (I-0981 C-0087 (b), the Step 1 marked ideal keeping its
  original members): `wEquiv_pullback_val_coeffHomAlong`, `wEquiv_stage_coeffHomAlong`, `exists_wEquiv_stage_coeffHomAlong`,
  `isGeoTestTower_tail_coeffHomAlong` (READING `(𝔞, μ)`: `u` a tangent direction of `(𝔍.ideal|_N, d)`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.ContactEquivalenceStage

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealOrder DerivativeIdealAlong
  TangentDirectionAlong BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CoefficientIdealRestriction HomogenizedIdealAlong HomogenizedIdealAlongTower MarkedIdealEquivalence
  MarkedIdealEquivalence.MarkedIdeal CoefficientIdealAlongRestrictionFull MarkedIdealBiholomorphism
  MarkedIdealRestrictOpen MemberInterTowerAlong ContactEquivalenceAlong MaximalContactAlongTower
open HomogenizedGlueingTower (strictAlong strictAlong_step strictAlong_restrict N_geoTransformAlong)

noncomputable section

variable {n : ℕ}

/-! ### Locality of strict transforms -/

section Local

variable {X : CMfd.{u} n}

/-- **Strict transforms along a tower are local over open sets of the base**: if `A` and `B` agree on the open set `O`,
their strict transforms agree over `O`. -/
theorem strictAlong_inter_preimage_eq {O : Set X} (hO : IsOpen O) {A B : Set X} (hAB : A ∩ O = B ∩ O) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → strictAlong T A ∩ T.proj ⁻¹' O = strictAlong T B ∩ T.proj ⁻¹' O
  | _, .refl => hAB
  | _, .step T C π hπ => by
      rw [strictAlong_step, strictAlong_step, BlowupTower.proj_step, preimage_comp]
      exact MaximalContactTower.geoStrictTransform_inter_preimage hπ.contMDiff.continuous
        (hO.preimage T.contMDiff_proj.continuous) (strictAlong_inter_preimage_eq hO hAB T)

end Local

/-! ### Giraud from local hypersurfaces of maximal contact -/

section Giraud

variable {X : CMfd.{u} n} (𝔫 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔫.N) (h𝔞 : 𝔫.ideal.IsCoherent)
  (hd : 1 ≤ 𝔫.d) {S : Set X}

/-- **Centres from cosupports**: if along every multiple test blow-up the cosupports lie in the strict transforms of `S`,
so do the centres. -/
theorem centresIn_of_cosupp_subset
    (hG : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔫 T →
      (geoTransformAlong 𝔫 T).cosupp ⊆ strictAlong T S) :
    {Y : CMfd.{u} n} → (T : BlowupTower X Y) → IsGeoTestTower 𝔫 T → CentresIn S T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
      obtain ⟨hT0, hC⟩ := (isGeoTestTower_step_iff 𝔫 T C π hπ).mp hT
      exact (centresIn_step_iff S T C π hπ).mpr ⟨centresIn_of_cosupp_subset hG T hT0, hC.2.1.trans (hG T hT0)⟩

include hN h𝔞 hd in
/-- **Giraud from local hypersurfaces of maximal contact**: if every point of `N` has an open neighbourhood `O` carrying a
tangent direction `w` of `(𝔞|_N, d)` along `N` with `N ∩ V(w) ∩ O ⊆ S`, then along every multiple test blow-up the
cosupport lies in the strict transform of `S`. -/
theorem cosupp_subset_strictAlong_of_forall_exists
    (hloc : ∀ z ∈ 𝔫.N, ∃ O : Set X, z ∈ O ∧ ∃ w : X → ℂ, IsTangentDirectionAlong 𝔫.N 𝔫.ideal 𝔫.d O w ∧
      𝔫.N ∩ {x | w x = 0} ∩ O ⊆ S)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔫 T) :
    (geoTransformAlong 𝔫 T).cosupp ⊆ strictAlong T S := by
  intro p hp
  have hpN : p ∈ strictAlong T 𝔫.N := by
    rw [← N_geoTransformAlong]
    exact (geoTransformAlong 𝔫 T).cosupp_subset_N hp
  obtain ⟨O, hzO, w, hw, hsub⟩ := hloc _ (strictAlong_subset_preimage T hN.1 hpN)
  exact strictAlong_mono T hsub (cosupp_subset_strictAlong_along 𝔫 hN h𝔞 hd hw T hT ⟨hp, hzO⟩)

include hN h𝔞 hd in
/-- **The reduction to a closed submanifold containing the cosupports** (Włodarczyk `le:codim2`, with the hypersurface of
maximal contact replaced by any closed submanifold `S ⊆ N` in whose strict transforms the cosupports lie along every
multiple test blow-up): `𝔫 ≃ 𝓒_N(𝔫)|_S`. -/
theorem wEquiv_withN_coeffMarkedAlong_of_cosupp_subset (hS : IsClosedSubmanifold n S) (hSN : S ⊆ 𝔫.N)
    (hG : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔫 T →
      (geoTransformAlong 𝔫 T).cosupp ⊆ strictAlong T S) :
    WEquiv 𝔫 (withN (coeffMarkedAlong 𝔫) S) := by
  refine ⟨rfl, fun T => ⟨⟨fun hT => ?_, fun hT => ?_⟩, fun hT => ?_⟩⟩
  · exact (coeffAlong_restrict_tower_iff 𝔫 hN h𝔞 hd hS hSN T).1.mpr ⟨hT, centresIn_of_cosupp_subset 𝔫 hG T hT⟩
  · exact ((coeffAlong_restrict_tower_iff 𝔫 hN h𝔞 hd hS hSN T).1.mp hT).1
  · rw [cosupp_coeffAlong_withN_tower 𝔫 hN h𝔞 hd hS hSN T hT (centresIn_of_cosupp_subset 𝔫 hG T hT)]
    exact (inter_eq_left.mpr (hG T hT)).symm

/-- **The cosupport condition passes to equivalent marked ideals.** -/
theorem cosupp_subset_of_wEquiv {𝔫' : MarkedIdeal n X} (h : WEquiv 𝔫' 𝔫)
    (hG : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔫 T →
      (geoTransformAlong 𝔫 T).cosupp ⊆ strictAlong T S)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔫' T) :
    (geoTransformAlong 𝔫' T).cosupp ⊆ strictAlong T S := by
  rw [(h.2 T).2 hT]
  exact hG T ((h.2 T).1.mp hT)

end Giraud

/-! ### The tangent directions at a later stage -/

section Stage

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔪.N) (h𝔞 : 𝔪.ideal.IsCoherent)
  (hd : 1 ≤ 𝔪.d) (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔪.N 𝔪.ideal 𝔪.d U u)
  {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower 𝔪 T₀)

include hN h𝔞 hd hu hT₀ in
/-- **The tangent directions at the stage `T₀`**: every point `z ∈ N_{T₀}` over `U` has an open neighbourhood `W` over `U`
carrying a tangent direction `w` of `(𝔞_{T₀}|_{N_{T₀}}, d)` along `N_{T₀}` with `N_{T₀} ∩ V(w) ∩ W = (N ∩ V(u))_{T₀} ∩ W`
(TN-CLASSICAL's `MaximalContactAlongTower.exists_contact_along`, made a genuine tangent direction by
`ContactEquivalenceAlong.exists_isTangentDirectionAlong_of_isInSpanOnAt`, and the locality of strict transforms). -/
theorem exists_isTangentDirectionAlong_stage {z : Y} (hzN : z ∈ (geoTransformAlong 𝔪 T₀).N) (hzU : T₀.proj z ∈ U) :
    ∃ W : Opens Y, z ∈ W ∧ (W : Set Y) ⊆ T₀.proj ⁻¹' U ∧ ∃ w : Y → ℂ,
      IsTangentDirectionAlong (geoTransformAlong 𝔪 T₀).N (geoTransformAlong 𝔪 T₀).ideal
        (geoTransformAlong 𝔪 T₀).d W w ∧
      (geoTransformAlong 𝔪 T₀).N ∩ {x | w x = 0} ∩ W = strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ∩ W := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T₀ hT₀
  have hdT : (geoTransformAlong 𝔪 T₀).d = 𝔪.d := d_geoTransformAlong 𝔪 T₀
  obtain ⟨O, w₀, hzO, hOo, hOU, hw₀, hw₀D, hw₀1, hw₀A⟩ := exists_contact_along 𝔪 hN h𝔞 hd hu T₀ hT₀ z hzN hzU
  rw [← hdT] at hw₀D
  obtain ⟨W, hzW, hWO, w, hw, hagree⟩ :=
    exists_isTangentDirectionAlong_of_isInSpanOnAt hcT hNT hOo hw₀ hw₀D hw₀1 hzO hzN
  refine ⟨W, hzW, hWO.trans hOU, w, hw, ?_⟩
  -- locality of the strict transform over `U`
  have hloc : strictAlong T₀ (𝔪.N ∩ {x | u x = 0} ∩ U) ∩ T₀.proj ⁻¹' U =
      strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' U :=
    strictAlong_inter_preimage_eq U.isOpen (by rw [inter_assoc, inter_self]) T₀
  ext y
  constructor
  · rintro ⟨⟨hyN, hy0⟩, hyW⟩
    have hyO := hWO hyW
    have hyA : y ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0} ∩ U) := by
      refine (hw₀A y hyO hyN).mp ?_
      rw [← hagree y hyW hyN]
      exact hy0
    have h1 : y ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0} ∩ U) ∩ T₀.proj ⁻¹' U := ⟨hyA, hOU hyO⟩
    rw [hloc] at h1
    exact ⟨h1.1, hyW⟩
  · rintro ⟨hyS, hyW⟩
    have hyO := hWO hyW
    have hyN : y ∈ (geoTransformAlong 𝔪 T₀).N :=
      strictAlong_subset_N 𝔪 (fun x hx => hx.1) T₀ hyS
    have h1 : y ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ∩ T₀.proj ⁻¹' U := ⟨hyS, hOU hyO⟩
    rw [← hloc] at h1
    have hyA := h1.1
    refine ⟨⟨hyN, ?_⟩, hyW⟩
    show w y = 0
    rw [hagree y hyW hyN]
    exact (hw₀A y hyO hyN).mpr hyA

include hN h𝔞 hd hu hT₀ in
/-- **The strict transform of the hypersurface of maximal contact is a closed submanifold over `U`**:
`(N ∩ V(u))_{T₀}` meets `V = T₀⁻¹U` in a closed submanifold of `V` (near each of its points it is `N_{T₀} ∩ V(w)` for a
tangent direction `w`, `exists_isTangentDirectionAlong_stage`). -/
theorem isClosedSubmanifold_strictAlong_stage :
    IsClosedSubmanifold n ((Subtype.val : openPreimage T₀ U → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T₀ hT₀
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT
  have hSN : strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ⊆ (geoTransformAlong 𝔪 T₀).N :=
    strictAlong_subset_N 𝔪 (fun x hx => hx.1) T₀
  refine ⟨isClosed_of_closure_subset fun y hy => ?_, fun y hy => ?_⟩
  · have hyN : (y : Y) ∈ (geoTransformAlong 𝔪 T₀).N := by
      have h1 : y ∈ closure ((Subtype.val : openPreimage T₀ U → Y) ⁻¹' (geoTransformAlong 𝔪 T₀).N) :=
        closure_mono (preimage_mono hSN) hy
      rw [(hNT.1.preimage continuous_subtype_val).closure_eq] at h1
      exact h1
    obtain ⟨W, hyW, -, w, hw, hWS⟩ := exists_isTangentDirectionAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ hyN y.2
    have hwc : ContinuousAt w (y : Y) :=
      (GiraudAlong.holomorphicAt_of_mem_iterDerivIdealAlong hhol _ y w (hw.mem y hyW)).self_of_nhds.continuousAt
    have hWy : ∀ᶠ p : openPreimage T₀ U in 𝓝 y, (p : Y) ∈ W :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds hyW)
    have hfreq : ∃ᶠ p : openPreimage T₀ U in 𝓝 y, w (p : Y) = 0 := by
      refine ((mem_closure_iff_frequently.mp hy).and_eventually hWy).mono fun p hp => ?_
      have h2 : (p : Y) ∈ strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) ∩ W := hp
      rw [← hWS] at h2
      exact h2.1.2
    have hy0 : w y = 0 := by
      have ht : Tendsto (fun p : openPreimage T₀ U => w (p : Y)) (𝓝 y) (𝓝 (w y)) :=
        hwc.comp continuous_subtype_val.continuousAt
      exact mem_singleton_iff.mp (isClosed_singleton.mem_of_frequently_of_tendsto
        (hfreq.mono fun p hp => mem_singleton_iff.mpr hp) ht)
    have h3 : (y : Y) ∈ (geoTransformAlong 𝔪 T₀).N ∩ {x | w x = 0} ∩ W := ⟨⟨hyN, hy0⟩, hyW⟩
    rw [hWS] at h3
    exact h3.1
  · obtain ⟨W, hyW, -, w, hw, hWS⟩ := exists_isTangentDirectionAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ (hSN hy) y.2
    have hy' : (y : Y) ∈ (geoTransformAlong 𝔪 T₀).N ∩ {x | w x = 0} ∩ W := by
      rw [hWS]
      exact ⟨hy, hyW⟩
    obtain ⟨k, -, hk⟩ := hw.regularAtDim_contact hhol hNT hy'
    have hk' : RegularAtDim (n := n) (strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) (y : Y) (k - 1) :=
      RegularPointDimension.regularAtDim_of_inter_eq W.isOpen hyW (by rw [inter_assoc, inter_self, hWS]) hk
    exact ⟨k - 1, AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hk'⟩

include hN h𝔞 hd hu hT₀ in
/-- **The local hypersurfaces of maximal contact on `V = T₀⁻¹U`**: the hypothesis of
`cosupp_subset_strictAlong_of_forall_exists` for `𝔪_{T₀}|_V` and `S = (N ∩ V(u))_{T₀} ∩ V` (the tangent directions of
`exists_isTangentDirectionAlong_stage`, restricted to `V`). -/
theorem forall_exists_isTangentDirectionAlong_stage_val :
    ∀ z ∈ (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔪 T₀)).N,
      ∃ O : Set (openPreimage T₀ U), z ∈ O ∧ ∃ w : openPreimage T₀ U → ℂ,
        IsTangentDirectionAlong (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔪 T₀)).N
          (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔪 T₀)).ideal
          (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔪 T₀)).d O w ∧
        (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔪 T₀)).N ∩ {x | w x = 0} ∩ O ⊆
          (Subtype.val : openPreimage T₀ U → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0}) := by
  intro z hz
  obtain ⟨-, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T₀ hT₀
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcT
  obtain ⟨W, hzW, -, w, hw, hWS⟩ := exists_isTangentDirectionAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀ hz z.2
  refine ⟨(Subtype.val : openPreimage T₀ U → Y) ⁻¹' W, hzW, w ∘ Subtype.val,
    isTangentDirectionAlong_pullback (fun y => ⟨DerivativeIdealAlongEtale.openInv (openPreimage T₀ U) y,
      DerivativeIdealAlongEtale.isLocalInverseAt_val (openPreimage T₀ U) y⟩) hhol hw, ?_⟩
  rintro p ⟨⟨hpN, hp0⟩, hpW⟩
  have h1 : (p : Y) ∈ (geoTransformAlong 𝔪 T₀).N ∩ {x | w x = 0} ∩ W := ⟨⟨hpN, hp0⟩, hpW⟩
  rw [hWS] at h1
  exact h1.1

include hN h𝔞 hd hu hT₀ in
/-- **The contact equivalence at the stage `T₀`, for every marked ideal equivalent to `𝔪_{T₀}` over `V`**: let `𝔫` have
the submanifold `N` of `𝔪` (closed submanifold, coherent ideal, mark `≥ 1`), let `T₀` be a multiple test blow-up of `𝔫`,
and assume `𝔫_{T₀}|_V ≃ 𝔪_{T₀}|_V` on `V = T₀⁻¹U`.  Then
`𝔫_{T₀}|_V ≃ (𝓒_{N_{T₀}}(𝔫_{T₀})|_{(N ∩ V(u))_{T₀}})|_V`.  (With `𝔫 = 𝔪` this is `wEquiv_stage`.) -/
theorem wEquiv_stage_of_wEquiv (𝔫 : MarkedIdeal n X) (hN𝔫 : IsClosedSubmanifold n 𝔫.N) (h𝔫 : 𝔫.ideal.IsCoherent)
    (hd𝔫 : 1 ≤ 𝔫.d) (hNN : 𝔫.N = 𝔪.N) (hT₀𝔫 : IsGeoTestTower 𝔫 T₀)
    (h : WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔫 T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔪 T₀))) :
    WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔫 T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong 𝔫 T₀)) (strictAlong T₀ (𝔪.N ∩ {x | u x = 0})))) := by
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN h𝔞 T₀ hT₀
  obtain ⟨hNT𝔫, hcT𝔫⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN𝔫 h𝔫 T₀ hT₀𝔫
  have hdT𝔫 : 1 ≤ (geoTransformAlong 𝔫 T₀).d := by rw [d_geoTransformAlong]; exact hd𝔫
  have hdT : 1 ≤ (geoTransformAlong 𝔪 T₀).d := by rw [d_geoTransformAlong]; exact hd
  set V := openPreimage T₀ U with hVdef
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : V → Y) := contMDiff_subtype_val
  -- the restricted marked ideals
  have hNV : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔪 T₀)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNT V
  have hcV : (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔪 T₀)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval hcT
  have hNV𝔫 : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔫 T₀)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNT𝔫 V
  have hcV𝔫 : (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔫 T₀)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback hval hcT𝔫
  -- the closed submanifold `S`
  have hS := isClosedSubmanifold_strictAlong_stage 𝔪 hN h𝔞 hd U hu T₀ hT₀
  have hSN : ((Subtype.val : V → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) ⊆
      (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔫 T₀)).N := by
    refine preimage_mono ?_
    rw [N_geoTransformAlong, hNN]
    exact strictAlong_mono T₀ (fun x hx => hx.1)
  -- Giraud for `𝔪_{T₀}|_V`, then for `𝔫_{T₀}|_V`
  have hG𝔪 : ∀ {Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) V) Z),
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔪 T₀)) T →
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔪 T₀)) T).cosupp ⊆
        strictAlong T ((Subtype.val : V → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) :=
    fun T hT => cosupp_subset_strictAlong_of_forall_exists (X := CMfd.of (n := n) V) _ hNV hcV hdT
      (forall_exists_isTangentDirectionAlong_stage_val 𝔪 hN h𝔞 hd U hu T₀ hT₀) T hT
  have hG𝔫 : ∀ {Z : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) V) Z),
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔫 T₀)) T →
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔫 T₀)) T).cosupp ⊆
        strictAlong T ((Subtype.val : V → Y) ⁻¹' strictAlong T₀ (𝔪.N ∩ {x | u x = 0})) :=
    fun T hT => cosupp_subset_of_wEquiv (X := CMfd.of (n := n) V) _ h (fun T' hT' => hG𝔪 T' hT') T hT
  have hW := wEquiv_withN_coeffMarkedAlong_of_cosupp_subset (X := CMfd.of (n := n) V)
    (MarkedIdeal.pullback (Subtype.val : V → Y) (geoTransformAlong 𝔫 T₀)) hNV𝔫 hcV𝔫 hdT𝔫 hS hSN
    (fun T hT => hG𝔫 T hT)
  rw [← pullback_val_coeffMarkedAlong V _ hcT𝔫 hNT𝔫 hdT𝔫] at hW
  exact hW

include hN h𝔞 hd hu hT₀ in
/-- **The contact equivalence at the stage `T₀`** (Włodarczyk `le:codim2` at the stage where Step 1bb forms its restricted
marked ideal): for `𝔪` with `N` a closed submanifold, `𝔞` coherent, `d ≥ 1`, a tangent direction `u` of `(𝔞|_N, d)` along
`N` on an open `U` and a multiple test blow-up `T₀` of `𝔪`, over `V = T₀⁻¹U`:
`𝔪_{T₀}|_V ≃ (𝓒_{N_{T₀}}(𝔪_{T₀})|_{(N ∩ V(u))_{T₀}})|_V`. -/
theorem wEquiv_stage :
    WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔪 T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong 𝔪 T₀)) (strictAlong T₀ (𝔪.N ∩ {x | u x = 0})))) :=
  wEquiv_stage_of_wEquiv 𝔪 hN h𝔞 hd U hu T₀ hT₀ 𝔪 hN h𝔞 hd rfl hT₀ (WEquiv.refl _)

end Stage

/-! ### Equivalences over an open set pass to the stages -/

section Restrict

variable {X : CMfd.{u} n}

/-- **Equivalence over `U` passes to the stages over `T⁻¹U`**: if `𝔫|_U ≃ 𝔪|_U` and `T` is a multiple test blow-up of both,
then `𝔫_T|_{T⁻¹U} ≃ 𝔪_T|_{T⁻¹U}` (`MarkedIdealRestrictOpen.geoTransformAlong_restrict`). -/
theorem wEquiv_pullback_val_geoTransformAlong {𝔫 𝔪 : MarkedIdeal n X} (hN𝔫 : IsClosedSubmanifold n 𝔫.N)
    (h𝔫 : 𝔫.ideal.IsCoherent) (hN𝔪 : IsClosedSubmanifold n 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent) (U : Opens X)
    (hU : WEquiv (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔫)
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT𝔫 : IsGeoTestTower 𝔫 T) (hT𝔪 : IsGeoTestTower 𝔪 T) :
    WEquiv (X := CMfd.of (n := n) (openPreimage T U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong 𝔫 T))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong 𝔪 T)) := by
  have h := hU.geoTransformAlong (isGeoTestTower_restrict U hN𝔫 h𝔫 T hT𝔫)
  rwa [geoTransformAlong_restrict U hN𝔫 h𝔫 T hT𝔫, geoTransformAlong_restrict U hN𝔪 h𝔪 T hT𝔪] at h

/-- **The tails of a segment**: let `𝔰` be a marked ideal on `V = T₀⁻¹U` equivalent to `𝔫_{T₀}|_V`.  If `T₀ T₁` is a
multiple test blow-up of `𝔫`, then `T₁|_V` is a multiple test blow-up of `𝔰`, and along it the cosupport of `𝔰` is the trace
of `cosupp 𝔫_{T₀ T₁}`. -/
theorem isGeoTestTower_tail_of_wEquiv {𝔫 : MarkedIdeal n X} (hN𝔫 : IsClosedSubmanifold n 𝔫.N)
    (h𝔫 : 𝔫.ideal.IsCoherent) (U : Opens X) {Y Z : CMfd.{u} n} (T₀ : BlowupTower X Y) (T₁ : BlowupTower Y Z)
    {𝔰 : MarkedIdeal n (CMfd.of (n := n) (openPreimage T₀ U))}
    (h : WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y) (geoTransformAlong 𝔫 T₀)) 𝔰)
    (hT : IsGeoTestTower 𝔫 (T₀.append T₁)) :
    IsGeoTestTower 𝔰 (restrict (openPreimage T₀ U) T₁) ∧
      (geoTransformAlong 𝔰 (restrict (openPreimage T₀ U) T₁)).cosupp =
        (Subtype.val : openPreimage T₁ (openPreimage T₀ U) → Z) ⁻¹' (geoTransformAlong 𝔫 (T₀.append T₁)).cosupp := by
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff 𝔫 T₀ T₁).mp hT
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hN𝔫 h𝔫 T₀ hT₀
  obtain ⟨-, hcTT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hNT hcT T₁ hT₁
  have hR := isGeoTestTower_restrict (openPreimage T₀ U) hNT hcT T₁ hT₁
  refine ⟨(h.2 _).1.mp hR, ?_⟩
  rw [← (h.2 _).2 hR, geoTransformAlong_restrict (openPreimage T₀ U) hNT hcT T₁ hT₁,
    cosupp_pullback_val _ (MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent hcTT), geoTransformAlong_append]

end Restrict

/-! ### The instance `J̄ = 𝓒_N(𝓗_N(𝔞), μ)` of Step 1b -/

section CoeffHom

open HomogenizedGlueingAlongTower (homogenizedMarkedAlong)
open ContactIndependenceAlong (coeffHom_basic)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M} {μ : ℕ}

/-- `𝓗_N` of the marked ideal `(M, N, ∅, 𝔞, μ)` is `homogenizedMarkedAlong N 𝔞 μ`. -/
theorem homMarkedAlong_mk : homMarkedAlong (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) = homogenizedMarkedAlong N 𝔞 μ := rfl

/-- **`J̄|_U ≃ (𝔞, μ)|_U`** on every open `U` (`J̄ = 𝓒_N(𝓗_N(𝔞), μ)`; `HomogenizedIdealAlongTower.coeff_homAlong_wEquiv` on
`U`, after commuting `𝓒_N` and `𝓗_N` with the restriction). -/
theorem wEquiv_pullback_val_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (U : Opens M) :
    WEquiv (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → M) (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)))
      (MarkedIdeal.pullback (Subtype.val : U → M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M)) := by
  have hH : (homogenizedMarkedAlong N 𝔞 μ).ideal.IsCoherent :=
    HomogenizedIdealAlong.isCoherent_homogenizedIdealAlong h𝔞 hN μ
  rw [pullback_val_coeffMarkedAlong U _ hH hN hμ, ← homMarkedAlong_mk,
    pullback_val_homMarkedAlong U _ h𝔞 hN hμ]
  exact coeff_homAlong_wEquiv (X := CMfd.of (n := n) U) _ (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
    (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞) hμ

/-- **The contact equivalence at the stage `T₀` for `J̄`, READING `(𝔞, μ)`** (the tangent direction lives on `(𝔞|_N, μ)` at
the start of Step 1, as in the glueing data `GlueingDataAlong N 𝔞 μ u v`; I-0981 C-0081): for `𝔞` coherent, `N` a closed
submanifold, `μ ≥ 1`, a tangent direction `u` of `(𝔞|_N, μ)` along `N` on an open `U` and a multiple test blow-up `T₀` of
`J̄ = 𝓒_N(𝓗_N(𝔞), μ)`, over `V = T₀⁻¹U`:

  `J̄_{T₀}|_V ≃ 𝓢_{u,T₀}|_V`,  `𝓢_{u,T₀} = 𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}}`,

the marked ideal transported by `BlowupTowerIsoTail.exists_isTowerIso_tail_coeffHom`.  (Through `J̄ ≃ (𝔞, μ)`: Giraud for
the transform of `(𝔞, μ)` at `T₀`, transferred to `J̄_{T₀}` along the equivalence over `U`.) -/
theorem wEquiv_stage_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (U : Opens M)
    {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {Y : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀) :
    WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
          (strictAlong T₀ (N ∩ {x | u x = 0})))) := by
  obtain ⟨hJN, hJc, hJd⟩ := coeffHom_basic (μ := μ) h𝔞 hN
  have hW : WEquiv (X := CMfd.of (n := n) M) (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ))
      (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) :=
    coeff_homAlong_wEquiv (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ
  have hT₀a : IsGeoTestTower (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) T₀ := (hW.2 T₀).1.mp hT₀
  exact wEquiv_stage_of_wEquiv (X := CMfd.of (n := n) M) (⟨N, [], 𝔞, μ⟩ : MarkedIdeal n M) hN h𝔞 hμ U hu T₀ hT₀a
    _ hJN hJc hJd rfl hT₀
    (wEquiv_pullback_val_geoTransformAlong hJN hJc hN h𝔞 U (wEquiv_pullback_val_coeffHom h𝔞 hN hμ U) T₀ hT₀ hT₀a)

/-- **The form asked for in I-0981 C-0081**: every point `z` over `U` has an open neighbourhood `W ⊆ T₀⁻¹U` with
`J̄_{T₀}|_W ≃ 𝓢_{u,T₀}|_W` (READING `(𝔞, μ)`; `W = T₀⁻¹U` itself). -/
theorem exists_wEquiv_stage_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (U : Opens M)
    {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {Y : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀) {z : Y} (hz : z ∈ openPreimage T₀ U) :
    ∃ W : Opens Y, z ∈ W ∧ (W : Set Y) ⊆ openPreimage T₀ U ∧
      WEquiv (X := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → Y)
          (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
        (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
            (strictAlong T₀ (N ∩ {x | u x = 0})))) :=
  ⟨openPreimage T₀ U, hz, subset_rfl, wEquiv_stage_coeffHom h𝔞 hN hμ U hu T₀ hT₀⟩

/-- **The contact equivalence at the stage `T₀` for `J̄`, READING `J̄`** (Włodarczyk's text, Step 1bb: "find a tangent
direction `u ∈ 𝒟^{μ̄-1}(J̄)`"): for a tangent direction `u` of `J̄` itself along `N` on `U`, `J̄_{T₀}|_V ≃ 𝓢_{u,T₀}|_V`
(`wEquiv_stage` with `𝔪 = J̄`).  The glueing data of `BlowupTowerIsoTail` glue tangent directions of `(𝔞, μ)`; this
reading composes with them only when `J̄` is itself the homogenized ideal being glued. -/
theorem wEquiv_stage_coeffHom_of_isTangentDirectionAlong_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    (U : Opens M) {u : M → ℂ}
    (hu : IsTangentDirectionAlong N (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)).ideal
      (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)).d U u)
    {Y : CMfd.{u} n} (T₀ : BlowupTower (CMfd.of (n := n) M) Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀) :
    WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
          (strictAlong T₀ (N ∩ {x | u x = 0})))) := by
  obtain ⟨hJN, hJc, hJd⟩ := coeffHom_basic (μ := μ) h𝔞 hN
  exact wEquiv_stage (X := CMfd.of (n := n) M) _ hJN hJc hJd U hu T₀ hT₀

/-- **The tails of the segment for `J̄`** (READING `(𝔞, μ)`): if `T₀ T₁` is a multiple test blow-up of `J̄`, then `T₁|_V` is a
multiple test blow-up of `𝓢_{u,T₀}|_V` (`V = T₀⁻¹U`), and along it the cosupport of `𝓢_{u,T₀}|_V` is the trace of
`cosupp J̄_{T₀ T₁}`.  With `BlowupTowerIsoTail.exists_isTowerIso_tail_coeffHom` (whose tail isomorphism fixes
`cosupp J̄_{T₀ T₁}` pointwise) this gives the hypotheses on `𝓢_{u,T₀}` of property (6) of `hir:centre-function` along the
tails. -/
theorem isGeoTestTower_tail_coeffHom (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (hμ : 1 ≤ μ) (U : Opens M)
    {u : M → ℂ} (hu : IsTangentDirectionAlong N 𝔞 μ U u) {Y Z : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) M) Y) (T₁ : BlowupTower Y Z)
    (hT : IsGeoTestTower (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (T₀.append T₁)) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
          (strictAlong T₀ (N ∩ {x | u x = 0})))) (restrict (openPreimage T₀ U) T₁) ∧
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) T₀))
          (strictAlong T₀ (N ∩ {x | u x = 0})))) (restrict (openPreimage T₀ U) T₁)).cosupp =
        (Subtype.val : openPreimage T₁ (openPreimage T₀ U) → Z) ⁻¹'
          (geoTransformAlong (coeffMarkedAlong (homogenizedMarkedAlong N 𝔞 μ)) (T₀.append T₁)).cosupp := by
  obtain ⟨hJN, hJc, -⟩ := coeffHom_basic (μ := μ) h𝔞 hN
  exact isGeoTestTower_tail_of_wEquiv (X := CMfd.of (n := n) M) hJN hJc U T₀ T₁
    (wEquiv_stage_coeffHom h𝔞 hN hμ U hu T₀ ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1) hT

end CoeffHom

/-! ### The instance `J̄ = 𝓒_N(𝓗_N(𝔍))` for a marked ideal `𝔍` with any divisor -/

section CoeffHomAlong

open ContactIndependenceAlong (one_le_coeffMarkedAlong_d)

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
  (hd : 1 ≤ 𝔍.d)

include hN h𝔞 hd in
/-- **`𝓒_N(𝓗_N(𝔍))|_U ≃ 𝔍|_U`** on every open `U`, for any divisor `E` of `𝔍`. -/
theorem wEquiv_pullback_val_coeffHomAlong (U : Opens X) :
    WEquiv (X := CMfd.of (n := n) U)
      (MarkedIdeal.pullback (Subtype.val : U → X) (coeffMarkedAlong (homMarkedAlong 𝔍)))
      (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) := by
  have hH : (homMarkedAlong 𝔍).ideal.IsCoherent := isCoherent_homMarkedAlong h𝔞 hN
  rw [pullback_val_coeffMarkedAlong U _ hH hN hd, pullback_val_homMarkedAlong U _ h𝔞 hN hd]
  exact coeff_homAlong_wEquiv (X := CMfd.of (n := n) U) _ (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U)
    (GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔞) hd

include hN h𝔞 hd in
/-- **The contact equivalence at the stage `T₀` for `J̄ = 𝓒_N(𝓗_N(𝔍))`, any divisor `E`** (READING `(𝔞, μ)` with the
divisor of the Step 1 marked ideal kept, I-0981 C-0087 (b)): for a tangent direction `u` of `(𝔍.ideal|_N, d)` along `N` on
an open `U` and a multiple test blow-up `T₀` of `J̄`, over `V = T₀⁻¹U`: `J̄_{T₀}|_V ≃ 𝓢_{u,T₀}|_V` with
`𝓢_{u,T₀} = 𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩ V(u))_{T₀}}` (both with the divisor `E_{T₀}` of `J̄_{T₀}`). -/
theorem wEquiv_stage_coeffHomAlong (U : Opens X) {u : X → ℂ} (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u)
    {Y : CMfd.{u} n} (T₀ : BlowupTower X Y) (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) :
    WEquiv (X := CMfd.of (n := n) (openPreimage T₀ U))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) := by
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  have hW := coeff_homAlong_wEquiv 𝔍 hN h𝔞 hd
  have hT₀a : IsGeoTestTower 𝔍 T₀ := (hW.2 T₀).1.mp hT₀
  exact wEquiv_stage_of_wEquiv 𝔍 hN h𝔞 hd U hu T₀ hT₀a _ hJN hJc (one_le_coeffMarkedAlong_d _) rfl hT₀
    (wEquiv_pullback_val_geoTransformAlong hJN hJc hN h𝔞 U (wEquiv_pullback_val_coeffHomAlong 𝔍 hN h𝔞 hd U) T₀ hT₀
      hT₀a)

include hN h𝔞 hd in
/-- **The form of I-0981 C-0081 for `J̄ = 𝓒_N(𝓗_N(𝔍))`, any divisor**: every point over `U` has an open neighbourhood
`W ⊆ T₀⁻¹U` with `J̄_{T₀}|_W ≃ 𝓢_{u,T₀}|_W` (`W = T₀⁻¹U`). -/
theorem exists_wEquiv_stage_coeffHomAlong (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y : CMfd.{u} n} (T₀ : BlowupTower X Y)
    (hT₀ : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀) {z : Y} (hz : z ∈ openPreimage T₀ U) :
    ∃ W : Opens Y, z ∈ W ∧ (W : Set Y) ⊆ openPreimage T₀ U ∧
      WEquiv (X := CMfd.of (n := n) W)
        (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
        (MarkedIdeal.pullback (Subtype.val : W → Y)
          (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
            (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) :=
  ⟨openPreimage T₀ U, hz, subset_rfl, wEquiv_stage_coeffHomAlong 𝔍 hN h𝔞 hd U hu T₀ hT₀⟩

include hN h𝔞 hd in
/-- **The tails of the segment for `J̄ = 𝓒_N(𝓗_N(𝔍))`, any divisor**: if `T₀ T₁` is a multiple test blow-up of `J̄`, then
`T₁|_V` is one of `𝓢_{u,T₀}|_V` and its cosupport along it is the trace of `cosupp J̄_{T₀ T₁}`. -/
theorem isGeoTestTower_tail_coeffHomAlong (U : Opens X) {u : X → ℂ}
    (hu : IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U u) {Y Z : CMfd.{u} n} (T₀ : BlowupTower X Y)
    (T₁ : BlowupTower Y Z) (hT : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T₁)) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict (openPreimage T₀ U) T₁) ∧
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : openPreimage T₀ U → Y)
        (withN (coeffMarkedAlong (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T₀))
          (strictAlong T₀ (𝔍.N ∩ {x | u x = 0})))) (restrict (openPreimage T₀ U) T₁)).cosupp =
        (Subtype.val : openPreimage T₁ (openPreimage T₀ U) → Z) ⁻¹'
          (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) (T₀.append T₁)).cosupp := by
  have hJN : IsClosedSubmanifold n (coeffMarkedAlong (homMarkedAlong 𝔍)).N := hN
  have hJc : (coeffMarkedAlong (homMarkedAlong 𝔍)).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN
  exact isGeoTestTower_tail_of_wEquiv hJN hJc U T₀ T₁
    (wEquiv_stage_coeffHomAlong 𝔍 hN h𝔞 hd U hu T₀ ((isGeoTestTower_append_iff _ T₀ T₁).mp hT).1) hT

end CoeffHomAlong

end

end Hironaka.ContactEquivalenceStage
