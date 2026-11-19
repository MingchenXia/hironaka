import Hironaka.Resolution.HironakaG8LocalStable
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCoefficientIdeals

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Transport of the local equivalences along biholomorphisms and to arbitrary opens of a stage (G8 lane, run 0080, round 6)

Blueprint: `hironaka-g8-resume-local-transport.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` §6c (module 6,
item (i): "a TRANSPORT of `LocEquiv` along `MaxLocusLocal.nestedOpensDiffeo`"), lane G11B's inbox item I-1348 (a).

The local equivalences `LocEquiv κ` of `HironakaG8LocalHistory` restrict to open subsets (`LocEquiv.restrict`), but an open
`V` of an open `W` of `Y` is a different manifold from the open `V` of `Y` (`CMfd.of (nestedOpens W V)` versus
`CMfd.of V`); the two are biholomorphic (`MaxLocusLocal.nestedOpensDiffeo`).  This module transports the local
equivalences along biholomorphisms, by the coinduction principle `HironakaG8LocalStable.LocEquiv.of_isLocStable`:

* `prodLineDiffeo Φ`, `restrictDiffeo Φ U`: a biholomorphism `Φ : Y' ≅ Y` induces biholomorphisms of the products with a
  line and of corresponding open subsets; `projectionTest_pullback`, `pullback_val_pullback_diffeo`: the test actions
  commute with the pullback along `Φ` (coherent ideals);
* `DiffeoRel κ`: "pullback along a biholomorphism of a locally equivalent pair with coherent ideals";
  `isLocStable_diffeoRel` (a blowup of the pulled-back pair is a blowup of the original pair along the composite, so it lands
  in `LocEquiv κ` itself);
* **`LocEquiv.pullback_diffeo`** (kinds without exceptional blowups, coherent ideals):
  `LocEquiv κ M M' → LocEquiv κ (Φ^*M) (Φ^*M')`; **`LocEquiv.pullback_diffeo_iff`**;
* **`LocEquiv.restrict_of_le`**: if the restrictions of `A`, `B` to an open `W` of `Y` are locally equivalent, so are their
  restrictions to every open `V ⊆ W` of `Y` (as marked ideals on `CMfd.of V`, not on `CMfd.of (nestedOpens W V)`).

Sorry-free.  Universe-polymorphic.  Import discipline: no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8LocalTransport

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism
  Hironaka.HironakaG8LocalHistory Hironaka.HironakaG8LocalStable
open Hironaka.HironakaActualProjectionTestRecord (projectionTest projectionAmbient horizontal)
open Hironaka.HironakaG8MixedEquiv (withBoundary withBoundary_eq)
open Hironaka.MaxLocusLocal (nestedOpens nestedOpensDiffeo pullback_symm_nestedOpensDiffeo)
open scoped ProductComplexManifold

noncomputable section

/-! ### Biholomorphisms of products with a line and of open subsets -/

section Diffeos

variable {m : ℕ} {Y Y' : CMfd.{u} m}

/-- **The product of a biholomorphism with the identity of the line.** -/
def prodLineDiffeo (Φ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Y) :
    projectionAmbient Y' ≃ₘ⟮𝓘(ℂ, ComplexModel (m + 1)), 𝓘(ℂ, ComplexModel (m + 1))⟯ projectionAmbient Y where
  toFun p := (Φ p.1, p.2)
  invFun p := (Φ.symm p.1, p.2)
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := ProductComplexManifold.contMDiff_prodMap (n := m) (m := 1) Φ.contMDiff contMDiff_id
  contMDiff_invFun := ProductComplexManifold.contMDiff_prodMap (n := m) (m := 1) Φ.symm.contMDiff contMDiff_id

/-- The open of `Y` corresponding to an open `U` of `Y'` under `Φ`. -/
def imageOpen (Φ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Y) (U : Opens Y') : Opens Y :=
  ⟨Φ.symm ⁻¹' (U : Set Y'), U.isOpen.preimage Φ.symm.continuous⟩

theorem mem_imageOpen_iff (Φ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Y) (U : Opens Y') (q : Y') :
    Φ q ∈ imageOpen Φ U ↔ q ∈ U := by
  show Φ.symm (Φ q) ∈ (U : Set Y') ↔ q ∈ U
  rw [Diffeomorph.symm_apply_apply]
  rfl

/-- **The restriction of a biholomorphism to corresponding open subsets.** -/
def restrictDiffeo (Φ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Y) (U : Opens Y') :
    CMfd.of (n := m) U ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ CMfd.of (n := m) (imageOpen Φ U) where
  toFun q := ⟨Φ q.1, (mem_imageOpen_iff Φ U q.1).mpr q.2⟩
  invFun p := ⟨Φ.symm p.1, p.2⟩
  left_inv q := Subtype.ext (Φ.symm_apply_apply q.1)
  right_inv p := Subtype.ext (Φ.apply_symm_apply p.1)
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (Φ.contMDiff.comp contMDiff_subtype_val)
    fun q => (mem_imageOpen_iff Φ U q.1).mpr q.2
  contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk (Φ.symm.contMDiff.comp contMDiff_subtype_val)
    fun p => p.2

/-- **The product with a line commutes with the pullback along a biholomorphism** (coherent ideal). -/
theorem projectionTest_pullback (Φ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Y) {P : MarkedIdeal m Y}
    (hP : P.ideal.IsCoherent) :
    projectionTest (MarkedIdeal.pullback Φ P) = MarkedIdeal.pullback (prodLineDiffeo Φ) (projectionTest P) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · show (P.E.map ((Φ : Y' → Y) ⁻¹' ·)).map ((Prod.fst : projectionAmbient Y' → Y') ⁻¹' ·) ++ [horizontal Y'] =
      (P.E.map ((Prod.fst : projectionAmbient Y → Y) ⁻¹' ·) ++ [horizontal Y]).map ((prodLineDiffeo Φ) ⁻¹' ·)
    rw [List.map_append, List.map_map, List.map_map]
    rfl
  · show GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y' → Y') (GermIdeal.pullback (m := m) Φ P.ideal) =
      GermIdeal.pullback (m := m + 1) (prodLineDiffeo Φ)
        (GermIdeal.pullback (m := m + 1) (Prod.fst : projectionAmbient Y → Y) P.ideal)
    have hfst' : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel m) ∞ (Prod.fst : projectionAmbient Y' → Y') :=
      ProductComplexManifold.contMDiff_fst (n := m) (m := 1)
    have hfst : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel m) ∞ (Prod.fst : projectionAmbient Y → Y) :=
      ProductComplexManifold.contMDiff_fst (n := m) (m := 1)
    rw [← HironakaSmoothSubmersionContactParameterCoefficientIdeals.coherent_parameter_pullback_comp (X := Y) (Y := Y')
      (Z := projectionAmbient Y') Φ.contMDiff hfst' P.ideal hP,
      ← HironakaSmoothSubmersionContactParameterCoefficientIdeals.coherent_parameter_pullback_comp (X := Y)
      (Y := projectionAmbient Y) (Z := projectionAmbient Y') hfst (prodLineDiffeo Φ).contMDiff P.ideal hP]
    rfl

/-- **Restriction to an open subset commutes with the pullback along a biholomorphism** (coherent ideal). -/
theorem pullback_val_pullback_diffeo (Φ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Y) {P : MarkedIdeal m Y}
    (hP : P.ideal.IsCoherent) (U : Opens Y') :
    MarkedIdeal.pullback (Subtype.val : U → Y') (MarkedIdeal.pullback Φ P) =
      MarkedIdeal.pullback (restrictDiffeo Φ U) (MarkedIdeal.pullback (Subtype.val : imageOpen Φ U → Y) P) := by
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl ?_ ?_ rfl
  · show (P.E.map ((Φ : Y' → Y) ⁻¹' ·)).map ((Subtype.val : U → Y') ⁻¹' ·) =
      (P.E.map ((Subtype.val : imageOpen Φ U → Y) ⁻¹' ·)).map ((restrictDiffeo Φ U) ⁻¹' ·)
    rw [List.map_map, List.map_map]
    rfl
  · show GermIdeal.pullback (m := m) (Subtype.val : U → Y') (GermIdeal.pullback (m := m) Φ P.ideal) =
      GermIdeal.pullback (m := m) (restrictDiffeo Φ U)
        (GermIdeal.pullback (m := m) (Subtype.val : imageOpen Φ U → Y) P.ideal)
    rw [← GermIdealTotalTransform.pullback_comp Φ.contMDiff contMDiff_subtype_val hP,
      ← GermIdealTotalTransform.pullback_comp contMDiff_subtype_val (restrictDiffeo Φ U).contMDiff hP]
    rfl

/-- **Pulling back along `Φ` and then along `Φ⁻¹` is the identity** (coherent ideal). -/
theorem pullback_symm_pullback (Φ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Y) {P : MarkedIdeal m Y}
    (hP : P.ideal.IsCoherent) : MarkedIdeal.pullback Φ.symm (MarkedIdeal.pullback Φ P) = P := by
  obtain ⟨N, E, I, d⟩ := P
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of ?_ ?_ ?_ rfl
  · exact MarkedIdealTowerTransport.symm_preimage_preimage Φ N
  · exact MarkedIdealTowerTransport.map_symm_preimage_map_preimage Φ E
  · show GermIdeal.pullback (m := m) Φ.symm (GermIdeal.pullback (m := m) Φ I) = I
    rw [← GermIdealTotalTransform.pullback_comp Φ.contMDiff Φ.symm.contMDiff hP]
    have hid : (Φ : Y' → Y) ∘ Φ.symm = id := funext fun y => Φ.apply_symm_apply y
    rw [hid]
    exact BlowupControlledTransform.pullback_id hP

end Diffeos

/-! ### The coinduction relation -/

section Rel

/-- **Pullback along a biholomorphism of a locally equivalent pair with coherent ideals.** -/
def DiffeoRel (κ : Kinds) {m : ℕ} {Y' : CMfd.{u} m} (P' Q' : MarkedIdeal m Y') : Prop :=
  ∃ (Y : CMfd.{u} m) (Φ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel m), 𝓘(ℂ, ComplexModel m)⟯ Y) (P Q : MarkedIdeal m Y),
    LocEquiv κ P Q ∧ P.ideal.IsCoherent ∧ Q.ideal.IsCoherent ∧
      P' = MarkedIdeal.pullback Φ P ∧ Q' = MarkedIdeal.pullback Φ Q

/-- **The relation of the coinduction is stable**: the local equivalence, or the pullback along a biholomorphism of a
locally equivalent pair with coherent ideals. -/
theorem isLocStable_diffeoRel (κ : Kinds) :
    IsLocStable.{u} κ (fun {m} {Y} P Q => LocEquiv (n := m) (X := Y) κ P Q ∨ DiffeoRel κ (m := m) (Y' := Y) P Q) where
  E_eq := by
    rintro m Y' P' Q' (h | ⟨Y, Φ, P, Q, h, -, -, rfl, rfl⟩)
    · exact h.E_eq
    · show Q.E.map ((Φ : Y' → Y) ⁻¹' ·) = P.E.map ((Φ : Y' → Y) ⁻¹' ·)
      rw [h.E_eq]
  cosupp_eq := by
    rintro m Y' P' Q' (h | ⟨Y, Φ, P, Q, h, hP, hQ, rfl, rfl⟩)
    · exact h.cosupp_eq_base
    · rw [MarkedIdealTowerTransport.cosupp_pullback_eq hP, MarkedIdealTowerTransport.cosupp_pullback_eq hQ,
        h.cosupp_eq_base]
  controlled := by
    rintro m Y' P' Q' (h | ⟨Y, Φ, P, Q, h, hP, hQ, rfl, rfl⟩) C' Z π' hπ' hC'
    · exact Or.inl ((isLocStable_locEquiv κ).controlled h C' π' hπ' hC')
    · left
      -- the centre and the blowup seen on `Y`
      have hCC : (Φ : Y' → Y) ⁻¹' (Φ.symm ⁻¹' C') = C' := by
        ext q; simp
      have hππ : (Φ.symm : Y → Y') ∘ ((Φ : Y' → Y) ∘ π') = π' := by
        funext z; simp
      have hπ : IsBlowupAlong m (Φ.symm ⁻¹' C') ((Φ : Y' → Y) ∘ π') :=
        isBlowupAlong_comp_inverse Φ.symm.contMDiff Φ.contMDiff Φ.symm_apply_apply Φ.apply_symm_apply hπ'
      have hC : P.IsAdmissibleCentre (Φ.symm ⁻¹' C') := by
        rw [← hCC] at hC'
        exact (MarkedIdealTowerTransport.isAdmissibleCentre_pullback_iff hP).mp hC'
      have eP := MarkedIdeal.geoTransform_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
        Φ.symm_apply_apply P hP (Φ.symm ⁻¹' C') hπ.contMDiff
      have eQ := MarkedIdeal.geoTransform_pullback Φ.contMDiff Φ.symm.contMDiff Φ.apply_symm_apply
        Φ.symm_apply_apply Q hQ (Φ.symm ⁻¹' C') hπ.contMDiff
      rw [hCC, hππ] at eP eQ
      rw [eP, eQ]
      exact (isLocStable_locEquiv κ).controlled h _ _ hπ hC
  projection := by
    rintro hp m Y' P' Q' (h | ⟨Y, Φ, P, Q, h, hP, hQ, rfl, rfl⟩)
    · exact Or.inl ((isLocStable_locEquiv κ).projection hp h)
    · right
      have hf : ContMDiff 𝓘(ℂ, ComplexModel (m + 1)) 𝓘(ℂ, ComplexModel m) ∞ (Prod.fst : projectionAmbient Y → Y) :=
        ProductComplexManifold.contMDiff_fst (n := m) (m := 1)
      exact ⟨_, prodLineDiffeo Φ, projectionTest P, projectionTest Q, (isLocStable_locEquiv κ).projection hp h,
        GermIdealPullbackCalculus.isCoherent_pullback hf hP, GermIdealPullbackCalculus.isCoherent_pullback hf hQ,
        projectionTest_pullback Φ hP, projectionTest_pullback Φ hQ⟩
  restrict := by
    rintro m Y' P' Q' (h | ⟨Y, Φ, P, Q, h, hP, hQ, rfl, rfl⟩) U
    · exact Or.inl (h.restrict U)
    · right
      have hval : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel m) ∞ (Subtype.val : imageOpen Φ U → Y) :=
        contMDiff_subtype_val
      exact ⟨_, restrictDiffeo Φ U, _, _, h.restrict (imageOpen Φ U),
        GermIdealPullbackCalculus.isCoherent_pullback hval hP, GermIdealPullbackCalculus.isCoherent_pullback hval hQ,
        pullback_val_pullback_diffeo Φ hP U, pullback_val_pullback_diffeo Φ hQ U⟩

end Rel

/-! ### Transport of the local equivalences -/

section Transport

variable {κ : Kinds} {n : ℕ} {X X' : CMfd.{u} n}

/-- **The local equivalences are invariant under biholomorphisms** (kinds without exceptional blowups, coherent ideals):
`LocEquiv κ M M'` implies `LocEquiv κ (Φ^*M) (Φ^*M')`. -/
theorem LocEquiv.pullback_diffeo (hexc : κ.exc = false) (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {M M' : MarkedIdeal n X} (hM : M.ideal.IsCoherent) (hM' : M'.ideal.IsCoherent) (h : LocEquiv κ M M') :
    LocEquiv κ (MarkedIdeal.pullback Φ M) (MarkedIdeal.pullback Φ M') :=
  LocEquiv.of_isLocStable (isLocStable_diffeoRel κ) hexc (Or.inr ⟨X, Φ, M, M', h, hM, hM', rfl, rfl⟩)

/-- **The local equivalences are invariant under biholomorphisms, both ways** (coherent ideals). -/
theorem LocEquiv.pullback_diffeo_iff (hexc : κ.exc = false)
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {M M' : MarkedIdeal n X} (hM : M.ideal.IsCoherent)
    (hM' : M'.ideal.IsCoherent) :
    LocEquiv κ (MarkedIdeal.pullback Φ M) (MarkedIdeal.pullback Φ M') ↔ LocEquiv κ M M' := by
  refine ⟨fun h => ?_, LocEquiv.pullback_diffeo hexc Φ hM hM'⟩
  have h' := LocEquiv.pullback_diffeo hexc Φ.symm (GermIdealPullbackCalculus.isCoherent_pullback Φ.contMDiff hM)
    (GermIdealPullbackCalculus.isCoherent_pullback Φ.contMDiff hM') h
  rwa [pullback_symm_pullback Φ hM, pullback_symm_pullback Φ hM'] at h'

/-- **Restriction to an arbitrary smaller open**: if the restrictions of `A` and `B` to an open `W` are locally equivalent,
so are their restrictions to every open `V ⊆ W` (coherent ideals; kinds without exceptional blowups). -/
theorem LocEquiv.restrict_of_le (hexc : κ.exc = false) {A B : MarkedIdeal n X} (hA : A.ideal.IsCoherent)
    (hB : B.ideal.IsCoherent) {W V : Opens X} (hVW : V ≤ W)
    (h : LocEquiv (X := CMfd.of (n := n) W) κ (MarkedIdeal.pullback (Subtype.val : W → X) A)
      (MarkedIdeal.pullback (Subtype.val : W → X) B)) :
    LocEquiv (X := CMfd.of (n := n) V) κ (MarkedIdeal.pullback (Subtype.val : V → X) A)
      (MarkedIdeal.pullback (Subtype.val : V → X) B) := by
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X) := contMDiff_subtype_val
  have hval' : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : nestedOpens W V → W) :=
    contMDiff_subtype_val
  have h1 := h.restrict (nestedOpens W V)
  have hA1 := GermIdealPullbackCalculus.isCoherent_pullback hval' (GermIdealPullbackCalculus.isCoherent_pullback hval hA)
  have hB1 := GermIdealPullbackCalculus.isCoherent_pullback hval' (GermIdealPullbackCalculus.isCoherent_pullback hval hB)
  have h2 := LocEquiv.pullback_diffeo hexc (nestedOpensDiffeo (n := n) hVW).symm hA1 hB1 h1
  rwa [pullback_symm_nestedOpensDiffeo hA hVW, pullback_symm_nestedOpensDiffeo hB hVW] at h2

/-- **The `LocWPEquiv` form** of `LocEquiv.restrict_of_le` (the relation of lane G11B's class functoriality). -/
theorem locWPEquiv_restrict_of_le {A B : MarkedIdeal n X} (hA : A.ideal.IsCoherent) (hB : B.ideal.IsCoherent)
    {W V : Opens X} (hVW : V ≤ W)
    (h : LocWPEquiv (X := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) A)
      (MarkedIdeal.pullback (Subtype.val : W → X) B)) :
    LocWPEquiv (X := CMfd.of (n := n) V) (MarkedIdeal.pullback (Subtype.val : V → X) A)
      (MarkedIdeal.pullback (Subtype.val : V → X) B) :=
  LocEquiv.restrict_of_le rfl hA hB hVW h

end Transport

end

end Hironaka.HironakaG8LocalTransport
