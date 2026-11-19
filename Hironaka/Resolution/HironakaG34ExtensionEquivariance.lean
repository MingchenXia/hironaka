import Hironaka.Resolution.HironakaG34MaskFoldEquivariance
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.StepOneTangentChange
import Hironaka.Invariant.RestrictEmptyTower

/-!
# Uniqueness of tower isomorphisms and equivariance of compact-footprint extensions (fifth brick of EQ_d)

Lane G34 (run 0080, round 9).  Blueprint: `hironaka-g34-resume-extension-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §1 (row "carrier, extension"), §2(c)(ii).

The carrier phase builds each profile-window block on a window `U`, then extends it to the whole space by the
compact-footprint extension (`HironakaCompactFootprintSharpExtension.exists_current_sharp_joint_test_extension`): a tower
`Q` over `X` with centres over a compact `K ⊆ U` and `Q|_U ≅ R` over the identity.  Equivariance of `Q` under a
biholomorphism `φ : V ≅ V'` of opens of `X` is NOT a formal consequence of that of `R` when `V ⊄ U`: it needs `φ` to
preserve `U`, and the isomorphism over `V` must be glued from the one over `U ∩ V` (given by `R`) and the trivial one off
`K`.  This module does the gluing centre by centre, using that isomorphisms of towers over a fixed base biholomorphism are
unique (universal property of each blowup).

## Main results

* **`IsTowerIso.eq_of_isTowerIso`**: two isomorphisms of the same towers over the same base biholomorphism have the same
  last-stage biholomorphism;
* `restrictBase`: the restriction of `φ : V ≅ V'` (preserving `U`) to the parts over `U`, as a biholomorphism of opens
  of `U`;
* `exists_eq_of_isTowerIso`: over `U`, an isomorphism `Q|_V ≅ Q|_{V'}` over `φ` is `e ∘ ρ ∘ e⁻¹`;
* **`exists_isTowerIso_restrict_of_extension`**: `Q|_V ≅ Q|_{V'}` over `φ` from `R|_{U ∩ V} ≅ R|_{U ∩ V'}` over the
  restriction of `φ`;
* **`isEquivariant_of_extension`**: `R` equivariant for the restricted data `(N ∩ U, E|_U)` ⇒ `Q` equivariant for
  `(N, U :: E)`; `isEquivariant_mono`.

New file; no existing statement changed; no named input.  Sorry-free.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG34ExtensionEquivariance

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerIsomorphism Hironaka.MaxLocusLocal
  Hironaka.StepOneTangentChange

noncomputable section

variable {n : ℕ}

/-- **Isomorphisms of towers over a fixed base biholomorphism are unique**: the last-stage biholomorphism of an
isomorphism of towers is determined by the base one (universal property of each blowup). -/
theorem IsTowerIso.eq_of_isTowerIso {X X' : CMfd.{u} n} {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (h : IsTowerIso Φ T' T χ) :
    ∀ {χ' : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}, IsTowerIso Φ T' T χ' → χ = χ' := by
  induction h with
  | refl => exact fun h' => h'.refl_inv.symm
  | @step Y' Y Z' Z T' T χ h C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro χ₁' h'
    obtain ⟨χ'', h'', hcomm', -⟩ := h'.step_inv
    obtain rfl := ih h''
    let ψ := χ₁'.symm.trans χ₁
    have hψ : π ∘ ψ = π := by
      funext q
      change π (χ₁ (χ₁'.symm q)) = π q
      rw [hcomm, ← hcomm', Diffeomorph.apply_symm_apply]
    have hu := (hπ.2.2.2.2 n Z π hπ.contMDiff hπ.2.2.2.1).unique ⟨ψ.contMDiff, hψ⟩ ⟨contMDiff_id, rfl⟩
    refine Diffeomorph.ext fun p => ?_
    have := congrFun hu (χ₁' p)
    change χ₁ (χ₁'.symm (χ₁' p)) = χ₁' p at this
    rwa [Diffeomorph.symm_apply_apply] at this

/-- **Equivariance is monotone in the preserved data**: equivariance for `(N, E)` gives equivariance for `(N, E')` when
every member of `E` is a member of `E'` (fewer biholomorphisms preserve more sets). -/
theorem isEquivariant_mono {X Y : CMfd.{u} n} {N : Set X} {E E' : List (Set X)} (hEE' : ∀ H ∈ E, H ∈ E')
    {T : BlowupTower X Y} (h : HironakaG34MaskFoldEquivariance.IsEquivariant N E T) :
    HironakaG34MaskFoldEquivariance.IsEquivariant N E' T :=
  fun V V' φ hφN hφH => h V V' φ hφN fun H hH => hφH H (hEE' H hH)

/-! ### Restricting a biholomorphism of opens to the part over a third open -/

section Restrict

variable {X : CMfd.{u} n} {U V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')
  (hφU : ∀ p : V, ((φ p : V') : X) ∈ U ↔ (p : X) ∈ U)

include hφU in
theorem mem_nestedOpens_iff (q : V) : q ∈ nestedOpens V (U ⊓ V) ↔ φ q ∈ nestedOpens V' (U ⊓ V') := by
  change (q : X) ∈ U ⊓ V ↔ ((φ q : V') : X) ∈ U ⊓ V'
  exact ⟨fun h => ⟨(hφU q).mpr h.1, (φ q).2⟩, fun h => ⟨(hφU q).mp h.1, q.2⟩⟩

/-- **The restriction of `φ : V ≅ V'` to the parts over `U`**, as a biholomorphism of opens of `U` (it preserves `U`). -/
def restrictBase :
    CMfd.of (n := n) (nestedOpens U (U ⊓ V)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens U (U ⊓ V')) :=
  (nestedOpensDiffeo (n := n) (inf_le_left : U ⊓ V ≤ U)).trans
    ((nestedOpensDiffeo (n := n) (inf_le_right : U ⊓ V ≤ V)).symm.trans
      ((diffeoOpens φ (nestedOpens V (U ⊓ V)) (nestedOpens V' (U ⊓ V')) (mem_nestedOpens_iff φ hφU)).trans
        ((nestedOpensDiffeo (n := n) (inf_le_right : U ⊓ V' ≤ V')).trans
          (nestedOpensDiffeo (n := n) (inf_le_left : U ⊓ V' ≤ U)).symm)))

theorem restrictBase_apply (q : nestedOpens U (U ⊓ V)) :
    (((restrictBase φ hφU q : nestedOpens U (U ⊓ V')) : U) : X) =
      ((φ ⟨(q : U), (q.2 : ((q : U) : X) ∈ U ⊓ V).2⟩ : V') : X) := rfl

end Restrict

/-! ### Comparison of a tower isomorphism with an extended one over `U` -/

section Compare

variable {X : CMfd.{u} n} {U V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')
  (hφU : ∀ p : V, ((φ p : V') : X) ∈ U ↔ (p : X) ∈ U)

/-- **Comparison over `U`**: let `Q` be a tower over `X` whose restriction to `U` is isomorphic over the identity to a tower
`R` over `U` (last-stage map `e`).  If `Q|_V ≅ Q|_{V'}` over `φ` (last-stage map `χ`) and `R|_{U ∩ V} ≅ R|_{U ∩ V'}` over
the restriction of `φ` (last-stage map `ρ`), then over `U` the map `χ` is `e ∘ ρ ∘ e⁻¹` (uniqueness of tower isomorphisms). -/
theorem exists_eq_of_isTowerIso {Y Z : CMfd.{u} n} (Q : BlowupTower X Y) (R : BlowupTower (CMfd.of (n := n) U) Z)
    {e : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage Q U)}
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) R (restrict U Q) e)
    {χ : CMfd.of (n := n) (openPreimage Q V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage Q V')}
    (hχ : IsTowerIso φ (restrict V Q) (restrict V' Q) χ)
    {ρ : CMfd.of (n := n) (openPreimage R (nestedOpens U (U ⊓ V))) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage R (nestedOpens U (U ⊓ V')))}
    (hρ : IsTowerIso (restrictBase φ hφU) (restrict (nestedOpens U (U ⊓ V)) R)
      (restrict (nestedOpens U (U ⊓ V')) R) ρ)
    (p : openPreimage Q V) (hp : Q.proj (p : Y) ∈ U) :
    ∃ r : openPreimage R (nestedOpens U (U ⊓ V)), (r : Z) = e.symm ⟨(p : Y), hp⟩ ∧
      ((χ p : openPreimage Q V') : Y) =
        ((e (ρ r : openPreimage R (nestedOpens U (U ⊓ V'))) : openPreimage Q U) : Y) := by
  have hW : ∀ q : CMfd.of (n := n) U, q ∈ nestedOpens U (U ⊓ V) ↔
      (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) q ∈ nestedOpens U (U ⊓ V) :=
    fun _ => Iff.rfl
  have hW' : ∀ q : CMfd.of (n := n) U, q ∈ nestedOpens U (U ⊓ V') ↔
      (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) q ∈ nestedOpens U (U ⊓ V') :=
    fun _ => Iff.rfl
  have EW := isTowerIso_restrictOpens hW he (isTowerIso_mem_openPreimage_iff he hW)
  have EW' := isTowerIso_restrictOpens hW' he (isTowerIso_mem_openPreimage_iff he hW')
  have hA := BlowupTowerSplitIso.IsTowerIso.congr_base (EW.symm.trans (hρ.trans EW'))
    (Φ' := restrictBase φ hφU) (fun _ => rfl)
  have N1 := isTowerIso_restrict_nestedOpens (inf_le_left : U ⊓ V ≤ U) Q
  have N2 := isTowerIso_restrict_nestedOpens (inf_le_right : U ⊓ V ≤ V) Q
  have hm := mem_nestedOpens_iff φ hφU
  have Xχ := isTowerIso_restrictOpens hm hχ (isTowerIso_mem_openPreimage_iff hχ hm)
  have N3 := isTowerIso_restrict_nestedOpens (inf_le_right : U ⊓ V' ≤ V') Q
  have N4 := isTowerIso_restrict_nestedOpens (inf_le_left : U ⊓ V' ≤ U) Q
  have hB := N1.trans (N2.symm.trans (Xχ.trans (N3.trans N4.symm)))
  have hEq := IsTowerIso.eq_of_isTowerIso hA hB
  have hproj : ((R.proj (e.symm ⟨(p : Y), hp⟩) : U) : X) = Q.proj (p : Y) := by
    have h1 := he.proj_comm (e.symm ⟨(p : Y), hp⟩)
    rw [Diffeomorph.apply_symm_apply] at h1
    exact (congrArg Subtype.val h1).trans (proj_restrict U Q ⟨(p : Y), hp⟩)
  have hrmem : e.symm ⟨(p : Y), hp⟩ ∈ openPreimage R (nestedOpens U (U ⊓ V)) := by
    change ((R.proj (e.symm ⟨(p : Y), hp⟩) : U) : X) ∈ U ⊓ V
    rw [hproj]
    exact ⟨hp, p.2⟩
  have hq0 : (⟨(p : Y), hp⟩ : openPreimage Q U) ∈ openPreimage (restrict U Q) (nestedOpens U (U ⊓ V)) := by
    change (((restrict U Q).proj ⟨(p : Y), hp⟩ : U) : X) ∈ U ⊓ V
    rw [proj_restrict]
    exact ⟨hp, p.2⟩
  refine ⟨⟨e.symm ⟨(p : Y), hp⟩, hrmem⟩, rfl, ?_⟩
  have := congrArg (fun f => ((f ⟨⟨(p : Y), hp⟩, hq0⟩ : openPreimage (restrict U Q) (nestedOpens U (U ⊓ V'))) :
    openPreimage Q U)) hEq
  exact (congrArg Subtype.val this).symm

end Compare

/-! ### Equivariance of an extension with compact footprint -/

section Extension

variable {X : CMfd.{u} n} {U V V' : Opens X}
  (φ : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')
  (hφU : ∀ p : V, ((φ p : V') : X) ∈ U ↔ (p : X) ∈ U)

/-- **Equivariance of an extension with footprint in `U`** (the compact-footprint extension of
`HironakaCompactFootprintSharpExtension`): let `Q` be a tower over `X` whose centres lie over `K ⊆ U` and whose restriction
to `U` is isomorphic over the identity to a tower `R` over `U`.  If `φ : V ≅ V'` preserves `U` and
`R|_{U ∩ V} ≅ R|_{U ∩ V'}` over the restriction of `φ`, then `Q|_V ≅ Q|_{V'}` over `φ`.  Over `U` the centres correspond by
the comparison lemma; off `U` there are no centres on either side. -/
theorem exists_isTowerIso_restrict_of_extension {K : Set X} (hKU : K ⊆ U) :
    ∀ {Y Z : CMfd.{u} n} (Q : BlowupTower X Y) (R : BlowupTower (CMfd.of (n := n) U) Z)
      {e : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage Q U)},
      RestrictEmptyTower.CentresOver K Q →
      IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) R (restrict U Q) e →
      ∀ {ρ : CMfd.of (n := n) (openPreimage R (nestedOpens U (U ⊓ V))) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage R (nestedOpens U (U ⊓ V')))},
      IsTowerIso (restrictBase φ hφU) (restrict (nestedOpens U (U ⊓ V)) R)
        (restrict (nestedOpens U (U ⊓ V')) R) ρ →
      ∃ χ : CMfd.of (n := n) (openPreimage Q V) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage Q V'), IsTowerIso φ (restrict V Q) (restrict V' Q) χ
  | _, _, .refl, _, _, _, _, _, _ => ⟨φ, IsTowerIso.refl⟩
  | _, _, .step Q C π hπ, R, e, hOver, he, ρ, hρ => by
    cases R with
    | refl => exact absurd he.length_eq (by simp [length_restrict])
    | step R CR πR hπR =>
      obtain ⟨e₀, he₀, -, hCe⟩ := he.step_inv
      obtain ⟨ρ₀, hρ₀, -, hCρ⟩ := hρ.step_inv
      obtain ⟨χ₀, hχ₀⟩ := exists_isTowerIso_restrict_of_extension hKU Q R hOver.1 he₀ hρ₀
      refine HironakaG34CanonicalLocalEquivariance.exists_isTowerIso_step hχ₀ _ _ ?_
      ext p
      change (χ₀ p : openPreimage Q V').val ∈ C ↔ (p : openPreimage Q V).val ∈ C
      by_cases hp : Q.proj (p : openPreimage Q V).val ∈ U
      · obtain ⟨r, hr, hχr⟩ := exists_eq_of_isTowerIso φ hφU Q R he₀ hχ₀ hρ₀ p hp
        rw [hχr]
        have h1 : (e₀ (ρ₀ r : openPreimage R (nestedOpens U (U ⊓ V'))).val : openPreimage Q U).val ∈ C ↔
            (ρ₀ r : openPreimage R (nestedOpens U (U ⊓ V'))).val ∈ CR := by
          rw [← hCe]
          rfl
        have h2 : (ρ₀ r : openPreimage R (nestedOpens U (U ⊓ V'))).val ∈ CR ↔
            (r : openPreimage R (nestedOpens U (U ⊓ V))).val ∈ CR :=
          Iff.of_eq (congrArg (r ∈ ·) hCρ)
        have h3 : (r : openPreimage R (nestedOpens U (U ⊓ V))).val ∈ CR ↔ (p : openPreimage Q V).val ∈ C := by
          rw [← hCe]
          change (e₀ (r : openPreimage R (nestedOpens U (U ⊓ V))).val : openPreimage Q U).val ∈ C ↔ _
          rw [hr, Diffeomorph.apply_symm_apply]
        exact h1.trans (h2.trans h3)
      · have hnot : (p : openPreimage Q V).val ∉ C := fun hpC => hp (hKU (hOver.2 hpC))
        have hχnot : (χ₀ p : openPreimage Q V').val ∉ C := by
          intro hC
          have hK := hKU (hOver.2 hC)
          have hval : Q.proj (χ₀ p : openPreimage Q V').val = ((φ ((restrict V Q).proj p) : V') : X) := by
            rw [hχ₀.proj_comm p, proj_restrict]
          change Q.proj (χ₀ p : openPreimage Q V').val ∈ U at hK
          rw [hval, hφU, proj_restrict] at hK
          exact hp hK
        exact iff_of_false hχnot hnot

/-- **An extension of an equivariant tower is equivariant for the data and the window**: if the centres of `Q` lie over
`K ⊆ U`, `Q|_U ≅ R` over the identity and `R` is equivariant for the restricted data `(N ∩ U, E|_U)`, then `Q` is equivariant
for `(N, U :: E)` (the window `U` is added to the preserved sets). -/
theorem isEquivariant_of_extension {X : CMfd.{u} n} {U : Opens X} {N K : Set X} {E : List (Set X)} (hKU : K ⊆ U)
    {Y Z : CMfd.{u} n} (Q : BlowupTower X Y) (R : BlowupTower (CMfd.of (n := n) U) Z)
    {e : Z ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage Q U)}
    (hOver : RestrictEmptyTower.CentresOver K Q)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) U) ∞) R (restrict U Q) e)
    (hR : HironakaG34MaskFoldEquivariance.IsEquivariant (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' N) (E.map ((Subtype.val : U → X) ⁻¹' ·)) R) :
    HironakaG34MaskFoldEquivariance.IsEquivariant N ((U : Set X) :: E) Q := by
  intro V V' φ hφN hφH
  have hφU : ∀ p : V, ((φ p : V') : X) ∈ U ↔ (p : X) ∈ U := hφH (U : Set X) (List.mem_cons_self ..)
  have hN' : ∀ q : nestedOpens U (U ⊓ V), (((restrictBase φ hφU q : nestedOpens U (U ⊓ V')) : U) : X) ∈ N ↔
      ((q : U) : X) ∈ N := fun q => hφN ⟨(q : U), (q.2 : ((q : U) : X) ∈ U ⊓ V).2⟩
  have hH' : ∀ H ∈ E.map ((Subtype.val : U → X) ⁻¹' ·), ∀ q : nestedOpens U (U ⊓ V),
      ((restrictBase φ hφU q : nestedOpens U (U ⊓ V')) : U) ∈ H ↔ (q : U) ∈ H := by
    intro H hH q
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact hφH H₀ (List.mem_cons_of_mem _ hH₀) ⟨(q : U), (q.2 : ((q : U) : X) ∈ U ⊓ V).2⟩
  obtain ⟨ρ, hρ⟩ := hR (nestedOpens U (U ⊓ V)) (nestedOpens U (U ⊓ V')) (restrictBase φ hφU) hN' hH'
  exact exists_isTowerIso_restrict_of_extension φ hφU hKU Q R hOver he hρ

end Extension

end

end Hironaka.HironakaG34ExtensionEquivariance
