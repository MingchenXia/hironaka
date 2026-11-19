import Hironaka.Resolution.HironakaG1RatioGraphEndpointAlignment
import Hironaka.Blowup.BlowupTowerIsoTail

/-! Uniqueness of the native clock over a literal common section. -/
set_option autoImplicit false
open Set
namespace Hironaka.HironakaG1SharedNativeLift
open Hironaka.BlowupSequences BlowupTowers HironakaActualNativeSectionFiniteHistory

private theorem nativeLift_compare {n k : ℕ} {X Y₁ : CMfd.{0} n} {hk : k ≤ n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
    {E : List (Set X)} {T₁ : BlowupTower X Y₁} {V₁ : Set Y₁}
    {hVc₁ : IsClosed V₁} {hV₁ : ∀ x ∈ V₁, RegularAtDim (n := n) V₁ x k}
    {Q₁ : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V₁ hV₁)}
    (h₁ : Lift hk W hWc hW E T₁ V₁ hVc₁ hV₁ Q₁) :
    ∀ {Y₂ : CMfd.{0} n} {T₂ : BlowupTower X Y₂} {V₂ : Set Y₂}
      {hVc₂ : IsClosed V₂} {hV₂ : ∀ x ∈ V₂, RegularAtDim (n := n) V₂ x k}
      {Q₂ : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V₂ hV₂)},
      Lift hk W hWc hW E T₂ V₂ hVc₂ hV₂ Q₂ →
      Y₁ = Y₂ → HEq T₁ T₂ → HEq V₁ V₂ ∧ HEq Q₁ Q₂ := by
  induction h₁ with
  | refl =>
    intro Y₂ T₂ V₂ hVc₂ hV₂ Q₂ h₂
    cases h₂ with
    | refl => intro _ _; exact ⟨HEq.rfl,HEq.rfl⟩
    | step => intro hY hT; exact BlowupTower.noConfusion rfl HEq.rfl (heq_of_eq hY) hT
  | @step Y₀ Y T V hVc hV Q h D hD hint π hπ hNC ih =>
    intro Y₂ T₂ V₂ hVc₂ hV₂ Q₂ h₂
    cases h₂ with
    | refl => intro hY hT; exact BlowupTower.noConfusion rfl HEq.rfl (heq_of_eq hY) hT
    | @step Y₀' Y' T' V' hVc' hV' Q' h' D' hD' hint' π' hπ' hNC' =>
      intro hY hT
      obtain rfl := hY
      obtain ⟨hYY,hTT,hCC,hππ⟩ := BlowupTower.step.inj (eq_of_heq hT)
      subst Y₀'
      have hT' : T = T' := eq_of_heq hTT
      subst T'
      obtain ⟨hVV,hQQ⟩ := ih h' rfl HEq.rfl
      have hV' : V = V' := eq_of_heq hVV
      subst V'
      have hQ' : Q = Q' := eq_of_heq hQQ
      subst Q'
      have hCenter : D = D' :=
        Set.image_injective.mpr Subtype.val_injective (eq_of_heq hCC)
      subst D'
      have heπ : π = π' := eq_of_heq hππ
      subst π'
      exact ⟨HEq.rfl,HEq.rfl⟩

/-- For a literal common source support there is only one native tower
lifting the given ambient clock. -/
theorem nativeLift_heq {n k : ℕ} {X Y : CMfd.{0} n} {hk : k ≤ n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
    {E : List (Set X)} {T : BlowupTower X Y} {V₁ V₂ : Set Y}
    {hVc₁ : IsClosed V₁} {hVc₂ : IsClosed V₂}
    {hV₁ : ∀ x ∈ V₁, RegularAtDim (n := n) V₁ x k}
    {hV₂ : ∀ x ∈ V₂, RegularAtDim (n := n) V₂ x k}
    {Q₁ : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V₁ hV₁)}
    {Q₂ : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V₂ hV₂)}
    (h₁ : Lift hk W hWc hW E T V₁ hVc₁ hV₁ Q₁)
    (h₂ : Lift hk W hWc hW E T V₂ hVc₂ hV₂ Q₂) :
    V₁ = V₂ ∧ HEq Q₁ Q₂ := by
  obtain ⟨hV,hQ⟩ := nativeLift_compare h₁ h₂ rfl HEq.rfl
  exact ⟨eq_of_heq hV,hQ⟩

open scoped Manifold ContDiff
open BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealTowerTransport

/-- A source commutative square for the full section maps identifies
their literal images in the common upper ambient. -/
theorem sourceSupport_eq_of_commuting_square
    {X A₁ A₂ : Type*} {W₁ W₂ : Set X}
    (c₁ : A₁ ≃ W₁) (c₂ : A₂ ≃ W₂) (η : A₁ ≃ A₂)
    (hη : ∀ x, (c₁ x).val = (c₂ (η x)).val) :
    W₁ = W₂ := by
  ext x
  constructor
  · intro hx
    let z : W₁ := ⟨x,hx⟩
    have h := hη (c₁.symm z)
    rw [c₁.apply_symm_apply] at h
    change z.val ∈ W₂
    exact h.symm ▸ (c₂ (η (c₁.symm z))).property
  · intro hx
    let z : W₂ := ⟨x,hx⟩
    have h := hη (η.symm (c₂.symm z))
    rw [η.apply_symm_apply,c₂.apply_symm_apply] at h
    change z.val ∈ W₁
    exact h ▸ (c₁ (η.symm (c₂.symm z))).property

/-- A source square over the common ambient suffices to identify two
actual native lift towers. The equality of the tower data is a conclusion. -/
theorem nativeLift_heq_of_source_square {n k : ℕ} {X Y : CMfd.{0} n} {hk : k ≤ n}
    {W₁ W₂ : Set X} {hWc₁ : IsClosed W₁} {hWc₂ : IsClosed W₂}
    {hW₁ : ∀ x ∈ W₁, RegularAtDim (n := n) W₁ x k}
    {hW₂ : ∀ x ∈ W₂, RegularAtDim (n := n) W₂ x k}
    {E : List (Set X)} {T : BlowupTower X Y} {V₁ V₂ : Set Y}
    {hVc₁ : IsClosed V₁} {hVc₂ : IsClosed V₂}
    {hV₁ : ∀ x ∈ V₁, RegularAtDim (n := n) V₁ x k}
    {hV₂ : ∀ x ∈ V₂, RegularAtDim (n := n) V₂ x k}
    {Q₁ : BlowupTower (nativeManifold hk W₁ hW₁) (nativeManifold hk V₁ hV₁)}
    {Q₂ : BlowupTower (nativeManifold hk W₂ hW₂) (nativeManifold hk V₂ hV₂)}
    (h₁ : Lift hk W₁ hWc₁ hW₁ E T V₁ hVc₁ hV₁ Q₁)
    (h₂ : Lift hk W₂ hWc₂ hW₂ E T V₂ hVc₂ hV₂ Q₂)
    {A₁ A₂ : Type*} (c₁ : A₁ ≃ W₁) (c₂ : A₂ ≃ W₂) (η : A₁ ≃ A₂)
    (hη : ∀ x, (c₁ x).val = (c₂ (η x)).val) :
    W₁ = W₂ ∧ V₁ = V₂ ∧ HEq Q₁ Q₂ := by
  have hW := sourceSupport_eq_of_commuting_square c₁ c₂ η hη
  subst W₂
  exact ⟨rfl,nativeLift_heq h₁ h₂⟩

set_option backward.isDefEq.respectTransparency false in
/-- The normalized biholomorphic charts of lifts of one literal support
induce an isomorphism of their actual unpadded towers. It is the
composition of the two strict-section charts, at source and endpoint. -/
theorem unpadded_transport_isTowerIso {n k : ℕ} {X Y : CMfd.{0} n} {hk : k ≤ n}
    {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
    {E : List (Set X)} {T : BlowupTower X Y} {V₁ V₂ : Set Y}
    {hVc₁ : IsClosed V₁} {hVc₂ : IsClosed V₂}
    {hV₁ : ∀ x ∈ V₁, RegularAtDim (n := n) V₁ x k}
    {hV₂ : ∀ x ∈ V₂, RegularAtDim (n := n) V₂ x k}
    {Q₁ : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V₁ hV₁)}
    {Q₂ : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V₂ hV₂)}
    (h₁ : Lift hk W hWc hW E T V₁ hVc₁ hV₁ Q₁)
    (h₂ : Lift hk W hWc hW E T V₂ hVc₂ hV₂ Q₂)
    {A₁ A₂ : CMfd.{0} k}
    (c₁ : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ nativeManifold hk W hW)
    (c₂ : A₂ ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ nativeManifold hk W hW) :
    let U₁ := transport (X' := A₁) c₁ Q₁
    let U₂ := transport (X' := A₂) c₂ Q₂
    ∃ (χ : U₁.target ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ U₂.target),
      IsTowerIso (c₁.trans c₂.symm) U₁.tower U₂.tower χ ∧
        ∀ z, (U₂.back (χ z)).val = (U₁.back z).val := by
  obtain ⟨hV,hQ⟩ := nativeLift_heq h₁ h₂
  subst V₂
  have hQ' : Q₁ = Q₂ := eq_of_heq hQ
  subst Q₂
  let U₁ := transport (X' := A₁) c₁ Q₁
  let U₂ := transport (X' := A₂) c₂ Q₁
  refine ⟨U₁.back.trans U₂.back.symm, ?_,?_⟩
  · exact (transport_isTowerIso (X' := A₁) c₁ Q₁).trans
      (transport_isTowerIso (X' := A₂) c₂ Q₁).symm
  · intro z
    exact congrArg Subtype.val (U₂.back.apply_symm_apply (U₁.back z))


/-- On a nonempty literal common support the source square also forces
equality of the native dimensions. Thus a tower identification over such
a square requires no supplied equality of dimensions or clocks. -/
theorem nativeLift_heq_of_nonempty_source_square {n k₁ k₂ : ℕ} {X Y : CMfd.{0} n}
    {hk₁ : k₁ ≤ n} {hk₂ : k₂ ≤ n}
    {W₁ W₂ : Set X} {hWc₁ : IsClosed W₁} {hWc₂ : IsClosed W₂}
    {hW₁ : ∀ x ∈ W₁, RegularAtDim (n := n) W₁ x k₁}
    {hW₂ : ∀ x ∈ W₂, RegularAtDim (n := n) W₂ x k₂}
    {E : List (Set X)} {T : BlowupTower X Y} {V₁ V₂ : Set Y}
    {hVc₁ : IsClosed V₁} {hVc₂ : IsClosed V₂}
    {hV₁ : ∀ x ∈ V₁, RegularAtDim (n := n) V₁ x k₁}
    {hV₂ : ∀ x ∈ V₂, RegularAtDim (n := n) V₂ x k₂}
    {Q₁ : BlowupTower (nativeManifold hk₁ W₁ hW₁) (nativeManifold hk₁ V₁ hV₁)}
    {Q₂ : BlowupTower (nativeManifold hk₂ W₂ hW₂) (nativeManifold hk₂ V₂ hV₂)}
    (h₁ : Lift hk₁ W₁ hWc₁ hW₁ E T V₁ hVc₁ hV₁ Q₁)
    (h₂ : Lift hk₂ W₂ hWc₂ hW₂ E T V₂ hVc₂ hV₂ Q₂)
    {A₁ A₂ : Type*} (c₁ : A₁ ≃ W₁) (c₂ : A₂ ≃ W₂) (η : A₁ ≃ A₂)
    (hη : ∀ x, (c₁ x).val = (c₂ (η x)).val) (hne : W₁.Nonempty) :
    k₁ = k₂ ∧ W₁ = W₂ ∧ V₁ = V₂ ∧ HEq Q₁ Q₂ := by
  have hW := sourceSupport_eq_of_commuting_square c₁ c₂ η hη
  obtain ⟨x,hx⟩ := hne
  have hk := RegularPointDimension.eq_of_regularAtDim (hW₁ x hx)
    (hW.symm ▸ hW₂ x (hW ▸ hx))
  subst k₂
  exact ⟨rfl,nativeLift_heq_of_source_square h₁ h₂ c₁ c₂ η hη⟩


set_option backward.isDefEq.respectTransparency false in
/-- A given full source square produces an isomorphism of the actual
unpadded towers over the specified source biholomorphism. The endpoint
square still commutes with the literal strict-section inclusions. -/
theorem unpadded_transport_isTowerIso_of_source_square {n k : ℕ} {X Y : CMfd.{0} n} {hk : k ≤ n}
    {W₁ W₂ : Set X} {hWc₁ : IsClosed W₁} {hWc₂ : IsClosed W₂}
    {hW₁ : ∀ x ∈ W₁, RegularAtDim (n := n) W₁ x k}
    {hW₂ : ∀ x ∈ W₂, RegularAtDim (n := n) W₂ x k}
    {E : List (Set X)} {T : BlowupTower X Y} {V₁ V₂ : Set Y}
    {hVc₁ : IsClosed V₁} {hVc₂ : IsClosed V₂}
    {hV₁ : ∀ x ∈ V₁, RegularAtDim (n := n) V₁ x k}
    {hV₂ : ∀ x ∈ V₂, RegularAtDim (n := n) V₂ x k}
    {Q₁ : BlowupTower (nativeManifold hk W₁ hW₁) (nativeManifold hk V₁ hV₁)}
    {Q₂ : BlowupTower (nativeManifold hk W₂ hW₂) (nativeManifold hk V₂ hV₂)}
    (h₁ : Lift hk W₁ hWc₁ hW₁ E T V₁ hVc₁ hV₁ Q₁)
    (h₂ : Lift hk W₂ hWc₂ hW₂ E T V₂ hVc₂ hV₂ Q₂)
    {A₁ A₂ : CMfd.{0} k}
    (c₁ : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ nativeManifold hk W₁ hW₁)
    (c₂ : A₂ ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ nativeManifold hk W₂ hW₂)
    (η : A₁ ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ A₂)
    (hη : ∀ x, (c₁ x).val = (c₂ (η x)).val) :
    let U₁ := transport (X' := A₁) c₁ Q₁
    let U₂ := transport (X' := A₂) c₂ Q₂
    ∃ (χ : U₁.target ≃ₘ⟮𝓘(ℂ,ComplexModel k),𝓘(ℂ,ComplexModel k)⟯ U₂.target),
      IsTowerIso η U₁.tower U₂.tower χ ∧
        ∀ z, (U₂.back (χ z)).val = (U₁.back z).val := by
  have hW := sourceSupport_eq_of_commuting_square c₁.toEquiv c₂.toEquiv η.toEquiv hη
  subst W₂
  have hBase : η = c₁.trans c₂.symm := by
    ext x
    apply c₂.injective
    change c₂ (η x) = c₂ (c₂.symm (c₁ x))
    rw [c₂.apply_symm_apply]
    exact Subtype.ext (hη x).symm
  rw [hBase]
  exact unpadded_transport_isTowerIso h₁ h₂ c₁ c₂

end Hironaka.HironakaG1SharedNativeLift
