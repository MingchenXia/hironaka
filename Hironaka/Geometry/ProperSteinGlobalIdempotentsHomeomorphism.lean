import Hironaka.Geometry.ProperSteinGlobalIdempotents

/-! # Actual original whole idempotents lift uniquely across underlying homeomorphisms. -/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace Hironaka.Geometry.ProperSteinGlobalIdempotents
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ORIGINAL scheme pullback on actual WHOLE global idempotents. -/
def idempotentPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    {e : Γ(Y, ⊤) // IsIdempotentElem e} → {e : Γ(X, ⊤) // IsIdempotentElem e} :=
  fun e => ⟨f.appTop e.1, e.2.map f.appTop.hom⟩

/-- An ORIGINAL underlying homeomorphism internally gives bijectivity of ORIGINAL whole idempotent pullback. -/
theorem idempotentPullback_bijective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsHomeomorph f) : Function.Bijective (idempotentPullback f) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    apply eq_of_basicOpen_eq Y a.2 b.2
    have hpre : f ⁻¹ᵁ Y.basicOpen a.1 = f ⁻¹ᵁ Y.basicOpen b.1 := by
      rw [Scheme.preimage_basicOpen_top, Scheme.preimage_basicOpen_top]
      exact congrArg (X.basicOpen ·) (congrArg Subtype.val hab)
    apply Opens.ext
    ext y
    obtain ⟨x, rfl⟩ := hf.surjective y
    change x ∈ f ⁻¹ᵁ Y.basicOpen a.1 ↔ x ∈ f ⁻¹ᵁ Y.basicOpen b.1
    rw [hpre]
  · intro a
    let V : Y.Opens := ⟨f '' (X.basicOpen a.1 : Set X),
      hf.isOpenMap _ (X.basicOpen a.1).isOpen⟩
    have hV : IsClosed (V : Set Y) :=
      (IsHomeomorph.homeomorph f hf).isClosed_image.mpr
        (isClopen_basicOpen X a.1 a.2).isClosed
    obtain ⟨b, hb, hbo⟩ := exists_idempotent_basicOpen_eq Y V hV
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    apply eq_of_basicOpen_eq X (hb.map f.appTop.hom) a.2
    rw [← Scheme.preimage_basicOpen_top, hbo]
    apply Opens.ext
    ext x
    change (∃ z, z ∈ X.basicOpen a.1 ∧ f z = f x) ↔ x ∈ X.basicOpen a.1
    constructor
    · rintro ⟨z, hz, hzx⟩
      exact hf.injective hzx ▸ hz
    · intro hx
      exact ⟨x, hx, rfl⟩

/-- The actual inverse equivalence uses the SAME original pullback on WHOLE idempotents. -/
def idempotentPullbackEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsHomeomorph f) :
    {e : Γ(Y, ⊤) // IsIdempotentElem e} ≃ {e : Γ(X, ⊤) // IsIdempotentElem e} :=
  Equiv.ofBijective (idempotentPullback f) (idempotentPullback_bijective f hf)

/-- The ENTIRE actual forward map is the ORIGINAL whole-section pullback. -/
theorem idempotentPullbackEquiv_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsHomeomorph f)
    (e : {e : Γ(Y, ⊤) // IsIdempotentElem e}) :
    (idempotentPullbackEquiv f hf e).1 = f.appTop e.1 := rfl

/-- Every ORIGINAL whole idempotent has a UNIQUE actual lift, with its ORIGINAL scheme pullback equation. -/
theorem existsUnique_idempotent_lift {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsHomeomorph f)
    (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    ∃! b : Γ(Y, ⊤), IsIdempotentElem b ∧ f.appTop b = e := by
  obtain ⟨b, hb⟩ := (idempotentPullback_bijective f hf).surjective ⟨e, he⟩
  refine ⟨b.1, ⟨b.2, congrArg Subtype.val hb⟩, ?_⟩
  intro c hc
  have h : idempotentPullback f ⟨c, hc.1⟩ = idempotentPullback f b := by
    apply Subtype.ext
    exact hc.2.trans (congrArg Subtype.val hb).symm
  exact congrArg Subtype.val ((idempotentPullback_bijective f hf).injective h)

end Hironaka.Geometry.ProperSteinGlobalIdempotents
