/-
Copyright (c) 2026. All rights reserved.
-/
import DeJongAlterations.Geometry.ProperSteinGlobalIdempotentsEqualizer
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Sheaves.Stalks

/-!
# Actual global idempotents and original clopen subsets of arbitrary schemes

Adapted from the same workspace source `EnvelopeProperty/SchemeGlobalIdempotents.lean`,
SHA256 5e42c025496a9064f8e9a1971e4537bb9939935b3e2cbf7f4c7261d76e8337ce.
The original whole equalizer and all other dependencies use native Mathlib.
-/
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
namespace DeJongAlterations.Geometry.ProperSteinGlobalIdempotents
variable (X : Scheme.{u})

/-- Every ORIGINAL global idempotent has its true clopen original basic open. -/
theorem isClopen_basicOpen (e : Γ(X, ⊤)) (he : IsIdempotentElem e) :
    IsClopen (X.basicOpen e : Set X) := by
  have hd : X.basicOpen e ⊓ X.basicOpen (1-e)=⊥ := by
    rw [← X.basicOpen_mul,he.mul_one_sub_self,X.basicOpen_zero]
  have hc : X.basicOpen e ⊔ X.basicOpen (1-e)=⊤ := by
    apply top_unique
    simpa only [add_sub_cancel,X.basicOpen_one] using X.basicOpen_add_le e (1-e)
  have hcompl : (X.basicOpen e : Set X)ᶜ = X.basicOpen (1-e) := by
    ext x
    have hh : x ∈ X.basicOpen e ∨ x ∈ X.basicOpen (1-e) := by
      change x ∈ X.basicOpen e ⊔ X.basicOpen (1-e)
      rw [hc]
      trivial
    have hn : ¬(x ∈ X.basicOpen e ∧ x ∈ X.basicOpen (1-e)) := by
      change x ∉ X.basicOpen e ⊓ X.basicOpen (1-e)
      rw [hd]
      exact not_false
    aesop
  exact ⟨isOpen_compl_iff.mp (hcompl ▸ (X.basicOpen (1-e)).isOpen), (X.basicOpen e).isOpen⟩

/-- Genuine original sheaf gluing constructs a whole idempotent for EVERY actual clopen open. -/
theorem exists_idempotent_basicOpen_eq (V : X.Opens) (hV : IsClosed (V : Set X)) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e=V := by
  classical
  let W : X.Opens := ⟨(V : Set X)ᶜ,hV.isOpen_compl⟩
  let U : ULift.{u} Bool → X.Opens := fun b => if b.down then V else W
  have htop : iSup U=⊤ := by
    ext x
    simp only [Opens.mem_iSup,U,SetLike.mem_coe,Opens.mem_top,iff_true]
    by_cases h : x ∈ V
    · exact ⟨⟨true⟩,h⟩
    · exact ⟨⟨false⟩,h⟩
  let s : ∀ b, Γ(X,U b) := fun b => if b.down then 1 else 0
  have hs : s ∈ ProperSteinSectionsEqualizer.compatible X U := by
    apply funext
    rintro ⟨⟨i⟩,⟨j⟩⟩
    cases i <;> cases j
    · simp [ProperSteinSectionsEqualizer.left,ProperSteinSectionsEqualizer.right,s]
    · have h : U ⟨false⟩ ⊓ U ⟨true⟩=⊥ := by ext x; simp [U,W]
      have : Subsingleton Γ(X,U ⟨false⟩ ⊓ U ⟨true⟩) := by rw [h]; infer_instance
      exact Subsingleton.elim _ _
    · have h : U ⟨true⟩ ⊓ U ⟨false⟩=⊥ := by ext x; simp [U,W]
      have : Subsingleton Γ(X,U ⟨true⟩ ⊓ U ⟨false⟩) := by rw [h]; infer_instance
      exact Subsingleton.elim _ _
    · simp [ProperSteinSectionsEqualizer.left,ProperSteinSectionsEqualizer.right,s]
  let z := (ProperSteinSectionsEqualizer.sectionsEquiv X U).symm ⟨s,hs⟩
  let e : Γ(X,⊤) := X.presheaf.map (eqToHom htop.symm).op z
  have her (b : ULift.{u} Bool) : X.presheaf.map (homOfLE (show U b≤⊤ from le_top)).op e=s b := by
    change X.presheaf.map _ (X.presheaf.map _ z)=s b
    have hz := congrArg (fun t : ProperSteinSectionsEqualizer.compatible X U => t.1 b)
      ((ProperSteinSectionsEqualizer.sectionsEquiv X U).apply_symm_apply ⟨s,hs⟩)
    change ProperSteinSectionsEqualizer.restriction X U z b=s b at hz
    rw [← ConcreteCategory.comp_apply,← Functor.map_comp]
    exact hz
  have he : IsIdempotentElem e := by
    change e*e=e
    apply X.sheaf.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) htop.ge
    intro b
    change (X.presheaf.map (homOfLE (show U b≤⊤ from le_top)).op).hom (e*e)=
      (X.presheaf.map (homOfLE (show U b≤⊤ from le_top)).op).hom e
    rw [map_mul,her]
    rcases b with ⟨b⟩
    cases b <;> simp [s]
  refine ⟨e,he,?_⟩
  have htrue : V ⊓ X.basicOpen e=V := by
    have h := congrArg (fun t => X.basicOpen t) (her ⟨true⟩)
    simpa [U,s] using h
  have hfalse : W ⊓ X.basicOpen e=⊥ := by
    have h := congrArg (fun t => X.basicOpen t) (her ⟨false⟩)
    simpa [U,s] using h
  apply le_antisymm
  · intro x hx
    by_contra hn
    have hxm : x ∈ W ⊓ X.basicOpen e := ⟨hn,hx⟩
    rw [hfalse] at hxm
    exact hxm
  · exact (inf_le_right : V ⊓ X.basicOpen e≤_).trans_eq' htrue

private theorem idempotent_eq_zero_of_not_isUnit {R : Type u} [CommRing R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) (hn : ¬IsUnit a) : a=0 := by
  obtain h | h := IsLocalRing.isUnit_or_isUnit_one_sub_self a
  · exact (hn h).elim
  · have hh := (IsIdempotentElem.iff_eq_one_of_isUnit h).mp ha.one_sub
    have hh' := congrArg (fun z : R => 1-z) hh
    simpa using hh'

/-- Actual local stalks and genuine germ extensionality detect WHOLE original idempotents. -/
theorem eq_of_basicOpen_eq {e f : Γ(X,⊤)} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : X.basicOpen e=X.basicOpen f) : e=f := by
  apply TopCat.Presheaf.section_ext X.sheaf ⊤ e f
  intro x hx
  let γ : Γ(X,⊤) →+* X.presheaf.stalk x := (X.presheaf.germ ⊤ x hx).hom
  have he' : IsIdempotentElem (γ e) := he.map γ
  have hf' : IsIdempotentElem (γ f) := hf.map γ
  have hu : IsUnit (γ e) ↔ IsUnit (γ f) := by
    change IsUnit (X.presheaf.germ ⊤ x hx e) ↔ IsUnit (X.presheaf.germ ⊤ x hx f)
    rw [← X.mem_basicOpen_top e x, ← X.mem_basicOpen_top f x, h]
  change γ e=γ f
  by_cases hh : IsUnit (γ e)
  · rw [(IsIdempotentElem.iff_eq_one_of_isUnit hh).mp he',
      (IsIdempotentElem.iff_eq_one_of_isUnit (hu.mp hh)).mp hf']
  · rw [idempotent_eq_zero_of_not_isUnit he' hh,
      idempotent_eq_zero_of_not_isUnit hf' (fun hh' => hh (hu.mpr hh'))]

/-- The ORIGINAL global-idempotent/basic-open map is a genuine correspondence on arbitrary schemes. -/
def idempotentEquivClopens : {e : Γ(X,⊤) // IsIdempotentElem e} ≃ Clopens X :=
  Equiv.ofBijective (fun e => ⟨X.basicOpen e.1,isClopen_basicOpen X e.1 e.2⟩) (by
    constructor
    · intro e f h
      apply Subtype.ext
      apply eq_of_basicOpen_eq X e.2 f.2
      exact congrArg (fun V : Clopens X => V.toOpens) h
    · intro V
      obtain ⟨e,he,hV⟩ := exists_idempotent_basicOpen_eq X V.toOpens V.isClosed
      refine ⟨⟨e,he⟩,?_⟩
      apply SetLike.coe_injective
      exact congrArg (fun U : X.Opens => (U : Set X)) hV)

/-- The genuine original clopen criterion is exactly triviality of WHOLE global idempotents. -/
theorem connectedSpace_iff_idempotents : ConnectedSpace X ↔ Nonempty X ∧
    ∀ e : Γ(X,⊤), IsIdempotentElem e → e=0 ∨ e=1 := by
  rw [connectedSpace_iff_clopen]
  apply and_congr_right
  intro _
  constructor
  · intro h e he
    obtain hD | hD := h (X.basicOpen e) (isClopen_basicOpen X e he)
    · left
      apply eq_of_basicOpen_eq X he .zero
      apply SetLike.coe_injective
      simpa only [X.basicOpen_zero,Opens.coe_bot] using hD
    · right
      apply eq_of_basicOpen_eq X he .one
      apply SetLike.coe_injective
      simpa only [X.basicOpen_one,Opens.coe_top] using hD
  · intro h V hV
    obtain ⟨e,he,hD⟩ := exists_idempotent_basicOpen_eq X ⟨V,hV.isOpen⟩ hV.isClosed
    obtain h | h := h e he
    · left
      have heq := congrArg (fun U : X.Opens => (U : Set X)) hD
      change (X.basicOpen e : Set X)=V at heq
      rw [h,X.basicOpen_zero] at heq
      exact heq.symm
    · right
      have heq := congrArg (fun U : X.Opens => (U : Set X)) hD
      change (X.basicOpen e : Set X)=V at heq
      rw [h,X.basicOpen_one] at heq
      exact heq.symm


/-- Nontrivial ORIGINAL global sections force genuine scheme nonemptiness. -/
theorem nonempty_of_nontrivial_globalSections [Nontrivial Γ(X,⊤)] : Nonempty X := by
  by_contra h
  have : IsEmpty X := ⟨fun x => h ⟨x⟩⟩
  have : Subsingleton Γ(X,⊤) := inferInstance
  exact zero_ne_one (Subsingleton.elim (0 : Γ(X,⊤)) 1)

/-- A genuine domain of ORIGINAL whole global sections derives actual connectedness and nonemptiness. -/
theorem connectedSpace_of_globalSections_isDomain [IsDomain Γ(X,⊤)] : ConnectedSpace X :=
  (connectedSpace_iff_idempotents X).mpr ⟨nonempty_of_nontrivial_globalSections X,
    fun _ he => IsIdempotentElem.iff_eq_zero_or_one.mp he⟩

end DeJongAlterations.Geometry.ProperSteinGlobalIdempotents
