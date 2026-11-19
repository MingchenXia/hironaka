import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
import Hironaka.Resolution.HironakaG10FiniteIdealFamilyArithmetic

/-! A finite family of locally coherent window flatteners gives a genuine
whole-fibre local flattener after proper shrinking. The per-window universal
quotient criteria remain explicit hypotheses. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10ProperFiniteWindowFlattener
open Hironaka HironakaG10HirIdealGerms
  HironakaG10HirFlatQuotient HironakaG10FiniteIdealFamilyArithmetic
open Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
noncomputable section

/-- Finite sums of actual locally generated stalk families are locally generated. -/
theorem locallyFinite_finset_sup {X : LocallyRingedSpace} {ι : Type} [DecidableEq ι]
    (V : Set X) (H : ι → ∀ x : X, Ideal (X.presheaf.stalk x)) (s : Finset ι)
    (hH : ∀ i ∈ s, IsLocallyFinitelyGeneratedOn X V (H i)) :
    IsLocallyFinitelyGeneratedOn X V (fun x => s.sup (fun i => H i x)) := by
  induction s using Finset.induction_on with
  | empty => simpa using isLocallyFinitelyGeneratedOn_bot V
  | @insert i s hi ih =>
    have hFi : IsLocallyFinitelyGeneratedOn X V (H i) := hH i (by simp)
    have hFs : IsLocallyFinitelyGeneratedOn X V (fun x => s.sup (fun j => H j x)) :=
      ih (fun j hj => hH j (by simp [hj]))
    simpa only [Finset.sup_insert] using isLocallyFinitelyGeneratedOn_sup V (H i)
      (fun x => s.sup (fun j => H j x)) hFi hFs

/-- Global necessity plus inner-window sufficiency and properness give one
coherent whole-fibre local flattener for all quotient ideals. -/
theorem exists_localFlattener_of_asymmetric_windows
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) (x₀ : X.obj.left)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : Set X.obj.left) (hV : IsOpen V) (hxV : x₀ ∈ V)
    (W : ι → Set Y.obj.left) (hW : ∀ i, IsOpen (W i))
    (hcover : ∀ y, f.hom.left.base y = x₀ → ∃ i, y ∈ W i)
    (H : ι → ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hfg : ∀ i, IsLocallyFinitelyGeneratedOn X.obj.left V (H i))
    (hproper : ∀ i, H i x₀ ≠ ⊤)
    (hnecessary : ∀ i x, x ∈ V → H i x ≠ ⊤ →
      ∀ J : Ideal (X.obj.left.presheaf.stalk x), FlatOverAt f x J → H i x ≤ J)
    (hsufficient : ∀ i x, x ∈ V → H i x ≠ ⊤ →
      ∀ J : Ideal (X.obj.left.presheaf.stalk x), H i x ≤ J →
        ∀ (y : Y.obj.left) (h : f.hom.left.base y = x), y ∈ W i →
          (quotMap (fibreStalkMap f x y h) J).Flat) :
    ∃ Z : LocalFlattener f, x₀ ∈ Z.support ∧
      ∀ x ∈ Z.V, Z.H x = Finset.univ.sup (fun i => H i x) := by
  classical
  let Ω : Set Y.obj.left := ⋃ i, W i
  have hΩ : IsOpen Ω := isOpen_iUnion hW
  let V' : Set X.obj.left := V ∩ (f.hom.left.base '' Ωᶜ)ᶜ
  have hV' : IsOpen V' := hV.inter ((hf.isClosedMap _ hΩ.isClosed_compl).isOpen_compl)
  have hxV' : x₀ ∈ V' := by
    refine ⟨hxV, ?_⟩
    rintro ⟨y, hy, hyx⟩
    obtain ⟨i, hi⟩ := hcover y hyx
    exact hy (mem_iUnion.2 ⟨i, hi⟩)
  have hcover' : ∀ x ∈ V', ∀ y, f.hom.left.base y = x → ∃ i, y ∈ W i := by
    intro x hx y hy
    by_contra hn
    have hyΩ : y ∉ Ω := by simpa [Ω] using hn
    exact hx.2 ⟨y, hyΩ, hy⟩
  let Hsum : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x) :=
    fun x => Finset.univ.sup (fun i => H i x)
  have hfgsum : IsLocallyFinitelyGeneratedOn X.obj.left V' Hsum :=
    (locallyFinite_finset_sup V H Finset.univ (fun i _ => hfg i)).mono inter_subset_left
  have hflat : ∀ x ∈ V', Hsum x ≠ ⊤ → IsGermFlattenerAt f x (Hsum x) := by
    intro x hx hne J
    have hproper' : ∀ i, H i x ≠ ⊤ := by
      intro i hi
      have hle : H i x ≤ Hsum x := Finset.le_sup (f := fun i => H i x) (Finset.mem_univ i)
      exact hne (top_le_iff.mp (hi ▸ hle))
    constructor
    · intro h
      apply Finset.sup_le
      intro i hi
      exact hnecessary i x hx.1 (hproper' i) J h
    · intro h y hy
      obtain ⟨i, hi⟩ := hcover' x hx y hy
      apply hsufficient i x hx.1 (hproper' i) J ?_ y hy hi
      exact (Finset.le_sup (f := fun i => H i x) (Finset.mem_univ i)).trans h
  have hne₀ : Hsum x₀ ≠ ⊤ := by
    have hle : Hsum x₀ ≤ IsLocalRing.maximalIdeal _ := by
      apply Finset.sup_le
      intro i hi
      exact hnecessary i x₀ hxV (hproper i) _ (flatOverAt_maximalIdeal x₀)
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hle))
  exact ⟨⟨V',hV',Hsum,hfgsum,hflat⟩,⟨hxV',hne₀⟩,fun _ _ => rfl⟩

/-- The same-window iff assembly follows from the asymmetric form. -/
theorem exists_localFlattener_of_finite_windows
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) (x₀ : X.obj.left)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : Set X.obj.left) (hV : IsOpen V) (hxV : x₀ ∈ V)
    (W : ι → Set Y.obj.left) (hW : ∀ i, IsOpen (W i))
    (hcover : ∀ y, f.hom.left.base y = x₀ → ∃ i, y ∈ W i)
    (H : ι → ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x))
    (hfg : ∀ i, IsLocallyFinitelyGeneratedOn X.obj.left V (H i))
    (hproper : ∀ i, H i x₀ ≠ ⊤)
    (hwindow : ∀ i x, x ∈ V → H i x ≠ ⊤ →
      ∀ J : Ideal (X.obj.left.presheaf.stalk x),
        (∀ (y : Y.obj.left) (h : f.hom.left.base y = x), y ∈ W i →
          (quotMap (fibreStalkMap f x y h) J).Flat) ↔ H i x ≤ J) :
    ∃ Z : LocalFlattener f, x₀ ∈ Z.support ∧
      ∀ x ∈ Z.V, Z.H x = Finset.univ.sup (fun i => H i x) := by
  apply exists_localFlattener_of_asymmetric_windows f hf x₀ V hV hxV W hW hcover H hfg hproper
  · intro i x hx hi J hflat
    apply (hwindow i x hx hi J).1
    intro y hy _
    exact hflat y hy
  · intro i x hx hi J hle
    exact (hwindow i x hx hi J).2 hle
end
end Hironaka.Analytic.Unibranch.HironakaG10ProperFiniteWindowFlattener
