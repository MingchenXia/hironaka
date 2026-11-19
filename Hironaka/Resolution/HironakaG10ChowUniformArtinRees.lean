import Mathlib.RingTheory.Ideal.Colon
import Hironaka.Resolution.HironakaG10ChowArtinReesCentre
import Hironaka.Resolution.HironakaG10PNIdealFamily

/-!
# Uniform Artin–Rees numbers over compact sets (Hironaka 1975, Lemma 3.2, p. 531)

Hironaka's centre `D_β = V(I_Z + I_S^β)` (printed p. 542) needs ONE exponent `β` at least the
Artin–Rees number of `(I_Z, I_S)` at every point of a relatively compact `Q` (proof of Lemma 3.2,
p. 531).  Lane G10C's M4 (`HironakaG10ChowArtinReesCentre.exists_artinRees`) is pointwise.  Here:

* `IsArtinReesNumber`, `IsArtinReesNumber.mono` — the property used by `sum_centre_dichotomy`
  (`hAR`) and its monotonicity in the exponent (so `β ≥ α` may be enlarged freely);
* `isArtinReesNumber_span_singleton` — **principal case**: for `I_S = (s)` an Artin–Rees number is
  any `N` at which the colon chain `I_Z : s^m` stops growing;
* `ArtinReesOn`, `exists_artinReesOn_of_local` — **compact assembly**: if every point of a compact
  `K` has a neighbourhood with a common Artin–Rees number, one number works on an open `W ⊇ K`;
* `colonFamily`, `isAscending_colonFamily`, `eventually_artinReesOn_of_principal`,
  `exists_artinReesOn_of_principal` — **the local Noether property gives uniform Artin–Rees numbers
  for locally principal `I_S`** whose colon families `I_Z : s^m` are coherent (one tail of the colon
  chain on one neighbourhood, G10P's `HasLocalNoetherProperty`).

The general (non-principal) case needs the Noether property of the Rees algebra `⊕ I_S^m` (Hironaka:
`gr_S(Y)` locally of finite presentation, p. 531), which is not available natively; see the report.
-/

set_option autoImplicit false

open Set TopologicalSpace Filter AlgebraicGeometry
open scoped Topology

namespace Hironaka.HironakaG10ChowUniformArtinRees

open HironakaG10PNIdealFamily

section Ring

variable {A : Type*} [CommRing A]

/-- `α` is an **Artin–Rees number** of `(I_Z, I_S)`: `I_Z ∩ I_S^m ⊆ I_S^(m-α) (I_Z ∩ I_S^α)` for every
`m ≥ α` (the hypothesis `hAR` of `HironakaG10ChowArtinReesCentre.sum_centre_dichotomy`). -/
def IsArtinReesNumber (IZ IS : Ideal A) (α : ℕ) : Prop :=
  ∀ m, α ≤ m → IZ ⊓ IS ^ m ≤ IS ^ (m - α) * (IZ ⊓ IS ^ α)

/-- **Artin–Rees numbers can be enlarged.** -/
theorem IsArtinReesNumber.mono {IZ IS : Ideal A} {α α' : ℕ} (h : IsArtinReesNumber IZ IS α)
    (hα : α ≤ α') : IsArtinReesNumber IZ IS α' := by
  intro m hm
  refine (h m (hα.trans hm)).trans ?_
  have hsplit : IS ^ (m - α) = IS ^ (m - α') * IS ^ (α' - α) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit, mul_assoc]
  refine Ideal.mul_mono_right (le_inf ?_ ?_)
  · exact Ideal.mul_le_right.trans inf_le_left
  · calc IS ^ (α' - α) * (IZ ⊓ IS ^ α) ≤ IS ^ (α' - α) * IS ^ α :=
          Ideal.mul_mono_right inf_le_right
      _ = IS ^ α' := by rw [← pow_add]; congr 1; omega

/-- Every Noetherian ring has an Artin–Rees number (M4, mathlib's Artin–Rees lemma). -/
theorem exists_isArtinReesNumber [IsNoetherianRing A] (IZ IS : Ideal A) :
    ∃ α, IsArtinReesNumber IZ IS α :=
  HironakaG10ChowArtinReesCentre.exists_artinRees IZ IS

/-- **Principal case.** If the colon chain `I_Z : s^m` does not grow beyond `N`, then `N` is an
Artin–Rees number of `(I_Z, (s))`. -/
theorem isArtinReesNumber_span_singleton (IZ : Ideal A) (s : A) (N : ℕ)
    (hN : ∀ m, N ≤ m → ∀ a : A, a * s ^ m ∈ IZ → a * s ^ N ∈ IZ) :
    IsArtinReesNumber IZ (Ideal.span {s}) N := by
  intro m hm x hx
  obtain ⟨hxZ, hxS⟩ := Ideal.mem_inf.mp hx
  rw [Ideal.span_singleton_pow] at hxS ⊢
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hxS
  have hN' : a * s ^ N ∈ IZ := hN m hm a hxZ
  have hsplit : a * s ^ m = s ^ (m - N) * (a * s ^ N) := by
    rw [mul_left_comm, ← pow_add]; congr 2; omega
  rw [hsplit]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.mem_inf.mpr ⟨hN', ?_⟩)
  rw [Ideal.span_singleton_pow]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

end Ring

section Space

universe u

variable {X : LocallyRingedSpace.{u}}

/-- `α` is an Artin–Rees number of `(I_Z, I_S)` at every point of `U`. -/
def ArtinReesOn (IZ IS : ∀ x : X, Ideal (X.presheaf.stalk x)) (U : Set X) (α : ℕ) : Prop :=
  ∀ y ∈ U, IsArtinReesNumber (IZ y) (IS y) α

theorem ArtinReesOn.mono {IZ IS : ∀ x : X, Ideal (X.presheaf.stalk x)} {U U' : Set X} {α α' : ℕ}
    (h : ArtinReesOn IZ IS U α) (hU : U' ⊆ U) (hα : α ≤ α') : ArtinReesOn IZ IS U' α' :=
  fun y hy => (h y (hU hy)).mono hα

/-- **Compact assembly** (finite subcover, maximum of the exponents): locally uniform Artin–Rees
numbers at the points of a compact `K` give ONE Artin–Rees number on an open `W ⊇ K`. -/
theorem exists_artinReesOn_of_local (IZ IS : ∀ x : X, Ideal (X.presheaf.stalk x)) (K : Set X)
    (hK : IsCompact K) (hloc : ∀ x ∈ K, ∃ U ∈ 𝓝 x, ∃ α, ArtinReesOn IZ IS U α) :
    ∃ (W : Set X) (α : ℕ), IsOpen W ∧ K ⊆ W ∧ ArtinReesOn IZ IS W α := by
  classical
  choose U hU α hα using hloc
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun p : K => interior (U p.1 p.2))
    (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hU x hx)⟩)
  refine ⟨⋃ p ∈ s, interior (U p.1 p.2), s.sup fun p => α p.1 p.2,
    isOpen_biUnion fun _ _ => isOpen_interior, hs, fun y hy => ?_⟩
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hy
  exact (hα p.1 p.2 y (interior_subset hyp)).mono
    (Finset.le_sup (f := fun p : K => α p.1 p.2) hp)

/-- The **colon families** `I_Z : s^m` of a family of stalk elements `s`. -/
noncomputable def colonFamily (IZ : ∀ x : X, Ideal (X.presheaf.stalk x)) (s : ∀ x : X, X.presheaf.stalk x)
    (m : ℕ) (x : X) : Ideal (X.presheaf.stalk x) :=
  (IZ x).colon {s x ^ m}

theorem mem_colonFamily {IZ : ∀ x : X, Ideal (X.presheaf.stalk x)} {s : ∀ x : X, X.presheaf.stalk x}
    {m : ℕ} {x : X} {a : X.presheaf.stalk x} : a ∈ colonFamily IZ s m x ↔ a * s x ^ m ∈ IZ x := by
  rw [colonFamily, Submodule.mem_colon_singleton, smul_eq_mul]

/-- The colon chain is ascending. -/
theorem isAscending_colonFamily (IZ : ∀ x : X, Ideal (X.presheaf.stalk x))
    (s : ∀ x : X, X.presheaf.stalk x) : IsAscending X (colonFamily IZ s) := by
  intro m x a ha
  rw [mem_colonFamily] at ha ⊢
  rw [pow_succ, ← mul_assoc]
  exact Ideal.mul_mem_right _ _ ha

/-- **Locally principal `I_S`: uniform Artin–Rees numbers near every point** from the local Noether
property, when the colon families `I_Z : s^m` are coherent. -/
theorem eventually_artinReesOn_of_principal (hX : HasLocalNoetherProperty X)
    (IZ IS : ∀ x : X, Ideal (X.presheaf.stalk x)) (s : ∀ x : X, X.presheaf.stalk x)
    (hcolon : ∀ m, IsLocallyFinitelyGenerated X (colonFamily IZ s m))
    (x : X) {U : Set X} (hU : U ∈ 𝓝 x) (hIS : ∀ y ∈ U, IS y = Ideal.span {s y}) :
    ∃ V ∈ 𝓝 x, ∃ α, ArtinReesOn IZ IS V α := by
  obtain ⟨N, W, hxW, hW⟩ := hX (colonFamily IZ s) (isAscending_colonFamily IZ s) hcolon x
  refine ⟨(W : Set X) ∩ U, inter_mem (W.isOpen.mem_nhds hxW) hU, N, fun y hy => ?_⟩
  rw [hIS y hy.2]
  refine isArtinReesNumber_span_singleton _ _ N fun m hm a ha => ?_
  have h := hW m hm y hy.1 (mem_colonFamily.mpr ha)
  exact mem_colonFamily.mp h

/-- **Uniform Artin–Rees number over a compact set for locally principal `I_S`** (Hironaka
Lemma 3.2, p. 531, the exponent `α(Y, Z, S, Q)`, in the principal case). -/
theorem exists_artinReesOn_of_principal (hX : HasLocalNoetherProperty X)
    (IZ IS : ∀ x : X, Ideal (X.presheaf.stalk x)) (s : ∀ x : X, X.presheaf.stalk x)
    (hcolon : ∀ m, IsLocallyFinitelyGenerated X (colonFamily IZ s m))
    (K : Set X) (hK : IsCompact K) {U : Set X} (hU : IsOpen U) (hKU : K ⊆ U)
    (hIS : ∀ y ∈ U, IS y = Ideal.span {s y}) :
    ∃ (W : Set X) (α : ℕ), IsOpen W ∧ K ⊆ W ∧ ArtinReesOn IZ IS W α :=
  exists_artinReesOn_of_local IZ IS K hK fun x hx =>
    eventually_artinReesOn_of_principal hX IZ IS s hcolon x (hU.mem_nhds (hKU hx)) hIS

end Space

end Hironaka.HironakaG10ChowUniformArtinRees
