import Hironaka.Resolution.HironakaActualIntrinsicLogDerivativeFrame
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.BlowupStrictSubmanifold

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The logarithmic derivative ideal along a carrier is étale-local (G8 lane, run 0079)

Blueprint: `hironaka-g8-resume-log-deriv-etale.tex`.

`logDerivIdealAlong N E A` (`HironakaActualIntrinsicLogDerivativeFrame`) is generated at `x` by `A`, by the
vanishing ideal of `N` and by the derivatives `ξ(f)` (`f ∈ A`) along holomorphic fields tangent to `N` and to
EVERY member of the boundary list `E`.  This module proves:

* `pullback_logDerivIdealAlong_mem_iff_of_localInverse`: if `φ` has a holomorphic local inverse at `y`, then
  `φ^*(𝓓_{N,E} A)` and `𝓓_{φ⁻¹N, φ⁻¹E}(φ^*A)` have the same germs at `y` (pointwise version of
  `DerivativeIdealAlongEtale.pullback_derivIdealAlong`, with tangency to every boundary member);
* `logDerivIdealAlong_mem_of_germ`: the operator at `y` depends only on the germs at `y` of the carrier and of
  the boundary members, and a member absent near `y` imposes nothing;
* for the blowup `π` along a closed centre `C`, with strict carrier `N'` and boundary `strict E ++ [π⁻¹C]`
  (the ordinary exceptional boundary of leaf G8-3H-C05), the ordinary pullback of the log operator and the log
  operator of the pulled-back ideal agree at every point `y` with `π y ∉ C ∩ N`
  (`blowup_logDerivIdealAlong_mem_iff_of_notMem`).  The remaining points `π y ∈ C ∩ N` are the chart case.

Sorry-free; no new hypotheses beyond closedness of `N`, `C` and of the boundary members.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8LogDerivEtale

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong
  Hironaka.HadamardBridge Hironaka.DerivativeIdealAlongCoherent
  Hironaka.RelativePrincipalizationSpan Hironaka.DerivativeIdealAlongEtale
  Hironaka.HironakaActualIntrinsicLogDerivativeFrame
  Hironaka.BlowupStrictSubmanifold

noncomputable section

section General

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- The generators of `logDerivIdealAlong N E A` at `x` (the generator predicate of the operator, restated
publicly). -/
def LogGen (N : Set M) (E : List (Set M)) (A : GermIdeal n M) (x : M) (s : M → ℂ) : Prop :=
  A.mem x s ∨ (vanishingIdeal (n := n) N).mem x s ∨
    ∃ (e : ComplexChart n M) (ξ : Fin n → M → ℂ) (f : M → ℂ),
      IsLogTangentField N E e ξ x ∧ A.mem x f ∧ s = fieldDeriv e ξ f

theorem mem_logDerivIdealAlong_iff {N : Set M} {E : List (Set M)} {A : GermIdeal n M} {x : M}
    {g : M → ℂ} :
    (logDerivIdealAlong N E A).mem x g ↔ IsInSpanAt (n := n) (LogGen N E A x) x g :=
  Iff.rfl

/-- A holomorphic germ of `A` lies in the log operator. -/
theorem mem_logDerivIdealAlong_of_mem {N : Set M} {E : List (Set M)} {A : GermIdeal n M} {x : M}
    {g : M → ℂ} (hg : A.mem x g) (hgh : HolomorphicAt n g x) : (logDerivIdealAlong N E A).mem x g :=
  mem_logDerivIdealAlong_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self (Or.inl hg) hgh)

/-- A germ vanishing on the carrier lies in the log operator. -/
theorem mem_logDerivIdealAlong_of_vanishing {N : Set M} {E : List (Set M)} {A : GermIdeal n M} {x : M}
    {g : M → ℂ} (hg : (vanishingIdeal (n := n) N).mem x g) : (logDerivIdealAlong N E A).mem x g :=
  mem_logDerivIdealAlong_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self (Or.inr (Or.inl hg)) hg.1)

/-- Away from a closed carrier the log operator contains every holomorphic germ. -/
theorem mem_logDerivIdealAlong_of_notMem {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hN : IsClosed N) {x : M} (hx : x ∉ N) {g : M → ℂ} (hg : HolomorphicAt n g x) :
    (logDerivIdealAlong N E A).mem x g :=
  mem_logDerivIdealAlong_of_vanishing
    ⟨hg, by filter_upwards [hN.isOpen_compl.mem_nhds hx] with p hp hpN using absurd hpN hp⟩

/-- A field is tangent to a set that is absent near the point. -/
theorem isTangentField_of_eventually_notMem {H : Set M} {e : ComplexChart n M} {ξ : Fin n → M → ℂ}
    {y : M} (hy : y ∈ e.val.source) (hξ : ∀ m, HolomorphicAt n (ξ m) y) (hH : ∀ᶠ q in 𝓝 y, q ∉ H) :
    IsTangentField H e ξ y :=
  ⟨hy, hξ, fun _ hg =>
    ⟨holomorphicAt_fieldDeriv hy hξ hg.1, hH.mono fun _ hq hqH => absurd hqH hq⟩⟩

/-- **Germ locality of the log operator.**  If the carriers agree near `y` and every member of the new
boundary list either agrees near `y` with a member of the old list or is absent near `y`, then every germ of
the old operator at `y` is a germ of the new one. -/
theorem logDerivIdealAlong_mem_of_germ {N₁ N₂ : Set M} {E₁ E₂ : List (Set M)} {A : GermIdeal n M}
    {y : M} (hN : ∀ᶠ q in 𝓝 y, q ∈ N₁ ↔ q ∈ N₂)
    (hE : ∀ H₂ ∈ E₂, (∃ H₁ ∈ E₁, ∀ᶠ q in 𝓝 y, q ∈ H₁ ↔ q ∈ H₂) ∨ ∀ᶠ q in 𝓝 y, q ∉ H₂)
    {g : M → ℂ} (hg : (logDerivIdealAlong N₁ E₁ A).mem y g) :
    (logDerivIdealAlong N₂ E₂ A).mem y g := by
  refine mem_logDerivIdealAlong_iff.mpr ((mem_logDerivIdealAlong_iff.mp hg).mono ?_)
  rintro s (hs | hs | ⟨e, ξ, f, hξ, hf, rfl⟩)
  · exact Or.inl hs
  · exact Or.inr (Or.inl (DerivativeIdealAlongEtale.vanishingIdeal_mem_congr hN hs))
  · refine Or.inr (Or.inr ⟨e, ξ, f, ⟨isTangentField_congr_set hξ.1 hN, fun H₂ hH₂ => ?_⟩, hf, rfl⟩)
    rcases hE H₂ hH₂ with ⟨H₁, hH₁, hH⟩ | hout
    · exact isTangentField_congr_set (hξ.2 H₁ hH₁) hH
    · exact isTangentField_of_eventually_notMem hξ.1.mem_source hξ.1.holomorphicAt hout

/-- **Log tangency transfers** along a local biholomorphism, for the carrier and every boundary member. -/
theorem isLogTangentField_transfer {φ : M' → M} {ψ : M → M'} {y : M'}
    (h : IsLocalInverseAt n φ ψ y) {N : Set M} {E : List (Set M)} {e : ComplexChart n M}
    {e' : ComplexChart n M'} (hy' : y ∈ e'.val.source) {ξ : Fin n → M → ℂ}
    (hξ : IsLogTangentField N E e ξ (φ y)) :
    IsLogTangentField (φ ⁻¹' N) (E.map (φ ⁻¹' ·)) e' (transferField φ ψ e e' ξ) y := by
  refine ⟨isTangentField_transfer h hy' hξ.1, ?_⟩
  intro H' hH'
  obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH'
  exact isTangentField_transfer h hy' (hξ.2 H hH)

/-- `φ^*(𝓓_{N,E} A) ⊆ 𝓓_{φ⁻¹N,φ⁻¹E}(φ^*A)` at a point where `φ` has a local inverse. -/
theorem pullback_logDerivIdealAlong_mem_of_localInverse {φ : M' → M} {ψ : M → M'} {y : M'}
    (hψ : IsLocalInverseAt n φ ψ y) {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) {g : M' → ℂ}
    (hg : (GermIdeal.pullback (m := n) φ (logDerivIdealAlong N E A)).mem y g) :
    (logDerivIdealAlong (φ ⁻¹' N) (E.map (φ ⁻¹' ·)) (GermIdeal.pullback (m := n) φ A)).mem y g := by
  refine mem_logDerivIdealAlong_iff.mpr (IsInSpanAt.trans ?_ (GermIdeal.mem_pullback_iff.mp hg))
  rintro s ⟨b, hb, rfl⟩
  obtain ⟨-, K, t, c, ht, hc, hsum⟩ := mem_logDerivIdealAlong_iff.mp hb
  have hcomp : (b ∘ φ) =ᶠ[𝓝 y] fun p => ∑ k, (c k ∘ φ) p * (t k ∘ φ) p :=
    hψ.mdiff.self_of_nhds.continuousAt.eventually hsum
  refine DerivativeIdeal.isInSpanAt_congr ?_ hcomp.symm
  refine IsInSpanAt.sum Finset.univ fun k _ =>
    IsInSpanAt.mul_left (holomorphicAt_comp_map hψ.mdiff (hc k)) ?_
  have hgen1 : ∀ {u : M' → ℂ},
      LogGen (φ ⁻¹' N) (E.map (φ ⁻¹' ·)) (GermIdeal.pullback (m := n) φ A) y u →
      HolomorphicAt n u y →
      IsInSpanAt (n := n) (LogGen (φ ⁻¹' N) (E.map (φ ⁻¹' ·)) (GermIdeal.pullback (m := n) φ A) y) y u :=
    fun hu hhu => InvertibleIdealQuotient.isInSpanAt_self hu hhu
  rcases ht k with htk | htk | ⟨e, ξ, f, hξ, hf, htk⟩
  · exact hgen1 (Or.inl (comp_mem_pullback hψ.mdiff htk (hA _ _ htk)))
      (holomorphicAt_comp_map hψ.mdiff (hA _ _ htk))
  · have hv := comp_mem_vanishingIdeal_preimage hψ htk
    exact hgen1 (Or.inr (Or.inl hv)) hv.1
  · set e' := complexChartAt (n := n) y
    have hy' : y ∈ e'.val.source := mem_complexChartAt_source y
    have hfhol := hA _ _ hf
    have hfφ : HolomorphicAt n (f ∘ φ) y := holomorphicAt_comp_map hψ.mdiff hfhol
    have htr := fieldDeriv_transfer hψ hy' hξ.1.mem_source ξ hfφ
    have hfψ : (f ∘ φ) ∘ ψ =ᶠ[𝓝 (φ y)] f := by
      filter_upwards [hψ.right_inv] with q hq
      simp [hq]
    have hloc' := DerivativeIdealAlongEtale.fieldDeriv_congr (ξ := ξ) hξ.1.mem_source hfψ
    have hloc'' : (fun p => fieldDeriv e ξ ((f ∘ φ) ∘ ψ) (φ p)) =ᶠ[𝓝 y]
        fun p => fieldDeriv e ξ f (φ p) :=
      hψ.mdiff.self_of_nhds.continuousAt.eventually hloc'
    have heq : fieldDeriv e' (transferField φ ψ e e' ξ) (f ∘ φ) =ᶠ[𝓝 y] t k ∘ φ := by
      filter_upwards [htr, hloc''] with p hp hp'
      rw [hp, hp', htk]
      rfl
    have hgen : LogGen (φ ⁻¹' N) (E.map (φ ⁻¹' ·)) (GermIdeal.pullback (m := n) φ A) y
        (fieldDeriv e' (transferField φ ψ e e' ξ) (f ∘ φ)) :=
      Or.inr (Or.inr ⟨e', _, f ∘ φ, isLogTangentField_transfer hψ hy' hξ,
        comp_mem_pullback hψ.mdiff hf hfhol, rfl⟩)
    exact DerivativeIdeal.isInSpanAt_congr (hgen1 hgen (holomorphicAt_fieldDeriv hy'
      (fun j => holomorphicAt_transferField hψ hy' hξ.1.mem_source hξ.1.holomorphicAt j) hfφ)) heq

/-- `𝓓_{φ⁻¹N,φ⁻¹E}(φ^*A) ⊆ φ^*(𝓓_{N,E} A)` at a point where `φ` has a local inverse. -/
theorem logDerivIdealAlong_pullback_mem_of_localInverse {φ : M' → M} {ψ : M → M'} {y : M'}
    (hψ : IsLocalInverseAt n φ ψ y) {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) {g : M' → ℂ}
    (hg : (logDerivIdealAlong (φ ⁻¹' N) (E.map (φ ⁻¹' ·))
      (GermIdeal.pullback (m := n) φ A)).mem y g) :
    (GermIdeal.pullback (m := n) φ (logDerivIdealAlong N E A)).mem y g := by
  have hψy : ψ (φ y) = y := hψ.left_inv.self_of_nhds
  have hpb : ∀ {b : M → ℂ}, (logDerivIdealAlong N E A).mem (φ y) b →
      IsInSpanAt (n := n) (fun s => ∃ a, (logDerivIdealAlong N E A).mem (φ y) a ∧ s = a ∘ φ) y
        (b ∘ φ) :=
    fun {b} hb => comp_mem_pullback hψ.mdiff hb hb.1
  refine GermIdeal.mem_pullback_iff.mpr (IsInSpanAt.trans ?_ (mem_logDerivIdealAlong_iff.mp hg))
  rintro t (ht | ht | ⟨e', ξ', f', hξ', hf', rfl⟩)
  · exact (GermIdeal.mem_pullback_iff.mp ht).mono fun s ⟨a, ha, hs⟩ =>
      ⟨a, mem_logDerivIdealAlong_of_mem ha (hA _ _ ha), hs⟩
  · have hv := comp_mem_vanishingIdeal hψ ht
    have heq : (t ∘ ψ) ∘ φ =ᶠ[𝓝 y] t := by
      filter_upwards [hψ.left_inv] with p hp
      simp [hp]
    exact DerivativeIdeal.isInSpanAt_congr (hpb (mem_logDerivIdealAlong_of_vanishing hv)) heq
  · obtain ⟨-, K, s, c, hs, hc, hsum⟩ := GermIdeal.mem_pullback_iff.mp hf'
    choose b hb hsb using hs
    have hbhol : ∀ k, HolomorphicAt n (b k) (φ y) := fun k => hA _ _ (hb k)
    have hsφ : ∀ k, HolomorphicAt n (s k) y := fun k =>
      hsb k ▸ holomorphicAt_comp_map hψ.mdiff (hbhol k)
    have hprod := fieldDeriv_eventuallyEq_sum_mul (ξ := ξ') hξ'.1.mem_source hc hsφ hsum
    refine DerivativeIdeal.isInSpanAt_congr ?_ hprod.symm
    refine IsInSpanAt.sum Finset.univ fun k _ => IsInSpanAt.add ?_ ?_
    · refine IsInSpanAt.mul_left
        (holomorphicAt_fieldDeriv hξ'.1.mem_source hξ'.1.holomorphicAt (hc k)) ?_
      rw [hsb k]
      exact hpb (mem_logDerivIdealAlong_of_mem (hb k) (hbhol k))
    · refine IsInSpanAt.mul_left (hc k) ?_
      set e := complexChartAt (n := n) (φ y)
      have hey : φ y ∈ e.val.source := mem_complexChartAt_source (φ y)
      have hψs := hψ.symm
      have hey' : ψ (φ y) ∈ e'.val.source := by rw [hψy]; exact hξ'.1.mem_source
      set ξ := transferField ψ φ e' e ξ'
      have htan1 : ∀ S : Set M, IsTangentField (φ ⁻¹' S) e' ξ' y → IsTangentField S e ξ (φ y) := by
        intro S hS
        have hS' : IsTangentField (φ ⁻¹' S) e' ξ' (ψ (φ y)) := by rw [hψy]; exact hS
        refine isTangentField_congr_set (isTangentField_transfer hψs hey hS') ?_
        filter_upwards [hψ.right_inv] with q hq
        simp only [mem_preimage, hq]
      have htan : IsLogTangentField N E e ξ (φ y) :=
        ⟨htan1 N hξ'.1, fun H hH => htan1 H (hξ'.2 _ (List.mem_map.mpr ⟨H, hH, rfl⟩))⟩
      have htr := fieldDeriv_transfer hψs hey hey' ξ' (hbhol k)
      have heq : (fieldDeriv e ξ (b k)) ∘ φ =ᶠ[𝓝 y] fieldDeriv e' ξ' (s k) := by
        have h1 := hψ.mdiff.self_of_nhds.continuousAt.eventually htr
        filter_upwards [h1, hψ.left_inv] with p hp hpψ
        simp only [Function.comp_apply]
        refine hp.trans ?_
        simp only [hpψ, hsb k]
      refine DerivativeIdeal.isInSpanAt_congr (hpb ?_) heq
      exact mem_logDerivIdealAlong_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
        (Or.inr (Or.inr ⟨e, ξ, b k, htan, hb k, rfl⟩))
        (holomorphicAt_fieldDeriv hey htan.1.holomorphicAt (hbhol k)))

/-- **The log operator commutes with pullback at a point where the map has a holomorphic local inverse**:
`φ^*(𝓓_{N,E} A)_y = 𝓓_{φ⁻¹N,φ⁻¹E}(φ^*A)_y`. -/
theorem pullback_logDerivIdealAlong_mem_iff_of_localInverse {φ : M' → M} {ψ : M → M'} {y : M'}
    (hψ : IsLocalInverseAt n φ ψ y) {N : Set M} {E : List (Set M)} {A : GermIdeal n M}
    (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) (g : M' → ℂ) :
    (GermIdeal.pullback (m := n) φ (logDerivIdealAlong N E A)).mem y g ↔
      (logDerivIdealAlong (φ ⁻¹' N) (E.map (φ ⁻¹' ·)) (GermIdeal.pullback (m := n) φ A)).mem y g :=
  ⟨pullback_logDerivIdealAlong_mem_of_localInverse hψ hA,
    logDerivIdealAlong_pullback_mem_of_localInverse hψ hA⟩

/-- **The log operator commutes with pullback by a local biholomorphism**, globally. -/
theorem pullback_logDerivIdealAlong_of_localInverse {φ : M' → M}
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y) {N : Set M} {E : List (Set M)}
    {A : GermIdeal n M} (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) :
    GermIdeal.pullback (m := n) φ (logDerivIdealAlong N E A) =
      logDerivIdealAlong (φ ⁻¹' N) (E.map (φ ⁻¹' ·)) (GermIdeal.pullback (m := n) φ A) :=
  GermIdeal.ext (funext fun y => funext fun g => propext
    (let ⟨_, hψ⟩ := hloc y; pullback_logDerivIdealAlong_mem_iff_of_localInverse hψ hA g))

end General

section Blowup

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **A blowup has a holomorphic local inverse at every point off the preimage of its centre.** -/
theorem exists_isLocalInverseAt_of_notMem_centre (hπ : IsBlowupAlong n C π) {y : Y} (hy : π y ∉ C) :
    ∃ ψ : X → Y, IsLocalInverseAt n π ψ y := by
  obtain ⟨s, hs, hsπ, hsec⟩ := BlowupIsomorphismOff.exists_section_compl hπ
  have hinv := isLocalInverseAt_val (n := n)
    (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens X) ⟨π y, hy⟩
  have hUy : ∀ᶠ q in 𝓝 (π y), q ∈ Cᶜ := hπ.1.1.isOpen_compl.mem_nhds hy
  have hYy : ∀ᶠ p in 𝓝 y, π p ∈ Cᶜ :=
    (hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous).mem_nhds hy
  have hopen : ∀ q (hq : q ∈ Cᶜ),
      openInv (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens X) ⟨π y, hy⟩ q = ⟨q, hq⟩ := by
    intro q hq
    simp only [openInv]
    exact dif_pos hq
  refine ⟨s ∘ openInv (⟨Cᶜ, hπ.1.1.isOpen_compl⟩ : TopologicalSpace.Opens X) ⟨π y, hy⟩,
    ⟨Eventually.of_forall fun p => (hπ.contMDiff p).mdifferentiableAt (by simp), ?_, ?_, ?_⟩⟩
  · have h := hinv.mdiff_inv
    filter_upwards [h] with q hq
    exact ((hs _).mdifferentiableAt (by simp)).comp q hq
  · filter_upwards [hYy] with p hp
    simp only [Function.comp_apply, hopen _ hp]
    exact hsec p hp
  · filter_upwards [hUy] with q hq
    simp only [Function.comp_apply, hopen _ hq]
    exact congrFun hsπ ⟨q, hq⟩

/-- **Off the centre**: for the blowup `π` along a closed centre `C`, the ordinary pullback of the log operator
of `(N, E, A)` and the log operator of `(strict N, strict E ++ [π⁻¹C], π^*A)` have the same germs at every
point `y` with `π y ∉ C`. -/
theorem blowup_logDerivIdealAlong_mem_iff_of_notMem_centre (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosed N) {E : List (Set X)} (hEc : ∀ H ∈ E, IsClosed H) {A : GermIdeal n X}
    (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) {y : Y} (hy : π y ∉ C) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (logDerivIdealAlong N E A)).mem y g ↔
      (logDerivIdealAlong (geoStrictTransform π C N) (E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
        (GermIdeal.pullback (m := n) π A)).mem y g := by
  obtain ⟨ψ, hψ⟩ := exists_isLocalInverseAt_of_notMem_centre hπ hy
  rw [pullback_logDerivIdealAlong_mem_iff_of_localInverse hψ hA]
  have hO : ∀ᶠ q in 𝓝 y, π q ∉ C :=
    (hπ.1.1.isOpen_compl.preimage hπ.contMDiff.continuous).mem_nhds hy
  have hstrict : ∀ {H : Set X}, IsClosed H →
      ∀ᶠ q in 𝓝 y, q ∈ π ⁻¹' H ↔ q ∈ geoStrictTransform π C H := fun {H} hH => by
    filter_upwards [hO] with q hq
    exact (mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hH hq).symm
  constructor
  · apply logDerivIdealAlong_mem_of_germ (hstrict hN)
    intro H₂ hH₂
    rcases List.mem_append.mp hH₂ with h | h
    · obtain ⟨H, hH, rfl⟩ := List.mem_map.mp h
      exact Or.inl ⟨π ⁻¹' H, List.mem_map.mpr ⟨H, hH, rfl⟩, hstrict (hEc H hH)⟩
    · rw [List.mem_singleton] at h
      subst h
      exact Or.inr hO
  · apply logDerivIdealAlong_mem_of_germ (by
      filter_upwards [hstrict hN] with q hq using hq.symm)
    intro H₂ hH₂
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hH₂
    exact Or.inl ⟨geoStrictTransform π C H,
      List.mem_append_left _ (List.mem_map.mpr ⟨H, hH, rfl⟩),
      by filter_upwards [hstrict (hEc H hH)] with q hq using hq.symm⟩

/-- **Off the carrier**: if `π y ∉ N` (`N` closed), both sides contain every holomorphic germ at `y`. -/
theorem blowup_logDerivIdealAlong_mem_iff_of_notMem_carrier (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosed N) (E : List (Set X)) (E' : List (Set Y)) (A : GermIdeal n X) (A' : GermIdeal n Y)
    {y : Y} (hy : π y ∉ N) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (logDerivIdealAlong N E A)).mem y g ↔
      (logDerivIdealAlong (geoStrictTransform π C N) E' A').mem y g := by
  have hcont := hπ.contMDiff.continuous
  constructor
  · intro hg
    have hhol : HolomorphicAt n g y := hg.1
    refine mem_logDerivIdealAlong_of_notMem isClosed_closure (fun hyN => hy ?_) hhol
    exact geoStrictTransform_subset_preimage hcont hN hyN
  · intro hg
    have hhol : HolomorphicAt n g y := hg.1
    have hone : (logDerivIdealAlong N E A).mem (π y) (fun _ => 1) :=
      mem_logDerivIdealAlong_of_notMem hN hy (holomorphicAt_const 1)
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_of_eq_mul ⟨(fun _ : X => (1 : ℂ)), hone, rfl⟩
      hhol hhol (Eventually.of_forall fun _ => by simp))

/-- **Every point off `C ∩ N`**: the ordinary pullback of the log operator and the log operator of the
ordinary exceptional data agree at every `y` with `π y ∉ C ∩ N`. -/
theorem blowup_logDerivIdealAlong_mem_iff_of_notMem (hπ : IsBlowupAlong n C π) {N : Set X}
    (hN : IsClosed N) {E : List (Set X)} (hEc : ∀ H ∈ E, IsClosed H) {A : GermIdeal n X}
    (hA : ∀ x g, A.mem x g → HolomorphicAt n g x) {y : Y} (hy : π y ∉ C ∩ N) (g : Y → ℂ) :
    (GermIdeal.pullback (m := n) π (logDerivIdealAlong N E A)).mem y g ↔
      (logDerivIdealAlong (geoStrictTransform π C N) (E.map (geoStrictTransform π C) ++ [π ⁻¹' C])
        (GermIdeal.pullback (m := n) π A)).mem y g := by
  by_cases hC : π y ∈ C
  · exact blowup_logDerivIdealAlong_mem_iff_of_notMem_carrier hπ hN _ _ _ _ (fun hN' => hy ⟨hC, hN'⟩) g
  · exact blowup_logDerivIdealAlong_mem_iff_of_notMem_centre hπ hN hEc hA hC g

end Blowup

end

end Hironaka.HironakaG8LogDerivEtale
