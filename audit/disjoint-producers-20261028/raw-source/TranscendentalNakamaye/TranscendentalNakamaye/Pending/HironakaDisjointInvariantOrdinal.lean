import TranscendentalNakamaye.Pending.CanonicalCentres
import Mathlib.SetTheory.Ordinal.Arithmetic
set_option autoImplicit false

/-!
# Explicit ordinal coordinates of the original canonical invariant

Blueprint: `hironaka-disjoint-invariant-ordinal.tex`.
The literal recursive constructors of `CanonicalCentres.ValTy` are mapped to
ordinal blocks. The monomial coordinate uses the established colex/binary order
isomorphism on the actual chronological indices. No geometric decrease or new
termination driver is asserted.
-/
open Ordinal
namespace TranscendentalNakamaye.Pending.HironakaDisjointInvariantOrdinal
noncomputable section
private structure Code (α : Type) [LinearOrder α] where
 bound : Ordinal
 pos : 0 < bound
 rank : α → Ordinal
 range_lt : ∀ x, rank x < bound
 mono : StrictMono rank

private def natCode : Code ℕ where
 bound := ω
 pos := Ordinal.omega0_pos
 rank := Nat.cast
 range_lt := Ordinal.natCast_lt_omega0
 mono := by intro a b h; exact_mod_cast h

private theorem block_lt {B r : Ordinal} (hr : r<B) (k : ℕ) :
 B*(k : Ordinal)+r < B*(k+1 : ℕ) := by
 rw [Nat.cast_add,Nat.cast_one,mul_add_one]
 exact (add_lt_add_iff_left _).mpr hr

private def natLex {α : Type} [LinearOrder α] (c : Code α) : Code (ℕ ×ₗ α) where
 bound := c.bound*ω
 pos := mul_pos c.pos Ordinal.omega0_pos
 rank := fun x => c.bound*(ofLex x).1+(c.rank (ofLex x).2)
 range_lt := by
  intro x
  exact (block_lt (c.range_lt _) _).trans (mul_lt_mul_of_pos_left (Ordinal.natCast_lt_omega0 _) c.pos)
 mono := by
  intro x y h
  rcases Prod.Lex.toLex_lt_toLex.mp h with h | ⟨h,h'⟩
  · have hn : ((ofLex x).1+1 : ℕ) ≤ (ofLex y).1 := h
    have hc : (((ofLex x).1+1 : ℕ) : Ordinal) ≤ ((ofLex y).1 : Ordinal) := by exact_mod_cast hn
    exact (block_lt (c.range_lt _) _).trans_le
      ((mul_le_mul_of_nonneg_left hc (le_of_lt c.pos)).trans le_self_add)
  · change c.bound * ((ofLex x).1 : Ordinal) + c.rank (ofLex x).2 <
      c.bound * ((ofLex y).1 : Ordinal) + c.rank (ofLex y).2
    change (ofLex x).1 = (ofLex y).1 at h
    rw [h]
    exact (add_lt_add_iff_left _).mpr (c.mono h')

private def topCode {α : Type} [LinearOrder α] (c : Code α) : Code (WithTop α) where
 bound := c.bound+1
 pos := lt_of_lt_of_le c.pos le_self_add
 rank := WithTop.recTopCoe c.bound c.rank
 range_lt := by
  intro x
  cases x using WithTop.recTopCoe with
  | top => exact lt_add_one _
  | coe a => exact (c.range_lt a).trans (lt_add_one _)
 mono := by
  intro x y h
  cases x using WithTop.recTopCoe <;> cases y using WithTop.recTopCoe
  · exact (lt_irrefl _ h).elim
  · exact (not_lt_of_ge le_top h).elim
  · exact c.range_lt _
  · exact c.mono (WithTop.coe_lt_coe.mp h)

private def botCodeLimit {α : Type} [LinearOrder α] (c : Code α)
    (hlimit : Order.IsSuccLimit c.bound) : Code (WithBot α) where
 bound := c.bound
 pos := c.pos
 rank := WithBot.recBotCoe 0 (fun a => c.rank a + 1)
 range_lt := by
  intro x
  cases x using WithBot.recBotCoe with
  | bot => exact c.pos
  | coe a =>
    change c.rank a + 1 < c.bound
    simpa only [Order.succ_eq_add_one] using hlimit.succ_lt (c.range_lt a)
 mono := by
  intro x y h
  cases x using WithBot.recBotCoe <;> cases y using WithBot.recBotCoe
  · exact (lt_irrefl _ h).elim
  · exact lt_of_le_of_lt zero_le (lt_add_one _)
  · exact (not_lt_of_ge bot_le h).elim
  · change c.rank _ + 1 < c.rank _ + 1
    simpa only [Order.succ_eq_add_one] using
      Order.succ_strictMono (c.mono (WithBot.coe_lt_coe.mp h))

private def sumCode {α β : Type} [LinearOrder α] [LinearOrder β] (a : Code α) (b : Code β) :
 Code (α ⊕ₗ β) where
 bound := a.bound+b.bound
 pos := a.pos.trans_le le_self_add
 rank := fun x => Sum.elim a.rank (fun y => a.bound+b.rank y) (ofLex x)
 range_lt := by
  rintro (x | x)
  · exact (a.range_lt x).trans_le le_self_add
  · exact (add_lt_add_iff_left _).mpr (b.range_lt x)
 mono := by
  rintro (x | x) (y | y) h
  · exact a.mono (Sum.Lex.inl_lt_inl_iff.mp h)
  · exact (a.range_lt x).trans_le le_self_add
  · exact (Sum.Lex.not_inr_lt_inl h).elim
  · exact (add_lt_add_iff_left _).mpr (b.mono (Sum.Lex.inr_lt_inr_iff.mp h))

/-- The binary coordinate of the actual chronological positions. -/
def chronologicalCode : Colex (Finset ℕ) → ℕ := Finset.orderIsoColex.symm

/-- The coordinate uses the original labels as binary exponents. -/
theorem chronologicalCode_eq_sum (K : Finset ℕ) :
    chronologicalCode (toColex K) = ∑ i ∈ K, 2 ^ i := rfl

private def colexCode : Code (Colex (Finset ℕ)) where
 bound := ω
 pos := Ordinal.omega0_pos
 rank := fun K => (chronologicalCode K : Ordinal)
 range_lt := fun K => Ordinal.natCast_lt_omega0 _
 mono := by
  intro x y h
  change ((Finset.orderIsoColex.symm x : ℕ) : Ordinal) <
    ((Finset.orderIsoColex.symm y : ℕ) : Ordinal)
  exact_mod_cast Finset.orderIsoColex.symm.strictMono h

private def monomialEncoding : Code MonomialInvariant.Val := natLex (natLex colexCode)

/-- The literal ordinal coordinates of a monomial value. -/
def monomialCode : MonomialInvariant.Val → Ordinal := monomialEncoding.rank

/-- The three original coordinates, with their chronological binary code. -/
theorem monomialCode_apply (a b : ℕ) (K : Finset ℕ) :
    monomialCode (toLex (a, toLex (b, toColex K))) =
      (ω * ω) * (a : Ordinal) + (ω * (b : Ordinal) + (∑ i ∈ K, 2 ^ i : ℕ)) := rfl

private def monomialBotEncoding : Code (WithBot MonomialInvariant.Val) :=
 botCodeLimit monomialEncoding
   (Ordinal.isSuccLimit_mul_right
     (mul_pos Ordinal.omega0_pos Ordinal.omega0_pos) Ordinal.isSuccLimit_omega0)

private def valueEncoding : (q : ℕ) → Code (CanonicalCentres.ValTy q)
 | 0 => natCode
 | q + 1 => natLex (sumCode monomialBotEncoding
     (topCode (natLex (topCode (valueEncoding q)))))

/-- Explicit recursive ordinal bound for the original value type. -/
def valueBound (q : ℕ) : Ordinal := (valueEncoding q).bound

/-- Explicit recursive ordinal coordinate of the original canonical value type. -/
def valueCode (q : ℕ) : CanonicalCentres.ValTy q → Ordinal := (valueEncoding q).rank

@[simp] theorem valueBound_zero : valueBound 0 = ω := rfl

/-- The bound is defined by the displayed ordinal arithmetic, without an abstract rank. -/
theorem valueBound_succ (q : ℕ) :
    valueBound (q + 1) =
      ((ω * ω) * ω + ((valueBound q + 1) * ω + 1)) * ω := rfl

@[simp] theorem valueCode_zero (v : ℕ) : valueCode 0 v = (v : Ordinal) := rfl

/-- Bottom of the monomial component keeps its literal endpoint code. -/
theorem valueCode_succ_bot (q o : ℕ) :
    valueCode (q + 1) (toLex (o, Sum.inlₗ ⊥)) =
      ((ω * ω) * ω + ((valueBound q + 1) * ω + 1)) * (o : Ordinal) + 0 := rfl

/-- A finite monomial value is the successor of its explicit triple coordinate. -/
theorem valueCode_succ_monomial (q o : ℕ) (v : MonomialInvariant.Val) :
    valueCode (q + 1) (toLex (o, Sum.inlₗ (v : WithBot MonomialInvariant.Val))) =
      ((ω * ω) * ω + ((valueBound q + 1) * ω + 1)) * (o : Ordinal) +
        (monomialCode v + 1) := rfl

/-- Top of the nonmonomial component follows all finite lower-step coordinates. -/
theorem valueCode_succ_top (q o : ℕ) :
    valueCode (q + 1) (toLex (o, Sum.inrₗ ⊤)) =
      ((ω * ω) * ω + ((valueBound q + 1) * ω + 1)) * (o : Ordinal) +
        ((ω * ω) * ω + (valueBound q + 1) * ω) := rfl

/-- The finite lower-step pair with top lower value has its own endpoint coordinate. -/
theorem valueCode_succ_lower_top (q o s : ℕ) :
    valueCode (q + 1) (toLex (o, Sum.inrₗ
      (((toLex (s, (⊤ : WithTop (CanonicalCentres.ValTy q)))) :
        ℕ ×ₗ WithTop (CanonicalCentres.ValTy q)) :
        WithTop (ℕ ×ₗ WithTop (CanonicalCentres.ValTy q))))) =
      ((ω * ω) * ω + ((valueBound q + 1) * ω + 1)) * (o : Ordinal) +
        ((ω * ω) * ω + ((valueBound q + 1) * (s : Ordinal) + valueBound q)) := rfl

/-- A finite lower value is recursively evaluated with no relabeling. -/
theorem valueCode_succ_lower (q o s : ℕ) (v : CanonicalCentres.ValTy q) :
    valueCode (q + 1) (toLex (o, Sum.inrₗ
      (((toLex (s, (v : WithTop (CanonicalCentres.ValTy q)))) :
        ℕ ×ₗ WithTop (CanonicalCentres.ValTy q)) :
        WithTop (ℕ ×ₗ WithTop (CanonicalCentres.ValTy q))))) =
      ((ω * ω) * ω + ((valueBound q + 1) * ω + 1)) * (o : Ordinal) +
        ((ω * ω) * ω + ((valueBound q + 1) * (s : Ordinal) + valueCode q v)) := rfl

/-- Every literal recursive coordinate lies below its explicit bound. -/
theorem valueCode_lt_bound (q : ℕ) (v : CanonicalCentres.ValTy q) :
    valueCode q v < valueBound q := (valueEncoding q).range_lt v

/-- The coordinate map is an order embedding of the actual original value type. -/
def valueEmbedding (q : ℕ) : CanonicalCentres.ValTy q ↪o Ordinal :=
 OrderEmbedding.ofStrictMono (valueCode q) (valueEncoding q).mono

/-- Strict order of actual original values is exactly strict order of the coordinates. -/
theorem valueCode_lt_iff (q : ℕ) (v w : CanonicalCentres.ValTy q) :
    valueCode q v < valueCode q w ↔ v < w := (valueEncoding q).mono.lt_iff_lt

open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
open MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers

universe u

/-- Evaluate the explicit coordinate directly on the original canonical invariant. -/
def actualValueCode {n : ℕ} (hn : 0 < n) (q : ℕ) {X : CMfd.{u} n}
    (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) : Ordinal :=
 valueCode q ((CanonicalCentres.invFamily hn q).inv 𝔪 T y)

/-- The direct original-invariant evaluation has the same explicit range bound. -/
theorem actualValueCode_lt_bound {n : ℕ} (hn : 0 < n) (q : ℕ) {X : CMfd.{u} n}
    (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    actualValueCode hn q 𝔪 T y < valueBound q := valueCode_lt_bound q _

/-- Comparisons of original invariant values are preserved and reflected. -/
theorem actualValueCode_lt_iff {n : ℕ} (hn : 0 < n) (q : ℕ) {X : CMfd.{u} n}
    (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y z : Y) :
    actualValueCode hn q 𝔪 T y < actualValueCode hn q 𝔪 T z ↔
      (CanonicalCentres.invFamily hn q).inv 𝔪 T y <
        (CanonicalCentres.invFamily hn q).inv 𝔪 T z := valueCode_lt_iff q _ _

end
end TranscendentalNakamaye.Pending.HironakaDisjointInvariantOrdinal
