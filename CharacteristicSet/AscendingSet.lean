import CharacteristicSet.TriangulatedSet
import CharacteristicSet.Initial

/-!
# Ascending Set and Basic Set

This file defines the abstract theory of **Ascending Set** and **Basic Set**.
An Ascending Set is a Triangulated Set with additional reduction properties.
A Basic Set is, informally, the "smallest" Ascending Set contained in a given set of polynomials.

We introduce two type main variables:
1. `AscendingSetTheory`:
  Abstracting the definition of an ascending set (e.g., strong vs. weak reduction).
2. `HasBasicSet`: Abstracting the algorithm to compute a basic set from a list of polynomials.

-/

section isMinimal

variable {α β γ : Type*} [Membership γ α] [Membership γ β]

/-- `a` is minimal in `b` if `a ⊆ b` and `a ≤ a'` for any `a' ⊆ b`.
This captures the definition of a Basic Set. -/
def isMinimal [LE α] (a : α) (b : β) : Prop :=
  (∀ ⦃c⦄, c ∈ a → c ∈ b) ∧ ∀ ⦃a'⦄, (∀ ⦃c⦄, c ∈ a' → c ∈ b) → a ≤ a'

theorem isMinimal_def [LE α] (a : α) (b : β) : isMinimal a b ↔
    (∀ ⦃c⦄, c ∈ a → c ∈ b) ∧ ∀ ⦃a'⦄, (∀ ⦃c⦄, c ∈ a' → c ∈ b) → a ≤ a' := Iff.rfl

theorem antisymmRel_of_isMinimal [LE α] {a₁ a₂ : α} {b : β} (h₁ : isMinimal a₁ b)
    (h₂ : isMinimal a₂ b) : AntisymmRel (· ≤ ·) a₁ a₂ := And.intro (h₁.2 h₂.1) (h₂.2 h₁.1)

variable [Preorder α] {a a₁ a₂ : α} {b b₁ b₂ : β}

theorem minimal_of_isMinimal_of_antisymmRel (h₁ : AntisymmRel (· ≤ ·) a₁ a₂)
    (h₂ : isMinimal a₂ b) : ∀ ⦃a'⦄, (∀ ⦃c⦄, c ∈ a' → c ∈ b) → a₁ ≤ a' :=
  fun _ h ↦ le_of_antisymmRel_of_le h₁ (h₂.2 h)

end isMinimal

open MvPolynomial

/--
The abstract theory of Ascending Sets.
This class allows us to define what it means for a `TriangulatedSet` to be an "Ascending Set".
Different instances can implement Ritt's strong ascending sets or Wu's weak ascending sets.
-/
class AscendingSetTheory (σ R : Type*) [CommSemiring R] [DecidableEq R] [LinearOrder σ] where
  /-- The reduction relation used to define the ascending property. -/
  protected reducedTo' : R[σ] → R[σ] → Prop
  decidableReducedTo : DecidableRel reducedTo' := by infer_instance
  /-- A key property linking the ascending set structure to the initial.
  If `S` is an ascending set, the initial of any non-constant element in `S`
  must be reduced with respect to `S`. -/
  protected initial_reducedToSet_of_mainVariable_ne_bot : ∀ ⦃S : TriangulatedSet σ R⦄ ⦃i : ℕ⦄,
    (∀ ⦃i j⦄, i < j → j < S.length → reducedTo' (S j) (S i)) →
    (S i).mainVariable ≠ ⊥ → (S i).initial.reducedToSet S

attribute [instance 900] AscendingSetTheory.decidableReducedTo

variable {R σ : Type*} [CommSemiring R] [DecidableEq R] [LinearOrder σ]

namespace TriangulatedSet

variable [AscendingSetTheory σ R] {S : TriangulatedSet σ R} {p : R[σ]}

/-- A Triangulated Set is an Ascending Set
if every element is reduced with respect to its predecessors. -/
def isAscendingSet (S : TriangulatedSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → AscendingSetTheory.reducedTo' (S j) (S i)

lemma isAscendingSet_iff : isAscendingSet S ↔ ∀ j < S.length, ∀ i < j,
    AscendingSetTheory.reducedTo' (S j) (S i) where
  mp h _ hj _ hi := h hi hj
  mpr h i j hi hj := h j hj i hi

instance : @DecidablePred (TriangulatedSet σ R) isAscendingSet := fun _ ↦
  decidable_of_iff _ isAscendingSet_iff.symm

theorem isAscendingSet_single (p : R[σ]) : (single p).isAscendingSet :=
  fun i _ hij hj ↦ False.elim <| Nat.not_lt_zero i <| lt_of_lt_of_le hij <|
    Nat.le_of_lt_succ <| lt_of_lt_of_le hj <| length_single_le_one

theorem isAscendingSet_empty : (∅ : TriangulatedSet σ R).isAscendingSet :=
  (single_eq_zero_iff.mp rfl : single (0 : R[σ]) = ∅) ▸ isAscendingSet_single 0

theorem isAscendingSet_take (n : ℕ) :
    S.isAscendingSet → (S.take n).isAscendingSet := fun hs i j hij hj ↦ by
  rewrite [take_apply' hj, take_apply' (lt_trans hij hj)]
  exact hs hij (lt_of_lt_of_le hj (Nat.min_le_right ..))

theorem isAscendingSet_drop (n : ℕ) : S.isAscendingSet → (S.drop n).isAscendingSet :=
  fun hs _ _ hij hj ↦ hs (Nat.add_lt_add_right hij n) (Nat.add_lt_of_lt_sub hj)

protected theorem isAscendingSet_concat (h : S.canConcat p)
    (hp : ∀ i < S.length, AscendingSetTheory.reducedTo' p (S i)) :
    S.isAscendingSet → (S.concat p).isAscendingSet := fun hs i j hij hj ↦ by
  have hi : i < S.length := lt_of_lt_of_le hij <| Nat.le_of_lt_succ hj
  simp only [length_concat, concat_apply, hi, reduceIte] at hj ⊢
  match Nat.lt_succ_iff_lt_or_eq.mp hj with
  | .inl hj => rewrite [if_pos hj]; exact hs hij hj
  | .inr hj => simp only [hj, lt_self_iff_false, reduceIte]; exact hp i hi

protected theorem isAscendingSet_takeConcat
    (hp : ∀ i < S.length, AscendingSetTheory.reducedTo' p (S i)) :
    S.isAscendingSet → (S.takeConcat p).isAscendingSet := fun h ↦ by
  unfold takeConcat
  split_ifs with h1 hc
  repeat exact isAscendingSet_single p
  refine TriangulatedSet.isAscendingSet_concat _ (fun n hn ↦ ?_) <| isAscendingSet_take _ h
  rewrite [take_apply' hn]
  exact hp _ (lt_of_lt_of_le hn (Nat.min_le_right ..))

end TriangulatedSet

/-- The type of Ascending Sets, which are Triangulated Sets satisfying the ascending property. -/
def AscendingSet (σ R : Type*) [CommSemiring R] [LinearOrder σ] [DecidableEq R]
    [AscendingSetTheory σ R] := { TS : TriangulatedSet σ R // TS.isAscendingSet }

/--
The interface for algorithms computing Basic Sets.
Any instance of this class provides a `basicSet` function that computes a minimal ascending set
contained in a given list of polynomials.
-/
class HasBasicSet (σ R : Type*) [CommSemiring R] [DecidableEq R] [LinearOrder σ]
    extends AscendingSetTheory σ R where
  /-- Computes a Basic Set from a list of polynomials. -/
  basicSet : List R[σ] → TriangulatedSet σ R
  /-- The output is always an Ascending Set. -/
  basicSet_isAscendingSet (l : List R[σ]) : (basicSet l).isAscendingSet
  /-- The output is a subset of the input. -/
  basicSet_subset (l : List R[σ]) : ∀ ⦃c⦄, c ∈ basicSet l → c ∈ l
  /-- Minimality condition: the output is ≤ any other ascending set contained in the input. -/
  basicSet_minimal (l : List R[σ]) :
      ∀ ⦃S⦄, S.isAscendingSet → (∀ ⦃p⦄, p ∈ S → p ∈ l) → basicSet l ≤ S
  /-- Rank reduction property: appending a reduced element strictly decreases the basic set rank.
  Crucial for proving termination of zero decomposition. -/
  basicSet_append_lt_of_exists_reducedToSet : ∀ ⦃l1 l2 : List R[σ]⦄,
      (∃ p ∈ l2, p ≠ 0 ∧ p.reducedToSet (basicSet l1)) → basicSet (l2 ++ l1) < basicSet l1

/-- Definition of Standard (Ritt) Ascending Set: strict degree reduction. -/
def StandardAscendingSet.isAscendingSet (S : TriangulatedSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → (S j).reducedTo (S i)

/-- Definition of Weak (Wu) Ascending Set: initial reduction. -/
def WeakAscendingSet.isAscendingSet (S : TriangulatedSet σ R) : Prop :=
  ∀ ⦃i j⦄, i < j → j < S.length → (S j).initial.reducedTo (S i)

theorem WeakAscendingSet.isAscendingSet_of_isStandardAscendingSet {S : TriangulatedSet σ R} :
    StandardAscendingSet.isAscendingSet S → WeakAscendingSet.isAscendingSet S :=
  fun h _ _ hij hj ↦ initial_reducedTo (h hij hj)


open TriangulatedSet

namespace AscendingSet

variable [AscendingSetTheory σ R] {S T : AscendingSet σ R} {p : R[σ]}

theorem initial_reducedToSet_of_mainVariable_ne_bot {S : TriangulatedSet σ R} {i : ℕ} :
    S.isAscendingSet → (S i).mainVariable ≠ ⊥ → (S i).initial.reducedToSet S := fun h ↦
  AscendingSetTheory.initial_reducedToSet_of_mainVariable_ne_bot h

theorem initial_reducedToSet_of_mainVariable_ne_bot' {S : TriangulatedSet σ R}
    (h : S.isAscendingSet) :
    p ∈ S → p.mainVariable ≠ ⊥ → p.initial.reducedToSet S := fun ⟨_, _, hi2⟩ hc ↦
  hi2 ▸ AscendingSet.initial_reducedToSet_of_mainVariable_ne_bot h (hi2 ▸ hc)

def mk {S : TriangulatedSet σ R} (h : S.isAscendingSet) : AscendingSet σ R := ⟨S, h⟩

instance : Coe (AscendingSet σ R) (TriangulatedSet σ R) := ⟨Subtype.val⟩

@[simp] theorem coe_mk (h) : (⟨S, h⟩ : AscendingSet σ R) = S := rfl

theorem coe_mk' (S : TriangulatedSet σ R) (h) : (⟨S, h⟩ : AscendingSet σ R) = S := rfl

theorem eq_of_coe_eq (h : S.val = T.val) : S = T := Subtype.ext h

theorem ne_of_coe_ne (h : S.val ≠ T.val) : S ≠ T := Subtype.coe_ne_coe.mp h

theorem coe_eq_coe : S.val = T.val ↔ S = T := Subtype.ext_iff.symm

theorem coe_ne_coe : S.val ≠ T.val ↔ S ≠ T := Subtype.coe_ne_coe

def length (S : AscendingSet σ R) : ℕ := S.val.length

def length_coe : S.length = S.val.length := rfl

instance : FunLike (AscendingSet σ R) ℕ R[σ] where
  coe S := S.val
  coe_injective' := DFunLike.coe_injective'.comp Subtype.coe_injective

@[ext]
theorem ext (h : ∀ i, S i = T i) : S = T := DFunLike.ext _ _ h

theorem ext' (h1 : S.length = T.length) (h2 : ∀ i < S.length, S i = T i) : S = T :=
  eq_of_coe_eq <| TriangulatedSet.ext' h1 h2

instance instSetLike : SetLike (AscendingSet σ R) R[σ] where
  coe := fun S ↦ S.val
  coe_injective' := SetLike.coe_injective'.comp Subtype.coe_injective

theorem mem_def : p ∈ S ↔ p ∈ S.val := Iff.rfl

instance : HasSubset (AscendingSet σ R) where
  Subset := InvImage (· ⊆ ·) Subtype.val

instance : HasSSubset (AscendingSet σ R) where
  SSubset := InvImage (· ⊂ ·) Subtype.val

theorem subset_def : S ⊆ T ↔ S.val ⊆ T.val := Iff.rfl

theorem ssubset_def : S ⊂ T ↔ S.val ⊂ T.val := Iff.rfl

def toFinset (S : AscendingSet σ R) : Finset R[σ] := S.val.toFinset

def toList (S : AscendingSet σ R) : List R[σ] := S.val.toList

noncomputable instance : EmptyCollection (AscendingSet σ R) := ⟨⟨∅, isAscendingSet_empty⟩⟩

noncomputable instance : Inhabited (AscendingSet σ R) := ⟨∅⟩

theorem empty_coe : (∅ : AscendingSet σ R) = (∅ : TriangulatedSet σ R) := rfl

theorem empty_eq_default : (∅ : AscendingSet σ R) = default := rfl

noncomputable def rank (S : AscendingSet σ R) : Lex (ℕ → WithTop (WithBot σ ×ₗ ℕ)) :=
  S.val.rank

theorem rank_def : S.rank = S.val.rank := rfl

instance : Preorder (AscendingSet σ R) := Preorder.lift ((↑) : _ → TriangulatedSet σ R)

theorem lt_def : S < T ↔ S.val < T.val := Iff.rfl

theorem le_def : S ≤ T ↔ S.val ≤ T.val := Iff.rfl

noncomputable instance : DecidableLE (AscendingSet σ R) :=
  fun _ _ ↦ decidable_of_iff _ le_def'.symm

noncomputable instance : DecidableLT (AscendingSet σ R) := decidableLTOfDecidableLE

instance : Setoid (AscendingSet σ R) := Setoid.comap ((↑) : _ → TriangulatedSet σ R) inferInstance

noncomputable instance instDecidableRelEquiv : @DecidableRel (AscendingSet σ R) _ (· ≈ ·) :=
  fun _ _ ↦ instDecidableAnd

theorem so_def : S ≈ T ↔ S.val ≈ T.val := Iff.rfl

section WellFounded

variable [Finite σ] (S' : Set (AscendingSet σ R))

instance instWellFoundedLT : WellFoundedLT (AscendingSet σ R) :=
  Subrelation.isWellFounded (InvImage (· < ·) Subtype.val) Iff.rfl.mp

instance instWellFoundedRelation : WellFoundedRelation (AscendingSet σ R) :=
  ⟨(· < ·), instWellFoundedLT.wf⟩

theorem Set.has_min (h : S'.Nonempty) : ∃ S ∈ S', ∀ T ∈ S', S ≤ T :=
  haveI : WellFounded (· < ·) := @wellFounded_lt (AscendingSet σ R) _ _
  have ⟨S, hS1, hS2⟩ := WellFounded.has_min this S' h
  ⟨S, hS1, fun T hT ↦ not_lt_iff_ge.mp (hS2 T hT)⟩

noncomputable def Set.min (h : S'.Nonempty) : AscendingSet σ R := Exists.choose (has_min S' h)

theorem Set.min_mem (h : S'.Nonempty) : min S' h ∈ S' :=
  (Exists.choose_spec (has_min S' h)).1

theorem Set.min_le (h : S'.Nonempty) : ∀ T ∈ S', min S' h ≤ T :=
  (Exists.choose_spec (has_min S' h)).2

end WellFounded

noncomputable instance instDecidableRelReducedToSet :
    @DecidableRel _ (AscendingSet σ R) MvPolynomial.reducedToSet :=
  fun _ S ↦ @decidable_of_iff _ _ reducedToSet_iff.symm (S.length.decidableBallLT _)

end AscendingSet


namespace MvPolynomial
namespace Classical

noncomputable section

variable [AscendingSetTheory σ R] [Finite σ] {α : Type*} [Membership R[σ] α]

/-- The main variableical existence of a Basic Set for any set of polynomials `a`.
This is guaranteed by the well-foundedness of the rank. -/
protected theorem hasBasicSet (a : α) : ∃ S : AscendingSet σ R, isMinimal S a :=
  AscendingSet.Set.has_min _ ⟨∅, fun n hn ↦ absurd hn <| notMem_empty n⟩

/-- Non-computable choice of a Basic Set for `a`. -/
protected def basicSet (a : α) : AscendingSet σ R := (Classical.hasBasicSet a).choose

protected theorem basicSet_isMinimal (a : α) : isMinimal (Classical.basicSet a) a :=
  (Classical.hasBasicSet a).choose_spec

end
end Classical

namespace List

variable [HasBasicSet σ R] (l : List R[σ]) {l1 l2 : List R[σ]} {S T : AscendingSet σ R}

/-- The Basic Set of a list `l`, as computed by the `HasBasicSet` instance. -/
def basicSet : AscendingSet σ R := ⟨HasBasicSet.basicSet l, HasBasicSet.basicSet_isAscendingSet l⟩

theorem basicSet_isMinimal (l : List R[σ]) : isMinimal l.basicSet l :=
  ⟨HasBasicSet.basicSet_subset l, fun ⟨_, hS⟩ ↦ HasBasicSet.basicSet_minimal l hS⟩

theorem basicSet_subset : ↑l.basicSet ⊆ {p | p ∈ l} := l.basicSet_isMinimal.1

theorem basicSet_minimal : ∀ ⦃S⦄, ↑S ⊆ {p | p ∈ l} → l.basicSet ≤ S := l.basicSet_isMinimal.2

theorem so_basicSet_of_isMinimal {l : List R[σ]} (h : isMinimal S l) : S ≈ l.basicSet := by
  apply antisymmRel_of_isMinimal h (basicSet_isMinimal l)

noncomputable instance instDecidableRelIsMinimal :
    @DecidableRel (AscendingSet σ R) (List R[σ]) isMinimal := fun S l ↦
  if h₁ : ∀ i < S.length, S i ∈ l then
    if h₂ : AntisymmRel (· ≤ ·) S l.basicSet then
      isTrue ⟨S.val.forall_mem_iff_forall_index.mpr h₁,
        minimal_of_isMinimal_of_antisymmRel h₂ l.basicSet_isMinimal⟩
    else isFalse fun h₃ ↦ absurd h₂ <| not_not.mpr <| so_basicSet_of_isMinimal h₃
  else isFalse (not_and_of_not_left _ <| (not_iff_not.mpr S.val.forall_mem_iff_forall_index).mpr h₁)

theorem basicSet_toList_so : l.basicSet.toList.basicSet ≈ l.basicSet := by
  refine And.intro ?_ ?_
  <;> refine basicSet_minimal _ fun p hp ↦ ?_
  · exact mem_toList_iff.mpr hp
  exact l.basicSet_subset <| mem_toList_iff.mp <| basicSet_subset _ hp

theorem basicSet_ge_of_subset : l1 ⊆ l2 → l2.basicSet ≤ l1.basicSet :=
  fun h ↦ l2.basicSet_minimal fun _ hp ↦ h <| l1.basicSet_subset hp

theorem basicSet_append_comm : (l1 ++ l2).basicSet ≈ (l2 ++ l1).basicSet :=
  have (l1 l2 : List R[σ]) : l2 ++ l1 ⊆ l1 ++ l2 := List.append_subset.mpr ⟨
    List.subset_append_of_subset_right l1 fun _ ↦ id,
    List.subset_append_of_subset_left l2 fun _ ↦ id⟩
  And.intro (basicSet_ge_of_subset <| this l1 l2) (basicSet_ge_of_subset <| this l2 l1)

theorem basicSet_append_lt_of_exists_reducedToSet
    (h : ∃ p ∈ l2, p ≠ 0 ∧ p.reducedToSet l1.basicSet) : (l2 ++ l1).basicSet < l1.basicSet :=
  HasBasicSet.basicSet_append_lt_of_exists_reducedToSet h

theorem _root_.TriangulatedSet.basicSet_toList_le_of_isAscendingSet {S : TriangulatedSet σ R}
    (hS : S.isAscendingSet) : S.toList.basicSet ≤ S := by
  change S.toList.basicSet ≤ ⟨S, hS⟩
  apply S.toList.basicSet_minimal
  simp only [mem_toList_iff, SetLike.setOf_mem_eq]
  rfl

end MvPolynomial.List
