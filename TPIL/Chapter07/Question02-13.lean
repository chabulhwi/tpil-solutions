/-
Copyright (c) 2025 Bulhwi Cha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bulhwi Cha
-/

set_option warn.sorry false

/-!
# Chapter 7 Quiz

## Question 2
-/

namespace Question02

/-- An inductive type with a finite, enumerated list of days of the week. -/
inductive DayOfWeek where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
deriving Repr

namespace DayOfWeek

/-- If `d` is a weekday, `DayOrEnd d` is the type of vectors with five days of the week; otherwise,
it's the type of vectors with two days of the week. -/
def DayOrEnd (d : DayOfWeek) : Type :=
  match d with
  | sunday    => Vector DayOfWeek 2
  | monday    => sorry
  | tuesday   => sorry
  | wednesday => sorry
  | thursday  => sorry
  | friday    => sorry
  | saturday  => sorry

/-- If `d` is a weekday, `listDayOrEnd d` is the vector with weekdays; otherwise, it's the vector
with the days in the weekend. -/
def listDayOrEnd (d : DayOfWeek) : DayOrEnd d :=
  match d with
  | sunday    => #v[sunday, saturday]
  | monday    => sorry
  | tuesday   => sorry
  | wednesday => sorry
  | thursday  => sorry
  | friday    => sorry
  | saturday  => sorry

end DayOfWeek

end Question02

/-!
## Question 3
-/

namespace Question03

namespace Bool

/-- Boolean “or”, also known as disjunction. -/
def or (a b : Bool) : Bool :=
  sorry

/-- Boolean “and”, also known as conjunction. -/
def and (a b : Bool) : Bool :=
  sorry

/-- Boolean negation, also known as Boolean complement. -/
def not (a : Bool) : Bool :=
  sorry

/-- `Bool.not_not`. -/
theorem not_involutive (a : Bool) : not (not a) = a :=
  sorry

/-- `Bool.and_comm`. -/
theorem and_commutative (a b : Bool) : and a b = and b a :=
  sorry

end Bool

end Question03

/-!
## Question 4
-/

namespace Question04

def Function.partComp {α : Type u} {β : Type v} {γ : Type w} (f : β → Option γ) (g : α → Option β)
    (x : α) : Option γ :=
  sorry

end Question04

/-!
## Question 5
-/

namespace Question05

example : Inhabited Bool := sorry
example : Inhabited Nat := sorry

section

variable {α : Type u} {β : Type v}

example {inst1 : Inhabited α} {inst2 : Inhabited β} : Inhabited (α × β) :=
  sorry

example {inst : Inhabited β} : Inhabited (α → β) :=
  sorry

end

end Question05

/-!
## Question 6
-/

namespace Question06

namespace Nat

def Odd : Type := sorry

example : Odd := sorry
example : Odd := sorry
example : Odd := sorry

end Nat

end Question06

/-!
## Question 7
-/

namespace Question07

theorem Nat.zero_add (n : Nat) : 0 + n = n :=
  sorry

end Question07

/-!
## Question 8
-/

namespace Question08

namespace List

theorem append_nil (as : List α) : as ++ [] = as :=
  sorry

theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  sorry

end List

end Question08

/-!
## Question 9
-/

namespace Question09

/-- The type of binary trees. -/
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

export BinaryTree (leaf node)

/-- a binary tree corresponding to the following ASCII art:
```
    o
   / \
  o   o
 / \
o   o
```
-/
def q09 : BinaryTree := sorry

end Question09

/-!
## Question 10
-/

namespace Question10

inductive Foo : Type where
  | cons₁ : Nat → Foo
  | cons₂ : Nat → Foo

export Foo (cons₁ cons₂)

end Question10

/-!
## Question 11
-/

namespace Question11

open Question10

example {a b : Nat} (h : cons₁ a = cons₁ b) {r : Nat → Nat → Prop} (h12 : a = b → r a b) : r a b :=
  (show (a = b → r a b) → r a b from Eq.recOn h
    (motive := fun (bar : Foo) (_ : cons₁ a = bar) ↦ Foo.recOn bar
      (cons₁ := fun (c : Nat) ↦ (a = c → r a c) → r a c)
      (cons₂ := fun (_ : Nat) ↦ sorry))
    (refl := sorry))
  (show a = b → r a b from sorry)

example {a b : Nat} (h : cons₁ a = cons₂ b) (p : Prop) : p :=
  Eq.recOn h
    (motive := fun (bar : Foo) (_ : cons₁ a = bar) ↦ Foo.recOn bar
      (cons₁ := fun (_ : Nat) ↦ sorry)
      (cons₂ := fun (_ : Nat) ↦ p))
    (refl := sorry)

end Question11

/-!
## Question 12
-/

namespace Question12

theorem Bool.false_ne_true : false ≠ true :=
  sorry

end Question12

/-!
## Question 13
-/

namespace Question13

namespace Eq

variable {α β : Type u} {a b c : α}

theorem symm (h : a = b) : b = a :=
  match h with
  | rfl => rfl

theorem trans (h₁ : a = b) (h₂ : b = c) : a = c :=
  sorry

theorem congr (f : α → β) (h : a = b) : f a = f b :=
  sorry

end Eq

end Question13
