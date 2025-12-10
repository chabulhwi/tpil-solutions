# Chapter 7 Quiz

## Question 1

\(a\) What are the introduction and elimination rules for the `Bool` type? \
\(b\) What are the constructors and recursor of the `Bool` type?

## Question 2

Define the following two functions, `DayOrEnd` and `listDayOrEnd`, which are
within the `DayOfWeek` namespace:

```lean
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
```

## Question 3

Define boolean operations `and`, `or`, `not` on the `Bool` type, and verify the
two identities listed below:

```lean
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
```

## Question 4

Develop a notion of composition for partial functions from `α` to `β` and `β` to
`γ`, and show that it behaves as expected.

## Question 5

Show that `Bool` and `Nat` are inhabited, that the product of two inhabited
types is inhabited, and that the type of functions to an inhabited type is
inhabited.

## Question 6

Use `Subtype` to define the type of odd numbers.

## Question 7

Use `Nat.recOn` to prove the theorem `Nat.zero_add`.

## Question 8

Prove the following theorems:

```
namespace Question08

namespace List

theorem append_nil (as : List α) : as ++ [] = as :=
  sorry

theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  sorry

end List

end Question08
```

## Question 9

```
    o
   / \
  o   o
 / \
o   o
```

Define an element of `BinaryTree` that corresponds to the above ASCII art:

```lean
namespace Question09

/-- The type of binary trees. -/
inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

export BinaryTree (leaf node)

def q09 : BinaryTree := sorry

end Question09
```

## Question 10

```lean
namespace Question10

inductive Foo : Type where
  | cons₁ : Nat → Foo
  | cons₂ : Nat → Foo

export Foo (cons₁ cons₂)

end Question10
```

Prove or disprove each of the following propositions about the constructors for
the inductive type `Foo` defined above.

\(a\) `∀ {a b : Nat}, cons₁ a = cons₁ b → a = b` \
\(b\) `∃ (a b : Nat), cons₁ a = cons₂ b`

## Question 11

Prove the following examples, replacing each `sorry` identifier with an actual
expression:

```lean
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
```

## Question 12

Prove the following theorem:

```lean
namespace Question12

theorem Bool.false_ne_true : false ≠ true :=
  sorry

end Question12
```

## Question 13

Prove the following theorems:

```lean
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
```

## Question 14

In the following paragraph, what do the noun phrases "the latter" and "it",
enclosed in square brackets, refer to?

> We have seen that the constructor to an inductive type takes
> *parameters*—intuitively, the arguments that remain fixed throughout the
> inductive construction—and *indices*, the arguments parameterizing the family
> of types that is simultaneously under construction. Each constructor should
> have a type, where the argument types are built up from previously defined
> types, the parameter and index types, and the inductive family currently being
> defined. The requirement is that if **[the latter]** is present at all,
> **[it]** occurs only *strictly positively*. This means simply that any
> argument type to the constructor in which **[it]** occurs is a dependent arrow
> type in which the inductive type under definition occurs only as the resulting
> type, where the indices are given in terms of constants and previous
> arguments.

## Question 15

Prove the following theorems:

```lean
namespace Question15

namespace Nat

mutual
  inductive Even : Nat → Prop where
    | even_zero : Even 0
    | even_succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)
end

theorem odd_one : Odd 1 :=
  sorry

theorem even_two : Even 2 :=
  sorry

end Nat

end Question15
```

## Question 16

```
     0
   / | \
  1  2  3
 / \     \
4   5     6
```

Define an element of `FinTree Nat` that corresponds to the above ASCII art:

```lean
namespace Question16

inductive FinTree (α : Type u) where
  | mk : α → List (FinTree α) → FinTree α

def q16 : FinTree Nat :=
  sorry

end Question16
```
