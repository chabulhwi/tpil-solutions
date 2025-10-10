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
