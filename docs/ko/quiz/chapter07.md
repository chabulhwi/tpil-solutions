# 7장 퀴즈

## 문제 1

\(a\) `Bool` 유형의 도입 규칙과 제거 규칙은 무엇인가? \
\(b\) `Bool` 유형의 구성자와 재귀자는 무엇인가?

## 문제 2

`DayOfWeek` 이름 공간 안의 두 함수 `DayOrEnd`와 `listDayOrEnd`를 정의하라.

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

## 문제 3

`Bool` 유형에 대한 불 연산 `and`, `or`, `not`을 정의하고, 아래 나열된 두 항등식을 검증하라.

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

## 문제 4

`α`에서 `β`로의 그리고 `β`에서 `γ`로의 부분 함수의 합성 개념을 정의하라. 그러고 나서, 이 개념이 우리가 예상한 대로 작동함을 보여라.

## 문제 5

두 유형 `Bool`과 `Nat`에 거주자가 있고, 거주자가 있는 두 유형의 곱에도 거주자가 있으며, 거주자가 있는 유형으로의 함수의 유형에도 거주자가 있음을 보여라.

## 문제 6

`Subtype`을 이용해 홀수의 유형을 정의하라.

## 문제 7

`Nat.recOn`을 이용해 정리 `Nat.zero_add`를 증명하라.

## 문제 8

다음 정리를 증명하라.

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

## 문제 9

```
    o
   / \
  o   o
 / \
o   o
```

위의 아스키 아트에 대응하는 `BinaryTree`의 원소를 정의하라.

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

## 문제 10

```lean
namespace Question10

inductive Foo : Type where
  | cons₁ : Nat → Foo
  | cons₂ : Nat → Foo

export Foo (cons₁ cons₂)

end Question10
```

위에서 정의된 귀납형 `Foo`의 구성자들에 대한 다음 명제가 참임을 증명하거나 거짓임을 증명하라.

\(a\) `∀ {a b : Nat}, cons₁ a = cons₁ b → a = b` \
\(b\) `∃ (a b : Nat), cons₁ a = cons₂ b`

## 문제 11

`sorry` 식별자를 실제 식으로 바꿔 다음 보기를 증명하라.

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

## 문제 12

다음 정리를 증명하라.

```lean
namespace Question12

theorem Bool.false_ne_true : false ≠ true :=
  sorry

end Question12
```

## 문제 13

다음 정리를 증명하라.

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

## 문제 14

다음 문단에서, 대괄호로 묶인 명사구 'the latter'와 'it'은 무엇을 가리키는가?

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

## 문제 15

다음 정리를 증명하라.

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

## 문제 16

```
     0
   / | \
  1  2  3
 / \     \
4   5     6
```

위의 아스키 아트에 대응하는 `FinTree Nat`의 원소를 정의하라.

```lean
namespace Question16

inductive FinTree (α : Type u) where
  | mk : α → List (FinTree α) → FinTree α

def q16 : FinTree Nat :=
  sorry

end Question16
```
