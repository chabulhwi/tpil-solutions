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
