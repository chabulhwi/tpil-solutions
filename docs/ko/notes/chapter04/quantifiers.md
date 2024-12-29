# 술어 논리

## 정량어

### 보편 정량어

* 이름: 보편 정량어
* 기호: `∀` ("모든"이라고 읽음)
* 편집기 단축키: `\forall`
* 뜻: 유형 `α`와 단항 술어 `p : α → Prop`가 주어져 있을 때, 명제 `∀ (x : α), p x`는 "유형 `α`에 속하는 모든 `x`에 대해, `p x`이다."라는 뜻이다.
* 린에서의 정의: `p`가 임의의 식이면, `∀ (x : α), p`는 `(x : α) → p`의 다른 표기법이다.
* 추론 규칙
  - 도입 규칙: 각각의 항 `x : α`에 대해 `p x`가 성립하면, `∀ (x : α), p x`가 성립한다. (*보편 일반화*)
  - 제거 규칙: `a : α`가 주어져 있을 때, `∀ (x : α), p x`에서 `p a`가 도출된다.
  (*보편 예시*)

### 존재 정량어

* 이름: 존재 정량어
* 린에서의 이름: `Exists`
* 기호: `∃` ("어떤"이라고 읽거나 "…이 존재한다"라고 읽음)
* 편집기 단축키: `\ex`, `\exists`
* 뜻: 유형 `α`와 단항 술어 `p : α → Prop`가 주어져 있을 때, 명제 `∃ (x : α), p x`는 "유형 `α`에 속하고 `p x`를 성립시키는 항 `x`가 존재한다."라는 뜻이다.
* 추론 규칙
  - 도입 규칙: `a : α`가 주어져 있을 때, `p a`에서 `∃ (x : α), p x`가 도출된다.
  (*존재 도입*)
  - 제거 규칙: `∃ (x : α), p x`와 `∀ (a : α), p a → q`에서 `q`가 도출된다. (*존재 제거*)