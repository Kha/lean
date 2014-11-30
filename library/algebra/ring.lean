/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.ring
Authors: Jeremy Avigad, Leonardo de Moura

Structures with multiplicative and additive components, including semirings, rings, and fields.
The development is modeled after Isabelle's library.
-/

import logic.eq data.unit data.sigma data.prod
import algebra.function algebra.binary algebra.group

open eq eq.ops

namespace algebra

variable {A : Type}

/- auxiliary classes -/

structure distrib [class] (A : Type) extends has_mul A, has_add A :=
(left_distrib : ∀a b c, mul a (add b c) = add (mul a b) (mul a c))
(right_distrib : ∀a b c, mul (add a b) c = add (mul a c) (mul b c))

theorem left_distrib [s : distrib A] (a b c : A) : a * (b + c) = a * b + a * c :=
!distrib.left_distrib

theorem right_distrib [s: distrib A] (a b c : A) : (a + b) * c = a * c + b * c :=
!distrib.right_distrib

structure mul_zero [class] (A : Type) extends has_mul A, has_zero A :=
(zero_mul_eq : ∀a, mul zero a = zero)
(mul_zero_eq : ∀a, mul a zero = zero)

theorem zero_mul_eq [s : mul_zero A] (a : A) : 0 * a = 0 := !mul_zero.zero_mul_eq
theorem mul_zero_eq [s : mul_zero A] (a : A) : a * 0 = 0 := !mul_zero.mul_zero_eq

structure zero_ne_one_class [class] (A : Type) extends has_zero A, has_one A :=
(zero_ne_one : zero ≠ one)

theorem zero_ne_one [s: zero_ne_one_class A] : 0 ≠ 1 := @zero_ne_one_class.zero_ne_one A s

/- semiring -/
structure semiring [class] (A : Type) extends add_comm_monoid A, monoid A, distrib A, mul_zero A,
    zero_ne_one_class A

structure comm_semiring [class] (A : Type) extends semiring A, comm_semigroup A

/- abstract divisibility -/

structure has_dvd [class] (A : Type) extends has_mul A :=
(dvd : A → A → Prop)
(dvd_intro : ∀a b c, mul a b = c → dvd a c)
(dvd_ex : ∀ a b, dvd a b → ∃c, mul a c = b)

definition dvd [s : has_dvd A] (a b : A) : Prop := has_dvd.dvd a b
infix `|` := dvd

theorem dvd.intro [s : has_dvd A] {a b c : A} : a * b = c → a | c := !has_dvd.dvd_intro

theorem dvd.ex [s : has_dvd A] {a b : A} : a | b → ∃c, a * c = b := !has_dvd.dvd_ex

theorem dvd.elim [s : has_dvd A] {P : Prop} {a b : A} (H₁ : a | b) (H₂ : ∀c, a * c = b → P) : P :=
exists_elim (dvd.ex H₁) H₂

structure comm_semiring_dvd [class] (A : Type) extends comm_semiring A, has_dvd A

section comm_semiring_dvd

  variables [s : comm_semiring_dvd A] (a b c : A)
  include s

  theorem dvd.refl : a | a := dvd.intro (!mul.right_id)

  theorem dvd.trans {a b c : A} (H₁ : a | b) (H₂ : b | c) : a | c :=
  dvd.elim H₁
    (take d, assume H₃ : a * d = b,
      dvd.elim H₂
        (take e, assume H₄ : b * e = c,
          @dvd.intro _ _ _ (d * e) _
            (calc
              a * (d * e) = (a * d) * e : mul.assoc
                ... = b * e : H₃
                ... = c : H₄)))

  theorem eq_zero_of_zero_dvd {H : 0 | a} : a = 0 :=
    dvd.elim H (take c, assume H' : 0 * c = a, (H')⁻¹ ⬝ !zero_mul_eq)

  theorem dvd_zero : a | 0 := dvd.intro !mul_zero_eq

  theorem one_dvd : 1 | a := dvd.intro !mul.left_id

  theorem dvd_mul_right : a | a * b := dvd.intro rfl

  theorem dvd_mul_left : a | b * a := mul.comm a b ▸ dvd_mul_right a b

  theorem dvd_mul_of_dvd_left {a b : A} (H : a | b) (c : A) : a | b * c :=
  dvd.elim H
    (take d,
      assume H₁ : a * d = b,
      dvd.intro
        (calc
          a * (d * c) = a * d * c : (!mul.assoc)⁻¹
             ... = b * c : H₁))

  theorem dvd_mul_of_dvd_right {a b : A} (H : a | b) (c : A) : a | c * b :=
  !mul.comm ▸ (dvd_mul_of_dvd_left H _)

  theorem mul_dvd_mul {a b c d : A} (dvd_ab : a | b) (dvd_cd : c | d) : a * c | b * d :=
  dvd.elim dvd_ab
    (take e, assume Haeb : a * e = b,
      dvd.elim dvd_cd
        (take f, assume Hcfd : c * f = d,
          dvd.intro
            (calc
              a * c * (e * f) = a * (c * (e * f)) : mul.assoc
                ... = a * (e * (c * f)) : mul.left_comm
                ... = a * e * (c * f) : (!mul.assoc)⁻¹
                ... = b * (c * f) : Haeb
                ... = b * d : Hcfd)))

  theorem dvd_of_mul_right_dvd {a b c : A} (H : a * b | c) : a | c :=
  dvd.elim H (take d, assume Habdc : a * b * d = c, dvd.intro (!mul.assoc⁻¹ ⬝ Habdc))

  theorem dvd_of_mul_left_dvd {a b c : A} (H : a * b | c) : b | c :=
  dvd_of_mul_right_dvd (mul.comm a b ▸ H)

  theorem dvd_add {a b c : A} (Hab : a | b) (Hac : a | c) : a | b + c :=
  dvd.elim Hab
    (take d, assume Hadb : a * d = b,
      dvd.elim Hac
        (take e, assume Haec : a * e = c,
          dvd.intro (show a * (d + e) = b + c, from Hadb ▸ Haec ▸ left_distrib a d e)))

end comm_semiring_dvd


/- ring -/

structure ring [class] (A : Type) extends add_comm_group A, monoid A, distrib A, zero_ne_one_class A

definition ring.to_semiring [instance] [s : ring A] : semiring A :=
semiring.mk ring.add ring.add_assoc !ring.zero ring.add_left_id
  add.right_id   -- note: we've shown that add_right_id follows from add_left_id in add_comm_group
  ring.add_comm ring.mul ring.mul_assoc !ring.one ring.mul_left_id ring.mul_right_id
  ring.left_distrib ring.right_distrib
  (take a,
    have H : 0 * a  + 0 = 0 * a + 0 * a, from
      calc
        0 * a + 0 = 0 * a : add.right_id
          ... = (0 + 0) * a : {(add.right_id 0)⁻¹}
          ... = 0 * a + 0 * a : ring.right_distrib,
    show 0 * a = 0, from  (add.left_cancel H)⁻¹)
  (take a,
    have H : a * 0 + 0 = a * 0 + a * 0, from
      calc
        a * 0 + 0 = a * 0 : add.right_id
          ... = a * (0 + 0) : {(add.right_id 0)⁻¹}
          ... = a * 0 + a * 0 : ring.left_distrib,
    show a * 0 = 0, from  (add.left_cancel H)⁻¹)
  !ring.zero_ne_one

section

  variables [s : ring A] (a b c d e : A)
  include s

  theorem neg_mul_eq_neg_mul : -(a * b) = -a * b :=
  neg_eq_of_add_eq_zero
    (calc
      a * b + -a * b = (a + -a) * b : right_distrib
        ... = 0 * b : add.right_inv
        ... = 0 : zero_mul_eq)

  theorem neg_mul_eq_mul_neg : -(a * b) = a * -b :=
  neg_eq_of_add_eq_zero
    (calc
      a * b + a * -b = a * (b + -b) : left_distrib
        ... = a * 0 : add.right_inv
        ... = 0 : mul_zero_eq)

  theorem neg_mul_neg_eq : -a * -b = a * b :=
  calc
     -a * -b = -(a * -b) : !neg_mul_eq_neg_mul⁻¹
       ... = - -(a * b) : neg_mul_eq_mul_neg
       ... = a * b : neg_neg_eq

  theorem neg_mul_comm : -a * b = a * -b := !neg_mul_eq_neg_mul⁻¹ ⬝ !neg_mul_eq_mul_neg

  theorem mul_sub_left_distrib : a * (b - c) = a * b - a * c :=
  calc
    a * (b - c) = a * b + a * -c : left_distrib
      ... = a * b + - (a * c) : {!neg_mul_eq_mul_neg⁻¹}
      ... = a * b - a * c : rfl

  theorem mul_sub_right_distrib : (a - b) * c = a * c - b * c :=
  calc
    (a - b) * c = a * c  + -b * c : right_distrib
      ... = a * c + - (b * c) : {!neg_mul_eq_neg_mul⁻¹}
      ... = a * c - b * c : rfl

  -- TODO: can calc mode be improved to make this easier?
  -- TODO: there is also the other direction. It will be easier when we
  -- have the simplifier.

  theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e : !add.comm ▸ !iff.refl
      ... ↔ a * e + c - b * e = d : iff.symm !sub_eq_iff_eq_add
      ... ↔ a * e - b * e + c = d : !sub_add_eq_add_sub ▸ !iff.refl
      ... ↔ (a - b) * e + c = d : !mul_sub_right_distrib ▸ !iff.refl

end

structure comm_ring [class] (A : Type) extends ring A, comm_semigroup A

definition comm_ring.to_comm_semiring [instance] [s : comm_ring A] : comm_semiring A :=
comm_semiring.mk comm_ring.add comm_ring.add_assoc (@comm_ring.zero A s)
  comm_ring.add_left_id comm_ring.add_right_id comm_ring.add_comm comm_ring.mul comm_ring.mul_assoc
  (@comm_ring.one A s) comm_ring.mul_left_id comm_ring.mul_right_id comm_ring.left_distrib
  comm_ring.right_distrib zero_mul_eq mul_zero_eq (@comm_ring.zero_ne_one A s)
  comm_ring.mul_comm

section

  variables [s : comm_ring A] (a b c d e : A)
  include s

  -- TODO: wait for the simplifier
  theorem mul_self_sub_mul_self_eq : a * a - b * b = (a + b) * (a - b) := sorry

  theorem mul_self_sub_one_eq : a * a - 1 = (a + 1) * (a - 1) :=
  mul.right_id 1 ▸ mul_self_sub_mul_self_eq a 1

end

structure comm_ring_dvd [class] (A : Type) extends comm_ring A, has_dvd A

definition comm_ring_dvd.to_comm_semiring_dvd [instance] [s : comm_ring_dvd A] :
    comm_semiring_dvd A :=
comm_semiring_dvd.mk comm_ring_dvd.add comm_ring_dvd.add_assoc (@comm_ring_dvd.zero A s)
  comm_ring_dvd.add_left_id comm_ring_dvd.add_right_id comm_ring_dvd.add_comm
  comm_ring_dvd.mul comm_ring_dvd.mul_assoc (@comm_ring_dvd.one A s) comm_ring_dvd.mul_left_id
  comm_ring_dvd.mul_right_id comm_ring_dvd.left_distrib comm_ring_dvd.right_distrib
  zero_mul_eq mul_zero_eq (@comm_ring_dvd.zero_ne_one A s) comm_ring_dvd.mul_comm
  comm_ring_dvd.dvd (@comm_ring_dvd.dvd_intro A s) (@comm_ring_dvd.dvd_ex A s)

section

  variables [s : comm_ring_dvd A] (a b c d e : A)
  include s

  theorem dvd_neg_iff_dvd : a | -b ↔ a | b :=
  iff.intro
    (assume H : a | -b,
      dvd.elim H
        (take c, assume H' : a * c = -b,
          dvd.intro
            (calc
              a * -c = -(a * c) : {!neg_mul_eq_mul_neg⁻¹}
                ... = -(-b) : H'
                ... = b : neg_neg_eq)))
    (assume H : a | b,
      dvd.elim H
        (take c, assume H' : a * c = b,
          dvd.intro
            (calc
              a * -c = -(a * c) : {!neg_mul_eq_mul_neg⁻¹}
                ... = -b : H')))

  theorem neg_dvd_iff_dvd : -a | b ↔ a | b :=
  iff.intro
    (assume H : -a | b,
      dvd.elim H
        (take c, assume H' : -a * c = b,
          dvd.intro
            (calc
              a * -c = -a * c : !neg_mul_comm⁻¹
                ... = b : H')))
    (assume H : a | b,
      dvd.elim H
        (take c, assume H' : a * c = b,
          dvd.intro
            (calc
              -a * -c = a * c : neg_mul_neg_eq
                ... = b : H')))

    theorem dvd_sub (H₁ : a | b) (H₂ : a | c) : a | (b - c) :=
    dvd_add H₁ (iff.elim_right !dvd_neg_iff_dvd H₂)

end


/- integral domains -/

-- TODO: some properties here may extend to cancellative semirings. It is worth the effort?

structure no_zero_divisors [class] (A : Type) extends has_mul A, has_zero A :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀a b, mul a b = zero → a = zero ∨ b = zero)

theorem eq_zero_or_eq_zero_of_mul_eq_zero {A : Type} [s : no_zero_divisors A] {a b : A}
    (H : a * b = 0) :
  a = 0 ∨ b = 0 := !no_zero_divisors.eq_zero_or_eq_zero_of_mul_eq_zero H

structure integral_domain [class] (A : Type) extends comm_ring_dvd A, no_zero_divisors A

section

  variables [s : integral_domain A] (a b c d e : A)
  include s

  theorem mul_ne_zero_of_ne_zero_ne_zero {a b : A} (H1 : a ≠ 0) (H2 : b ≠ 0) : a * b ≠ 0 :=
  assume H : a * b = 0,
    or.elim (eq_zero_or_eq_zero_of_mul_eq_zero H) (assume H3, H1 H3) (assume H4, H2 H4)

  theorem mul.cancel_right {a b c : A} (Ha : a ≠ 0) (H : b * a = c * a) : b = c :=
  have H1 : b * a - c * a = 0, from iff.mp !eq_iff_sub_eq_zero H,
  have H2 : (b - c) * a = 0, from eq.trans !mul_sub_right_distrib H1,
  have H3 : b - c = 0, from or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero H2) Ha,
  iff.elim_right !eq_iff_sub_eq_zero H3

  theorem mul.cancel_left {a b c : A} (Ha : a ≠ 0) (H : a * b = a * c) : b = c :=
  have H1 : a * b - a * c = 0, from iff.mp !eq_iff_sub_eq_zero H,
  have H2 : a * (b - c) = 0, from eq.trans !mul_sub_left_distrib H1,
  have H3 : b - c = 0, from or.resolve_right (eq_zero_or_eq_zero_of_mul_eq_zero H2) Ha,
  iff.elim_right !eq_iff_sub_eq_zero H3

  -- TODO: do we want the iff versions?

  -- TODO: wait for simplifier
  theorem mul_self_eq_mul_self_iff (a b : A) : a * a = b * b ↔ a = b ∨ a = -b := sorry

  theorem mul_self_eq_one_iff (a : A) : a * a = 1 ↔ a = 1 ∨ a = -1 := sorry

  -- TODO: c - b * c → c = 0 ∨ b = 1 and variants

  theorem dvd_of_mul_dvd_mul_left {a b c : A} (Ha : a ≠ 0) (Hdvd : a * b | a * c) : b | c :=
  dvd.elim Hdvd
    (take d,
      assume H : a * b * d = a * c,
      have H1 : b * d = c, from mul.cancel_left Ha (mul.assoc a b d ▸ H),
      dvd.intro H1)

  theorem dvd_of_mul_dvd_mul_right {a b c : A} (Ha : a ≠ 0) (Hdvd : b * a | c * a) : b | c :=
  dvd.elim Hdvd
    (take d,
      assume H : b * a * d = c * a,
      have H1 : b * d * a = c * a, from eq.trans !mul.right_comm H,
      have H2 : b * d = c, from mul.cancel_right Ha H1,
      dvd.intro H2)

end

end algebra
