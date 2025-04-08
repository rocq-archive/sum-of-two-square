(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(* Ugly Code to define the maximal exponent such that a^c | b
   *)
Require Export Aux.
Open Scope Z_scope.
 
Definition Zdiv_exp_spec:
 forall a b,
  ({c : Z |
   0 <= c /\
   ((1 < a -> 0 <= b ->  Z.divide (Zpower a c) b) /\
    ((1 < a -> 1 <= b ->  ~ Z.divide (Zpower a (1 + c)) b) /\
     (forall d,
      1 < a ->
      1 <= b ->
      0 <= d ->
      Z.divide (Zpower a d) b -> ~ Z.divide (Zpower a (1 + d)) b ->  c = d)))}).
intros a b.
case (Z_lt_dec 1 a); intros H1.
2:exists 0; auto with zarith.
case (Z_le_dec 0 b); intros H2.
2:exists 0; auto with zarith.
pattern b; apply Zlt_0_rec.
2:auto.
clear b H2; intros b.
intros f _.
case (Z_lt_dec 0 b); intros H3.
case (Z_lt_dec 1 b); intros H3'.
2:exists 0; auto with zarith.
case (Zdivide_dec a b); intros H4.
2:exists 0; (repeat (split; auto with zarith)).
2:rewrite Zpower_exp; auto with zarith.
2:rewrite Zpower_exp_1; auto with zarith.
2:rewrite Zpower_exp_0; auto with zarith.
2:rewrite Zmult_1_r; auto.
2:intros d H H0 H2 H5 H6; case (Zle_lt_or_eq 0 d); auto with zarith.
2:intros Hd; case H4.
2:apply Zdivide_trans with (a ^ d); auto.
2:replace d with (1 + (d - 1)); auto with zarith.
2:rewrite Zpower_exp; auto with zarith.
2:rewrite Zpower_exp_1; auto with zarith.
assert (Ha1:  0 <= Z.div b a < b ).
case (Zdivide_Zdiv_lt_pos a b); auto with zarith.
case (f _ Ha1).
intros res [Hb1 [Hb2 [Hb3 Hb4]]].
exists (1 + res); split; auto with zarith.
split.
intros Hc1 Hc2.
rewrite Zpower_exp; auto with zarith.
rewrite Zpower_exp_1; auto with zarith.
rewrite (Zdivide_Zdiv_eq a b); auto with zarith.
split; auto.
intros Hc1 Hc2.
case (Zle_lt_or_eq 1 (b / a)); auto with zarith.
case (Zdivide_Zdiv_lt_pos a b); auto with zarith.
intros Hd1 [q Hb5]; case Hb3; auto with zarith.
exists q.
apply Zmult_reg_l with a; auto with zarith.
rewrite <- (Zdivide_Zdiv_eq a b); auto with zarith.
apply trans_equal with ( 1 := Hb5 ).
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
intros tmp; assert (Hd1: a = b).
rewrite (Zdivide_Zdiv_eq a b); auto with zarith.
subst b; intros tmp1; absurd (Z.divide (Zpower a 2) a).
replace 2 with (1 + 1); auto with zarith.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
intros [q tmp2]; contradict H3'; replace a with 1; auto with zarith.
case (Zmult_1_inversion_l a q); auto with zarith.
apply Zmult_reg_l with a; auto with zarith.
apply Zdivide_trans with ( 2 := tmp1 ).
exists (Zpower a res).
replace 2 with (1 + 1); auto with zarith.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
intros d H H0 H2 H5 H6.
case (Zle_lt_or_eq 1 (b / a)); auto with zarith.
case (Zdivide_Zdiv_lt_pos a b); auto with zarith.
intros HH.
case (Zle_lt_or_eq 0 d); auto; intros H7.
replace res with (d - 1); auto with zarith.
apply sym_equal; apply Hb4; auto with zarith.
case H5; intros q Hq; exists q.
apply Zmult_reg_l with a; auto with zarith.
rewrite <- (Zdivide_Zdiv_eq a b); auto with zarith.
rewrite Hq; pattern d at 1; replace d with (1 + (d - 1)); auto with zarith.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
intros [q Hq]; case H6; exists q.
rewrite (Zdivide_Zdiv_eq a b); auto with zarith.
rewrite Hq.
replace (1 + (d - 1)) with d; auto with zarith.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
case H6; rewrite <- H7.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
(repeat rewrite Zpower_exp_0); auto with zarith.
rewrite Zmult_1_r; auto.
intros tmp; assert (Hd1: a = b).
rewrite (Zdivide_Zdiv_eq a b); auto with zarith.
case (Zle_lt_or_eq 0 res); auto; intros tmp1.
absurd (Z.divide a 1); auto with zarith.
intros [q tmp2].
case (Zmult_1_inversion_l a q); auto with zarith.
apply Zdivide_trans with (a ^ res).
pattern a at 1; rewrite <- (Zpower_exp_1 a); auto with zarith.
exists (Zpower a (res - 1)).
(repeat rewrite <- Zpower_exp); auto with zarith.
replace ((res - 1) + 1) with res; auto with zarith.
rewrite tmp; auto with zarith.
case (Zle_lt_or_eq 0 d); auto; intros tmp2.
case (Zle_lt_or_eq 1 d); auto with zarith; intros tmp3.
absurd (Z.divide (a * a) a); auto with zarith.
intros [q tmp4].
case (Zmult_1_inversion_l a q); auto with zarith.
apply Zmult_reg_l with a; auto with zarith.
subst b.
apply Zdivide_trans with (a ^ d); auto.
exists (Zpower a (d - 2)).
pattern d at 1; replace d with (((d - 2) + 1) + 1); auto with zarith.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
case H6; subst d; subst a; exists 1.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
(repeat rewrite Zpower_exp_0); auto with zarith.
split; auto with zarith.
replace b with 1; auto with zarith.
(repeat rewrite Zpower_exp_0); auto with zarith.
split; auto with zarith; split.
intros; (try (red; intros)); case (Zdivide_1 a); auto with zarith.
intros d H H0 H2 H4 H5; case Zle_lt_or_eq with ( 1 := H2 ); auto; intros H6.
case (Zdivide_1 a); auto with zarith.
apply Zdivide_trans with ( 2 := H4 ).
exists (Zpower a (Z.pred d)).
pattern a at 3; rewrite <- (Zpower_exp_1 a); auto with zarith.
rewrite <- Zpower_exp; auto with zarith.
replace (Z.pred d + 1) with d; auto with zarith.
exists 0; auto with zarith.
Defined.
 
Definition Zdiv_exp: Z -> Z ->  Z.
intros a b; case (Zdiv_exp_spec a b).
intros c _; exact c.
Defined.
 
Theorem Zdiv_exp_pos: forall a b,  (0 <= Zdiv_exp a b).
intros a b; unfold Zdiv_exp; case (Zdiv_exp_spec a b).
intros x H; case H; auto.
Qed.
 
Theorem Zdiv_exp_div:
 forall a b, 1 < a -> 0 <= b ->  Z.divide (Zpower a (Zdiv_exp a b)) b.
intros a b; unfold Zdiv_exp; case (Zdiv_exp_spec a b).
intros x H; case H; intros _ H1; case H1; auto.
Qed.
 
Theorem Zdiv_exp_not_div:
 forall a b, 1 < a -> 0 < b ->  ~ Z.divide (Zpower a (1 + Zdiv_exp a b)) b.
intros a b; unfold Zdiv_exp; case (Zdiv_exp_spec a b).
intros x H; case H; intros _ H1; case H1; intros _ H2; case H2; auto with zarith.
Qed.
 
Theorem Zdiv_exp_inv:
 forall a b c,
 1 < a ->
 0 < b ->
 0 <= c ->
 Z.divide (Zpower a c) b -> ~ Z.divide (Zpower a (1 + c)) b ->  c = Zdiv_exp a b.
intros a b; unfold Zdiv_exp; case (Zdiv_exp_spec a b).
intros c [H1 [H2 [H3 H4]]].
intros d L1 L2 L3 L4 L5; apply sym_equal; apply H4 with ( 4 := L4 );
 auto with zarith.
Qed.
 
Theorem Zdiv_exp_id: forall a, 1 < a ->  Zdiv_exp a a = 1.
intros a Ha; apply sym_eq; apply Zdiv_exp_inv; auto with zarith.
simpl; unfold Zpower_pos; simpl; exists 1; auto with zarith.
intros [q Hq].
case (Zmult_1_inversion_l a q); auto with zarith.
apply Zmult_reg_l with a; auto with zarith.
Qed.
 
Theorem Zdiv_exp_prime:
 forall a b c,
 0 < b ->
 0 < c -> prime a -> ~ Z.divide a c ->  Zdiv_exp a (b * c) = Zdiv_exp a b.
intros a b c H H0 H1 H2.
assert (Ha: 1 < a).
inversion H1; auto.
apply sym_equal; apply Zdiv_exp_inv; auto with zarith.
apply Zdiv_exp_pos; auto.
apply Zdivide_trans with b; auto with zarith.
apply Zdiv_exp_div; auto with zarith.
intros [q Hq].
case (Zdiv_exp_div a b); auto with zarith.
intros q1 Hq1.
assert (Hb: c * q1 = a * q); auto with zarith.
apply Zmult_reg_l with b; auto with zarith.
repeat rewrite Zmult_assoc.
rewrite Hq.
pattern b at 2; rewrite Hq1.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
generalize (Zdiv_exp_pos a b); auto with zarith.
assert (Hc: Z.divide a q1); auto.
apply Gauss with c; auto with zarith.
exists q; rewrite Hb; auto with zarith.
case (Zdiv_exp_not_div a b); auto with zarith.
case Hc; intros q2 Hq2; exists q2.
pattern b at 1; rewrite Hq1.
pattern q1 at 1; rewrite Hq2.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
generalize (Zdiv_exp_pos a b); auto with zarith.
Qed.
 
Theorem Zdiv_exp_succ:
 forall a b, 0 < b -> prime a ->  Zdiv_exp a (a * b) = 1 + Zdiv_exp a b.
intros a b H H0.
assert (Ha: 1 < a).
inversion H0; auto.
apply sym_equal; apply Zdiv_exp_inv; auto with zarith.
generalize (Zdiv_exp_pos a b); auto with zarith.
case (Zdiv_exp_div a b); auto with zarith.
intros q Hq; exists q.
pattern b at 1; rewrite Hq.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
generalize (Zdiv_exp_pos a b); auto with zarith.
intros [q Hq].
case (Zdiv_exp_not_div a b); auto with zarith.
exists q.
apply Zmult_reg_l with a; auto with zarith.
rewrite Hq.
(repeat rewrite Zpower_exp); auto with zarith.
(repeat rewrite Zpower_exp_1); auto with zarith.
generalize (Zdiv_exp_pos a b); auto with zarith.
generalize (Zdiv_exp_pos a b); auto with zarith.
Qed.
