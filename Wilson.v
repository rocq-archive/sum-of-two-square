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


(* 
   Proof of Wilson theorem
   The proof is as follows:
    (p-1)! = 1 * 2 ... * p-2 * p-1
    we have
      1 mod p = 1
      p -1 mod p = - 1
      and for a, 2 <= a <= p-2, there is an inverse b (ab mod p =1)
            such 2 <= b <= p-2 and a<>b
            so we can rearrange the product 2 ... * p-2 in pairs
            of an element and its inverse. This means that
             2 ... * p-2 (mod p) = 1*)
Require Export ZisMod.
Open Scope Z_scope.
 
Theorem Zis_mod_rel_prime_inverse:
 forall a p,
 1 < p ->
 rel_prime a p ->
  (exists b , ( 1 <= b <= p - 1 ) /\ (rel_prime b p /\ Zis_mod (a * b) 1 p) ).
intros a p Hp H.
assert (Ha: Bezout a p 1).
apply rel_prime_bezout; auto.
inversion_clear Ha as [u v Huv].
exists (Z.modulo u p); split; [split | split].
case (Z_mod_lt u p); auto with zarith; intros H1 H2.
case (Zle_lt_or_eq _ _ H1); clear H1; intros H1; auto with zarith.
assert (Ha: Z.divide p u).
apply Zmod_divide; auto with zarith.
inversion_clear Ha as [k Hk].
case (Zmult_1_inversion_l p (k * a + v)); auto with zarith.
case (Z_mod_lt u p); auto with zarith; intros H1 H2.
apply bezout_rel_prime.
apply Bezout_intro with a ((u / p) * a + v).
apply trans_equal with ((p * (u / p) + u mod p) * a + v * p); auto with zarith.
rewrite <- Z_div_mod_eq_full; auto with zarith.
apply Zis_mod_def; auto with zarith.
rewrite (Zmod_def_small 1); auto with zarith.
rewrite Zmod_mult; auto with zarith.
rewrite Zmod_mod; auto with zarith.
rewrite <- Zmod_mult; auto with zarith.
replace (a * u) with (1 + - v * p); auto with zarith.
rewrite Z_mod_plus; auto with zarith.
apply Zmod_def_small; auto with zarith.
Qed.
 
Theorem wilson: forall p, prime p ->  Zis_mod (Zfact (p - 1)) (- 1) p.
intros p Hp.
case Zle_lt_or_eq with ( 1 := prime_le_2 p Hp ); auto with zarith; intros Hp1.
unfold Zfact.
replace (p - 1) with ((p - 2) + 1); auto with zarith.
rewrite Zprod_S_right; auto with zarith.
apply Zis_mod_def; auto with zarith.
rewrite Zmod_mult; auto with zarith.
replace (Zprod 1 (p - 2) (fun (x : Z) => x) mod p) with 1.
rewrite Zmult_1_l.
rewrite Zmod_mod; auto with zarith.
replace ((p - 2) + 1) with (- 1 + 1 * p); auto with zarith.
apply Z_mod_plus; auto with zarith.
apply sym_equal.
case (Zle_lt_or_eq 3 p); auto with zarith; clear Hp1; intros Hp1.
rewrite Zprod_S_left; auto with zarith.
replace (1 + 1) with 2; auto with zarith.
rewrite Zmult_1_l.
unfold Zprod; rewrite Zle_imp_le_bool; auto with zarith.
cut
 (forall a,
  In a (progression Z.succ 2 (Z.abs_nat ((1 + (p - 2)) - 2))) ->
   (exists b ,
    In b (progression Z.succ 2 (Z.abs_nat ((1 + (p - 2)) - 2))) /\
    (rel_prime b p /\ Zis_mod (a * b) 1 p) )).
cut
 (forall a,
  In a (progression Z.succ 2 (Z.abs_nat ((1 + (p - 2)) - 2))) ->
   ( 1 < a < p - 1 ) /\ rel_prime a p).
cut (ulist (progression Z.succ 2 (Z.abs_nat ((1 + (p - 2)) - 2)))).
elim (progression Z.succ 2 (Z.abs_nat ((1 + (p - 2)) - 2)))  using list_length_ind.
intros l1; case l1.
intros; simpl; auto.
apply Zmod_def_small; auto with zarith.
intros a1 l2 Rec H1 H2 H3.
assert (Ul2: ulist l2); (try apply ulist_inv with ( 1 := H1 )).
cut ( 1 < a1 < p - 1 ); auto with zarith.
intros [Hm1 Hm2].
case (H3 a1); auto with datatypes.
intros b1 [H4 [H5 H6]].
simpl in H4 |-; case H4; clear H4; intros H4.
subst b1.
case Zis_mod_square_1 with ( 2 := H6 ); auto with zarith; intros Hn1.
absurd (a1 = 1); auto with zarith.
rewrite <- (Zmod_def_small a1 p); auto with zarith.
rewrite <- (Zmod_def_small 1 p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
absurd (a1 = p - 1); auto with zarith.
rewrite <- (Zmod_def_small a1 p); auto with zarith.
rewrite <- (Zmod_def_small (p - 1) p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
case in_permutation_ex with ( 1 := H4 ); auto; intros l3 Hl3.
replace (iter 1 (fun (x : Z) => x) Zmult (cons a1 l2))
     with (iter 1 (fun (x : Z) => x) Zmult (cons a1 (cons b1 l3))).
simpl.
rewrite Zmult_assoc.
rewrite Zmod_mult; auto with zarith.
replace ((a1 * b1) mod p) with 1; auto with zarith.
rewrite Zmult_1_l.
rewrite Zmod_mod; auto with zarith.
apply Rec; auto with zarith datatypes.
simpl; rewrite <- permutation_length with ( 1 := Hl3 ); simpl; auto with arith.
apply ulist_inv with b1.
apply ulist_perm with ( 1 := permutation_sym _ _ _ Hl3 ); auto.
intros c Hc; apply H2.
right; apply permutation_in with ( 1 := Hl3 ); auto with datatypes.
intros c Hc; case (H3 c); auto with datatypes.
right; apply permutation_in with ( 1 := Hl3 ); auto with datatypes.
intros d [Hd1 [Hd2 Hd3]]; exists d; split; auto.
simpl in Hd1 |-; case Hd1; clear Hd1; intros Hd1.
subst d.
absurd (In b1 l3).
assert (Ubl: ulist (cons b1 l3)).
apply ulist_perm with ( 1 := permutation_sym _ _ _ Hl3 ); auto.
inversion Ubl; auto.
replace b1 with c; auto.
rewrite <- (Zmod_def_small c p); auto with zarith.
rewrite <- (Zmod_def_small b1 p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
apply Zis_mod_cancel with ( a := a1 ); auto.
apply Zis_mod_trans with 1; auto.
rewrite Zmult_comm; auto.
apply Zis_mod_sym; auto.
case (H2 b1); auto with zarith.
right; apply permutation_in with ( 1 := Hl3 ); auto with datatypes.
case (H2 c); auto with zarith.
right; apply permutation_in with ( 1 := Hl3 ); auto with datatypes.
cut (In d (cons b1 l3)); auto with datatypes.
simpl; intros [Hd4|Hd4]; auto.
subst d.
absurd (In a1 l2).
inversion H1; auto.
replace a1 with c; auto.
apply permutation_in with ( 1 := Hl3 ); auto with datatypes.
rewrite <- (Zmod_def_small c p); auto with zarith.
rewrite <- (Zmod_def_small a1 p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
apply Zis_mod_cancel with ( a := b1 ); auto.
apply Zis_mod_trans with 1; auto.
rewrite Zmult_comm; auto.
rewrite Zmult_comm; auto.
apply Zis_mod_sym; auto.
case (H2 c); auto with zarith.
right; apply permutation_in with ( 1 := Hl3 ); auto with datatypes.
apply permutation_in with ( 1 := permutation_sym _ _ _ Hl3 );
 auto with datatypes.
rewrite <- (Zmod_def_small 1 p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
apply Zis_mod_sym; auto.
apply iter_permutation; auto with zarith.
case (H2 a1); auto with zarith datatypes.
apply ulist_Zprogression.
intros a Ha; assert (Hb:  1 < a < p - 1 ).
split.
generalize (Zprogression_le_init _ _ _ Ha); auto with zarith.
generalize (Zprogression_le_end _ _ _ Ha); auto with zarith.
replace ((1 + (p - 2)) - 2) with (p - 3); auto with zarith.
split; auto.
apply rel_prime_le_prime; auto with zarith.
intros a Ha; assert (Hb:  1 < a < p - 1 ).
split.
generalize (Zprogression_le_init _ _ _ Ha); auto with zarith.
generalize (Zprogression_le_end _ _ _ Ha); auto with zarith.
replace ((1 + (p - 2)) - 2) with (p - 3); auto with zarith.
case (Zis_mod_rel_prime_inverse a p); auto with zarith.
apply rel_prime_le_prime; auto with zarith.
intros b [[Hb1 Hb2] [Hb3 Hb4]]; auto.
case Zle_lt_or_eq with ( 1 := Hb1 ); clear Hb1; intros Hb1.
case Zle_lt_or_eq with ( 1 := Hb2 ); clear Hb2; intros Hb2.
exists b; split; auto.
apply in_Zprogression; auto with zarith.
replace ((1 + (p - 2)) - 2) with (p - 3); auto with zarith.
subst b.
absurd (Z.modulo a p = p - 1).
rewrite Zmod_def_small; auto with zarith.
rewrite <- (Zmod_def_small (p - 1) p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
apply Zis_mod_cancel with ( a := p - 1 ); auto.
apply Zis_mod_trans with 1; auto.
rewrite Zmult_comm; auto.
replace ((p - 1) * (p - 1)) with (1 + (p - 2) * p); auto with zarith.
apply Zis_mod_def; auto with zarith.
apply sym_equal; apply Z_mod_plus; auto with zarith.
subst b.
rewrite Zmult_1_r in Hb4.
absurd (Z.modulo a p = 1).
rewrite Zmod_def_small; auto with zarith.
rewrite <- (Zmod_def_small 1 p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
subst p; simpl; auto.
subst p; apply Zis_mod_def; simpl; auto with zarith.
Qed.
Hint Unfold Zfact : core.
 
 
 

(*
   If n = 4  (p-1)! mod p = 2
   If n > 4 and p composite
         p = x (p/x)
           if x <> (p/x) then 
                        1 < x < p and 1 < p/x < p
                         so  
                        x and (p/x) appears in (p-1)!
                         so
                          p divides (p-1)!, (p-1)! mod p = 0
           if x = (p/x) then 
                        1 < x < p and 1 < 2x < p
                         so  
                        x and (2x) appears in (p-1)!
                         so
                         p divides 2x^2 so p divides (p-1)!, (p-1)! mod p = 0
 *)

Theorem wilson_converse:
 forall p, 1 < p -> Zis_mod (Zfact (p - 1)) (- 1) p ->  prime p.
intros p Hp H.
case (prime_dec p); auto; intros Hp1.
case (Zle_lt_or_eq 2 p); auto with zarith; clear Hp; intros Hp.
2:subst p; apply prime2.
case (Zle_lt_or_eq 3 p); auto with zarith; clear Hp; intros Hp.
2:subst p; apply prime3.
case (Zle_lt_or_eq 4 p); auto with zarith; clear Hp; intros Hp.
absurd (Zis_mod 0 (- 1) p).
intros Hf; case Hf; simpl.
intros q Hq; case (Zmult_1_inversion_l p q); auto with zarith.
apply Zis_mod_trans with (Zfact (p - 1)); auto.
apply Zis_mod_sym; auto.
case not_prime_divide with ( 2 := Hp1 ); auto with zarith.
intros x [[Hx1 Hx2] Hx3].
assert (H1: p = x * (p / x)).
apply Z_div_exact_2; auto with zarith.
apply Zdivide_mod; auto with zarith.
case (Z.eq_dec x (p / x)); intros Heq.
assert (Hl:  1 < 2 * x < p ).
split; auto with zarith.
case (Zle_lt_or_eq 2 x); auto with zarith; intros H2.
rewrite H1; rewrite <- Heq; auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
unfold Zfact, Zprod.
rewrite Zle_imp_le_bool; auto with zarith.
replace ((1 + (p - 1)) - 1) with (p - 1); auto with zarith.
generalize (ulist_Zprogression 1 (Z.abs_nat (p - 1))); intros Hu.
case (in_permutation_ex _ x (progression Z.succ 1 (Z.abs_nat (p - 1)))).
apply in_Zprogression; auto with zarith.
intros l1 Hl1.
case (in_permutation_ex _ (2 * x) l1).
cut (In (2 * x) (cons x l1)).
intros tmp; case tmp; auto with zarith.
intros Hv; absurd (1 * x < 2 * x); auto with zarith.
apply permutation_in with ( 1 := permutation_sym _ _ _ Hl1 ).
apply in_Zprogression; auto with zarith.
intros l2 Hl2.
rewrite iter_permutation with ( l2 := cons x (cons (2 * x) l2) );
 auto with zarith.
exists (2 * iter 1 (fun (x0 : Z) => x0) Zmult l2); rewrite H1; auto.
rewrite <- Heq.
(repeat rewrite (Zmult_comm 2)); simpl; ring.
apply permutation_sym; auto.
apply permutation_trans with (cons x l1); auto.
assert (Hl:  1 < p / x < p ).
assert (Hl1: 1 < p / x).
apply Zmult_lt_reg_r with x; auto with zarith.
split; auto with zarith.
pattern p at 2; rewrite H1; auto with zarith.
apply Z.le_lt_trans with (1 * (p / x)); auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
unfold Zfact, Zprod.
rewrite Zle_imp_le_bool; auto with zarith.
replace ((1 + (p - 1)) - 1) with (p - 1); auto with zarith.
generalize (ulist_Zprogression 1 (Z.abs_nat (p - 1))); intros Hu.
case (in_permutation_ex _ x (progression Z.succ 1 (Z.abs_nat (p - 1)))).
apply in_Zprogression; auto with zarith.
intros l1 Hl1.
case (in_permutation_ex _ (p / x) l1).
cut (In (p / x) (cons x l1)).
intros tmp; case tmp; auto with zarith.
intros tmp1; case Heq; auto.
apply permutation_in with ( 1 := permutation_sym _ _ _ Hl1 ).
apply in_Zprogression; auto with zarith.
intros l2 Hl2.
rewrite iter_permutation with ( l2 := cons x (cons (p / x) l2) );
 auto with zarith.
exists (iter 1 (fun (x0 : Z) => x0) Zmult l2); simpl; auto.
pattern p at 2; rewrite H1; ring.
apply permutation_sym; auto.
apply permutation_trans with (cons x l1); auto.
subst p; cut (Z.modulo (Zfact (4 - 1)) 4 = Z.modulo (- 1) 4).
unfold Zfact, Zprod, Z.modulo; simpl; intros; discriminate.
apply Zis_mod_def_inv; auto with zarith.
Qed.
