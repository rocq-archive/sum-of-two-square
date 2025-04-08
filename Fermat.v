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

   Proof of Fermat little theorem

   The proof is as follows:
    we considere the product
     prod_{i=1}^{p-1} (a * i)
     on one side we have
       prod_{i=1}^{p-1} (a * i) 
         = prod_{i=1}^{p-1} a * prod_{i=1}^{p-1} i
         = a^(p-1) * (p - 1)!
     on the other side we have
       prod_{i=1}^{p-1} (a * i) mod p 
         = prod_{i=1}^{p-1} ((a * i) mod p) mod p
       but we have that a is relatively prime,
          so by the cancelation rule we have
              (a * i) mod p = (a * j) mod p implies that i = j
          this means that the (a * i) mod p are p-1 distinct elements
          between 1 and p-1, so they can be put in a one-to-one correspondance
          with 1..p-1
       prod_{i=1}^{p-1} ((a * i) mod p) mod p 
          = prod_{i=1}^{p-1} (i) mod p 
          = (p-1)! mod p

     using both sides we have that
         (a^(p-1) * (p - 1)!) mod p = (p-1)! mod p
     using once again the cancellation rule sine ((p-1)! is relatively
     prime to p (as a product of number relatively primes to p))
         a^(p-1)  mod p = 1

*)
Require Export ZisMod.
 
Theorem fermat_little:
 forall a p, prime p -> rel_prime a p ->  Zis_mod (Zpower a (p - 1)) 1 p.
intros a p H1 H2.
assert (Hp: 1 < p).
apply Z.lt_le_trans with 2; auto with zarith.
apply prime_le_2; auto.
assert (Hp1: 0 <= p - 1); auto with zarith.
apply Zis_mod_cancel with (Zfact (p - 1)).
apply rel_prime_sym; unfold Zfact.
apply inv_Zprod; auto with zarith.
apply prime_rel_prime; auto.
intros [x H3].
absurd (prime p); auto.
replace p with 1; auto.
apply not_prime_1.
apply sym_equal; apply (Zmult_one p x); auto with zarith.
intros; apply rel_prime_mult; auto with zarith.
intros x [H3 H4]; apply prime_rel_prime; auto with zarith.
intros [y H5].
assert (H6: 0 < p).
apply Z.lt_trans with 1; auto with zarith.
generalize H3 H4; rewrite H5; clear H3 H4; intros H3 H4.
case (Zle_or_lt y 0); intros H7.
contradict H3; apply Zlt_not_le.
apply Z.le_lt_trans with (0 * p); auto with zarith.
contradict H4; apply Zlt_not_le.
apply Z.lt_le_trans with (1 * p); auto with zarith.
rewrite Zmult_1_r; auto with zarith.
pattern (p - 1) at 2; replace (p - 1) with ((1 + (p - 1)) - 1); auto with zarith.
rewrite <- Zprod_c; auto with zarith.
unfold Zfact; rewrite Zprod_mult.
apply Zis_mod_trans with (Z.modulo (Zprod 1 (p - 1) (fun (i : Z) => i * a)) p).
apply Zis_mod_mod; auto with zarith.
replace (Zprod 1 (p - 1) (fun (i : Z) => i * a) mod p)
     with (Zprod 1 (p - 1) (fun (i : Z) => (i * a) mod p) mod p).
apply Zis_mod_trans with (Zprod 1 (p - 1) (fun (i : Z) => (i * a) mod p)).
apply Zis_mod_sym; apply Zis_mod_mod; auto with zarith.
replace (Zprod 1 (p - 1) (fun (i : Z) => (i * a) mod p))
     with (Zprod 1 (p - 1) (fun (x : Z) => x)).
apply Zis_mod_ref.
unfold Zprod; rewrite Zle_imp_le_bool; auto with zarith.
replace ((1 + (p - 1)) - 1) with (p - 1); auto with zarith.
rewrite <- (iter_map
             _ _ _ 1 (fun (x : Z) => x) Zmult (fun (i : Z) => (i * a) mod p)).
apply iter_permutation; auto with zarith.
apply permutation_sym; apply ulist_eq_permutation; auto with zarith.
cut (ulist (progression Z.succ 1 (Z.abs_nat (p - 1)))).
generalize (Zprogression_le_init 1 (Z.abs_nat (p - 1))).
generalize (Zprogression_le_end 1 (Z.abs_nat (p - 1))).
replace (1 + Z_of_nat (Z.abs_nat (p - 1))) with p; auto with zarith.
elim (progression Z.succ 1 (Z.abs_nat (p - 1))); auto.
intros a0 l H H0 H3 H4; simpl; apply ulist_cons; auto.
intros Hi1; case (in_map_inv _ _ _ _ _ Hi1).
intros x [Ha1 Ha2].
absurd (In a0 l); auto with zarith.
inversion H4; auto.
replace a0 with x; auto.
rewrite <- (Zmod_def_small x p); auto with zarith.
rewrite <- (Zmod_def_small a0 p); auto with zarith.
apply Zis_mod_def_inv; auto with zarith.
apply Zis_mod_cancel with a; auto with zarith.
(repeat rewrite (Zmult_comm a)); apply Zis_mod_def; auto with zarith.
split; auto with datatypes zarith.
apply Z.le_trans with 1; auto with datatypes zarith.
split; auto with datatypes zarith.
apply Z.le_trans with 1; auto with datatypes zarith.
apply H; auto with datatypes zarith.
apply ulist_inv with ( 1 := H4 ).
apply ulist_Zprogression.
intros b Hb.
apply in_Zprogression; auto with zarith.
case (in_map_inv _ _ _ _ _ Hb); intros c [Hc1 Hc2].
subst b.
assert (Hd : 1 + Z_of_nat (Z.abs_nat (p - 1)) = p).
rewrite Z_of_nat_Zabs_nat; auto with zarith.
rewrite Hd.
case (Z_mod_lt (c * a) p); auto with zarith; intros Hm1 Hm2; split;
 auto with zarith.
case (Zle_lt_or_eq _ _ Hm1); auto with zarith.
intros Hm3.
assert (Hm4: Z.divide p (c * a)); auto with zarith.
apply Zmod_divide; auto with zarith.
case (prime_mult _ H1 _ _ Hm4).
intros [d Hd1]; case (Zle_or_lt d 0); intros Hm5.
absurd (1 <= c); auto with zarith.
apply Zprogression_le_init with ( 1 := Hc1 ).
absurd (c < 1 * p).
apply Zle_not_lt; subst c; auto with zarith.
rewrite <- Hd.
rewrite Zmult_1_l.
apply Zprogression_le_end with ( 1 := Hc1 ).
intros Hm5; case (Zdivide_1 p); auto with zarith.
apply Gauss with ( b := a ); auto with zarith.
apply rel_prime_sym; auto with zarith.
apply length_map.
unfold Zprod; rewrite Zle_imp_le_bool; auto with zarith.
elim (progression Z.succ 1 (Z.abs_nat ((1 + (p - 1)) - 1))); simpl;
 auto with zarith.
intros a0 l H.
rewrite (Zmod_mult ((a0 * a) mod p)); auto with zarith.
rewrite H.
rewrite Zmod_mod; auto with zarith.
rewrite <- Zmod_mult; auto with zarith.
Qed.
