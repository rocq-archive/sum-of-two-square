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


(**********************************************************************
    Aux.v                                
                                                                     
    Auxillary functions & Theorems                                   
                                                                     
                                                                     
                                    Laurent.Thery@inria.fr (2003)    
  **********************************************************************)
Require Export List.
Require Export Arith.
Require Export ZArith.
Require Export ZArithRing.
Require Export Znumtheory.
Require Export Tactic.
Require Import Inverse_Image.
Require Import Wf_nat.

(* 
   Some properties on list operators: app, map,...
   *)

Open Scope nat_scope.
 
Section List.

Variables (A : Set) (B : Set) (C : Set).
Variable f : A ->  B.
(* An induction theorem for list based on length 
   *)
 
Theorem list_length_ind:
 forall (P : list A ->  Prop),
 (forall (l1 : list A),
  (forall (l2 : list A), length l2 < length l1 ->  P l2) ->  P l1) ->
 forall (l : list A),  P l.
intros P H l;
 apply well_founded_ind with ( R := fun (x y : list A) => (length x < length y)%nat );
 auto.
apply wf_inverse_image with ( R := lt ); auto.
apply lt_wf.
Qed.
 
Definition list_length_induction:
 forall (P : list A ->  Set),
 (forall (l1 : list A),
  (forall (l2 : list A), length l2 < length l1 ->  P l2) ->  P l1) ->
 forall (l : list A),  P l.
intros P H l;
 apply well_founded_induction
      with ( R := fun (x y : list A) => length x < length y ); auto.
apply wf_inverse_image with ( R := lt ); auto.
apply lt_wf.
Qed.
 
Theorem in_ex_app:
 forall (a : A) (l : list A),
 In a l ->  (exists l1 : list A , exists l2 : list A , l = l1 ++ (a :: l2)  ).
intros a l; elim l; clear l; simpl; auto.
intros H; case H.
intros a1 l H [H1|H1]; auto.
exists (nil (A:=A)); exists l; simpl; auto.
apply f_equal2 with ( f := cons (A:=A) ); auto.
case H; auto; intros l1 [l2 Hl2]; exists (a1 :: l1); exists l2; simpl; auto.
apply f_equal2 with ( f := cons (A:=A) ); auto.
Qed.
(* Properties on app 
   *)
 
Theorem length_app:
 forall (l1 l2 : list A),  length (l1 ++ l2) = length l1 + length l2.
intros l1; elim l1; simpl; auto.
Qed.
 
Theorem app_inv_head:
 forall (l1 l2 l3 : list A), l1 ++ l2 = l1 ++ l3 ->  l2 = l3.
intros l1; elim l1; simpl; auto.
intros a l H l2 l3 H0; apply H; injection H0; auto.
Qed.
 
Theorem app_inv_tail:
 forall (l1 l2 l3 : list A), l2 ++ l1 = l3 ++ l1 ->  l2 = l3.
intros l1 l2; generalize l1; elim l2; clear l1 l2; simpl; auto.
intros l1 l3; case l3; auto.
intros b l H; absurd (length ((b :: l) ++ l1) <= length l1).
simpl; rewrite length_app; auto with arith.
rewrite <- H; auto with arith.
intros a l H l1 l3; case l3.
simpl; intros H1; absurd (length (a :: (l ++ l1)) <= length l1).
simpl; rewrite length_app; auto with arith.
rewrite H1; auto with arith.
simpl; intros b l0 H0; injection H0.
intros H1 H2; apply f_equal2 with ( f := cons (A:=A) ); auto.
apply H with ( 1 := H1 ); auto.
Qed.
 
Theorem app_inv_app:
 forall l1 l2 l3 l4 a,
 l1 ++ l2 = l3 ++ (a :: l4) ->
  (exists l5 : list A , l1 = l3 ++ (a :: l5) ) \/
  (exists l5 , l2 = l5 ++ (a :: l4) ).
intros l1; elim l1; simpl; auto.
intros l2 l3 l4 a H; right; exists l3; auto.
intros a l H l2 l3 l4 a0; case l3; simpl.
intros H0; left; exists l; apply f_equal2 with ( f := cons (A:=A) );
 injection H0; auto.
intros b l0 H0; case (H l2 l0 l4 a0); auto.
injection H0; auto.
intros [l5 H1].
left; exists l5; apply f_equal2 with ( f := cons (A:=A) ); injection H0; auto.
Qed.
 
Theorem app_inv_app2:
 forall l1 l2 l3 l4 a b,
 l1 ++ l2 = l3 ++ (a :: (b :: l4)) ->
  (exists l5 : list A , l1 = l3 ++ (a :: (b :: l5)) ) \/
  ((exists l5 , l2 = l5 ++ (a :: (b :: l4)) ) \/
   l1 = l3 ++ (a :: nil) /\ l2 = b :: l4).
intros l1; elim l1; simpl; auto.
intros l2 l3 l4 a b H; right; left; exists l3; auto.
intros a l H l2 l3 l4 a0 b; case l3; simpl.
case l; simpl.
intros H0; right; right; injection H0; split; auto.
apply f_equal2 with ( f := cons (A:=A) ); auto.
intros b0 l0 H0; left; exists l0; injection H0; intros;
 (repeat apply f_equal2 with ( f := cons (A:=A) )); auto.
intros b0 l0 H0; case (H l2 l0 l4 a0 b); auto.
injection H0; auto.
intros [l5 HH1]; left; exists l5; apply f_equal2 with ( f := cons (A:=A) );
 auto; injection H0; auto.
intros [H1|[H1 H2]]; auto.
right; right; split; auto; apply f_equal2 with ( f := cons (A:=A) ); auto;
 injection H0; auto.
Qed.
 
Theorem same_length_ex:
 forall (a : A) l1 l2 l3,
 length (l1 ++ (a :: l2)) = length l3 ->
  (exists l4 ,
   exists l5 ,
   exists b : B ,
   length l1 = length l4 /\ (length l2 = length l5 /\ l3 = l4 ++ (b :: l5))   ).
intros a l1; elim l1; simpl; auto.
intros l2 l3; case l3; simpl; (try (intros; discriminate)).
intros b l H; exists (nil (A:=B)); exists l; exists b; (repeat (split; auto)).
intros a0 l H l2 l3; case l3; simpl; (try (intros; discriminate)).
intros b l0 H0.
case (H l2 l0); auto.
intros l4 [l5 [b1 [HH1 [HH2 HH3]]]].
exists (b :: l4); exists l5; exists b1; (repeat (simpl; split; auto)).
apply f_equal2 with ( f := cons (A:=B) ); auto.
Qed.
(* 
  Properties on map 
   *)
 
Theorem in_map_inv:
 forall (b : B) (l : list A),
 In b (map f l) ->  (exists a : A , In a l /\ b = f a ).
intros b l; elim l; simpl; auto.
intros tmp; case tmp.
intros a0 l0 H [H1|H1]; auto.
exists a0; auto.
case (H H1); intros a1 [H2 H3]; exists a1; auto.
Qed.
 
Theorem in_map_fst_inv:
 forall a (l : list (B * C)),
 In a (map (fst (B:=_)) l) ->  (exists c , In (a, c) l ).
intros a l; elim l; simpl; auto.
intros H; case H.
intros a0 l0 H [H0|H0]; auto.
exists (snd a0); left; rewrite <- H0; case a0; simpl; auto.
case H; auto; intros l1 Hl1; exists l1; auto.
Qed.
 
Theorem length_map: forall l,  length (map f l) = length l.
intros l; elim l; simpl; auto.
Qed.
 
Theorem map_app: forall l1 l2,  map f (l1 ++ l2) = map f l1 ++ map f l2.
intros l; elim l; simpl; auto.
intros a l0 H l2; apply f_equal2 with ( f := cons (A:=B) ); auto.
Qed.
 
Theorem map_length_decompose:
 forall l1 l2 l3 l4,
 length l1 = length l2 ->
 map f (app l1 l3) = app l2 l4 ->  map f l1 = l2 /\ map f l3 = l4.
intros l1; elim l1; simpl; auto; clear l1.
intros l2; case l2; simpl; auto.
intros; discriminate.
intros a l1 Rec l2; case l2; simpl; clear l2; auto.
intros; discriminate.
intros b l2 l3 l4 H1 H2.
injection H2; clear H2; intros H2 H3.
case (Rec l2 l3 l4); auto.
intros H4 H5; split; auto.
apply f_equal2 with ( f := @cons B ); auto.
Qed.
(* 
  Properties of flat_map 
   *)
 
Theorem in_flat_map:
 forall (l : list B) (f : B ->  list C) a b,
 In a (f b) -> In b l ->  In a (flat_map f l).
intros l g; elim l; simpl; auto.
intros a l0 H a0 b H0 [H1|H1]; apply in_or_app; auto.
left; rewrite H1; auto.
right; apply H with ( b := b ); auto.
Qed.
 
Theorem in_flat_map_ex:
 forall (l : list B) (f : B ->  list C) a,
 In a (flat_map f l) ->  (exists b , In b l /\ In a (f b) ).
intros l g; elim l; simpl; auto.
intros a H; case H.
intros a l0 H a0 H0; case in_app_or with ( 1 := H0 ); simpl; auto.
intros H1; exists a; auto.
intros H1; case H with ( 1 := H1 ).
intros b [H2 H3]; exists b; simpl; auto.
Qed.
 
End List.
(* Propertie of list_prod
   *)
 
Theorem length_list_prod:
 forall (A : Set) (l1 l2 : list A),
  length (list_prod l1 l2) = length l1 * length l2.
intros A l1 l2; elim l1; simpl; auto.
intros a l H; rewrite length_app; rewrite length_map; rewrite H; auto.
Qed.
 
Theorem in_list_prod_inv:
 forall (A B : Set) a l1 l2,
 In a (list_prod l1 l2) ->
  (exists b : A , exists c : B , a = (b, c) /\ (In b l1 /\ In c l2)  ).
intros A B a l1 l2; elim l1; simpl; auto; clear l1.
intros H; case H.
intros a1 l1 H1 H2.
case in_app_or with ( 1 := H2 ); intros H3; auto.
case in_map_inv with ( 1 := H3 ); intros b1 [Hb1 Hb2]; auto.
exists a1; exists b1; split; auto.
case H1; auto; intros b1 [c1 [Hb1 [Hb2 Hb3]]].
exists b1; exists c1; split; auto.
Qed.
(* 
   Properties of Z_nat
   *)
 
Theorem inj_eq_inv: forall (n m : nat), Z_of_nat n = Z_of_nat m ->  n = m.
apply Nat2Z.inj_iff.
Qed.
 
Theorem inj_le_inv: forall (n m : nat), (Z_of_nat n <= Z_of_nat m)%Z ->  le n m.
intros n m H1; case (Nat.le_gt_cases n m); auto with arith.
intros H2; contradict H1; auto with zarith.
Qed.
 
Theorem Z_of_nat_Zabs_nat:
 forall (z : Z), (0 <= z)%Z ->  Z_of_nat (Z.abs_nat z) = z.
intros z; case z; simpl; auto with zarith.
Qed.

(* Properties of Zdivide
   *)
 
Theorem Zdivide_trans: forall a b c, Z.divide a b -> Z.divide b c ->  Z.divide a c.
intros a b c [d H1] [e H2]; exists (d * e)%Z; auto with zarith.
Qed.

Theorem Zdivide_Zabs_l: forall a b, Z.divide (Z.abs a) b ->  Z.divide a b.
intros a b [x H]; subst b.
pattern (Z.abs a); apply Zabs_intro.
exists (- x)%Z; ring.
exists x; ring.
Qed.
 
Theorem Zdivide_Zabs_inv_l: forall a b, Z.divide a b ->  Z.divide (Z.abs a) b.
intros a b [x H]; subst b.
pattern (Z.abs a); apply Zabs_intro.
exists (- x)%Z; ring.
exists x; ring.
Qed.

Theorem Zdivide_le: forall a b, (0 <= a)%Z -> (0 < b)%Z -> Z.divide a b ->  (a <= b)%Z.
intros a b H1 H2 [q H3]; subst b.
case (Zle_lt_or_eq 0 a); auto with zarith; intros H3.
case (Zle_lt_or_eq 0 q); auto with zarith.
intros H4; apply Z.le_trans with (1 * a)%Z; auto with zarith.
Qed.

Theorem Zdivide_Zdiv_eq: forall a b, (0 < a)%Z -> Z.divide a b ->  b = (a * (b / a))%Z.
intros a b Hb Hc.
pattern b at 1; rewrite (Z_div_mod_eq_full b a); auto with zarith.
rewrite (Zdivide_mod b a); auto with zarith.
Qed.
 
Theorem Zdivide_Zdiv_lt_pos:
 forall a b, (1 < a)%Z -> (0 < b)%Z -> Z.divide a b ->  ( 0 < Z.div b a < b )%Z.
intros a b H1 H2 H3; split.
apply Zmult_lt_reg_r with a; auto with zarith.
rewrite (Zmult_comm (Z.div b a)); rewrite <- Zdivide_Zdiv_eq; auto with zarith.
apply Zmult_lt_reg_r with a; auto with zarith.
(repeat rewrite (fun x => Zmult_comm x a)); auto with zarith.
rewrite <- Zdivide_Zdiv_eq; auto with zarith.
pattern b at 1; replace b with (1 * b)%Z; auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
Qed.


(* Properties of Zis_gcd 
   *)
 
Theorem Zis_gcd_unique:
 forall (a b c d : Z), Zis_gcd a b c -> Zis_gcd b a d ->  c = d \/ c = (- d)%Z.
intros a b c d H1 H2.
inversion_clear H1 as [Hc1 Hc2 Hc3].
inversion_clear H2 as [Hd1 Hd2 Hd3].
assert (H3: Z.divide c d); auto.
assert (H4: Z.divide d c); auto.
apply Z.divide_antisym; auto.
Qed.
(* Properties rel_prime
   *)
 
Theorem rel_prime_sym: forall a b, rel_prime a b ->  rel_prime b a.
intros a b H; auto with zarith.
red; apply Zis_gcd_sym; auto with zarith.
Qed.
 
Theorem rel_prime_le_prime:
 forall a p, prime p -> ( 1 < a < p )%Z ->  rel_prime a p.
intros a p Hp [H1 H2].
apply rel_prime_sym; apply prime_rel_prime; auto.
intros [q Hq]; subst a.
case (Zle_or_lt q 0); intros Hl.
absurd (q * p <= 0 * p)%Z; auto with zarith.
absurd (1 * p <= q * p)%Z; auto with zarith.
Qed.
 
Definition rel_prime_dec:
 forall a b,  ({ rel_prime a b }) + ({ ~ rel_prime a b }).
intros a b; case (Z.eq_dec (Z.gcd a b) 1); intros H1.
left; red.
rewrite <- H1; apply Zgcd_is_gcd.
right; contradict H1.
case (Zis_gcd_unique a b (Z.gcd a b) 1); auto.
apply Zgcd_is_gcd.
apply Zis_gcd_sym; auto.
intros H2; absurd (0 <= Z.gcd a b)%Z; auto with zarith.
generalize (Zgcd_is_pos a b); auto with zarith.
Qed.

(* 
  Properties of Zabs
   *)
 
Theorem Zabs_square: forall a,  (a * a)%Z = (Z.abs a * Z.abs a)%Z.
intros a; rewrite <- Zabs_Zmult; apply sym_equal; apply Z.abs_eq;
 auto with zarith.
case (Zle_or_lt 0%Z a); auto with zarith.
Qed.

(* 
  Properties of Zabs_nat
   *)
 
Theorem Z_of_nat_abs_le:
 forall x y, (x <= y)%Z ->  (x + Z_of_nat (Z.abs_nat (y - x)))%Z = y.
intros x y Hx1.
rewrite Z_of_nat_Zabs_nat; auto with zarith.
Qed.

Theorem Zabs_nat_Zsucc:
 forall p, (0 <= p)%Z ->  Z.abs_nat (Z.succ p) = S (Z.abs_nat p).
intros p Hp.
apply inj_eq_inv.
rewrite inj_S; (repeat rewrite Z_of_nat_Zabs_nat); auto with zarith.
Qed.
 

(* 
  Properties Zsqrt
   *)

Theorem Zsqrt_is_pos: forall n, (0 <= n)%Z ->  (0 <= Z.sqrt n)%Z.
Proof.
intros. apply Z.sqrt_nonneg.
Qed.

Theorem Zsqrt_square_id: forall a, (0 <= a)%Z ->  Z.sqrt (a * a)%Z = a.
Proof.
apply Z.sqrt_square.
Qed.
 
Theorem Zsqrt_le:
 forall p q, ( 0 <= p <= q )%Z ->  (Z.sqrt p <= Z.sqrt q)%Z.
Proof.
intros p q (_,H). now apply Z.sqrt_le_mono.
Qed.

(* 
  Properties Z.modulo 
   *)
 
Theorem Zmod_mult:
 forall a b n, (0 < n)%Z ->  Z.modulo (a * b) n = Z.modulo (Z.modulo  a n * Z.modulo  b n) n.
intros a b n H.
pattern a at 1; rewrite (Z_div_mod_eq_full a n); auto with zarith.
pattern b at 1; rewrite (Z_div_mod_eq_full b n); auto with zarith.
replace ((n * (a / n) + a mod n) * (n * (b / n) + b mod n))%Z
     with
      ((a mod n) * (b mod n) +
       (((n * (a / n)) * (b / n) + (b mod n) * (a / n)) + (a mod n) * (b / n)) *
       n)%Z; auto with zarith.
apply Z_mod_plus; auto with zarith.
Qed.

Theorem Zmod_plus_eq:
 forall a b n, (0 < n)%Z ->  Z.modulo (a + b)%Z n = Z.modulo (Z.modulo a n + Z.modulo b n)%Z n.
intros a b n H.
pattern a at 1; rewrite (Z_div_mod_eq_full a n); auto with zarith.
pattern b at 1; rewrite (Z_div_mod_eq_full b n); auto with zarith.
replace ((n * (a / n) + a mod n) + (n * (b / n) + b mod n))%Z
     with ((a mod n + b mod n) + (a / n + b / n) * n)%Z; auto with zarith.
apply Z_mod_plus; auto with zarith.
Qed.

 
Theorem Zmod_mod: forall a n, (0 < n)%Z ->  Z.modulo (Z.modulo a n) n = Z.modulo a n.
intros a n H.
pattern a at 2; rewrite (Z_div_mod_eq_full a n); auto with zarith.
rewrite Zplus_comm; rewrite Zmult_comm.
apply sym_equal; apply Z_mod_plus; auto with zarith.
Qed.
 
Theorem Zmod_def_small: forall a n, ( 0 <= a < n )%Z ->  Z.modulo a n = a.
intros a n [H1 H2]; unfold Z.modulo.
generalize (Z_div_mod a n); case (Z.div_eucl a n).
intros q r H3; case H3; clear H3; auto with zarith.
intros H4 [H5 H6].
case (Zle_or_lt q (- 1)); intros H7.
contradict H1; apply Zlt_not_le.
subst a.
apply Z.le_lt_trans with (n * - 1 + r)%Z; auto with zarith.
case (Zle_lt_or_eq 0 q); auto with zarith; intros H8.
contradict H2; apply Zle_not_lt.
apply Z.le_trans with (n * 1 + r)%Z; auto with zarith.
rewrite H4; auto with zarith.
Qed.

(* Properties
	Zpower
 *)
Theorem Zpower_1: forall a, (0 <= a)%Z ->  Zpower 1%Z a = 1%Z.
intros a Ha; pattern a; apply natlike_ind; auto with zarith.
intros x Hx Hx1; unfold Z.succ.
rewrite Zpower_exp; auto with zarith.
Qed.
 
Theorem Zpower_exp_0: forall a,  Zpower a 0%Z = 1%Z.
simpl; unfold Zpower_pos; simpl; auto with zarith.
Qed.
 
Theorem Zpower_exp_1: forall a,  Zpower a 1%Z = a%Z.
simpl; unfold Zpower_pos; simpl; auto with zarith.
Qed.

Theorem Zpower_Zabs: forall a b,  Z.abs (Zpower a b) = Zpower (Z.abs a) b.
intros a b; case (Zle_or_lt 0%Z b).
intros Hb; pattern b; apply natlike_ind; auto with zarith.
intros x Hx Hx1; unfold Z.succ.
(repeat rewrite Zpower_exp); auto with zarith.
case b; simpl; auto with zarith.
Qed.

(* 
  Properties prime 
   *)
 
Theorem not_prime_0: ~ prime 0.
intros H1; case (prime_divisors _ H1 2); auto with zarith.
Qed.

 
Theorem not_prime_1: ~ prime 1.
intros H1; absurd (1 < 1)%Z; auto with zarith.
inversion H1; auto.
Qed.
 
Theorem prime2: prime 2.
apply prime_intro; auto with zarith.
intros n [H1 H2]; case Zle_lt_or_eq with ( 1 := H1 ); auto with zarith;
 clear H1; intros H1.
contradict H2; auto with zarith.
subst n; red; auto with zarith.
apply Zis_gcd_intro; auto with zarith.
Qed.
 
Theorem prime3: prime 3.
apply prime_intro; auto with zarith.
intros n [H1 H2]; case Zle_lt_or_eq with ( 1 := H1 ); auto with zarith;
 clear H1; intros H1.
case (Zle_lt_or_eq 2 n); auto with zarith; clear H1; intros H1.
contradict H2; auto with zarith.
subst n; red; auto with zarith.
apply Zis_gcd_intro; auto with zarith.
intros x [q1 Hq1] [q2 Hq2].
exists (q2 - q1)%Z.
apply trans_equal with (3 - 2)%Z; auto with zarith.
subst n; red; auto with zarith.
apply Zis_gcd_intro; auto with zarith.
Qed.
 
Theorem prime_le_2: forall p, prime p ->  (2 <= p)%Z.
intros p Hp; inversion Hp; auto with zarith.
Qed.
 
Definition prime_dec_aux:
 forall p m,
  ({ forall n, ( 1 < n < m )%Z ->  rel_prime n p }) +
  ({ exists n , ( 1 < n < m )%Z /\ ~ rel_prime n p  }).
intros p m.
case (Z_lt_dec 1 m); intros H1.
apply natlike_rec
     with
      ( P :=
      fun m =>
      ({ forall (n : Z), ( 1 < n < m )%Z ->  rel_prime n p }) +
      ({ exists n : Z , ( 1 < n < m )%Z /\ ~ rel_prime n p  }) );
 auto with zarith.
left; intros n [HH1 HH2]; contradict HH2; auto with zarith.
intros x Hx Rec; case Rec.
intros P1; case (rel_prime_dec x p); intros P2.
left; intros n [HH1 HH2].
case (Zgt_succ_gt_or_eq x n); auto with zarith.
intros HH3; subst x; auto.
case (Z_lt_dec 1 x); intros HH1.
right; exists x; split; auto with zarith.
left; intros n [HHH1 HHH2]; contradict HHH1; auto with zarith.
intros tmp; right; case tmp; intros n [HH1 HH2]; exists n; auto with zarith.
left; intros n [HH1 HH2]; contradict H1; auto with zarith.
Defined.
 
Theorem not_prime_divide:
 forall p,
 (1 < p)%Z -> ~ prime p ->  (exists n , ( 1 < n < p )%Z /\ Z.divide n p ).
intros p Hp Hp1.
case (prime_dec_aux p p); intros H1.
case Hp1; apply prime_intro; auto.
intros n [Hn1 Hn2].
case Zle_lt_or_eq with ( 1 := Hn1 ); auto with zarith.
intros H2; subst n; red; apply Zis_gcd_intro; auto with zarith.
case H1; intros n [Hn1 Hn2].
generalize (Zgcd_is_pos n p); intros Hpos.
case (Zle_lt_or_eq 0 (Z.gcd n p)); auto with zarith; intros H3.
case (Zle_lt_or_eq 1 (Z.gcd n p)); auto with zarith; intros H4.
exists (Z.gcd n p); split; auto.
split; auto.
apply Z.le_lt_trans with n; auto with zarith.
generalize (Zgcd_is_gcd n p); intros tmp; inversion_clear tmp as [Hr1 Hr2 Hr3].
apply Zdivide_le; auto with zarith.
apply Z.gcd_divide_r.
case Hn2; red.
rewrite H4; apply Zgcd_is_gcd.
generalize (Zgcd_is_gcd n p); rewrite <- H3; intros tmp;
 inversion_clear tmp as [Hr1 Hr2 Hr3].
absurd (n = 0)%Z; auto with zarith.
case Hr1; auto with zarith.
Defined.
 
Definition prime_dec: forall p,  ({ prime p }) + ({ ~ prime p }).
intros p; case (Z_lt_dec 1 p); intros H1.
case (prime_dec_aux p p); intros H2.
left; apply prime_intro; auto.
intros n [Hn1 Hn2]; case Zle_lt_or_eq with ( 1 := Hn1 ); auto.
intros HH; subst n.
red; apply Zis_gcd_intro; auto with zarith.
right; intros H3; inversion_clear H3 as [Hp1 Hp2].
case H2; intros n [Hn1 Hn2]; case Hn2; auto with zarith.
right; intros H3; inversion_clear H3 as [Hp1 Hp2]; case H1; auto.
Defined.

 
Theorem prime_def:
 forall p, (1 < p)%Z -> (forall n, ( 1 < n < p )%Z ->  ~ Z.divide n p) ->  prime p.
intros p H1 H2.
apply prime_intro; auto.
intros n H3.
red; apply Zis_gcd_intro; auto with zarith.
intros x H4 H5.
case (Zle_lt_or_eq 0 (Z.abs x)); auto with zarith; intros H6.
case (Zle_lt_or_eq 1 (Z.abs x)); auto with zarith; intros H7.
case (Zle_lt_or_eq (Z.abs x) p); auto with zarith.
apply Zdivide_le; auto with zarith.
apply Zdivide_Zabs_inv_l; auto.
intros H8; case (H2 (Z.abs x)); auto.
apply Zdivide_Zabs_inv_l; auto.
intros H8; subst p; absurd (Z.abs x <= n)%Z; auto with zarith.
apply Zdivide_le; auto with zarith.
apply Zdivide_Zabs_inv_l; auto.
rewrite H7; pattern (Z.abs x); apply Zabs_intro; auto with zarith.
absurd (0%Z = p); auto with zarith.
cut (Z.divide (Z.abs x) p).
intros [q Hq]; subst p; rewrite <- H6; auto with zarith.
apply Zdivide_Zabs_inv_l; auto.
Qed.
 
Theorem prime_inv_def: forall p n, prime p -> ( 1 < n < p )%Z ->  ~ Z.divide n p.
intros p n H1 H2 H3.
absurd (rel_prime n p); auto.
unfold rel_prime; intros H4.
case (Zis_gcd_unique n p n 1); auto with zarith.
apply Zis_gcd_intro; auto with zarith.
inversion H1; auto with zarith.
Qed.
 
Theorem square_not_prime: forall a,  ~ prime (a * a).
intros a; rewrite (Zabs_square a).
case (Zle_lt_or_eq 0 (Z.abs a)); auto with zarith; intros Hza1.
case (Zle_lt_or_eq 1 (Z.abs a)); auto with zarith; intros Hza2.
intros Ha; case (prime_inv_def (Z.abs a * Z.abs a)%Z (Z.abs a)); auto.
split; auto.
pattern (Z.abs a) at 1; replace (Z.abs a) with (1 * Z.abs a)%Z; auto with zarith.
apply Zmult_lt_compat_r; auto with zarith.
exists (Z.abs a); auto.
rewrite <- Hza2; simpl; apply not_prime_1.
rewrite <- Hza1; simpl; apply not_prime_0.
Qed.


Theorem prime_divide_prime_eq:
 forall p1 p2, prime p1 -> prime p2 -> Z.divide p1 p2 ->  p1 = p2.
intros p1 p2 Hp1 Hp2 Hp3.
assert (Ha: (1 < p1)%Z).
inversion Hp1; auto.
assert (Ha1: (1 < p2)%Z).
inversion Hp2; auto.
case (Zle_lt_or_eq p1 p2); auto with zarith.
apply Zdivide_le; auto with zarith.
intros Hp4.
case (prime_inv_def p2 p1); auto with zarith.
Qed.
