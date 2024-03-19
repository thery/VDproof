(* Formalisation of the Veltkamp/Dekker Algorithms with Directed Roundings *)

(* Copyright (c)  Inria. All rights reserved. *)
Require Import Reals  Psatz.
From Flocq Require Import Core Plus_error Mult_error Relative Sterbenz Operations.
From Flocq Require Import  Round.
From mathcomp Require Import all_ssreflect.
Require Import Rmore.

Set Implicit Arguments.

Inductive dwR := DWR (xh : R) (xl : R).

Definition opp_DWR (d : dwR) := 
 let: DWR xh xl := d in DWR (- xh) (- xl).

Lemma opp_DWR_K d : opp_DWR (opp_DWR d) = d.
Proof. by case: d => xh xl; congr DWR; lra. Qed.
Definition scale_DWR (s : R) (d : dwR) := 
 let: DWR xh xl := d in DWR (s * xh) (s * xl).

Open Scope R_scope.

Section split.

Definition  beta:= radix2.
Variable p : Z.
Variable fexp : Z -> Z.
Variable rnd : R -> Z.
Notation pow e := (bpow beta e).
Local Notation RND := (round beta fexp rnd).

Definition split (x : R) (s : Z) :=
  let C := pow s  + 1 in 
  let g := RND (C * x) in 
  let d := RND (x - g) in 
  let xh := RND (g + d) in 
  let xl := RND (x - xh) in 
  DWR xh xl.

Context ( valid_rnd : Valid_rnd rnd ).

Lemma split_0 s : split 0 s = DWR 0 0.
Proof. by rewrite /split !(round_0, Rsimp01). Qed.


End split.

Lemma split_opp rnd fexp x s : 
  split fexp rnd (- x) s = opp_DWR (split fexp (Zrnd_opp rnd) x s).
Proof.
rewrite /Rminus /split.
have -> : (bpow beta s + 1) * - x = - ((bpow beta s + 1) * x) by lra.
by rewrite /Rminus !(round_opp, =^~ Ropp_plus_distr).
Qed.

Lemma split_oppr rnd fexp x s : 
  split fexp (Zrnd_opp rnd) (- x) s = opp_DWR (split fexp rnd x s).
Proof.
by rewrite -[in RHS](Ropp_involutive x) [in RHS]split_opp opp_DWR_K.
Qed.

Section Scale.

Variable p : Z.
Hypothesis precisionNotZero : (1 < p)%Z.
Context { prec_gt_0_ : Prec_gt_0 p}.
Notation format := (generic_format beta (FLX_exp p)).
Notation pow e := (bpow beta e).
Variable rnd : R -> Z.
Context ( valid_rnd : Valid_rnd rnd ).

Local Notation fexp := (FLX_exp p).
Local Notation ce := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation split := (split fexp rnd).
Local Notation splitr := (split fexp (Zrnd_opp rnd)).

Lemma cexp_bpow_flx x e (xne0 : x <> R0) : ce (pow e * x) = (ce x + e)%Z.
Proof. by rewrite /cexp Rmult_comm mag_mult_bpow // /fexp; lia. Qed.

Lemma mant_bpow_flx x e : mant (pow e * x) = mant x.
Proof.
have [->|Zx] := Req_dec x 0 ; first by rewrite Rsimp01.
rewrite /scaled_mantissa cexp_bpow_flx // Rmult_comm -Rmult_assoc Rmult_comm.
by congr Rmult; rewrite -bpow_plus; congr bpow; lia.
Qed.

Lemma round_bpow_flx x e : RND (pow e * x) = pow e  * RND x.
Proof.
have [->|Zx] := Req_dec x 0; first by rewrite !(round_0, Rsimp01).
by rewrite /round /F2R /= cexp_bpow_flx // mant_bpow_flx bpow_plus; lra.
Qed.

Lemma split_scale x s t : split (pow t * x) s = scale_DWR (pow t) (split x s).
Proof.
rewrite /split.
have -> : (pow s + 1) * (pow t * x) = pow t * ((pow s + 1) * x) by lra.
by rewrite !(round_bpow_flx, =^~ Rmult_minus_distr_l, =^~ Rmult_plus_distr_l).
Qed.

Lemma split_1 s :  (1 <= s <= p - 1)%Z -> split 1 s = DWR 1 0.
Proof.
move=> sB; rewrite /split !Rsimp01.
have -> : RND (pow s + 1) = pow s + 1.
  apply: round_generic.
  have -> : pow s + 1 = F2R (Float beta (2 ^ s + 1) 0).
    by rewrite /F2R /= plus_IZR (IZR_Zpower beta) //; try lra; lia.
  apply/generic_format_FLX/(FLX_spec _ _ _ (Float beta  (2 ^ s + 1) 0)) => //.
  rewrite /=.
  have -> : (Z.abs (2 ^ s + 1) = 2 ^ s + 1)%Z by lia.
  apply: Z.lt_le_trans (_ : (2 ^ (s + 1) <= _)%Z); last first.
    by apply: (Zpower_le beta); lia.
  have -> : (2 ^ (s + 1) = 2 ^ s + 2 ^ s)%Z by rewrite Z.pow_add_r; lia.
  suff : (1 < 2 ^ s)%Z by lia.
  by apply: (Zpower_lt beta 0); lia.
have -> : 1 - (pow s + 1) = - pow s by lra.
rewrite [RND (- _)]round_generic; last first.
  apply: generic_format_opp; apply: generic_format_bpow.
  by rewrite /fexp; lia.
have -> : pow s + 1 + - pow s  = 1 by lra.
rewrite [RND 1]round_generic; last first.
  by apply: (generic_format_bpow beta _ 0); rewrite /fexp; lia.
by rewrite Rsimp01 round_0.
Qed.

End Scale.


Section IMUL.

Variable p : Z.
Hypothesis precisionNotZero : (1 < p)%Z.
Context { prec_gt_0_ : Prec_gt_0 p}.
Notation format := (generic_format beta (FLX_exp p)).
Notation pow e := (bpow beta e).
Variable rnd : R -> Z.
Context ( valid_rnd : Valid_rnd rnd ).

Local Notation fexp := (FLX_exp p).
Local Notation ce := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation ulp := (ulp beta fexp).
Local Notation split := (split fexp rnd).
Local Notation splitr := (split fexp (Zrnd_opp rnd)).


Definition is_imul x y := exists z : Z, x = IZR z * y.

Lemma is_imul_add x1 x2 y : 
  is_imul x1 y -> is_imul x2 y -> is_imul (x1 + x2) y.
Proof.
move=> [z1 ->] [z2 ->]; exists (z1 + z2)%Z.
by rewrite plus_IZR; lra.
Qed.

Lemma is_imul_sub x1 x2 y : 
  is_imul x1 y -> is_imul x2 y -> is_imul (x1 - x2) y.
Proof.
move=> [z1 ->] [z2 ->]; exists (z1 - z2)%Z.
by rewrite minus_IZR; lra.
Qed.

Lemma is_imul_format_mag_pow x y : 
  format x -> (y <= fexp (mag beta x))%Z -> is_imul x (pow y).
Proof.
move=> Fx My.
have [-> | x_neq0] := Req_dec x 0; first by exists 0%Z; lra.
rewrite /generic_format /F2R /= in Fx.
rewrite Fx /cexp.
set m := Ztrunc _.
exists (m * (beta ^ (fexp (mag beta x) - y)))%Z.
rewrite mult_IZR IZR_Zpower; last by lia.
by rewrite Rmult_assoc -bpow_plus; congr (_ * pow _); lia.
Qed.

Lemma is_imul_pow_le_pow x s :
  format x -> pow s <= x -> is_imul x (pow (s - p + 1)).
Proof.
move=> xF pLx.
have pP : 0 < pow s by apply: bpow_gt_0.
have sLm : (s < mag beta x)%Z.
  by apply: mag_gt_bpow; rewrite Rabs_pos_eq; lra.
rewrite xF /cexp /fexp /F2R /=.
set z := Ztrunc _; exists (z * (beta ^ (mag beta x - s - 1)))%Z.
rewrite mult_IZR IZR_Zpower; last by lia.
by rewrite Rmult_assoc -bpow_plus; congr (_ * pow _); lia.
Qed.

Lemma is_imul_pow_round x y : is_imul x (pow y) -> is_imul (RND x) (pow y).
Proof.
move=> [k ->].
rewrite /round /mant /F2R /=.
set e1 := ce _; set m1 := rnd _.
have [e1L|yLe1] := Zle_or_lt e1 y.
  exists k.
  rewrite /m1.
  have -> : IZR k * pow y * pow (- e1) = IZR (k * beta ^ (y - e1)).
    rewrite Rmult_assoc -bpow_plus -IZR_Zpower; last by lia.
    by rewrite -mult_IZR.
  rewrite Zrnd_IZR.
  rewrite mult_IZR IZR_Zpower; last by lia.
  by rewrite Rmult_assoc -bpow_plus; congr (_ * pow _); lia.
exists ((rnd (IZR k * pow (y - e1))%R) * beta ^ (e1 - y))%Z.
rewrite mult_IZR IZR_Zpower; try lia.
rewrite /m1 Rmult_assoc -bpow_plus.
rewrite  Rmult_assoc -bpow_plus.
congr (_ * pow _); lia.
Qed.

Lemma is_imul_ulp x : format x -> is_imul x (ulp x).
Proof.
have [->|x_neq_0] := Req_dec x 0.
  by rewrite ulp_FLX_0; exists 0%Z; lra.
move=> xF; rewrite ulp_neq_0 // {1}xF.
by exists (Ztrunc (mant x)).
Qed.

Lemma is_imul_rnd_ulp x : 0 <= x -> is_imul (RND x) (ulp x).
Proof.
have [->|x_neq_0] := Req_dec x 0.
  by rewrite ulp_FLX_0 round_0; exists 0%Z; lra.
move=> xP; have {x_neq_0}xP : 0 < x by lra.
have [<-|->] : ulp (RND x) = ulp x \/ RND x = pow (mag beta x).
- by apply: ulp_round_pos.
- by apply: is_imul_ulp; apply: generic_format_round.
rewrite ulp_neq_0 /ce /fexp; last by lra.
exists (beta ^ p)%Z.
by rewrite IZR_Zpower -?bpow_plus; try congr bpow; lia.
Qed.

Lemma is_imul_pow_le x y1 y2 : 
  is_imul x (pow y1) -> (y2 <= y1)%Z -> is_imul x (pow y2).
Proof.
move=> [z ->] y2Ly1.
exists (z * beta ^ (y1 - y2))%Z.
rewrite mult_IZR IZR_Zpower; last by lia.
rewrite Rmult_assoc -bpow_plus; congr (_ * pow _); lia.
Qed.

Lemma is_imul_opp x v : is_imul x v -> is_imul (- x) v.
Proof. by move=> [z] ->; exists (- z)%Z; rewrite opp_IZR; lra. Qed.

Lemma is_imul_abs x v : is_imul x v -> is_imul (Rabs x) v.
Proof. by split_Rabs => //; apply: is_imul_opp. Qed.

Lemma is_abs_imul x v : is_imul (Rabs x) v -> is_imul x v.
Proof. 
by split_Rabs => //; rewrite -(Ropp_involutive x); apply: is_imul_opp.
Qed.

End IMUL.

Section FIT_IN.

Variable p : Z.
Hypothesis precisionNotZero : (1 < p)%Z.
Context { prec_gt_0_ : Prec_gt_0 p}.
Notation format := (generic_format beta (FLX_exp p)).
Notation pow e := (bpow beta e).
Variable rnd : R -> Z.
Context ( valid_rnd : Valid_rnd rnd ).

Definition fit_in x (n : nat) := 
  exists p, is_imul x (pow p) /\ (x <> 0 -> Rabs x < pow (Z.of_nat n + p)).

Lemma fit_in_opp x n : fit_in x n -> fit_in (- x) n.
Proof.
move=> [e] [Hx Hm]; exists e; split; first by apply: is_imul_opp.
by move=> x_neq0; rewrite Rabs_Ropp; apply: Hm; lra.
Qed.

Lemma fit_in_0 n : fit_in 0 n.
Proof. by exists 0%Z; split; [exists 0%Z|]; lra. Qed.

Lemma fit_in_pow e n : (1 <= n)%nat -> fit_in (pow e) n.
Proof.
exists e; split => [|_]; first by exists 1%Z; lra.
have epP: 0 < pow e by apply: bpow_gt_0.
rewrite ?bpow_plus Rabs_pos_eq; last by lra.
suff : 1 < pow (Z.of_nat n) by nra.
apply: (bpow_lt _ 0).
by move/ltP: H; lia.
Qed.

Lemma fit_in_1 n : (1 <= n)%nat -> fit_in 1 n.
Proof. by apply: (fit_in_pow 0). Qed.

Lemma fit_inE x n :
  fit_in x n <-> 
  exists m, exists e, (x = IZR m * pow e) /\ (Z.abs m < beta ^ Z.of_nat n)%Z.
Proof.
split => [[e [[m -> Hz]]]|[m [e [Hxe Hme]]]].
  exists m; exists e; split; first by lra.
  have epP: 0 < pow e by apply: bpow_gt_0.
  apply/lt_IZR; rewrite IZR_Zpower //; try lia.
  rewrite abs_IZR.
  have [->|mZ] := Req_dec (IZR m) 0; first by rewrite Rabs_R0; apply: bpow_gt_0.
  apply: Rmult_lt_reg_r (epP) _.
  rewrite -bpow_plus -[pow _]Rabs_pos_eq -?Rabs_mult; last by lra.
  by apply: Hz; nra.
have epP: 0 < pow e by apply: bpow_gt_0.
exists e; split => [|x_neq0]; first by exists m.
rewrite Hxe bpow_plus Rabs_mult [Rabs (pow _)]Rabs_pos_eq; last by lra.
apply: Rmult_lt_compat_r => //.
rewrite -abs_IZR -IZR_Zpower; last by lia.
by apply/IZR_lt.
Qed.

Lemma fit_in_pow_mult x n e : fit_in (pow e * x) n <-> fit_in x n.
Proof.
have epP: 0 < pow e by apply: bpow_gt_0.
split => [] [] e1.
  move=> [[z Hz] Hx]; exists (e1 - e)%Z; split.
    exists z.
    have -> : x = pow e * x * pow (- e).
      rewrite Rmult_comm -Rmult_assoc -bpow_plus.
      suff <- : 1 = pow (- e + e) by lra.
      by rewrite -[1]/(pow 0); congr (pow _); lia.
    rewrite Hz bpow_plus; lra.
  move=> x_neq0; rewrite bpow_plus.
  apply: Rmult_lt_reg_r (epP) _.
  rewrite Rmult_assoc -!bpow_plus.
  have -> : (e1 - e + e = e1)%Z by lia.
  rewrite -[pow _]Rabs_pos_eq -?Rabs_mult; last by lra.
  by rewrite Rmult_comm; apply: Hx; nra.
move=> [Hm Hx]; exists (e1 + e)%Z; split => [|Hz].
  by rewrite bpow_plus; case: Hm => z ->; exists z; lra.
rewrite Rmult_comm Zplus_assoc bpow_plus Rabs_mult [Rabs(pow _)]Rabs_pos_eq.
  by apply: Rmult_lt_compat_r => //; apply: Hx; nra.
lra.
Qed.

End FIT_IN.

Section Main.

Variable p : Z.
Hypothesis precisionNotZero : (1 < p)%Z.
Context { prec_gt_0_ : Prec_gt_0 p}.
Notation format := (generic_format beta (FLX_exp p)).
Notation pow e := (bpow beta e).
Variable rnd : R -> Z.
Context ( valid_rnd : Valid_rnd rnd ).

Local Notation fexp := (FLX_exp p).
Local Notation ce := (cexp beta fexp).
Local Notation mant := (scaled_mantissa beta fexp).
Local Notation ulp := (ulp beta fexp).
Local Notation RND := (round beta fexp rnd).
Local Notation split := (split fexp rnd).
Local Notation splitr := (split fexp (Zrnd_opp rnd)).
Local Notation pred := (Ulp.pred beta fexp).

Lemma bpow_lt_ulp x s :  Rabs x < pow s -> ulp x <= pow (s - p).
Proof.
move=> xLs.
pose y := pred (pow s).
have yE : y = pow s - pow (s - p) by apply: pred_bpow.
have yP : 0 < y.
  rewrite yE; suff : pow (s - p) < pow s by lra.
  by apply: bpow_lt; lia.
have s1Lp : pow (s - 1) < y.
  rewrite yE; have -> : pow s = 2 * pow (s - 1).
    by rewrite -(bpow_plus radix2 1); congr (pow _); lia.
  suff : pow (s - p) < pow (s - 1) by lra.
  by apply: bpow_lt; lia.
have yU : ulp y = pow (s - p).
  rewrite ulp_neq_0; last by lra.
  rewrite /cexp /fexp (mag_unique_pos beta _ s) //; split; first by lra.
  rewrite yE; suff : 0 < pow (s - p) by lra.
  by apply: bpow_gt_0.
have [xLp|pLx] := Rle_lt_dec (Rabs x) y.
  rewrite -yU -[ulp x]ulp_abs.
  by apply: ulp_le_pos => //; clear; split_Rabs; lra.
rewrite -[ulp x]ulp_abs; suff -> : ulp (Rabs x) = pow (s - p) by lra.
rewrite ulp_neq_0 /cexp /fexp; last by lra.
rewrite (mag_unique_pos beta _ s) //.
by split; lra.
Qed.

Lemma split_sum x s :  
  [\/ forall x, rnd x = Ztrunc x, forall x, rnd x = Zfloor x |
      forall x, rnd x = Zceil x] ->
  format x -> (1 <= s <= p - 1)%Z -> let: DWR xh xl := split x s in 
  [/\ x = xh + xl,
      fit_in xh (Z.to_nat (p - s)) & fit_in xl (Z.to_nat s)].
Proof.
move=> Crnd xF sB.
move: rnd valid_rnd Crnd.
have psP : 0 < pow s by apply: bpow_gt_0.
have ps1P : 0 < pow (s + 1) by apply: bpow_gt_0.
have ps1pP : 0 < pow (s - p + 1) by apply: bpow_gt_0.
have psp1P : 0 < pow (- p + 1) by apply: bpow_gt_0.
wlog : x xF / 0 < x => [IH rnd1 Vrnd1 Crnd1| xP rnd1 Vrnd1 Crnd1].
  have [->|xP|xN]: [\/ x = 0, 0 < x | x < 0].
  - case: (Rle_dec x 0) => ?; last by apply: Or32; lra.
    by case: (Req_dec x 0) => ?; [apply: Or31| apply: Or33; lra].
  - by rewrite split_0; split; try (by apply: fit_in_0); lra.
  - by apply: IH.
  have xNN : 0 < - x by lra.
  suff : let 'DWR xh xl := FLX_VD.split fexp (Zrnd_opp rnd1) (- x) s 
         in [/\ - x = xh + xl, fit_in xh (Z.to_nat (p - s)) & 
                 fit_in xl (Z.to_nat s)].
    rewrite split_oppr; case: FLX_VD.split => /= xh xl [? ? ?].
    split; first by lra.
      have -> : xh = - (- xh) by lra.
      by apply: fit_in_opp.
    have -> : xl = - (- xl) by lra.
    by apply: fit_in_opp.
  apply: IH => //.
    by apply: generic_format_opp.
    case: Crnd1 => Hr.
    apply: Or31 => x1.
    by rewrite /Zrnd_opp /= Hr Ztrunc_opp; lia.
  apply: Or33 => x1; first by rewrite /Zrnd_opp /= Hr.
  apply: Or32 => x1.
  rewrite /Zrnd_opp /= Hr /Zceil.
  suff -> : (- - x1 = x1)%R by lia.
  lra.
set splitv := FLX_VD.split fexp rnd1.
wlog : x xP xF / 1 <= x  < 2 => [IH | xB].
  pose e := (- (mag beta x - 1))%Z.
  have epP : 0 < pow e by apply: bpow_gt_0.
  suff : let 'DWR xh xl := splitv (pow e * x) s 
         in [/\ (pow e * x) = xh + xl, fit_in xh (Z.to_nat (p -s)) &
                fit_in xl (Z.to_nat s)].
    rewrite /splitv split_scale; case: FLX_VD.split => /= xh xl [H1 H2 H3].
    split; first by nra.
      by apply/fit_in_pow_mult; exact: H2.
    by apply/fit_in_pow_mult; exact: H3.
  apply: IH; first by nra.
    by rewrite Rmult_comm; apply: mult_bpow_exact_FLX.
  have -> : 1 =  pow e * pow (- e).
    have -> : 1 = pow 0 by [].
    by rewrite -bpow_plus; congr bpow; lia.
  have -> : 2 =  pow e * pow (mag beta x).
    have -> : 2 = pow 1 by [].
    by rewrite -bpow_plus; congr bpow; lia.
  split.
    apply: Rmult_le_compat_l; first by apply: bpow_ge_0.
    rewrite -[X in _ <= X]Rabs_pos_eq; last by lra.
    rewrite /e Z.opp_involutive.
    by apply: bpow_mag_le; lra.
  apply: Rmult_lt_compat_l; first by apply: bpow_gt_0.
  rewrite -[X in X < _]Rabs_pos_eq; last by lra.
  by apply: bpow_mag_gt; lra.
have [->|x_neq_1]:= Req_dec x 1.
  rewrite /splitv split_1 //; split; first by lra.
    by apply: fit_in_1; apply/leP; lia.
  by apply: fit_in_0.
have {x_neq_1 xP}xB : 1 < x < 2 by lra.
have xB1 : 1 + pow (- p + 1) <= x <= 2 - pow (- p + 1).
  split.
    have <- : ulp 1 = pow (- p + 1) by rewrite ulp_FLX_1.
    rewrite -succ_eq_pos; last by lra.
    apply: succ_le_lt => //; last by lra.
    by apply: (generic_format_bpow beta _ 0); rewrite /fexp; lia.
  suff -> : 2 - pow (- p + 1) =  Ulp.pred beta fexp 2.
    apply: pred_ge_gt => //; last by lra.
    by apply: (generic_format_bpow beta _ 1); rewrite /fexp; lia.
  by rewrite (pred_bpow beta _ 1) /fexp; congr (_ - pow _); lia.
pose C := pow s  + 1.
have powsP : 1 < pow s by apply: (bpow_lt beta 0); lia.
have CxB : pow s + 1 < C * x < pow (s + 2).
  rewrite /C; split; first by nra.
  have -> : (s + 2 = (s + 1) + 1)%Z by lia.
  rewrite bpow_plus -[pow 1]/2.
  apply: Rmult_lt_compat; try lra.
  by rewrite bpow_plus -[pow 1]/2; lra.
have uCxB :  pow (s - p + 1) <= ulp (C * x) <= pow (s - p + 2).
  split.
    suff <- : ulp (pow s + 1) = pow (s - p + 1).
      by apply: ulp_le_pos; lra.
    rewrite ulp_neq_0; last by lra.
    congr bpow; rewrite /cexp /fexp (mag_unique_pos beta _ (s + 1)).
      by lia.
    split; first by (have -> : (s + 1 - 1 = s)%Z by lia); lra.
    by rewrite bpow_plus -[pow 1]/2; lra.
  rewrite ulp_neq_0 /cexp /fexp; last by lra.
  apply: bpow_le.
  suff: (mag beta (C * x) <= s + 2)%Z by lia.
  apply: mag_le_bpow; first by nra.
  rewrite Rabs_pos_eq; first by lra.
  by nra.
pose RND1 := (round beta fexp rnd1).
pose g := RND1 (C * x).
pose e1 := g - C * x.
have e1E : g = C * x + e1 by rewrite /e1; lra.
have e1B : Rabs e1 < pow (s - p + 2).
  suff : Rabs e1 < ulp (C * x) by lra.
  by apply: error_lt_ulp; lra.
have gM : is_imul g (pow (s - p + 1)).
  have gM1 : is_imul g (ulp (C * x)).
    apply: is_imul_rnd_ulp => //; first by lra.
  rewrite ulp_neq_0 in gM1 uCxB; last by lra.
  apply: is_imul_pow_le gM1 _.
  by apply: (le_bpow beta); lra.
pose d := RND1 (x - g).
pose e2 := d - (x - g).
have e2E : d =  x - g + e2 by rewrite /e2; lra.
have e2E1 : d = - pow s * x - e1 + e2 by rewrite e2E e1E /C; lra.
have rs1E : RND1 (- pow (s + 1)) = - pow (s + 1).
  apply: round_generic.
  apply: generic_format_opp.
  apply: generic_format_bpow.
  by rewrite /fexp; lia.    
have xgE : x - g = - pow s * x - e1 by rewrite e1E /C; lra.
have p2C : p = 2%Z -> (g = 4 /\ (d = - 3 \/ d = - 2)) \/
                      (g = 6 /\ (d = - 6 \/ d = - 4)).
    move=> pE; rewrite pE -[pow _]/(/2) in xB1.
    have sE : s = 1%Z by lia.
    have cE : C = 3 by rewrite /C sE -[pow _]/2; lra.
    have xE : x = 1 + /2 by lra.
    have cxE : C * x = 4 + 1/2 by rewrite cE xE; lra.
    have [gE|gE] : g = round beta fexp Zfloor (C * x) \/ 
                   g = round beta fexp Zceil (C * x).
    - rewrite /g /RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (C * x))) => ->; [left|right].
    - left. 
      have gE1 : g = 4.
        rewrite gE; apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta 1 2)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        split; first by lra.
        suff -> : succ beta fexp 4 = 6 by lra.
        rewrite succ_eq_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 3) //.
          rewrite pE -[pow _]/2; lra.
        by rewrite -[pow _]/4 -[pow 3]/8; lra.
      split => //.
      have xgE1 : x - g = - 3 + /2 by lra.
      have [dE|dE] : d = round beta fexp Zfloor (x - g) \/ 
                         d = round beta fexp Zceil (x - g).
      - rewrite /d/RND1 /round /=.
        by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
      - left; rewrite dE.
        apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta (-3) 0)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        rewrite succ_opp -[IPR 3]/3.
        suff -> : pred 3 = 2 by lra.
        rewrite pred_eq_pos /pred_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 2) //.
          rewrite pE -[pow _]/2 -[pow _]/(/2) -[pow _]/1.
          by case: Req_bool_spec; lra.
        by rewrite -[pow _]/2 -[pow _]/4; lra.
      right; rewrite dE.
      apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-2) 0)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      rewrite pred_opp succ_eq_pos -[IPR _]/2; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 2) //.
        by rewrite pE -[pow _]/1; lra.
      by rewrite -[pow _]/2 -[pow _]/4; lra.
    right.
    have gE1 : g = 6.
      rewrite gE; apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta 3 1)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : pred 6 = 4 by lra.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        rewrite pE -[pow _]/4 -[pow _]/1 -[pow _]/2.
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    split => //.
    have xgE1 : x - g = - 5 + /2 by lra.
    have [dE|dE] : d = round beta fexp Zfloor (x - g) \/ 
                        d = round beta fexp Zceil (x - g).
    - rewrite /d/RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
    - left; rewrite dE.
      apply: round_DN_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-3) 1)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      rewrite succ_opp -[IPR _]/6.
      suff -> : pred 6 = 4 by lra.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        rewrite pE -[pow _]/4 -[pow _]/1 -[pow _]/2.
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    right; rewrite dE.
    apply: round_UP_eq.
      apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta (-1) 2)).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    rewrite pred_opp succ_eq_pos -[IPR _]/4; last by lra.
    rewrite ulp_neq_0 /ce /fexp; last by lra.
    rewrite (mag_unique_pos beta _ 3) //.
      by rewrite pE -[pow _]/2; lra.
    by rewrite -[pow _]/4 -[pow _]/8; lra.
have p3C : p = 3%Z -> [\/ x = 1 + /4 /\
                          [\/ g = 4 - /2 /\ (d = - 2 - /2 \/ d = - 2),
                              g = 4      /\ (d = - 3      \/ d = - 2 - /2),
                              g = 6      /\ (d = - 5      \/ d = - 4) |
                              g = 7      /\ (d = - 6      \/ d = - 5)]    ,
                          x = 1 + /2 /\
                          [\/ g = 4      /\  d = - 3  + /2,
                              g = 5      /\  d = - 4  + /2,
                              g = 7      /\ (d = - 6      \/ d = - 5) |
                              g = 8      /\ (d = - 7      \/ d = - 6)]    |
                          x = 2 - /4 /\
                          [\/ g = 5       /\ (d = - 3  - /2 \/ d = - 3),
                              g = 6       /\ (d = - 5       \/ d = - 4),
                              g = 8       /\ (d = - 7       \/ d = - 6) |
                              g = 10      /\ (d = - 10      \/ d = - 8)]].
  move=> pE; rewrite pE -[pow _]/(/4) in xB1.
  have sE : s = 1%Z \/ s = 2%Z by lia.
  have [xE|xD1] := Req_dec x (1 + /4).
    apply: Or31; split => //.
    case: sE => sE.
      have cE : C = 3 by rewrite /C sE -[pow _]/2; lra.
      have cxE : C * x = 4 - / 4 by rewrite cE xE; lra.
      have [gE|gE] : g = round beta fexp Zfloor (C * x) \/ 
                     g = round beta fexp Zceil (C * x).
      - rewrite /g /RND1 /round /=.
        by case: (Zrnd_DN_or_UP rnd1 (mant (C * x))) => ->; [left|right].
      - have gE1 : g = 4 - /2.
          rewrite gE; apply: round_DN_eq.
            apply: generic_format_FLX.
            apply: (FLX_spec beta p _ (Float beta 7 (-1))).
              by rewrite /F2R /=; lra.
            by rewrite /= pE; lia.
          suff -> : succ beta fexp (4 - /2) = 4 by lra.
          rewrite succ_eq_pos; last by lra.
          rewrite ulp_neq_0 /ce /fexp; last by lra.
          rewrite (mag_unique_pos beta _ 2) //.
            by rewrite pE -[pow _]/(/2); lra.
          by rewrite -[pow _]/2 -[pow _]/4; lra.
        apply: Or41; split => //.
        have xgE1 : x - g = - 2 - /4 by lra.
        have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                         d = round beta fexp Zceil (x - g).
        - rewrite /d /RND1 /round /=.
          by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
        - suff dE2 : d = - 2 - /2 by lra.
          rewrite dE1; apply: round_DN_eq.
            apply: generic_format_FLX.
            apply: (FLX_spec beta p _ (Float beta (-5) (-1))).
              by rewrite /F2R /=; lra.
            by rewrite /= pE; lia.
          suff -> : succ beta fexp (- 2 - /2) = - 2 by lra.
          have -> : - 2 - /2 = - (2 + /2) by lra.
          rewrite succ_opp.
          rewrite pred_eq_pos /pred_pos; last by lra.
          rewrite ulp_neq_0 /ce /fexp; last by lra.
          rewrite (mag_unique_pos beta _ 2) //.
            rewrite pE -[pow _]/2 -[pow _]/(/4) -[pow _]/(/2).
            by case: Req_bool_spec; lra.
          by rewrite -[pow _]/2 -[pow _]/4; lra.
        suff dE2 : d = - 2 by lra.
        rewrite dE1; apply: round_UP_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta (-1) 1)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : pred (- 2) = - 2 - /2 by lra.
        have -> : - 2 - /2 = - (2 + /2) by lra.
        rewrite pred_opp -[IPR 2]/2.
        rewrite succ_eq_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 2) //.
          by rewrite pE -[pow _]/(/2); lra.
        by rewrite -[pow _]/2 -[pow _]/4; lra.
      have gE1 : g = 4.
        rewrite gE; apply: round_UP_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta 1 2)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : pred 4 = 4 - /2 by lra.
        rewrite pred_eq_pos /pred_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 3) //.
          rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/1.
          by case: Req_bool_spec; lra.
        by rewrite -[pow _]/4 -[pow _]/8; lra.
      apply: Or42; split => //.
      have xgE1 : x - g = - 3 + /4 by lra.
      have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                      d = round beta fexp Zceil (x - g).
      - rewrite /d /RND1 /round /=.
        by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
      - suff dE2 : d = - 3 by lra.
        rewrite dE1; apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta (-3) 0)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : succ beta fexp (- 3) = - 3 + /2 by lra.
        rewrite succ_opp -[IPR 3]/3.
        rewrite pred_eq_pos /pred_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 2) //.
          rewrite pE -[pow _]/2 -[pow _]/(/4) -[pow _]/(/2).
          by case: Req_bool_spec; lra.
        by rewrite -[pow _]/2 -[pow _]/4; lra.
      suff dE2 : d = - 2 - /2 by lra.
      rewrite dE1; apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-5) (-1))).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : pred (- 2 - /2) = - 3 by lra.
      have -> : - 2 - /2 = - (2 + /2) by lra.
      rewrite pred_opp.
      rewrite succ_eq_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 2) //.
        by rewrite pE -[pow _]/(/2); lra.
      by rewrite -[pow _]/2 -[pow _]/4; lra.
    have cE : C = 5 by rewrite /C sE -[pow _]/4; lra.
    have cxE : C * x = 6 + / 4 by rewrite cE xE; lra.
    have [gE|gE] : g = round beta fexp Zfloor (C * x) \/ 
                    g = round beta fexp Zceil (C * x).
    - rewrite /g /RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (C * x))) => ->; [left|right].
    - have gE1 : g = 6.
        rewrite gE; apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta 3 1)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : succ beta fexp 6 = 7 by lra.
        rewrite succ_eq_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 3) //.
          by rewrite pE -[pow _]/1; lra.
        by rewrite -[pow _]/4 -[pow _]/8; lra.
      apply: Or43; split => //.
      have xgE1 : x - g = - 5 + /4 by lra.
      have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                        d = round beta fexp Zceil (x - g).
      - rewrite /d /RND1 /round /=.
        by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
      - suff dE2 : d = - 5 by lra.
        rewrite dE1; apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta (-5) (0))).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : succ beta fexp (- 5) = - 4 by lra.
        rewrite succ_opp -[IPR _]/5.
        rewrite pred_eq_pos /pred_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 3) //.
          rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/1.
          by case: Req_bool_spec; lra.
        by rewrite -[pow _]/4 -[pow _]/8; lra.
      suff dE2 : d = - 4 by lra.
      rewrite dE1; apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-1) 2)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      rewrite pred_opp -[IPR _]/4.
      rewrite succ_eq_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        by rewrite pE -[pow _]/1; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    have gE1 : g = 7.
      rewrite gE; apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta 7 0)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : pred 7 = 6 by lra.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/1.
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    apply: Or44; split => //.
    have xgE1 : x - g = - 6 + /4 by lra.
    have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                    d = round beta fexp Zceil (x - g).
    - rewrite /d /RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
    - suff dE2 : d = - 6 by lra.
      rewrite dE1; apply: round_DN_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-3) 1)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : succ beta fexp (- 6) = - 5 by lra.
      rewrite succ_opp -[IPR _]/6.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/(1).
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    suff dE2 : d = - 5 by lra.
    rewrite dE1; apply: round_UP_eq.
      apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta (-5) 0)).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    rewrite pred_opp -[IPR _]/5.
    rewrite succ_eq_pos; last by lra.
    rewrite ulp_neq_0 /ce /fexp; last by lra.
    rewrite (mag_unique_pos beta _ 3) //.
      by rewrite pE -[pow _]/1; lra.
    by rewrite -[pow _]/4 -[pow _]/8; lra.
  have [xE|xD2] := Req_dec x (1 + /2).
    apply: Or32; split => //.
    case: sE => sE.
      have cE : C = 3 by rewrite /C sE -[pow _]/2; lra.
      have cxE : C * x = 4 + / 2 by rewrite cE xE; lra.
      have [gE|gE] : g = round beta fexp Zfloor (C * x) \/ 
                      g = round beta fexp Zceil (C * x).
      - rewrite /g /RND1 /round /=.
        by case: (Zrnd_DN_or_UP rnd1 (mant (C * x))) => ->; [left|right].
      - have gE1 : g = 4.
          rewrite gE; apply: round_DN_eq.
            apply: generic_format_FLX.
            apply: (FLX_spec beta p _ (Float beta 1 2)).
              by rewrite /F2R /=; lra.
            by rewrite /= pE; lia.
          suff -> : succ beta fexp 4 = 5 by lra.
          rewrite succ_eq_pos; last by lra.
          rewrite ulp_neq_0 /ce /fexp; last by lra.
          rewrite (mag_unique_pos beta _ 3) //.
            by rewrite pE -[pow _]/1; lra.
          by rewrite -[pow _]/4 -[pow _]/8; lra.
        apply: Or41; split => //.
        have xgE1 : x - g = - 3 + /2 by lra.
        rewrite - xgE1; apply: round_generic.
        rewrite xgE1.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-5) (-1))).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      have gE1 : g = 5.
        rewrite gE; apply: round_UP_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta 5 0)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : pred 5 = 4 by lra.
        rewrite pred_eq_pos /pred_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 3) //.
          rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/1.
          by case: Req_bool_spec; lra.
        by rewrite -[pow _]/4 -[pow _]/8; lra.
      apply: Or42; split => //.
      have xgE1 : x - g = - 4 + /2 by lra.
      rewrite -xgE1; apply: round_generic.
      rewrite xgE1; apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta (-7) (-1))).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    have cE : C = 5 by rewrite /C sE -[pow _]/4; lra.
    have cxE : C * x = 7 + / 2 by rewrite cE xE; lra.
    have [gE|gE] : g = round beta fexp Zfloor (C * x) \/ 
                    g = round beta fexp Zceil (C * x).
    - rewrite /g /RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (C * x))) => ->; [left|right].
    - have gE1 : g = 7.
        rewrite gE; apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta 7 0)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : succ beta fexp 7 = 8 by lra.
        rewrite succ_eq_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 3) //.
          by rewrite pE -[pow _]/1; lra.
        by rewrite -[pow _]/4 -[pow _]/8; lra.
      apply: Or43; split => //.
      have xgE1 : x - g = - 6 + /2 by lra.
      have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                      d = round beta fexp Zceil (x - g).
      - rewrite /d /RND1 /round /=.
        by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
      - suff dE2 : d = - 6 by lra.
        rewrite dE1; apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta (-3) 1)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : succ beta fexp (- 6) = - 5 by lra.
        rewrite succ_opp -[IPR _]/6.
        rewrite pred_eq_pos /pred_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 3) //.
          rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/(1).
          by case: Req_bool_spec; lra.
        by rewrite -[pow _]/4 -[pow _]/8; lra.
      suff dE2 : d = - 5 by lra.
      rewrite dE1; apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-5) 0)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      rewrite pred_opp -[IPR _]/5.
      rewrite succ_eq_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        by rewrite pE -[pow _]/1; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    have gE1 : g = 8.
      rewrite gE; apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta 1 3)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : pred 8 = 7 by lra.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 4) //.
        rewrite pE -[pow _]/8 -[pow _]/1 -[pow _]/2.
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/8 -[pow _]/16; lra.
    apply: Or44; split => //.
    have xgE1 : x - g = - 7 + /2 by lra.
    have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                     d = round beta fexp Zceil (x - g).
    - rewrite /d /RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
    - suff dE2 : d = - 7 by lra.
      rewrite dE1; apply: round_DN_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-7) 0)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : succ beta fexp (- 7) = - 6 by lra.
      rewrite succ_opp -[IPR _]/7.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/(1).
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    suff dE2 : d = - 6 by lra.
    rewrite dE1; apply: round_UP_eq.
      apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta (-3) 1)).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    rewrite pred_opp -[IPR _]/6.
    rewrite succ_eq_pos; last by lra.
    rewrite ulp_neq_0 /ce /fexp; last by lra.
    rewrite (mag_unique_pos beta _ 3) //.
      by rewrite pE -[pow _]/1; lra.
    by rewrite -[pow _]/4 -[pow _]/8; lra.
  have xE : x = 2 - /4.
    have F1 : format (1 + /4).
      apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta 5 (-2))).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    have F2 : succ beta fexp (1 + /4) = 1 + /2.
      rewrite succ_eq_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 1) //.
        by rewrite pE -[pow _]/(/4); lra.
      by rewrite -[pow _]/1 -[pow _]/2; lra.
    have F3 : succ beta fexp (1 + /2) = 2 - /4.
      rewrite succ_eq_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 1) //.
        by rewrite pE -[pow _]/(/4); lra.
      by rewrite -[pow _]/1 -[pow _]/2; lra.
    have F4 : 1 + /2 <= x by rewrite -F2; apply: succ_le_lt => //; lra.
    suff F5 : 2 - /4 <= x by lra.
    rewrite -F3; apply: succ_le_lt => //.
      by rewrite -F2; apply: generic_format_succ.
    by lra.
  apply: Or33; split => //.
  case: sE => sE.
    have cE : C = 3 by rewrite /C sE -[pow _]/2; lra.
    have cxE : C * x = 5 + / 4 by rewrite cE xE; lra.
    have [gE|gE] : g = round beta fexp Zfloor (C * x) \/ 
                   g = round beta fexp Zceil (C * x).
    - rewrite /g /RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (C * x))) => ->; [left|right].
    - have gE1 : g = 5.
        rewrite gE; apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta 5 0)).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : succ beta fexp 5 = 6 by lra.
        rewrite succ_eq_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 3) //.
          by rewrite pE -[pow _]/1; lra.
        by rewrite -[pow _]/4 -[pow _]/8; lra.
      apply: Or41; split => //.
      have xgE1 : x - g = - 3 - /4 by lra.
      have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                       d = round beta fexp Zceil (x - g).
      - rewrite /d /RND1 /round /=.
        by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
      - suff dE2 : d = - 3 - /2 by lra.
        rewrite dE1; apply: round_DN_eq.
          apply: generic_format_FLX.
          apply: (FLX_spec beta p _ (Float beta (-7) (-1))).
            by rewrite /F2R /=; lra.
          by rewrite /= pE; lia.
        suff -> : succ beta fexp (- 3 - /2) = - 3 by lra.
        have -> : - 3 - /2 = - (3 + /2) by lra.
        rewrite succ_opp.
        rewrite pred_eq_pos /pred_pos; last by lra.
        rewrite ulp_neq_0 /ce /fexp; last by lra.
        rewrite (mag_unique_pos beta _ 2) //.
          rewrite pE -[pow _]/2 -[pow _]/(/4) -[pow _]/(/2).
          by case: Req_bool_spec; lra.
        by rewrite -[pow _]/2 -[pow _]/4; lra.
      suff dE2 : d = - 3 by lra.
      rewrite dE1; apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-3) 0)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      rewrite pred_opp -[IPR 3]/3.
      rewrite succ_eq_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 2) //.
        by rewrite pE -[pow _]/(/2); lra.
      by rewrite -[pow _]/2 -[pow _]/4; lra.
    have gE1 : g = 6.
      rewrite gE; apply: round_UP_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta 3 1)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : pred 6 = 5 by lra.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/1.
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    apply: Or42; split => //.
    have xgE1 : x - g = - 4 - /4 by lra.
    have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                     d = round beta fexp Zceil (x - g).
    - rewrite /d /RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
    - suff dE2 : d = - 5 by lra.
      rewrite dE1; apply: round_DN_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-5) 0)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : succ beta fexp (- 5) = - 4 by lra.
      rewrite succ_opp -[IPR _]/5.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/1.
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    suff dE2 : d = - 4 by lra.
    rewrite dE1; apply: round_UP_eq.
      apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta (-1) 2)).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    rewrite pred_opp -[IPR _]/4.
    rewrite succ_eq_pos; last by lra.
    rewrite ulp_neq_0 /ce /fexp; last by lra.
    rewrite (mag_unique_pos beta _ 3) //.
      by rewrite pE -[pow _]/1; lra.
    by rewrite -[pow _]/4 -[pow _]/8; lra.
  have cE : C = 5 by rewrite /C sE -[pow _]/4; lra.
  have cxE : C * x = 9 - / 4 by rewrite cE xE; lra.
  have [gE|gE] : g = round beta fexp Zfloor (C * x) \/ 
                 g = round beta fexp Zceil (C * x).
  - rewrite /g /RND1 /round /=.
    by case: (Zrnd_DN_or_UP rnd1 (mant (C * x))) => ->; [left|right].
  - have gE1 : g = 8.
      rewrite gE; apply: round_DN_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta 1 3)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : succ beta fexp 8 = 10 by lra.
      rewrite succ_eq_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 4) //.
        by rewrite pE -[pow _]/2; lra.
      by rewrite -[pow _]/8 -[pow _]/16; lra.
    apply: Or43; split => //.
    have xgE1 : x - g = - 6 - /4 by lra.
    have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                     d = round beta fexp Zceil (x - g).
    - rewrite /d /RND1 /round /=.
      by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
    - suff dE2 : d = - 7 by lra.
      rewrite dE1; apply: round_DN_eq.
        apply: generic_format_FLX.
        apply: (FLX_spec beta p _ (Float beta (-7) 0)).
          by rewrite /F2R /=; lra.
        by rewrite /= pE; lia.
      suff -> : succ beta fexp (- 7) = - 6 by lra.
      rewrite succ_opp -[IPR _]/7.
      rewrite pred_eq_pos /pred_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 3) //.
        rewrite pE -[pow _]/4 -[pow _]/(/2) -[pow _]/1.
        by case: Req_bool_spec; lra.
      by rewrite -[pow _]/4 -[pow _]/8; lra.
    suff dE2 : d = - 6 by lra.
    rewrite dE1; apply: round_UP_eq.
      apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta (-3) 1)).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    rewrite pred_opp -[IPR _]/6.
    rewrite succ_eq_pos; last by lra.
    rewrite ulp_neq_0 /ce /fexp; last by lra.
    rewrite (mag_unique_pos beta _ 3) //.
      by rewrite pE -[pow _]/1; lra.
    by rewrite -[pow _]/4 -[pow _]/8; lra.
  have gE1 : g = 10.
    rewrite gE; apply: round_UP_eq.
      apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta 5 1)).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    suff -> : pred 10 = 8 by lra.
    rewrite pred_eq_pos /pred_pos; last by lra.
    rewrite ulp_neq_0 /ce /fexp; last by lra.
    rewrite (mag_unique_pos beta _ 4) //.
      rewrite pE -[pow _]/8 -[pow _]/1 -[pow _]/2.
      by case: Req_bool_spec; lra.
    by rewrite -[pow _]/8 -[pow _]/16; lra.
  apply: Or44; split => //.
  have xgE1 : x - g = - 8 - /4 by lra.
  have [dE1|dE1] : d = round beta fexp Zfloor (x - g) \/ 
                  d = round beta fexp Zceil (x - g).
  - rewrite /d /RND1 /round /=.
    by case: (Zrnd_DN_or_UP rnd1 (mant (x - g))) => ->; [left|right].
  - suff dE2 : d = - 10 by lra.
    rewrite dE1; apply: round_DN_eq.
      apply: generic_format_FLX.
      apply: (FLX_spec beta p _ (Float beta (-5) 1)).
        by rewrite /F2R /=; lra.
      by rewrite /= pE; lia.
    suff -> : succ beta fexp (- 10) = - 8 by lra.
    rewrite succ_opp -[IPR _]/10.
    rewrite pred_eq_pos /pred_pos; last by lra.
    rewrite ulp_neq_0 /ce /fexp; last by lra.
    rewrite (mag_unique_pos beta _ 4) //.
      rewrite pE -[pow _]/8 -[pow _]/1 -[pow _]/2.
      by case: Req_bool_spec; lra.
    by rewrite -[pow _]/8 -[pow _]/16; lra.
  suff dE2 : d = - 8 by lra.
  rewrite dE1; apply: round_UP_eq.
    apply: generic_format_FLX.
    apply: (FLX_spec beta p _ (Float beta (-1) 3)).
      by rewrite /F2R /=; lra.
    by rewrite /= pE; lia.
  rewrite pred_opp -[IPR _]/8.
  rewrite succ_eq_pos; last by lra.
  rewrite ulp_neq_0 /ce /fexp; last by lra.
  rewrite (mag_unique_pos beta _ 4) //.
    by rewrite pE -[pow _]/2; lra.
  by rewrite -[pow _]/8 -[pow _]/16; lra.
have xgB : Rabs (x - g) < pow (s + 1) + pow (s- p + 1).
  rewrite xgE.
  apply: Rle_lt_trans (_ : Rabs (pow s * x) + Rabs e1 < _).
    by split_Rabs; lra.
  have -> : pow (s + 1) + pow (s - p + 1) =  
            pow s * (2 - pow (- p +1)) + pow (s- p + 2).
    have -> : (s - p + 1 = s + (- p + 1))%Z by lia.
    have -> : (s - p + 2 = 1 + s + (- p + 1))%Z by lia.
    by rewrite !bpow_plus -[pow 1]/2; lra.
  suff : Rabs (pow s * x) <= pow s * (2 - pow (- p + 1)) by lra.
  rewrite Rabs_mult !Rabs_pos_eq; try lra.
  apply: Rmult_le_compat_l; lra.
have sxBu :  - pow s * x <= - pow s - pow (s - p + 1).
  have -> : (s - p + 1 = s + (- p + 1))%Z by lia.
  by rewrite bpow_plus; nra.
have xgBu : x - g < - pow s + pow (s - p + 1).
  suff : pow (s - p + 2) = 2 * pow (s - p + 1).
    by rewrite xgE; clear -e1B sxBu; split_Rabs; lra. 
  have -> : (s - p + 2 = (s - p + 1) + 1)%Z by lia.
  by rewrite bpow_plus -[pow 1]/2; lra.
have xgN : x - g < 0.
  suff :  pow (s - p + 1) < pow s by lra.
  by apply: bpow_lt; lia.
have e1NxgB : e1 <= 0 ->  - pow (s + 1) <= x - g.
  move=> e1N.
  have F2 : pow (s - p + 1) - pow (s + 1) <= - pow s * x.
    have -> : (s - p + 1 = s + (- p + 1))%Z by lia.
    by rewrite bpow_plus [pow (s + 1)]bpow_plus -[pow 1]/2; nra.
  have F3 : pow (s - p + 1) - pow (s + 1) <= x - g by rewrite xgE; lra.
  by lra.
have e1PxgB : 0 < e1 -> x - g <= - pow (s + 1) -> d = - pow (s + 1).
  move=> e1P xgBl.
  have CxNF : ~ format (C * x).
    move => CxF; suff : g = C * x by lra.
    by rewrite /g /RND1 round_generic.
  have Hrnd1 x1 : rnd1 x1 = Zceil x1.
    have CxB1 : round beta fexp Zfloor (C * x) < C * x < 
                round beta fexp Zceil (C * x).
        by apply: round_DN_UP_lt.
    case: Crnd1 => HC //.
      have rCxE : RND1 (C * x) = round beta fexp Ztrunc (C * x).
        by rewrite /RND1 /round HC.
      rewrite round_ZR_DN in rCxE; last by lra.
      by rewrite -rCxE -/g in CxB1; lra.
    have rCxE : RND1 (C * x) = round beta fexp Zfloor (C * x).
      by rewrite /RND1 /round HC.
    by rewrite -rCxE -/g in CxB1; lra.
  rewrite Rabs_pos_eq in e1B; last by lra.
  have xgBd : - pow (s + 1) - pow (s - p + 1) < x - g .
    have sxBd : pow (s - p + 1) - pow (s + 1) <= - pow s * x.
      have -> : (s - p + 1 = s + (- p + 1))%Z by lia.
      by rewrite bpow_plus [pow (s + 1)]bpow_plus -[pow 1]/2; nra.
    have xgBd1 : pow (s - p + 1) - pow (s + 1) - pow (s - p + 2) < x - g.
      by rewrite xgE; lra.
    suff : pow (s - p + 2) = 2 * pow (s - p + 1) by lra. 
    have -> : (s - p + 2 = (s - p + 1) + 1)%Z by lia.
    by rewrite bpow_plus -[pow 1]/2; lra.
  have ubsE : Ulp.pred beta fexp (- pow (s + 1)) = 
                    - (pow (s + 1) + pow (s - p + 2)) .
    rewrite pred_opp succ_eq_pos; last apply: bpow_ge_0.
    rewrite ulp_bpow /fexp.
    by congr (- (pow _ + pow _)); lia.
  have xgB1 : Ulp.pred beta fexp (- pow (s + 1)) < x - g <= - pow (s + 1).
    split; last by lra.
    have -> : Ulp.pred beta fexp (- pow (s + 1)) =
                - (pow (s + 1) + pow (s - p + 2)).
      rewrite pred_opp succ_eq_pos; last by apply: bpow_ge_0.
      rewrite ulp_bpow /fexp.
      by congr (- (pow _ + pow _)); lia.
    have sxBd : pow (s - p + 1) - pow (s + 1) <= - pow s * x.
      have -> : (s - p + 1 = s + (- p + 1))%Z by lia.
      by rewrite bpow_plus [pow (s + 1)]bpow_plus -[pow 1]/2; nra.
    suff : pow (s - p + 2) = 2 * pow (s - p + 1) by lra. 
    have -> : (s - p + 2 = (s - p + 1) + 1)%Z by lia.
    by rewrite bpow_plus -[pow 1]/2; lra.
  have -> : d = round beta fexp Zceil (x - g).
    by rewrite /d /round -Hrnd1.
  rewrite (round_UP_eq _ _ _ _ _ xgB1) //.
  apply/generic_format_opp/generic_format_bpow.
  by rewrite /fexp; lia.
have dBu : Rabs d <= pow (s + 1).
  rewrite /d Rabs_left1; last first.
    have <- : RND1 0 = 0 by apply: round_0.
    by apply: round_le; lra.
  suff : - pow (s + 1) <= RND1 (x - g) by lra.
  have [e1N|e1P] := Rle_lt_dec e1 0.
    by rewrite -rs1E; apply: round_le; lra.
  have [xgLp|pLxg] := Rle_lt_dec (x - g) (- pow (s + 1)).
    by rewrite -/d e1PxgB; lra.
  by rewrite -rs1E; apply: round_le; lra.
have dBd : pow s <= Rabs d.
  have [pE|pGt] : (p = 2%Z \/ 3 <= p)%Z by lia.
    have sE : s = 1%Z by lia.
    rewrite sE -[pow _]/2.
    case: (p2C pE); case => _ []->; clear; split_Rabs; lra.
  rewrite /d Rabs_left1; last first.
    have <- : RND1 0 = 0 by apply: round_0.
    by apply: round_le; lra.
  suff : RND1 (x - g) <= - pow s by lra.
  have [xE|xD] := Req_dec x (1 + pow (-p  + 1)); last first.
    have xB2 : 1 + pow (- p + 2) <= x.
      have succ1E : succ beta fexp 1 = 1 + pow (- p + 1).
        rewrite succ_eq_pos; last by lra.
        by rewrite -[ulp 1]/(ulp (pow 0)) ulp_bpow /fexp; congr (_ + pow _); lia.
      suff <- : succ beta fexp (1 + pow (- p + 1)) = 1 + pow (- p + 2).
        apply: succ_le_lt => //; last by lra.
        rewrite -succ1E; apply: generic_format_succ => //.
        rewrite -[1]/(pow 0).
        by apply: generic_format_bpow; rewrite /fexp; lia.
      rewrite succ_eq_pos; last by lra.
      rewrite ulp_neq_0 /ce /fexp; last by lra.
      rewrite (mag_unique_pos beta _ 1).
        have -> : (- p + 2 = - p + 1 + 1)%Z by lia.
        by rewrite !bpow_plus -[pow 1]/2; lra.
      rewrite -[pow (1 - 1)]/1 -[pow 1]/2.
      suff : 0 <= pow (- p + 1) < pow 0 by rewrite -[pow 0]/1; lra.
      split; first by lra.
      by apply: bpow_lt; lia.
    have <- : RND1 (- pow s) = - pow s.
      apply/round_generic/generic_format_opp/generic_format_bpow.
      by rewrite /fexp; lia.
    apply: round_le.
    rewrite xgE.
    have {2}-> : - pow s = - pow s * (1 + pow (- p + 2)) + pow (s - p + 2).
      by rewrite !bpow_plus; lra.
    apply: Rplus_le_compat; last by clear -e1B ps1pP; split_Rabs; lra.
    by nra.
  have [HC | HNC]: (forall x : R, rnd1 x = Zceil x) \/ 
        ((forall x : R, rnd1 x = Ztrunc x) \/ forall x : R, rnd1 x = Zfloor x).
  - by case: Crnd1; [right; left| right; right|left].
  - have e1P : 0 <= e1.
      suff : C * x <= RND1 (C * x) by rewrite /e1 /g; lra.
      have -> : RND1 (C * x) = round beta fexp Zceil (C * x).
        by rewrite /RND1 /round HC.
      have [CxF|CxNF] // := generic_format_EM beta fexp (C * x).
        by rewrite round_generic //; lra. 
      have CxB1 : round beta fexp Zfloor (C * x) < C * x < 
                  round beta fexp Zceil (C * x).
          by apply: round_DN_UP_lt.
      by lra.
    have <- : RND1 (- pow s) = - pow s.
      apply/round_generic/generic_format_opp/generic_format_bpow.
      by rewrite /fexp; lia.
    apply: round_le.
    by rewrite xgE; nra.
  have gE1 : g = round beta fexp Zfloor (C * x).
    case: HNC => HNC;  last by rewrite /g /RND1 /round HNC.
    rewrite -round_ZR_DN; last by lra.
    by rewrite /g /RND1 /round HNC.
  suff -> : g = pow s + 1 + pow (s - p + 1).
    have <- : RND1 (- pow s) = - pow s.
      apply/round_generic/generic_format_opp/generic_format_bpow.
      by rewrite /fexp; lia.
    apply: round_le.
    suff : pow (- p + 1) <= pow (s - p + 1) by rewrite xE; lra.
    by apply: bpow_le; lia.
  pose gf := (Float beta (2 ^ (p - 1) + 2 ^ (p - s - 1) + 1) (s - p + 1)).
  have gfE : pow s + 1 + pow (s - p + 1) = F2R gf.  
    rewrite /F2R /= !plus_IZR !(IZR_Zpower beta); try lia.
    rewrite !Rmult_plus_distr_r -!bpow_plus Rsimp01 -[1]/(pow 0).
    by congr (pow _ + pow _ + pow _); lia.
  have gfF : format (F2R gf).
    apply: generic_format_FLX.
    apply: (FLX_spec beta p _ gf) => //=.
    rewrite /= Z.abs_eq; last by lia.
    have -> : (2 ^ p = 2 * 2 ^ (p - 1))%Z.
      by rewrite -(Zpower_plus 2 1); try congr (2 ^  _)%Z; lia.
    suff : (1 + 2 ^ (p - s - 1) < 2 ^ (p - 1))%Z by lia.
    have -> : (2 ^ (p - 1) = 2 * 2 ^ (p - 2))%Z.
      by rewrite -(Zpower_plus 2 1); try congr (2 ^  _)%Z; lia.
    have : (1 < 2 ^ (p -2))%Z by apply (Zpower_lt beta 0); lia.
    have : (2 ^ (p -  s - 1) <= 2 ^ (p -2))%Z by apply (Zpower_le beta); lia.
    by lia.
  rewrite gE1; apply: round_DN_eq => //.
    by rewrite gfE.
  rewrite xE /C; split.
    suff : pow (s - p + 1) <= pow s * pow (- p + 1) by lra.
    rewrite -bpow_plus.
    have -> : (s + (- p + 1) = s - p + 1)%Z by lia.
    by lra.
  rewrite succ_eq_pos; last by lra.
  suff : pow s * pow (- p + 1) + pow (- p + 1) <
        pow (s - p + 1) + ulp (pow s + 1 + pow (s - p + 1)) by lra.
  suff : pow (- p + 1) <  ulp (pow s + 1 + pow (s - p + 1)).
    rewrite -bpow_plus.
    have -> : (s + (- p + 1) = s - p + 1)%Z by lia.
    by lra.
  rewrite [X in ulp X]gfE ulp_neq_0 //; last first.
    by rewrite -gfE; lra.
  apply: bpow_lt.
  rewrite /cexp /fexp; suff : (1 < mag beta (F2R gf))%Z by lia.
  rewrite (mag_unique_pos beta _ (s + 1)); first by lia.
  rewrite -gfE.
  have -> : (s + 1 - 1 = s)%Z by lia.
  split; first by lra.
  suff : 1 + pow (s - p + 1) < pow s by rewrite !bpow_plus -[pow 1]/2; lra.
  have -> : pow s = 2 * pow (s - 1).
    by rewrite -(bpow_plus beta 1); congr (pow _); lia.
  have : 1 <= pow (s - 1) by apply: (bpow_le _ 0); lia.
  have : pow (s - p + 1) < pow (s - 1) by apply: bpow_lt; lia.
  by lra.
have dM : is_imul d (pow (s - p + 1)).
  apply/is_abs_imul/is_imul_pow_le_pow => //.
  by apply/generic_format_abs/generic_format_round.
have e2B : Rabs e2 < pow (s - p + 1).
  have [xgEp|xgNEp] := Req_dec (x - g) (- (pow (s + 1))).
    rewrite /e2 /d xgEp /RND1 round_generic; last first.
      by apply/generic_format_opp/generic_format_bpow; rewrite /fexp; lia.
    by rewrite !Rsimp01; apply: bpow_gt_0.
  have [e1N|e1P] := Rle_lt_dec e1 0.
    apply: Rlt_le_trans (_ : ulp (x - g) <= _).
      apply: error_lt_ulp; first by lra.
    have -> : (s - p + 1 = s + 1 - p)%Z by lia.
    apply: bpow_lt_ulp.
    by rewrite Rabs_left1; lra.
  have [xgLp|pLxg] := Rle_lt_dec (x - g) (- pow (s + 1)).
    rewrite /e2 e1PxgB // Rabs_pos_eq; last by lra.
    by clear -xgB; split_Rabs; lra.
  apply: Rlt_le_trans (_ : ulp (x - g) <= _).
    by apply: error_lt_ulp; lra.
  have -> : (s - p + 1 = s + 1 - p)%Z by lia.
  by apply: bpow_lt_ulp; rewrite Rabs_left1; lra.
have dLgB : - d <= g <= 2 * - d.
  split.
    suff : 0 <= x + e2 by rewrite e2E e1E; lra.
    apply: Rle_trans (_ : 1  + pow (- p + 1) - pow (s - p + 1) <= _); last first.
      by clear - e2B xB1; split_Rabs; lra.
    have : 0 < pow (- p + 1) by apply: bpow_gt_0.
    suff : pow (s - p + 1) <= 1 by lra.
    by apply: (bpow_le _ _ 0); lia.
  suff : g + 2 * d <= 0 by lra.
  have [pE2|pE3|pG4] : [\/ p = 2%Z, p = 3%Z | (4 <= p)%Z].
  - have [?|[?|?]]: (p = 2%Z \/ p = 3%Z \/ 4 <= p)%Z by lia.
    - by apply: Or31.
    - by apply: Or32.
    by apply: Or33.
  - by case p2C => //; case=> -> []->; lra.
  - case p3C => //.
    - by case=> _; case; do 2 case => ->; lra.
    - by case=> _; case; case => ->; lra.
    by case=> _; case; do 2 case => ->; lra.    
  have -> : g + 2 * d = - pow s * x + x - e1 + 2 * e2.
    by rewrite e2E e1E; lra.
  have [sE1|sNE1] := Z.eq_dec s 1.
    suff : - x - e1 + 2 * e2 <= 0 by rewrite sE1 -[pow 1]/2; lra.
    have sp1E : (s - p + 1 = 2 - p)%Z by lia.
    have sp2E : (s - p + 2 = 3 - p)%Z by lia.
    rewrite sp2E in e1B; rewrite sp1E in e2B.
    apply: Rle_trans (_ : -x + pow (4 - p) <= _).
      have -> : pow (4 - p) = pow (3 - p) + 2 * pow (2 - p).
        have -> : (4 - p = 1 + (3 - p))%Z by lia.
        have -> : (3 - p = 1 + (2 - p))%Z by lia.
        by rewrite !bpow_plus -[pow 1]/2; lra.
      rewrite -Rplus_assoc; repeat apply: Rplus_le_compat; first by lra.
      - by clear -e1B;split_Rabs; lra.
      by clear -e2B; split_Rabs; lra.  
    suff : pow (4 - p) <= 1 by lra.
    by apply: (bpow_le radix2 _ 0); lia.
  have [sE2|sNE2] := Z.eq_dec s (p - 1)%Z.
    apply: Rle_trans (_ : - 4 * x + pow (s - p + 2) + 2 * pow (s - p + 1) <= _).
      repeat apply: Rplus_le_compat.
      - suff :  4 * x <= (pow s - 1) * x by lra.
        apply: Rmult_le_compat_r; first by lra.
        suff : 8 <= pow s by lra.
        by apply: (bpow_le beta 3); lia.
      - by clear -e1B; split_Rabs; lra.
      by clear -e2B; split_Rabs; lra.
    have -> :  pow (s - p + 2) = 2 * pow (s - p + 1).
      by rewrite -(bpow_plus beta 1); congr (pow _); lia.
    suff : pow (s - p + 1) <= 1 by lra.
    by apply: (bpow_le radix2 _ 0); lia.
  apply: Rle_trans (_ : - 3 * x + pow (s - p + 2) + 2 * pow (s - p + 1) <= _).
    repeat apply: Rplus_le_compat.
    - suff :  3 * x <= (pow s - 1) * x by lra.
      apply: Rmult_le_compat_r; first by lra.
      suff : 4 <= pow s by lra.
      by apply: (bpow_le beta 2); lia.
    - by clear -e1B; split_Rabs; lra.
    by clear -e2B; split_Rabs; lra.
  have <- :  pow (s - p + 2) = 2 * pow (s - p + 1).
    by rewrite -(bpow_plus beta 1); congr (pow _); lia.
  suff : pow (s - p + 2) <= 1 by lra.
  by apply: (bpow_le radix2 _ 0); lia.
pose xh := RND1 (g + d).
have xhE : xh = g + d.
  apply: round_generic.
  have -> : g + d = g - (- d) by lra.
  apply: sterbenz; first by apply: generic_format_round.
    by apply/generic_format_opp/generic_format_round.
  by lra.
have xhP : 0 <= xh.
  have <- : RND1 0 = 0 by apply: round_0.
  by apply: round_le; lra.
have xhM : is_imul xh (pow (s - p + 1)).
  by apply/is_imul_pow_round/is_imul_add.
have xhBu : xh <= 2.
  have xhBu : xh < 2 + pow (s - p + 1).
    have -> : xh = x + e2 by rewrite xhE e2E; lra.
    by clear -xB e2B; split_Rabs; lra.
  case: xhM => z Hz; rewrite Hz in xhBu *.
  have -> : 2 = IZR (2 ^ (p - s)) * pow (s - p + 1).
    rewrite (IZR_Zpower beta); last by lia.
    by rewrite -bpow_plus -[2]/(pow 1); congr (pow _); lia.
  have [/IZR_le zLps|/IZR_le psLz] :
    (z <= 2 ^ (p - s) \/ (2 ^ (p - s) + 1 <= z))%Z by lia.
    by clear -zLps ps1pP; nra.
  suff : 2 + pow (s - p + 1) <= IZR z * pow (s - p + 1) by lra.
  have -> : 2 = IZR (2 ^ (p - s)) * pow (s - p + 1).
    rewrite (IZR_Zpower beta); last by lia.
    by rewrite -bpow_plus -[2]/(pow 1); congr (pow _); lia.
  rewrite plus_IZR in psLz.
  by clear -psLz ps1pP; nra.
have xhE2 : xh = x + e2 by lra.
pose xl := RND1 (x - xh).
have xlM : is_imul xl (pow (- p + 1)).
  apply/is_imul_pow_round/is_imul_sub => //.
    have -> : (- p + 1 = 0 - p + 1)%Z by lia.
    apply: is_imul_pow_le_pow => //.
    by rewrite -[pow _]/1; lra.
  by apply: is_imul_pow_le xhM _; lia.
have xlE : xl = x - xh.
  apply: round_generic.
  have -> : x - xh = - (xh - x) by lra.
  apply/generic_format_opp/sterbenz => //; first by apply: generic_format_round.
  suff : 1 <= xh by lra.
  have -> : 1 =  pow (- (s - p + 1)) * pow (s - p + 1).
    by rewrite -bpow_plus -[1]/(pow 0); congr (pow _); lia.
  case: xhM => z zE.
  rewrite zE; apply: Rmult_le_compat_r; first by apply: bpow_ge_0.
  have [zLp|pLz]: 
      (z <= (2 ^ (- (s - p + 1)))- 1)%Z \/ (2 ^ (- (s - p + 1)) <= z)%Z.
  - by lia.
  - suff : xh <= 1 - pow (s - p + 1) by clear -e2B xhE2 xB; split_Rabs; lra.
    rewrite zE.
    suff :  IZR (z + 1) * (pow (s - p + 1)) <= 1 by rewrite plus_IZR; lra.
    have <- : pow (- (s - p + 1)) * pow (s - p + 1) = 1.
      by rewrite -bpow_plus -[1]/(pow 0); congr (pow _); lia.
    apply: Rmult_le_compat_r; first by lra.
    rewrite -IZR_Zpower // /beta /=; last by lia.
    by apply/IZR_le; lia.
  rewrite -IZR_Zpower; last by lia.
  by apply: IZR_le.
rewrite /= -/C -/RND1 -/d -/g -/xh -/x -/xl; split; first by lra.
  have [->|xhN2] := Req_dec xh 2.
    by apply: (fit_in_pow 1); apply/ltP; lia.
  exists (s - p + 1)%Z; split => // => _.
  rewrite Z2Nat.id; last by lia.
  have -> : (p - s + (s - p + 1) = 1)%Z by lia.
  by rewrite -[pow _]/2; clear -xhP xhBu xhN2; split_Rabs; lra.
exists (- p + 1)%Z; split => // => _.
rewrite Z2Nat.id; last by lia.
have -> : (s + (- p + 1)  = s - p + 1)%Z by lia.
suff -> : xl = - e2 by rewrite Rabs_Ropp; lra.
lra.
Qed.

End Main.





