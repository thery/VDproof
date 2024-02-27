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

Theorem cexp_bpow_flx x e (xne0 : x <> R0) : ce (pow e * x) = (ce x + e)%Z.
Proof. by rewrite /cexp Rmult_comm mag_mult_bpow // /fexp; lia. Qed.

Theorem mant_bpow_flx x e : mant (pow e * x) = mant x.
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

Lemma split_scale x s t : split (pow t  * x) s = scale_DWR (pow t) (split x s).
Proof.
rewrite /split.
have -> : (pow s + 1) * (pow t * x) = pow t * ((pow s + 1) * x) by lra.
by rewrite !(round_bpow_flx, =^~ Rmult_minus_distr_l, =^~ Rmult_plus_distr_l).
Qed.

Lemma split_1 s :  (2 <= s <= p - 2)%Z -> split 1 s = DWR 1 0.
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

End IMUL.

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

Lemma split_sum x s :  
  format x -> (2 <= s <= p - 2)%Z -> let: DWR xh xl := split x s in x = xh + xl.
Proof.
move=> xF sB.
move: rnd valid_rnd.
wlog : x xF / 0 < x => [IH rnd1 Vrnd1| xP rnd1 Vrnd1].
  have [->|xP|xN]: [\/ x = 0, 0 < x | x < 0].
  - case: (Rle_dec x 0) => ?; last by apply: Or32; lra.
    by case: (Req_dec x 0) => ?; [apply: Or31| apply: Or33; lra].
  - by rewrite split_0 //; lra.
  - by apply: IH.
  have xNN : 0 < - x by lra.
  suff : let 'DWR xh xl := FLX_VD.split fexp (Zrnd_opp rnd1) (- x) s 
         in - x = xh + xl.
    by rewrite split_oppr; case: FLX_VD.split => /= xh xl; lra.
  by apply: IH => //; apply: generic_format_opp.
set splitv := FLX_VD.split fexp rnd1.
wlog : x xP xF / 1 <= x  < 2 => [IH | xB].
  suff : let 'DWR xh xl := splitv (pow (- (mag beta x - 1)) * x) s 
         in (pow (- (mag beta x - 1)) * x) = xh + xl.
    rewrite /splitv split_scale; case: FLX_VD.split => /= xh xl.
    set uu  := pow (- (mag beta x - 1)).
    suff : 0 < uu by nra.
    by apply: bpow_gt_0.
  apply: IH.
  - set uu  := pow (- (mag beta x - 1)).
    suff : 0 < uu by nra.
    by apply: bpow_gt_0.
  - by rewrite Rmult_comm; apply: mult_bpow_exact_FLX.
  have -> : 1 =  pow (- (mag beta x - 1)) * pow ((mag beta x - 1)).
    have -> : 1 = pow 0 by [].
    by rewrite -bpow_plus; congr bpow; lia.
  have -> : 2 =  pow (- (mag beta x - 1)) * pow (mag beta x).
    have -> : 2 = pow 1 by [].
    by rewrite -bpow_plus; congr bpow; lia.
  split.
    apply: Rmult_le_compat_l; first by apply: bpow_ge_0.
    rewrite -[X in _ <= X]Rabs_pos_eq; last by lra.
    by apply: bpow_mag_le; lra.
  apply: Rmult_lt_compat_l; first by apply: bpow_gt_0.
  rewrite -[X in X < _]Rabs_pos_eq; last by lra.
  by apply: bpow_mag_gt; lra.
have [->|x_neq_1]:= Req_dec x 1.
  by rewrite /splitv split_1 //; lra.
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
have xgE : x - g = - pow s * x - e1 by rewrite e1E /C; lra.
have xgB : Rabs (x - g) < pow (s + 1) + pow (s- p + 1).
  rewrite xgE.
  apply: Rle_lt_trans (_ : Rabs (pow s * x) + Rabs e1 < _); first by split_Rabs; lra.
  have -> : pow (s + 1) + pow (s - p + 1) =  
            pow s * (2 - pow (- p +1)) + pow (s- p + 2).
    have -> : (s - p + 1 = s + (- p + 1))%Z by lia.
    have -> : (s - p + 2 = 1 + s + (- p + 1))%Z by lia.
    by rewrite !bpow_plus -[pow 1]/2; lra.
  suff : Rabs (pow s * x) <= pow s * (2 - pow (- p + 1)) by lra.
  rewrite Rabs_mult !Rabs_pos_eq; try lra.
  apply: Rmult_le_compat_l; lra.
Qed.

End Main.





