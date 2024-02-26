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
  (forall x, round beta fexp rnd (- x) = - round beta fexp rnd x) -> 
  split fexp rnd (- x) s = opp_DWR (split fexp rnd x s).
Proof.
move=> oppR; rewrite /Rminus /split.
have -> : (bpow beta s + 1) * - x = - ((bpow beta s + 1) * x) by lra.
by rewrite /Rminus !(oppR, =^~ Ropp_plus_distr).
Qed.

Lemma split_ZR_opp fexp x s : 
  split fexp Ztrunc (- x) s = opp_DWR (split fexp Ztrunc x s).  
Proof. by apply/split_opp/round_ZR_opp. Qed.

Lemma split_AW_opp fexp x s : 
  split fexp Zaway (- x) s = opp_DWR (split fexp Zaway x s).  
Proof. by apply/split_opp/round_AW_opp. Qed.

Lemma split_UP_opp fexp x s : 
  split fexp Zceil (- x) s = opp_DWR (split fexp Zfloor x s).  
Proof.
rewrite /Rminus /split.
have -> : (bpow beta s + 1) * - x = - ((bpow beta s + 1) * x) by lra.
by rewrite /Rminus !(round_UP_opp, =^~ Ropp_plus_distr).
Qed.

Lemma split_DN_opp fexp x s : 
  split fexp Zfloor (- x) s = opp_DWR (split fexp Zceil x s).  
Proof. by rewrite -[in RHS](Ropp_involutive x) split_UP_opp opp_DWR_K. Qed.

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
Local Notation RND := (round beta fexp rnd).
Local Notation split := (split fexp rnd).

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

Hypothesis  basic_rnd : [\/ rnd = Ztrunc,
                            rnd = Zaway,
                            rnd = Zfloor | rnd = Zceil].
 
Lemma split_sum x s : let: DWR xh xl := split x s in x = xh + xl.
Proof.
move: rnd valid_rnd basic_rnd.
wlog : x / 0 < x => [IH rnd1 Vrnd1| xP rnd1 Vrnd1 Brnd1].
  have [->|xP|xN]: [\/ x = 0, 0 < x | x < 0].
  - case: (Rle_dec x 0) => ?; last by apply: Or32; lra.
    by case: (Req_dec x 0) => ?; [apply: Or31| apply: Or33; lra].
  - by rewrite split_0 //; lra.
  - by apply: IH.
  have xNN : 0 < - x by lra.
  case => rE; rewrite rE.
  - suff : let 'DWR xh xl := FLX_VD.split fexp Ztrunc (- x) s in - x = xh + xl.
      by rewrite split_ZR_opp; case: FLX_VD.split => /= xh xl; lra.
    by apply: IH => //; apply: Or41.
  - suff : let 'DWR xh xl := FLX_VD.split fexp Zaway (- x) s in - x = xh + xl.
      by rewrite split_AW_opp; case: FLX_VD.split => /= xh xl; lra.
    by apply: IH => //; apply: Or42.
  - suff : let 'DWR xh xl := FLX_VD.split fexp Zceil (- x) s in - x = xh + xl.
      by rewrite split_UP_opp; case: FLX_VD.split => /= xh xl; lra.
    by apply: IH => //; apply: Or44.
  suff : let 'DWR xh xl := FLX_VD.split fexp Zfloor (- x) s in - x = xh + xl.
    by rewrite split_DN_opp; case: FLX_VD.split => /= xh xl; lra.
  by apply: IH => //; apply: Or43.
Qed.

End Main.





