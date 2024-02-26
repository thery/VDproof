(* Formalisation of the Veltkamp/Dekker Algorithms with Directed Roundings *)

(* Copyright (c)  Inria. All rights reserved. *)
Require Import Reals  Psatz.
From Flocq Require Import Core Plus_error Mult_error Relative Sterbenz Operations.
From Flocq Require Import  Round.
Require Import mathcomp.ssreflect.ssreflect Rmore.

Set Implicit Arguments.

Section Main.
Definition  beta:= radix2.
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

Inductive dwR := DWR (xh : R) (xl : R).

Definition opp_DWR (d : dwR) := 
 let: DWR xh xl := d in DWR (- xh) (- xl).

Definition scale_DWR (s : R) (d : dwR) := 
 let: DWR xh xl := d in DWR (s * xh) (s * xl).

Open Scope R_scope.

Definition split (x : R) (s : Z) :=
  let C := pow s  + 1 in 
  let g := RND (C * x) in 
  let d := RND (x - g) in 
  let xh := RND (g + d) in 
  let xl := RND (x - xh) in 
  DWR xh xl.

Lemma split_0 s : split 0 s = DWR 0 0.
Proof. by rewrite /split !(round_0, Rsimp01). Qed.

Lemma split_opp x s : 
  (forall x, RND (- x) = - RND x) -> split (- x) s = opp_DWR (split x s).
Proof.
move=> oppR; rewrite /Rminus /split.
have -> : (pow s + 1) * - x = - ((pow s + 1) * x) by lra.
by rewrite /Rminus !(oppR, =^~ Ropp_plus_distr).
Qed.

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

End Main.





