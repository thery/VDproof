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
by rewrite /Rminus !(oppR, (fun x y => sym_equal (Ropp_plus_distr x y))).
Qed.

End Main.





