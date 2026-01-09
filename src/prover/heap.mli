
open Core.Syntax


val biab : hprop -> hprop -> hprop * hprop

val xpure : hprop -> prop

val split_sep_conj : hprop -> hprop list
