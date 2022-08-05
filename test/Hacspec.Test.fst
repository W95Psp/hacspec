module Hacspec.Test

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

noeq type a_t =
| Bar_a_t : a_t

