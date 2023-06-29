open Variable;;
open Formula;;

type 'program nonterminal = { name : string; expansions : 'program list; strongest : ((variable * variable) list * formula) option }

val to_str : 'program nonterminal -> string
val expand : 'program nonterminal -> 'program list
