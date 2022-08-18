let accept_all string = Some string

type my_nonterminals = 
  |Paragraph | Sentence | NPhrase | VPhrase | Noun | Verb | Adj | Adv
let my_grammar = 
  (Paragraph,
   function
   | Paragraph -> [(*[N Paragraph; N Sentence];*)[N Sentence];]
   | Sentence -> [[N NPhrase ; N VPhrase; N NPhrase; T "."]]
   | NPhrase -> [[N Noun]; [N Adj; N Noun]]
   | VPhrase -> [[N Verb]; [N Adv; N Verb]]
   | Noun -> [[T"I"];[T"you"];[T"Chocolate"];[T"coding"]]
   | Verb -> [[T"kick"];[T"drink"];[T"eat"];[T"twist"]]
   | Adj -> [[T"good"];[T"bad"];[T"perfect"];[T"mediocre"]]
   | Adv -> [[T"meh"];[T"forcefully"];[T"delightly"];[T"smoothly"]]
  )

let make_matcher_test =
  ((make_matcher my_grammar accept_all ["I"; "kick"; "coding"; "."; "good"; "chocolate"; "twist"; "you"; "."]) = Some ["good"; "chocolate";"twist"; "you"; "."])


let parser_frag = ["I";"twist";"coding"; "."]



let make_parser_test =
  match make_parser my_grammar parser_frag with
    | Some tree -> parse_tree_leaves tree = parser_frag
    | _ -> false