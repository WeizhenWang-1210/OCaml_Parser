type ('nonterminal, 'terminal) symbol =
  | N of 'nonterminal
  | T of 'terminal;;
(**takes in a hw1-styled grammar and convert to hw2-styles grammar*)

type ('nonterminal, 'terminal) parse_tree =
  | Node of 'nonterminal * ('nonterminal, 'terminal) parse_tree list
  | Leaf of 'terminal;;

(**q1 *)
let convert_grammar gram1 = 
    match gram1 with
    | (sexpr, rules) -> let rec get_m_rules lst =
                            match lst with
                            | [] -> [] (**if no rules for a non-terminal symbol, there shouldn't be anything in its alternative list *)
                            | first::rest -> (match first with
                                                | (lhs ,rhs) -> rhs::(get_m_rules rest)(**Append the rhs of a rule for a non-terminal symbol to a list of rhs.*)
                                                ) 
                        in
                        (sexpr, (fun input_symbol -> (get_m_rules (List.filter (fun (a,b) -> a = input_symbol) rules))));;(**Only  select the rules with lhs equal to the input_symbol*)
(**takes in root node, return a list of leafs from left to right *)




(**q2 *)
let parse_tree_leaves tree =
    (**Since pattern matching match for the same type, if we want to check for child nodes, we need to 
    input the root node as a list of node with count 1.*)
    let rec parse_tree_leaves_l tree_l =
        match tree_l with
        |[] -> []
        | first_node :: rst_node -> (match first_node with
                                    (**if we find a Node, we check for leafs in its child and append the result to the list of leafs which will be computed from other nodes of the same level*)
                                    |Node (_, childs) -> (parse_tree_leaves_l childs)@(parse_tree_leaves_l rst_node)
                                    (**if we find a leaf, we append this leaf to the result and moves on to the unchecked nodes*)
                                    |Leaf l -> (l::parse_tree_leaves_l rst_node))in
    parse_tree_leaves_l [tree] ;;





(**make_matcher takes in an a grammar and returns a matcher for the gram
    matcher takes in an acceptor and a frag and returns the result of calling the supplied acceptor on the suffix.
    A matcher can either return Some or None. *)
let rec make_a_matcher_from_rhss prodfunc sexpr altlist acceptor frag =
  match altlist with
  |[]->None(**We have tried out all possible rule in the altlist at a specific level and still no result*)
  |fst_rhs :: rst_rhs -> let result = make_a_matcher_from_syms prodfunc fst_rhs acceptor frag in
                          match result with 
                          |None -> make_a_matcher_from_rhss prodfunc sexpr rst_rhs acceptor frag (**if one possible rule failed at a specific level, we need can try others *)
                          |Some x -> Some x (**if this choice of rule return something, use it *)
and  make_a_matcher_from_syms prodfunc syms acceptor frag=
  match syms with
  | [] -> acceptor frag (**We've matched every symbol in a rule to an element in the frag *)
  | fst_sym::rst_sym ->
                        match fst_sym with
                        (**if the first symbol is non-terminal, it will have an altlist. We will need to try out all possible rules in its altlist *)
                        |N n -> let concatonated_matcher = make_a_matcher_from_syms prodfunc rst_sym acceptor in (**AND *)
                                make_a_matcher_from_rhss prodfunc n (prodfunc n) concatonated_matcher frag
                        (**if the first symbol is terminal, if it matches the first element in the frag then it's OK, we check the rest; else we fail *)
                        |T t -> match frag with
                                |[] -> None
                                |h::tail -> if h = t then (make_a_matcher_from_syms prodfunc rst_sym acceptor tail)
                                            else None;;



(**q3 *)
let rec make_matcher grammar =
  match grammar with
  |(sexpr, sprodfunc) -> let saltlist = sprodfunc sexpr in
                        (fun acceptor frag-> make_a_matcher_from_rhss sprodfunc sexpr saltlist acceptor frag);;






let parse_acceptor path fragment = match fragment with
	|[] -> Some path (**our path should exhaust the frament, else we don't have a path tree. *)
	|_ -> None;;


(**we add a path in order to record it *)
let rec try_a_tree prodfunc parent_sym altlist acceptor path frag = 
  match altlist with
  | []-> None (**at any level of the tree, if we tries out all the alternative next children, we have no place to go *)
  | fst_try_children :: rst_try_children -> let result_path = make_a_tree prodfunc fst_try_children acceptor (path@[(parent_sym, fst_try_children)]) frag in
                                            match result_path with
                                            |None -> try_a_tree prodfunc parent_sym rst_try_children acceptor path frag (**similar to matcher, if we can't generate a path using the first rule in altlist we try a new one *)
                                            |Some path -> Some path
and make_a_tree prodfunc child_sym_list acceptor path frag = 
  match child_sym_list with
  |[] -> acceptor path frag (**similar to matcher, if we've traversed down all symbols in the sym_list, we have a valid result *)
  |fst_child_sym :: rst_child_sym -> match fst_child_sym with
                            (**if we encounter a non-terminal, it will have an altlist. We need to try all possibilities *)
                            |N n-> let n_acceptor= make_a_tree prodfunc rst_child_sym acceptor in
                                   let n_altlist = prodfunc n in
                                   try_a_tree prodfunc n n_altlist n_acceptor path frag 
                            (**if we encounter a terminal, just check if it matches the first element in the frag. *)  
                            |T t-> match frag with
                                  |[] -> None
                                  |head::tail -> if head = t then make_a_tree prodfunc rst_child_sym acceptor path tail
                                           else None;;
      


let make_tree path_generator fragment =
    let path = path_generator fragment in
    match path with
    (**path can be some or None. if None then we can't have a parse tree, return None. If some, we should generate a parse tree
       according to the path *)
    |Some path ->
                  let rec build_tree path = 
                  match path with
                  |fst_step :: rst_step -> let parent_symbol = fst fst_step in
                                           let child_symbol_list = snd fst_step in
                                           let result = build_children rst_step child_symbol_list in (**build children will make a node list that is the tree starting from the child level *)
                                           let next_level_path = fst result in (**this is the path left without the rules we've used to generate the child *)
                                           let child_nodes = snd result in (**this is a list of node *)
                                          next_level_path, Node(parent_symbol, child_nodes)
                  |[] -> [], Leaf("Not a path") (**this is an impossible case put here to get rid of the warning *)
              and build_children path child_symbol_list = 
                  match child_symbol_list with
                  |[] -> path, [] (**if we've build all child node, we are done *)
                  |fst_child_sym :: rst_child_sym -> match fst_child_sym with
                                                    (**if the fisrt child have non_terminal symbol, it is a node, it can have a subtree. We need to get its subtree. *)
                                                   |N n -> let fst_child_tree = build_tree path in
                                                           let path_remain = fst fst_child_tree in
                                                           let fst_child_node = snd fst_child_tree in
                                                           (**a node have siblings, we have to also find the subtrees of its siblings and appeend the nodes representing subtrees in a list *)
                                                           let same_level_nodes = build_children path_remain rst_child_sym in
                                                           let path_remain_remain = fst same_level_nodes in
                                                           let fst_child_siblings = snd same_level_nodes in
                                                           path_remain_remain, fst_child_node::fst_child_siblings
                                                           (**if a leaf, then we just need to find the corresponding subtress of its siblings. *)
                                                   |T t ->  let same_level_nodes = build_children path rst_child_sym in
                                                            let path_remain = fst same_level_nodes in
                                                            let siblings = snd same_level_nodes in
                                                            path_remain, (Leaf t)::siblings
                                                           in
                  (**build_tree's first element in its return tuple will be the path, the second element be  *)
                  Some (snd (build_tree path))         
    |_ -> None;;



(**q4 *)
let make_parser gram = 
        let prodfunc = snd gram in
        let start_symbol = fst gram in
        let start_altlist = prodfunc start_symbol in
        let path_generator = try_a_tree prodfunc start_symbol start_altlist parse_acceptor [] in
        make_tree path_generator;;
