:- module(dancing_links, [compute_axioms/4, update_roots_axiom/4, update_roots_contraction/5]).

:- use_module(ordset, [ord_union/3,ord_insert/3,ord_member/2,ord_select/3]).
:- use_module(tree234, [btree_init/1,btree_get_replace/5,btree_insert/4,btree_to_list/2,btree_get/3]).
:- use_module(auxiliaries, [count_check/4]).

% =======================================
% =            Dancing links            =
% =======================================

% = compute most restricted axioms.

compute_axioms(Root, Graph, ATree, Axioms) :-
	btree_init(Tree0),
	compute_ancestors(Root, Graph, Tree0, Tree),
	collect_atoms(Graph, ATree),
	best_axiom(ATree, Tree, Axioms).

% get all atomic formulas from the graph

collect_atoms(Graph, Tree) :-
	btree_init(Tree0),
	collect_atoms(Graph, Tree0, Tree).

collect_atoms([], Tree, Tree).
collect_atoms([vertex(N, Atoms, _, _)|Rest], Tree0, Tree) :-
	collect_atoms1(Atoms, N, Tree0, Tree1),
	collect_atoms(Rest, Tree1, Tree).

collect_atoms1([], _, Tree, Tree).
collect_atoms1([A|As], N, Tree0, Tree) :-
	collect_atom(A, N, Tree0, Tree1),
	collect_atoms1(As, N, Tree1, Tree).

collect_atom(neg(Atom,Id1,Id2,_Sem,Vars), Num, Tree0, Tree) :-
    (
	btree_get_replace(Tree0, Atom, atoms(Ps,Ns), atoms(Ps,[tuple(Id1,Id2,Num,Vars)|Ns]), Tree)
    ->
	true
    ;
	btree_insert(Tree0, Atom, atoms([],[tuple(Id1,Id2,Num,Vars)]), Tree) 		 
    ).

collect_atom(pos(Atom,Id1,Id2,_Sem,Vars), Num, Tree0, Tree) :-
    (
	btree_get_replace(Tree0, Atom, atoms(Ps,Ns), atoms([tuple(Id1,Id2,Num,Vars)|Ps],Ns), Tree)
    ->
	true
    ;
	btree_insert(Tree0, Atom, atoms([tuple(Id1,Id2,Num,Vars)],[]), Tree) 		 
    ).


best_axiom(AtomTree, AncestorTree, Links) :-
	btree_to_list(AtomTree, List),
	best_axiom1(List, AncestorTree, Links).

best_axiom1(List, ATree, Links) :-
	best_axiom1(List, ATree, min, _Min, [], Links).

best_axiom1([], _, Min, Min, Links, Links).
best_axiom1([AtName-atoms(Pos, Neg)|Rest], ATree, Min0, Min, Links0, Links) :-
	/* count check */
	length(Pos, LP),
	length(Neg, LN),
	count_check(LN, LP, AtName, Rest),
	try_link_atoms(Pos, Neg, ATree, Min0, Min1, Links0, Links1),
	best_axiom1(Rest, ATree, Min1, Min, Links1, Links).


try_link_atoms(Ps, Ns, ATree, Min0, Min, Links) :-
	try_link_atoms(Ps, Ns, ATree, Min0, Min, [], Links).

try_link_atoms([], _, _, Min, Min, Links, Links).
try_link_atoms([P|Ps], Ns, ATree, Min0, Min, Links0, Links) :-
	try_link_atom(Ns, [], 0, P, ATree, Min0, Min1, Links0, Links1),
	try_link_atoms(Ps, Ns, ATree, Min1, Min, Links1, Links).

% we only need to keep track of the atoms with the *minimum* number of possible connections
% (all of them, to allow for addition and evaluation of tie-breakers later).
try_link_atom([], Options, NO, tuple(IdP1,IdP2,NumP,_), _, Min0, Min, Links0, Links) :-
  (	
	NO @< Min0
  ->
        /* new best choice, forget Min0 and Links0 */
        Min = NO,
	Links = [tuple(IdP1,IdP2,NumP,Options)] 
  ;		  
	NO == Min0
  ->
        /* same as best choice, remember for future tie-breaker */
        Min = Min0,
	Links = [tuple(IdP1,IdP2,NumP,Options)|Links0]  
  ;
        /* worse than other choices, forget Options */
        Min = Min0,
        Links = Links0
  ).			 
try_link_atom([tuple(IdN1,IdN2,NumN,VarsN)|Ns], Options0, NO0, tuple(IdP1,IdP2,NumP,VarsP), ATree, Min0, Min, Links0, Links) :-
	btree_get(ATree, NumN, AncN),
	btree_get(ATree, NumP, AncP),
  (
	unifiable(VarsN, VarsP, _Unifier),
        \+ ord_member(NumP, AncN),
        \+ ord_member(NumN, AncP)
  ->
        /* possible axiom link, add to options */
	Options = [tuple(IdN1,IdN2,NumN)|Options0],
        NO is NO0 + 1
  ;	  
        Options = Options0,
        NO = NO0
  ),
        try_link_atom(Ns, Options, NO, tuple(IdP1,IdP2,NumP,VarsP), ATree, Min0, Min, Links0, Links).

% =======================================
% =         Ancestor predicates         =
% =======================================

% compute for each node in the graph the set of its ancestors.
% NOTE: we presuppose acyclicity throughout!

compute_ancestors(Roots, Graph, Tree0, Tree) :-
	compute_ancestors(Roots, Graph, [], _, Tree0, Tree).

compute_ancestors([], _, Visited, Visited, Tree, Tree).
compute_ancestors([A|As], Graph, Visited0, Visited, Tree0, Tree) :-
	btree_insert(Tree0, A, [A], Tree1),
	ord_insert(Visited0, A, Visited1),
	visit(A, Graph, [A], Visited1, Visited2, Tree1, Tree2),
        compute_ancestors(As, Graph, Visited2, Visited, Tree2, Tree).

% = visit(+Vertex, +Graph, ?Ancestors, +Visited).

visit(N, Graph, Anc, V0, V, Tree0, Tree) :-
	graph_get(N, Graph, Edges),
	next_edges(Edges, Next0, []),
	sort(Next0, Next1),
	/* for cross edges, add the current ancestors */
	ord_intersect(Next1, V0, Cross),
	update_cross(Cross, Anc, Tree0, Tree1),
	/* remove already visited nodes */
	ord_subtract(Next1, V0, Next),
	visit_next(Next, Graph, Anc, V0, V, Tree1, Tree).

visit_next([], _, _, V, V, Tree, Tree).
visit_next([N|Ns], G, Anc0, V0, V, Tree0, Tree) :-
	ord_insert(Anc0, N, Anc),
	ord_insert(V0, N, V1),
   (
	ord_member(N, V0)
   ->
	update_cross1(N, Anc, Tree0, Tree1)
   ;			
        btree_insert(Tree0, N, Anc, Tree1)
   ),
	visit(N, G, Anc, V1, V2, Tree1, Tree2),
	visit_next(Ns, G, Anc0, V2, V, Tree2, Tree).

update_cross([], _, Tree, Tree).
update_cross([C|Cs], Anc, Tree0, Tree) :-
	update_cross1(C, Anc, Tree0, Tree1),
	update_cross(Cs, Anc, Tree1, Tree).
update_cross1(C, Anc, Tree0, Tree) :-
	btree_get_replace(Tree0, C, As0, As, Tree),
	ord_union(Anc, As0, As).	


next_edges([], N, N).
next_edges([P|Ps], N0, N) :-
	next_par(P, N0, N1),
	next_edges(Ps, N1, N).

next_par(par(X,Y), [X,Y|Ns], Ns).
next_par(univ(_,X), [X|Ns], Ns).

graph_get(N, Graph, Ps) :-
	  memberchk(vertex(N, _, _, Ps), Graph).


% update_roots

update_roots_axiom(Roots0, N0, N1, Roots) :-
   (
	/* delete N0 if it is a root */	
        ord_select(N0, Roots0, Roots1)
   ->
        Bool = 1
   ;
        Roots1 = Roots0, Bool = 0
   ),
         /* delete N1 only when N0 wasn't a root */
   (     Bool =:= 0, ord_select(N1, Roots1, Roots)
   ->
	true
   ;		   
        Roots = Roots1
   ).

update_roots_contraction(Roots0, Graph, N0, N1, Roots) :-
   (
        ord_select(N0, Roots0, Roots1)
   ->
    /* N1 does not necessarily become a root when N0 was, verify there are no other paths */
        (is_root(Graph,N1) -> ord_insert(Roots1, N1, Roots) ; Roots = Roots1)
   ;
        Roots = Roots0
   ).

is_root([], _).
is_root([vertex(_, _, _, Ps)|Rest], N) :-
	next_edges(Ps, Next, []),
	\+ member(N, Next),
	is_root(Rest, N).