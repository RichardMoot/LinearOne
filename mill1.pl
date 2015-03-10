:- use_module(ordset, [ord_union/3,ord_insert/3,ord_delete/3,ord_member/2,ord_key_member/3,ord_key_insert/4,ord_select/3]).
:- use_module(portray_graph_tikz, [portray_graph/1,graph_header/0,graph_footer/1,latex_graph/1]).
:- use_module(translations, [translate_lambek/3,translate_displacement/3,translate_hybrid/6]).
:- use_module(latex, [latex_proof/1,proof_header/0,proof_footer/0,latex_semantics/1]).
:- use_module(sem_utils, [substitute_sem/3,reduce_sem/2]).
:- use_module(tree234, [btree_init/1,btree_insert/4,btree_get/3,btree_get_replace/5,btree_to_list/2]).
:- use_module(lexicon, [parse/2]).

:- dynamic '$PROOFS'/1, '$AXIOMS'/1.
:- dynamic node_formula/3.

generate_diagnostics(false).

portray(neg(F, X, L)) :-
	atom(F),
	Term =.. [F|L],
	format('-~p ~p',[Term,X]).
portray(pos(F, X, L)) :-
	atom(F),
	Term =.. [F|L],
	format('+~p ~p',[Term,X]).
portray(at(X, Vs)) :-
	atom(X),
	Term =.. [X|Vs],
	print(Term).
portray(at(X, I1, I2, Vs)) :-
	atom(X),
	Term =.. [X|Vs],
	format('~w{~w,~w}', [Term,I1,I2]).
portray(impl(A,B)) :-
	format('(~p -o ~p)', [A,B]).
portray(rule(N,A,B,Ps)) :-
	Ps \== [],
	format('rule(~p,~p,~p,...)', [N,A,B]).
portray(appl(appl(appl(F,Z),Y),X)) :-
	!,
	atom(F),
	!,
	Term =.. [F,X,Y,Z],
	print(Term).
portray(appl(appl(F,Y),X)) :-
	atom(F),
	!,
	Term =.. [F,X,Y],
	print(Term).
portray(appl(F,X)) :-
	atom(F),
	!,
	Term =.. [F,X],
	print(Term).
portray(appl(M,N)) :-
	format('(~p ~p)', [M,N]).
portray(lambda(X,M)) :-
        format('(~p^~p)', [X,M]).
portray(bool(P,B,Q)) :-
	format('(~p ~p ~p)', [P,B,Q]).



multi_prove(Antecedent, Goal) :-
	multi_prove(Antecedent, Goal, []).

multi_prove(Antecedent, Goal, LexSem) :-
        unfold_sequent(Antecedent, Goal, Roots, Vs0, _W, Sem0),
	/* keep a copy of the initial graph (before any unificiations) for later proof generation */
	copy_term(Vs0, Vs),
        prove1(Vs0, Roots, Trace),
	/* proof found */
	/* update proof statistics */
	'$PROOFS'(N0),
	N is N0 + 1,
	retractall('$PROOFS'(_)),
	assert('$PROOFS'(N)),
	/* generate semantics */
	substitute_sem(LexSem, Sem0, Sem1),
	reduce_sem(Sem1, Sem),
	format(user_error, '~NSemantics ~w: ~p~n', [N,Sem]),
	latex_semantics(Sem),
	/* generate a LaTeX proof */
	generate_proof(Vs, Trace).

% = compute most restricted axioms.

compute_axioms(Root, Graph, ATree, Axioms) :-
	btree_init(Tree0),
	compute_ancestors(Root, Graph, Tree0, Tree),
	collect_atoms(Graph, ATree),
	best_axiom(ATree, Tree, Axioms).

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
best_axiom1([_AtName-atoms(Pos, Neg)|Rest], ATree, Min0, Min, Links0, Links) :-
	/* count check */
	length(Pos, LP),
	length(Neg, LN),
	LN == LP,
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

% = prove(+Antecedent, +GoalFormula)

prove(Antecedent, Goal) :-
	prove(Antecedent, Goal, []).

prove(Antecedent, Goal, LexSem) :-
	initialisation,
	multi_prove(Antecedent, Goal, LexSem),
	fail.
prove(_, _, _) :-
	final_statistics.

initialisation :-
	/* LaTeX output */
	graph_header,
	proof_header,
	/* reset counters */
	retractall('$PROOFS'(_)),
	assert('$PROOFS'(0)),
	retractall('$AXIOMS'(_)),
	assert('$AXIOMS'(0)).

final_statistics :-
	/* print final statistics and generate pdf files */
	'$AXIOMS'(A),
	'$PROOFS'(N),
	write_axioms(A),
	write_proofs(N),
	/* LaTeX graphs */
	graph_footer(N),
	/* LaTeX proofs */
	proof_footer.


proof_diagnostics(Msg, P) :-
	proof_diagnostics(Msg, [], P).
proof_diagnostics(Msg, Vs, P) :-
   (
	generate_diagnostics(true)
    ->
	format(latex, Msg, Vs),
	latex_proof(P)
    ;
        true
    ).

generate_proof(Vs, Trace) :-
	node_proofs(Vs, Ps),
	combine_proofs(Trace, Ps, Proof),
	latex_proof(Proof).

combine_proofs([], [Proof], Proof).
combine_proofs([N0-par(N1)|Rest], Ps0, Proof) :-
	select(N0-P0, Ps0, Ps1),
	select(N1-P1, Ps1, Ps2),
	combine(P0, P1, N0, N1, P2),
	replace_proofs_labels([P2|Ps2], N0, N1, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([N0-univ(V,N1)|Rest], Ps0, Proof) :-
        select(N0-P0, Ps0, Ps1),
	select(N1-P1, Ps1, Ps2),
	combine_univ(P0, P1, N0, N1, V, P2),
	replace_proofs_labels([P2|Ps2], N0, N1, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([ax(N1,AtV1,AtO1,N0,AtV0,AtO0)|Rest], Ps0, Proof) :-
	select_pos_proof(Ps0, Ps1, AtV1, AtO1, DeltaP, A2, P2),
	proof_diagnostics('~NPos:~2n', P2),
	select_neg_proof(Ps1, Ps2, AtV0, AtO0, Gamma, A1, Delta, C, P1),
	proof_diagnostics('~NNeg:~2n', P1),
        append(Gamma, DeltaP, GDP1),
	append(GDP1, Delta, GDP),
	unify_atoms(A1, A2),
	trivial_cut_elimination(P1, P2, GDP, C, Rule),
	replace_proofs_labels([N0-Rule|Ps2], N1, N0, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([Next|_], CurrentProofs, Proof) :-
	/* dump all partial proofs in case of failure (useful for inspection) */
	format(user_error, '~N{Error: proof generation failed!}~nNext:~p~2n', [Next]),
	member(Proof, CurrentProofs).

trivial_cut_elimination(P1, P2, GDP, C, rule(Nm, GDP, C, R)) :-
        is_axiom(P1),
        !,
	rulename(P2, Nm),
        subproofs(P2, R).
trivial_cut_elimination(P1, P2, GDP, C, rule(Nm, GDP, C, R)) :-
        is_axiom(P2),
        !,
	rulename(P1, Nm),		    
        subproofs(P1, R).
trivial_cut_elimination(P1, P2, GDP, C, rule(cut, GDP, C, [P2,P1])).


subproofs(_-R, S) :-
        subproofs(R, S).
subproofs(rule(_,_,_,S), S).

rulename(_-R, N) :-
        rulename(R, N).
rulename(rule(N,_,_,_), N).


is_axiom(_-R) :-
        is_axiom(R).
is_axiom(rule(ax,_,_,_)).


combine_univ(P1, P2, N0, N1, V, N1-Rule) :-
        P1 = rule(Nm, Gamma, N0-exists(var(V),N1-A), _),
	P2 = rule(_, Delta0, C, _),
	!,
	%	rename_bound_variables(A, AA),
	A = AA,
	select_formula(AA, N1, Delta0, Delta),
	replace_formula(AA, N1, N1-exists(var(V),N1-AA), Delta0, Delta1),
	append(Gamma, Delta, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(el, GD, C, [P2])
   ;		  
        Rule = rule(cut, GD, C, [P1,rule(el, Delta1, C, [P2])])
   ).
combine_univ(P1, P2, _N0, N1, V, N1-Rule) :-
        P2 = rule(_, Gamma, A, _),
	P1 = rule(Nm, Delta, C, _),
%	rename_bound_variables(A, AA),
	A = AA,
	append(Delta0, [_-forall(var(V),AA)|Delta1], Delta),
	append(Delta0, Gamma, GD0),
	append(GD0, Delta1, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(fr,GD,N1-forall(var(V),N1-AA), [P2])
   ;		  
        Rule = rule(cut, GD, C, [P1,rule(fr,Gamma,N1-forall(var(V),N1-A), [P2])])
   ).
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(Nm, Gamma, N0-p(N1-A, N1-B), _),
        P2 = rule(_, Delta0, C, _),
	!,
%        rename_bound_variables(A, AA),
%	rename_bound_variables(B, BB),
	A = AA,
	B = BB,
	select_formula(BB, N1, Delta0, Delta1),
	select_formula(AA, N1, Delta1, Delta),
	replace_formula(AA, N1, N1-p(N1-AA,N1-BB), Delta1, Delta2),
	append(Gamma, Delta, GD),		  
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(pl, GD, C, [P2])
   ;		  
        Rule = rule(cut, GD, C, [P1,rule(pl, Delta2, C, [P2])])
   ).
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(Nm, Gamma, A, _),
	P2 = rule(_, Delta0, _B, _),
	append(Gamma0, [N0-impl(N1-C,N1-D)|Gamma1], Gamma),
	rename_bound_variables(C, CC),
	select_formula(CC, N1, Delta0, Delta),
	append(Gamma0, Delta, GD0),
	append(GD0, Gamma1, GD),
	/* don't create trivial cuts */
   (
	Nm = ax
   ->
        Rule = rule(ir, GD, A, [P2])
   ;		  
        Rule = rule(cut, GD, A, [P1,rule(ir, Delta, impl(N1-C,N1-D), [P2])])
   ).

/* I don't believe it's necessary to do replacements inside the subproofs Rs here */

replace_proofs_labels([], _, _, []).
replace_proofs_labels([R0|Rs0], X, Y, [R|Rs]) :-
	replace_proof_labels(R0, X, Y, R),
	replace_proofs_labels(Rs0, X, Y, Rs).

replace_proof_labels(N0-R0, X, Y, N-R) :-
	replace_item(N0, X, Y, N),
	replace_proof_labels(R0, X, Y, R).
replace_proof_labels(rule(N, As0, F0, Rs), X, Y, rule(N, As, F, Rs)) :-
	replace_antecedent_labels(As0, X, Y, As),
	replace_formula_labels(F0, X, Y, F).

replace_antecedent_labels([], _, _, []).
replace_antecedent_labels([A|As], X, Y, [B|Bs]) :-
	replace_formula_labels(A, X, Y, B),
	replace_antecedent_labels(As, X, Y, Bs).

replace_formula_labels(N0-F0, X, Y, N-F) :-
	replace_item(N0, X, Y, N),
	replace_formula_labels(F0, X, Y, F).
replace_formula_labels(at(A,B,C,D), _, _, at(A,B,C,D)).
replace_formula_labels(impl(A0,B0), X, Y, impl(A,B)) :-
	replace_formula_labels(A0, X, Y, A),
	replace_formula_labels(B0, X, Y, B).
replace_formula_labels(p(A0,B0), X, Y, p(A,B)) :-
	replace_formula_labels(A0, X, Y, A),
	replace_formula_labels(B0, X, Y, B).
replace_formula_labels(forall(V,A0), X, Y, forall(V,A)) :-
	replace_formula_labels(A0, X, Y, A).
replace_formula_labels(exists(V,A0), X, Y, exists(V,A)) :-
	replace_formula_labels(A0, X, Y, A).

unify_atoms(_-at(A, _, _, Vs), _-at(A, _, _, Vs)).

select_neg_proof([P|Ps], Ps, V, O, Gamma, A, Delta, C, Proof) :-
	select_neg_proof1(P, V, O, Gamma, A, Delta, C, Proof),
	!.
select_neg_proof([P|Ps], [P|Rs], V, O, Gamma, A, Delta, C, Proof) :-
	select_neg_proof(Ps, Rs, V, O, Gamma, A, Delta, C, Proof).

select_neg_proof1(_-P, V, O, Gamma, A, Delta, C, R) :-
	select_neg_proof1(P, V, O, Gamma, A, Delta, C, R).
select_neg_proof1(rule(Nm, GammaADelta, C, Ps), V, O, Gamma, A, Delta, C, rule(Nm, GammaADelta, C, Ps)) :-
	select_ant_formula(GammaADelta, V, O, Gamma, [], A, Delta).

select_pos_proof([P|Ps], Ps, V, O, Delta, A, Proof) :-
	select_pos_proof1(P, V, O, Delta, A, Proof),
	!.
select_pos_proof([P|Ps], [P|Rs], V, O, Delta, A, Proof) :-
	select_pos_proof(Ps, Rs, V, O, Delta, A, Proof).

select_pos_proof1(_-P, V, O, Delta, A, R) :-
	select_pos_proof1(P, V, O, Delta, A, R).
select_pos_proof1(rule(Nm, Delta, N-at(At,V,O,Vars), Rs), V, O, Delta, N-at(At,V,O,Vars), rule(Nm, Delta, N-at(At,V,O,Vars), Rs)).

select_ant_formula([N-at(At,V,O,Vars)|Delta], V, O, Gamma, Gamma, N-at(At,V,O,Vars), Delta) :-
	!.
select_ant_formula([G|Gs], V, O, [G|Gamma0], Gamma, A, Delta) :-
	select_ant_formula(Gs, V, O, Gamma0, Gamma, A, Delta).

	

node_proofs([V|Vs], [P|Ps]) :-
        node_proof1(V, P),
        node_proofs(Vs, Ps).
node_proofs([], []).

node_proof1(vertex(N0, As, _, _), N0-Proof) :-
        node_formula(N0, Pol, F),
        node_proof2(As, F, N0, Pol, Proof),
	proof_diagnostics('~w. ', [N0], Proof),	
	!.

node_proof2([], F, N, _, rule(ax, [N-F], N-F, [])).
node_proof2([A|As], F, N, Pol, Proof) :-
        node_proof3(Pol, [A|As], F, N, Proof).

node_proof3(pos, L, F, N, Proof) :-
        create_pos_proof(F, N, L, [], Proof).
node_proof3(neg, L, F, N, Proof) :-
        max_neg(F, MN0),
	rename_bound_variables(MN0, MN),
        create_neg_proof(F, N, L, [], MN, Proof).

max_neg(impl(_,_-F0), F) :-
	!,
	max_neg(F0, F).
max_neg(forall(_,_-F0), F) :-
	!,
	max_neg(F0, F).
max_neg(F, F).

create_pos_proof(N-A, L0, L, Proof) :-
	create_pos_proof(A, N, L0, L, Proof).

create_pos_proof(at(A,C,N,Vars), M, [pos(A,C,N,_,Vars)|L], L, rule(ax,[M-at(A,C,N,Vars)], M-at(A,C,N,Vars), [])) :-
	!.
create_pos_proof(exists(X,N-A), N, L0, L, rule(er, Gamma, N-exists(Y,N-A3), [ProofA])) :-
        !,
	/* rename to make sure bound variable isn't unified */
	rename_bound_variables(A, A2),
	rename_bound_variable(exists(X,N-A2), X, Y, exists(Y,N-A3)),
        create_pos_proof(A, N, L0, L, ProofA),
        ProofA = rule(_, Gamma, N-A2, _).
create_pos_proof(p(N-A,N-B), N, L0, L, rule(pr, GD, N-p(N-A,N-B), [P1,P2])) :-
        !,
        create_pos_proof(A, N, L0, L1, P1),
        create_pos_proof(B, N, L1, L, P2),
        P1 = rule(_, Gamma, _, _),
        P2 = rule(_, Delta, _, _),
        append(Gamma, Delta, GD).
% complex subformula
create_pos_proof(F, N, L, L, rule(ax, [N-F], N-F, [])).

create_neg_proof(N-A, L0, L, Neg, Proof) :-
	create_neg_proof(A, N, L0, L, Neg, Proof).
create_neg_proof(at(A,C,N,Vars), M, [neg(A,C,N,_,Vars)|L], L, at(A,C,N,Vars), rule(ax, [M-at(A,C,N,Vars)], M-at(A,C,N,Vars), [])) :-
        !.
create_neg_proof(impl(N-A,N-B), N, L0, L, Neg, rule(il, GD, N-Neg, [ProofA,ProofB])) :-
        !,
        create_neg_subproof(A, N, L0, L1, ProofA),
	create_neg_proof(B, N, L1, L, Neg, ProofB),
%	rename_bound_variables(A, A2),
	rename_bound_variables(B, B2),
	copy_term(B2, B3),
%	format(user_error, '~NB :~w~nB2: ~w~n', [B,B2]),
	ProofA = rule(_, Gamma, N-A3, _),
	ProofB = rule(_, Delta, _, _),
%	replace_list(B3, N, Delta0, _, Delta),
	select_formula(B, N, Delta, Delta_B),
	%	format(user_error, '~NB :~w~nB2: ~w~n', [B,B2]),
	% B2 can have instantiated forall, so use B3
	append(Gamma, [N-impl(N-A3,N-B3)|Delta_B], GD).
create_neg_proof(forall(X,N-A), N, L0, L, Neg, rule(fl, GammaP, C, [ProofA])) :-
        !,
	rename_bound_variables(A, A2),
        create_neg_proof(A, N, L0, L, Neg, ProofA),
        ProofA = rule(_, Gamma, C, _),
	/* rename to make sure bound variables aren't unified */
	replace_list(A2, N, Gamma, N-forall(Y,N-A3), GammaP),
	rename_bound_variable(forall(X,N-A2), X, Y, forall(Y,N-A3)).
create_neg_proof(F, N, L, L, _, rule(ax, [N-F], N-F, [])).

create_neg_subproof(at(A,C,N,Vars), M, [pos(A,C,N,_,Vars)|L], L, rule(ax, [M-at(A,C,N,Vars)], M-at(A,C,N,Vars), [])) :-
        !.
create_neg_subproof(p(N-A0,N-B0), N, L0, L, rule(pr, GD, N-p(N-A,N-B), [ProofA, ProofB])) :-
	!,
	rename_bound_variables(A0, A),
	rename_bound_variables(B0, B),
	create_neg_subproof(A, N, L0, L1, ProofA),
	create_neg_subproof(B, N, L1, L, ProofB),
	ProofA = rule(_, Gamma, _, _),
	ProofB = rule(_, Delta, _, _),
	append(Gamma, Delta, GD).
create_neg_subproof(exists(X,N-A), N, L0, L, rule(er, Gamma, N-exists(Y,N-A3), [ProofA])) :-
	!,
	rename_bound_variables(A, A2),
	rename_bound_variable(exists(X,N-A2), X, Y, exists(Y,N-A3)),
	create_neg_subproof(A, N, L0, L, ProofA),
	ProofA = rule(_, Gamma, N-A2, _).
create_neg_subproof(A0, N, L, L, rule(ax, [N-A], N-A, [])) :-
	rename_bound_variables(A0, A).


rename_bound_variable(N-F0, X, Y, N-F) :-
	rename_bound_variable(F0, X, Y, F).
rename_bound_variable(at(A,C,N,Vars0), X, Y, at(A,C,N,Vars)) :-
	rename_bound_var_list(Vars0, X, Y, Vars).
rename_bound_variable(forall(Z,A0), X, Y, forall(V,A)) :-
	rename_bound_var(Z, X, Y, V),
	rename_bound_variable(A0, X, Y, A).
rename_bound_variable(exists(Z,A0), X, Y, exists(V,A)) :-
	rename_bound_var(Z, X, Y, V),
	rename_bound_variable(A0, X, Y, A).
rename_bound_variable(impl(A0,B0), X, Y, impl(A,B)) :-
	rename_bound_variable(A0, X, Y, A),
	rename_bound_variable(B0, X, Y, B).
rename_bound_variable(p(A0,B0), X, Y, p(A,B)) :-
	rename_bound_variable(A0, X, Y, A),
	rename_bound_variable(B0, X, Y, B).


rename_bound_var_list([], _, _, []).
rename_bound_var_list([V|Vs], X, Y, [W|Ws]) :-
	rename_bound_var(V, X, Y, W),
	rename_bound_var_list(Vs, X, Y, Ws).

rename_bound_var(V, X, Y, W) :-
   (
	V == X 
   ->
	W = Y
   ;
	W = V
   ).

    
rename_bound_variables(F0, F) :-
	rename_bound_variables(F0, [], F).
rename_bound_variables(N-F0, Map, N-F) :-
	rename_bound_variables(F0, Map, F).
rename_bound_variables(at(A,C,N,Vars0), Map, at(A,C,N,Vars)) :-
	rename_bound_var_list(Vars0, Map, Vars).
rename_bound_variables(forall(Z,A0), Map0, forall(V,A)) :-
	ord_key_insert(Map0, Z, V, Map),
	rename_bound_variables(A0, Map, A).
rename_bound_variables(exists(Z,A0), Map0, exists(V,A)) :-
	ord_key_insert(Map0, Z, V, Map),
	rename_bound_variables(A0, Map, A).
rename_bound_variables(impl(A0,B0), Map, impl(A,B)) :-
	rename_bound_variables(A0, Map, A),
	rename_bound_variables(B0, Map, B).
rename_bound_variables(p(A0,B0), Map, p(A,B)) :-
	rename_bound_variables(A0, Map, A),
	rename_bound_variables(B0, Map, B).

rename_bound_var_list([], _, []).
rename_bound_var_list([V|Vs], Map, [W|Ws]) :-
	rename_bound_var(V, Map, W),
	rename_bound_var_list(Vs, Map, Ws).

rename_bound_var(V, Map, W) :-
   (
	ord_key_member(V, Map, W) 
   ->
	true
   ;
	W = V
   ).

print_list([]).
print_list([A|As]) :-
	format(user_error, '~p~n', [A]),
	print_list(As).

select_formula(F, N, L0, L) :-
%   (
%        F = at(_,_,_,_)
%   ->
%	select(F, L0, L)
%   ;
        select(N-F, L0, L),
%   ),
        !.

replace_formula(F0, N, F, L0, L) :-
   (
        F0 = at(_,_,_,_)
   ->
	select(F0, L0, F, L)
   ;
        select(N-F0, L0, F, L)
   ),
        !.


%replace_list(at(A,C,N,Vars), _, List0, R, List) :-
%	!,
%	replace_list(List0, at(A,C,N,Vars), R, List).
replace_list(F, N, List0, R, List) :-
	replace_list(List0, N-F, R, List). 
replace_list([], _, _, []).
replace_list([A|As], C, D, [B|Bs]) :-
    (
       A = C
    ->
       B = D
    ;
       B = A
    ),
       replace_list(As, C, D, Bs).


write_proofs(P) :-
   (
       P =:= 0
   ->
       format(user_output, 'No proofs found!~n', [])
   ;
       P =:= 1
   ->
       format(user_output, '1 proof found.~n', [])
   ;
       format(user_output, '~p proofs found.~n', [P])
   ).
write_axioms(A) :-
   (
       A =:= 0
   ->
       format(user_output, 'No axioms performed!~n', [])
   ;
       A =:= 1
   ->
       format(user_output, '1 axiom performed.~n', [])
   ;
       format(user_output, '~p axioms performed.~n', [A])
   ).


prove1([vertex(_, [], _, [])], _, []) :-
        format(user_error, '~N= Sequent proved!~n', []),
        !.
prove1(G0, Roots0, [ax(N0,AtV0,AtO0,N1,AtV1,AtO1)|Rest0]) :-
        portray_graph(G0),
	compute_axioms(Roots0, G0, _ATree, [tuple(AtV1,AtO1,N1,Choices)|_Axioms]),
        select(vertex(N1, [A|As0], FVs0, Ps0), G0, G1),
        select(pos(At,AtV1,AtO1,X,Vars), [A|As0], As),
	/* forced choice for positive atom */
	!,
	member(tuple(AtV0,AtO0,N0), Choices),
	select(vertex(N0, [B|Bs0], FVs1, Ps1), G1, G2),
	select(neg(At,AtV0,AtO0,X,Vars), [B|Bs0], Bs),
        \+ cyclic(Ps0, G2, N0),
        \+ cyclic(Ps1, G2, N1),
	'$AXIOMS'(Ax0),
	Ax is Ax0 + 1,
	retractall('$AXIOMS'(_)),
	assert('$AXIOMS'(Ax)),
	append(As, Bs, Cs),
	append(Ps0, Ps1, Ps),
	merge_fvs(FVs0, FVs1, FVs),
	replace(G2, N0, N1, G3),
	replace_pars(Ps, N0, N1, Rs),
	update_roots_axiom(Roots0, N0, N1, Roots1),
	G4 = [vertex(N1,Cs,FVs,Rs)|G3],
        portray_graph(G4),
	contract(G4, G, Rest0, Rest, Roots1, Roots),
	connected(G),
	prove1(G, Roots, Rest).
prove1(G1, _, _) :-
        format(user_error, '~N= Done!~n', []),
        portray_graph(G1),
        fail.

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

update_roots_contraction(Roots0, N0, N1, Roots) :-
   (
        ord_select(N0, Roots0, Roots1)
   ->
        ord_insert(Roots1, N1, Roots)
   ;
        Roots = Roots0
   ).

% test for cyclicity
% G2 contains unvisited nodes
% P contains paths from current node
% N is the node to reach for a cycle.

cyclic([P|_], G2, N) :-
    cyclic1(P, G2, N).
cyclic([_|Ps], G2, N) :-
    cyclic(Ps, G2, N).

cyclic1(par(M,P), G2, N) :-
    (
       N =:= M
    ;
       N =:= P
    ;
       select(vertex(M,_,_,Ps), G2, G3),
       cyclic(Ps, G3, N)
    ;
       P \== M,
       select(vertex(P,_,_,Ps), G2, G3),
       cyclic(Ps, G3, N)
    ).
cyclic1(univ(_,M), G2, N) :-
    (
       N =:= M
     ;
       select(vertex(M,_,_,Ps), G2, G3),
       cyclic(Ps, G3, N)
    ).        

% = connected(+Graph)
%
% true if Graph is connected or at least can be made connected
% by vertex identifications (corresponding to axioms)

connected([V|Vs]) :-
   (
       Vs = []
   ->
       /* a single-node graph is connected */
       true
   ;
       connected1([V|Vs])
   ).

connected1([]).
connected1([vertex(_,As,_,Ps)|Vs]) :-
    (
        As = []
    ->  /* in a multiple-node graph, if a node has no */
        /* atoms, it must have a link */
        Ps = [_|_]
    ;
        true
    ),
    connected1(Vs).

% merge two sets of free variables
% remove variables already instantiated (these have an integer value)
% we need to sort again (since variable instantiations/unifications may
% have changed term order)

merge_fvs(Vs0, Ws0, Zs) :-
    reduce_fvs(Vs0, Vs1),
    sort(Vs1, Vs),
    reduce_fvs(Ws0, Ws1),
    sort(Ws1, Ws),
    ord_union(Vs, Ws, Zs).

reduce_fvs([], []).
reduce_fvs([V|Vs], Ws) :-
    (
        integer(V)
    ->
        reduce_fvs(Vs, Ws)
    ;
        Ws = [V|Ws0],
        reduce_fvs(Vs, Ws0)
    ).

% = contract(+InGraph,-OutGraph)
%
% perform all valid contractions on InGraph producing OutGraph;
% these are Danos-style contractions, performed in a first-found
% search.

contract(G0, G, L0, L, R0, R) :-
        contract1(G0, G1, L0, L1, R0, R1),
        portray_graph(G1),
        !,
        contract(G1, G, L1, L, R1, R).
contract(G, G, L, L, R, R).

% par contraction
contract1(G0, [vertex(N1,Cs,FVs,Rs)|G], [N0-par(N1)|Rest], Rest, Roots0, Roots) :-
        select(vertex(N0, As, FVsA, Ps0), G0, G1),
        select(par(N1, N1), Ps0, Ps),
	select(vertex(N1, Bs, FVsB, Qs), G1, G2),
	\+ cyclic(Qs, G2, N0),
	!,
	append(As, Bs, Cs),
	append(Ps, Qs, Rs0),
	merge_fvs(FVsA, FVsB, FVs),
	replace_pars(Rs0, N0, N1, Rs),
	replace(G2, N0, N1, G),
        update_roots_contraction(Roots0, N0, N1, Roots).
% forall contraction
contract1(G0, [vertex(N1,Cs,FVs,Rs)|G], [N0-univ(U,N1)|Rest], Rest, Roots0, Roots) :-
        select(vertex(N0, As, FVsA, Ps0), G0, G1),
        select(univ(U, N1), Ps0, Ps),
	select(vertex(N1, Bs, FVsB, Qs), G1, G2),
	no_occurrences1(FVsA, U),
	no_occurrences(G2, U),
	!,
	append(As, Bs, Cs),
	append(Ps, Qs, Rs0),
	merge_fvs(FVsA, FVsB, FVs),
	replace_pars(Rs0, N0, N1, Rs),
	replace(G2, N0, N1, G),
        update_roots_contraction(Roots0, N0, N1, Roots).


% = no_occurrences(+Graph, +VarNum)
%
% walks through +Graph and checks that none of its vertices
% has the variable +VarNum in their list of free variables.

no_occurrences([], _).
no_occurrences([vertex(_, _, FVs, _)|Rest], U) :-
        no_occurrences1(FVs, U),
        no_occurrences(Rest, U).

no_occurrences1([], _).
no_occurrences1([V|Vs], U) :-
        var(U) \== V,
        no_occurrences1(Vs, U).


% = replace(+InGraph,+InNodeNum,+OutNodeNum,+Outgraph)
%
% renumbers InNode for OutNode throughout Graph.

replace([], _, _, []).
replace([vertex(N,As,FVs,Ps0)|Rest0], N0, N1, [vertex(N,As,FVs,Ps)|Rest]) :-
        replace_pars(Ps0, N0, N1, Ps),
        replace(Rest0, N0, N1, Rest).

replace_pars([], _, _, []).
replace_pars([P0|Ps0], N0, N1, [P|Ps]) :-
        replace_par(P0, N0, N1, P),
        replace_pars(Ps0, N0, N1, Ps).

replace_par(par(X,Y), N0, N1, par(V,W)) :-
        replace_item(X, N0, N1, V),
        replace_item(Y, N0, N1, W).
replace_par(univ(M,X), N0, N1, univ(M,Y)) :-
        replace_item(X, N0, N1, Y).

replace_item(X, N0, N1, Y) :-
    (
	X = N0
    ->
	Y = N1
    ;
        Y = X
    ).

% = unfolding
%
% transforms sequents, antecedents and (polarized) formulas into graphs

unfold_sequent(List, Goal, Roots, Vs0, W, Sem) :-
        retractall(node_formula(_,_,_)),
	unfold_antecedent(List, 0, W, 0, N0, 0, M, Roots0, Vs0, [vertex(N0,As,FVsG,Es)|Vs1]),
	N is N0 + 1,
	append(Roots0, [N0], Roots),
	number_subformulas_pos(Goal, N0, N, _, _-NGoal),
        assert(node_formula(N0, pos, NGoal)),
	free_vars_p(Goal, FVsG),
	unfold_pos(NGoal, Sem, M, _, As, [], Es, [], Vs1, []).

unfold_antecedent([], W, W, N, N, M, M, [], Vs, Vs).
unfold_antecedent([F|Fs], W0, W, N0, N, M0, M, [N0|Rs], [vertex(N0,As,FVsF,Es)|Vs0], Vs) :-
        N1 is N0 + 1,
        W1 is W0 + 1,
	free_vars_n(F, FVsF),
	number_subformulas_neg(F, N0, N1, N2, _-NF),
        assert(node_formula(N0, neg, NF)),
	unfold_neg(NF, '$VAR'(W0), M0, M1, As, [], Es, [], Vs0, Vs1),
	unfold_antecedent(Fs, W1, W, N2, N, M1, M, Rs, Vs1, Vs).

% = number_subformulas_neg(+Formula, +CurrentNodeNumber, +NextNodeNumberIn, -NextNodeNumberOut, -NumberFormula)
%
% assigns node numbers to all subformulas of Formula, allowing us to designate
% all (sub-)formula occurrences in a sequent by a unique node number, and in the
% case of atomic formulas a combination of node-index (where index is a
% left-to-right numbering of the atomic subformulas at a node).

number_subformulas_neg(F, C, N0, N, NF) :-
        number_subformulas_neg(F, C, N0, N, 1, _, NF).

number_subformulas_neg(at(A,Vars), C, N, N, M0, M, C-at(A,C,M0,Vars)) :-
        M is M0 + 1.
number_subformulas_neg(forall(X,A), C, N0, N, M0, M, C-forall(X,NA)) :-
	number_subformulas_neg(A, C, N0, N, M0, M, NA).
number_subformulas_neg(exists(X,A), C, N0, N, M, M, C-exists(X,NA)) :-
	N1 is N0 + 1,
	number_subformulas_neg(A, N0, N1, N, 1, _, NA).
number_subformulas_neg(p(A,B), C, N0, N, M, M, C-p(NA,NB)) :-
	N1 is N0 + 1,
	N2 is N1 + 1,
	number_subformulas_neg(A, N0, N2, N3, 1, _, NA),
	number_subformulas_neg(B, N1, N3, N, 1, _, NB).
number_subformulas_neg(impl(A,B), C, N0, N, M0, M, C-impl(NA,NB)) :-
	number_subformulas_pos(A, C, N0, N1, M0, M1, NA),
	number_subformulas_neg(B, C, N1, N, M1, M, NB).

number_subformulas_pos(F, C, N0, N, NF) :-
        number_subformulas_pos(F, C, N0, N, 1, _, NF).

number_subformulas_pos(at(A,Vars), C, N, N, M0, M, C-at(A,C,M0,Vars)) :-
	M is M0 + 1.
number_subformulas_pos(forall(X,A), C, N0, N, M, M, C-forall(X,NA)) :-
	N1 is N0 + 1,
	number_subformulas_pos(A, N0, N1, N, 1, _, NA).
number_subformulas_pos(exists(X,A), C, N0, N, M0, M, C-exists(X,NA)) :-
	number_subformulas_pos(A, C, N0, N, M0, M, NA).
number_subformulas_pos(p(A,B), C, N0, N, M0, M, C-p(NA,NB)) :-
	number_subformulas_pos(A, C, N0, N1, M0, M1, NA),
	number_subformulas_pos(B, C, N1, N, M1, M, NB).
number_subformulas_pos(impl(A,B), C, N0, N, M, M, C-impl(NA,NB)) :-
	N1 is N0 + 1,
	N2 is N1 + 1,	
	number_subformulas_neg(A, N0, N2, N3, 1, _, NA),
	number_subformulas_pos(B, N1, N3, N, 1, _, NB).

%= unfold(+Formula, Sem, VertexNo, VarNo, AtomsDL, EdgesDL, VerticesDL)

%unfold_neg(N-F, X, M0, M, As0, As, Es0, Es, Vs0, Vs) :-
%        unfold_neg(F, N, X, M0, M, As0, As, Es0, Es, Vs0, Vs).

unfold_neg(at(A,C,N,Vars), X, M, M, [neg(A,C,N,X,Vars)|As], As, Es, Es, Vs, Vs).
unfold_neg(forall(_,_-A), X, M0, M, As0, As, Es0, Es, Vs0, Vs) :-
	unfold_neg(A, X, M0, M, As0, As, Es0, Es, Vs0, Vs).
unfold_neg(exists(var(M0),N-A), X, M0, M, As, As, [univ(M0,N)|Es], Es, [vertex(N,Bs,FVsA,Fs)|Vs0], Vs) :-
        assert(node_formula(N, neg, A)),
        free_vars_n(A, FVsA),
	M1 is M0 + 1,
	unfold_neg(A, X, M1, M, Bs, [], Fs, [], Vs0, Vs).
unfold_neg(p(N0-A,N1-B), X, M0, M, As, As, [par(N0,N1)|Es], Es, [vertex(N0,Bs,FVsA,Fs),vertex(N1,Cs,FVsB,Gs)|Vs0], Vs) :-
        assert(node_formula(N0, neg, A)),
        assert(node_formula(N1, neg, B)),
        free_vars_n(A, FVsA),
        free_vars_n(B, FVsB),
	unfold_neg(A, pi1(X), M0, M1, Bs, [], Fs, [], Vs0, Vs1),
	unfold_neg(B, pi2(X), M1, M, Cs, [], Gs, [], Vs1, Vs).
unfold_neg(impl(_-A,_-B), X, M0, M, As0, As, Es0, Es, Vs0, Vs) :-
	unfold_pos(A, Y, M0, M1, As0, As1, Es0, Es1, Vs0, Vs1),
	unfold_neg(B, appl(X,Y), M1, M, As1, As, Es1, Es, Vs1, Vs).

unfold_pos(at(A,C,N,Vars), X, M, M, [pos(A,C,N,X,Vars)|As], As, Es, Es, Vs, Vs).
unfold_pos(forall(var(M0),N0-A), X, M0, M, As, As, [univ(M0,N0)|Es], Es, [vertex(N0,Bs,FVsA,Fs)|Vs0], Vs) :-
        assert(node_formula(N0, pos, A)),
        free_vars_p(A, FVsA),
	M1 is M0 + 1,
	unfold_pos(A, X, M1, M, Bs, [], Fs, [], Vs0, Vs).
unfold_pos(exists(_,_-A), X, M0, M, As0, As, Es0, Es, Vs0, Vs) :-
	unfold_pos(A, X, M0, M, As0, As, Es0, Es, Vs0, Vs).
unfold_pos(p(_-A,_-B), pair(X,Y), M0, M, As0, As, Es0, Es, Vs0, Vs) :-
	unfold_pos(A, X, M0, M1, As0, As1, Es0, Es1, Vs0, Vs1),
	unfold_pos(B, Y, M1, M, As1, As, Es1, Es, Vs1, Vs).
unfold_pos(impl(N0-A,N1-B), lambda(X,Y), M0, M, As, As, [par(N0,N1)|Es], Es, [vertex(N0,Bs,FVsA,Fs),vertex(N1,Cs,FVsB,Gs)|Vs0], Vs) :-
        assert(node_formula(N0, neg, A)),
        assert(node_formula(N1, pos, B)),
        free_vars_n(A, FVsA),
        free_vars_p(B, FVsB),
	unfold_neg(A, X, M0, M1, Bs, [], Fs, [], Vs0, Vs1),
	unfold_pos(B, Y, M1, M, Cs, [], Gs, [], Vs1, Vs).

% = free_vars_n(+Formula, -SetOfFreeVars)
%
% true if Formula (of negative polariy) has
% SetOfFreeVars, but with a slight twist: all
% variables bound by a tensor prefix are
% considered free. For example, a prefix of
% universal quantifiers is removed (and, in
% general, any negative forall/impl and
% postive exists/prod); this is the implicit
% tensor contraction rule).

free_vars_n(_-A, Vars) :-
        free_vars_n(A, Vars).
free_vars_n(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars_n(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars_n(p(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_n(impl(A,B), Vars) :-
        free_vars_p(A, Vars1),
        free_vars_n(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_n(forall(_,A), Vars) :-
        free_vars_n(A, Vars).
free_vars_n(exists(X,A), Vars) :-
       free_vars(A, Vars0),
       ord_delete(Vars0, X, Vars).

% = free_vars_p(+Formula, -SetOfFreeVars)
%
% true if Formula (of positive polariy) has
% SetOfFreeVars, but with a slight twist: all
% variables bound by a tensor prefix are
% considered free (this is the implicit tensor
% contraction rule).

free_vars_p(_-A, Vars) :-
        free_vars_p(A, Vars).
free_vars_p(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars_p(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars_p(p(A,B), Vars) :-
        free_vars_p(A, Vars1),
        free_vars_p(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_p(impl(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars_p(exists(_,A), Vars) :-
        free_vars_p(A, Vars).
free_vars_p(forall(X,A), Vars) :-
        free_vars(A, Vars0),
        ord_delete(Vars0, X, Vars).

% = free_vars(+Formula, -SetOfFreeVars)
%
% true if Formula has SetOfFreeVars under the
% standard interpretation of free/bound.

free_vars(_-A, Vars) :-
        free_vars(A, Vars).
free_vars(at(_, Vars0), Vars) :-
        sort(Vars0, Vars). 
free_vars(at(_, _, _, Vars0), Vars) :-
	sort(Vars0, Vars).
free_vars(p(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars(impl(A,B), Vars) :-
        free_vars(A, Vars1),
        free_vars(B, Vars2),
        ord_union(Vars1, Vars2, Vars).
free_vars(exists(X,A), Vars) :-
        free_vars(A, Vars0),
	ord_delete(Vars0, X, Vars).
free_vars(forall(X,A), Vars) :-
        free_vars(A, Vars0),
        ord_delete(Vars0, X, Vars).

% = print_trace(+Stream, +List).

print_trace(Stream, [A|As]) :-
        format(Stream, '~n= Proof trace =~n', []),
        print_trace(As, A, Stream).

print_trace([], A, Stream) :-
        format(Stream, '~p~n= End of trace =~2n', [A]).
print_trace([B|Bs], A, Stream) :-
        format(Stream, '~p~n', [A]),
        print_trace(Bs, B, Stream).


% = some test predicates

test :-
        /* this should fail ! */
	prove([forall(X,exists(Y,at(f,[X,Y])))], exists(V,forall(W,at(f,[W,V])))).
test0 :-
	prove([exists(X,forall(Y,at(f,[X,Y])))], forall(V,exists(W,at(f,[W,V])))).

test1 :-
        translate_lambek(p(dr(at(np),at(n)),at(n)), [0,1], F),
        prove([F], at(np, [0,1])).

test2 :-
	prove([at(np,[0,1]),forall(X,impl(at(np,[X,1]),at(s,[X,2])))], at(s,[0,2])).

test3 :-
	prove([forall(Y,forall(Z,impl(impl(at(np,[0,1]),at(s,[Y,Z])),at(s,[Y,Z])))),forall(X,impl(at(np,[X,1]),at(s,[X,2])))], at(s,[0,2])).

test4 :-
        translate_hybrid(at(np), lambda(X,appl(john,X)), john, 0, 1, John),
	translate_hybrid(h(h(at(s),at(np)),at(np)), lambda(P,lambda(Q,lambda(Z,appl(Q,appl(loves,appl(P,Z)))))), loves, 1, 2, Loves),
        translate_hybrid(at(np), lambda(V,appl(mary,V)), mary, 2, 3, Mary),
	prove([John, Loves, Mary], at(s, [0,3])).

test5 :-
        translate_hybrid(at(np), lambda(X,appl(john,X)), john, 0, 1, John),
	translate_hybrid(h(h(at(s),at(np)),at(s)), lambda(P,lambda(Q,lambda(Z,appl(Q,appl(believes,appl(P,Z)))))), believes, 1, 2, Believes),
	translate_hybrid(h(at(s),h(at(s),at(np))), lambda(VP,lambda(Z,appl(appl(VP,someone),Z))), someone, 2, 3, Someone),
	translate_hybrid(h(at(s),at(np)), lambda(S,lambda(Z1,appl(S,appl(left,Z1)))), left, 3, 4, Left),
	prove([John, Believes, Someone, Left], at(s, [0,4])).

% = I need a better axiom selection strategy

% succeeds, but proof generation fails
test6 :-
	translate_displacement(at(np), [0,1], John),
	translate_displacement(dl(at(np),at(s)), [1,2], Left),
	translate_displacement(dr(dl(dl(at(np),at(s)),dl(at(np),at(s))),at(s)), [2,3], Before),
	translate_displacement(at(np), [3,4], Mary),
	translate_displacement(dl(dr(dr(>,dl(at(np),at(s)),dl(at(np),at(s))),dl(at(np),at(s))),dr(>,dl(at(np),at(s)),dl(at(np),at(s)))), [4,5], Did),
	prove([John,Left,Before,Mary,Did], at(s,[0,5])).

% fails (verify!)
test7 :-
        translate_hybrid(at(np), lambda(X,appl(john,X)), john, 0, 1, John),
	translate_hybrid(dr(dl(at(np),at(s)),at(np)), lambda(Y,appl(studies,Y)), studies, 1, 2, Studies),
        translate_hybrid(at(np), lambda(Z,appl(logic,Z)), logic, 2, 3, Logic),
	translate_hybrid(h(h(h(at(s),dr(dl(at(np),at(s)),at(np))),h(at(s),dr(dl(at(np),at(s)),at(np)))),h(at(s),dr(dl(at(np),at(s)),at(np)))),
			 lambda(STV2,lambda(STV1,lambda(TV,lambda(V,appl(appl(STV1,TV),appl(and,appl(appl(STV2,lambda(W,W)),V))))))), and, 3, 4, And),
        translate_hybrid(at(np), lambda(X1,appl(charles,X1)), charles, 4, 5, Charles),
        translate_hybrid(at(np), lambda(Z1,appl(phonetics,Z1)), phonetics, 5, 6, Phonetics),
	prove([John, Studies, Logic, And, Charles, Phonetics], at(s,[0,6])).

% = test translations

test_d1(F) :-
	/* generalized quantifier */
	translate_displacement(dl(>,dr(>,at(s),at(np)),at(s)), [1,2], F).
test_d2(F) :-
	/* did */
	translate_displacement(dl(dr(dr(>,at(vp),at(vp)),at(vp)),dr(>,at(vp),at(vp))), [4,5], F).
test_d3(F) :-
	/* himself */
	translate_displacement(dl(<,dr(<,dr(>,at(vp),at(np)),at(np)),dr(>,at(vp),at(np))), [3,4], F).

test_h1(F) :-
	translate_hybrid(h(at(s),at(np)), lambda(P,lambda(Z,appl(P,appl(walks,Z)))), walks, 1, 2, F).
test_h2(F) :-
	translate_hybrid(h(at(s),h(at(s),at(np))), lambda(P,lambda(Z,appl(appl(P,everyone),Z))), everyone, 0, 1, F).

	
