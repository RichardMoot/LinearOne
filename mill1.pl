
:- use_module(dancing_links,       [compute_axioms/4,
				    update_roots_axiom/4,
				    update_roots_contraction/4]).
%:- use_module(portray_graph_tikz, [portray_graph/1,graph_header/0,graph_footer/1,latex_graph/1]).
:- use_module(portray_graph_none,  [portray_graph/1,graph_header/0,graph_footer/1,latex_graph/1]).
:- use_module(translations,        [translate_lambek/3,
				    translate_displacement/3,
				    translate_hybrid/6,
				    exhaustive_test/6]).
:- use_module(proof_generation,    [generate_proof/2,
				    generate_sequent_proof/2,
				    generate_natural_deduction_proof/2,
				    generate_nd_proof/2,
				    generate_hybrid_proof/2,
				    generate_displacement_proof/2]).
:- use_module(latex,               [proof_header/0,
				    proof_footer/0,
				    latex_semantics/1,
				    latex_lexicon/1,
				    latex_lexicon1/0]).
:- use_module(sem_utils,           [substitute_sem/3,
				    reduce_sem/2]).
:- use_module(replace,             [replace_graph/6,
				    replace_proofs_labels/4,
				    replace_formula/5]).
:- use_module(lexicon,             [lookup/5]).
:- use_module(auxiliaries,         [merge_fvs/3,
				    free_vars_n/2,
				    free_vars_p/2]).

:- dynamic '$PROOFS'/2, '$AXIOMS'/1, '$LOOKUP'/1.
:- dynamic node_formula/3.

:- op(400, xfy, \).
:- op(190, yfx, @).

% = adds some likely location for pdflatex/lualatex to the file search path

user:file_search_path(path, '/usr/texbin/').
user:file_search_path(path, '/opt/local/bin/').

% = some definitions for pretty-printing

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
	copy_term(A-B, AA-BB),
	numbervars(AA-BB, 0, _),
	Ps \== [],
	format('rule(~p,~p  |-  ~p,...)', [N,AA,BB]).
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

% =======================================
% = Top-level theorem prover predicates =
% =======================================

% = parse_all
%
% parse all test sentences in the currently loaded
% grammar file; test sentences are assumed to be
% of the form
%
% test(N) :-
%       parse(Words, Goal).
%
% or
%
% test(N) :-
%       prove(Antecedent, Goal).

parse_all :-
	findall(N, clause(test(N),_), List),
	parse_all(List, Solutions),
	print_solutions(List, Solutions).

parse_all([], []).
parse_all([N|Ns], [P-SemList|Ps]) :-
        test(N),
        user:'$PROOFS'(P, SemList),
	parse_all(Ns, Ps).

% = parse(+ListOfWords, +GoalFormula)
%
% true if there are lexical entries for each of the words in ListOfWords
% which allow us to derive GoalFormula; lexical entries for the Displacement
% calculus or hybrid type-logical grammars are translated into first-order
% linear logic beforehand.

parse(ListOfWords, Goal0) :-
	initialisation,
	retractall('$LOOKUP'(_)),
	assert('$LOOKUP'(0)),
	lookup(ListOfWords, Formulas, LexSem, Goal0, Goal),
	/* update lookup statistics */
	'$LOOKUP'(N0),
	N is N0 + 1,
	retractall('$LOOKUP'(_)),
	assert('$LOOKUP'(N)),
        format(user_error, '~N= Lookup ~D~n', [N]),
	prove0(Formulas, Goal, LexSem),
	fail.
parse(_, _) :-
        format(user_error, '~N= Done!~2n================~n=  statistics  =~n================~n', []),	
	'$LOOKUP'(L),
	write_lookups(L),
        final_statistics.
% Commented out since this is inconsistent with the behavior of parse_all
%	/* succeed only if at least one proof was found */
%        user:'$PROOFS'(N),
%        N > 0.

% = prove(+Antecedent, +GoalFormula)
%
% true if the sequent Antecedent |- GoalFormula is derivable in
% first-order linear logic.
%
% prove/2 and prove/3 are wrapper predicates: they do initialisation,
% call prove0/3, enumerate solutions by a failure-drive loop and
% outputs some proof statistics.
%
% The LaTeX headers and footers are also output here (when LaTeX
% output is generated).

prove(Antecedent, Goal) :-
	prove(Antecedent, Goal, []).

% = prove(+Antecedent, +GoalFormula, +LexicalSubstitutions)

prove(Antecedent, Goal, LexSem) :-
	initialisation,
	prove0(Antecedent, Goal, LexSem),
	fail.
prove(_, _, _) :-
        format(user_error, '~N= Done!~2n================~n=  statistics  =~n================~n', []),	
	final_statistics.

initialisation :-
	/* LaTeX output */
	graph_header,
	proof_header,
	/* reset counters */
	retractall('$PROOFS'(_, _)),
	assert('$PROOFS'(0, [])),
	retractall('$AXIOMS'(_)),
	assert('$AXIOMS'(0)).

final_statistics :-
	/* print final statistics and generate pdf files */
	'$AXIOMS'(A),
	'$PROOFS'(N, _),
	write_proofs(N),
	write_axioms(A),
	/* LaTeX graphs */
	graph_footer(N),
	/* LaTeX proofs */
	proof_footer.

% prove0/2, prove0/3 is a second wrapper, doing sequent unfolding
% calling the recursive prover predicate prove1/3, doing lexical
% subsitution and outputing semantics
% and proofs.

prove0(Antecedent, Goal) :-
	prove0(Antecedent, Goal, []).

prove0(Antecedent, Goal, LexSem) :-
        unfold_sequent(Antecedent, Goal, Roots, Graph, Sem0, Stats),
	portray_sequent_statistics(Stats),
	format(user_error, 'Parsing: ', []),
	/* keep a copy of the initial graph (before any unificiations) for later proof generation */
	copy_term(Graph, GraphCopy),
	portray_graph(Graph),
        prove1(Graph, Roots, Trace),
	/* proof found */
	'$PROOFS'(N0, SemList),
	N is N0 + 1,
	/* generate semantics */
	substitute_sem(LexSem, Sem0, Sem1),
	reduce_sem(Sem1, Sem),
	format(user_error, '~N= Semantics ~w: ~p~n', [N,Sem]),
	latex_semantics(Sem),
	/* update proof statistics */
	retractall('$PROOFS'(_, _)),
	assert('$PROOFS'(N, [Sem|SemList])),
	/* generate a LaTeX proof */
	/* generate_proof/2 outputs Displacement, hybrid, natural deduction and sequent proofs */
	/* if you are only interested in one type of proof, replace generate_proof/2 by one of: */
	/* generate_hybrid_proof/2, (natural deduction proofs in hybrid type-logical grammar) */
        /* generate_displacement_proof/2, (natural deduction proofs for the Displacement calculus) */
	/* generate_sequent_proof/2, (sequent proofs in first-order linear logic) */
	/* generate_natural_deduction_proof/2, (natural deduction proof in first-order linear logic) */
	/* generate_nd_proof/2, (natural deduction proof in first-order linear logic with implicit antecedents) */
%	generate_hybrid_proof(GraphCopy, Trace).
%	generate_displacement_proof(GraphCopy, Trace).
	generate_proof(GraphCopy, Trace).

% = first_proof
%
% a version of the prover predicate which only finds the first proof.

first_proof(Antecedent, Goal, Sem) :-
	first_proof(Antecedent, Goal, [], Sem).

first_proof(Antecedent, Goal, LexSem, Sem) :-
	( is_stream(graph) -> true ; open_null_stream(Stream), set_stream(Stream, alias(graph))),
        unfold_sequent(Antecedent, Goal, Roots, Graph, Sem0, _Stats),
        prove1(Graph, Roots, _Trace),
	!,
	substitute_sem(LexSem, Sem0, Sem1),
	reduce_sem(Sem1, Sem).


% = first_parse(+ListOfWords, +GoalFormula)
%
% a version of parse which finds only the first solution.

first_parse(ListOfWords, Goal0) :-
	initialisation,
	retractall('$LOOKUP'(_)),
	assert('$LOOKUP'(0)),
	lookup(ListOfWords, Formulas, LexSem, Goal0, Goal),
	/* update lookup statistics */
	'$LOOKUP'(N0),
	N is N0 + 1,
	retractall('$LOOKUP'(_)),
	assert('$LOOKUP'(N)),
        format(user_error, '~N= Lookup ~D~n', [N]),
	prove0(Formulas, Goal, LexSem),
	!,
        format(user_error, '~N= Done!~2n================~n=  statistics  =~n================~n', []),	
	'$LOOKUP'(L),
	write_lookups(L),
        final_statistics.


% = prove1(+Graph, +Roots, -Trace)
%
% true if Graph (with root nodes Roots) is a proof net, as justified by
% the axioms/contractions in Trace.
%
% the prove1 predicate operates by identifying, at each recursive step, a pair
% of atomic formulas and contracting the input graph (verifying for acyclicity
% and connectedness)

prove1([vertex(_, [], _, [])], _, []) :-
	/* a single vertex with atoms or links, we have succeeded ! */
        format(user_error, '~N= Proof found!~n', []),
        !.
prove1(Graph0, Roots0, [ax(N0,AtV0,AtO0,N1,AtV1,AtO1)|Rest0]) :-
	/* forced choice for positive atom, using first-found from the best */
	/* choices returned by the dancing links algorithm */
	/* TODO: evaluate different tie-breakers here as a heuristic for selecting */
	/* atoms likely to fail quickly */
	compute_axioms(Roots0, Graph0, _ATree, [tuple(AtV1,AtO1,N1,Choices)|_Axioms]),
        select(vertex(N1, [A|As0], FVs0, Ps0), Graph0, Graph1),
        select(pos(At,AtV1,AtO1,X,Vars), [A|As0], As),
	!,
	/* enumerate choices for negative atom */
	member(tuple(AtV0,AtO0,N0), Choices),
	select(vertex(N0, [B|Bs0], FVs1, Ps1), Graph1, Graph2),
	select(neg(At,AtV0,AtO0,X,Vars), [B|Bs0], Bs),
        /* verify no cycle has been created */
        \+ cyclic(Ps0, Graph2, N0),
        \+ cyclic(Ps1, Graph2, N1),
	'$AXIOMS'(Ax0),
	Ax is Ax0 + 1,
	retractall('$AXIOMS'(_)),
	assert('$AXIOMS'(Ax)),
	/* identify nodes of positive and negative atom */
	/* (and do the necessary replacements) */
	append(As, Bs, Cs),
	append(Ps0, Ps1, Ps),
	merge_fvs(FVs0, FVs1, FVs),
	replace_graph(Graph2, Ps, N0, N1, Graph3, Rs),
	update_roots_axiom(Roots0, N0, N1, Roots1),
	Graph4 = [vertex(N1,Cs,FVs,Rs)|Graph3],
        portray_graph(Graph4),
	/* perform Danos-style graph contractions */
	contract(Graph4, Graph, Rest0, Rest, Roots1, Roots),
	/* verify the result is (at least potentially) connected */
	connected(Graph),
	mark_progress(Graph),
	prove1(Graph, Roots, Rest).

% =======================================
% =              Proof nets             =
% =======================================

% = contract(+InGraph,-OutGraph, TraceDL, RootNodeAcc)
%
% perform all valid contractions on InGraph producing OutGraph;
% these are Danos-style contractions, performed in a first-found
% search.
%
% In addition, it returns a Trace of the contractions performed (as
% a difference list) and updates the root nodes of the graph (using
% an accumulator).

contract(Graph0, Graph, L0, L, R0, R) :-
        contract1(Graph0, Graph1, L0, L1, R0, R1),
        portray_graph(Graph1),
        !,
        contract(Graph1, Graph, L1, L, R1, R).
contract(Graph, Graph, L, L, R, R).

% par contraction
contract1(Graph0, [vertex(N1,Cs,FVs,Rs)|Graph], [N0-par(N1)|Rest], Rest, Roots0, Roots) :-
        select(vertex(N0, As, FVsA, Ps0), Graph0, Graph1),
        select(par(N1, N1), Ps0, Ps),
	select(vertex(N1, Bs, FVsB, Qs), Graph1, Graph2),
	\+ cyclic(Qs, Graph2, N0),
	!,
	append(As, Bs, Cs),
	append(Ps, Qs, Rs0),
	merge_fvs(FVsA, FVsB, FVs),
	replace_graph(Graph2, Rs0, N0, N1, Graph, Rs),
        update_roots_contraction(Roots0, N0, N1, Roots).
% forall contraction
contract1(Graph0, [vertex(N1,Cs,FVs,Rs)|Graph], [N0-univ(U,N1)|Rest], Rest, Roots0, Roots) :-
        select(vertex(N0, As, FVsA, Ps0), Graph0, Graph1),
        select(univ(U, N1), Ps0, Ps),
	select(vertex(N1, Bs, FVsB, Qs), Graph1, Graph2),
	no_occurrences(Bs, Qs, Graph2, U),
	no_occurrences1(FVsA, U),
	no_occurrences(Graph2, U),
	!,
	append(As, Bs, Cs),
	append(Ps, Qs, Rs0),
	merge_fvs(FVsA, FVsB, FVs),
	replace_graph(Graph2, Rs0, N0, N1, Graph, Rs),
        update_roots_contraction(Roots0, N0, N1, Roots).

% = no_occurrences
%
% verify that the module above the forall link has no remaining occurrences of the eigenvariable
% of the link in atomic formulas
%
% TODO: this can surely be done in a smarter way. For example, it only makes sense to try and
% contract a forall link after all atomic formulas containing its eigenvariable have been
% connected.

no_occurrences([], Ps, G, V) :-
	no_occurrences_pars(Ps, G, V).
no_occurrences([A|As], Ps, G, V) :-
	no_atom_occurrences(A, V),
	no_occurrences(As, Ps, G, V).

no_atom_occurrences(pos(_, _, _, _, Vs), V) :-
	no_varlist_occurrences(Vs, V).
no_atom_occurrences(neg(_, _, _, _, Vs), V) :-
	no_varlist_occurrences(Vs, V).

no_varlist_occurrences([], _).
no_varlist_occurrences([V|Vs], W) :-
	V \== var(W),
	no_varlist_occurrences(Vs, W).

no_occurrences_pars([], _, _).
no_occurrences_pars([P|Ps], G0, V) :-
	no_occurrences_par(P, V, G0, G),
	no_occurrences_pars(Ps, G, V).

no_occurrences_par(univ(_,N1), V, G0, G) :-
    (
	selectchk(vertex(N1,Cs,_,Rs), G0, G)
    ->			 
	no_occurrences(Cs, Rs, G, V)
    ;
        G = G0
    ).
no_occurrences_par(par(N1,N2), V, G0, G) :-
    (
	selectchk(vertex(N1,Cs,_,Rs), G0, G1)
    ->			 
	no_occurrences(Cs, Rs, G1, V)
    ;
        G1 = G0
    ),
    (
	selectchk(vertex(N2,Ds,_,Ss), G1, G)
    ->			 
	no_occurrences(Ds, Ss, G, V)
    ;
        G = G1
    ).


% test for cyclicity
% G2 contains unvisited nodes
% P contains paths from current node
% N is the node to reach for a cycle.

cyclic([P|_], Graph, N) :-
    cyclic1(P, Graph, N).
cyclic([_|Ps], Graph, N) :-
    cyclic(Ps, Graph, N).

cyclic1(par(M,P), Graph0, N) :-
    (
       N =:= M
    ;
       N =:= P
    ;
       select(vertex(M,_,_,Ps), Graph0, Graph),
       cyclic(Ps, Graph, N)
    ;
       P \== M,
       select(vertex(P,_,_,Ps), Graph0, Graph),
       cyclic(Ps, Graph, N)
    ).
cyclic1(univ(_,M), Graph0, N) :-
    (
       N =:= M
     ;
       select(vertex(M,_,_,Ps), Graph0, Graph),
       cyclic(Ps, Graph, N)
    ).        

% = connected(+Graph)
%
% true if Graph is connected or at least can be made connected
% by vertex identifications (corresponding to axioms)
%
% This test presupposes that all possible contractions for the
% current graph have been performed.

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
	/* In other words, in a fully contracted graph, */
	/* a node cannot have both As and Ps empty */    
        Ps = [_|_]
    ;
        true
    ),
    connected1(Vs).

% = no_occurrences(+Graph, +VarNum)
%
% walks through +Graph and checks that none of its vertices
% has the variable +VarNum in their list of free variables
% (this is the condition on the forall contraction)

no_occurrences([], _).
no_occurrences([vertex(_, _, FVs, _)|Rest], U) :-
        no_occurrences1(FVs, U),
        no_occurrences(Rest, U).

no_occurrences1([], _).
no_occurrences1([V|Vs], U) :-
        var(U) \== V,
        no_occurrences1(Vs, U).

% =======================================
% =      Formula/sequent unfolding      =
% =======================================

% transforms sequents, antecedents and (polarized) formulas into graphs

% = unfold_sequent(+ListOfFormulas, +GoalFormula, -RootNodes, -Vertices, -Semantics) 
%
% unfold the sequent ListOfFormulas |- GoalFormula into the graph Vertices, keeping
% track of the RootNodes (of the resulting forest) and the term representing the
% Semantics (after all axiom links have been performed).
%
% In addition, for later proof generation, all nodes in the initial graph will have
% their node number, polarity and the formula corresponding to this node stored by
% means of an asserted
%
% node_formula(NodeNumber, Polarity, Formula)
%
% declaration (with Polarity one of pos/neg).
	    
unfold_sequent(List, Goal, Roots, Vs0, Sem, Stats) :-
        retractall(node_formula(_,_,_)),
	init_stats(Stats0),
	unfold_antecedent(List, 0, _W, 0, N0, 0, M, Roots0, Vs0, [vertex(N0,As,FVsG,Es)|Vs1], Stats0, Stats1),
	N is N0 + 1,
	append(Roots0, [N0], Roots),
	number_subformulas_pos(Goal, N0, N, _, _-NGoal),
        assert(node_formula(N0, pos, NGoal)),
	free_vars_p(Goal, FVsG),
	unfold_pos(NGoal, Sem, M, _, As, [], Es, [], Vs1, [], Stats1, Stats).

unfold_antecedent([], W, W, N, N, M, M, [], Vs, Vs, Stats, Stats).
unfold_antecedent([F|Fs], W0, W, N0, N, M0, M, [N0|Rs], [vertex(N0,As,FVsF,Es)|Vs0], Vs, Stats0, Stats) :-
        N1 is N0 + 1,
        W1 is W0 + 1,
	free_vars_n(F, FVsF),
	number_subformulas_neg(F, N0, N1, N2, _-NF),
        assert(node_formula(N0, neg, NF)),
	unfold_neg(NF, '$VAR'(W0), M0, M1, As, [], Es, [], Vs0, Vs1, Stats0, Stats1),
	unfold_antecedent(Fs, W1, W, N2, N, M1, M, Rs, Vs1, Vs, Stats1, Stats).

%= unfold_neg(+Formula, Sem, VertexNo, VarNoAcc, AtomsDL, AtomsDL, EdgesDL, VerticesDL)

unfold_neg(at(A,C,N,Vars), X, M, M, [neg(A,C,N,X,Vars)|As], As, Es, Es, Vs, Vs, Stats0, Stats) :-
	add_neg_atom(Stats0, Stats).
unfold_neg(forall(_,_-A), X, M0, M, As0, As, Es0, Es, Vs0, Vs, Stats0, Stats) :-
	add_unary_tensor(Stats0, Stats1),
	unfold_neg(A, X, M0, M, As0, As, Es0, Es, Vs0, Vs, Stats1, Stats).
unfold_neg(exists(var(M0),N-A), X, M0, M, As, As, [univ(M0,N)|Es], Es, [vertex(N,Bs,FVsA,Fs)|Vs0], Vs, Stats0, Stats) :-
        assert(node_formula(N, neg, A)),
        free_vars_n(A, FVsA),
	M1 is M0 + 1,
	add_unary_par(Stats0, Stats1),
	unfold_neg(A, X, M1, M, Bs, [], Fs, [], Vs0, Vs, Stats1, Stats).
unfold_neg(p(N0-A,N1-B), X, M0, M, As, As, [par(N0,N1)|Es], Es, [vertex(N0,Bs,FVsA,Fs),vertex(N1,Cs,FVsB,Gs)|Vs0], Vs, Stats0, Stats) :-
        assert(node_formula(N0, neg, A)),
        assert(node_formula(N1, neg, B)),
        free_vars_n(A, FVsA),
        free_vars_n(B, FVsB),
	add_binary_par(Stats0, Stats1),
	unfold_neg(A, pi1(X), M0, M1, Bs, [], Fs, [], Vs0, Vs1, Stats1, Stats2),
	unfold_neg(B, pi2(X), M1, M, Cs, [], Gs, [], Vs1, Vs, Stats2, Stats).
unfold_neg(impl(_-A,_-B), X, M0, M, As0, As, Es0, Es, Vs0, Vs, Stats0, Stats) :-
	add_binary_tensor(Stats0, Stats1),
	unfold_pos(A, Y, M0, M1, As0, As1, Es0, Es1, Vs0, Vs1, Stats1, Stats2),
	unfold_neg(B, appl(X,Y), M1, M, As1, As, Es1, Es, Vs1, Vs, Stats2, Stats).

%= unfold_pos(+Formula, Sem, VertexNo, VarNoAcc, AtomsDL, AtomsDL, EdgesDL, VerticesDL)

unfold_pos(at(A,C,N,Vars), X, M, M, [pos(A,C,N,X,Vars)|As], As, Es, Es, Vs, Vs, Stats0, Stats) :-
	add_pos_atom(Stats0, Stats).
unfold_pos(forall(var(M0),N0-A), X, M0, M, As, As, [univ(M0,N0)|Es], Es, [vertex(N0,Bs,FVsA,Fs)|Vs0], Vs, Stats0, Stats) :-
        assert(node_formula(N0, pos, A)),
        free_vars_p(A, FVsA),
	M1 is M0 + 1,
	add_unary_par(Stats0, Stats1),
	unfold_pos(A, X, M1, M, Bs, [], Fs, [], Vs0, Vs, Stats1, Stats).
unfold_pos(exists(_,_-A), X, M0, M, As0, As, Es0, Es, Vs0, Vs, Stats0, Stats) :-
	add_unary_tensor(Stats0, Stats1),
	unfold_pos(A, X, M0, M, As0, As, Es0, Es, Vs0, Vs, Stats1, Stats).
unfold_pos(p(_-A,_-B), pair(X,Y), M0, M, As0, As, Es0, Es, Vs0, Vs, Stats0, Stats) :-
	add_binary_tensor(Stats0, Stats1),
	unfold_pos(A, X, M0, M1, As0, As1, Es0, Es1, Vs0, Vs1, Stats1, Stats2),
	unfold_pos(B, Y, M1, M, As1, As, Es1, Es, Vs1, Vs, Stats2, Stats).
unfold_pos(impl(N0-A,N1-B), lambda(X,Y), M0, M, As, As, [par(N0,N1)|Es], Es, [vertex(N0,Bs,FVsA,Fs),vertex(N1,Cs,FVsB,Gs)|Vs0], Vs, Stats0, Stats) :-
        assert(node_formula(N0, neg, A)),
        assert(node_formula(N1, pos, B)),
        free_vars_n(A, FVsA),
        free_vars_p(B, FVsB),
	add_binary_par(Stats0, Stats1),
	unfold_neg(A, X, M0, M1, Bs, [], Fs, [], Vs0, Vs1, Stats1, Stats2),
	unfold_pos(B, Y, M1, M, Cs, [], Gs, [], Vs1, Vs, Stats2, Stats).

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


% =======================================
% =             Input/output            =
% =======================================

mark_progress(G) :-
	length(G, L),
	format(user_error, '~D.', [L]),
        flush_output(user_error).
	

% = sequent statistics predicates

init_stats(stats(0,0,0,0,0,0)).

add_neg_atom(stats(A0,B,C,D,E,F), stats(A,B,C,D,E,F)) :-
	A is A0 + 1.

add_pos_atom(stats(A,B0,C,D,E,F), stats(A,B,C,D,E,F)) :-
	B is B0 + 1.

add_unary_tensor(stats(A,B,C0,D,E,F), stats(A,B,C,D,E,F)) :-
	C is C0 + 1.

add_unary_par(stats(A,B,C,D0,E,F), stats(A,B,C,D,E,F)) :-
	D is D0 + 1.

add_binary_tensor(stats(A,B,C,D,E0,F), stats(A,B,C,D,E,F)) :-
	E is E0 + 1.

add_binary_par(stats(A,B,C,D,E,F0), stats(A,B,C,D,E,F)) :-
	F is F0 + 1.


portray_sequent_statistics(stats(A,B,C,D,E,F)) :-
   (
	A =:= B
    ->
	format('~NAtoms:   ~|~t~D~4+~n', [A])
    ;
        format('~NAtoms:   ~|~t-~D~4+  ~|~t+~D~4+~n', [A,B])
    ),
        format('Unary : T~|~t~D~4+ P~|~t~D~4+~n', [C,D]),
	format('Binary: T~|~t~D~4+ P~|~t~D~4+~n', [E,F]).




% = print_trace(+Stream, +List).
%
% output proof trace in List to Stream

print_trace(Stream, [A|As]) :-
        format(Stream, '~n= Proof trace =~n', []),
        print_trace(As, A, Stream).

print_trace([], A, Stream) :-
        format(Stream, '~p~n= End of trace =~2n', [A]).
print_trace([B|Bs], A, Stream) :-
        format(Stream, '~p~n', [A]),
        print_trace(Bs, B, Stream).


% = print_list(+List)
%
% output List to user_error

print_list([]).
print_list([A|As]) :-
	format(user_error, '~p~n', [A]),
	print_list(As).

% = write_proof(P)
%
% output a message stating P proofs have been found

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
       format(user_output, '~D proofs found.~n', [P])
   ).

% = write_axioms(A)
%
% output a message stating A axioms have been performed

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
       format(user_output, '~D axioms performed.~n', [A])
   ).

% = write_lookup(L)
%
% output a message stating L lexical lookups have been done

write_lookups(L) :-
   (
       L =:= 0
   ->
       format(user_output, 'No lexical lookups!~n', [])
   ;
       L =:= 1
   ->
       format(user_output, '1 lexical lookup.~n', [])
   ;
       format(user_output, '~D lexical lookups.~n', [L])
   ).


% = print_solutions(+ExampleNos, +NumSolutions)
%
% display for each example in ExampleNo its number of solutions
% in NumSolutions and print an overview of the number of failed,
% succeeded and total examples.

print_solutions(L, NS) :-
	open('parse_log.txt', write, Stream, []), 
	format(Stream, 'SentNo Solutions~n', []),
	format(user_error, 'SentNo Solutions~n', []),
	print_solutions(L, Stream, 0, 0, NS),
	close(Stream).
print_solutions([], Stream, S, F, []) :-
	Total is S + F,
	format(Stream, '~nTotal sentences :~|~t~d~4+~nSucceeded       :~|~t~d~4+~nFailed          :~|~t~d~4+~n', [Total, S, F]),
	format(user_error, '~nTotal sentences :~|~t~d~4+~nSucceeded       :~|~t~d~4+~nFailed          :~|~t~d~4+~n', [Total, S, F]).
print_solutions([N|Ns], Stream, S0, F0, [P-SemList|Ps]) :-
	format(Stream, '~|~t~d~6+ ~|~t~d~9+', [N,P]),
	format(user_error, '~|~t~d~6+ ~|~t~d~9+', [N,P]),
    (
	P =:= 0
    ->
        format(Stream, ' * ~p~n', [SemList]),
        format(user_error, ' * ~p~n', [SemList]),
	F is F0 + 1,
	S = S0
    ;
        format(Stream, '   ~p~n', [SemList]),
        format(user_error, '   ~p~n', [SemList]),
        S is S0 + 1,
        F = F0
    ),
	print_solutions(Ns, Stream, S, F, Ps).

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

% = generate exhaustive test file	
