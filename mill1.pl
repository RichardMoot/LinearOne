
:- use_module(dancing_links, [compute_axioms/4, update_roots_axiom/4, update_roots_contraction/4]).
%:- use_module(portray_graph_tikz, [portray_graph/1,graph_header/0,graph_footer/1,latex_graph/1]).
:- use_module(portray_graph_none, [portray_graph/1,graph_header/0,graph_footer/1,latex_graph/1]).
:- use_module(translations, [translate_lambek/3,translate_displacement/3,translate_hybrid/6]).
:- use_module(proof_generation, [generate_proof/2]).
:- use_module(latex, [latex_proof/1,proof_header/0,proof_footer/0,latex_semantics/1]).
:- use_module(sem_utils, [substitute_sem/3,reduce_sem/2]).
:- use_module(replace, [replace_graph/6,replace_proofs_labels/4,replace_formula/5]).
:- use_module(lexicon, [parse/2,parse_all/0]).
:- use_module(auxiliaries, [merge_fvs/3, free_vars_n/2, free_vars_p/2]).

:- dynamic '$PROOFS'/1, '$AXIOMS'/1.
:- dynamic node_formula/3.

generate_diagnostics(false).

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

% =======================================
% = Top-level theorem prover predicates =
% =======================================

% = prove(+Antecedent, +GoalFormula)

prove(Antecedent, Goal) :-
	prove(Antecedent, Goal, []).

% = prove(+Antecedent, +GoalFormula, +LexicalSubstitutions)

prove(Antecedent, Goal, LexSem) :-
	initialisation,
	multi_prove(Antecedent, Goal, LexSem),
	fail.
prove(_, _, _) :-
        format(user_error, '~N= Done!~2n================~n=  statistics  =~n================~n', []),	
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
	write_proofs(N),
	write_axioms(A),
	/* LaTeX graphs */
	graph_footer(N),
	/* LaTeX proofs */
	proof_footer.



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
	format(user_error, '~N= Semantics ~w: ~p~n', [N,Sem]),
	latex_semantics(Sem),
	/* generate a LaTeX proof */
	generate_proof(Vs, Trace).


prove1([vertex(_, [], _, [])], _, []) :-
        format(user_error, '~N= Proof found!~n', []),
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
	replace_graph(G2, Ps, N0, N1, G3, Rs),
%	replace(G2, N0, N1, G3),
%	replace_pars(Ps, N0, N1, Rs),
	update_roots_axiom(Roots0, N0, N1, Roots1),
	G4 = [vertex(N1,Cs,FVs,Rs)|G3],
        portray_graph(G4),
	contract(G4, G, Rest0, Rest, Roots1, Roots),
	connected(G),
	prove1(G, Roots, Rest).

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
	replace_graph(G2, Rs0, N0, N1, G, Rs),
%	replace_pars(Rs0, N0, N1, Rs),
%	replace(G2, N0, N1, G),
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
	replace_graph(G2, Rs0, N0, N1, G, Rs),
%	replace_pars(Rs0, N0, N1, Rs),
%	replace(G2, N0, N1, G),
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

% =======================================
% =             Input/output            =
% =======================================

% = print_trace(+Stream, +List).

print_trace(Stream, [A|As]) :-
        format(Stream, '~n= Proof trace =~n', []),
        print_trace(As, A, Stream).

print_trace([], A, Stream) :-
        format(Stream, '~p~n= End of trace =~2n', [A]).
print_trace([B|Bs], A, Stream) :-
        format(Stream, '~p~n', [A]),
        print_trace(Bs, B, Stream).


print_list([]).
print_list([A|As]) :-
	format(user_error, '~p~n', [A]),
	print_list(As).

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

	
