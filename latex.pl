:- module(latex, [latex_proof/1,proof_header/0,proof_footer/0,latex_semantics/1]).

% set this option to "prolog_like" for a Prolog-like output; this will portray terms like
% ((f y) x) as f(x,y)

option(prolog_like).

proof_header :-
      ( exists_file('latex_proofs.tex') -> delete_file('latex_proofs.tex') ; true),
	open('latex_proofs.tex', write, _Stream, [alias(latex)]),
	format(latex, '\\documentclass[leqno]{article}~2n', []),
	format(latex, '\\usepackage[a2paper]{geometry}~n', []),
	format(latex, '\\usepackage{proof}~n', []),
	format(latex, '\\usepackage{amsmath}~n', []),
	format(latex, '\\usepackage{amssymb}~2n', []),
	format(latex, '\\begin{document}~2n', []).

proof_footer :-
	format(latex, '~n\\end{document}~n', []),
	close(latex),
    (
	access_file('latex_proofs.tex', read)
    ->
	shell('pdflatex latex_proofs.tex > /dev/null'),
	format('LaTeX proofs ready~n', [])
     ;
        format('LaTeX proof output failed~n', [])
     ).


latex_proof(Proof0) :-
	copy_term(Proof0, Proof),
	numbervars(Proof, 0, _),
	latex_proof(Proof, 0),
        format(latex, '~n\\bigskip~n', []).

latex_proof(_-Proof, Tab) :-
        latex_proof(Proof, Tab).
latex_proof(rule(Name, Ant, Suc, SubProofs), Tab0) :-
	format(latex, '\\infer[~@]{~@}{', [latex_rule_name(Name),latex_sequent(Ant,Suc)]),
	Tab is Tab0 + 6,
	latex_proofs(SubProofs, Tab),
	(SubProofs = [] -> true ; tab(latex,Tab0)),
        format(latex, '}~n', []).


latex_proofs([], _Tab).
latex_proofs([P|Ps], Tab) :-
	/* newline and tab only when there is at least one premiss */
	nl(latex),
	tab(latex, Tab),
	latex_proofs1(Ps, P, Tab).

latex_proofs1([], P, Tab) :-
	latex_proof(P, Tab).
latex_proofs1([P|Ps], Q, Tab) :-
	latex_proof(Q, Tab),
	tab(latex, Tab),
	format(latex, '&~n', []),
	tab(latex, Tab),
	latex_proofs1(Ps, P, Tab).


%latex_rule_name(ax) :-
%	write('Axiom').
latex_rule_name(ax).
latex_rule_name(cut) :-
	write(latex, 'Cut').
latex_rule_name(fl) :-
	write(latex, 'L\\forall').
latex_rule_name(fr) :-
	write(latex, 'R\\forall').
latex_rule_name(el) :-
	write(latex, 'L\\exists').
latex_rule_name(er) :-
	write(latex, 'R\\exists').
latex_rule_name(il) :-
	write(latex, 'L\\multimap').
latex_rule_name(ir) :-
	write(latex, 'R\\multimap').
latex_rule_name(pl) :-
	write(latex, 'L\\otimes').
latex_rule_name(pr) :-
	write(latex, 'R\\otimes').

latex_sequent(Ant, Suc) :-
	format(latex, '~@ \\vdash ~@', [latex_antecedent(Ant),latex_formula(Suc)]).

latex_antecedent([]).
latex_antecedent([A|As]) :-
	latex_antecedent(As, A).

latex_antecedent([], A) :-
	latex_formula(A).
latex_antecedent([A|As], B) :-
	latex_formula(B),
	write(latex, ','),
	latex_antecedent(As, A).

latex_formula(F) :-
	latex_formula(F, 0).

latex_formula(_-F, N) :-
	latex_formula(F, N).
latex_formula(at(F,Vs0), _) :-
	update_vars(Vs0, Vs),
	Term =.. [F|Vs],
	print(latex, Term).
latex_formula(at(F,_,_,Vs0), _) :-
	update_vars(Vs0, Vs),
	Term =.. [F|Vs],
	print(latex, Term).
latex_formula(forall(X,F), _) :-
	!,
	update_var(X, Y),
   (
	is_quantified(F)
   ->
	format(latex, '\\forall ~w. ~@', [Y,latex_formula(F, 1)])
   ;
	format(latex, '\\forall ~w. [~@]', [Y,latex_formula(F, 0)])
   ).
latex_formula(exists(X,F), _) :-
	!,
	update_var(X, Y),
   (
	is_quantified(F)
   ->
	format(latex, '\\exists ~w. ~@', [Y,latex_formula(F, 1)])
   ;
	format(latex, '\\exists ~w. [~@]', [Y,latex_formula(F, 0)])
   ).
latex_formula(p(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\otimes ~@', [latex_formula(A, 1),latex_formula(B, 1)])
   ;
	format(latex, '(~@ \\otimes ~@)', [latex_formula(A, 1),latex_formula(B, 1)])
   ).
latex_formula(impl(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\multimap ~@', [latex_formula(A, 1),latex_formula(B, 0)])
   ;
	format(latex, '(~@ \\multimap ~@)', [latex_formula(A, 1),latex_formula(B, 1)])
   ).

is_quantified(_-F) :-
	is_quantified(F).
is_quantified(exists(_,_)).
is_quantified(forall(_,_)).
is_quantified(at(_,_)).
is_quantified(at(_,_,_,_)).

update_vars([], []).
update_vars([V|Vs], [W|Ws]) :-
	update_var(V, W),
	update_vars(Vs, Ws).

update_var(V, W) :-
    (
         V = var(M)
    ->
         variable_atom(M, W)
    ;
         V = W
    ).	


variable_atom(N, At) :-
	VN is N mod 5,
	VI is N//5,
	print_var1(VI, V),
	atomic_list_concat([V, '_{', VN, '}'], At).
    
print_var1(0, x).
print_var1(1, y).
print_var1(2, z).
print_var1(3, v).
print_var1(4, w).

latex_semantics(Sem) :-
	format(latex, '~2n\\begin{equation}~n', []),	
	latex_semantics(Sem, 0),
	format(latex, '~n\\end{equation}~2n', []).

latex_semantics(true, _) :-
	!,
	format(latex, '\\top ', []).
latex_semantics(false, _) :-
	!,
	format(latex, '\\bot ', []).
latex_semantics(empty_set, _) :-
	!,
	format(latex, '\\emptyset ', []).
latex_semantics(forall, _) :-
	!,
	format(latex, '\\forall ', []).
latex_semantics(exists, _) :-
	!,
	format(latex, '\\exists ', []).
latex_semantics(iota, _) :-
	!,
	format(latex, '\\iota ', []).
latex_semantics(epsilon, _) :-
	!,
	format(latex, '\\epsilon ', []).
latex_semantics(tau, _) :-
	!,
	format(latex, '\\tau ', []).
latex_semantics(number_of(A), _) :-
	!,
	format(latex, '\\| ~@ \\|', [latex_semantics(A, 0)]).
latex_semantics(A, _) :-
	atomic(A),
	!,
	latex_atom(A).
latex_semantics('$VAR'(N), _) :-
	!,
	variable_atom(N, At),
	write(latex, At).
latex_semantics(lambda(X,M), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '\\lambda ~@. ~@', [latex_semantics(X, 1), latex_semantics(M, 1)])
   ;
	format(latex, '(\\lambda ~@. ~@)', [latex_semantics(X, 1), latex_semantics(M, 1)])
   ).
latex_semantics(appl(appl(appl(F,Z),Y),X), _) :-
	atomic(F),
	option(prolog_like),
	!,
	format(latex, '~@(~@,~@,~@)', [latex_atom(F),latex_semantics(X, 0),latex_semantics(Y, 0),latex_semantics(Z, 0)]).
latex_semantics(appl(appl(F,Y),X), _) :-
	atomic(F),
	option(prolog_like),
	!,
	format(latex, '~@(~@,~@)', [latex_atom(F),latex_semantics(X, 0),latex_semantics(Y, 0)]).
latex_semantics(appl(F,X), _) :-
	atomic(F),
	option(prolog_like),
	!,
	format(latex, '~@(~@)', [latex_atom(F),latex_semantics(X, 0)]).
latex_semantics(appl(N,M), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@\\, ~@', [latex_semantics(N, 1), latex_semantics(M, 1)])
   ;
	format(latex, '(~@\\, ~@)', [latex_semantics(N, 1), latex_semantics(M, 1)])
   ).
latex_semantics(pair(N,M), _NB) :-
	!,
	format(latex, '\\langle ~@,~@\\rangle', [latex_semantics(N, 0), latex_semantics(M, 0)]).
latex_semantics(pi1(N), _NB) :-
	!,
    (
	unary_term(N)
    ->
        format(latex, '\\pi_1 ~@', [latex_semantics(N, 1)])
    ;	     
        format(latex, '\\pi_1(~@)', [latex_semantics(N, 0)])
    ).
latex_semantics(pi2(N), _NB) :-
	!,
    (
	unary_term(N)
    ->
        format(latex, '\\pi_2 ~@', [latex_semantics(N, 1)])
    ;	     
        format(latex, '\\pi_2(~@)', [latex_semantics(N, 0)])
    ).
latex_semantics(neg(N), _NB) :-
	!,
    (
	unary_term(N)
    ->
        format(latex, '\\neg ~@', [latex_semantics(N, 1)])
    ;	     
        format(latex, '\\neg(~@)', [latex_semantics(N, 0)])
    ).
latex_semantics(possible(N), _NB) :-
	!,
    (
	unary_term(N)
    ->
        format(latex, '\\Diamond ~@', [latex_semantics(N, 1)])
    ;	     
        format(latex, '\\Diamond(~@)', [latex_semantics(N, 0)])
    ).
latex_semantics(necessary(N), _NB) :-
	!,
    (
	unary_term(N)
    ->
        format(latex, '\\Box ~@', [latex_semantics(N, 1)])
    ;	     
        format(latex, '\\Box(~@)', [latex_semantics(N, 0)])
    ).
latex_semantics(quant(Q,X,F), _NB) :-
	!,
    (	
	F = quant(_,_,_)
    ->
	format(latex, '~@ ~@. ~@', [latex_quantifier(Q), latex_semantics(X, 0), latex_semantics(F, 1)])
    ;
        format(latex, '~@ ~@.[~@]', [latex_quantifier(Q), latex_semantics(X, 0), latex_semantics(F, 0)])
    ).
latex_semantics(bool(P,B,Q), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ ~@ ~@', [latex_semantics(P, 1), latex_bool(B), latex_semantics(Q, 1)])
   ;
	format(latex, '(~@ ~@ ~@)', [latex_semantics(P, 1), latex_bool(B), latex_semantics(Q, 1)])
   ).
latex_semantics(Term, _) :-
	/* unknown: warn but output normally */
	functor(Term, F, A),
	format(user_error, '~N{Warning: unknown LaTeX output form: ~w (with functor ~w/~w)}~n', [Term, F, A]),
	format(latex, ' ~w ', [Term]).

latex_bool(&) :-
	!,
	write(latex, '\\wedge').
latex_bool(\/) :-
	!,
	write(latex, '\\vee').
latex_bool(->) :-
	!,
	write(latex, '\\rightarrow').
latex_bool(leq) :-
	!,
	write(latex, '\\leq').
latex_bool(lneq) :-
	!,
	write(latex, '\\lneq').
latex_bool(geq) :-
	!,
	write(latex, '\\geq').
latex_bool(gneq) :-
	!,
	write(latex, '\\gneq').
latex_bool(set_member) :-
	!,
	write(latex, '\\in').
latex_bool(B) :-
	/* unknown: warn but output normally */
	format(user_error, '~N{Warning: unknown LaTeX output boolean connective: ~w}~n', [B]),
	format(latex, ' ~w ', [B]).

latex_quantifier(Q) :-
	atom(Q),
	!,
	format(latex, '\\~w ', [Q]).
latex_quantifier(Q) :-
	/* unknown: warn but output normally */
	format(user_error, '~N{Warning: unknown LaTeX output quantifier: ~w}~n', [Q]),
	format(latex, ' ~w ', [Q]).


latex_atom(A0) :-
	/* take care of Prolog atoms containing '_' */
	atomic_list_concat(List, '_', A0),
	atomic_list_concat(List, '\\_', A),
	format(latex, '\\textrm{~w}', [A]).

% = unary_term(+Term)
%
% if unary_term(Term) is true of their argument, the unary connectives pi1,
% pi2, neg, etc. will not put parentheses around this argument.

unary_term(pi1(_)).
unary_term(pi2(_)).
unary_term(neg(_)).
unary_term(possible(_)).
unary_term(necessary(_)).
unary_term(number_of(_)).
unary_term(quant(_,_,_)).
unary_term(true).
unary_term(false).
