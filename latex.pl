:- module(latex, [latex_proof/1,latex_nd/1,latex_hybrid/1,proof_header/0,proof_footer/0,latex_semantics/1,latex_lexicon/0]).

:- use_module(translations, [compute_pros_term/3]).
:- use_module(lexicon, [macro_expand/2]).

% =====================================================
% =          parameters for semantic output           =
% =====================================================

% set this option to "prolog_like" for a Prolog-like output; this will portray terms like
% ((f y) x) as f(x,y)

option(prolog_like).

%lexicon_separator(' - ').
lexicon_separator(' :: ').

% =====================================================
% = parameters for hybrid type-logical grammar output =
% =====================================================


% this option allows you to choose how to display the ACG/lambda grammar/hybrid type-logical
% grammar "|" or "-o" connective.
% A connective h(A,B) will be displayed by portraying, from left-to-right one of the
% subformulas (A or B) then a Prolog atom (passed to LaTeX directly), then the other
% subformula.

hybrid_connective(h(A,B), A, '|', B).             % hybrid type-logical grammar style
%hybrid_connective(h(A,B), B, '\\multimap ', A).   % ACG/lambda grammar style

hybrid_epsilon('\\epsilon').
hybrid_concat('\\circ').

% =====================================================
% =          parameters for axiom link trace          =
% =====================================================


% set this option to "yes" to ouput unique identifier indices of atomic formulas (useful for
% debugging)

%output_indices(yes).

output_indices(no).

% =====================================================
% =            parameters LaTeX paper size            =
% =====================================================

% the argument to the predicate geometry/1 is passed as an argument to the LaTeX geometry package.
% so very wide page lenghts are preset; comment out all but the desired choice.
% geometry(a2paper).
geometry(a1paper).
% geometry('paperwidth=200cm,textwidth=195cm').
% geometry('paperwidth=300cm,textwidth=295cm').
% geometry('paperwidth=400cm,textwidth=395cm').
% geometry('paperwidth=500cm,textwidth=495cm').

proof_header :-
      ( exists_file('latex_proofs.tex') -> delete_file('latex_proofs.tex') ; true),
	open('latex_proofs.tex', write, _Stream, [alias(latex)]),
	format(latex, '\\documentclass[leqno,fleqn]{article}~2n', []),
	geometry(Geometry),
	format(latex, '\\usepackage[~p]{geometry}~n', [Geometry]),
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
        /* find pdflatex in the user's $PATH */
	absolute_file_name(path(pdflatex), PdfLaTeX, [access(execute)]),
	process_create(PdfLaTeX, ['latex_proofs.tex'], [stdout(null)]),
	format('LaTeX proofs ready~n', [])
     ;
        format('LaTeX proof output failed~n', [])
     ).

% =

latex_lexicon :-
   ( stream_property(Stream, alias(latex)) -> close(Stream) ; true),
    (	
	current_predicate(lex/3)
    ->			    
        findall(mill1_lex(X,Y,Z), lex(X,Y,Z), List1)
    ;
        List1 = []
    ),
    (
	current_predicate(lex/4)
    ->
        findall(hybrid_lex(X,Y,Z,V), lex(X,Y,Z,V), List2)
    ;
        List2 = []
    ),     
        append(List1, List2, List),
      ( exists_file('lexicon.tex') -> delete_file('lexicon.tex') ; true),
	open('lexicon.tex', write, _Stream, [alias(latex)]),
	format(latex, '\\documentclass[leqno,fleqn]{article}~2n', []),
	geometry(Geometry),
	format(latex, '\\usepackage[~p]{geometry}~n', [Geometry]),
	format(latex, '\\usepackage{proof}~n', []),
	format(latex, '\\usepackage{amsmath}~n', []),
	format(latex, '\\usepackage{amssymb}~2n', []),
	format(latex, '\\begin{document}~2n', []),
	format(latex, '\\begin{align*}~n', []),
	latex_lexicon(List),
	format(latex, '\\end{align*}~2n', []),
	format(latex, '~n\\end{document}~n', []),
	close(latex),
    (
	access_file('lexicon.tex', read)
    ->
        /* find pdflatex in the user's $PATH */
	absolute_file_name(path(pdflatex), PdfLaTeX, [access(execute)]),
	process_create(PdfLaTeX, ['lexicon.tex'], [stdout(null)]),
	format('LaTeX lexicon ready~n', [])
     ;
        format('LaTeX lexicon output failed~n', [])
    ).

latex_lexicon([]).
latex_lexicon([A|As]) :-
	latex_lexical_entry(A),
	latex_lexicon(As).

latex_lexical_entry(mill1_lex(Word,Formula0,Semantics)) :-
	macro_expand(Formula0, Formula),
	numbervars(Semantics, 0, _),
	lexicon_separator(Sep),
	!,
	format(latex, '~w &~w ~@ ~w ~@\\\\~n', [Word, Sep, latex_formula(Formula), Sep, latex_semantics(Semantics,0)]).
latex_lexical_entry(hybrid_lex(Word, Formula0, ProsTerm0, SemTerm)) :-
	macro_expand(Formula0, Formula),
	numbervars(SemTerm, 0, _),
	compute_pros_term(ProsTerm0, Formula, ProsTerm),
	lexicon_separator(Sep),
	!,
	format(latex, '~w &~w ~@ ~w ~@ ~w ~@\\\\~n', [Word,Sep,latex_hybrid_formula(Formula),Sep,latex_pros_term(ProsTerm),Sep,latex_semantics(SemTerm,0)]). 
  
% = latex_proof(+Proof)
%
% produces LaTeX output of Proof to the stream "latex".

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

% = latex_rule_name(+RuleName)
%
% output RuleName to LaTeX stream "latex"

%latex_rule_name(ax) :-
%	write('Axiom').
% don't print "Axiom" to save space (replace by the code commented out above if you want the axioms to be explicitly named)
latex_rule_name(ax).
latex_rule_name(hyp(_)).
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
latex_rule_name(fi) :-
	write(latex, '\\forall I').
latex_rule_name(fe) :-
	write(latex, '\\forall E').
latex_rule_name(ei) :-
	write(latex, '\\exists I').
latex_rule_name(ee(_)) :-
	write(latex, '\\exists E').
latex_rule_name(ee) :-
	write(latex, '\\exists E').
latex_rule_name(ii) :-
	write(latex, '\\multimap I').
latex_rule_name(ii(_)) :-
	write(latex, '\\multimap I').
latex_rule_name(dre) :-
	write(latex, '/ E').
latex_rule_name(dle) :-
	write(latex, '\\backslash E').
latex_rule_name(he) :-
	hybrid_connective(_, _, C, _),
	format(latex, '~w E', [C]).
latex_rule_name(hi) :-
	hybrid_connective(_, _, C, _),
	format(latex, '~w I', [C]).
latex_rule_name(hi(_)) :-
	hybrid_connective(_, _, C, _),
	format(latex, '~w I', [C]).
latex_rule_name(ie) :-
	write(latex, '\\multimap E').
latex_rule_name(pi) :-
	write(latex, '\\otimes I').
latex_rule_name(pe) :-
	write(latex, '\\otimes E').
latex_rule_name(pe(_)) :-
	write(latex, '\\otimes E').
latex_rule_name_(dri(_)) :-
	format(latex, '/ I', []),
	!.
latex_rule_name_(dli(_)) :-
	format(latex, '\\backslash I', []),
	!.
latex_rule_name_(dri) :-
	format(latex, '/ I', []),
	!.
latex_rule_name_(dli) :-
	format(latex, '\\backslash I', []),
	!.

latex_rule_name_i(ii(I)) :-
	format(latex, '\\multimap I_{~w}', [I]),
	!.
latex_rule_name_i(dri(I)) :-
	format(latex, '/ I_{~w}', [I]),
	!.
latex_rule_name_i(dli(I)) :-
	format(latex, '\\backslash I_{~w}', [I]),
	!.
latex_rule_name_i(hi(I)) :-
	hybrid_connective(_, _, C, _),
	format(latex, '~w I_{~w}', [C,I]),
	!.
latex_rule_name_i(pe(I)) :-
	format(latex, '\\otimes E_{~w}', [I]),
	!.
latex_rule_name_i(ee(I)) :-
	format(latex, '\\exists E_{~w}', [I]),
	!.
latex_rule_name_i(Name) :-
	latex_rule_name(Name).

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


% = latex_nd(+Proof)
%
% this version of latex_proof output natural deduction proofs with implicit antecedents (and coindexing between rules and withdrawn hypotheses)

latex_nd(Proof0) :-
	copy_term(Proof0, Proof),
	numbervars(Proof, 0, _),
	latex_nd(Proof, 0),
        format(latex, '~n\\bigskip~n', []).

latex_nd(_-Proof, Tab) :-
        latex_nd(Proof, Tab).
latex_nd(rule(Name, _, Formula, SubProofs), Tab) :-
	latex_nd(SubProofs, Name, Formula, Tab).

latex_nd([], Name, Formula, _Tab) :-
     ( Name = hyp(I) ->  format(latex, '[~@]^{~w} ', [latex_formula(Formula),I]) ; format(latex, '~@ ', [latex_formula(Formula)])).
latex_nd([S|Ss], Name, Formula, Tab0) :-
	format(latex, '\\infer[~@]{~@}{', [latex_rule_name_i(Name),latex_formula(Formula)]),
	Tab is Tab0 + 6,
	nl(latex),
	tab(latex, Tab),
	latex_nds(Ss, S, Tab),
	tab(latex,Tab0),
        format(latex, '}~n', []).

latex_nds([], P, Tab) :-
	latex_nd(P, Tab).
latex_nds([P|Ps], Q, Tab) :-
	latex_nd(Q, Tab),
	tab(latex, Tab),
	format(latex, '&~n', []),
	tab(latex, Tab),
	latex_nds(Ps, P, Tab).


% = latex_hybrid(+Proof)
%
% this version of latex_proof outputs hybrid type-logical grammar natural deduction proofs (with implicit antecedents and coindexing between rules and withdrawn hypotheses)

latex_hybrid(Proof) :-
	latex_hybrid(Proof, 0),
        format(latex, '~n\\bigskip~n', []).

latex_hybrid(_-Proof, Tab) :-
        latex_hybrid(Proof, Tab).
latex_hybrid(rule(Name, Term, Formula, SubProofs), Tab) :-
	latex_hybrid(SubProofs, Name, Term, Formula, Tab).

latex_hybrid([], Name, Term, Formula, _Tab) :-
     ( Name = hyp(I) ->  format(latex, '[~@:~@]^{~w} ', [latex_pros_term(Term),latex_hybrid_formula(Formula),I]) ; format(latex, '~@:~@ ', [latex_pros_term(Term),latex_hybrid_formula(Formula)])).
latex_hybrid([S|Ss], Name, Term, Formula, Tab0) :-
	format(latex, '\\infer[~@]{~@:~@}{', [latex_rule_name_i(Name),latex_pros_term(Term),latex_hybrid_formula(Formula)]),
	Tab is Tab0 + 6,
	nl(latex),
	tab(latex, Tab),
	latex_hybrids(Ss, S, Tab),
	tab(latex,Tab0),
        format(latex, '}~n', []).

latex_hybrids([], P, Tab) :-
	latex_hybrid(P, Tab).
latex_hybrids([P|Ps], Q, Tab) :-
	latex_hybrid(Q, Tab),
	tab(latex, Tab),
	format(latex, '&~n', []),
	tab(latex, Tab),
	latex_hybrids(Ps, P, Tab).

latex_pros_term(epsilon) :-
	!,
	hybrid_epsilon(Epsilon),
	format(latex, '~w ', [Epsilon]).
latex_pros_term(A+B) :-
	!,
	hybrid_concat(Conc),
	format(latex, '~@ ~w ~@ ', [latex_pros_term(A),Conc,latex_pros_term(B)]).
latex_pros_term('$VAR'(N)) :-
	!,
	pros_variable_atom(N, At),
	write(latex, At).
latex_pros_term(Atom) :-
	atomic(Atom),
	!,
	latex_pros_atom(Atom).
latex_pros_term(lambda(X,Y)) :-
	!,
	format(latex, '\\lambda ~@ . ~@ ', [latex_pros_term(X),latex_pros_term(Y)]).
latex_pros_term(appl(X,Y)) :-
	!,
	format(latex, '(~@\\,~@)', [latex_pros_term(X),latex_pros_term(Y)]).


pros_variable_atom(N, At) :-
	VI is N mod 5,
	VN is N//5,
	print_pros_var1(VI, V),
	atomic_list_concat([V, '_{', VN, '}'], At).
    
print_pros_var1(0, p).
print_pros_var1(1, q).
print_pros_var1(2, r).
print_pros_var1(3, s).
print_pros_var1(4, t).

latex_pros_atom(A0) :-
	/* take care of Prolog atoms containing '_' */
	atomic_list_concat(List, '_', A0),
	atomic_list_concat(List, '\\_', A),
	format(latex, '\\textrm{~w}', [A]).

latex_hybrid_formula(F) :-
	latex_hybrid_formula(F, 0).
latex_hybrid_formula(at(A), _) :-
	print(latex,A).
latex_hybrid_formula(h(A,B), N) :-
	hybrid_connective(h(A,B), L, C, R),
   (
	N = 0
   ->
        format(latex, '~@~w~@ ', [latex_hybrid_formula(L,1),C,latex_hybrid_formula(R,1)])
   ;
        format(latex, '(~@~w~@)', [latex_hybrid_formula(L,1),C,latex_hybrid_formula(R,1)])
   ).
latex_hybrid_formula(dr(A,B), N) :-
   (
	N = 0
   ->
	format(latex, '~@/~@ ', [latex_hybrid_formula(A,1),latex_hybrid_formula(B,1)])
   ;
        format(latex, '(~@/~@)', [latex_hybrid_formula(A,1),latex_hybrid_formula(B,1)])
   ).
latex_hybrid_formula(dl(A,B), N) :-
   (
	N = 0
   ->
	format(latex, '(~@\\backslash ~@)', [latex_hybrid_formula(A,1),latex_hybrid_formula(B,1)])
   ;
        format(latex, '(~@\\backslash ~@)', [latex_hybrid_formula(A,1),latex_hybrid_formula(B,1)])
   ).

% = latex_formula(+Formula)
%
% 

latex_formula(F) :-
	latex_formula(F, 0).

latex_formula(_-F, N) :-
	latex_formula(F, N).
latex_formula(at(F,Vs0), _) :-
	update_vars(Vs0, Vs),
	Term =.. [F|Vs],
	print(latex, Term).
latex_formula(at(F,N,E,Vs0), _) :-
	update_vars(Vs0, Vs),
  (	
	output_indices(yes)
  ->
	format(latex, '~@^{~p,~p}~@', [latex_atom(F),N,E,latex_arguments(Vs)])
  ;
	format(latex, '~@~@', [latex_atom(F),latex_arguments(Vs)])
  ).
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

% = latex_semantics(+LambdaTerm)
%
% output LambdaTerm to LaTeX stream "latex
% supports several convenient abbreviations to make the output look more like first-order/higher-order logic

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
	format(latex, ' | ~@ |', [latex_semantics(A, 0)]).
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

% = latex_atom(+PrologAtom)
%
% output a Prolog atom to LaTeX, giving some constants (forall/exists/iota)
% special treatment and taking care of underscores to help LaTeX process them

latex_atom(forall) :-
	!,
	format(latex, '\\forall ', []).
latex_atom(exists) :-
	!,
	format(latex, '\\exists ', []).
latex_atom(iota) :-
	!,
	format(latex, '\\iota ', []).
latex_atom(epsilon) :-
	!,
	format(latex, '\\epsilon ', []).
latex_atom(tau) :-
	!,
	format(latex, '\\tau ', []).
latex_atom(A0) :-
	/* take care of Prolog atoms containing '_' */
	atomic_list_concat(List, '_', A0),
	atomic_list_concat(List, '\\_', A),
	format(latex, '\\textrm{~w}', [A]).

% = latex_arguments(+ListOfArguments)
%
% write a list of arguments to a predicate ie. (t_1, t_2, t3) sending
% each t_i to print and outputing nothing for a proposition (ie. the
% empty list of arguments.

latex_arguments([]).
latex_arguments([A|As]) :-
	write(latex, '('),
	latex_arguments(As, A),
        write(latex, ')').

latex_arguments([], A) :-
	print(latex, A).
latex_arguments([A|As], A0) :-
	format(latex, '~w, ', [A0]),
	latex_arguments(As, A).

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
unary_term(quant(_, _, _)).
unary_term(true).
unary_term(false).
