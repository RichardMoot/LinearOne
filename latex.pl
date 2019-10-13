:- module(latex, [latex_proof/1,latex_nd/1,latex_hybrid/1,latex_displacement/1,proof_header/0,proof_footer/0,latex_semantics/1,latex_lexicon/1,latex_lexicon1/0,latex_it_atom/1,latex_arguments/1,latex_rm_atom/1,latex_it_atom/1]).

:- use_module(proof_generation, [eta_reduce/2]).
:- use_module(translations, [compute_pros_term/3,translate/3,translate_hybrid/6]).
:- use_module(lexicon, [macro_expand/2,canonical_semantic_term/2]).
:- use_module(options, [term_application/1,
			lexicon_separator/1,
			hybrid_connective/4,
			hybrid_epsilon/1,
			hybrid_concat/1,
			hybrid_item_start/1,
			hybrid_item_mid/1,
			hybrid_item_end/1,
			d_separator/1,
			d_concat/1,
			d_epsilon/1,
			output_indices/1,
			geometry/1,
			eta_short/1]).

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

lexicon_header :-
   ( stream_property(Stream, alias(latex)) -> close(Stream) ; true),
      ( exists_file('lexicon.tex') -> delete_file('lexicon.tex') ; true),
	open('lexicon.tex', write, _Stream, [alias(latex)]),
	format(latex, '\\documentclass[leqno,fleqn]{article}~2n', []),
	geometry(Geometry),
	format(latex, '\\usepackage[~p]{geometry}~n', [Geometry]),
	format(latex, '\\usepackage{proof}~n', []),
	format(latex, '\\usepackage{amsmath}~n', []),
	format(latex, '\\usepackage{amssymb}~2n', []),
	format(latex, '\\begin{document}~2n', []),
	format(latex, '\\begin{align*}~n', []).

lexicon_footer :-
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

% = latex_lexicon1
%
% abbreviates latex_lexicon(mill1); outputs the current lexicon as first-order linear logic formulas, translating
% displacement calculus, hybrid type-logical grammar and Lambek calculus entries when required.

latex_lexicon1 :-
	latex_lexicon(mill1).

% = latex_lexicon(+GrammarType)
%
% Grammar type must be one of d, displacement, mill1, hybrid
% outputs the grammar in the format indicated by the grammar type.

% displacement calculus

latex_lexicon(displacement) :-
	latex_lexicon(d).

latex_lexicon(d) :-
	lexicon_header,
    (	
	current_predicate(lex/3)
    ->			    
        findall(d_lex(X,Y,Z), lex(X,Y,Z), List)
    ;
        List = []
    ),
        latex_lexicon_d(List),
	lexicon_footer.

% first-order linear logic

latex_lexicon(mill1) :-
	lexicon_header,
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
    (	
	current_predicate(lex/5)
    ->			    
        findall(ll1_lex(X,Y,Z), lex(X,Y,l,r,Z), List3)
    ;
        List3 = []
    ),
        append(List1, List2, List12),
        append(List12, List3, List),
	latex_lexicon_list(List),
	lexicon_footer.

% hybrid type-logical grammars
%
% treat "acg" and "lambda" as "hybrid".

latex_lexicon(acg) :-
	latex_lexicon(hybrid).
latex_lexicon(lambda) :-
	latex_lexicon(hybrid).

latex_lexicon(hybrid) :-
	lexicon_header,
    (
	current_predicate(lex/4)
    ->
        findall(hybrid_lex(X,Y,Z,V), lex(X,Y,Z,V), List)
    ;
        List = []
    ),     
	latex_lexicon_hybrid(List),
	lexicon_footer.

% = latex_lexicon_d(+ListOfEntries)
%
% output ListOfEntries as Displacement calculus lexical entries

latex_lexicon_d([]).
latex_lexicon_d([d_lex(A,B,C)|As]) :-
	latex_d_item(A,B,C),
	latex_lexicon_d(As).

latex_d_item(Word, Formula0, Semantics0) :-
	macro_expand(Formula0, Formula),
	lexicon_separator(Sep),
	canonical_semantic_term(Semantics0, Semantics),
	numbervars(Semantics, 0, _),
	!,
	format(latex, '~@ &~w ~@ ~w ~@\\\\~n', [latex_rm_atom(Word), Sep, latex_d_formula(Formula), Sep, latex_semantics(Semantics,0)]).
	
% = latex_lexicon_list(+ListOfEntries)
%
% output ListOfEntries as first-order linear logic lexical entries

latex_lexicon_list([]).
latex_lexicon_list([A|As]) :-
	latex_mill1_item(A),
	latex_lexicon_list(As).

latex_mill1_item(hybrid_lex(Word,Formula0,ProsTerm,Semantics0)) :-
	macro_expand(Formula0, Formula1),
	translate_hybrid(Formula1, ProsTerm, Word, l, r, Formula),
	canonical_semantic_term(Semantics0, Semantics),
	numbervars(Formula, 0, _),
	numbervars(Semantics, 0, _),
	lexicon_separator(Sep),
	!,
	format(latex, '~@ &~w ~@ ~w ~@\\\\~n', [latex_rm_atom(Word), Sep, latex_formula(Formula), Sep, latex_semantics(Semantics,0)]).
latex_mill1_item(mill1_lex(Word,Formula0,Semantics0)) :-
	macro_expand(Formula0, Formula1),
	try_translate(Formula1, Formula),
	canonical_semantic_term(Semantics0, Semantics),
	numbervars(Formula, 0, _),
	numbervars(Semantics, 0, _),
	lexicon_separator(Sep),
	!,
	format(latex, '~@ &~w ~@ ~w ~@\\\\~n', [latex_rm_atom(Word), Sep, latex_formula(Formula), Sep, latex_semantics(Semantics,0)]).
latex_mill1_item(ll1_lex(Word,Formula0,Semantics0)) :-
	macro_expand(Formula0, Formula),
	canonical_semantic_term(Semantics0, Semantics),
	numbervars(Formula, 0, _),
	numbervars(Semantics, 0, _),
	lexicon_separator(Sep),
	!,
	format(latex, '~@ &~w ~@ ~w ~@\\\\~n', [latex_rm_atom(Word), Sep, latex_formula(Formula), Sep, latex_semantics(Semantics,0)]).

% = latex_lexicon_hybrid(+ListOfEntries)
%
% output ListOfEntries as hybrid type-logical grammars lexical entries

latex_lexicon_hybrid([]).
latex_lexicon_hybrid([hybrid_lex(A,B,C,D)|As]) :-
	latex_lexical_entry(A, B, C, D),
	latex_lexicon_hybrid(As).

latex_lexical_entry(mill1_lex(Word,Formula0,Semantics0)) :-
	macro_expand(Formula0, Formula1),
	try_translate(Formula1, Formula),
	canonical_semantic_term(Semantics0, Semantics),
	numbervars(Semantics, 0, _),
	lexicon_separator(Sep),
	!,
	format(latex, '~@ &~w ~@ ~w ~@\\\\~n', [latex_rm_atom(Word), Sep, latex_formula(Formula), Sep, latex_semantics(Semantics,0)]).
latex_lexical_entry(Word, Formula0, ProsTerm0, SemTerm0) :-
	macro_expand(Formula0, Formula),
	/* prevent strange behavior when a variable is shared between the prosodic term */
	/* and the semantic term (otherwise, the behavior is correct under the Prolog */
	/* meaning of bound variables, but very unlikely what the grammar writer intended) */
	/* NOTE: best practice is still to use a different set of variables for the prosodic */
	/* term and the semantic term */
	canonical_semantic_term(SemTerm0, SemTerm),
	numbervars(SemTerm, 0, _),
	compute_pros_term(ProsTerm0, Formula, ProsTerm),
	lexicon_separator(Sep),
	!,
	format(latex, '~@ &~w ~@ ~w ~@ ~w ~@\\\\~n', [latex_rm_atom(Word),Sep,latex_hybrid_formula(Formula),Sep,latex_pros_term(ProsTerm),Sep,latex_semantics(SemTerm,0)]). 


try_translate(Formula0, Formula) :-
	translate(Formula0, [l,r], Formula),
	!.
try_translate(Formula, Formula).

% = latex_proof(+Proof)
%
% produces LaTeX output of Proof to the stream "latex".

latex_proof(Proof0) :-
	copy_term(Proof0, Proof),
	numbervars(Proof, 0, _),
        format(latex, '\\[~n', []),
	latex_proof(Proof, 0),
        format(latex, '\\]~n\\bigskip~n', []).

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
latex_rule_name(dre(W)) :-
	format(latex, '\\uparrow_{~w} E', [W]).
latex_rule_name(dle(W)) :-
	format(latex, '\\downarrow_{~w} E', [W]).
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
latex_rule_name(dri(_)) :-
	format(latex, '/ I', []),
	!.
latex_rule_name(dli(_)) :-
	format(latex, '\\backslash I', []),
	!.
latex_rule_name(dri) :-
	format(latex, '/ I', []),
	!.
latex_rule_name(dli) :-
	format(latex, '\\backslash I', []),
	!.
latex_rule_name(bridge_i) :-
	format(latex, '\\,\\hat{\\,} I', []).
latex_rule_name(rproj_e) :-
	format(latex, '\\triangleright^{-1} E', []).
latex_rule_name(lproj_e) :-
	format(latex, '\\triangleleft^{-1} E', []).

latex_rule_name_i(ii(I)) :-
	format(latex, '\\multimap I_{~w}', [I]),
	!.
latex_rule_name_i(dri(I)) :-
	format(latex, '/ I_{~w}', [I]),
	!.
latex_rule_name_i(dli(I)) :-
	format(latex, '\\backslash I_{~w}', [I]),
	!.
latex_rule_name_i(dri(D,I)) :-
	format(latex, '\\uparrow_{~w} I_{~w}', [D,I]),
	!.
latex_rule_name_i(dli(D,I)) :-
	format(latex, '\\downarrow_{~w} I_{~w}', [D,I]),
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
	copy_term(Proof0, Proof1),
	numbervars(Proof1, 0, _),
	eta_reduce(Proof1, Proof),
        format(latex, '\\[~n', []),
	latex_nd(Proof, 0),
        format(latex, '\\]~n\\bigskip~n', []).

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

latex_hybrid(Proof0) :-
	eta_reduce(Proof0, Proof),
        format(latex, '\\[~n', []),
	latex_hybrid(Proof, 0),
        format(latex, '\\]~n\\bigskip~n', []).

latex_hybrid(_-Proof, Tab) :-
        latex_hybrid(Proof, Tab).
latex_hybrid(rule(Name, Term, Formula, SubProofs), Tab) :-
	latex_hybrid(SubProofs, Name, Term, Formula, Tab).

latex_hybrid([], Name, Term, Formula, _Tab) :-
     ( Name = hyp(I) ->  format(latex, '\\left [ ~@\\right ]^{~w} ', [latex_hybrid_item(Term,Formula),I]) ; format(latex, '~@ ', [latex_hybrid_item(Term,Formula)])).
latex_hybrid([S|Ss], Name, Term, Formula, Tab0) :-
	format(latex, '\\infer[~@]{~@}{', [latex_rule_name_i(Name),latex_hybrid_item(Term,Formula)]),
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

% = latex_hybrid_item

latex_hybrid_item(Pros, Formula) :-
	hybrid_item_start(HS),
	hybrid_item_mid(HM),
	hybrid_item_end(HE),
	format(latex, '~w~@~w~@~w ', [HS,latex_pros_term(Pros),HM,latex_hybrid_formula(Formula),HE]).

% = latex_pros_term(+Prosodics)
%
% output a prosodic term, as used in lambda grammars/ACGs and hybrid type-logical grammars to LaTeX

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

% = pros_variable_atom(+Number, -LaTeXAtom)
%
% translates a Number into a Prolog atom printed as a LaTeX variable with a subscript

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

% = latex_hybrid_formula(+Formula)
%
% outputs a formula of hybrid type-logical grammars to LaTeX

latex_hybrid_formula(F) :-
	latex_hybrid_formula(F, 0).
latex_hybrid_formula(at(A), _) :-
	latex_atom(A).
latex_hybrid_formula(at(F, Vs), _) :-
	format(latex, '~@~@', [latex_atom(F),latex_arguments(Vs)]).
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

% latex_displacement

latex_displacement(Proof0) :-
	eta_reduce(Proof0, Proof),
        format(latex, '\\[~n', []),
	latex_displacement(Proof, 0),
        format(latex, '\\]~n\\bigskip~n', []).

latex_displacement(_-Proof, Tab) :-
        latex_displacement(Proof, Tab).
latex_displacement(rule(hyp(I), Ant, Suc, []), _Tab) :-
	!,
	format(latex, '[~@\\vdash ~@]^{~w}~n', [latex_d_label(Ant),latex_d_formula(Suc),I]). 
latex_displacement(rule(ax, Ant, Suc, []), _Tab) :-
	!,
	format(latex, '~@\\vdash ~@~n', [latex_d_label(Ant),latex_d_formula(Suc)]). 
latex_displacement(rule(Name, Ant, Suc, SubProofs), Tab0) :-
	format(latex, '\\infer[~@]{~@ \\vdash ~@}{', [latex_rule_name_i(Name),latex_d_label(Ant),latex_d_formula(Suc)]),
	Tab is Tab0 + 6,
	latex_d_proofs(SubProofs, Tab),
	(SubProofs = [] -> true ; tab(latex,Tab0)),
        format(latex, '}~n', []).


latex_d_proofs([], _Tab).
latex_d_proofs([P|Ps], Tab) :-
	/* newline and tab only when there is at least one premiss */
	nl(latex),
	tab(latex, Tab),
	latex_d_proofs1(Ps, P, Tab).

latex_d_proofs1([], P, Tab) :-
	latex_displacement(P, Tab).
latex_d_proofs1([P|Ps], Q, Tab) :-
	latex_displacement(Q, Tab),
	tab(latex, Tab),
	format(latex, '&~n', []),
	tab(latex, Tab),
	latex_d_proofs1(Ps, P, Tab).


% = latex_d_label

latex_d_label([A|As]) :-
	latex_d_label1(As, A).

latex_d_label1([], A) :-
	latex_d_label_item(A).
latex_d_label1([B|Bs], A) :-
	latex_d_label_item(A),
	d_separator(Sep),
	write(latex, Sep),
	latex_d_label1(Bs, B).

latex_d_label_item([]) :-
	d_epsilon(Epsilon),
	write(latex, Epsilon).
latex_d_label_item([A|As]) :-
	latex_d_label_item1(As, A).

latex_d_label_item1([], A) :-
	latex_d_item(A).
latex_d_label_item1([B|Bs], A) :-
	latex_d_item(A),
	d_concat(Conc),
	write(latex, Conc),
	latex_d_label_item1(Bs, B).

latex_d_item('$VAR'(N)) :-
	!,
	/* shared with hybrid type-logical grammars */
	pros_variable_atom(N, At),
	write(latex, At).
latex_d_item(W) :-
	latex_atom(W).
	
% = latex_d_formula

latex_d_formula(F) :-
	latex_d_formula(F, 0).

latex_d_formula(at(A), _) :-
	latex_it_atom(A).
latex_d_formula(at(F, Vs), _) :-
	format(latex, '~@~@', [latex_it_atom(F),latex_arguments(Vs)]).
latex_d_formula(bridge(A), _) :-
	!,
	format(latex, '\\,\\hat{\\,}(~@ )', [latex_d_formula(A, 0)]).
latex_d_formula(lproj(A), _) :-
	!,
	format(latex, '\\triangleleft^{-1}( ~@ )', [latex_d_formula(A, 0)]).
latex_d_formula(rproj(A), _) :-
	!,
	format(latex, '\\triangleright^{-1}( ~@ )', [latex_d_formula(A, 0)]).
latex_d_formula(p(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\bullet ~@', [latex_d_formula(A, 1),latex_d_formula(B, 1)])
   ;
	format(latex, '(~@ \\bullet ~@)', [latex_d_formula(A, 1),latex_d_formula(B, 1)])
   ).
latex_d_formula(dl(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\backslash ~@', [latex_d_formula(A, 1),latex_d_formula(B, 1)])
   ;
	format(latex, '(~@ \\backslash ~@)', [latex_d_formula(A, 1),latex_d_formula(B, 1)])
   ).
latex_d_formula(dr(A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ / ~@', [latex_d_formula(A, 1),latex_d_formula(B, 1)])
   ;
	format(latex, '(~@ / ~@)', [latex_d_formula(A, 1),latex_d_formula(B, 1)])
   ).
latex_d_formula(p(K,A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\odot_{~w} ~@', [latex_d_formula(A, 1),K,latex_d_formula(B, 1)])
   ;
	format(latex, '(~@ \\odot_{~w} ~@)', [latex_d_formula(A, 1),K,latex_d_formula(B, 1)])
   ).
latex_d_formula(dl(K,A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\downarrow_{~w} ~@', [latex_d_formula(A, 1),K,latex_d_formula(B, 1)])
   ;
	format(latex, '(~@ \\downarrow_{~w} ~@)', [latex_d_formula(A, 1),K,latex_d_formula(B, 1)])
   ).
latex_d_formula(dr(K,A,B), NB) :-
	!,
   (
        NB =:= 0
   ->
	format(latex, '~@ \\uparrow_{~w} ~@', [latex_d_formula(A, 1),K,latex_d_formula(B, 0)])
   ;
	format(latex, '(~@ \\uparrow_{~w} ~@)', [latex_d_formula(A, 1),K,latex_d_formula(B, 1)])
   ).


% = latex_formula(+Formula)
%
% 

latex_formula(F) :-
	latex_formula(F, 0).

latex_formula(_-F, N) :-
	latex_formula(F, N).
latex_formula(at(F,Vs), _) :-
%	update_vars(Vs0, Vs),
	format(latex, '~@~@', [latex_atom(F),latex_arguments(Vs)]).
latex_formula(at(F,N,E,Vs), _) :-
  (	
	output_indices(yes)
  ->
	format(latex, '~@^{~p,~p}~@', [latex_atom(F),N,E,latex_arguments(Vs)])
  ;
	format(latex, '~@~@', [latex_atom(F),latex_arguments(Vs)])
  ).
latex_formula(forall(X,F), _) :-
	!,
   (
	is_quantified(F)
   ->
	format(latex, '\\forall ~@. ~@', [latex_var(X),latex_formula(F, 1)])
   ;
	format(latex, '\\forall ~@. [~@]', [latex_var(X),latex_formula(F, 0)])
   ).
latex_formula(exists(X,F), _) :-
	!,
   (
	is_quantified(F)
   ->
	format(latex, '\\exists ~@. ~@', [latex_var(X),latex_formula(F, 1)])
   ;
	format(latex, '\\exists ~@. [~@]', [latex_var(X),latex_formula(F, 0)])
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

latex_var(V) :-
    (
         V = var(M)
    ->
         variable_atom(M, W),
         write(latex, W)
    ;
         print(latex, V)
    ).


variable_atom(N, At) :-
	VN is N mod 5,
	VI is N//5,
	print_var1(VN, V),
	atomic_list_concat([V, '_{', VI, '}'], At).
    
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
	term_application(prolog_like),
	!,
	format(latex, '~@(~@,~@,~@)', [latex_atom(F),latex_semantics(X, 0),latex_semantics(Y, 0),latex_semantics(Z, 0)]).
latex_semantics(appl(appl(F,Y),X), _) :-
	atomic(F),
	term_application(prolog_like),
	!,
	format(latex, '~@(~@,~@)', [latex_atom(F),latex_semantics(X, 0),latex_semantics(Y, 0)]).
latex_semantics(appl(F,X), _) :-
	atomic(F),
	term_application(prolog_like),
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
latex_semantics(not(N), _NB) :-
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

latex_rm_atom(A0) :-
	/* take care of Prolog atoms containing '_' */
	atomic_list_concat(List, '_', A0),
	atomic_list_concat(List, '\\_', A),
	format(latex, '\\textrm{~w}', [A]).

latex_it_atom(A0) :-
	/* take care of Prolog atoms containing '_' */
	atomic_list_concat(List, '_', A0),
	atomic_list_concat(List, '\\_', A),
	format(latex, '\\textit{~w}', [A]).

latex_term(Term) :-
   (
	var(Term)
   ->
	format(latex, '\\_', [])
   ;
        integer(Term)
   ->
        write(latex,Term)
   ;
        Term = '$VAR'(_)
   ->
	print(latex, Term)
   ;
        Term = var(V)
   ->
	variable_atom(V, At),
	write(latex, At)
   ;			
	Term =.. [F|Args],
	latex_it_atom(F),
	latex_arguments(Args)
   ).

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
	latex_term(A).
latex_arguments([A|As], A0) :-
        format(latex, '~@, ', [latex_term(A0)]),
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
