:- module(proof_generation, [generate_proof/2,
			     generate_sequent_proof/2,
			     generate_natural_deduction_proof/2,
			     generate_nd_proof/2,
			     generate_displacement_proof/2,
			     generate_hybrid_proof/2]).

:- use_module(latex,        [latex_proof/1,
			     latex_nd/1,
			     latex_hybrid/1,
			     latex_displacement/1]).
:- use_module(replace,      [rename_bound_variable/4,
			     rename_bound_variables/2,
			     replace_proofs_labels/4]).
:- use_module(auxiliaries,  [select_formula/4,
			     subproofs/2,
			     rulename/2,
			     is_axiom/1,
			     antecedent/2,
			     identical_prefix/3,
			     identical_postfix/3,
			     identical_lists/2,
			     split_list/4]).
:- use_module(translations, [linear_to_hybrid/2,
			     linear_to_hybrid/3,
			     linear_to_hybrid/4,
			     linear_to_lambek/3,
			     linear_to_displacement/3,
			     displacement_sort/2,
			     simple_to_pure/4,
			     pure_to_simple/3,
			     compute_pros_term/5,
			     formula_type/2]).

:- dynamic free_var/2, d_hyp/2.

% set this flag to true to obtain a proof trace of the sequent proof generation
%
%generate_diagnostics(true).
generate_diagnostics(false).

% =======================================
% =           Proof generation          =
% =======================================

% = generate_sequent_proof(+InitialGraph, +ProofTrace)
%
% generate a sequent proof from the initial graph and proof trace
% given as arguments, and set the output to LaTeX.

generate_sequent_proof(Graph, Trace) :-
	node_proofs(Graph, Proofs),
	combine_proofs(Trace, Proofs, Proof),
	latex_proof(Proof).


% = generate_natural_deduction_proof(+InitialGraph, +ProofTrace)
%
% generate a natural deduction proof from the initial graph and proof trace
% given as arguments, and set the output to LaTeX.

generate_natural_deduction_proof(Graph, Trace) :-
	node_proofs(Graph, Proofs),
	combine_proofs(Trace, Proofs, Proof),
	sequent_to_nd(Proof, NDProof),
	latex_proof(NDProof).

% = generate_nd_proof(+InitialGraph, +ProofTrace)
%
% as generate_natural_deduction_proof/2, but output the natural deduction
% proof with implicit antecedents and explicit hypothesis cancellation.

generate_nd_proof(Graph, Trace) :-
	node_proofs(Graph, Proofs),
	combine_proofs(Trace, Proofs, Proof),
	sequent_to_nd(Proof, NDProof),
	latex_nd(NDProof).

% = generate_hybrid_proof(+InitialGraph, +ProofTrace)
%
% generate a proof in hybrid type-logical grammars based on the first-order
% linear logic proof. This predicate presupposed the lexical entries are
% all hybrid lexical entries.

generate_hybrid_proof(Graph, Trace) :-
	node_proofs(Graph, Proofs),
	combine_proofs(Trace, Proofs, Proof),
	sequent_to_nd(Proof, NDProof),
	nd_to_hybrid(NDProof, HProof),
	latex_hybrid(HProof).

% = generate_displacement_proof(+InitialGraph, +ProofTrace)
%
% generate a displacement calculus proof (in natural deduction)
% from the first-order natural deduction proof

generate_displacement_proof(Graph, Trace) :-
	node_proofs(Graph, Proofs),
	combine_proofs(Trace, Proofs, Proof),
	sequent_to_nd(Proof, NDProof),
	latex_nd(NDProof),
	nd_to_displacement(NDProof, DProof),
	latex_displacement(DProof).

% = generate_proof(+InitialGraph, +ProofTrace)
%
% generate a sequent proof, natural deduction proof and hybrid proof of the
% same (hybrid) sequent.

generate_proof(Graph, Trace) :-
	node_proofs(Graph, Proofs),
	combine_proofs(Trace, Proofs, Proof),
	sequent_to_nd(Proof, NDProof),
    (
        /* use presence of (hybrid grammar) lex/4 predicate as indication */
	/* that the current grammar is a hybrid grammar */    
	current_predicate(lex/4)
    ->	
	nd_to_hybrid(NDProof, HProof),
	latex_hybrid(HProof)
     ;
        true
     ),
	latex_nd(NDProof),
	latex_proof(Proof).

combine_proofs([], [Proof], Proof).
combine_proofs([N0-par(N1)|Rest], Ps0, Proof) :-
	selectchk(N0-P0, Ps0, Ps1),
	selectchk(N1-P1, Ps1, Ps2),
	combine(P0, P1, N0, N1, P2),
	replace_proofs_labels([P2|Ps2], N0, N1, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([N0-univ(V,N1)|Rest], Ps0, Proof) :-
        selectchk(N0-P0, Ps0, Ps1),
	selectchk(N1-P1, Ps1, Ps2),
	combine_univ(P0, P1, N0, N1, V, P2),
	replace_proofs_labels([P2|Ps2], N0, N1, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([ax(N1,AtV1,AtO1,N0,AtV0,AtO0)|Rest], Ps0, Proof) :-
	select_neg_axiom(Ps0, Ps1, AtV1, AtO1, _-CL, A, _-LeftProof),
	A = _-at(_, AtV0, AtO0, _),
	proof_diagnostics('~NNeg (~D) ~D,~D:~2n', [N0, AtV0,AtO0], LeftProof),
	select_pos_axiom(Ps1, Ps2, AtV0, AtO0, Gamma, _-CR, _-RightProof),
	Gamma = [_-at(_, AtV1, AtO1, _)],
	proof_diagnostics('~NPos (~D) ~D,~D:~2n', [N1, AtV1, AtO1], RightProof),
	RightProof = rule(_, Ant, D, _),
	LeftProof = rule(_, Gamma0, _, _),
	split_antecedent(Ant, AtV1, AtO1, Delta1, Delta2),
        append(Delta1, Gamma0, GDP1),
	append(GDP1, Delta2, GDP),
	print_diagnostics('~NUnifier: ~@~2n', [print_unifier(CL,CR)]),
	unify_atoms(_-CL, _-CR),
	try_cut_elimination_right(LeftProof, RightProof, GDP, D, Gamma0, _-CL, _-CR, Rule),
	proof_diagnostics('~NResults (~D):~2n', [N0], Rule),
	diagnostics_rule,
	replace_proofs_labels([N0-Rule|Ps2], N1, N0, Ps),
	!,
	combine_proofs(Rest, Ps, Proof).
combine_proofs([Next|_], CurrentProofs, Proof) :-
	/* dump all partial proofs in case of failure (useful for inspection) */
	format(user_error, '~N{Error: proof generation failed!}~nNext:~p~2n', [Next]),
	numbervars(CurrentProofs, 0, _),
	keysort(CurrentProofs, SortedProofs),
	/* exploits the fact that the top-level is a failure-driven loop */
	member(N-Proof, SortedProofs),
        format(latex, '~2n ~D. ', [N]).

% = split_antecedent(+GammaADelta, +V, +O, Gamma, Delta)
%
% split antecedent GammaADelta at the atomic formula indicated by identifier V, O returning
% the formulas before it in Gamma and thos after it in Delta.

split_antecedent([A|As], V, O, Bs, Delta) :-
   (
	A = _-at(_,AtV,AtO,_),
	AtV == V,
	AtO == O
   ->		       
        Bs = [],
	Delta = As
   ;			
        Bs = [A|Bs0],
        split_antecedent(As, V, O, Bs0, Delta)
   ).			

% = split_antecedent(+GammaADelta, +A, Gamma, Delta)
%
% split antecedent GammaADelta at the formula A returning
% the formulas before it in Gamma and thos after it in Delta.

split_antecedent([A0|As], A, Bs, Delta) :-
   (
        same_formula(A0, A)		
    ->
	Bs = [],
	Delta = As
    ;
        Bs = [A0|Bs0],
        split_antecedent(As, A, Bs0, Delta)
    ).
    
% = trivial_cut_elimination(+LeftSubProof, +RightSubProof, +ConclusionAntecedent, +ConclusionSuccedent, -NewProof)

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

% = try_cut_elimination_left(+LeftProof, +RightProof, +GammaDelta, +Delta1, +Delta2, +A, +CL, +CR, -Proof)
%
% try to perform cut elimination of C (occurring as CL in LeftProof and as CR in RightProof) obtaining a Proof
% which conclusion GammaDelta |- A.
% More specifically, the RightProof has conclusion Delta1, CR, Delta2 |- A, LeftProof has conclusion Gamma |- CL
% and GammaDelta is equal to Delta1, Gamma, Delta2

try_cut_elimination_left(LeftProof, RightProof, GammaDelta, Delta1, Delta2, A, _-CL, _-CR, Proof) :-
	turbo_cut_elimination_left(LeftProof, RightProof, Delta1, Delta2, A, CL, CR, Proof0),
	!,
	rulename(LeftProof, LeftN),
	rulename(RightProof, RightN),
	update_proof_cheat(Proof0, GammaDelta, A, Proof, LeftN, RightN).
try_cut_elimination_left(LeftProof, RightProof, GammaDelta, _, _, A, _, _, rule(cut, GammaDelta, A, [LeftProof,RightProof])).

% = try_cut_elimination_right(+LeftProof, +RightProof, +GammaDelta, +A, +Gamma, +CL, +CR, -Proof)
%
% try to perform cut elimination of C (occurring as CL in LeftProof and as CR in RightProof) obtaining a Proof
% with conclusion GammaDelta |- A.
% The subproofs are of Gamma |- CL and of  Delta1, CR, Delta2 |- A

try_cut_elimination_right(LeftProof, RightProof, GammaDelta, A, Gamma, _-CL, _-CR, Proof) :-
	turbo_cut_elimination_right(RightProof, LeftProof, Gamma, CL, CR, Proof0),
	!,
	rulename(LeftProof, LeftN),
	rulename(RightProof, RightN),
	update_proof_cheat(Proof0, GammaDelta, A, Proof, LeftN, RightN).
try_cut_elimination_right(LeftProof, RightProof, GammaDelta, A, _Gamma, _CL, _CR, rule(cut, GammaDelta, A, [LeftProof,RightProof])).

% = as the name indicates, this predicate needs to be subsumed by the main cut elimination predicates later

update_proof_cheat(rule(Nm, Gamma0, _, Rs), Gamma, A, rule(Nm, Gamma, A, Rs), LeftN, RightN) :-
   (	
	generate_diagnostics(true),
	Gamma0 \= Gamma
    ->
        format(user_error, '~n= Computed ~w ~w =~n', [LeftN,RightN]),
	print_antecedent(Gamma0),
        format(user_error, '~n= Correct =~n', []),	
	print_antecedent(Gamma)    
    ;
        true
    ).		   


print_antecedent(Ant) :-
	print_antecedent(Ant, 0).

print_antecedent([], _).
print_antecedent([A|As], N0) :-
	copy_term(A, AA),
	numbervars(AA, N0, N),
	format(user_error, '~p~n', [AA]),
	print_antecedent(As, N).
	
%                      CL |- CL             Gamma |- CR
%                         .                       .
%                         .                       .
%  Gamma |- CR  Delta, CL |- A        Gamma, Delta |- A
%
% the proof on the left keeps CL constant in its right branch; in the proof of the right, we replace
% CL by Gamma throughout (and CL in the succedent by CR).

turbo_cut_elimination_left(rule(Nm, Gamma, _-CL, Rs0), RightProof, Delta1, Delta2, A, CL, CR, Proof) :-
    (
        Gamma = [_-CL], Rs0 = []
    ->
	/* reached axiom */     
	Proof = RightProof    
    ;				      		
        /* add Delta to Gamma and replace CL by A */
        append(Delta1, Gamma, GammaDelta1),
	append(GammaDelta1, Delta2, GammaDelta),
	Proof = rule(Nm, GammaDelta, A, Rs),
	turbo_cut_elimination_left1(Rs0, RightProof, Delta1, Delta2, A, CL, CR, Rs)
    ).

turbo_cut_elimination_left1([R0|Rs0], RightProof, Delta1, Delta2, A, CL0, CR, [R|Rs]) :-
    (
	R0 = rule(_, _,_-CL, _),
	same_formula1(CL0, CL)
    ->
	Rs = Rs0,
	turbo_cut_elimination_left(R0, RightProof, Delta1, Delta2, A, CL, CR, R)
    ;		     
        R = R0,
        turbo_cut_elimination_left1(Rs0, RightProof, Delta1, Delta2, A, CL0, CR, Rs)
    ).

%     CR |- CR                               Delta, CL |- A
%        .                                             .
%        .                                             .
%  Gamma |- CR  Delta, CL |- A            Delta, Gamma |- A
%
% the proof on the left transforms CR to Gamma without changing the succedent; we can
% use this same sequence of rules on the right to transform (replace) CL by the
% successive antecedents of the left proof

turbo_cut_elimination_right(rule(Nm, Delta, A, Rs0), LeftProof, Gamma, CL, CR, Proof) :-
    (
        Delta = [_-CL0], same_formula1(CL0, CL), Rs0 = []
    ->
	/* reached axiom */     
	Proof = LeftProof    
    ;				      		
        /* replace CL in the antecedent by Gamma */
        split_antecedent(Delta, _-CL, Delta1, Delta2),
	%append(Delta1, [_-CL|Delta2], Delta),
	append(Delta1, Gamma, GammaDelta1),
	append(GammaDelta1, Delta2, GammaDelta),
	Proof = rule(Nm, GammaDelta, A, Rs),
	turbo_cut_elimination_right1(Rs0, LeftProof, Gamma, CL, CR, Rs)
    ).

% = proceed to the subproof containing CR
turbo_cut_elimination_right1([R0|Rs0], LeftProof, Gamma, CL0, CR, [R|Rs]) :-
    (
	antecedent_member(CL0, CL, R0)
    ->
	Rs = Rs0,
	turbo_cut_elimination_right(R0, LeftProof, Gamma, CL, CR, R)
    ;		     
        R = R0,
        turbo_cut_elimination_right1(Rs0, LeftProof, Gamma, CL0, CR, Rs)
    ).

antecedent_member(F, rule(_, Gamma, _, _)) :-
	antecedent_member(F, _, Gamma).

antecedent_member(F0, F, rule(_, Gamma, _, _)) :-
	antecedent_member1(Gamma, F0, F).

antecedent_member1([_-G|Gs], F0, F) :-
   (
	same_formula1(F0, G)
   ->
        F = G
   ;		       
        antecedent_member1(Gs, F0, F)
   ).

% = combine_univ(+Proof1, +Proof2, +Node1, +Node2, +VariableNumber, -Proof)
%
% combine Proof1 and Proof2 into Proof using a unary par contraction (with eigenvariable
% VariableNumber) which links Node1 to Node2

% = left rule for existential quantifier
combine_univ(P1, P2, N0, N1, V, N1-Rule) :-
        P1 = rule(_, Gamma, N0-exists(var(V),N1-A), _),
	P2 = rule(_, Delta0, C, _),
	!,
	/* TODO: guarantee this is the same formula occurrence, split_antecedent is too strict of a condition */
	/* Q: are the node numbers enough to guarantee this? Verify! */
	append(Delta1, [N1-A|Delta2], Delta0),
	%split_antecedent(Delta0, _-A, Delta1, Delta2), 
	append(Delta1, [N1-exists(var(V),N1-A)|Delta2], Delta),
	append(Delta1, Gamma, GD1),
	append(GD1, Delta2, GD),
	/* try to create a cut-free proof */
	try_cut_elimination_left(P1, rule(el, Delta, C, [P2]), GD, Delta1, Delta2, C, N0-exists(var(V),N1-A), N0-exists(var(V),N1-A), Rule).

% = right rule for universal quantifier
combine_univ(P1, P2, N0, N1, V, N1-Rule) :-
        P2 = rule(_, Gamma, N1-A, _),
	P1 = rule(_, Delta, C, _),
	/* TODO: guarantee this is the same formula occurrence, split_antecedent is too strict of a condition */
	/* Q: are the node numbers enough to guarantee this? Verify! */
	append(Delta0, [N0-forall(var(V),N1-A)|Delta1], Delta),
	%split_antecedent(Delta, _-forall(var(V),N1-A), Delta0, Delta1),
	append(Delta0, Gamma, GD0),
	append(GD0, Delta1, GD),
	/* try to create a cut-free proof */
	try_cut_elimination_right(rule(fr,Gamma,N1-forall(var(V),N1-A), [P2]), P1, GD, C, Gamma, N0-forall(var(V),N1-A), N0-forall(var(V),N1-A), Rule).

% = combine(+Proof1, +Proof2, +Node1, +Node2, -Proof)
%
% combine Proof1 and Proof2 into Proof using a binary par contraction which links Node1
% to Node2 (since this is a valid contraction, the two edges leaving Node1 must arrive
% in the same node Node2)

% = left rule for product
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(_, Gamma, N0-p(N1-A, N1-B), _),
        P2 = rule(_, Delta0, C, _),
	!,
	/* TODO: guarantee this is the same formula occurrence, split_antecedent is too strict of a condition */
	/* Q: are the node numbers enough to guarantee this? Verify! */
	select_same_formula(N1, B, Delta0, Delta1),
	select_same_formula(N1, A, Delta1, Delta),
	replace_formula(A, N1, N1-p(N1-A,N1-B), Delta1, Delta2),
	append(Delta3, [N1-p(N1-A,N1-B)|Delta4], Delta2),
	append(Gamma, Delta, GD),		  
	/* try to create a cut-free proof */
	try_cut_elimination_left(P1, rule(pl, Delta2, C, [P2]), GD, Delta3, Delta4, C, N0-p(N1-A, N1-B), N0-p(N1-A, N1-B), Rule).

% = right rule for implication
combine(P1, P2, N0, N1, N1-Rule) :-
	P1 = rule(_, Gamma, A, _),
	P2 = rule(_, Delta0, N1-D, _),	
	/* TODO: guarantee this is the same formula occurrence, split_antecedent is too strict of a condition */
	/* Q: are the node numbers enough to guarantee this? Verify! */
	append(Gamma0, [N0-impl(N1-C,N1-D)|Gamma1], Gamma),
%	split_antecedent(Gamma, N0-impl(N1-C,N1-D), Gamma0, Gamma1),
	select_same_formula(N1, C, Delta0, Delta),
	append(Gamma0, Delta, GD0),
	append(GD0, Gamma1, GD),
	/* try to create a cut-free proof */
	try_cut_elimination_right(rule(ir, Delta, N0-impl(N1-C,N1-D), [P2]), P1, GD, A, Delta, N0-impl(N1-C,N1-D), N0-impl(N1-C,N1-D), Rule).

% = unify_atoms(+Atom1, +Atom2)
%
% true if Atom1 and Atom2 unify when disregarding the unique two-integer
% identifiers

unify_atoms(_-at(A, _, _, Vs), _-at(A, _, _, Vs)).

% = same_formula(+Formula1, +Formula2)
%
% true if Formula1 and Formula2 are the same when disregarding the subformula
% numbering

same_formula(_-F0, _-F) :-
	same_formula1(F0, F).

same_formula1(F0, F) :-
	/* variable subformulas unify */
	var(F0),
        !,
	F0 = F.
same_formula1(F0, F) :-
	var(F),
	!,
	F = F0.
same_formula1(at(A,Id1,Id2,_), at(A,Id3,Id4,_)) :-
	/* demand strict identity of atoms */
	Id1 == Id3,
	Id2 == Id4.
same_formula1(forall(X,F0), forall(Y,F)) :-
	X == Y,
	same_formula(F0, F).
same_formula1(exists(X,F0), exists(Y,F)) :-
	X == Y,
	same_formula(F0, F).
same_formula1(impl(A0,B0), impl(A,B)) :-
	same_formula(A0, A),
	same_formula(B0, B).
same_formula1(p(A0,B0), p(A,B)) :-
	same_formula(A0, A),
	same_formula(B0, B).

%

same_formula2(F0, F) :-
	/* variable subformulas unify */
	var(F0),
        !,
	F0 = F.
same_formula2(F0, F) :-
	var(F),
	!,
	F = F0.
same_formula2(at(A,Id1,Id2,Vs), at(A,Id3,Id4,Vs)) :-
	/* demand strict identity of atoms and unify variables */
	Id1 == Id3,
	Id2 == Id4.
same_formula2(forall(X,_-F0), forall(Y,_-F)) :-
	X = Y,
	same_formula2(F0, F).
same_formula2(exists(X,_-F0), exists(Y,_-F)) :-
	X = Y,
	same_formula2(F0, F).
same_formula2(impl(_-A0,_-B0), impl(_-A,_-B)) :-
	same_formula2(A0, A),
	same_formula2(B0, B).
same_formula2(p(_-A0,_-B0), p(_-A,_-B)) :-
	same_formula2(A0, A),
	same_formula2(B0, B).


%

select_same_formula(N, F, L0, L) :-
	select(N-F0, L0, L),
	same_formula2(F0, F),
	!.

% = select_neg_axiom(+InProofs, -OutProofs, +Vertex, +Order, -C, -A, -Proof)
%
% select the negative atomic formula indicated by the unique identifier Vertex-Order from InProofs, that is
% we are seeking a Proof with axiom
%
%   C |- A
%
% such that C is the formula indicated by Vertex-Order and OutProofs are the other proofs.

select_neg_axiom([Proof|Ps], Ps, V, O, C, A, Proof) :-
	select_neg_axiom1(Proof, V, O, C, A),
	!.
select_neg_axiom([P|Ps], [P|Rs], V, O, C, A, Proof) :-
	select_neg_axiom(Ps, Rs, V, O, C, A, Proof).

select_neg_axiom1(_-P, V, O, C, A) :-
	select_neg_axiom1(P, V, O, C, A).
select_neg_axiom1(rule(ax, [M-at(At,V2,O2,Vars)], N-at(At,V1,O1,Vars), []), V, O, M-at(At,V2,O2,Vars), N-at(At,V1,O1,Vars)) :-
	V2 == V,
	O2 == O,
	!.
select_neg_axiom1(rule(_, _, _, Rs), V, O, C, A) :-
	select_neg_axiom_list(Rs, V, O, C, A).

select_neg_axiom_list([R|_], V, O, C, A) :-
	select_neg_axiom1(R, V, O, C, A),
	!.
select_neg_axiom_list([_|Rs], V, O, C, A) :-
	select_neg_axiom_list(Rs, V, O, C, A).

% = select_pos_axiom(+InProofs, -Outproof, +Vertex, +Order, -Delta, -A, -Proof)
%
% select the positive atomic indicated by the unique identifier Vertex-Order from InProofs, that is
% we are seeking a Proof with conclusion
%
%   Delta |- A
%
% such that A is the formula indicated by Vertex-Order and OutProofs are the other proofs.

select_pos_axiom([Proof|Ps], Ps, V, O, Delta, A, Proof) :-
	select_pos_axiom1(Proof, V, O, Delta, A),
	!.
select_pos_axiom([P|Ps], [P|Rs], V, O, Delta, A, Proof) :-
	select_pos_axiom(Ps, Rs, V, O, Delta, A, Proof).

select_pos_axiom1(_-P, V, O, Delta, A) :-
	select_pos_axiom1(P, V, O, Delta, A).
select_pos_axiom1(rule(ax, [M-at(At,V2,O2,Vars)], N-at(At,V1,O1,Vars), []), V, O, [M-at(At,V2,O2,Vars)], N-at(At,V1,O1,Vars)) :-
	V1 == V,
	O1 == O,
	!.
select_pos_axiom1(rule(_, _, _, Rs), V, O, Delta, A) :-
	select_pos_axiom_list(Rs, V, O, Delta, A).

select_pos_axiom_list([R|_], V, O, Delta, A) :-
	select_pos_axiom1(R, V, O, Delta, A),
	!.
select_pos_axiom_list([_|Rs], V, O, Delta, A) :-
	select_pos_axiom_list(Rs, V, O, Delta, A).

% = select_ant_formula(+Antecedent, +Vertex, +Order, -Gamma, -A, -Delta)
%
% select the (negative) atomic formula indicated by Vertex-Order from the given Antecedent,
% dividing the antecedent into Gamma, A, Delta (Gamma is represented as a difference list)

select_ant_formula([N-F|Delta], V, O, [], N-at(At,V,O,Vars), Delta) :-
	max_neg(F, at(At,V1,O1,Vars)),
	V1 == V,
	O1 == O,
	!.
select_ant_formula([G|Gs], V, O, [G|Gamma], A, Delta) :-
	select_ant_formula(Gs, V, O, Gamma, A, Delta).

% = node_proofs(+Graph, -Proofs)
%
% for each of the nodes in Graph, retrieve the stored formula and polarity of the node and
% compute the corresponding sequent proof

node_proofs([V|Vs], [P|Ps]) :-
        node_proof1(V, P),
        node_proofs(Vs, Ps).
node_proofs([], []) :-
	diagnostics_rule.

node_proof1(vertex(N0, As, _, _), N0-Proof) :-
        node_formula(N0, Pol, F),
        node_proof2(As, F, N0, Pol, Proof),
	proof_diagnostics('~w. ', [N0], Proof),	
	!.

% = node_proof2(+Atoms, +Formula, +NodeNumber, +Polarity, -Proof)
%
% create a Proof using matching Formula to its Atoms

node_proof2([], F, N, _, rule(ax, [N-F], N-F, [])).
node_proof2([A|As], F, N, Pol, Proof) :-
        node_proof3(Pol, [A|As], F, N, Proof).

node_proof3(pos, L, F, N, Proof) :-
        create_pos_proof(F, N, L, [], Proof).
node_proof3(neg, L, F, N, Proof) :-
        max_neg_noid(F, MN0),
	rename_bound_variables(MN0, MN),
        create_neg_proof(F, N, L, [], MN, Proof).

% = max_neg(+Formula, -Conclusion)
%
% given a negative (antecedent) formula, compute the Conclusion of the proof we are computing for it;
% this is (maximal) subformula we reach following a path of negative subformulas.

max_neg(impl(_,_-F0), F) :-
	!,
	max_neg(F0, F).
max_neg(forall(_,_-F0), F) :-
	!,
	max_neg(F0, F).
max_neg(F, F).

% = max_neg(+Formula, -Conclusion)
%
% as max_neg, but erases the node id if the maximal negative formula is an atom

max_neg_noid(at(At, _, _, FVs), at(At, _, _, FVs)) :-
	!.
max_neg_noid(impl(_,_-F0), F) :-
	!,
	max_neg_noid(F0, F).
max_neg_noid(forall(_,_-F0), F) :-
	!,
	max_neg_noid(F0, F).
max_neg_noid(F, F).

% = create_pos_proof(+NumberedPositiveFormula, +/-AtomsDL, -Proof)

create_pos_proof(N-A, L0, L, Proof) :-
	create_pos_proof(A, N, L0, L, Proof).

% = create_pos_proof(+PositiveFormula, +NodeNumber, +/-AtomsDL, -Proof)

create_pos_proof(at(A,C,N,Vars), M, [pos(A,C,N,_,Vars)|L], L, rule(ax,[M-at(A,_C,_N,Vars)], M-at(A,C,N,Vars), [])) :-
	!.
create_pos_proof(exists(X,N-A), N, L0, L, rule(er, Gamma, N-exists(Y,N-A3), [ProofA])) :-
        !,
	/* rename to make sure bound variable isn't unified */
	rename_bound_variables(A, A2),
        create_pos_proof(A, N, L0, L, ProofA),
        ProofA = rule(_, Gamma, N-A2, _),
	rename_bound_variable(exists(X,N-A2), X, Y, exists(Y,N-A3)).
create_pos_proof(p(N-A,N-B), N, L0, L, rule(pr, GD, N-p(N-A2,N-B2), [P1,P2])) :-
        !,
        create_pos_proof(A, N, L0, L1, P1),
        create_pos_proof(B, N, L1, L, P2),
        P1 = rule(_, Gamma, N-A2, _),
        P2 = rule(_, Delta, N-B2, _),
        append(Gamma, Delta, GD).
% complex (negative) subformula
create_pos_proof(F, N, L, L, rule(ax, [N-F], N-F, [])).

% = create_neg_proof(+NumberedNegativeFormula, +/-AtomsDL, +Goal, -Proof)

create_neg_proof(N-A, L0, L, Neg, Proof) :-
	create_neg_proof(A, N, L0, L, Neg, Proof).

% = create_neg_proof(+NegativeFormula, +NodeNumber, +/-AtomsDL, +Goal, -Proof)

create_neg_proof(at(A,C,N,Vars), M, [neg(A,C,N,_,Vars)|L], L, at(A,C1,N1,Vars), rule(ax, [M-at(A,C,N,Vars)], M-at(A,C1,N1,Vars), [])) :-
        !.
create_neg_proof(impl(N-A0,N-B), N, L0, L, Neg, rule(il, GD, N-Neg, [ProofA,ProofB])) :-
        !,
	remove_formula_indices(A0, A),
	rename_bound_variables(A, AA),
        create_pos_proof(AA, N, L0, L1, rule(Nm, Gamma, N-A0, Rs)),
	create_neg_proof(B, N, L1, L, Neg, ProofB),
	rename_bound_variables(B, B2),
	/* put back the formula indices for the conclusion */
	ProofA = rule(Nm, Gamma, N-A0, Rs),
	ProofB = rule(_, Delta, _, _),
	select_formula(B2, N, Delta, Delta_B),
	append(Gamma, [N-impl(N-A0,N-B2)|Delta_B], GD).
create_neg_proof(forall(X,N-A), N, L0, L, Neg, rule(fl, GammaP, N-Neg, [ProofA])) :-
        !,
	rename_bound_variables(A, A2),
        create_neg_proof(A, N, L0, L, Neg, ProofA),
        ProofA = rule(_, Gamma, _C, _),
	/* rename to make sure bound variables aren't unified */
	replace_formula(A2, N, N-forall(Y,N-A3), Gamma, GammaP),
	rename_bound_variable(forall(X,N-A2), X, Y, forall(Y,N-A3)).
% complex (positive) subformula
create_neg_proof(F, N, L, L, _, rule(ax, [N-F], N-F, [])).

% = remove_formula_indices(+FormulaId, -FormulaNoId)
%
% remove node identifier information on the atomic subformulas of FormulaId
% to produce FormulaNoId

remove_formula_indices(N-F0, N-F) :-
	remove_formula_indices(F0, F).
remove_formula_indices(at(A,_,_,Vars), at(A,_,_,Vars)).
remove_formula_indices(forall(X, A0), forall(X, A)) :-
	remove_formula_indices(A0, A).
remove_formula_indices(exists(X, A0), exists(X, A)) :-
	remove_formula_indices(A0, A).
remove_formula_indices(impl(A0, B0), impl(A, B)) :-
	remove_formula_indices(A0, A),
	remove_formula_indices(B0, B).
remove_formula_indices(p(A0, B0), p(A, B)) :-
	remove_formula_indices(A0, A),
	remove_formula_indices(B0, B).

remove_formula_nodes(_-F0, F) :-
	remove_formula_nodes(F0, F).
remove_formula_nodes(at(A,_,_,Vars), at(A,Vars)).
remove_formula_nodes(forall(X,A0), forall(X, A)) :-
	remove_formula_nodes(A0, A).
remove_formula_nodes(exists(X,A0), exists(X, A)) :-
	remove_formula_nodes(A0, A).
remove_formula_nodes(impl(A0,B0), impl(A,B)) :-
	remove_formula_nodes(A0, A),
	remove_formula_nodes(B0, B).
remove_formula_nodes(p(A0,B0), p(A,B)) :-
	remove_formula_nodes(A0, A),
	remove_formula_nodes(B0, B).

% = sequent_to_nd(+SequentProof, -NaturalDeductionProof)
%
% translate a sequent proof to a natural deduction proof

sequent_to_nd(SequentProof, NDproof) :-
	sequent_to_nd(SequentProof, NDproof, 1, _NewIndex).

sequent_to_nd(_-R0, R, I0, I) :-
	sequent_to_nd(R0, R, I0, I).
sequent_to_nd(rule(ax, [M-A1], N-A2, []), rule(ax, [M-A1], N-A2, []), I, I).

sequent_to_nd(rule(el, Gamma, C, [R]), rule(ee, Gamma, C, [rule(ax,[N1-exists(X,N0-B0)], N1-exists(X,N0-B0), []), Proof]), I0, I) :-
	member(N1-exists(X,N0-B0), Gamma),
	antecedent_member(B0, _B1, R),
	!,
	sequent_to_nd(R, Proof0, I0, I1),
	I is I1 + 1,
	withdraw_hypothesis(Proof0, I1, B0, Proof).

sequent_to_nd(rule(er, Gamma, N-A, [R0]), rule(ei, Gamma, N-A, [R]), I0, I) :-
	sequent_to_nd(R0, R, I0, I).

%             R                   forall(X,B) |- forall(X,B)       Proof0
%                                 --------------------------
%        Gamma, B |- C            forall(X,B) |- B              Gamma, B |- C
%   -----------------------       -------------------------------------------
%   Gamma, forall(X,B) |- C            Gamma, forall(X,B) |- C
%

sequent_to_nd(rule(fl, Gamma0, C, [R]), Proof, I0, I) :-
	% find a formula which is of the form forall(X,B) in the conclusion of the rule
	% and B in the premiss of the rule.
	member(N1-forall(X,N0-B0), Gamma0),
	antecedent_member(B0, B1, R),	
	!,
	sequent_to_nd(R, Proof0, I0, I),
	antecedent(Proof0, GammaB),
	select_same_formula(_NB, B1, GammaB, Gamma),
	GammaDelta = [N1-forall(X,N0-B0)|Gamma],
	try_cut_elimination_right(rule(fe, [N-forall(X,N0-B0)], N0-B1, [rule(ax, [N-forall(X,N-B0)], N1-forall(X,N0-B0), [])]),
				  Proof0, GammaDelta, C, [N-forall(X,N0-B0)], N-B0, N-B1, Proof).

sequent_to_nd(rule(fr, Gamma, N-A, [R0]), rule(fi, Gamma, N-A, [R]), I0, I) :-
	sequent_to_nd(R0, R, I0, I).

%                                         ProofA                        ProofC
%
%      R1              R2               Delta |- A   A -o B |- A -o B
%                                       -----------------------------
%  Delta |- A   Gamma, B |- C               Delta, A -o B |- B        Gamma, B |- C
%  --------------------------               ---------------------------------------
%   Gamma, Delta, A -o B |- C                      Gamma, Delta, A -o B |- C
%

sequent_to_nd(rule(il, Ant, C, [R1,R2]), Proof, I0, I) :-
	member(M-impl(N-A,N-B0), Ant),
	sequent_to_nd(R1, ProofA, I0, I1),
	sequent_to_nd(R2, ProofC, I1, I),
	ProofA = rule(_, Delta, _NA0, _),
	ProofC = rule(_, GammaB, _, _),
	antecedent_member(B0, B, R2),
	select_same_formula(_NB, B, GammaB, Gamma),
	append(Delta, [M-impl(N-A,N-B0)], DeltaAB),
	append(Gamma, DeltaAB, GammaDeltaAB),
	try_cut_elimination_right(rule(ie, DeltaAB, N-B0, [ProofA,rule(ax, [M-impl(N-A,N-B0)], M-impl(N-A,N-B0), [])]),
				  ProofC, GammaDeltaAB, C, DeltaAB, N-B0, N-B, Proof).

sequent_to_nd(rule(ir, Gamma, _-impl(_-A,_-B), [R0]), rule(ii(I1), Gamma, impl(A,B), [R]), I0, I) :-
	sequent_to_nd(R0, R1, I0, I1),
	I is I1 + 1,
        withdraw_hypothesis(R1, I1, A, R).

sequent_to_nd(rule(pl, Gamma, C, [R]), rule(pe(I1), Gamma, C, [rule(ax,[N0-p(N1-A0,N2-B0)], N0-p(N1-A,N2-B), []), Proof]), I0, I) :-
	member(N0-p(N1-A0,N2-B0), Gamma),
	antecedent_member(A0, A, R),
	antecedent_member(B0, B, R),
	!,
	sequent_to_nd(R, Proof0, I0, I1),
	I is I1 + 1,
        withdraw_hypothesis(Proof0, I1, A, Proof1),
	withdraw_hypothesis(Proof1, I1, B, Proof).

sequent_to_nd(rule(pr, Gamma, C, [R1,R2]), rule(pi, Gamma, C, [Proof1, Proof2]), I0, I) :-
	sequent_to_nd(R1, Proof1, I0, I1),
	sequent_to_nd(R2, Proof2, I1, I).

% = max_hypothesis(+Proof, +MaxIn, -MaxOut)
%
% find the hypothesis with the maximal integer index in Proof

max_hypothesis(rule(hyp(I), _, _, _), Max0, Max) :-
	!,
        Max is max(I,Max0).
max_hypothesis(rule(_, _, _, Rs), Max0, Max) :-
	max_hypothesis_list(Rs, Max0, Max).

max_hypothesis_list([], Max, Max).
max_hypothesis_list([R|Rs], Max0, Max) :-
	max_hypothesis(R, Max0, Max1),
	max_hypothesis_list(Rs, Max1, Max).

% = nd_to_hybrid(+NaturalDeductionProof, -HybridProof).
%
% translate a natural deduction first-order linear logic proof into a proof of
% hybrid type-logical grammars.

nd_to_hybrid(Proof0, Proof) :-
	max_hypothesis(Proof0, 0, Max0),
	Max1 is Max0 + 1,
	nd_to_hybrid(Proof0, Max1, Max, Proof),
	numbervars(Proof, Max, _).

nd_to_hybrid(rule(hyp(I), _, C0, []), Max, Max, rule(hyp(I), '$VAR'(I), HF, [])) :-
	remove_formula_nodes(C0, C),
	linear_to_hybrid(C, HF),
	formula_type(HF, Type),
	retractall(free_var(I, _)),
	assert(free_var(I, Type)).
nd_to_hybrid(rule(ax, _, C0, []), Max0, Max, rule(ax, Lambda, HF, [])) :-
	remove_formula_nodes(C0, C),
	/* recover lexical lambda term here */
	linear_to_hybrid(C, VarList, _, HF),
	numbervars(VarList, 0, _),
        get_positions(VarList, N0, _R),
	lexicon:hybrid_lookup(N0, HF, Lambda0),
	compute_pros_term(Lambda0, HF, Lambda, Max0, Max),
	!.
nd_to_hybrid(rule(ie, _, _, [P1,rule(fe, _, _, [P2])]), Max0, Max, Rule) :-
	!,
	P2 = rule(_, _, C0, _),
	nd_to_hybrid(P1, Max0, Max1, Proof1),
	nd_to_hybrid(P2, Max1, Max2, Proof2),
	antecedent(Proof1, Term1),
	antecedent(Proof2, Term2),
	remove_formula_nodes(C0, C),
	linear_to_lambek(C, [_, _], LF),
	lambek_rule(LF, Term1, Term2, Max2, Max, Proof1, Proof2, Rule).
nd_to_hybrid(rule(fi, _, C0, [rule(ii(I), _, _, [P1])]), Max0, Max, rule(Nm, Term, LF, [Proof1])) :-
	remove_formula_nodes(C0, C),
	linear_to_lambek(C, [_, _], LF),
	nd_to_hybrid(P1, Max0, Max1, Proof1),
	antecedent(Proof1, Term1),
	retractall(free_var(I, _)),
	compute_pros_term(appl(lambda('$VAR'(I),Term1),epsilon), LF, Term, Max1, Max),
        lambek_rule_name(LF, I, Nm).
nd_to_hybrid(rule(ie, _, C0, [P1,P2]), Max0, Max, rule(he, Term, HF, [Proof1,Proof2])) :-
	remove_formula_nodes(C0, C),
	linear_to_hybrid(C, HF),
	nd_to_hybrid(P1, Max0, Max1, Proof1),
	nd_to_hybrid(P2, Max1, Max2, Proof2),
	antecedent(Proof1, Term1),
	antecedent(Proof2, Term2),
	compute_pros_term(appl(Term2,Term1), HF, Term, Max2, Max).
nd_to_hybrid(rule(ii(I), _, C0, [P1]), Max0, Max, rule(hi(I), Term, HF, [Proof1])) :-
	remove_formula_nodes(C0, C),
	linear_to_hybrid(C, HF),
	nd_to_hybrid(P1, Max0, Max1, Proof1),
	antecedent(Proof1, Term0),
	retractall(free_var(I, _)),
	compute_pros_term(lambda('$VAR'(I),Term0), HF, Term, Max1, Max).
	
get_positions(VarList0, L, R) :-
	msort(VarList0, VarList),
	get_positions1(VarList, L, R).

get_positions1([A,A|Rest], L, R) :-
	!,
	get_positions1(Rest, L, R).
get_positions1([L|Rest], L, R) :-
	get_positions2(Rest, R).

get_positions2([A,A|Rest], R) :-
	!,
	get_positions2(Rest, R).
get_positions2([R|Rest], R) :-
	get_positions3(Rest).

get_positions3([]).
get_positions3([A,A|Rest]) :-
	get_positions3(Rest).

lambek_rule_name(dl(_,_), I, dli(I)).
lambek_rule_name(dr(_,_), I, dri(I)).

lambek_rule(dl(_,A), Term1, Term2, Max0, Max, Proof1, Proof2, rule(dle, Term, A, [Proof1, Proof2])) :-
	compute_pros_term(Term1+Term2, A, Term, Max0, Max).
lambek_rule(dr(A,_), Term1, Term2, Max0, Max, Proof1, Proof2, rule(dre, Term, A, [Proof2, Proof1])) :-
	compute_pros_term(Term2+Term1, A, Term, Max0, Max).

% = withdraw_hypothesis(+InProof, +Index, +Atom, -OutProof)
%
% replace the axiom rule of Atom by a hypothesis rule indexed with I; ensures that when
% the proof is output using latex_nd/1 (instead of latex_proof/1) it will be portrayed
% as
%
% [ Atom ]^{Index}
%
% where Index will be shared with the rule introducing the hypothesis.

withdraw_hypothesis(rule(ax, [N-A0], B, []), I, A, rule(hyp(I), [N-A0], B, [])) :-
	same_formula2(A0, A),
	!.
withdraw_hypothesis(rule(Nm, Ant, F, Rs0), I, A, rule(Nm, Ant, F, Rs)) :-
	withdraw_hypothesis_list(Rs0, I, A, Rs).

withdraw_hypothesis_list([R0|Rs0], I, A, [R|Rs]) :-
   (
	withdraw_hypothesis(R0, I, A, R)
   ->	
        Rs = Rs0
   ;			 
        R = R0,
        withdraw_hypothesis_list(Rs0, I, A, Rs)
   ).


% = nd_to_displacement(+NaturalDeductionProof, -DisplacementCalculusProof).
%
% translate a natural deduction first-order linear logic proof into a proof of
% the Displacement calculus

nd_to_displacement(Rule0, Rule) :-
	nd_to_displacement(Rule0, 0, _, Rule).

nd_to_displacement(rule(hyp(I), _, C0, []), Max0, Max, rule(hyp(I), Label, DF, [])) :-
	remove_formula_nodes(C0, C),
	linear_to_displacement(C, Vars, DF),
	vars_to_d_label(Vars, Max0, Max, Label),
	!,
	retractall(d_hyp(I, _)),
	assert(d_hyp(I, Label)).

nd_to_displacement(rule(ax, _, C0, []), Max, Max, rule(ax, [[Word]], DF, [])) :-
	remove_formula_nodes(C0, C),
	linear_to_displacement(C, [N0,_], DF),
	/* recover the corresponding word from lexical lookup here */
	lexicon:memo_lookup(N0, Word),
	!.
% Lambek product introduction
nd_to_displacement(rule(ei,_,C0, [rule(pi, _, _, [P1,P2])]), Max0, Max, rule(pi, Label, DF, [Proof1,Proof2])) :-
	remove_formula_nodes(C0, C),
	linear_to_displacement(C, _, DF),
	nd_to_displacement(P1, Max0, Max1, Proof1),
	nd_to_displacement(P2, Max1, Max, Proof2),
	Proof1 = rule(_, Label1, _, _),
	Proof2 = rule(_, Label2, _, _),
	d_concat(Label1, Label2, Label),
	!.
% Displacement product introduction
nd_to_displacement(rule(ei,_,C0,[rule(ei,_,_,[rule(pi,_,_,[P1,P2])])]), Max0, Max, rule(pi(LR), Label, DF, [Proof1,Proof2])) :-
	remove_formula_nodes(C0, C),
	linear_to_displacement(C, _, DF),
	/* look at the formula to determine whether we found a left-wrap or right-wrap product */
	DF = p(LR,_,_),
	nd_to_displacement(P1, Max0, Max1, Proof1),
	nd_to_displacement(P2, Max1, Max, Proof2),
	Proof1 = rule(_, Label1, _, _),
	Proof2 = rule(_, Label2, _, _),
        ((LR = >) -> d_lwrap(Label1, Label2, Label) ; d_rwrap(Label1, Label2, Label)), 
	!.

nd_to_displacement(rule(ie,_,C0, [RuleA,RuleAB0]), Max0, Max, Rule) :-
	/* elimination rule for one of the implications */
	/* get the positions of the conclusion of the rule */
	remove_formula_nodes(C0, C),
	linear_to_displacement(C, VarsC, DF),
	/* get the positions of the argument (minor premiss) of the rule */
	RuleA = rule(_, _, A0, _),
	remove_formula_nodes(A0, A),
	linear_to_displacement(A, VarsA, _DA),
	/* use both together to decide which forall elimination rules belong to the */
	/* connective of the main formula of the rule */
	d_implication_elim(RuleAB0, VarsA, VarsC, RuleAB),
	nd_to_displacement(RuleA, Max0, Max1, Proof1),
	nd_to_displacement(RuleAB, Max1, Max, Proof2),
	Proof2 = rule(_, _, MainF, _),
	d_combine_proofs(Proof1, Proof2, MainF, DF, Rule),
	!.
nd_to_displacement(Rule0, Max0, Max, Rule) :-
	/* introduction rule for one of the implications */
	Rule0 = rule(_, _, C0, _),
	remove_formula_nodes(C0, C),
	linear_to_displacement(C, _Vars, DF),
	mill1_argument(C, A),
	linear_to_displacement(A, VarsA, _DA),
	length(VarsA, Len),
	d_quantifier_number(DF, Len, QN),
	d_implication_intro(Rule0, QN, I, Rule1),
	nd_to_displacement(Rule1, Max0, Max, Proof1),
	d_hyp(I, HLabel),
	antecedent(Proof1, PLabel),
	d_withdraw_hypothesis(DF, I, HLabel, PLabel, Proof1, Rule),
	!.
% = bridge
nd_to_displacement(rule(ei,_,C0, [P1]), Max0, Max, rule(bridge_e, Label, DF, [Proof1])) :-
	remove_formula_nodes(C0, C),
	linear_to_displacement(C, _, DF),
	nd_to_displacement(P1, Max0, Max, Proof1),
	antecedent(Proof1, ALabel),
	d_lwrap(ALabel, [[]], Label),
	!.
% = left/right projections
nd_to_displacement(rule(fe, _, C0, [P1]), Max0, Max, rule(Nm, Label, DF, [Proof1])) :-
	remove_formula_nodes(C0, C),
	linear_to_displacement(C, _, DF),
	nd_to_displacement(P1, Max0, Max, Proof1),
	Proof1 = rule(_, ALabel, AF, _),
	d_projection(AF, Nm, ALabel, Label),
	!.

% Lambek: the number of quantifiers is equal to 2*s(A)+1 (ie. the number of string positions of the
% argument minus one
% uparrow: the number of quantifiers is equal to to 2*s(B) (ie. the number of string positions of the
% argument minus two
% downarrow: the number of quantifiers is equal to the number of string positions of the argument
% minus two

d_quantifier_number(dl(_,_), N0, N) :-
	N is N0 - 1.
d_quantifier_number(dr(_,_), N0, N) :-
	N is N0 - 1.
d_quantifier_number(dl(_,_,_), N0, N) :-
	N is N0 - 2.
d_quantifier_number(dr(_,_,_), N0, N) :-
	N is N0 - 2.


mill1_argument(forall(_,A0), A) :-
	mill1_argument(A0, A).
mill1_argument(impl(A,_), A).



d_projection(rproj(_), rproj_e, Label, [[]|Label]).
d_projection(lproj(_), lproj_e, Label0, Label) :-
	append(Label0, [[]], Label).


vars_to_d_label([_, _], Max0, Max, [['$VAR'(Max0)]]) :-
	!,
	Max is Max0 + 1.
vars_to_d_label([_, _|Vars], Max0, Max, [['$VAR'(Max0)]|Rest0]) :-
	Max1 is Max0 + 1,
	vars_to_d_label(Vars, Max1, Max, Rest0).

d_withdraw_hypothesis(dl(A,B), I, HLabel, PLabel, P1, rule(dli(I), CLabel, dl(A,B), [P1])) :-
	d_concat(HLabel, CLabel, PLabel).
d_withdraw_hypothesis(dr(A,B), I, HLabel, PLabel, P1, rule(dri(I), CLabel, dr(A,B), [P1])) :-
	d_concat(CLabel, HLabel, PLabel).
d_withdraw_hypothesis(dr(>,A,B), I, [[C]], PLabel, P1, rule(dri(>,I), CLabel, dr(>,A,B), [P1])) :-
	PLabel = [PL1|PLs],
	split_list(PL1, C, C1, C2),
	CLabel = [C1,C2|PLs].
d_withdraw_hypothesis(dl(>,A,B), I, HLabel, PLabel, P1, rule(dli(>,I), CLabel, dl(>,A,B), [P1])) :-	
	d_lwrap(HLabel, CLabel, PLabel).
d_withdraw_hypothesis(dr(<,A,B), I, HLabel, PLabel, P1, rule(dri(>,I), CLabel, dr(<,A,B), [P1])) :-
	d_rwrap(CLabel, HLabel, PLabel).
d_withdraw_hypothesis(dl(<,A,B), I, HLabel, PLabel, P1, rule(dli(>,I), CLabel, dl(<,A,B), [P1])) :-
	d_rwrap(HLabel, CLabel, PLabel).

d_combine_proofs(Proof1, Proof2, MainF, DF, rule(Nm, Label, DF, Ps)) :-
	Proof1 = rule(_, LLabel, _, _),
	Proof2 = rule(_, RLabel, _, _),
	d_combine_proofs(MainF, Nm, LLabel, RLabel, Label, Proof1, Proof2, Ps).

d_combine_proofs(dr(_,_), dre, L1, L2, L, Proof1, Proof2, [Proof2, Proof1]) :-
	d_concat(L2, L1, L).
d_combine_proofs(dl(_,_), dle, L1, L2, L, Proof1, Proof2, [Proof1, Proof2]) :-
	d_concat(L1, L2, L).
d_combine_proofs(dr(>,_,_), dre(>), L1, L2, L, Proof1, Proof2, [Proof2, Proof1]) :-
	d_lwrap(L2, L1, L).
d_combine_proofs(dl(>,_,_), dle(>), L1, L2, L, Proof1, Proof2, [Proof1, Proof2]) :-
	d_lwrap(L1, L2, L).
d_combine_proofs(dr(<,_,_), dre(<), L1, L2, L, Proof1, Proof2, [Proof2, Proof1]) :-
	d_rwrap(L2, L1, L).
d_combine_proofs(dl(<,_,_), dle(<), L1, L2, L, Proof1, Proof2, [Proof1, Proof2]) :-
	d_rwrap(L1, L2, L).

d_concat(As, Bs0, Cs) :-
	var(As),
	!,
    (
        Bs0 == []
    ->
        As = Cs
    ;
        Bs0 = [B|Bs],	
	append(As0, [M|Bs], Cs),
	append(A, B, M),
        append(As0, [A], As)
    ).
d_concat(L1, [First|L2], L) :-
	append(Prefix, [Last], L1),
	append(Last, First, Merged),
	append(Prefix, [Merged|L2], L).
% d_lwrap([As0|As], Bs, [C|Cs]) :-
% 	var(As),
% 	!,
% 	d_concat(As0, Bs, Cs),
% 	d_concat([As0], [B|Bs], ABs0),
% 	d_concat(ABs0, As, [C|Cs]),
% 	As = [A|As0].
d_lwrap([A0,A|As], Bs, Cs) :-
   (
        var(Bs)
   ->
	d_concat(ABs0, [A|As], Cs),
        d_concat([A0], Bs, ABs0)
   ;
        d_concat([A0], Bs, ABs0),
        d_concat(ABs0, [A|As], Cs)
   ).
%	d_concat(ABs0, [A|As], Cs).
d_rwrap(As, Bs, Cs) :-
	append(Prefix, [Last], As),
	d_concat(Prefix, Bs, PBs0),
	d_concat(PBs0, [Last], Cs).


universal_quantifier_variable(_-F, Q) :-
	universal_quantifier_variable(F, Q).
universal_quantifier_variable(forall(X,_), X).

% recover the list of quantified variables

d_implication_elim(Rule0, ArgVars0, ResultVars, Rule) :-
	/* dl(A,B) */
	append(ArgVars, [_], ArgVars0),
	identical_prefix(ArgVars, _, ResultVars),
	d_implication_elim(ArgVars, Rule0, Rule),
	!.
d_implication_elim(Rule0, [_|ArgVars], ResultVars, Rule) :-
	/* dr(A,B) */
	identical_postfix(_, ArgVars, ResultVars),
	d_implication_elim(ArgVars, Rule0, Rule),
	!.
d_implication_elim(Rule0, [_|ArgVars0], [_|ResultVars], Rule) :-
	/* \uparrow_> */
	append(ArgVars, [_], ArgVars0),
	identical_prefix(ArgVars, _, ResultVars),
	d_implication_elim(ArgVars, Rule0, Rule),
	!.
d_implication_elim(Rule0, [A,_,_|ArgVars], [R|ResultVars], Rule) :-
	A == R,
	/* \downarrow_> */
	identical_postfix(_, ArgVars, ResultVars),
	d_implication_elim([A|ArgVars], Rule0, Rule),
	!.
d_implication_elim(Rule0, [_|ArgVars0], ResultVars0, Rule) :-
	/* \uparrow_< */
	append(ArgVars, [_], ArgVars0),
	append(ResultVars, [_], ResultVars0),
	identical_postfix(_, ArgVars, ResultVars),
	d_implication_elim(ArgVars, Rule0, Rule),
	!.
d_implication_elim(Rule0, ArgVars0, ResultVars0, Rule) :-
	/* \downarrow_< */
	append(ArgVars1, [_,_,Z], ArgVars0),
	append(ResultVars, [XNM], ResultVars0),
	XNM == Z,
	identical_prefix(ArgVars1, _, ResultVars),
	append(ArgVars1, [XNM], ArgVars),
	d_implication_elim(ArgVars, Rule0, Rule),
	!.

d_implication_elim([_|Vs], rule(fe, _, _, [Rule0]), Rule) :-
%	Rule0 = rule(_, _, AB0, _),
%	remove_formula_nodes(AB0, AB1),
%	AB1 = forall(X,_),
%	X == V,
	!,
	d_implication_elim(Vs, Rule0, Rule).
d_implication_elim([], Rule, Rule).
	

d_implication_intro(rule(fi, _, _, [Rule0]), N0, I, Rule) :-
	N0 > 0,
	N is N0 - 1,
	!,
	d_implication_intro(Rule0, N, I, Rule).
d_implication_intro(rule(ii(I), _, _, [Rule]), 0, I, Rule).

% =======================================
% =             Input/output            =
% =======================================

print_unifier(at(At,_,_,Vs0), at(At,_,_,Vs)) :-
	unifiable(Vs0, Vs, Unifier0),
	copy_term(Unifier0, Unifier),
	numbervars(Unifier, 0, _),
	latex_list(Unifier).

latex_list([]) :-
	format(latex, '[]', []).
latex_list([A|As]) :-
	format(latex, '[', []),
	latex_list1(As, A).

latex_list1([], A) :-
	format(latex, '~p]', [A]).
latex_list1([A|As], B) :-
	format(latex, '~p,', [B]),
	latex_list1(As, A).

print_diagnostics(Msg) :-
	proof_diagnostics(Msg, []).
print_diagnostics(Msg, Vs) :-
   (
	generate_diagnostics(true)
    ->
	format(latex, Msg, Vs)
    ;
        true
    ).


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

diagnostics_rule :-
   (
	generate_diagnostics(true)
    ->
	format(latex, '~2n\\hrule~n\\medskip~2n', [])
    ;
        true
    ).
	
