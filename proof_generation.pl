:- module(proof_generation, [generate_proof/2]).

:- use_module(latex, [latex_proof/1]).
:- use_module(replace, [rename_bound_variable/4, rename_bound_variables/2, replace_proofs_labels/4]).
:- use_module(auxiliaries, [select_formula/4, subproofs/2, rulename/2, is_axiom/1, antecedent/2]).

%generate_diagnostics(true).
generate_diagnostics(false).

% =======================================
% =           Proof generation          =
% =======================================

% = generate_proof(+InitialGraph, +ProofTrace)
%
% generate a sequent proof from the initial graph and proof trace
% given as arguments, and set the output to LaTeX.

generate_proof(Graph, Trace) :-
	node_proofs(Graph, Proofs),
	combine_proofs(Trace, Proofs, Proof),
	trace,
	sequent_to_nd(Proof, NDProof),
	latex_proof(NDProof),
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
%	append(Delta1, [_-at(_,AtV2,AtO2,_)|Delta2], Ant),
%	AtV2 == AtV1,
%	AtO2 == AtO1,
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
	select_same_formula(B, N1, Delta0, Delta1),
	select_same_formula(A, N1, Delta1, Delta),
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
	same_formula(F0, F).
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

% = select_neg_proof(+InProofs, -OutProofs, +Vertex, +Order, -Gamma, -A, -Delta, -C, -Proof)
%
% select the negative atomic formula indicated by the unique identifier Vertex-Order from InProofs, that is
% we are seeking a Proof with conclusion
%
%   Gamma, A, Delta |- C
%
% such that A is the formula indicated by Vertex-Order and OutProofs are the other proofs.


%% select_neg_proof([P|Ps], Ps, V, O, Gamma, A, Delta, C, Proof) :-
%% 	select_neg_proof1(P, V, O, Gamma, A, Delta, C, Proof),
%% 	!.
%% select_neg_proof([P|Ps], [P|Rs], V, O, Gamma, A, Delta, C, Proof) :-
%% 	select_neg_proof(Ps, Rs, V, O, Gamma, A, Delta, C, Proof).

%% select_neg_proof1(N-P, V, O, Gamma, A, Delta, C, N-R) :-
%% 	select_neg_proof1(P, V, O, Gamma, A, Delta, C, R).
%% select_neg_proof1(rule(Nm, GammaADelta, C, Ps), V, O, Gamma, A, Delta, C, rule(Nm, GammaADelta, C, Ps)) :-
%% 	select_ant_formula(GammaADelta, V, O, Gamma, A, Delta).

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

% = select_pos_proof(+InProofs, -Outproof, +Vertex, +Order, -Delta, -A, -Proof)
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
	
%% select_pos_proof([P|Ps], Ps, V, O, Delta, A, Proof) :-
%% 	select_pos_proof1(P, V, O, Delta, A, Proof),
%% 	!.
%% select_pos_proof([P|Ps], [P|Rs], V, O, Delta, A, Proof) :-
%% 	select_pos_proof(Ps, Rs, V, O, Delta, A, Proof).

%% select_pos_proof1(_-P, V, O, Delta, A, R) :-
%% 	select_pos_proof1(P, V, O, Delta, A, R).
%% select_pos_proof1(rule(Nm, Delta, N-at(At,V1,O1,Vars), Rs), V, O, Delta, N-at(At,V,O,Vars), rule(Nm, Delta, N-at(At,V,O,Vars), Rs)) :-
%% 	V1 == V,
%% 	O1 == O,
%% 	!.
%select_pos_proof1(rule(_, _, _, Rs), V, O, Delta, A, Proof) :-

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



% = sequent_to_nd(+SequentProof, -NaturalDeductionProof)
%
% Q: is it easier to generate natural deduction proofs directly?

sequent_to_nd(_-R0, R) :-
	sequent_to_nd(R0, R).
sequent_to_nd(rule(ax, [M-A1], N-A2, []), rule(ax, [M-A1], N-A2, [])).

%             R                   forall(X,B) |- forall(X,B)       Proof0
%                                 --------------------------
%        Gamma, B |- C            forall(X,B) |- B              Gamma, B |- C
%   -----------------------       -------------------------------------------
%   Gamma, forall(X,B) |- C            Gamma, forall(X,B) |- C
%

sequent_to_nd(rule(fl, Gamma0, C, [R]), Proof) :-
	% find a formula which is of the form forall(X,B) in the conclusion of the rule
	% and B in the premiss of the rule.
	member(N1-forall(X,N0-B0), Gamma0),
	antecedent_member(B0, B1, R),	
	!,
	sequent_to_nd(R, Proof0),
	antecedent(Proof0, GammaB),
	select_same_formula(_NB, B1, GammaB, Gamma),
	GammaDelta = [N1-forall(X,N0-B0)|Gamma],
	try_cut_elimination_right(rule(fe, [N-forall(X,N0-B0)], N0-B1, [rule(ax, [N-forall(X,N-B0)], N1-forall(X,N0-B0), [])]),
				  Proof0, GammaDelta, C, Gamma, N-B0, N-B1, Proof).

sequent_to_nd(rule(fr, Gamma, _-A, Rs0), rule(fi, Gamma, A, Rs)) :-
	sequent_to_nd_list(Rs0, Rs).

%                                         ProofA                        ProofC
%
%      R1              R2               Delta |- A   A -o B |- A -o B
%                                       -----------------------------
%  Delta |- A   Gamma, B |- C               Delta, A -o B |- B        Gamma, B |- C
%  --------------------------               ---------------------------------------
%   Gamma, Delta, A -o B |- C                      Gamma, Delta, A -o B |- C
%

sequent_to_nd(rule(il, Ant, C, [R1,R2]), Proof) :-
	member(M-impl(N-A,N-B0), Ant),
%	R1 = rule(_, _, _-A0, _),
	sequent_to_nd(R1, ProofA),
	sequent_to_nd(R2, ProofC),
	ProofA = rule(_, Delta, _NA0, _),
	ProofC = rule(_, GammaB, _, _),
	antecedent_member(B0, B, R2),
	select_same_formula(_NB, B, GammaB, Gamma),
	append(Delta, [M-impl(N-A,N-B0)], DeltaAB),
	append(Gamma, DeltaAB, GammaDeltaAB),
	try_cut_elimination_right(rule(ie, DeltaAB, N-B0, [ProofA,rule(ax, [M-impl(N-A,N-B0)], M-impl(N-A,N-B0), [])]),
				  ProofC, GammaDeltaAB, C, DeltaAB, N-B0, N-B, Proof).

	%% P1 = rule(_, Gamma, A, _),
	%% P2 = rule(_, Delta0, N1-D, _),	
	%% /* TODO: guarantee this is the same formula occurrence, split_antecedent is too strict of a condition */
	%% /* Q: are the node numbers enough to guarantee this? Verify! */
	%% append(Gamma0, [N0-impl(N1-C,N1-D)|Gamma1], Gamma),
	%% select_same_formula(N1, C, Delta0, Delta),
	%% append(Gamma0, Delta, GD0),
	%% append(GD0, Gamma1, GD),
	%% /* try to create a cut-free proof */
	%% try_cut_elimination_right(rule(ir, Delta, N0-impl(N1-C,N1-D), [P2]), P1, GD, A, Delta, N0-impl(N1-C,N1-D), N0-impl(N1-C,N1-D), Rule).

sequent_to_nd(rule(ir, _Gamma, _-impl(_-A,_-B), [R0]), rule(ii, impl(A,B), [R])) :-
	/* TODO: add axiom withdrawal */
	sequent_to_nd(R0, R).

sequent_to_nd_list([], []).
sequent_to_nd_list([R0|Rs0], [R|Rs]) :-
	sequent_to_nd(R0, R),
	sequent_to_nd_list(Rs0, Rs).



insert_rule(rule(Nm, _Gamma, A, Rs), rule(Nm, _Delta, B, Rs), Proof, Proof) :-
	same_formula1(A, B),
	!.
insert_rule(rule(Nm, Gamma, A, Rs0), Sub1, Sub2, rule(Nm, Gamma, A, Rs)) :-
	insert_rule_list(Rs0, Sub1, Sub2, Rs).

insert_rule_list([R0|Rs0], Sub1, Sub2, [R|Rs]) :-
	insert_rule(R0, Sub1, Sub2, R),
	!,
	Rs0 = Rs.
insert_rule_list([R|Rs0], Sub1, Sub2, [R|Rs]) :-
	insert_rule_list(Rs0, Sub1, Sub2, Rs).

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
	
