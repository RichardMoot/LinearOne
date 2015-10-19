% =================================
% =        Hybrid grammar         =
% =================================

% This grammar contains many examples from the following articles.
%
% Yusuke Kubota and Robert Levine (2012) Gapping as Like-Category Coordination, in Denis Bechet and
% Alexander Dikovsky (eds), Logical Aspects of Computational Linguistics 2012, Springer Lecture Notes
% in Computer Science 7351, pp. 135-150.
%
% Yusuke Kubota and Robert Levine (2013) Determiner Gapping as Higher-Order Discontinuous Constituency
% in Glyn Morrill and Mark-Jan Nederhof (eds), Formal Grammar 2013, Springer Lecture Notes in Computer
% Science 8036, pp. 225-241.

% define operators to allow for easier specification of
% hybrid type-logical grammar lexical entries.
%
% WARNING: in case of doubt, use parentheses to disambiguate!
% I have deliberately not changed the definitions of standard
% mathematical and logical operations of Prolog, notably |
% (alternative of ; for use in DCG), ^, /, * and +.
%
% This means for example that:
% c/d*b/c = ((c/d)*b)/c
% which corresponds to a left-to-right evaluation of the
% mathematical functions of division and multiplication.
%
% It also means that (s|s|np) = (s|(s|np))
%
% However, we do have the familiar a/b/c = (a/b)/c and
% c\b\a = (c\(b\a) and even a\b/c = (a\b)/c.
%
% For lambda terms, X^M is short for lambda(X,M) and M@N
% is short for appl(M,N). As expected, X^Y^Z^X@Y@Z is
% short for lambda(X,lambda(Y,lambda(Z,appl(appl(X,Y),Z))))
% though be warned that X@Y+V@Z corresponds to (X@Y)+(V@Z)

:- op(400, xfy, \).
:- op(190, yfx, @).

:- abolish(lex/3), abolish(lex/4), abolish(test/1), abolish(atomic_formula/3), abolish(atomic_formula/1), abolish(macro/2).

test(1) :-
	parse([someone,talked,to,everyone,yesterday], s).
test(2) :-
	parse([leslie,bought,a,cd,and1,robin,a,book], s1).
test(3) :-
	parse([leslie,bought,a,cd,and,robin,a,book], s).
test(4) :-
	parse([robin,must,discover,a,solution], s).
test(5) :-
	parse([john,cant,eat,steak,and1,mary,pizza], s1).
test(6) :-
	parse([john,cant,eat,steak,and,mary,pizza], s).
% split scope
test(7) :-
	parse([no2,neg,fish,walks], s).
test(8) :-
	parse([no2,neg,dog,eats,whiskas,or2,neg,cat,alpo], s).
% comparative subdeletion
test(9) :-
	parse([john,ate,more,donuts,than,mary,bought,bagels], s).
test(b) :-
	parse([john,ate,more2,donuts,than2,mary,bought,bagels], s).
test(10) :-
	parse([no,fish,walks], s).
% NOTE: The next two examples illustrate the improvement of the dancing links algorithm over the naive algorith rather spectacularly!
test(11) :-
	/* first-found axioms */
	/*         3,142,516 axioms ! */
        /*     5,808,425,093 inferences, 2014.396 CPU in 2139.522 seconds (94% CPU, 2883458 Lips) */
	/* with first dancing links version */
	/*            28,520 axioms */
        /*        65,422,872 inferences,    8.827 CPU in 10.075 seconds (88% CPU, 7411284 Lips) */
	parse([no,dog,eats,whiskas,or,cat,alpo], s).
test(12) :-
	/* first-found */
        /*     4,215,069,209 axioms performed */
	/* 3,014,184,930,660 inferences, 375241.334 CPU in 375357.875 seconds (100% CPU, 8032657 Lips) */
	/*                          = 4d8h14m01.334s */
	/*    59 proofs */
	/* with first dancing links version */
	/*        24,370,833 axioms */
        /*    77,693,926,965 inferences,  11458.063 CPU in  12895.382 seconds  (89% CPU, 6780721 Lips) */
	/*                            = 3h10m58.063s */
	/*    59 proofs */
 	parse([no,dog,eats,more,whiskas2,than,leslie,buys,donuts,or,cat,alpo], s).

% has (unwanted) second reading since the np "bananafish" can lift to Lambek reflexive type and resulting
% in a coordination between "lobster yesterday" and "bananafish", with "today" having wide scope over the
% complete sentence.
test(24) :-
	parse([captain_jack,served,lobster,yesterday,and3,bananafish,today], s).

test(30) :-
	parse([rarely,does,john,call,mary,and,mary,john], s).
test(31) :-
	parse([rarely,does,john,call,mary,at_home,and,mary,john], s).

test_and :-
	exhaustive_test('and.pl', and, ((((s| np)| np)| (s| np)| np)| (s| np)| np), lambda(M, lambda(J, lambda(K, lambda(L, bool(appl(appl(J, K), L), &, appl(appl(M, K), L)))))), [and], (((np\s)/np)\((np\s)/np))/((np\s)/np)).

test_jsl :-
	parse([john,studies,logic,and,charles,phonetics], s1).

% =======================
% =       Lexicon       =
% =======================

lex(rarely, s/s, rarely, rarely).
lex(does, (s/sinf)/np, does, lambda(Subj,lambda(Inf,appl(Inf,Subj)))).
lex(call, sinf/np, call, call).
%lex(at_home, sinf\sinf, at_home, at_home).
lex(at_home, s\s, at_home, at_home).
%lex(and, (s|((s/np)|np))|
lex(and, (((s|((s/np)|np))|(s|((s/np)|np)))|(s|((s/np)|np))), lambda(STV2,lambda(STV1,lambda(TV,appl(STV1,TV)+and+(appl(STV2,lambda(W,W)))))), lambda(S2,lambda(S1,lambda(T,bool(appl(S1,T),&,appl(S2,T)))))).

% = lex(+Word, +Formula, +ProsodicTerm, +SemanticTerm)
%
% ProsodicTerm must be a linear lambda term containing exactly one occurrence of Word

lex(leslie, np, leslie, l).
lex(robin, np, robin, r).
lex(john, np, john, j).
lex(charles, np, charles, c).
lex(logic, np, logic, l).
lex(phonetics, np, phonetics, p).
lex(mary, np, mary, m).
lex(bought, tv, bought, buy).
lex(buys, tv, buys, buy).
lex(studies, tv, studies, study).
lex(eats, tv, eats, eat).
lex(ate, tv, ate, eat).
lex(chased, tv, chased, chase).
lex(talked, (np\s)/pp, talked, talk).
lex(discover, tv, discover, discover).
lex(discovers, tv, discovers, discover).
lex(walks, np\s, walks, walk).
lex(eat, tv, eat, eat).
lex(a, ((s|(s|np))|n), lambda(N,lambda(P,lambda(Z,appl(appl(P,lambda(V,appl(a,appl(N,V)))),Z)))), lambda(X,lambda(Y,quant(exists,Z,bool(appl(X,Z),&,appl(Y,Z)))))).
lex(every, ((s|(s|np))|n), lambda(N, lambda(P,appl(P,every+N))), lambda(X,lambda(Y,quant(forall,Z,bool(appl(X,Z),->,appl(Y,Z)))))).
lex(someone, (s|(s|np)), lambda(Pr,lambda(Z,appl(appl(Pr,someone),Z))), lambda(P,quant(exists,X,bool(appl(person,X),&,appl(P,X))))).
lex(everyone, (s|(s|np)), lambda(Pr,lambda(Z,appl(appl(Pr,everyone),Z))), lambda(P,quant(forall,X,bool(appl(person,X),->,appl(P,X))))).
lex(yesterday, (np\s)\(np\s), yesterday, X^Y^(yesterday@(X@Y))).
lex(today, (np\s)\(np\s), today, X^Y^(today@(X@Y))).
lex(fish, n, fish, fish).
lex(dog, n, dog, dog).
lex(cat, n, cat, cat).
lex(cd, n, cd, cd).
lex(book, n, book, book).
lex(donuts, n, donuts, donuts).
lex(bagels, n, bagels, bagels).
lex(solution, n, solution, solution).
lex(steak, np, steak, steak).
lex(pizza, np, pizza, pizza).
lex(whiskas, np, whiskas, whiskas).
lex(alpo, np, alpo, alpo).
lex(whiskas2, n, whiskas2, whiskas).
lex(alpo2, n, alpo2, alpo).
lex(to, pp/np, to, lambda(X,X)).
lex(that, (n|n)|(s|np), lambda(SNP,lambda(N,N+that+appl(SNP,epsilon))), lambda(P,lambda(Q,lambda(X,bool(appl(Q,X),&,appl(P,X)))))).
% = uses s1 as final category to avoid quantifier scope outside of the individual conjuncts
lex(and1, (((s1|tv)|(s|tv))|(s|tv)), lambda(STV2,lambda(STV1,lambda(TV,lambda(V,appl(appl(STV1,TV),appl(and1,appl(appl(STV2,lambda(W,W)),V))))))), lambda(S2,lambda(S1,lambda(T,bool(appl(S1,T),&,appl(S2,T)))))).
lex(and, (((s|tv)|(s|tv))|(s|tv)), lambda(STV2,lambda(STV1,lambda(TV,lambda(V,appl(appl(STV1,TV),appl(and,appl(appl(STV2,lambda(W,W)),V))))))), lambda(S2,lambda(S1,lambda(T,bool(appl(S1,T),&,appl(S2,T)))))).
lex(and_np, dr(dl(np,np),np), and_np, lambda(NP2,lambda(NP1,bool(NP1,&,NP2)))).
lex(and_q, (((s|s|np)|(s|s|np))|(s|s|np)), lambda(SP2,lambda(SP1,lambda(P,appl(P,appl(SP1,lambda(V,V))+and_q+appl(SP2,lambda(W,W)))))), lambda(SQ2,lambda(SQ1,lambda(SNP,bool(appl(SQ1,SNP),&,appl(SQ2,SNP)))))).
lex(must, (s|(s|(vp/vp))), lambda(SVP,lambda(Z,appl(appl(SVP,must),Z))), lambda(F,necessary(appl(F,lambda(Y,Y))))).
lex(cant, (s|(s|(vp/vp))), lambda(SVP,lambda(Z,appl(appl(SVP,cant),Z))), lambda(F,neg(possible(appl(F,lambda(Y,Y)))))).
lex(no, (s|(s|h_det)), lambda(Rho,lambda(Z,appl(appl(Rho,lambda(Phi,lambda(Sigma,lambda(V,appl(appl(Sigma,lambda(W,appl(no,appl(Phi,W)))),V))))),Z))), lambda(P,neg(appl(P,lambda(Q,lambda(R,quant(exists,X,bool(appl(Q,X),&,appl(R,X))))))))).
lex(than, than, than, lambda(X,X)).
lex(more, (((s|(s|h_det))|(s|h_det))|than), lambda(Than,lambda(Rho1,lambda(Rho2,lambda(Z,appl(appl(Rho2,lambda(Phi,lambda(Sigma,appl(Sigma,lambda(V,appl(more,appl(Phi,V))))))),appl(Than,appl(appl(Rho1,lambda(Phi2,lambda(Sigma2,lambda(W,appl(appl(Sigma2,Phi2),W))))),Z))))))), lambda(_,lambda(F,lambda(G,bool(number_of(appl(G,lambda(P,lambda(Q,lambda(X,bool(appl(P,X),&,appl(Q,X))))))),gneq,number_of(appl(F,lambda(P2,lambda(Q2,lambda(Y,bool(appl(P2,Y),&,appl(Q2,Y)))))))))))).
lex(or, ((((s|h_det)|tv)|((s|h_det)|tv))|((s|h_det)|tv)), lambda(Rho2,lambda(Rho1,lambda(Phi,lambda(Tau,lambda(Z,appl(appl(appl(Rho1,Phi),Tau),appl(or,appl(appl(appl(Rho2,lambda(V,V)),lambda(Phi2,lambda(Sigma2,lambda(W,appl(appl(Sigma2,Phi2),W))))),Z)))))))), lambda(SDTV2,lambda(SDTV1,lambda(TV,lambda(Det,bool(appl(appl(SDTV1,TV),Det),\/,appl(appl(SDTV2,TV),Det))))))).
%lex(more_d, (s/<d_q)\<(s/(^(cp/<d_q))), lambda(X,lambda(Y,bool(number_of(lambda(Z,appl(X,lambda(P,lambda(Q,bool(appl(P,Z),&,appl(Q,Z))))))),gneq,number_of(lambda(Z1,appl(Y,lambda(P1,lambda(Q1,bool(appl(P1,Z1),&,appl(Q1,Z1))))))))))).
lex(and3, ((np\s/np)\np\s)\ (np\s/np)\np\s/ ((np\s/np)\np\s), and3, lambda(P,lambda(Q,lambda(R,lambda(X,bool(appl(appl(Q,R),X),&,appl(appl(P,R),X))))))).
lex(served, (np\s)/np, served, serve).
lex(captain_jack, np, captain_jack, captain_jack).
lex(lobster, np, lobster, lobster).
lex(bananafish, np, bananafish, bananafish).

% lexical entries for "split scope"

lex(no2, (s|sneg), lambda(S,lambda(Z,appl(appl(S,no2),Z))), neg).
lex(or2, (((sneg|tv)|(sneg|tv))|(sneg|tv)), lambda(Sigma2,lambda(Sigma1,lambda(Phi1,lambda(Phi2,lambda(Z,appl(appl(appl(Sigma1,Phi1),Phi2),appl(or2,appl(appl(appl(Sigma2,lambda(V,V)),lambda(W,W)),Z)))))))), lambda(V1,lambda(W1,lambda(TV,bool(appl(W1,TV),\/,appl(V1,TV)))))).
lex(neg, ((sneg|(s|np))|n), lambda(Phi1,lambda(Sigma,lambda(Phi2,lambda(W,appl(appl(Sigma,lambda(V,appl(Phi2,appl(neg,appl(Phi1,V))))),W))))), lambda(X,lambda(Y,quant(exists,Z,bool(appl(X,Z),&,appl(Y,Z)))))).


% attempt to recreate the Morrill e.a. analysis

lex(than2, cp/s, than2, lambda(X,X)).
lex(more2, ((s|(cp|h_det))|(s|h_det)), lambda(Rho1,lambda(Rho2,lambda(Z,appl(appl(Rho2,lambda(Phi,lambda(Sigma,appl(Sigma,lambda(V,appl(more2,appl(Phi,V))))))),appl(appl(Rho1,lambda(Phi2,lambda(Sigma2,lambda(W,appl(appl(Sigma2,Phi2),W))))),Z))))), lambda(F,lambda(G,bool(number_of(appl(G,lambda(P,lambda(Q,lambda(X,bool(appl(P,X),&,appl(Q,X))))))),gneq,number_of(appl(F,lambda(P2,lambda(Q2,lambda(Y,bool(appl(P2,Y),&,appl(Q2,Y))))))))))).


